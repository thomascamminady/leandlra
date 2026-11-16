# LeanDLRA conventions

New and moved code is reviewed against this page. The page describes the core as it is: where the
two differ, the core is the reference and the page is corrected. Declarations, files and folders
named here exist, with one exception: the second column of the table in §7 gives examples of names
formed by the rules.

## 1. Principles

1. **Correct before tidy.** A move, rename or refactor never changes what a theorem says without
   being listed. Every change keeps: zero warnings, standard axioms only, kernel replay, and the
   recorded statements unchanged (`scripts/fidelity.py`, through the rename map of §11).
2. **One definition per concept.** A concept is defined once, in a `Defs.lean` (§3). A second
   definition of the same object is replaced by the first. A *different* object gets its own name.
3. **Chain only what provably means the same.** Two definitions are merged only after a Lean
   lemma `local = core` (or `local ↔ core`). If only one direction holds, keep both and prove the
   implication. If neither holds, keep two names, each docstring says how they differ, and an
   `example` separates them.
4. **Mathlib style.** Mathlib's naming, docstring and file-header conventions apply unless this page
   says otherwise. Do not redefine what Mathlib has.

## 2. Layers and folders

The core is one theory in layers. A file imports Mathlib and files of its own or a lower layer,
never a higher one.

| # | Folder | Owns |
|---|---|---|
| 1 | `LinearAlgebra/` | the Frobenius inner product and the weighted inner products (`Frobenius/Defs.lean`); orthogonal and oblique projectors (`IsOrthProj`, `leftProj`, `rightProj`, `rankOneProj`, `obliqueProj`; `Projection/Defs.lean`); pseudoinverses, factorizations and the projectors built from them (`Factorization/Defs.lean`); singular vectors and the truncated SVD (`SVD/Defs.lean`); low-rank sets (`lowRankSet`, `distLR`, `epsRank`; `LowRank/Defs.lean`) |
| 2 | `Analysis/` | `ODESolution`, `IsLipschitzField`, `IsBoundedField`, `IsOneSidedLipschitzField`; the conditions on a region and on a tube around a curve (`tubeSet`, `IsLipschitzOnTube`, `IsBoundedOnTube`); Butcher tableaux (`Analysis/Defs.lean`) |
| 3 | `FixedRank/` | the tangent and normal calculus (`tangent`, `normal`), `tangentProj`, oblique tangent projectors (`FixedRank/Defs.lean`); the tangent projector and the tangent space at a matrix, `tangentProjAt` and `tangentSpaceAt` (`FixedRank/TangentSpace/Defs.lean`); tangent vectors of the fixed-rank manifold |
| 4 | `DLRA/` | `DLRAProblem` and the normal-component bound `NormalBoundOn` (`DLRA/Defs.lean`) |
| 5 | `Integrators/` | time grids, local errors, step relations and runs (`Integrators/Defs.lean`); the theory for all methods (`GlobalError.lean`, `Tube.lean`, `Method.lean`); one file per method in projector form (`BUG.lean`, `ProjectorSplitting.lean`, `ParallelBUG.lean`, `RankAdaptiveBUG.lean`, …); the matrix forms of the methods in `Integrators/Matrix/` |
| 6 | `Tensor/` | tensors, unfoldings, Tucker tensors, tensor trains, tree tensor networks (`Tensor/Defs.lean`), and their integrators |
| 7 | `Kinetic/`, `Stochastic/`, `Training/`, `Filtering/`, `Control/` | applications; they build on layers 1–6 |

A result goes into the **lowest** layer that can state it.

The folders `Foundations/`, `Matrix/`, `Classical/`, `Dynamics/`, `Stability/`, `Stiff/`,
`HighOrder/`, `Randomized/` and `Research/` are older than the layers. By content `Foundations/`
belongs to layer 2 (its `Projector.lean` to layers 1 and 3), `Matrix/` to layers 1 and 3,
`Classical/` to layer 1, `Dynamics/` to layer 4, and `Stiff/`, `HighOrder/` and `Randomized/` to
layer 5. The import rule above holds between the layer folders; it does not yet hold for every
file of the older folders (for example `Foundations/Localization.lean` imports
`Integrators/BUG.lean`). A new file goes into a layer folder.

The folders `Literature/`, `OpenProblems/`, `Novel/` and `Corrections/` hold the catalogue
([STRUCTURE.md](STRUCTURE.md)): results of single papers, stated in definitions of their own. A
paper result that is a special case of a core theorem is proved from the core theorem, and its
module can then be promoted (§10).

## 3. The `Defs.lean` rule

- Every public `def`, `abbrev`, `structure`, `class`, `inductive` and non-scoped `instance` lives in
  the `Defs.lean` of its topic: `LeanDLRA/<Topic>/Defs.lean`, or `LeanDLRA/<Topic>/<Sub>/Defs.lean`
  where a topic needs several (as in `LinearAlgebra/`). [DEFINITIONS.md](DEFINITIONS.md) lists the
  definitions of the core with their files.
- A `Defs.lean` contains the definitions, their basic API (`_apply`, `_def`, `@[simp]` lemmas,
  `ext`, conversion lemmas to Mathlib such as `isOrthProj_starProjection`), and one `example` per
  structure showing that it can be satisfied. Theorems with real proofs go elsewhere.
- A `Defs.lean` imports Mathlib and lower-layer `Defs.lean` files only, so that importing the
  vocabulary stays cheap.
- Exempt: `private` definitions, definitions inside proofs, concrete example data inside
  `namespace …Examples` (marked `private` where possible), and auto-generated declarations
  (`match_1`, `eq_1`).
- Before adding a definition, search [DEFINITIONS.md](DEFINITIONS.md), [CONCEPTS.md](CONCEPTS.md)
  and Mathlib. If the object exists, use it. If the paper's object differs, define it locally from
  core pieces, prove the bridging lemma in the same file, and say in the docstring why the core one
  does not fit.
- Concrete vectors and matrices are not concepts: write `Pi.single i 1`,
  `EuclideanSpace.single i 1` or `Matrix.single i j 1` instead of a local `e₁`.

The rule holds for new files. Many definitions of the core are still in the file that first
needed them (the step structures of the methods, for example `IsBUGStep` in `Integrators/BUG.lean`);
the column "File and line" of [DEFINITIONS.md](DEFINITIONS.md) shows where each one is.

## 4. Notation and standing variables

Use these names in statements and docstrings. Deviate only where a paper's notation is
established in an application (for example `X` space basis, `V` velocity basis, `f = X S Vᵀ` in
`Kinetic/`), and say so in the module header.

| Symbol | Lean | Meaning |
|---|---|---|
| `E` | `[NormedAddCommGroup E] [InnerProductSpace ℝ E]` | state space; `[CompleteSpace E]` only when used |
| `m n` | `[Fintype m] [Fintype n]` | row and column index types of matrices |
| `r` | `r : ℕ`, factors indexed by `Fin r` | rank; `k`, `l`, `k'` for general basis index types |
| `F` | `F : ℝ → E → E` | right-hand side, time first |
| `A` | `A : ℝ → E` | exact solution, `ODESolution F A a b` |
| `Y` | `Y : ℝ → E` or `Y : ℕ → E` | low-rank approximation (DLRA trajectory or numerical values) |
| `Y₀ Y₁` | `E` | start and result of one step |
| `YK YL YS` | `ℝ → E` | full-space trajectories of the K-, L- and S-substeps |
| `U V`, `S` | `Uᵀ * U = 1`, `Vᵀ * V = 1`; `Y = U * S * Vᵀ` | bases and coefficient matrix |
| `K L` | `K = U * S`, `L = V * Sᵀ` | factor unknowns of the substeps |
| `P Q` | `E →L[ℝ] E` with `IsOrthProj` | left and right projectors; `P₀ Q₀` old, `P₁ Q₁` new bases |
| `P_Y` | `tangent P Q`, `tangentProj U V` | tangent projector at `Y` |
| `ε` | `ℝ` | bound on the normal component of `F` |
| `h H` | `ℝ` | step size and an upper bound for it |
| `τ` | `τ : ℕ → ℝ` with `IsGrid τ N` | time grid; the uniform grid is `uniformGrid t₀ h` |
| `t₀ N T` | grid `t₀ + n * h`, `n ≤ N`, with `n * h ≤ T` or `N * h ≤ T` | start time, number of steps and horizon |
| `L B ℓ Lₜ` | `ℝ` | Lipschitz constant, bound of `F`, one-sided Lipschitz constant, time-Lipschitz constant |
| `δ ϑ η` | `ℝ` | initial error, truncation tolerance, substep inexactness |
| `ρ` | `ℝ` | radius of the tube around the exact solution (`tubeSet A a b ρ`, `DLRAProblem F A a b ρ L B`), in layers 2, 4 and 5 |
| `κ` | `ℝ` | margin constant of a step method (`StepMethod.IsTubeLocal M Adm κ`) |
| `Φ` | `ℕ → ℝ → E` | exact solutions started at the numerical values `(τ n, Y n)` (`IsExactFan`) |
| `C` | `E →L[ℝ] E` | moment projector in conservation results |

- `ρ` has a second use: in `Matrix/Curvature.lean` it is the lower bound of the nonzero singular
  values (`σ_r(X) ≥ ρ > 0`), as in the source of that file. The module header says which one is
  meant when a file uses `ρ` in this sense.
- Grid points of the uniform grid are written `t₀ + n * h` and `t₀ + (n + 1) * h`, with `(n : ℝ)`
  casts left to elaboration. Intervals: `Icc` for continuity and hypotheses on closed intervals,
  `Ico` for right derivatives, as in `ODESolution`.
- Projector applications are written `P (Q x)` and `(1 - P) x`, not `(P * Q) x`.
- Matrix products associate to the left: `U * S * Vᵀ`. Transpose is `ᵀ` (`open scoped Matrix`).
- Orthonormal columns are the equation `Uᵀ * U = 1`; do not add a predicate for it.

## 5. Norms and scalars

- **Matrices carry the Frobenius norm and inner product.** They come from
  `open scoped LeanDLRA.Frobenius` (scoped instances in `LinearAlgebra/Frobenius/Defs.lean`); never
  make them global. Then `‖A‖` is the Frobenius norm and `⟪A, B⟫ = ∑ i j, A i j * B i j`.
- **The spectral norm** is `Curvature.specNorm A` (`LinearAlgebra/Frobenius/Defs.lean`), which is
  Mathlib's L2 operator norm (`specNorm_eq_l2`, `Matrix/Curvature.lean`). A statement that mixes
  both norms names the spectral one explicitly. Do not introduce local `frob2`, `frobNorm`,
  `gridFrobSq`, `l2Sq`: use `‖A‖ ^ 2`, or a weighted inner product from
  `LinearAlgebra/Frobenius/Defs.lean` (`weightedInner`, `WeightedMatrix`).
- **Abstract results** are stated on `E` with `⟪x, y⟫` (`open scoped RealInnerProductSpace`) and
  `‖x‖`. Matrices, Tucker tensors, tensor trains and function spaces are instances.
- **The scalar field is `ℝ`.** Complex problems (Schrödinger, complex symmetric) use the
  realification of a complex inner product space (`Re ⟪x, y⟫_ℂ`, `restrictScalars ℝ`), as in the
  `example` on `ℂⁿ` for `ODESolution.galerkin_energy_eq_of_skew` in `Foundations/Galerkin.lean`
  (projectors `K.starProjection.restrictScalars ℝ`). `RCLike 𝕜`
  is used where it already is (`Classical/SVD.lean`, `Classical/CourantFischer.lean`,
  `Classical/KyFan.lean`) and where complex linearity is part of the statement. The projector
  layer stays real (decision of 2026-11-09); it is connected to Mathlib's complex projections by
  `isOrthProj_iff_isSymmetricProjection` and `IsOrthProj.restrictScalars`.

## 6. Hypotheses

### 6.1 One property, one predicate

Single properties are unbundled `Prop`s, as in Mathlib:

| Predicate | Meaning | File |
|---|---|---|
| `ODESolution F y a b` | `y' = F t y` on `[a, b]` (continuity on `Icc`, right derivatives on `Ico`) | `Analysis/Defs.lean` |
| `IsLipschitzField F L` | `‖F t x - F t y‖ ≤ L * ‖x - y‖` for all `t x y` | `Analysis/Defs.lean` |
| `IsBoundedField F B` | `‖F t x‖ ≤ B` | `Analysis/Defs.lean` |
| `IsLipschitzOnTube F A a b ρ L` | the Lipschitz condition for `t ∈ [a, b]` and `‖x - A t‖ ≤ ρ`, `‖y - A t‖ ≤ ρ` | `Analysis/Defs.lean` |
| `IsBoundedOnTube F A a b ρ B` | `‖F t x‖ ≤ B` for `t ∈ [a, b]` and `‖x - A t‖ ≤ ρ` | `Analysis/Defs.lean` |
| `IsOneSidedLipschitzField F ℓ` | `⟪F t x - F t y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2`, any real `ℓ` | `Analysis/Defs.lean` |
| `IsOneSidedLipschitzOn F K ℓ` | the same for states in a set `K` | `Analysis/Defs.lean` |
| `IsDerivRHS F A t₀ t₁` | `F t Y = Ȧ(t)` for every state `Y` (exactness setting) | `Analysis/Defs.lean` |
| `IsOrthProj P` | `P` idempotent and symmetric | `LinearAlgebra/Projection/Defs.lean` |
| `IsObliqueProj P Q` | `P` an oblique projector onto `range Q` | `LinearAlgebra/Projection/Defs.lean` |

Nonnegativity of constants is a separate hypothesis (`hL : 0 ≤ L`), not part of the predicate.

### 6.2 Bundles

- `DLRAProblem F A a b ρ L B : Prop` (`DLRA/Defs.lean`) is the problem near its solution: fields
  `sol : ODESolution F A a b`, `L_nonneg : 0 ≤ L`, `B_nonneg : 0 ≤ B`,
  `lipschitz : IsLipschitzOnTube F A a b ρ L`, `bounded : IsBoundedOnTube F A a b ρ B`. Nothing is
  assumed about `F` outside the tube of radius `ρ` around `A`. The constants stay explicit
  arguments so that they can appear in conclusions. A globally Lipschitz and bounded field gives a
  `DLRAProblem` for every radius (`DLRAProblem.of_global`).
- New main theorems take the bundle. The theorems for globally Lipschitz and bounded fields
  (for example `bug_global_error`) keep the unbundled hypotheses `hF hL hB`.
- **Normal component.** Each theorem uses the weakest form it needs: along a trajectory
  (`hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε`, `Dynamics/ContinuousDLRA.lean`); inside a
  step (fields `kNormal`, `lNormal` of the step structures); for matrices on a region `D` of times
  and points `FactoredNormalBoundOn F r D ε` (all orthonormal `U`, `V` and all `S` with
  `(t, U * S * Vᵀ) ∈ D`), with the instances `MatrixBUG.FactoredNormalBound F r ε` (`D = univ`,
  `factoredNormalBound_iff_univ`) and `NearNormalBound F r ε t₀ t₁ Y ρ` (`nearNormalBound_iff`);
  the abstract form on `E` is `NormalBoundOn` (`factoredNormalBoundOn_iff_normalBoundOn`). The
  error theorems on a tube take `FactoredNormalBoundOn` on `tubeSet A a b ρ`.
- Stiff problems use `IsOneSidedLipschitzField F ℓ` directly; `ℓ` may be negative. There is no
  separate bundle.

### 6.3 Integrator steps

One step of a method is a `Prop` structure `Is<Method>Step` in projector form on `E`. The template
is `IsBUGStep` (`Integrators/BUG.lean`):

```lean
structure IsBUGStep (F : ℝ → E → E) (ε : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YK YL YS : ℝ → E) : Prop where
  projP₀ : IsOrthProj P₀      -- projP₀ projQ₀ projP₁ projQ₁
  comm₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)
  kSol : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁   -- substep: kSol, kStart
  kStart : YK t₀ = Y₀
  kCap : P₁ (YK t₁) = YK t₁                              -- capture replaces QR
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  -- lSol lStart lCap lNormal, sSol sStart likewise
```

- **Argument order:** field, tolerances (`ε ϑ η`), projectors (old, then new), times, start value,
  substep trajectories, computed values (`K₁ … Y₁`).
- **Field names:** `proj*` for `IsOrthProj`, `comm*`, `<sub>Sol`/`<sub>Start` for substeps,
  `<sub>Cap` for captures, `<sub>Normal` for normal-component bounds, `<sub>Err` for inexact
  substeps, `aug*` for augmentation, `trunc` for truncation. Each field has a docstring with its
  matrix meaning.
- **QR steps are capture hypotheses** (`P₁ (YK t₁) = YK t₁`, matrix form `U₁ * U₁ᵀ * K₁ = K₁`),
  never a particular QR algorithm. `MatrixBUG.kCap_of_qr` derives them from a QR factorization.
- **The algorithm without constants of the analysis.** `IsBUGStepCore` and `BasisUpdate`
  (`Integrators/BUGCore.lean`) state the step without the bound `ε`; `isBUGStep_iff` says that
  `IsBUGStep` is `IsBUGStepCore` together with the two normal bounds.
- **Matrix factor form** is a second structure at the level of `U S V` in the namespace of the
  method, which converts to the projector form: `MatrixBUG.IsStep` with
  `MatrixBUG.IsStep.isBUGStep`, `MatrixKSL.IsStep` with `MatrixKSL.IsStep.isKSLStep`, and
  `MatrixParallelBUG.IsStep` with `MatrixParallelBUG.IsStep.isParallelBUGStep`.
- **Step relation.** The method as a relation between the start and the result of a step is
  `stepRel` in the namespace of the method (`MatrixBUG.stepRel F r : StepRel (Matrix m n ℝ)`,
  `MatrixKSL.stepRel`, `MatrixParallelBUG.stepRel`). A method defined for all fields is a
  `StepMethod E`, a map from fields to step relations (`Integrators/Method.lean`).
- Variants extend the base structure (`IsRankAdaptiveBUGStep extends IsBUGStep`) or, where the
  substeps differ, reuse the same field names.

### 6.4 Runs and global errors

A run of a method is `IsRun M τ N Y` (`Integrators/Defs.lean`): `M : StepRel E` is the step
relation, `τ` a grid with `IsGrid τ N`, and `M (τ n) (τ (n + 1)) (Y n) (Y (n + 1))` holds for all
`n < N`. On the uniform grid, `IsRun M (uniformGrid t₀ h) N Y` is the same as
`∀ n < N, M (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1))` for `0 ≤ h`
(`isRun_uniformGrid_iff`). The older theorems state a run in this second form, with the step
structure in place of `M`, the update `Y (n + 1) = …` and exact solutions `Φ n` from
`(t₀ + n * h, Y n)` (for example `bug_global_error`).

The local error of a step is `HasLocalError F t₀ t₁ Y₀ Y₁ δ`: `‖Y₁ - Φ t₁‖ ≤ δ` for every exact
solution `Φ` on `[t₀, t₁]` with `Φ t₀ = Y₀`. Global errors are derived from local errors by the
theorems for all methods, never by a discrete Grönwall argument of the method file:

- on a general grid, from the local errors and the stability of the exact flow along the
  solutions `Φ n` (`FanStable.norm_sub_le`, `IsExactFan.norm_sub_le`; for a globally Lipschitz
  field `IsLipschitzField.norm_sub_le_of_hasLocalError`; all in `Integrators/GlobalError.lean`),
  and on the uniform grid by the Lady Windermere lemmas of `Foundations/Gronwall.lean`
  (`lady_windermere`, `lady_windermere_sum`, `lady_windermere_of_le`);
- for a `DLRAProblem`, the tube theorems of `Integrators/Tube.lean`
  (`IsRun.norm_sub_le_of_tube`, `IsRun.norm_sub_le_of_tube_uniformGrid`);
- for a method `M : StepMethod E` with existence of a step, invariance of a predicate `Adm` and
  locality (`StepMethod.IsTubeLocal M Adm κ`) and with a local error `h * c`,
  `StepMethod.IsTubeLocal.exists_run_norm_sub_le` gives a run and its error bound
  `exp (L * T) * δ + T * exp (L * T) * c`. The header of `Integrators/Method.lean` says how a new
  integrator is treated; `MatrixBUG.exists_run_norm_sub_le` is the model.

A method file proves the properties of one step and takes the run and the global error from these
theorems.

### 6.5 Binder order and names

For globally Lipschitz fields follow `bug_global_error`:
`(hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)`, tolerance signs (`hε`), grid
(`hh : 0 ≤ h`, `hhH : h ≤ H`), exact solution `hA`, steps `hstep`, updates `hY`, exact solutions on
the steps `hΦ hΦ₀`, initial error `hδ`. For a problem on a tube follow
`MatrixBUG.exists_run_norm_sub_le`: the problem `hP : DLRAProblem …`, continuity `hc`, normal bound
`hε` and its sign `hε₀`, grid (`hh`, `hhH`, `hNT : N * h ≤ T`), dimensions (`hrm`, `hrn`), start
value (`hY₀`, `hδ`), and last the smallness condition `hsmall`. Hypothesis names start with `h`
followed by the object (`hF`, `hP`, `hU`), and `hU : Uᵀ * U = 1` for orthonormality.

**Non-vacuity.** Every structure and every main theorem has an `example` or `exists_…` theorem
showing that its hypotheses can be satisfied with nontrivial data, built in CI.

## 7. Naming

Mathlib's rules apply (`https://leanprover-community.github.io/contribute/naming.html`):

- `Prop`-valued structures and predicates: UpperCamelCase, `Is…`/`Has…` prefix when it reads as
  "is a"/"has a" (`IsOrthProj`, `IsBUGStep`), otherwise an adjective or noun phrase
  (`FactoredNormalBoundOn`). Data-valued definitions: lowerCamelCase (`tangentProj`, `distLR`).
- Theorems: snake_case built from the lowerCamelCase names in the statement, conclusion first,
  `_of_` before hypotheses, `_iff` for equivalences, `_le`/`_lt`/`_eq` for the relation:
  `tangentProj_apply`, `isOrthProj_tangentProj`, `norm_sub_le_gronwallBound_of_oneSided`.
- Dot notation through the namespace of a type or structure: `IsOrthProj.norm_le`,
  `IsBUGStep.local_error_le`, `ODESolution.dlra_norm_sub_le_gronwallBound`.
- Namespaces. A method in matrix factor form has a namespace of its own (`MatrixBUG`, `MatrixKSL`,
  `MatrixParallelBUG`), and the same names are used inside each of them: `IsStep`, `stepRel`,
  `isTubeLocal_stepRel`, `exists_run_norm_sub_le`. A new file does not open a namespace that only
  names the file. Older core files do (`LeanDLRA.EckartYoung`, `LeanDLRA.KyFan`,
  `LeanDLRA.MeanSquare`); these namespaces are not a model. A catalogue module has a namespace
  for its paper or problem (for example `LeanDLRA.Literature.P2002_02356`) and keeps it when it
  is promoted. Operations on matrices go into the namespace `Matrix` (`Matrix.pinv`,
  `Matrix.gramPinv` in `LinearAlgebra/Factorization/Defs.lean`).
- Conversions between structures: `toX` (`IsRankAdaptiveBUGStep.toInexact`,
  `IsBUGStep.toTucker`). The conversion of a step in matrix factor form to the step structure in
  projector form is named after that structure (`MatrixBUG.IsStep.isBUGStep`,
  `MatrixKSL.IsStep.isKSLStep`).
- Main error results keep the readable form `<method>_local_error_le` / `<method>_global_error_le`
  with the method in lowerCamelCase (`bug_local_error_le`, `ksl_global_error_le`,
  `rankAdaptiveBUG_global_error_le`), or the dot form on the step structure
  (`IsBUGStep.local_error_le`). The theorem that gives a run with its error bound is
  `exists_run_norm_sub_le` in the namespace of the method. Established names of classical results
  are fine (`lady_windermere`, `IsOrthProj.diracFrenkel_tfae`, `gronwallBound`). Numbers of a
  paper (theorem, lemma, equation), arXiv identifiers and codes of the catalogue are not part of
  a new name in the core. The declarations listed in [CORRECTIONS.md](CORRECTIONS.md) keep their
  names.
- No primes for a second copy of a statement; a prime is only a Mathlib-style variant (e.g.
  explicit vs implicit arguments) next to the unprimed one.
- No new Unicode subscripts in declaration names (`bugC₁` stays, new constants are spelled out).

Examples from the library. The first column gives names that exist; the second column shows how
the rules would name the statement and is not a list of declarations.

| Name in the library | Name by the rules | Why |
|---|---|---|
| `lemma_2_8_matrix_core` (`Literature/Stochastic/P2002_02356a.lean`) | `exists_unique_orthogonal_of_transpose_mul_eq` | name the statement, not the label of the paper |
| `remark311_ceaType` (`Literature/Applications/P2405_18094a.lean`) | `norm_sub_le_of_isMinOn_of_sqrt_bounds` | same |
| `algorithm_1_psd` (`Literature/Stiff/P1705_10175a.lean`) | `IsAlg1Step.posSemidef_iterate`, with `IsAlg1Step` renamed after the method | same; "Alg1" is a label of the paper too |
| `rk1` (`Literature/HighOrder/P2610_11747b.lean`) | `rankOneProj` | same body as the core definition |
| `IsDefectBUGStep` in `Integrators/InexactSubsteps.lean` and in `OpenProblems/Stability/Part1Defs.lean` | two different names | one name, two different structures |
| `specNorm_add_le` in `Novel/OpHO38.lean`, `Novel/OpTR37.lean`, `Literature/HighOrder/P2608_17157a.lean` | `WeylSingular.specNorm_add_le` | the core has the lemma |
| `exists_orthogonal_diagonalisation` in `Literature/Kinetic/P1801_01103a.lean` and `Literature/Applications/P2110_13481a.lean` | one lemma, next to Mathlib's `Matrix.IsHermitian.spectral_theorem` | one statement, one declaration |

## 8. Docstrings and file headers

Every file starts with a module docstring. The layout is Mathlib's:

```lean
/-!
# Robust error bound for the BUG integrator

One paragraph: what the file proves, in DLRA terms.

## Main definitions
* `IsBUGStep`: one step of the BUG integrator in projector form.

## Main results
* `bug_global_error_le`: `‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ ε + c₂ h` [CerutiLubich2022, Thm. 4].

## Implementation notes
Projector form; QR steps are capture hypotheses.

## References
* [CerutiLubich2022]
-/
```

- The sections come in this order: `## Main definitions`, `## Main results`, then the optional
  sections `## Notation`, `## Implementation notes`, `## TODO`, `## References`, `## Tags`.
  "Main definitions" is omitted when the file has none, "References" when it cites no paper.
- The header lists only declarations that exist in the file, under their names.
- `## Implementation notes` says how the file states its objects and where it differs from the
  paper it cites. `## TODO` says what the file does not prove; there are no other headings for
  this ("What remains open", "Not formalised here").
- An open problem of the survey is named by its tag (form `OP-HO-14`). The tags are the
  identifiers of `docs/survey/open-problems.json`; the header of a file that uses tags names this
  file once.
- A docstring is required for every definition, for every theorem that a page of `docs/` names,
  and for every theorem with a hypothesis that needs explanation. No docstring is required for a
  lemma that only rewrites or unfolds a definition (simp lemmas and lemmas ending in `_iff`,
  `_apply`, `_def`).
- The first sentence of a docstring says what the declaration states, in words, with formulas in
  backticks. Then the citation. Then every deviation from the paper: stronger hypothesis, weaker
  conclusion, finite dimensions instead of `L²`, a step of the paper taken as a hypothesis,
  different constants.
- A theorem that assumes a step the paper proves is **conditional**: the docstring says
  "Conditional on …", and the hypothesis is named after that step.
- Bold names (`**Robust global error bound**`) only for named results. No "we", no proof
  narrative, no history of the file.
- Docstrings make no claim of novelty; [NOVEL.md](NOVEL.md) is the place for the comparison with
  the literature. A declaration that belongs to an entry of [CORRECTIONS.md](CORRECTIONS.md) is
  listed there by name.
- Docstrings cite papers by key (§9), declarations by name and tracked files by path. They do not
  cite planning documents.

## 9. Citing papers

- All papers are entries of `docs/references.bib`. The key is the surnames of up to three authors
  followed by the year (`CerutiLubich2022`, `CerutiKuschLubich2022`), or
  `<FirstSurname>EtAl<Year>` for four or more authors (`CarrelEtAl2025`). ASCII only
  (`KochLubich2007`). The year is the journal year if the paper is published, else the arXiv
  year. Clashes get `a`, `b`. An entry records the arXiv identifier in the field `eprint` when
  the paper has one.
- Docstrings cite `[Key]` or `[Key, Thm. 4]`, `[Key, Lemma 2.8]`, `[Key, eq. (3.5)]`,
  `[Key, §3.1]`, `[Key, Alg. 2]`, `[Key, Remark 3.11]`.
- The arXiv identifier belongs to the entry of the bibliography. It does not appear in core
  docstrings or in names of the core. Where a core docstring still has an identifier, it is
  replaced by the key when the file is changed.
- `scripts/docgen.py keys` lists the keys that core docstrings and the pages of `docs/` use and
  that have no entry in `docs/references.bib`.

## 10. Results of single papers

A result of a single paper that is not stated in the core definitions is a module of the catalogue
(folders `Literature/`, `OpenProblems/`, `Novel/`, `Corrections/`; see
[STRUCTURE.md](STRUCTURE.md)). For such a module:

1. The header names the paper, the part of it that was read, what is proved, what is not, and
   which definitions of the library the statements use.
2. Each statement says how it relates to the printed one: *verbatim*, *stronger hypothesis*,
   *weaker conclusion* or *conditional on …*. A docstring says "this is Theorem X of [Key]" only
   after the statement was compared with the printed paper.
3. Local definitions only for objects the core does not have, each with a docstring sentence
   saying why the core definition does not fit.
4. `example`s show that the hypotheses of the paper can be satisfied.

A module is promoted to the core once its definitions are the core definitions or are proven
equal to them by bridging lemmas ([STRUCTURE.md](STRUCTURE.md), "Promotion"). A theorem in the
form of the paper that differs from the core statement is then proved from the core theorem, and
proofs that other files need move to the core file of the topic.

## 11. Moves, renames and deprecations

- **Moves** of a declaration between files are free: the name and the statement do not change.
  Keep binder order, implicit arguments and instance arguments identical, and diff the dumped types
  of the moved definitions before and after (a different `variable` block can add a
  `[DecidableEq m]` argument and change every statement that uses the definition).
- **Old module paths** stay as files that only `import` the new module until all internal imports
  are updated; `deprecated_module (since := "…")` is added only after that, because a deprecation
  warning in an importing file fails the `--wfail` build.
- **Renames** leave `@[deprecated (since := "YYYY-MM-DD")] alias oldName := newName` directly after
  the new declaration, in the same file, until the release after v0.1.0. Internal uses are renamed
  in the same change (deprecated names warn, and warnings fail the build).
- **Renaming a definition changes the statement hash of every theorem that mentions it.** Each such
  rename is entered in the rename map `docs/renames.json` (old constant → new constant), which
  `scripts/fidelity.py` and the gate read, and the change lists the number of affected
  statements. Theorem renames update `docs/statements.json`.
- A `structure` rename keeps its field names; renamed fields get deprecated theorem aliases.

## 12. Proof hygiene

- No `import Mathlib` in library files; import what is used (`lake exe shake`). The reason is
  build time.
- No blanket `set_option linter.* false`; use `omit … in` or fix the signature.
- `set_option maxHeartbeats` only with a comment saying why.
- Helpers used once are `private`. `example`s for non-vacuity stay in the file of the definition.

## 13. Checklist for a new or moved file

- [ ] Imports only lower layers; no `import Mathlib`.
- [ ] Definitions only in a `Defs.lean`, or `private`, or bridged with a reason.
- [ ] Statements use core definitions; notation as in §4; Frobenius scoped.
- [ ] Names follow §7; no paper numbers.
- [ ] Module header and docstrings as in §8; citations as in §9.
- [ ] Non-vacuity examples for new structures and main theorems.
- [ ] Renames: deprecated aliases, rename map entry, affected statement count in the batch notes.
