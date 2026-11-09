# LeanDLRA conventions

Status: written 2026-11-09 as step 2 of `wip/PLAN.md`. New and moved code is reviewed against this
page. Where the code on `main` still differs, `wip/UNIFY.md` says how and in which batch it is
migrated. Names marked *(to add)* do not exist yet; everything else names existing declarations.

## 1. Principles

1. **Correct before tidy.** A move, rename or refactor never changes what a theorem says without
   being listed. Every batch keeps: zero warnings, standard axioms only, kernel replay,
   `scripts/fidelity.py` at 489/489 (through the rename map of §11).
2. **One definition per concept.** A concept is defined once, in a `Defs.lean` (§3). A second
   definition of the same object is replaced by the first. A *different* object gets its own name.
3. **Chain only what provably means the same.** Two definitions are merged only after a Lean
   lemma `local = core` (or `local ↔ core`). If only one direction holds, keep both and prove the
   implication. If neither holds, keep two names, each docstring says how they differ, and an
   `example` separates them.
4. **Mathlib style.** Mathlib's naming, docstring and file-header conventions apply unless this page
   says otherwise. Do not redefine what Mathlib has.

## 2. Layers and folders

The library is one theory in layers. A file imports Mathlib and files of its own or a lower layer,
never a higher one.

| # | Folder | Owns |
|---|---|---|
| 1 | `LinearAlgebra/` | Frobenius inner product and matrix CLMs; orthogonal and oblique projectors (`IsOrthProj`, `leftProj`, `rightProj`, `rankOneProj`, `obliqueProj`); orthonormal bases, QR data, pseudoinverses; SVD, Eckart–Young, Ky Fan, Weyl, Courant–Fischer; low-rank sets (`lowRankSet`, `distLR`, `epsRank`); DEIM / interpolation |
| 2 | `Analysis/` | `ODESolution`, `IsLipschitzField`, `IsBoundedField`, `IsOneSidedLipschitzField`; existence; Grönwall (continuous, discrete, Lady Windermere); localization in tubes; Galerkin projections of ODEs; energy estimates; Butcher tableaux |
| 3 | `FixedRank/` | the tangent/normal calculus (`tangent`, `normal`), `tangentProj`, oblique tangent projectors, curvature of the fixed-rank manifold, gauge ODEs |
| 4 | `DLRA/` | the projected equation `Ẏ = P(t) F(t, Y)`; Dirac–Frenkel; `DLRAProblem` *(to add)* and the normal-component bounds; continuous error bounds and quasi-optimality |
| 5 | `Integrators/` | the step framework (`Integrators/Defs.lean`), one folder per method: `ProjectorSplitting/`, `BUG/`, `AugmentedBUG/`, `ParallelBUG/`, `RankAdaptive/`, `HighOrder/`, `Implicit/`, `Randomized/`, `Conservation/` |
| 6 | `Tensor/` | Tucker, tensor trains, tree tensor networks, and their integrators |
| 7 | `Kinetic/`, `Stochastic/`, `Training/`, `Filtering/`, `Control/` | applications; they import layers 1–6, not each other |
| – | `Counterexamples/`, `References/`, `Examples/` | refuted claims; one file per paper (§10); worked examples |

A result goes into the **lowest** layer that can state it. Paper results that are special cases
of a core theorem go into `References/`, not into a topic folder.

Until the move (PLAN step 3) is done, the current folders map as follows: `Foundations/` →
`Analysis/` (`Projector.lean` → `LinearAlgebra/` and `FixedRank/`); `Matrix/` →
`LinearAlgebra/` and `FixedRank/`; `Classical/` → `LinearAlgebra/SVD/`; `Dynamics/` → `DLRA/`;
`Stability/` → `Analysis/Energy` and `Integrators/Conservation/`; `Stiff/`, `HighOrder/`,
`Randomized/` → `Integrators/…`; `Stochastic/KalmanBucy.lean` → `Filtering/`; `Novel/`,
`OpenProblems/`, `Research/`, `Literature/` are dissolved into the topics and `References/`.

## 3. The `Defs.lean` rule

- Every public `def`, `abbrev`, `structure`, `class`, `inductive` and non-scoped `instance` lives in
  the `Defs.lean` of its topic: `LeanDLRA/<Topic>/Defs.lean`, or `LeanDLRA/<Topic>/<Sub>/Defs.lean`
  where a topic needs several (the list is in `wip/UNIFY.md` §a). `LeanDLRA/Defs.lean` imports all
  of them.
- A `Defs.lean` contains the definitions, their basic API (`_apply`, `_def`, `@[simp]` lemmas,
  `ext`, conversion lemmas to Mathlib such as `isOrthProj_starProjection`, today proved three
  times: `MeanSquare.`, `Novel.KineticAP.`, and privately in `Dynamics/ContinuousDLRA.lean`), and
  one `example` per
  structure showing that it can be satisfied. Theorems with real proofs go elsewhere.
- A `Defs.lean` imports Mathlib and lower-layer `Defs.lean` files only, so that importing the
  vocabulary stays cheap.
- Exempt: `private` definitions, definitions inside proofs, concrete example data inside
  `namespace …Examples` or `Counterexamples/` (marked `private` where possible), and
  auto-generated declarations (`match_1`, `eq_1`).
- Before adding a definition, search `LeanDLRA/Defs.lean` and Mathlib. If the object exists, use
  it. If the paper's object differs, define it locally from core pieces, prove the bridging lemma
  in the same file, and say in the docstring why the core one does not fit.
- Concrete vectors and matrices are not concepts: write `Pi.single i 1`,
  `EuclideanSpace.single i 1` or `Matrix.single i j 1` instead of a local `e₁` (19 copies today).

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
| `t₀ N T` | grid `t₀ + n * h`, `n ≤ N`, `n * h ≤ T` | time grid and horizon |
| `L B ℓ Lₜ` | `ℝ` | Lipschitz constant, bound of `F`, one-sided Lipschitz constant, time-Lipschitz constant |
| `δ ϑ η` | `ℝ` | initial error, truncation tolerance, substep inexactness |
| `ρ` | `ℝ` | lower bound of the smallest nonzero singular value |
| `Φ` | `ℕ → ℝ → E` | exact flows started at the numerical values `(tₙ, Y n)` |
| `C` | `E →L[ℝ] E` | moment projector in conservation results |

- Grid points are written `t₀ + n * h` and `t₀ + (n + 1) * h`, with `(n : ℝ)` casts left to
  elaboration. Intervals: `Icc` for continuity and hypotheses on closed intervals, `Ico` for
  right derivatives, as in `ODESolution`.
- Projector applications are written `P (Q x)` and `(1 - P) x`, not `(P * Q) x`.
- Matrix products associate to the left: `U * S * Vᵀ`. Transpose is `ᵀ` (`open scoped Matrix`).
- Orthonormal columns are the equation `Uᵀ * U = 1`; do not add a predicate for it.

## 5. Norms and scalars

- **Matrices carry the Frobenius norm and inner product.** They come from
  `open scoped LeanDLRA.Frobenius` (scoped instances in `Matrix/Frobenius.lean`); never make them
  global. Then `‖A‖` is the Frobenius norm and `⟪A, B⟫ = ∑ i j, A i j * B i j`.
- **The spectral norm** is `Curvature.specNorm A`, which is Mathlib's L2 operator norm
  (`specNorm_eq_l2`). A statement that mixes both norms names the spectral one explicitly. Do not
  introduce local `frob2`, `frobNorm`, `gridFrobSq`, `l2Sq`: use `‖A‖ ^ 2`, or a weighted inner
  product from `LinearAlgebra/Frobenius/Defs.lean`.
- **Abstract results** are stated on `E` with `⟪x, y⟫` (`open scoped RealInnerProductSpace`) and
  `‖x‖`. Matrices, Tucker tensors, tensor trains and function spaces are instances.
- **The scalar field is `ℝ`.** Complex problems (Schrödinger, complex symmetric) use the
  realification of a complex inner product space (`Re ⟪x, y⟫_ℂ`, `restrictScalars ℝ`), as in the
  `example` on `ℂⁿ` for `ODESolution.galerkin_energy_eq_of_skew` in `Foundations/Galerkin.lean`
  (projectors `K.starProjection.restrictScalars ℝ`). `RCLike 𝕜`
  is used where it already is (`Classical/SVD.lean`, `Classical/CourantFischer.lean`,
  `Classical/KyFan.lean`) and where complex linearity is part of the statement. The projector
  layer stays real (decision 2026-11-09); it is connected to Mathlib's complex projections by
  `isOrthProj_iff_isSymmetricProjection` and `IsOrthProj.restrictScalars`.

## 6. Hypotheses

### 6.1 One property, one predicate

Single properties are unbundled `Prop`s, as in Mathlib:

| Predicate | Meaning | File |
|---|---|---|
| `ODESolution F y a b` | `y' = F t y` on `[a, b]` (continuity on `Icc`, right derivatives on `Ico`) | `Foundations/ODE.lean` |
| `IsLipschitzField F L` | `‖F t x - F t y‖ ≤ L * ‖x - y‖` for all `t x y` | `Foundations/ODE.lean` |
| `IsBoundedField F B` | `‖F t x‖ ≤ B` | `Foundations/ODE.lean` |
| `IsOneSidedLipschitzField F ℓ` | `⟪F t x - F t y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2`, any real `ℓ` | `Foundations/OneSided.lean` |
| `IsOneSidedLipschitzOn F K ℓ` | the same on a set `K` | `Foundations/OneSided.lean` |
| `IsOrthProj P` | `P` idempotent and symmetric | `Foundations/Projector.lean` |
| `IsObliqueProj P Q` | `P` an oblique projector onto `range Q` | `Matrix/Interpolation.lean` |
| `IsDerivRHS F A t₀ t₁` | `F t Y = Ȧ(t)` for every state `Y` (exactness setting) | `Integrators/Exactness.lean` |

Nonnegativity of constants is a separate hypothesis (`hL : 0 ≤ L`), not part of the predicate.

### 6.2 Bundles

- `DLRAProblem F L B : Prop` *(to add, `DLRA/Defs.lean`)*: fields `L_nonneg : 0 ≤ L`,
  `lipschitz : IsLipschitzField F L`, `bounded : IsBoundedField F B`. The constants stay explicit
  arguments so that they can appear in conclusions. Every main theorem takes the bundle
  (decision 2026-11-09); unbundled forms remain only as helper lemmas inside proofs, and catalogue
  statements are tracked through the rename map of §11.
- **Normal component.** There are three forms, and each theorem uses the weakest one it needs:
  along a trajectory (`hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε`, `Dynamics/ContinuousDLRA`);
  inside a step (fields `kNormal`, `lNormal` of the step structures); for matrices
  `MatrixBUG.FactoredNormalBound F r ε` (all orthonormal `U`, `V`, all `S`) and its localized form
  `NearNormalBound F r ε t₀ t₁ Y ρ`. Implications go from the global to the local forms
  (`nearNormalBound_of_factored`, `MatrixBUG.IsStep.isBUGStep`).
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
- **Matrix factor form** is a second structure at the level of `U S V` that converts to the
  projector form: today `MatrixBUG.IsStep` with `MatrixBUG.IsStep.isBUGStep`; target name
  `IsFactoredBUGStep` with `IsFactoredBUGStep.toIsBUGStep` (`wip/UNIFY.md` §b).
- Variants extend the base structure (`IsRankAdaptiveBUGStep extends IsBUGStep`) or, where the
  substeps differ, reuse the same field names. Shared K/L data become a parent structure
  *(to add, `wip/UNIFY.md` §a)*.

### 6.4 Runs and global errors

A run is stated as `∀ n < N, Is<Method>Step … (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) …` with the
update `Y (n + 1) = …` and exact flows `Φ n` from `(t₀ + n * h, Y n)`. Global errors are derived
from local errors through the Lady Windermere lemmas of `Foundations/Gronwall.lean`
(`lady_windermere`, `lady_windermere_sum`, `lady_windermere_of_le`), and later through the
general theorem `LocalErrorBound.norm_sub_le` *(to add)*. A method file proves only its local
error and its stability, never its own discrete Grönwall argument.

### 6.5 Binder order and names

Follow `bug_global_error`: `(hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)`,
tolerance signs (`hε`), grid (`hh : 0 ≤ h`, `hhH : h ≤ H`), exact solution `hA`, steps `hstep`,
updates `hY`, flows `hΦ hΦ₀`, initial error `hδ`. Hypothesis names start with `h` followed by the
object (`hF`, `hP`, `hU`), and `hU : Uᵀ * U = 1` for orthonormality.

**Non-vacuity.** Every structure and every main theorem has an `example` or `exists_…` theorem
showing that its hypotheses can be satisfied with nontrivial data, built in CI.

## 7. Naming

Mathlib's rules apply (`https://leanprover-community.github.io/contribute/naming.html`):

- `Prop`-valued structures and predicates: UpperCamelCase, `Is…`/`Has…` prefix when it reads as
  "is a"/"has a" (`IsOrthProj`, `IsBUGStep`), otherwise an adjective or noun phrase
  (`FactoredNormalBound`). Data-valued definitions: lowerCamelCase (`tangentProj`, `distLR`).
- Theorems: snake_case built from the lowerCamelCase names in the statement, conclusion first,
  `_of_` before hypotheses, `_iff` for equivalences, `_le`/`_lt`/`_eq` for the relation:
  `tangentProj_apply`, `isOrthProj_tangentProj`, `norm_sub_le_gronwallBound_of_oneSided`.
- Dot notation through the namespace of a type or structure: `IsOrthProj.norm_le`,
  `IsBUGStep.local_error_le`, `ODESolution.dlra_norm_sub_le_gronwallBound`. Do not use a
  namespace that only names a file (`MatrixBUG`, `Curvature`, `EckartYoung`, `Novel.OpTR37`,
  `Literature.P2001_08599`).
- Conversions between structures: `toX` (`IsFactoredBUGStep.toIsBUGStep`), Mathlib style.
- Main error results keep the readable form `<method>_local_error_le` / `<method>_global_error_le`
  with the method in lowerCamelCase (`bug`, `ksl`, `parallelBUG`, `rankAdaptiveBUG`), or the dot
  form on the step structure. Established names of classical results are fine (`lady_windermere`,
  `IsOrthProj.diracFrenkel_tfae`, `gronwallBound`); paper numbers, arXiv ids and catalogue codes
  are not.
- No primes for a second copy of a statement; a prime is only a Mathlib-style variant (e.g.
  explicit vs implicit arguments) next to the unprimed one.
- No new Unicode subscripts in declaration names (`bugC₁` stays, new constants are spelled out).

Bad → good, from this library:

| Current | Target | Why |
|---|---|---|
| `lemma_2_8_matrix_core` (`Literature/Stochastic/P2002_02356a.lean`) | `exists_unique_orthogonal_of_transpose_mul_eq` | name the statement, not the paper label |
| `remark311_ceaType` (`Literature/Applications/P2405_18094a.lean`) | `norm_sub_le_of_isMinOn_of_sqrt_bounds` (docstring: conditional on (3.7)) | same |
| `algorithm_1_psd` (`Literature/Stiff/P1705_10175a.lean`) | `IsAlg1Step.posSemidef_iterate`, with `IsAlg1Step` renamed after the method | same; "Alg1" is a paper label too |
| `pinvL`, `pinv`, `pinvT`, `gramPinv` (five files) | `Matrix.gramPinv` | one concept, one name, `Matrix.` namespace for matrix operations |
| `MatrixBUG.IsStep`, `MatrixKSL.IsStep`, `MatrixParallelBUG.IsStep` | `IsFactoredBUGStep`, `IsFactoredKSLStep`, `IsFactoredParallelBUGStep` | `IsStep` exists 12 times; the namespace names a file |
| `MatrixBUG.IsStep.isBUGStep` | `IsFactoredBUGStep.toIsBUGStep` | conversion naming |
| `InexactSubsteps.IsDefectBUGStep` vs `OpenProblems.Stability.IsDefectBUGStep` | `IsCaptureDefectBUGStep` vs `IsInexactSubstepBUGStep` | one name, two meanings |
| `rk1` (`Literature/HighOrder/P2610_11747b.lean`) | `rankOneProj` | same body as the core definition |
| `specNorm_add_le` (three files) | `norm_add_le` after `specNorm_eq_l2` | Mathlib has it |
| `exists_orthogonal_diagonalisation` (two files) | Mathlib's `Matrix.IsHermitian.spectral_theorem` | Mathlib has it |
| `theorem_5_1_printed_false` (`Literature/Kinetic/P2212_12012a.lean`) | `Counterexamples.not_…` naming what fails | the conclusion is a negation |

## 8. Docstrings and file headers

Every file starts with a module docstring:

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

- "Main definitions" is omitted when there are none; "Implementation notes" and a section
  "Differences from the literature" are added when needed.
- Every public declaration has a docstring (Mathlib's `docBlame`). The first sentence says what the
  declaration states, in words, with formulas in backticks. Then the citation. Then every
  deviation from the paper: stronger hypothesis, weaker conclusion, finite dimensions instead of
  `L²`, a paper step taken as a hypothesis, different constants.
- A theorem that assumes a step the paper proves is **conditional**: the docstring says
  "Conditional on …", and the hypothesis is named after that step.
- Bold names (`**Robust global error bound**`) only for named results. No "we", no proof
  narrative, no history of the file.
- New results say "(new)" and give the `docs/NOVEL.md` entry. Corrections link to the
  `Counterexamples/` declaration and `docs/CORRECTIONS.md`.

## 9. Citing papers

- All papers are entries of `docs/references.bib` (created in PLAN step 6). The key is the
  surnames of up to three authors followed by the year (`CerutiLubich2022`,
  `CerutiKuschLubich2022`), or `<FirstSurname>EtAl<Year>` for four or more. ASCII only
  (`KochLubich2007`). The year is the journal year if published, else the arXiv year. Clashes get
  `a`, `b`. Each entry records `eprint` (arXiv id) and the version checked against the PDF.
- Docstrings cite `[Key]` or `[Key, Thm. 4]`, `[Key, Lemma 2.8]`, `[Key, eq. (3.5)]`,
  `[Key, §3.1]`, `[Key, Alg. 2]`, `[Key, Remark 3.11]`.
- arXiv ids appear only in `docs/references.bib` and in the header of a `References/` file, never
  in core docstrings or names.

## 10. `References/` entries

One file per paper, `References/<Key>.lean`, namespace `LeanDLRA.References.<Key>`. It contains:

1. A module header: full citation, arXiv id and version checked, who checked it and when.
2. A table "paper statement → library declaration → status", with status one of *verbatim*,
   *stronger hypothesis*, *weaker conclusion*, *conditional on …*, *not formalized*, *corrected
   (see `Counterexamples/…`)*.
3. A theorem in the paper's own form only where it differs from the core statement, proved in a
   few lines from the core theorem. Proofs longer than about 20 lines move to the core.
4. Local definitions only for objects the core does not have, each with its bridging lemma and a
   docstring sentence saying why the core definition does not fit.
5. `example`s showing that the paper's hypotheses can be satisfied.

An entry may say "this is Theorem X of [Key]" only after the statement was checked against the
printed PDF (PLAN, zeroth principle).

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
  in the same batch (deprecated names warn, and warnings fail the build).
- **Renaming a definition changes the statement hash of every theorem that mentions it.** Each such
  rename is entered in the rename map read by `scripts/fidelity.py` (old constant → new constant),
  and the batch lists the number of affected statements. Theorem renames update
  `docs/statements.json`.
- A `structure` rename keeps its field names; renamed fields get deprecated theorem aliases.

## 12. Proof hygiene

- No `import Mathlib` in library files (29 today); import what is used (`lake exe shake`).
- No blanket `set_option linter.* false` (145 today, mostly `unusedDecidableInType`,
  `unusedFintypeInType`, `unusedSectionVars`); use `omit … in` or fix the signature.
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
