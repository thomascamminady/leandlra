import LeanDLRA.LinearAlgebra.Frobenius.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Definitions: low-rank matrices and matrices given by their columns

The vocabulary of the low-rank layer (`LinearAlgebra/LowRank/`). Dynamical low-rank approximation
works on the set `M_{≤ r} = {Y : rank Y ≤ r}` of real `m × n` matrices of rank at most `r`, with
the Frobenius norm (`open scoped LeanDLRA.Frobenius`). Its basic quantities are the distance
`dist(X, M_{≤ r})` of a matrix to this set and the `ε`-rank, the smallest rank within distance `ε`.
Orthonormal bases of column spaces are handled through the columns of a matrix as vectors of
`EuclideanSpace ℝ m`.

The theorems about these objects are in `LeanDLRA/Matrix/LowRankDistance.lean` (distance, closedness
of `M_{≤ r}`, existence of best approximations, `ε`-rank), `LeanDLRA/Matrix/Orthonormal.lean`
(orthonormal bases capturing a column space) and `LeanDLRA/Classical/WeylSingular.lean`
(singular-value tails).

## Main definitions

* `LeanDLRA.lowRankSet m n r`: the set `M_{≤ r}` of `m × n` matrices of rank at most `r`.
* `LeanDLRA.distLR r X`: the Frobenius distance `dist(X, M_{≤ r})`, defined as an infimum.
* `LeanDLRA.epsRank ε X`: the `ε`-rank `min {k : dist(X, M_{≤ k}) ≤ ε}`.
* `LeanDLRA.colSpan A`: the span of the columns of `A` in `EuclideanSpace ℝ m`.
* `LeanDLRA.ofCols u`: the matrix whose `j`-th column is the Euclidean vector `u j`.
* `LeanDLRA.WeylSingular.tailNorm A r = (∑_{r ≤ l < n} σ_l(A)²)^{1/2}`: the singular-value tail,
  the distance of `A` to the matrices of rank at most `r` (`WeylSingular.tailNorm_eq_infDist`).

## Implementation notes

`distLR` and `epsRank` are defined without singular values: by Eckart–Young, `distLR r X` is the
singular-value tail `tailNorm X r`, but this identification is not used in the definitions.

The name `WeylSingular.tailNorm` is kept from the file that uses it. `tailNorm` lives here and not
in `LeanDLRA/LinearAlgebra/SVD/Defs.lean` because a definition body abstracts its proof arguments
into auxiliary theorems that are shared within a module: next to
`EckartYoung.rightSingularVectors` (or `KyFan.podBasis`) it would reuse their auxiliary proofs and
the body would change.
-/

open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### Columns as Euclidean vectors -/

section Columns

open Submodule

variable {m n ι : Type*}

/-- The span of the columns of `A`, as a subspace of `EuclideanSpace ℝ m`. -/
def colSpan (A : Matrix m n ℝ) : Submodule ℝ (EuclideanSpace ℝ m) :=
  span ℝ (Set.range fun j => WithLp.toLp 2 (A.col j))

/-- The matrix whose `j`-th column is the Euclidean vector `u j`. -/
def ofCols (u : ι → EuclideanSpace ℝ m) : Matrix m ι ℝ := Matrix.of fun i j => u j i

/-- `ofCols u i j = u j i`. -/
@[simp] lemma ofCols_apply (u : ι → EuclideanSpace ℝ m) (i : m) (j : ι) :
    ofCols u i j = u j i := rfl

end Columns

/-! ### The low-rank set, the distance to it and the `ε`-rank -/

section LowRank

open Set Metric

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The set `M_{≤ r} = {Y ∈ ℝ^{m×n} : rank Y ≤ r}` of matrices of rank at most `r`. -/
def lowRankSet (m n : Type*) [Fintype n] (r : ℕ) : Set (Matrix m n ℝ) := {Y | Y.rank ≤ r}

omit [Fintype m] in
/-- `Y ∈ M_{≤ r} ↔ rank Y ≤ r`. -/
@[simp] lemma mem_lowRankSet {r : ℕ} {Y : Matrix m n ℝ} : Y ∈ lowRankSet m n r ↔ Y.rank ≤ r :=
  Iff.rfl

/-- The Frobenius distance `dist(X, M_{≤ r}) = inf {‖X - Y‖ : rank Y ≤ r}` of `X` to the set of
matrices of rank at most `r`. By the Eckart–Young theorem this is the norm of the tail
`(σ_{r+1}² + σ_{r+2}² + ⋯)^{1/2}` of the singular values; the theorems of
`LeanDLRA/Matrix/LowRankDistance.lean` are proved from the definition as an infimum. -/
noncomputable def distLR (r : ℕ) (X : Matrix m n ℝ) : ℝ := infDist X (lowRankSet m n r)

/-- The **`ε`-rank** `rank_ε(X) = min {k : dist(X, M_{≤ k}) ≤ ε}`. For the Frobenius norm this is
(by Eckart–Young) the rank selected by tolerance truncation of the singular values
`(∑_{j > k} σ_j²)^{1/2} ≤ ε`, as in the truncation step of the rank-adaptive BUG integrator
[CerutiKuschLubich2022]. For `ε < 0` the defining set is empty and the value is `0` by
convention; all results assume `ε ≥ 0`. -/
noncomputable def epsRank (ε : ℝ) (X : Matrix m n ℝ) : ℕ := sInf {k | distLR k X ≤ ε}

end LowRank

end LeanDLRA

/-! ### The singular-value tail -/

section Tail

open Matrix WithLp Module Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.WeylSingular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

open scoped LeanDLRA.Frobenius in
/-- The **singular-value tail** `τ_r(A) = (∑_{r ≤ l < n} σ_l(A)²)^{1/2}`, the Frobenius error of
the best rank-`r` approximation. -/
noncomputable def tailNorm (A : Matrix m n ℝ) (r : ℕ) : ℝ :=
  √(∑ l ∈ Ico r (Fintype.card n), (toEuclideanLin A).singularValues l ^ 2)

end LeanDLRA.WeylSingular

end Tail

/-! ### Non-vacuity -/

/-- The zero matrix lies in every low-rank set. -/
example (r : ℕ) : (0 : Matrix (Fin 2) (Fin 3) ℝ) ∈ LeanDLRA.lowRankSet (Fin 2) (Fin 3) r := by
  simp
