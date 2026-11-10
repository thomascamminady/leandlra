import LeanDLRA.LinearAlgebra.LowRank.Defs
import LeanDLRA.LinearAlgebra.Projection.Defs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Definitions: pseudoinverses, factorizations, and the projectors built from them

The vocabulary of layer 1 (`LinearAlgebra/`) for generalized inverses. Low-rank integrators meet
pseudoinverses in two forms: the **Moore–Penrose inverse** `A⁺`, defined for every matrix by the
four Penrose equations, and the **Gram formula** `(Aᵀ A)⁻¹ Aᵀ`, which papers write as `A⁺` (or
`A†`) for matrices of full column rank (bases `U`, sketches `Ω`, factors `K = U S`). This file
defines both, proves that the Penrose equations have exactly one solution, and characterizes
exactly when the two agree. The same holds for the projectors built from them: the orthogonal
projector `A A⁺` onto the column space, and the Gram formula `A (Aᵀ A)⁻¹ Aᵀ`.

## Main definitions

* `Matrix.IsMoorePenrose A G`: `G` satisfies the four Penrose equations for `A`:
  `A G A = A`, `G A G = G`, `(A G)ᵀ = A G`, `(G A)ᵀ = G A`.
* `Matrix.pinv A`: the Moore–Penrose inverse `A⁺`, written explicitly through the spectral
  decomposition `Aᵀ A = W diag(λ) Wᵀ` as `A⁺ = W diag(λ⁺) Wᵀ Aᵀ` with `λ⁺ = λ⁻¹` (and `0⁻¹ = 0`).
* `Matrix.gramPinv A`: the Gram pseudoinverse `(Aᵀ A)⁻¹ Aᵀ`, a left inverse of every matrix of
  full column rank.
* `Matrix.rangeProj A`: the orthogonal projector `A A⁺` onto the column space of `A`, for every
  `A`.
* `Matrix.colProj A`: the Gram column-space projector `A (Aᵀ A)⁻¹ Aᵀ`.
* `LeanDLRA.galerkinProj U V`: the Galerkin projector `Z ↦ U Uᵀ Z V Vᵀ` onto the matrices
  `U S Vᵀ`.
* `Matrix.IsOrthCapture W X`: `W` has orthonormal columns and `W Wᵀ X = X` (the capture
  hypothesis that replaces QR in the step structures); `Matrix.IsOrthBasisOf W X`: in addition the
  columns of `W` lie in the column space of `X`.
* `Matrix.IsQR K Q R`: `K = Q R` with orthonormal `Q` and upper triangular `R`.
* `Matrix.IsSVD A U σ V`: `A = U diag(σ) Vᵀ` with orthonormal `U`, `V` and
  `σ₀ ≥ ⋯ ≥ σ_{p-1} ≥ 0`; `Matrix.svdTrunc U σ V r`: its truncation
  `U diag(σ₀, …, σ_{r-1}, 0, …, 0) Vᵀ` to the first `r` triplets; `LeanDLRA.tailSqSum σ r`: the
  discarded weight `∑_{i ≥ r} σᵢ²`.
* `LeanDLRA.IsBestLowRankApprox r A X`: `X` has rank `≤ r` and is a closest such matrix to `A` in
  the Frobenius norm.
* `LeanDLRA.KyFan.podBasis A hr`: the POD basis of rank `r`, the top `r` eigenvectors of `Aᵀ A`
  (right singular vectors of `A`) as the columns of an `n × r` matrix.
* `LeanDLRA.Novel.BGKEntropy.colSpace A`: the column space of `A` as a subspace of `m → ℝ`;
  `LeanDLRA.Novel.BGKEntropy.IsOrthProjOnto Q S`: `Q` is the matrix of the orthogonal projector
  onto the subspace `S`; `LeanDLRA.Novel.BGKEntropy.hyperplane u` and
  `LeanDLRA.Novel.BGKEntropy.hyperProj u`: the hyperplane `u^⊥` and its projector
  `I - u uᵀ / ‖u‖²`. They keep the names of the file in which they were first stated.

## Main results

* `Matrix.IsMoorePenrose.unique`, `Matrix.isMoorePenrose_pinv`,
  `Matrix.existsUnique_isMoorePenrose`, `Matrix.isMoorePenrose_iff_eq_pinv`: the Penrose
  equations have exactly one solution, `A.pinv`.
* `Matrix.IsMoorePenrose.symm`, `Matrix.IsMoorePenrose.transpose`, `Matrix.pinv_pinv`,
  `Matrix.pinv_transpose`, `Matrix.pinv_eq_inv`, `Matrix.pinv_mul_mul_transpose`
  (`(U S Vᵀ)⁺ = V S⁻¹ Uᵀ` for orthonormal `U`, `V` and invertible `S`).
* `Matrix.gramPinv_eq_pinv`: for full column rank (`IsUnit (Aᵀ * A).det`, equivalently
  `A.rank = Fintype.card k` by `Matrix.isUnit_det_transpose_mul_self_iff`), the Gram formula is
  the Moore–Penrose inverse.
* `Matrix.gramPinv_eq_pinv_iff`: in general `A.gramPinv = A.pinv` iff `A` has full column rank or
  `A = 0`; the `example` after it shows a rank-deficient matrix for which the two differ.
* `Matrix.eq_rangeProj_iff`: `rangeProj A` is the only symmetric matrix `A C` that fixes the
  columns of `A`; hence `Matrix.rangeProj_eq_mul_transpose` (`U Uᵀ` for orthonormal `U`),
  `Matrix.rangeProj_eq_of_capture` (every orthonormal basis of the column space computes it) and
  `Matrix.rangeProj_eq_rangeProj_of_mul` (it depends only on the column space).
* `Matrix.colProj_eq_rangeProj`, `Matrix.colProj_eq_rangeProj_iff`: the Gram formula is the
  column-space projector iff `A` has full column rank or `A = 0`.
* `LeanDLRA.isOrthProj_galerkinProj`: for orthonormal `U`, `V` the Galerkin projector is an
  orthogonal projector; `LeanDLRA.obliqueProj_self`: the oblique projector with test matrix `A`
  is `colProj A`.
* `Matrix.isOrthCapture_iff` (capture iff `X = W R`), `Matrix.IsQR.isOrthCapture`,
  `Matrix.IsQR.isOrthBasisOf`, `Matrix.IsOrthBasisOf.mul_transpose_eq_rangeProj`: a QR
  factorization with invertible `R` gives an orthonormal basis of the column space, and every such
  basis computes `rangeProj`.
* `Matrix.svdTrunc_eq_submatrix`: for `r ≤ p`, `svdTrunc U σ V r = U_{:r} Σ_r V_{:r}ᵀ`, the
  leading-column form in which papers write the truncation.
* `LeanDLRA.Novel.BGKEntropy.isOrthProjOnto_colSpace_iff`: `Q` is the orthogonal projector onto
  the column space of `A` iff `Q = A.rangeProj`;
  `LeanDLRA.Novel.BGKEntropy.isOrthProjMat_iff_isOrthProjOnto`: the symmetric idempotent matrices
  are the projectors onto their column space;
  `LeanDLRA.Novel.BGKEntropy.colSpan_eq_map_colSpace`: `colSpan A` is `colSpace A` seen in
  `EuclideanSpace ℝ m`;
  `LeanDLRA.Novel.BGKEntropy.hyperProj_eq_one_sub_rangeProj`: `hyperProj u` is `1 - rangeProj` of
  the one-column matrix `u`.

## Implementation notes

The scalar field is `ℝ` (`docs/CONVENTIONS.md` §5), so `Aᴴ = Aᵀ` and the Penrose equations are
stated with the transpose. `A.pinv` is defined explicitly, not by choice; that it satisfies the
Penrose equations is `isMoorePenrose_pinv`, and every other solution equals it. The Gram formula
uses Mathlib's `⁻¹` on square matrices, which is `0` for singular matrices; hence
`A.gramPinv = 0` and `A.colProj = 0` when `Aᵀ A` is singular (`gramPinv_of_not_isUnit`,
`colProj_of_not_isUnit`). `A.rangeProj` is defined through `A.pinv` with classical decidable
equality on the column indices, so that it needs no `DecidableEq` argument
(`rangeProj_eq_mul_pinv` rewrites it for any instance).

The three projectors are projectors of layer 1 and belong with `LinearAlgebra/Projection/Defs.lean`
(`docs/CONVENTIONS.md` §3). They are defined here because `rangeProj` and
`colProj` are built from `pinv` and `gramPinv`, and `galerkinProj` joined them so that batch C2
did not touch the root of the import graph; moving them is hash-neutral. Likewise
`Matrix.svdTrunc`, `LeanDLRA.tailSqSum` and `LeanDLRA.IsBestLowRankApprox` belong with
`LinearAlgebra/SVD/Defs.lean` and `LinearAlgebra/LowRank/Defs.lean`,
which batch B5 created; they were added here in batch C3 and can move there (hash-neutral).
`KyFan.podBasis` (with the two symmetry lemmas for `Aᵀ A` it uses) is here and not in
`LinearAlgebra/SVD/Defs.lean` or `LinearAlgebra/LowRank/Defs.lean` because a definition body
abstracts its proof arguments into auxiliary theorems that are shared within a module: next to
`EckartYoung.rightSingularVectors` or `WeylSingular.tailNorm` it would reuse their auxiliary
proofs and its body would change.
`IsBestLowRankApprox` is the minimizer form; it does not need the distance `distLR` of
`Matrix/LowRankDistance.lean`.

## References

* [Penrose1955]: R. Penrose, *A generalized inverse for matrices*, Proc. Cambridge Philos. Soc.
  51 (1955).
-/

open scoped Matrix

namespace Matrix

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-! ### The Penrose equations -/

/-- `A.IsMoorePenrose G` says that `G` is a Moore–Penrose inverse of the real matrix `A`: the four
Penrose equations `A G A = A`, `G A G = G`, `(A G)ᵀ = A G` and `(G A)ᵀ = G A` hold. Such a `G`
exists and is unique (`existsUnique_isMoorePenrose`); it is `A.pinv`. -/
structure IsMoorePenrose (A : Matrix m n ℝ) (G : Matrix n m ℝ) : Prop where
  /-- First Penrose equation: `G` is a generalized (inner) inverse, `A G A = A`. -/
  mul_pinv_mul : A * G * A = A
  /-- Second Penrose equation: `G` is an outer inverse, `G A G = G`. -/
  pinv_mul_pinv : G * A * G = G
  /-- Third Penrose equation: `A G` is symmetric. -/
  transpose_mul_pinv : (A * G)ᵀ = A * G
  /-- Fourth Penrose equation: `G A` is symmetric. -/
  transpose_pinv_mul : (G * A)ᵀ = G * A

namespace IsMoorePenrose

variable {A : Matrix m n ℝ} {G H : Matrix n m ℝ}

/-- The Penrose equations are symmetric in `A` and `G`: if `G` is the Moore–Penrose inverse of
`A`, then `A` is the Moore–Penrose inverse of `G`. -/
theorem symm (h : A.IsMoorePenrose G) : G.IsMoorePenrose A :=
  ⟨h.pinv_mul_pinv, h.mul_pinv_mul, h.transpose_pinv_mul, h.transpose_mul_pinv⟩

/-- The Penrose equations are stable under transposition: `Gᵀ` is the Moore–Penrose inverse of
`Aᵀ`. -/
theorem transpose (h : A.IsMoorePenrose G) : Aᵀ.IsMoorePenrose Gᵀ where
  mul_pinv_mul := by
    rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, h.mul_pinv_mul]
  pinv_mul_pinv := by
    rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, h.pinv_mul_pinv]
  transpose_mul_pinv := by
    rw [← transpose_mul]
    exact congrArg Matrix.transpose h.transpose_pinv_mul
  transpose_pinv_mul := by
    rw [← transpose_mul]
    exact congrArg Matrix.transpose h.transpose_mul_pinv

/-- `A G` is idempotent: the orthogonal projector onto the range of `A`. -/
theorem mul_pinv_idem (h : A.IsMoorePenrose G) : A * G * (A * G) = A * G := by
  rw [← Matrix.mul_assoc, h.mul_pinv_mul]

/-- `G A` is idempotent: the orthogonal projector onto the row space of `A`. -/
theorem pinv_mul_idem (h : A.IsMoorePenrose G) : G * A * (G * A) = G * A := by
  rw [← Matrix.mul_assoc, h.pinv_mul_pinv]

/-- Two Moore–Penrose inverses `G`, `H` of `A` give the same projector `A G = A H`. -/
theorem mul_eq_mul (hG : A.IsMoorePenrose G) (hH : A.IsMoorePenrose H) : A * G = A * H := by
  have h1 : A * G * (A * H) = A * H := by rw [← Matrix.mul_assoc, hG.mul_pinv_mul]
  have h2 : A * H * (A * G) = A * G := by rw [← Matrix.mul_assoc, hH.mul_pinv_mul]
  calc A * G = (A * G)ᵀ := hG.transpose_mul_pinv.symm
    _ = (A * H * (A * G))ᵀ := by rw [h2]
    _ = (A * G)ᵀ * (A * H)ᵀ := transpose_mul _ _
    _ = A * G * (A * H) := by rw [hG.transpose_mul_pinv, hH.transpose_mul_pinv]
    _ = A * H := h1

/-- Two Moore–Penrose inverses `G`, `H` of `A` give the same projector `G A = H A`. -/
theorem mul_eq_mul' (hG : A.IsMoorePenrose G) (hH : A.IsMoorePenrose H) : G * A = H * A := by
  have h := congrArg Matrix.transpose (hG.transpose.mul_eq_mul hH.transpose)
  rwa [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose] at h

/-- **Uniqueness of the Moore–Penrose inverse** [Penrose1955, Thm. 1]: the Penrose equations have
at most one solution. -/
theorem unique (hG : A.IsMoorePenrose G) (hH : A.IsMoorePenrose H) : G = H :=
  calc G = G * A * G := hG.pinv_mul_pinv.symm
    _ = G * (A * H) := by rw [Matrix.mul_assoc, hG.mul_eq_mul hH]
    _ = H * A * H := by rw [← Matrix.mul_assoc, hG.mul_eq_mul' hH]
    _ = H := hH.pinv_mul_pinv

end IsMoorePenrose

/-- A square matrix with `A A = A` and `Aᵀ = A` (an orthogonal projector) is its own Moore–Penrose
inverse. -/
theorem isMoorePenrose_self_of_idem {A : Matrix n n ℝ} (hA : A * A = A) (hAt : Aᵀ = A) :
    A.IsMoorePenrose A where
  mul_pinv_mul := by rw [hA, hA]
  pinv_mul_pinv := by rw [hA, hA]
  transpose_mul_pinv := by rw [hA, hAt]
  transpose_pinv_mul := by rw [hA, hAt]

/-- For `X = U S Vᵀ` with orthonormal columns `Uᵀ U = 1`, `Vᵀ V = 1` and invertible `S`, the
Moore–Penrose inverse is `V S⁻¹ Uᵀ` (a thin SVD needs `S` diagonal; this is not used). -/
theorem isMoorePenrose_mul_mul_transpose [DecidableEq k] {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {S : Matrix k k ℝ} (hS : IsUnit S.det) :
    (U * S * Vᵀ).IsMoorePenrose (V * S⁻¹ * Uᵀ) := by
  have e1 : U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * Uᵀ := by
    calc _ = U * (S * (Vᵀ * V) * S⁻¹) * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * Uᵀ := by rw [hV, Matrix.mul_one, mul_nonsing_inv _ hS, Matrix.mul_one]
  have e2 : V * S⁻¹ * Uᵀ * (U * S * Vᵀ) = V * Vᵀ := by
    calc _ = V * (S⁻¹ * (Uᵀ * U) * S) * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = V * Vᵀ := by rw [hU, Matrix.mul_one, nonsing_inv_mul _ hS, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]
    calc _ = U * (Uᵀ * U) * S * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]
  · rw [e2]
    calc _ = V * (Vᵀ * V) * S⁻¹ * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  · rw [e1, transpose_mul, transpose_transpose]
  · rw [e2, transpose_mul, transpose_transpose]

/-! ### The Moore–Penrose inverse -/

omit [Fintype n] in
/-- `Aᵀ A` is symmetric, as a Hermitian matrix over `ℝ`. -/
private theorem isHermitian_transpose_mul_self' (A : Matrix m n ℝ) : (Aᵀ * A).IsHermitian := by
  simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul]

/-- The **Moore–Penrose inverse** `A⁺` of a real matrix, explicitly: with the spectral
decomposition `Aᵀ A = W diag(λ) Wᵀ` (Mathlib's `IsHermitian.eigenvectorUnitary` and
`IsHermitian.eigenvalues`), `A⁺ = W diag(λ⁺) Wᵀ Aᵀ`, where `λ⁺ = λ⁻¹` for `λ ≠ 0` and `0⁺ = 0`.
It satisfies the Penrose equations (`isMoorePenrose_pinv`) and is their only solution
(`isMoorePenrose_iff_eq_pinv`). -/
noncomputable def pinv [DecidableEq n] (A : Matrix m n ℝ) : Matrix n m ℝ :=
  ((isHermitian_transpose_mul_self' A).eigenvectorUnitary : Matrix n n ℝ) *
    diagonal (fun i => ((isHermitian_transpose_mul_self' A).eigenvalues i)⁻¹) *
    ((isHermitian_transpose_mul_self' A).eigenvectorUnitary : Matrix n n ℝ)ᵀ * Aᵀ

section Spectral

variable [DecidableEq n]

/-- Spectral data of a symmetric real matrix `M`: an orthogonal `W` and real `d` with
`M = W diag(d) Wᵀ`. -/
private theorem exists_spectral {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    M = (hM.eigenvectorUnitary : Matrix n n ℝ) * diagonal hM.eigenvalues *
        (hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ ∧
      (hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ * (hM.eigenvectorUnitary : Matrix n n ℝ) = 1 := by
  refine ⟨?_, ?_⟩
  · have h2 : M = (hM.eigenvectorUnitary : Matrix n n ℝ) * diagonal hM.eigenvalues *
        star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
      simpa [Unitary.conjStarAlgAut_apply] using hM.spectral_theorem
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h2
  · have := UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

/-- The Penrose equations from a spectral decomposition `Aᵀ A = W diag(d) Wᵀ`, `Wᵀ W = 1`:
`W diag(d⁺) Wᵀ Aᵀ` is the Moore–Penrose inverse of `A`. -/
private theorem isMoorePenrose_of_spectral {A : Matrix m n ℝ} {W : Matrix n n ℝ} {d : n → ℝ}
    (hWW : Wᵀ * W = 1) (hspec : Aᵀ * A = W * diagonal d * Wᵀ) :
    A.IsMoorePenrose (W * diagonal (fun i => (d i)⁻¹) * Wᵀ * Aᵀ) := by
  obtain ⟨Mp, hMp⟩ : ∃ Mp, Mp = W * diagonal (fun i => (d i)⁻¹) * Wᵀ := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = Aᵀ * A := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = W * diagonal (fun i => d i * (d i)⁻¹) * Wᵀ := ⟨_, rfl⟩
  rw [← hMp]
  rw [← hMdef] at hspec
  -- the products `M Mp` and `Mp M` are the symmetric matrix `P = W diag(d d⁻¹) Wᵀ`
  have hMMp : M * Mp = P := by
    rw [hspec, hMp, hP]
    calc _ = W * (diagonal d * (Wᵀ * W) * diagonal (fun i => (d i)⁻¹)) * Wᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWW, Matrix.mul_one, diagonal_mul_diagonal]
  have hMpM : Mp * M = P := by
    rw [hspec, hMp, hP]
    calc _ = W * (diagonal (fun i => (d i)⁻¹) * (Wᵀ * W) * diagonal d) * Wᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hWW, Matrix.mul_one, diagonal_mul_diagonal]
          simp only [mul_comm]
  have hPt : Pᵀ = P := by
    rw [hP, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
      Matrix.mul_assoc]
  have hMpt : Mpᵀ = Mp := by
    rw [hMp, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
      Matrix.mul_assoc]
  have hMMpM : M * Mp * M = M := by
    rw [hMMp, hP, hspec]
    calc _ = W * (diagonal (fun i => d i * (d i)⁻¹) * (Wᵀ * W) * diagonal d) * Wᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hWW, Matrix.mul_one, diagonal_mul_diagonal]
          simp only [mul_inv_mul_cancel]
  have hMpMMp : Mp * M * Mp = Mp := by
    rw [hMpM, hP, hMp]
    calc _ = W * (diagonal (fun i => d i * (d i)⁻¹) * (Wᵀ * W) *
          diagonal (fun i => (d i)⁻¹)) * Wᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hWW, Matrix.mul_one, diagonal_mul_diagonal]
          congr 3
          funext i
          by_cases h : d i = 0 <;> simp [h]
  -- `A Mp M = A`: the residual `A (1 - Mp M)` has zero Gram matrix
  have hAE : A * (Mp * M) = A := by
    obtain ⟨E, hE⟩ : ∃ E, E = 1 - Mp * M := ⟨_, rfl⟩
    have hMEz : M * E = 0 := by
      rw [hE, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hMMpM, sub_self]
    have hEt : Eᵀ = E := by rw [hE, transpose_sub, transpose_one, hMpM, hPt]
    have h0 : (A * E)ᴴ * (A * E) = 0 := by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, hEt]
      calc E * Aᵀ * (A * E) = E * (M * E) := by rw [hMdef]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hMEz, Matrix.mul_zero]
    have hz := conjTranspose_mul_self_eq_zero.1 h0
    rw [hE, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
    exact hz.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc A * (Mp * Aᵀ) * A = A * (Mp * M) := by rw [hMdef]; simp only [Matrix.mul_assoc]
      _ = A := hAE
  · calc Mp * Aᵀ * A * (Mp * Aᵀ) = Mp * M * Mp * Aᵀ := by
          rw [hMdef]; simp only [Matrix.mul_assoc]
      _ = Mp * Aᵀ := by rw [hMpMMp]
  · calc (A * (Mp * Aᵀ))ᵀ = A * Mpᵀ * Aᵀ := by
          simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = A * (Mp * Aᵀ) := by rw [hMpt, Matrix.mul_assoc]
  · calc (Mp * Aᵀ * A)ᵀ = (Mp * M)ᵀ := by rw [hMdef, Matrix.mul_assoc]
      _ = Mp * M := by rw [hMpM, hPt]
      _ = Mp * Aᵀ * A := by rw [hMdef, Matrix.mul_assoc]

/-- The Moore–Penrose inverse satisfies the Penrose equations. -/
theorem isMoorePenrose_pinv (A : Matrix m n ℝ) : A.IsMoorePenrose A.pinv :=
  isMoorePenrose_of_spectral (exists_spectral (isHermitian_transpose_mul_self' A)).2
    (exists_spectral (isHermitian_transpose_mul_self' A)).1

omit [DecidableEq n] in
/-- **Existence and uniqueness of the Moore–Penrose inverse** [Penrose1955, Thm. 1]: for every
real matrix `A` the Penrose equations have exactly one solution. -/
theorem existsUnique_isMoorePenrose (A : Matrix m n ℝ) : ∃! G, A.IsMoorePenrose G := by
  classical
  exact ⟨A.pinv, isMoorePenrose_pinv A, fun _ hG => hG.unique (isMoorePenrose_pinv A)⟩

/-- Every solution of the Penrose equations is `A.pinv`. -/
theorem IsMoorePenrose.eq_pinv {A : Matrix m n ℝ} {G : Matrix n m ℝ} (h : A.IsMoorePenrose G) :
    G = A.pinv :=
  h.unique (isMoorePenrose_pinv A)

/-- `G` solves the Penrose equations for `A` iff `G = A⁺`. -/
theorem isMoorePenrose_iff_eq_pinv {A : Matrix m n ℝ} {G : Matrix n m ℝ} :
    A.IsMoorePenrose G ↔ G = A.pinv :=
  ⟨IsMoorePenrose.eq_pinv, fun h => h ▸ isMoorePenrose_pinv A⟩

/-- First Penrose equation for `A⁺`: `A A⁺ A = A`. -/
@[simp]
theorem mul_pinv_mul_self (A : Matrix m n ℝ) : A * A.pinv * A = A :=
  (isMoorePenrose_pinv A).mul_pinv_mul

/-- Second Penrose equation for `A⁺`: `A⁺ A A⁺ = A⁺`. -/
@[simp]
theorem pinv_mul_self_mul_pinv (A : Matrix m n ℝ) : A.pinv * A * A.pinv = A.pinv :=
  (isMoorePenrose_pinv A).pinv_mul_pinv

/-- Third Penrose equation for `A⁺`: `A A⁺` is symmetric. -/
theorem transpose_mul_pinv (A : Matrix m n ℝ) : (A * A.pinv)ᵀ = A * A.pinv :=
  (isMoorePenrose_pinv A).transpose_mul_pinv

/-- Fourth Penrose equation for `A⁺`: `A⁺ A` is symmetric. -/
theorem transpose_pinv_mul (A : Matrix m n ℝ) : (A.pinv * A)ᵀ = A.pinv * A :=
  (isMoorePenrose_pinv A).transpose_pinv_mul

/-- `(A⁺)⁺ = A`. -/
@[simp]
theorem pinv_pinv [DecidableEq m] (A : Matrix m n ℝ) : A.pinv.pinv = A :=
  ((isMoorePenrose_pinv A).symm.eq_pinv).symm

/-- `(Aᵀ)⁺ = (A⁺)ᵀ`. -/
theorem pinv_transpose [DecidableEq m] (A : Matrix m n ℝ) : Aᵀ.pinv = A.pinvᵀ :=
  ((isMoorePenrose_pinv A).transpose.eq_pinv).symm

/-- `0⁺ = 0`. -/
@[simp]
theorem pinv_zero : (0 : Matrix m n ℝ).pinv = 0 :=
  (IsMoorePenrose.eq_pinv (A := 0) ⟨by simp, by simp, by simp, by simp⟩).symm

/-- For an invertible square matrix the Moore–Penrose inverse is the inverse. -/
theorem pinv_eq_inv {A : Matrix n n ℝ} (hA : IsUnit A.det) : A.pinv = A⁻¹ := by
  refine (IsMoorePenrose.eq_pinv ⟨?_, ?_, ?_, ?_⟩).symm
  · rw [mul_nonsing_inv _ hA, Matrix.one_mul]
  · rw [nonsing_inv_mul _ hA, Matrix.one_mul]
  · rw [mul_nonsing_inv _ hA, transpose_one]
  · rw [nonsing_inv_mul _ hA, transpose_one]

/-- `1⁺ = 1`. -/
@[simp]
theorem pinv_one : (1 : Matrix n n ℝ).pinv = 1 := by
  rw [pinv_eq_inv (by simp), inv_one]

/-- `(U S Vᵀ)⁺ = V S⁻¹ Uᵀ` for orthonormal columns `Uᵀ U = 1`, `Vᵀ V = 1` and invertible `S`. -/
theorem pinv_mul_mul_transpose [DecidableEq k] {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {S : Matrix k k ℝ} (hS : IsUnit S.det) :
    (U * S * Vᵀ).pinv = V * S⁻¹ * Uᵀ :=
  (isMoorePenrose_mul_mul_transpose hU hV hS).eq_pinv.symm

end Spectral

/-! ### The Gram pseudoinverse -/

section Gram

variable [DecidableEq k]

/-- The **Gram pseudoinverse** `(Aᵀ A)⁻¹ Aᵀ` of `A ∈ ℝ^{m × k}`. For `A` of full column rank
(`IsUnit (Aᵀ * A).det`) it is a left inverse of `A` (`gramPinv_mul_self`) and the Moore–Penrose
inverse (`gramPinv_eq_pinv`); this is what papers on low-rank integrators write as `U⁺`, `K⁺` or
`Ω†`. Otherwise it is `0` (`gramPinv_of_not_isUnit`), which differs from `A⁺` unless `A = 0`
(`gramPinv_eq_pinv_iff`). -/
noncomputable def gramPinv (A : Matrix m k ℝ) : Matrix k m ℝ := (Aᵀ * A)⁻¹ * Aᵀ

/-- Unfolding lemma: `A⁺ = (Aᵀ A)⁻¹ Aᵀ`. -/
theorem gramPinv_def (A : Matrix m k ℝ) : A.gramPinv = (Aᵀ * A)⁻¹ * Aᵀ := rfl

/-- `A` has full column rank iff its Gram matrix `Aᵀ A` is invertible. -/
theorem isUnit_det_transpose_mul_self_iff {A : Matrix m k ℝ} :
    IsUnit (Aᵀ * A).det ↔ A.rank = Fintype.card k := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_surjective_iff_isUnit,
    mulVec_surjective_iff_rank_eq_card, rank_transpose_mul_self]

/-- `A⁺ A = 1` for `A` of full column rank. -/
theorem gramPinv_mul_self {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) : A.gramPinv * A = 1 := by
  rw [gramPinv, Matrix.mul_assoc, nonsing_inv_mul _ h]

/-- `(A⁺)ᵀ = A (Aᵀ A)⁻¹`. -/
theorem transpose_gramPinv (A : Matrix m k ℝ) : A.gramPinvᵀ = A * (Aᵀ * A)⁻¹ := by
  rw [gramPinv, transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_mul,
    transpose_transpose]

/-- `A A⁺ = A (Aᵀ A)⁻¹ Aᵀ` is symmetric, for every `A`. -/
theorem transpose_mul_gramPinv (A : Matrix m k ℝ) : (A * A.gramPinv)ᵀ = A * A.gramPinv := by
  rw [transpose_mul, transpose_gramPinv, gramPinv, Matrix.mul_assoc]

/-- The Gram pseudoinverse vanishes when `Aᵀ A` is singular. -/
theorem gramPinv_of_not_isUnit {A : Matrix m k ℝ} (h : ¬IsUnit (Aᵀ * A).det) :
    A.gramPinv = 0 := by
  rw [gramPinv, nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul]

/-- `A⁺ = Aᵀ` for orthonormal columns `Aᵀ A = 1`. -/
theorem gramPinv_eq_transpose {A : Matrix m k ℝ} (hA : Aᵀ * A = 1) : A.gramPinv = Aᵀ := by
  rw [gramPinv, hA, inv_one, Matrix.one_mul]

/-- `(W R)⁺ = R⁻¹ Wᵀ` for orthonormal columns `Wᵀ W = 1` and invertible `R`: a change of basis of
the column space. -/
theorem gramPinv_mul {W : Matrix m k ℝ} (hW : Wᵀ * W = 1) {R : Matrix k k ℝ}
    (hR : IsUnit R.det) : (W * R).gramPinv = R⁻¹ * Wᵀ := by
  have hRt : IsUnit Rᵀ.det := by rwa [det_transpose]
  have hG : (W * R)ᵀ * (W * R) = Rᵀ * R := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul]
  rw [gramPinv, hG, Matrix.mul_inv_rev, transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Rᵀ⁻¹, nonsing_inv_mul _ hRt, Matrix.one_mul]

/-- **Bridge (full column rank)**: for `A` of full column rank the Gram formula `(Aᵀ A)⁻¹ Aᵀ`
satisfies the Penrose equations. -/
theorem isMoorePenrose_gramPinv {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) :
    A.IsMoorePenrose A.gramPinv where
  mul_pinv_mul := by rw [Matrix.mul_assoc, gramPinv_mul_self h, Matrix.mul_one]
  pinv_mul_pinv := by rw [gramPinv_mul_self h, Matrix.one_mul]
  transpose_mul_pinv := transpose_mul_gramPinv A
  transpose_pinv_mul := by rw [gramPinv_mul_self h, transpose_one]

/-- **Bridge (full column rank)**: for `A` of full column rank, `(Aᵀ A)⁻¹ Aᵀ = A⁺`. -/
theorem gramPinv_eq_pinv {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) : A.gramPinv = A.pinv :=
  (isMoorePenrose_gramPinv h).eq_pinv

/-- **Exactly when the Gram formula is the Moore–Penrose inverse**: `(Aᵀ A)⁻¹ Aᵀ` satisfies the
Penrose equations iff `A` has full column rank or `A = 0`. -/
theorem isMoorePenrose_gramPinv_iff {A : Matrix m k ℝ} :
    A.IsMoorePenrose A.gramPinv ↔ IsUnit (Aᵀ * A).det ∨ A = 0 := by
  refine ⟨fun hA => ?_, ?_⟩
  · by_cases h : IsUnit (Aᵀ * A).det
    · exact Or.inl h
    · right
      have h1 := hA.mul_pinv_mul
      rwa [gramPinv_of_not_isUnit h, Matrix.mul_zero, Matrix.zero_mul, eq_comm] at h1
  · rintro (h | rfl)
    · exact isMoorePenrose_gramPinv h
    · have h0 : (0 : Matrix m k ℝ).gramPinv = 0 := by simp [gramPinv]
      rw [h0]
      exact ⟨by simp, by simp, by simp, by simp⟩

/-- **Exactly when the Gram formula is the Moore–Penrose inverse**: `(Aᵀ A)⁻¹ Aᵀ = A⁺` iff `A` has
full column rank or `A = 0`. For a nonzero rank-deficient `A` the two differ (see the `example`
below). -/
theorem gramPinv_eq_pinv_iff {A : Matrix m k ℝ} :
    A.gramPinv = A.pinv ↔ IsUnit (Aᵀ * A).det ∨ A = 0 := by
  rw [← isMoorePenrose_gramPinv_iff, isMoorePenrose_iff_eq_pinv]

end Gram

/-! ### Projectors onto the column space of a matrix -/

/-- The **orthogonal projector onto the column space** of `A`: `A A⁺` with the Moore–Penrose
inverse `A⁺ = Matrix.pinv A`. It is defined for every `A`, whatever its rank: it is symmetric
(`transpose_rangeProj`), idempotent, fixes the columns of `A` (`rangeProj_mul_self`) and is the
only symmetric matrix of the form `A C` that does (`eq_rangeProj_of_mul_self`). For orthonormal
`U` it is `U Uᵀ` (`rangeProj_eq_mul_transpose`); for `A` of full column rank it is the Gram
formula `A (Aᵀ A)⁻¹ Aᵀ = colProj A` (`colProj_eq_rangeProj`). -/
noncomputable def rangeProj (A : Matrix m k ℝ) : Matrix m m ℝ :=
  letI := Classical.decEq k; A * A.pinv

/-- `rangeProj A = A A⁺`, for any decidable equality on the column indices. -/
theorem rangeProj_eq_mul_pinv [inst : DecidableEq k] (A : Matrix m k ℝ) :
    A.rangeProj = A * A.pinv := by
  have h : Classical.decEq k = inst := Subsingleton.elim _ _
  unfold rangeProj
  rw [h]

/-- The column-space projector is symmetric. -/
theorem transpose_rangeProj (A : Matrix m k ℝ) : A.rangeProjᵀ = A.rangeProj := by
  classical
  rw [rangeProj_eq_mul_pinv]
  exact A.transpose_mul_pinv

/-- The column-space projector fixes the columns of `A`: `A A⁺ A = A`. -/
theorem rangeProj_mul_self (A : Matrix m k ℝ) : A.rangeProj * A = A := by
  classical
  rw [rangeProj_eq_mul_pinv]
  exact A.mul_pinv_mul_self

/-- The column-space projector is idempotent. -/
theorem rangeProj_mul_rangeProj (A : Matrix m k ℝ) : A.rangeProj * A.rangeProj = A.rangeProj := by
  classical
  rw [rangeProj_eq_mul_pinv, ← Matrix.mul_assoc, A.mul_pinv_mul_self]

/-- The column-space projector is an orthogonal projector matrix. -/
theorem isOrthProjMat_rangeProj (A : Matrix m k ℝ) :
    LeanDLRA.Curvature.IsOrthProjMat A.rangeProj :=
  ⟨transpose_rangeProj A, rangeProj_mul_rangeProj A⟩

/-- The column-space projector has the form `A C`: its columns lie in the column space of `A`. -/
theorem exists_rangeProj_eq_mul (A : Matrix m k ℝ) : ∃ C : Matrix k m ℝ, A.rangeProj = A * C := by
  classical
  exact ⟨A.pinv, rangeProj_eq_mul_pinv A⟩

/-- **Uniqueness of the column-space projector.** A symmetric matrix `P = A C` whose columns lie in
the column space of `A` and that fixes the columns of `A` is `rangeProj A`. -/
theorem eq_rangeProj_of_mul_self {A : Matrix m k ℝ} {P : Matrix m m ℝ} {C : Matrix k m ℝ}
    (hsymm : Pᵀ = P) (hfix : P * A = A) (hfac : P = A * C) : P = A.rangeProj := by
  classical
  have h1 : A.rangeProj * P = P := by rw [hfac, ← Matrix.mul_assoc, rangeProj_mul_self]
  have h2 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, hsymm, transpose_rangeProj] at h2
  rw [← h2, rangeProj_eq_mul_pinv, ← Matrix.mul_assoc, hfix]

/-- `rangeProj A` is characterized by three properties: it is symmetric, it fixes the columns of
`A`, and it has the form `A C`. -/
theorem eq_rangeProj_iff {A : Matrix m k ℝ} {P : Matrix m m ℝ} :
    P = A.rangeProj ↔ Pᵀ = P ∧ P * A = A ∧ ∃ C : Matrix k m ℝ, P = A * C := by
  constructor
  · rintro rfl
    exact ⟨transpose_rangeProj A, rangeProj_mul_self A, exists_rangeProj_eq_mul A⟩
  · rintro ⟨hs, hf, C, hC⟩
    exact eq_rangeProj_of_mul_self hs hf hC

omit [Fintype n] in
/-- `rangeProj A * X = X` iff the columns of `X` lie in the column space of `A`. -/
theorem rangeProj_mul_eq_self_iff {A : Matrix m k ℝ} {X : Matrix m n ℝ} :
    A.rangeProj * X = X ↔ ∃ C : Matrix k n ℝ, X = A * C := by
  classical
  constructor
  · intro h
    exact ⟨A.pinv * X, by rw [← Matrix.mul_assoc, ← rangeProj_eq_mul_pinv, h]⟩
  · rintro ⟨C, rfl⟩
    rw [← Matrix.mul_assoc, rangeProj_mul_self]

/-- **Orthonormal bases.** The column-space projector of a matrix with orthonormal columns
`Uᵀ U = 1` is `U Uᵀ`. -/
theorem rangeProj_eq_mul_transpose [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) :
    U.rangeProj = U * Uᵀ := by
  refine (eq_rangeProj_of_mul_self (C := Uᵀ) ?_ ?_ rfl).symm
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- **Capture.** If the columns of `W` lie in the column space of `A` (`W = A C`) and `W Wᵀ` fixes
the columns of `A`, then `rangeProj A = W Wᵀ`: an orthonormal basis of the column space computes
the projector, whichever way it was obtained (QR, SVD, Gram–Schmidt). Orthonormality of `W` is not
needed as a hypothesis; it follows (`W Wᵀ` is then idempotent). -/
theorem rangeProj_eq_of_capture {l : Type*} [Fintype l] {A : Matrix m k ℝ} {W : Matrix m l ℝ}
    {C : Matrix k l ℝ} (hcap : W * Wᵀ * A = A) (hWA : W = A * C) : A.rangeProj = W * Wᵀ := by
  refine (eq_rangeProj_of_mul_self (C := C * Wᵀ) ?_ hcap ?_).symm
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [← Matrix.mul_assoc, ← hWA]

/-- The column-space projector depends only on the column space: if `A = B C` and `B = A D`, then
`rangeProj A = rangeProj B`. -/
theorem rangeProj_eq_rangeProj_of_mul {l : Type*} [Fintype l] {A : Matrix m k ℝ}
    {B : Matrix m l ℝ} {C : Matrix l k ℝ} {D : Matrix k l ℝ} (hA : A = B * C) (hB : B = A * D) :
    A.rangeProj = B.rangeProj := by
  obtain ⟨E, hE⟩ := exists_rangeProj_eq_mul B
  refine (eq_rangeProj_of_mul_self (C := D * E) (transpose_rangeProj B) ?_ ?_).symm
  · rw [hA, ← Matrix.mul_assoc, rangeProj_mul_self]
  · rw [hE, hB, Matrix.mul_assoc]

/-- The column-space projector of the zero matrix is `0`. -/
theorem rangeProj_zero : (0 : Matrix m k ℝ).rangeProj = 0 := by
  classical
  rw [rangeProj_eq_mul_pinv, Matrix.zero_mul]

/-! ### The Gram column-space projector -/

section Gram

variable [DecidableEq k]

/-- The **Gram column-space projector** `A (Aᵀ A)⁻¹ Aᵀ = A A⁺`, with the Gram pseudoinverse
`A⁺ = Matrix.gramPinv A`. Papers on low-rank integrators write it for bases of full column rank
(`IsUnit (Aᵀ * A).det`); there it is the orthogonal projector `rangeProj A` onto the column space
(`colProj_eq_rangeProj`), and it equals `U Uᵀ` for every QR factorization `A = U R`
(`colProj_mul_of_isUnit`, `colProj_eq_mul_transpose`). For a rank-deficient `A` Mathlib's
`(Aᵀ A)⁻¹` is `0`, so `colProj A = 0` (`colProj_of_not_isUnit`), which differs from
`rangeProj A` unless `A = 0` (`colProj_eq_rangeProj_iff` and the `example` below). -/
noncomputable def colProj (A : Matrix m k ℝ) : Matrix m m ℝ := A * A.gramPinv

/-- Unfolding lemma: `colProj A = A (Aᵀ A)⁻¹ Aᵀ`. -/
theorem colProj_def (A : Matrix m k ℝ) : A.colProj = A * (Aᵀ * A)⁻¹ * Aᵀ := by
  rw [colProj, gramPinv, Matrix.mul_assoc]

/-- The Gram column-space projector is symmetric. -/
theorem transpose_colProj (A : Matrix m k ℝ) : A.colProjᵀ = A.colProj :=
  transpose_mul_gramPinv A

/-- The Gram column-space projector vanishes when `Aᵀ A` is singular. -/
theorem colProj_of_not_isUnit {A : Matrix m k ℝ} (h : ¬IsUnit (Aᵀ * A).det) : A.colProj = 0 := by
  rw [colProj, gramPinv_of_not_isUnit h, Matrix.mul_zero]

/-- **Bridge (full column rank).** For `A` of full column rank, `A (Aᵀ A)⁻¹ Aᵀ` is the orthogonal
projector onto the column space. -/
theorem colProj_eq_rangeProj {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) :
    A.colProj = A.rangeProj := by
  rw [colProj, rangeProj_eq_mul_pinv, gramPinv_eq_pinv h]

/-- For `A` of full column rank, `colProj A` fixes the columns of `A`. -/
theorem colProj_mul_self {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) : A.colProj * A = A := by
  rw [colProj_eq_rangeProj h, rangeProj_mul_self]

/-- The Gram column-space projector is idempotent, for every `A` (it is `0` without full column
rank). -/
theorem colProj_mul_colProj (A : Matrix m k ℝ) : A.colProj * A.colProj = A.colProj := by
  by_cases h : IsUnit (Aᵀ * A).det
  · rw [colProj_eq_rangeProj h, rangeProj_mul_rangeProj]
  · rw [colProj_of_not_isUnit h, Matrix.zero_mul]

/-- **Exactly when the Gram formula gives the column-space projector**: `colProj A = rangeProj A`
iff `A` has full column rank or `A = 0`. -/
theorem colProj_eq_rangeProj_iff {A : Matrix m k ℝ} :
    A.colProj = A.rangeProj ↔ IsUnit (Aᵀ * A).det ∨ A = 0 := by
  refine ⟨fun hA => ?_, ?_⟩
  · by_cases h : IsUnit (Aᵀ * A).det
    · exact Or.inl h
    · right
      rw [← rangeProj_mul_self A, ← hA, colProj_of_not_isUnit h, Matrix.zero_mul]
  · rintro (h | rfl)
    · exact colProj_eq_rangeProj h
    · rw [rangeProj_zero, colProj, Matrix.zero_mul]

/-- `colProj U = U Uᵀ` for orthonormal columns `Uᵀ U = 1`. -/
theorem colProj_eq_mul_transpose {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) : U.colProj = U * Uᵀ := by
  rw [colProj, gramPinv_eq_transpose hU]

/-- **Change of basis.** `colProj (A C) = colProj A` for invertible `C`; with
`colProj_eq_mul_transpose` this gives `colProj A = U Uᵀ` for every QR factorization `A = U R`. -/
theorem colProj_mul_of_isUnit {A : Matrix m k ℝ} {C : Matrix k k ℝ} (hC : IsUnit C.det) :
    (A * C).colProj = A.colProj := by
  have hG : (A * C)ᵀ * (A * C) = Cᵀ * (Aᵀ * A) * C := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hCt : IsUnit Cᵀ.det := by rwa [det_transpose]
  by_cases h : IsUnit (Aᵀ * A).det
  · have h' : IsUnit ((A * C)ᵀ * (A * C)).det := by
      rw [hG, det_mul, det_mul]
      exact (hCt.mul h).mul hC
    rw [colProj_eq_rangeProj h, colProj_eq_rangeProj h']
    refine rangeProj_eq_rangeProj_of_mul (D := C⁻¹) rfl ?_
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hC, Matrix.mul_one]
  · have h' : ¬IsUnit ((A * C)ᵀ * (A * C)).det := by
      rw [hG, det_mul, det_mul]
      exact fun hu => h (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu))
    rw [colProj_of_not_isUnit h, colProj_of_not_isUnit h']

end Gram

/-! ### Orthonormal frames, QR and SVD data -/

section Frames

variable {l : Type*} [Fintype l] [DecidableEq l]

omit [Fintype k] in
/-- `W` is an **orthonormal frame capturing `X`**: `W` has orthonormal columns (`Wᵀ W = 1`) and
`W Wᵀ X = X`, i.e. the columns of `X` lie in the column space of `W`. This is what the QR step of
a BUG-type integrator provides (`K₁ = U₁ R` gives `U₁ U₁ᵀ K₁ = K₁`); the error analysis uses
nothing else (`docs/CONVENTIONS.md` §6.3). -/
structure IsOrthCapture (W : Matrix m l ℝ) (X : Matrix m k ℝ) : Prop where
  /-- `W` has orthonormal columns. -/
  orth : Wᵀ * W = 1
  /-- `W Wᵀ` fixes the columns of `X`. -/
  capture : W * Wᵀ * X = X

/-- `W` is an **orthonormal basis of the column space of `X`**: an orthonormal frame capturing `X`
whose columns lie in the column space of `X` (`W = X C`). Then `W Wᵀ` is the orthogonal projector
onto the column space of `X` (`IsOrthBasisOf.mul_transpose_eq_rangeProj`). -/
structure IsOrthBasisOf (W : Matrix m l ℝ) (X : Matrix m k ℝ) : Prop where
  /-- `W` has orthonormal columns. -/
  orth : Wᵀ * W = 1
  /-- `W Wᵀ` fixes the columns of `X`. -/
  capture : W * Wᵀ * X = X
  /-- The columns of `W` lie in the column space of `X`. -/
  span : ∃ C : Matrix k l ℝ, W = X * C

/-- An orthonormal basis of the column space captures it. -/
theorem IsOrthBasisOf.isOrthCapture {W : Matrix m l ℝ} {X : Matrix m k ℝ}
    (h : IsOrthBasisOf W X) : IsOrthCapture W X :=
  ⟨h.orth, h.capture⟩

omit [Fintype k] in
/-- An orthonormal frame `W` captures `X` iff `X = W R` for some `R` (then `R = Wᵀ X`). -/
theorem isOrthCapture_iff {W : Matrix m l ℝ} {X : Matrix m k ℝ} :
    IsOrthCapture W X ↔ Wᵀ * W = 1 ∧ ∃ R : Matrix l k ℝ, X = W * R := by
  constructor
  · rintro ⟨hW, hc⟩
    exact ⟨hW, Wᵀ * X, by rw [← Matrix.mul_assoc, hc]⟩
  · rintro ⟨hW, R, rfl⟩
    exact ⟨hW, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul]⟩

/-- **Bridge.** For an orthonormal basis `W` of the column space of `X`, `W Wᵀ` is the orthogonal
projector `rangeProj X` onto it. -/
theorem IsOrthBasisOf.mul_transpose_eq_rangeProj {W : Matrix m l ℝ} {X : Matrix m k ℝ}
    (h : IsOrthBasisOf W X) : W * Wᵀ = X.rangeProj := by
  obtain ⟨C, hC⟩ := h.span
  exact (rangeProj_eq_of_capture h.capture hC).symm

/-- `W` is an orthonormal basis of its own column space. -/
theorem isOrthBasisOf_self {W : Matrix m l ℝ} (hW : Wᵀ * W = 1) : IsOrthBasisOf W W :=
  ⟨hW, by rw [Matrix.mul_assoc, hW, Matrix.mul_one], 1, (Matrix.mul_one W).symm⟩

end Frames

section QR

variable {p : ℕ}

/-- `K = Q R` is a **(thin) QR factorization**: `Q` has orthonormal columns and `R` is upper
triangular. -/
structure IsQR (K Q : Matrix m (Fin p) ℝ) (R : Matrix (Fin p) (Fin p) ℝ) : Prop where
  /-- `K = Q R`. -/
  eq : K = Q * R
  /-- `Q` has orthonormal columns. -/
  orth : Qᵀ * Q = 1
  /-- `R` is upper triangular. -/
  upper : R.BlockTriangular id

/-- The orthonormal factor of a QR factorization captures `K` (the capture hypothesis of the
BUG-type steps, `docs/CONVENTIONS.md` §6.3). -/
theorem IsQR.isOrthCapture {K Q : Matrix m (Fin p) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    (h : IsQR K Q R) : IsOrthCapture Q K :=
  isOrthCapture_iff.2 ⟨h.orth, R, h.eq⟩

/-- With invertible `R`, the orthonormal factor of a QR factorization is an orthonormal basis of
the column space of `K`, so `Q Qᵀ = rangeProj K`. -/
theorem IsQR.isOrthBasisOf {K Q : Matrix m (Fin p) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    (h : IsQR K Q R) (hR : IsUnit R.det) : IsOrthBasisOf Q K := by
  refine ⟨h.orth, h.isOrthCapture.capture, R⁻¹, ?_⟩
  rw [h.eq, Matrix.mul_assoc, mul_nonsing_inv _ hR, Matrix.mul_one]

/-- Non-vacuity: `1 = 1 · 1` is a QR factorization. -/
example : IsQR (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 :=
  ⟨(Matrix.one_mul 1).symm, by simp, blockTriangular_one⟩

end QR

section SVD

variable {p : ℕ}

/-- `A = U diag(σ) Vᵀ` is a **singular value decomposition with `p` triplets**: `U` and `V` have
orthonormal columns and `σ₀ ≥ σ₁ ≥ ⋯ ≥ σ_{p-1} ≥ 0`. This covers the thin SVD (`p = rank A`) and
the reduced SVD (`p = min (m, n)`). -/
structure IsSVD (A : Matrix m n ℝ) (U : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ)
    (V : Matrix n (Fin p) ℝ) : Prop where
  /-- `U` has orthonormal columns. -/
  orthU : Uᵀ * U = 1
  /-- `V` has orthonormal columns. -/
  orthV : Vᵀ * V = 1
  /-- The singular values are sorted decreasingly. -/
  antitone : Antitone σ
  /-- The singular values are nonnegative. -/
  nonneg : ∀ i, 0 ≤ σ i
  /-- `A = U diag(σ) Vᵀ`. -/
  eq : A = U * diagonal σ * Vᵀ

/-- Non-vacuity: `1 = 1 · diag(1, 1) · 1ᵀ` is an SVD. -/
example : IsSVD (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => 1) 1 :=
  ⟨by simp, by simp, fun _ _ _ => le_rfl, fun _ => zero_le_one, by simp⟩

end SVD

section Truncation

variable {p : ℕ}

omit [Fintype m] [Fintype n] in
/-- The **truncated SVD** `U diag(σ₀, …, σ_{r-1}, 0, …, 0) Vᵀ = U_{:r} Σ_r V_{:r}ᵀ`: the first `r`
triplets of `U diag(σ) Vᵀ`. For an SVD of `A` (`Matrix.IsSVD`) it is a best rank-`r`
approximation of `A`, with error `‖A - svdTrunc U σ V r‖² = tailSqSum σ r`. -/
def svdTrunc (U : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ) (V : Matrix n (Fin p) ℝ) (r : ℕ) :
    Matrix m n ℝ :=
  U * diagonal (fun i : Fin p => if (i : ℕ) < r then σ i else 0) * Vᵀ

omit [Fintype m] [Fintype n] in
/-- Unfolding lemma for `svdTrunc`. -/
theorem svdTrunc_def (U : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ) (V : Matrix n (Fin p) ℝ) (r : ℕ) :
    svdTrunc U σ V r = U * diagonal (fun i : Fin p => if (i : ℕ) < r then σ i else 0) * Vᵀ := rfl

/-- Sums over the first `r` of `p` indices. -/
private theorem sum_castLE_eq_sum_ite {r : ℕ} (hr : r ≤ p) (g : Fin p → ℝ) :
    ∑ i : Fin r, g (Fin.castLE hr i) = ∑ i : Fin p, if (i : ℕ) < r then g i else 0 := by
  rw [← Finset.sum_filter]
  have h : Finset.filter (fun i : Fin p => (i : ℕ) < r) Finset.univ =
      Finset.univ.map (Fin.castLEEmb hr) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2
  rw [h, Finset.sum_map]
  rfl

omit [Fintype m] [Fintype n] in
/-- **Bridge to the leading-column form.** For `r ≤ p`, the truncation is
`U_{:r} diag(σ₀, …, σ_{r-1}) V_{:r}ᵀ`, the form in which papers write it. -/
theorem svdTrunc_eq_submatrix (U : Matrix m (Fin p) ℝ) (σ : Fin p → ℝ) (V : Matrix n (Fin p) ℝ)
    {r : ℕ} (hr : r ≤ p) :
    svdTrunc U σ V r = U.submatrix id (Fin.castLE hr) * diagonal (σ ∘ Fin.castLE hr) *
      (V.submatrix id (Fin.castLE hr))ᵀ := by
  ext a b
  rw [svdTrunc_def, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    Function.comp]
  rw [sum_castLE_eq_sum_ite hr (fun i => U a i * σ i * V b i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Truncation

/-! ### Examples -/

/-- `diag(1, 0)` is idempotent. -/
private theorem diagonal_one_zero_mul_self :
    diagonal ![(1 : ℝ), 0] * diagonal ![(1 : ℝ), 0] = diagonal ![(1 : ℝ), 0] := by
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Non-vacuity of the Penrose equations: the orthogonal projector `diag(1, 0)` is its own
Moore–Penrose inverse. -/
example : (diagonal ![(1 : ℝ), 0]).IsMoorePenrose (diagonal ![(1 : ℝ), 0]) :=
  isMoorePenrose_self_of_idem diagonal_one_zero_mul_self (diagonal_transpose _)

/-- Non-vacuity of the full-rank bridge: the column `A = (1, 1)ᵀ` has full column rank, so its
Gram pseudoinverse is its Moore–Penrose inverse. -/
example : (of fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ)).gramPinv =
    (of fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ)).pinv := by
  refine gramPinv_eq_pinv ?_
  rw [det_fin_one, Matrix.mul_apply, Fin.sum_univ_two]
  simp [isUnit_iff_ne_zero]

/-- **The Gram formula is not the Moore–Penrose inverse without full column rank.** For the
rank-one matrix `A = diag(1, 0)`, `Aᵀ A` is singular, so `(Aᵀ A)⁻¹ Aᵀ = 0`, while `A⁺ = A ≠ 0`. -/
example : (diagonal ![(1 : ℝ), 0]).gramPinv ≠ (diagonal ![(1 : ℝ), 0]).pinv := by
  rw [Ne, gramPinv_eq_pinv_iff, not_or, diagonal_transpose, diagonal_one_zero_mul_self,
    det_diagonal, Fin.prod_univ_two]
  refine ⟨by simp, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  simp at this

/-- Non-vacuity: the column-space projector of the column `e₁ = (1, 0)ᵀ` is `diag(1, 0)`. -/
example : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ).rangeProj = diagonal ![(1 : ℝ), 0] := by
  rw [rangeProj_eq_mul_transpose (by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply])]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- **Capture does not give a basis of the column space.** The identity frame captures the column
`e₁ = (1, 0)ᵀ`, but its columns do not lie in the column space of `e₁`: `IsOrthCapture` does not
imply `IsOrthBasisOf`. -/
example : IsOrthCapture (1 : Matrix (Fin 2) (Fin 2) ℝ) (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) ∧
    ¬IsOrthBasisOf (1 : Matrix (Fin 2) (Fin 2) ℝ) (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) := by
  refine ⟨⟨by simp, by simp⟩, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h.span
  have := congrFun (congrFun hC 1) 1
  simp [Matrix.mul_apply] at this

/-- **The Gram projector is not the column-space projector without full column rank.** For
`A = diag(1, 0)`, `Aᵀ A` is singular, so `A (Aᵀ A)⁻¹ Aᵀ = 0`, while `rangeProj A = A ≠ 0`. -/
example : (diagonal ![(1 : ℝ), 0]).colProj ≠ (diagonal ![(1 : ℝ), 0]).rangeProj := by
  rw [Ne, colProj_eq_rangeProj_iff, not_or, diagonal_transpose, diagonal_one_zero_mul_self,
    det_diagonal, Fin.prod_univ_two]
  refine ⟨by simp, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  simp at this

end Matrix

namespace LeanDLRA

open scoped RealInnerProductSpace

/-! ### Galerkin projectors on matrices -/

section Galerkin

open scoped LeanDLRA.Frobenius

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k']

/-- The **Galerkin projector** `Z ↦ U Uᵀ Z V Vᵀ`, the composition `leftProj U * rightProj V`. For
orthonormal `U`, `V` it is the orthogonal projector onto the matrices `U S Vᵀ`
(`isOrthProj_galerkinProj`); the S-substep of every BUG-type integrator is the Galerkin flow of
this projector. -/
noncomputable def galerkinProj (U : Matrix m k ℝ) (V : Matrix n k' ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  leftProj U * rightProj V

/-- Unfolding lemma: `galerkinProj U V = leftProj U * rightProj V`. -/
theorem galerkinProj_def (U : Matrix m k ℝ) (V : Matrix n k' ℝ) :
    galerkinProj U V = (leftProj U * rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) := rfl

/-- `galerkinProj U V X = U Uᵀ X V Vᵀ`. -/
theorem galerkinProj_apply (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (X : Matrix m n ℝ) :
    galerkinProj U V X = U * Uᵀ * X * (V * Vᵀ) := by
  change leftProj U (rightProj V X) = _
  simp only [leftProj_apply, rightProj_apply', Matrix.mul_assoc]

/-- The Frobenius inner product as a trace (a private copy of `Frobenius.inner_eq_trace`, which
lives in a theorem file). -/
private theorem galerkinProj_inner_eq_trace (A B : Matrix m n ℝ) :
    ⟪A, B⟫ = Matrix.trace (Aᵀ * B) := by
  simp only [Frobenius.inner_def, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

/-- For orthonormal `U` and `V` (`Uᵀ U = 1`, `Vᵀ V = 1`) the Galerkin projector is an orthogonal
projector. -/
theorem isOrthProj_galerkinProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) : IsOrthProj (galerkinProj U V) where
  idem X := by
    simp only [galerkinProj_apply]
    have hP : U * Uᵀ * (U * Uᵀ) = U * Uᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
    have hQ : V * Vᵀ * (V * Vᵀ) = V * Vᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
    calc U * Uᵀ * (U * Uᵀ * X * (V * Vᵀ)) * (V * Vᵀ)
        = U * Uᵀ * (U * Uᵀ) * X * (V * Vᵀ * (V * Vᵀ)) := by simp only [Matrix.mul_assoc]
      _ = U * Uᵀ * X * (V * Vᵀ) := by rw [hP, hQ]
  symm X Y := by
    have hP : (U * Uᵀ)ᵀ = U * Uᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hQ : (V * Vᵀ)ᵀ = V * Vᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [galerkinProj_apply, galerkinProj_apply]
    calc ⟪U * Uᵀ * X * (V * Vᵀ), Y⟫ = Matrix.trace (V * Vᵀ * (Xᵀ * (U * Uᵀ) * Y)) := by
          rw [galerkinProj_inner_eq_trace, Matrix.transpose_mul (U * Uᵀ * X), hQ,
            Matrix.transpose_mul, hP]
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Xᵀ * (U * Uᵀ) * Y * (V * Vᵀ)) := Matrix.trace_mul_comm _ _
      _ = ⟪X, U * Uᵀ * Y * (V * Vᵀ)⟫ := by
          rw [galerkinProj_inner_eq_trace]
          simp only [Matrix.mul_assoc]

end Galerkin

section Oblique

open Matrix

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]

/-- The oblique projector `U (Sᵀ U)⁻¹ Sᵀ` with test matrix `S = A` is the Gram column-space
projector `A (Aᵀ A)⁻¹ Aᵀ`. -/
theorem obliqueProj_self (A : Matrix m k ℝ) : obliqueProj A A = A.colProj := by
  rw [obliqueProj, colProj_def]

end Oblique

section Truncation

/-- The **discarded weight** `∑_{i ≥ r} σᵢ²` of the singular values `σ₀, …, σ_{p-1}` beyond rank `r`
(zero-indexed): the squared Frobenius error of `Matrix.svdTrunc` for an SVD. -/
def tailSqSum {p : ℕ} (σ : Fin p → ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin p, if r ≤ (i : ℕ) then σ i ^ 2 else 0

/-- Unfolding lemma for `tailSqSum`. -/
theorem tailSqSum_def {p : ℕ} (σ : Fin p → ℝ) (r : ℕ) :
    tailSqSum σ r = ∑ i : Fin p, if r ≤ (i : ℕ) then σ i ^ 2 else 0 := rfl

/-- The discarded weight is nonnegative. -/
theorem tailSqSum_nonneg {p : ℕ} (σ : Fin p → ℝ) (r : ℕ) : 0 ≤ tailSqSum σ r :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [sq_nonneg]

/-- Nothing is discarded at rank `p`. -/
theorem tailSqSum_of_le {p : ℕ} (σ : Fin p → ℝ) {r : ℕ} (hr : p ≤ r) : tailSqSum σ r = 0 :=
  Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun h => absurd (i.2.trans_le hr) (not_lt.2 h)

/-- Non-vacuity: for `σ = (3, 2, 1)`, the weight discarded at rank `1` is `2² + 1² = 5`. -/
example : tailSqSum ![(3 : ℝ), 2, 1] 1 = 5 := by
  simp [tailSqSum, Fin.sum_univ_three]
  norm_num

end Truncation

section BestApprox

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `X` is a **best rank-`r` approximation** of `A` in the Frobenius norm: `rank X ≤ r` and
`‖A - X‖ ≤ ‖A - B‖` for every matrix `B` of rank at most `r`. -/
def IsBestLowRankApprox (r : ℕ) (A X : Matrix m n ℝ) : Prop :=
  X.rank ≤ r ∧ ∀ B : Matrix m n ℝ, B.rank ≤ r → ‖A - X‖ ≤ ‖A - B‖

/-- A matrix of rank at most `r` is its own best rank-`r` approximation. -/
theorem isBestLowRankApprox_self {r : ℕ} {A : Matrix m n ℝ} (hA : A.rank ≤ r) :
    IsBestLowRankApprox r A A :=
  ⟨hA, fun B _ => by rw [sub_self, norm_zero]; exact norm_nonneg _⟩

/-- Non-vacuity: `0` is a best rank-`0` approximation of `0`. -/
example : IsBestLowRankApprox 0 (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 :=
  isBestLowRankApprox_self (by simp)

end BestApprox

end LeanDLRA

/-! ### The POD basis -/

section POD

open Finset
open scoped InnerProductSpace ComplexConjugate

namespace LeanDLRA.KyFan

open scoped Matrix LeanDLRA.Frobenius

variable {m n ι : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

omit [Fintype n] [DecidableEq n] in
/-- The Gram matrix `Aᵀ A` of a real matrix is symmetric. -/
theorem isHermitian_transpose_mul_self (A : Matrix m n ℝ) : (Aᵀ * A).IsHermitian := by
  simpa using Matrix.isHermitian_conjTranspose_mul_self A

/-- `Aᵀ A` acts as a symmetric operator on `EuclideanSpace ℝ n`. -/
theorem isSymmetric_toEuclideanLin_transpose_mul_self (A : Matrix m n ℝ) :
    (Matrix.toEuclideanLin (Aᵀ * A)).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (isHermitian_transpose_mul_self A)

/-- The *POD basis* of rank `r`: the top `r` eigenvectors of `Aᵀ A`, as the columns of an
`n × r` matrix. -/
noncomputable def podBasis (A : Matrix m n ℝ) {r : ℕ} (hr : r ≤ Fintype.card n) :
    Matrix n (Fin r) ℝ :=
  ofCols fun j => (isSymmetric_toEuclideanLin_transpose_mul_self A).eigenvectorBasis
    finrank_euclideanSpace (Fin.castLE hr j)

end LeanDLRA.KyFan

end POD

/-! ### Column spaces in `m → ℝ` and the projector matrix onto a subspace

`colSpace`, `IsOrthProjOnto`, `IsOrthProjOnto.unique`, `hyperplane` and `hyperProj` were stated in
`Novel/BGKEntropy.lean` and keep the names they had there. The lemmas after them connect them to
the rest of this layer: `IsOrthProjOnto Q (colSpace A)` holds exactly for `Q = A.rangeProj`, a
matrix is an `IsOrthProjOnto` of its own column space exactly if it is a
`Curvature.IsOrthProjMat`, and `colSpan A` is `colSpace A` seen in `EuclideanSpace ℝ m`. -/

namespace LeanDLRA.Novel.BGKEntropy

open Filter Topology Matrix

section General

variable {m n : Type*} [Fintype n]

variable [Fintype m]

/-- The column space of `f`. -/
def colSpace (f : Matrix m n ℝ) : Submodule ℝ (m → ℝ) := LinearMap.range f.mulVecLin

end General

section Projector

variable {ι : Type*} [Fintype ι]

/-- `Q` is the matrix of the orthogonal projector onto `S`.  There is at most one such matrix,
see `IsOrthProjOnto.unique`. -/
structure IsOrthProjOnto (Q : Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ)) : Prop where
  symm : Qᵀ = Q
  mem : ∀ x, Q *ᵥ x ∈ S
  fix : ∀ x ∈ S, Q *ᵥ x = x

/-- The orthogonal projector onto a subspace is unique. -/
theorem IsOrthProjOnto.unique {Q Q' : Matrix ι ι ℝ} {S : Submodule ℝ (ι → ℝ)}
    (h : IsOrthProjOnto Q S) (h' : IsOrthProjOnto Q' S) : Q = Q' := by
  have key : ∀ {A B : Matrix ι ι ℝ}, IsOrthProjOnto A S → IsOrthProjOnto B S → A * B = B := by
    intro A B hA hB
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec, hA.fix _ (hB.mem x)]
  have h1 : Q * Q' = Q' := key h h'
  have h2 : Q' * Q = Q := key h' h
  have h3 : Q' * Q = Q' := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, h.symm, h'.symm] at this
  rw [← h2, h3]

/-- The hyperplane `u^⊥`. -/
def hyperplane (u : ι → ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {x | u ⬝ᵥ x = 0}
  add_mem' := by
    intro a b (ha : u ⬝ᵥ a = 0) (hb : u ⬝ᵥ b = 0)
    change u ⬝ᵥ (a + b) = 0
    rw [dotProduct_add, ha, hb, add_zero]
  zero_mem' := dotProduct_zero u
  smul_mem' := by
    intro c x (hx : u ⬝ᵥ x = 0)
    change u ⬝ᵥ (c • x) = 0
    rw [dotProduct_smul, hx, smul_zero]

variable [DecidableEq ι]

/-- The orthogonal projector onto `u^⊥`, `I - u uᵀ / ‖u‖²`. -/
noncomputable def hyperProj (u : ι → ℝ) : Matrix ι ι ℝ :=
  1 - (u ⬝ᵥ u)⁻¹ • vecMulVec u u

end Projector

section Bridges

variable {m k : Type*} [Fintype m] [Fintype k]

/-- The matrix of the orthogonal projector onto a subspace is symmetric and idempotent. -/
theorem IsOrthProjOnto.isOrthProjMat {Q : Matrix m m ℝ} {S : Submodule ℝ (m → ℝ)}
    (h : IsOrthProjOnto Q S) : Curvature.IsOrthProjMat Q := by
  refine ⟨h.symm, ?_⟩
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, h.fix _ (h.mem x)]

/-- A symmetric idempotent matrix is the orthogonal projector onto its own column space. -/
theorem isOrthProjOnto_colSpace_self {Q : Matrix m m ℝ} (h : Curvature.IsOrthProjMat Q) :
    IsOrthProjOnto Q (colSpace Q) := by
  refine ⟨h.symm, fun x => LinearMap.mem_range.mpr ⟨x, rfl⟩, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  change Q *ᵥ (Q *ᵥ y) = Q *ᵥ y
  rw [Matrix.mulVec_mulVec, h.idem]

/-- **Projector matrices are the projectors onto their column space**: `Curvature.IsOrthProjMat`
(symmetric and idempotent) and `IsOrthProjOnto` (symmetric, maps into the subspace and fixes it)
describe the same matrices. -/
theorem isOrthProjMat_iff_isOrthProjOnto {Q : Matrix m m ℝ} :
    Curvature.IsOrthProjMat Q ↔ IsOrthProjOnto Q (colSpace Q) :=
  ⟨isOrthProjOnto_colSpace_self, IsOrthProjOnto.isOrthProjMat⟩

/-- `A.rangeProj = A A⁺` is the orthogonal projector onto the column space of `A`. -/
theorem isOrthProjOnto_rangeProj (A : Matrix m k ℝ) :
    IsOrthProjOnto A.rangeProj (colSpace A) := by
  classical
  refine ⟨Matrix.transpose_rangeProj A,
    fun x => LinearMap.mem_range.mpr ⟨A.pinv *ᵥ x, ?_⟩, fun x hx => ?_⟩
  · change A *ᵥ (A.pinv *ᵥ x) = A.rangeProj *ᵥ x
    rw [Matrix.mulVec_mulVec, Matrix.rangeProj_eq_mul_pinv]
  · obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    change A.rangeProj *ᵥ (A *ᵥ y) = A *ᵥ y
    rw [Matrix.mulVec_mulVec, Matrix.rangeProj_mul_self]

/-- **The two descriptions of the column-space projector agree**: `Q` is the orthogonal projector
onto the column space of `A` in the sense of `IsOrthProjOnto` iff it is `A.rangeProj = A A⁺`. -/
theorem isOrthProjOnto_colSpace_iff {A : Matrix m k ℝ} {Q : Matrix m m ℝ} :
    IsOrthProjOnto Q (colSpace A) ↔ Q = A.rangeProj :=
  ⟨fun h => h.unique (isOrthProjOnto_rangeProj A), fun h => h ▸ isOrthProjOnto_rangeProj A⟩

omit [Fintype m] in
/-- The span of the columns `colSpan A`, a subspace of `EuclideanSpace ℝ m`, is the column space
`colSpace A`, a subspace of `m → ℝ`, under the identification of the two spaces. -/
theorem colSpan_eq_map_colSpace (A : Matrix m k ℝ) :
    colSpan A = (colSpace A).map (WithLp.linearEquiv 2 ℝ (m → ℝ)).symm.toLinearMap := by
  rw [colSpace, Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The projector `!![1, 0; 0, 0]` onto the first coordinate axis is the `IsOrthProjOnto` of its
column space. -/
example : IsOrthProjOnto (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) (colSpace !![1, 0; 0, 0]) :=
  isOrthProjOnto_colSpace_self
    ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl,
      by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/-- **The hyperplane projector through `rangeProj`**: `hyperProj u = I - P_u`, where
`P_u = rangeProj` of the one-column matrix `u` is the orthogonal projector onto the span of `u`.
No hypothesis `u ≠ 0` is needed: for `u = 0` both sides are the identity. -/
theorem hyperProj_eq_one_sub_rangeProj [DecidableEq m] (u : m → ℝ) :
    hyperProj u = 1 - (Matrix.replicateCol Unit u).rangeProj := by
  have h : (u ⬝ᵥ u)⁻¹ • vecMulVec u u = (Matrix.replicateCol Unit u).rangeProj := by
    refine Matrix.eq_rangeProj_of_mul_self (C := (u ⬝ᵥ u)⁻¹ • Matrix.replicateRow Unit u)
      ?_ ?_ ?_
    · rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec]
    · by_cases hu : u ⬝ᵥ u = 0
      · have h0 : u = 0 := dotProduct_self_eq_zero.mp hu
        simp [h0]
      · ext i j
        have hsum : ∑ x, u i * u x * u x = u i * (u ⬝ᵥ u) := by
          rw [dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
        rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply]
        simp only [Matrix.vecMulVec_apply, Matrix.replicateCol_apply]
        rw [hsum, smul_eq_mul, mul_comm (u i), ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    · rw [Matrix.mul_smul, Matrix.vecMulVec_eq Unit]
  rw [hyperProj, h]

/-- The projector onto the hyperplane orthogonal to `(1, 2)`. -/
example : hyperProj ![(1 : ℝ), 2] = 1 - (Matrix.replicateCol Unit ![(1 : ℝ), 2]).rangeProj :=
  hyperProj_eq_one_sub_rangeProj _

end Bridges

end LeanDLRA.Novel.BGKEntropy
