import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Definitions: pseudoinverses of real matrices

The vocabulary of layer 1 (`LinearAlgebra/`) for generalized inverses. Low-rank integrators meet
pseudoinverses in two forms: the **Moore–Penrose inverse** `A⁺`, defined for every matrix by the
four Penrose equations, and the **Gram formula** `(Aᵀ A)⁻¹ Aᵀ`, which papers write as `A⁺` (or
`A†`) for matrices of full column rank (bases `U`, sketches `Ω`, factors `K = U S`). This file
defines both, proves that the Penrose equations have exactly one solution, and characterizes
exactly when the two agree.

## Main definitions

* `Matrix.IsMoorePenrose A G`: `G` satisfies the four Penrose equations for `A`:
  `A G A = A`, `G A G = G`, `(A G)ᵀ = A G`, `(G A)ᵀ = G A`.
* `Matrix.pinv A`: the Moore–Penrose inverse `A⁺`, written explicitly through the spectral
  decomposition `Aᵀ A = W diag(λ) Wᵀ` as `A⁺ = W diag(λ⁺) Wᵀ Aᵀ` with `λ⁺ = λ⁻¹` (and `0⁻¹ = 0`).
* `Matrix.gramPinv A`: the Gram pseudoinverse `(Aᵀ A)⁻¹ Aᵀ`, a left inverse of every matrix of
  full column rank.

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

## Implementation notes

The scalar field is `ℝ` (`docs/CONVENTIONS.md` §5), so `Aᴴ = Aᵀ` and the Penrose equations are
stated with the transpose. `A.pinv` is defined explicitly, not by choice; that it satisfies the
Penrose equations is `isMoorePenrose_pinv`, and every other solution equals it. The Gram formula
uses Mathlib's `⁻¹` on square matrices, which is `0` for singular matrices; hence
`A.gramPinv = 0` when `Aᵀ A` is singular (`gramPinv_of_not_isUnit`).

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

end Matrix
