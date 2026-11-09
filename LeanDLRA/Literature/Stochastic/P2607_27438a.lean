import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Auto
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# Results of arXiv 2607.27438: Dynamical low-rank smoothing

This module proves the Moore–Penrose identity that the paper uses in the proofs of its
DLRA-JMCO smoothers (Propositions 3.3 and 4.1). Let `U ∈ ℝ^{k×d}` have orthonormal rows,
`U Uᵀ = 1`, and let `C ∈ ℝ^{k×k}` be invertible (the paper's covariance `C_Ŷ`, assumed full rank
there). Then `(Uᵀ C U)† = Uᵀ C⁻¹ U`, where `†` is the Moore–Penrose inverse of the `d × d` matrix
`Uᵀ C U` (the paper's `Ĉ`). The paper states this identity in the proof of Proposition 3.3 and
uses it for the gain in Proposition 4.1.

Contents:

* `IsMoorePenrose.transpose`, `IsMoorePenrose.unique`: the Penrose equations (core
  `Matrix.IsMoorePenrose`) are stable under transposition and have at most one solution, so
  `G = X†` is well defined; both are the core lemmas for square matrices.
* `isMoorePenrose_orthonormal_sandwich`: `Uᵀ C⁻¹ U` satisfies the Penrose equations for `Uᵀ C U`.
* `moorePenrose_orthonormal_sandwich`: the paper's identity `(Uᵀ C U)† = Uᵀ C⁻¹ U`, and
  `pinv_orthonormal_sandwich`: the same with the core Moore–Penrose inverse `Matrix.pinv`.
* `example`: a non-vacuous instance with `k = 1`, `d = 2`, `U = (1, 0)` and `C = (2)`.

Core definitions: `Matrix.IsMoorePenrose` (the four Penrose equations) and `Matrix.pinv`
(`LinearAlgebra/Factorization/Defs.lean`). The local square-matrix `IsMoorePenrose` of an earlier
version of this file had the same four equations and was replaced by the core definition
(unification batch C1); its deprecated alias is at the end of the file.

Left out, not formalized: Propositions 3.1 and 3.2 (the classical and ensemble Rauch–Tung–Striebel
smoothers, cited from the literature), Propositions 3.3 and 4.1 themselves (the mean, covariance and
basis update formulas), and the stochastic forward step (11)–(12) and the algorithm of Section 3.
The smoother formulas depend on the RTS formulas, which are not derived here and are not assumed as
hypotheses, so the smoother statements are not proved. The range invariance `U^s_k = U_k` is not
formalized either.
-/

open scoped Matrix

namespace LeanDLRA.Literature.P2607_27438

/-- The Penrose equations are stable under transposition (the core
`Matrix.IsMoorePenrose.transpose` for square matrices). -/
lemma IsMoorePenrose.transpose {n : Type*} [Fintype n] {X G : Matrix n n ℝ}
    (h : X.IsMoorePenrose G) : Xᵀ.IsMoorePenrose Gᵀ :=
  Matrix.IsMoorePenrose.transpose h

/-- The Moore–Penrose inverse is unique: the Penrose equations determine `X†` (the core
`Matrix.IsMoorePenrose.unique` for square matrices). -/
theorem IsMoorePenrose.unique {n : Type*} [Fintype n] {X G H : Matrix n n ℝ}
    (hG : X.IsMoorePenrose G) (hH : X.IsMoorePenrose H) : G = H :=
  Matrix.IsMoorePenrose.unique hG hH

/-- Key identity (paper, proof of Proposition 3.3): if `U` has orthonormal rows and `C` is
invertible, then `Uᵀ C⁻¹ U` satisfies the Penrose equations for `Uᵀ C U`. This is the core
`Matrix.isMoorePenrose_mul_mul_transpose` for the orthonormal columns `Uᵀ`. -/
theorem isMoorePenrose_orthonormal_sandwich {k d : Type*} [Fintype k] [DecidableEq k]
    [Fintype d]
    (U : Matrix k d ℝ) (hU : U * Uᵀ = 1) (C : Matrix k k ℝ) (hC : IsUnit C.det) :
    (Uᵀ * C * U).IsMoorePenrose (Uᵀ * C⁻¹ * U) := by
  have hU' : Uᵀᵀ * Uᵀ = 1 := by rwa [Matrix.transpose_transpose]
  simpa only [Matrix.transpose_transpose] using
    Matrix.isMoorePenrose_mul_mul_transpose hU' hU' hC

/-- The paper's identity `(Uᵀ C U)† = Uᵀ C⁻¹ U` (proof of Proposition 3.3), for `U` with orthonormal
rows and `C` invertible: any Moore–Penrose inverse of `Uᵀ C U` equals `Uᵀ C⁻¹ U`. -/
theorem moorePenrose_orthonormal_sandwich {k d : Type*} [Fintype k] [DecidableEq k]
    [Fintype d]
    (U : Matrix k d ℝ) (hU : U * Uᵀ = 1) (C : Matrix k k ℝ) (hC : IsUnit C.det)
    {G : Matrix d d ℝ} (hG : (Uᵀ * C * U).IsMoorePenrose G) :
    G = Uᵀ * C⁻¹ * U :=
  hG.unique (isMoorePenrose_orthonormal_sandwich U hU C hC)

/-- The paper's identity `(Uᵀ C U)† = Uᵀ C⁻¹ U` (proof of Proposition 3.3) with the core
Moore–Penrose inverse `Matrix.pinv`, for `U` with orthonormal rows and `C` invertible. -/
theorem pinv_orthonormal_sandwich {k d : Type*} [Fintype k] [DecidableEq k]
    [Fintype d] [DecidableEq d]
    (U : Matrix k d ℝ) (hU : U * Uᵀ = 1) (C : Matrix k k ℝ) (hC : IsUnit C.det) :
    (Uᵀ * C * U).pinv = Uᵀ * C⁻¹ * U :=
  (isMoorePenrose_orthonormal_sandwich U hU C hC).eq_pinv.symm

/-- Non-vacuity: `U = (1, 0)` has orthonormal rows and `C = (2)` is invertible, so the identity
applies to the instance `Uᵀ C U = [[2, 0], [0, 0]]`. -/
example : (!![(1 : ℝ), 0]ᵀ * !![(2 : ℝ)] * !![(1 : ℝ), 0]).IsMoorePenrose
    (!![(1 : ℝ), 0]ᵀ * !![(2 : ℝ)]⁻¹ * !![(1 : ℝ), 0]) := by
  have hU : (!![(1 : ℝ), 0] : Matrix (Fin 1) (Fin 2) ℝ) * !![(1 : ℝ), 0]ᵀ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hC : IsUnit (!![(2 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ).det := by
    rw [Matrix.det_fin_one_of]
    exact isUnit_iff_ne_zero.mpr two_ne_zero
  exact isMoorePenrose_orthonormal_sandwich _ hU _ hC

/-- The local square-matrix Penrose predicate of this file, replaced by the core
`Matrix.IsMoorePenrose` (same four equations). -/
@[deprecated "use the core `Matrix.IsMoorePenrose`" (since := "2026-11-09")]
abbrev IsMoorePenrose {n : Type*} [Fintype n] (X G : Matrix n n ℝ) : Prop :=
  Matrix.IsMoorePenrose X G

end LeanDLRA.Literature.P2607_27438
