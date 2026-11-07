import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Auto
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Results of arXiv 2607.27438: Dynamical low-rank smoothing

This module proves the Moore–Penrose identity that the paper uses in the proofs of its
DLRA-JMCO smoothers (Propositions 3.3 and 4.1). Let `U ∈ ℝ^{k×d}` have orthonormal rows,
`U Uᵀ = 1`, and let `C ∈ ℝ^{k×k}` be invertible (the paper's covariance `C_Ŷ`, assumed full rank
there). Then `(Uᵀ C U)† = Uᵀ C⁻¹ U`, where `†` is the Moore–Penrose inverse of the `d × d` matrix
`Uᵀ C U` (the paper's `Ĉ`). The paper states this identity in the proof of Proposition 3.3 and
uses it for the gain in Proposition 4.1.

Contents:

* `IsMoorePenrose X G`: the four Penrose equations, a definition of `G = X†` for square matrices.
* `IsMoorePenrose.unique`: the Moore–Penrose inverse is unique, so `G = X†` is well defined.
* `isMoorePenrose_orthonormal_sandwich`: `Uᵀ C⁻¹ U` satisfies the Penrose equations for `Uᵀ C U`.
* `moorePenrose_orthonormal_sandwich`: the paper's identity `(Uᵀ C U)† = Uᵀ C⁻¹ U`.
* `example`: a non-vacuous instance with `k = 1`, `d = 2`, `U = (1, 0)` and `C = (2)`.

Core definitions: the library has no Moore–Penrose inverse on matrices (only the Penrose conditions
written in comments), so `IsMoorePenrose` is defined locally from Mathlib's `Matrix` and `⁻¹`.

Left out, not formalized: Propositions 3.1 and 3.2 (the classical and ensemble Rauch–Tung–Striebel
smoothers, cited from the literature), Propositions 3.3 and 4.1 themselves (the mean, covariance and
basis update formulas), and the stochastic forward step (11)–(12) and the algorithm of Section 3.
The smoother formulas depend on the RTS formulas, which are not derived here and are not assumed as
hypotheses, so the smoother statements are not proved. The range invariance `U^s_k = U_k` is not
formalized either.
-/

open scoped Matrix

namespace LeanDLRA.Literature.P2607_27438

/-- The Penrose equations: `IsMoorePenrose X G` says that `G` is the Moore–Penrose inverse `X†` of
the square matrix `X`, namely `X G X = X`, `G X G = G`, and `X G`, `G X` are symmetric. -/
structure IsMoorePenrose {n : Type*} [Fintype n] (X G : Matrix n n ℝ) : Prop where
  xgx : X * G * X = X
  gxg : G * X * G = G
  xg_symm : (X * G)ᵀ = X * G
  gx_symm : (G * X)ᵀ = G * X

/-- The Penrose equations are stable under transposition. -/
lemma IsMoorePenrose.transpose {n : Type*} [Fintype n] {X G : Matrix n n ℝ}
    (h : IsMoorePenrose X G) : IsMoorePenrose Xᵀ Gᵀ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg Matrix.transpose h.xgx
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · have := congrArg Matrix.transpose h.gxg
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · have := h.gx_symm
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this ⊢
    exact this.symm
  · have := h.xg_symm
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this ⊢
    exact this.symm

/-- Step of the uniqueness proof: two Moore–Penrose inverses of `X` give the same product `X G`. -/
private lemma xg_eq_of_penrose {n : Type*} [Fintype n] {X G H : Matrix n n ℝ}
    (hG : IsMoorePenrose X G) (hH : IsMoorePenrose X H) : X * G = X * H := by
  have h1 : (X * G) * (X * H) = X * H := by
    calc (X * G) * (X * H) = X * G * X * H := by simp [Matrix.mul_assoc]
      _ = X * H := by rw [hG.xgx]
  have h2 : (X * H) * (X * G) = X * G := by
    calc (X * H) * (X * G) = X * H * X * G := by simp [Matrix.mul_assoc]
      _ = X * G := by rw [hH.xgx]
  calc X * G = (X * G)ᵀ := hG.xg_symm.symm
    _ = ((X * H) * (X * G))ᵀ := by rw [h2]
    _ = (X * G)ᵀ * (X * H)ᵀ := Matrix.transpose_mul _ _
    _ = (X * G) * (X * H) := by rw [hG.xg_symm, hH.xg_symm]
    _ = X * H := h1

/-- The Moore–Penrose inverse is unique: the Penrose equations determine `X†`. -/
theorem IsMoorePenrose.unique {n : Type*} [Fintype n] {X G H : Matrix n n ℝ}
    (hG : IsMoorePenrose X G) (hH : IsMoorePenrose X H) : G = H := by
  have hXG : X * G = X * H := xg_eq_of_penrose hG hH
  have hGX : G * X = H * X := by
    have hT := xg_eq_of_penrose hG.transpose hH.transpose
    have := congrArg Matrix.transpose hT
    simpa [Matrix.transpose_mul] using this
  calc G = G * X * G := hG.gxg.symm
    _ = G * (X * G) := Matrix.mul_assoc G X G
    _ = G * (X * H) := by rw [hXG]
    _ = G * X * H := (Matrix.mul_assoc G X H).symm
    _ = H * X * H := by rw [hGX]
    _ = H := hH.gxg

/-- Key identity (paper, proof of Proposition 3.3): if `U` has orthonormal rows and `C` is
invertible, then `Uᵀ C⁻¹ U` satisfies the Penrose equations for `Uᵀ C U`. -/
theorem isMoorePenrose_orthonormal_sandwich {k d : Type*} [Fintype k] [DecidableEq k]
    [Fintype d]
    (U : Matrix k d ℝ) (hU : U * Uᵀ = 1) (C : Matrix k k ℝ) (hC : IsUnit C.det) :
    IsMoorePenrose (Uᵀ * C * U) (Uᵀ * C⁻¹ * U) := by
  have hC1 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hC
  have hC2 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hC
  have hUU : ∀ M : Matrix k d ℝ, U * (Uᵀ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hCC1 : ∀ M : Matrix k d ℝ, C⁻¹ * (C * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hC1, Matrix.one_mul]
  have hCC2 : ∀ M : Matrix k d ℝ, C * (C⁻¹ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hC2, Matrix.one_mul]
  have hXG : Uᵀ * C * U * (Uᵀ * C⁻¹ * U) = Uᵀ * U := by
    simp only [Matrix.mul_assoc, hUU, hCC2]
  have hGX : Uᵀ * C⁻¹ * U * (Uᵀ * C * U) = Uᵀ * U := by
    simp only [Matrix.mul_assoc, hUU, hCC1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, hUU, hCC2]
  · simp only [Matrix.mul_assoc, hUU, hCC1]
  · rw [hXG]
    simp [Matrix.transpose_mul]
  · rw [hGX]
    simp [Matrix.transpose_mul]

/-- The paper's identity `(Uᵀ C U)† = Uᵀ C⁻¹ U` (proof of Proposition 3.3), for `U` with orthonormal
rows and `C` invertible: any Moore–Penrose inverse of `Uᵀ C U` equals `Uᵀ C⁻¹ U`. -/
theorem moorePenrose_orthonormal_sandwich {k d : Type*} [Fintype k] [DecidableEq k]
    [Fintype d]
    (U : Matrix k d ℝ) (hU : U * Uᵀ = 1) (C : Matrix k k ℝ) (hC : IsUnit C.det)
    {G : Matrix d d ℝ} (hG : IsMoorePenrose (Uᵀ * C * U) G) :
    G = Uᵀ * C⁻¹ * U :=
  hG.unique (isMoorePenrose_orthonormal_sandwich U hU C hC)

/-- Non-vacuity: `U = (1, 0)` has orthonormal rows and `C = (2)` is invertible, so the identity
applies to the instance `Uᵀ C U = [[2, 0], [0, 0]]`. -/
example : IsMoorePenrose (!![(1 : ℝ), 0]ᵀ * !![(2 : ℝ)] * !![(1 : ℝ), 0])
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

end LeanDLRA.Literature.P2607_27438
