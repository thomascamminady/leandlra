import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Low-rank BUG solver for the Sylvester equation: exact bases (arXiv 2511.01735, Sec. 2)

Source: G. Vretinaris, *A Low-Rank BUG Method for Sylvester-Type Equations*, arXiv:2511.01735,
Section 2 ("Low-Rank BUG Sylvester Solver"), matrix case only. Real matrices throughout.

Setting, as in the paper: `A` is `m × m`, `B` is `n × n`, `C` is `m × n`, and `A X + X Bᵀ = C`
(paper Eq. (1)). The solution is `X = U S Vᵀ` with `Uᵀ U = 1`, `Vᵀ V = 1` and `S` nonsingular.
The paper's reduced equations are:

* K-step: `A K + K (Vᵀ B V)ᵀ = C V` with `K = U S`;
* L-step: `B L + L (Uᵀ A U)ᵀ = Cᵀ U` with `L = V Sᵀ`;
* S-step (Galerkin): `(Uhᵀ A Uh) S + S (Vhᵀ B Vh)ᵀ = Uhᵀ C Vh`, where `Uh = orth(K)` and
  `Vh = orth(L)`.

Proved here:

* `kStep_exact`: `K = U S` solves the K-step equation.
* `lStep_exact`: `L = V Sᵀ` solves the L-step equation.
* `orth_eq_mul_of_qr`: if `U S = Uh R` with `Uhᵀ Uh = 1` (a QR factorization, `R` square), then
  `Uh = U Q` for an orthogonal `Q`. This is the content of "orth returns an orthonormal basis of
  the range of `K`", derived from `S` nonsingular.
* `galerkin_exact_bases`: for `Uh = orth(K)` and `Vh = orth(L)` there is an `r × r` matrix `S'`
  with `Uh S' Vhᵀ = X` that solves the S-step equation. The S-step solution is a representation
  of `X` in the new bases, not a claim that `S'` is unique.
* An `example` (non-vacuity) with `1 × 1` matrices shows that the hypotheses of
  `galerkin_exact_bases` can hold.

Formalization choices:

* `orth(K)` is modeled by any `Uh` with `Uhᵀ Uh = 1` and `K = Uh R` for some square `R`. This is
  exactly what a QR decomposition provides.
* The paper's Stiefel and nonsingularity conditions are the hypotheses `Uᵀ * U = 1`,
  `Vᵀ * V = 1` and `IsUnit S.det`.

Not formalized, and left out on purpose:

* Algorithms 1 and 2 (the fixed-rank and rank-adaptive iterations, truncation by SVD, stopping
  rule). They are procedures, not theorems, and the paper proves no convergence result for
  them.
* Section 3 (Tucker extension, Algorithm 3). It consists of derivations of Eqs. (6)-(11) with no
  stated theorem, and it needs a mode-product layer that the library does not have.
-/

namespace LeanDLRA.Literature.P2511_01735

open scoped Matrix

variable {m n r : ℕ}

/-- **K-step solves the reduced equation** (paper, K-step): if `X = U S Vᵀ` solves
`A X + X Bᵀ = C` and `Vᵀ V = 1`, then `K = U S` solves `A K + K (Vᵀ B V)ᵀ = C V`. -/
theorem kStep_exact {A : Matrix (Fin m) (Fin m) ℝ} {B : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin r) ℝ}
    {V : Matrix (Fin n) (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    (hV : Vᵀ * V = 1) (hX : A * (U * S * Vᵀ) + (U * S * Vᵀ) * Bᵀ = C) :
    A * (U * S) + (U * S) * (Vᵀ * B * V)ᵀ = C * V := by
  have h1 : (A * (U * S * Vᵀ) + (U * S * Vᵀ) * Bᵀ) * V
      = A * (U * S) + U * S * (Vᵀ * Bᵀ * V) := by
    rw [Matrix.add_mul]
    congr 1
    · simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
    · simp only [Matrix.mul_assoc]
  have h2 : (Vᵀ * B * V)ᵀ = Vᵀ * Bᵀ * V := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h2, ← h1, hX]

/-- **L-step solves the reduced equation** (paper, L-step): if `X = U S Vᵀ` solves
`A X + X Bᵀ = C` and `Uᵀ U = 1`, then `L = V Sᵀ` solves `B L + L (Uᵀ A U)ᵀ = Cᵀ U`. -/
theorem lStep_exact {A : Matrix (Fin m) (Fin m) ℝ} {B : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin r) ℝ}
    {V : Matrix (Fin n) (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hX : A * (U * S * Vᵀ) + (U * S * Vᵀ) * Bᵀ = C) :
    B * (V * Sᵀ) + (V * Sᵀ) * (Uᵀ * A * U)ᵀ = Cᵀ * U := by
  have hT : V * Sᵀ * Uᵀ * Aᵀ + B * (V * Sᵀ * Uᵀ) = Cᵀ := by
    have h := congrArg Matrix.transpose hX
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose] at h
    simpa only [Matrix.mul_assoc] using h
  have h2 : (Uᵀ * A * U)ᵀ = Uᵀ * Aᵀ * U := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have h3 : (V * Sᵀ * Uᵀ * Aᵀ + B * (V * Sᵀ * Uᵀ)) * U
      = V * Sᵀ * (Uᵀ * Aᵀ * U) + B * (V * Sᵀ) := by
    rw [Matrix.add_mul]
    congr 1
    · simp only [Matrix.mul_assoc]
    · simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [h2, add_comm, ← h3, hT]

/-- **Orthonormal QR factor is a rotation of `U`**: let `U` have orthonormal columns and
`S` be nonsingular. If `U S = Uh R` with `Uhᵀ Uh = 1` (a QR decomposition of `K = U S`), then
`Uh = U Q` for an orthogonal `r × r` matrix `Q`. -/
theorem orth_eq_mul_of_qr {U : Matrix (Fin m) (Fin r) ℝ} (hU : Uᵀ * U = 1)
    {S : Matrix (Fin r) (Fin r) ℝ} (hS : IsUnit S.det)
    {W : Matrix (Fin m) (Fin r) ℝ} (hW : Wᵀ * W = 1) {R : Matrix (Fin r) (Fin r) ℝ}
    (hK : U * S = W * R) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ, W = U * Q ∧ Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 := by
  obtain ⟨M, hUM⟩ : ∃ M : Matrix (Fin r) (Fin r) ℝ, U = W * M := by
    refine ⟨R * S⁻¹, ?_⟩
    calc U = U * S * S⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv S hS, Matrix.mul_one]
      _ = W * R * S⁻¹ := by rw [hK]
      _ = W * (R * S⁻¹) := Matrix.mul_assoc _ _ _
  have hMM : Mᵀ * M = 1 := by
    calc Mᵀ * M = Mᵀ * (Wᵀ * W) * M := by rw [hW, Matrix.mul_one]
      _ = (W * M)ᵀ * (W * M) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Uᵀ * U := by rw [hUM]
      _ = 1 := hU
  have hMM' : M * Mᵀ = 1 := mul_eq_one_comm.mp hMM
  refine ⟨Mᵀ, ?_, by rw [Matrix.transpose_transpose]; exact hMM',
    by rw [Matrix.transpose_transpose]; exact hMM⟩
  calc W = W * (M * Mᵀ) := by rw [hMM', Matrix.mul_one]
    _ = (W * M) * Mᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = U * Mᵀ := by rw [hUM]

/-- The S-step equation holds for any representation `X = Uh S' Vhᵀ` with orthonormal
`Uh`, `Vh`. -/
private theorem galerkin_of_sylvester {A : Matrix (Fin m) (Fin m) ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ} {C : Matrix (Fin m) (Fin n) ℝ}
    {Uh : Matrix (Fin m) (Fin r) ℝ} {Vh : Matrix (Fin n) (Fin r) ℝ}
    {S' : Matrix (Fin r) (Fin r) ℝ} (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1)
    (h : A * (Uh * S' * Vhᵀ) + (Uh * S' * Vhᵀ) * Bᵀ = C) :
    (Uhᵀ * A * Uh) * S' + S' * (Vhᵀ * B * Vh)ᵀ = Uhᵀ * C * Vh := by
  rw [show (Vhᵀ * B * Vh)ᵀ = Vhᵀ * Bᵀ * Vh by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc], ← h]
  calc (Uhᵀ * A * Uh) * S' + S' * (Vhᵀ * Bᵀ * Vh)
      = (Uhᵀ * A * Uh) * S' * (Vhᵀ * Vh) + (Uhᵀ * Uh) * S' * (Vhᵀ * Bᵀ * Vh) := by
        rw [hVh, hUh]; simp only [Matrix.mul_one, Matrix.one_mul]
    _ = Uhᵀ * (A * (Uh * S' * Vhᵀ) + (Uh * S' * Vhᵀ) * Bᵀ) * Vh := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- **Galerkin S-step on the exact bases** (paper, S-step with `Uh = orth(K)`, `Vh = orth(L)`):
for `X = U S Vᵀ` solving `A X + X Bᵀ = C` with `S` nonsingular, let `Uh` and `Vh` be
orthonormal bases produced by QR decompositions `U S = Uh R₁` and `V Sᵀ = Vh R₂`.
Then there is `S'` with `Uh S' Vhᵀ = X` solving `(Uhᵀ A Uh) S' + S' (Vhᵀ B Vh)ᵀ = Uhᵀ C Vh`.
The theorem does not claim that `S'` is unique. -/
theorem galerkin_exact_bases {A : Matrix (Fin m) (Fin m) ℝ} {B : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin r) ℝ}
    {V : Matrix (Fin n) (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hX : A * (U * S * Vᵀ) + (U * S * Vᵀ) * Bᵀ = C)
    {Uh : Matrix (Fin m) (Fin r) ℝ} {Vh : Matrix (Fin n) (Fin r) ℝ}
    {R₁ R₂ : Matrix (Fin r) (Fin r) ℝ}
    (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1) (hK : U * S = Uh * R₁)
    (hL : V * Sᵀ = Vh * R₂) :
    ∃ S' : Matrix (Fin r) (Fin r) ℝ, Uh * S' * Vhᵀ = U * S * Vᵀ ∧
      (Uhᵀ * A * Uh) * S' + S' * (Vhᵀ * B * Vh)ᵀ = Uhᵀ * C * Vh := by
  obtain ⟨Q, hQ, hQ1, hQ2⟩ := orth_eq_mul_of_qr hU hS hUh hK
  obtain ⟨P, hP, hP1, hP2⟩ :=
    orth_eq_mul_of_qr hV (by rw [Matrix.det_transpose]; exact hS) hVh hL
  have hrep : Uh * (Qᵀ * S * P) * Vhᵀ = U * S * Vᵀ := by
    have e : Uh * (Qᵀ * S * P) * Vhᵀ = U * (Q * Qᵀ) * S * (P * Pᵀ) * Vᵀ := by
      rw [hQ, hP]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hQ2, hP2]
    simp only [Matrix.mul_one]
  refine ⟨Qᵀ * S * P, hrep, galerkin_of_sylvester hUh hVh ?_⟩
  rw [hrep]
  exact hX

/-- Non-vacuity: the hypotheses of `galerkin_exact_bases` hold for `A = 2`, `B = 3`, `C = 5`,
`U = V = Uh = Vh = 1`, `S = R₁ = R₂ = 1` (so `X = 1` and `2 + 3 = 5`). -/
example := galerkin_exact_bases (A := !![2]) (B := !![3]) (C := !![5]) (U := !![1])
  (V := !![1]) (S := !![1]) (Uh := !![1]) (Vh := !![1]) (R₁ := !![1]) (R₂ := !![1])
  (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply])
  (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply])
  (by simp)
  (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct])
  (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply])
  (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply])
  (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply])

end LeanDLRA.Literature.P2511_01735
