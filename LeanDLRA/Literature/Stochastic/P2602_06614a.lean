import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Results of arXiv 2602.06614: Dynamical low-rank ensemble Kalman filter

Formalizes the Woodbury form of the semi-implicit analysis step of the paper (Sec. 2.2, eq. (11)),
in finite dimensions over `ℝ` with the Kalman gain `K = P Hᵀ (Γ + Δt H P Hᵀ)⁻¹`:
`analysis_woodbury` shows that `(I + Δt P Hᵀ Γ⁻¹ H) X^a = X^f + P Hᵀ Γ⁻¹ W` implies
`X^a = (I - Δt K H) X^f + K W`, with `W` arbitrary and invertibility derived from `Γ` positive
definite, `P` positive semidefinite and `Δt ≥ 0`.  Helper lemmas `inv_identities` and
`inv_mul_identity` give the inverse identities behind it, and an example checks that the
hypotheses are satisfiable.

Core definitions: none are used, since the core library has no Kalman gain or ensemble analysis
object; the Kalman gain `kalmanGain` is defined locally from matrices.

Not formalized (left out): eqs. (18)-(21) (DLR analysis equals EnKF on `span U`), the forecast
claim of Sec. 3.1 (mean separation `E_N[U S̃ Yᵀ] = 0`), and the signal-tracking claims of Sec. 3.1.2
(in-range assimilation and covariance underestimation).  The rank-adaptive truncation rule of
eq. (22), Sec. 3.1.1, is already proved in `LeanDLRA/Matrix/LowRankDistance.lean` as
`epsRank_augmented_le`, so it is not repeated here.  The eq. (11) bracket `W` is not tied to the
paper's Δt placement: the lemma holds for any `W`.
-/

open Set Finset
open scoped Matrix

namespace LeanDLRA.Literature.P2602_06614

variable {n k m : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- The Kalman gain `K = P Hᵀ (Γ + Δt H P Hᵀ)⁻¹` of arXiv 2602.06614, Sec. 2.2 (the gain of
eq. (11), with `H̄`, `P^f` and `Γ` in the roles of `H`, `P` and `Γ`). -/
noncomputable def kalmanGain (dt : ℝ) (P : Matrix n n ℝ) (H : Matrix k n ℝ) (Γ : Matrix k k ℝ) :
    Matrix n k ℝ :=
  P * Hᵀ * (Γ + dt • (H * P * Hᵀ))⁻¹

/-- Two inverse identities for `G = Γ + Δt A`: `Γ⁻¹ = G⁻¹ + Δt Γ⁻¹ A G⁻¹` and
`G⁻¹ = Γ⁻¹ - Δt G⁻¹ A Γ⁻¹`. -/
lemma inv_identities {Γ A G : Matrix k k ℝ} {dt : ℝ} (hΓ : IsUnit Γ.det)
    (hG : IsUnit G.det) (hGdef : G = Γ + dt • A) :
    Γ⁻¹ = G⁻¹ + dt • (Γ⁻¹ * A * G⁻¹) ∧ G⁻¹ = Γ⁻¹ - dt • (G⁻¹ * A * Γ⁻¹) := by
  have h1 : Γ⁻¹ * G = 1 + dt • (Γ⁻¹ * A) := by
    rw [hGdef, Matrix.mul_add, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hΓ]
  have e1 : Γ⁻¹ = G⁻¹ + dt • (Γ⁻¹ * A * G⁻¹) := by
    calc Γ⁻¹ = Γ⁻¹ * G * G⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = (1 + dt • (Γ⁻¹ * A)) * G⁻¹ := by rw [h1]
      _ = G⁻¹ + dt • (Γ⁻¹ * A * G⁻¹) := by rw [add_mul, one_mul, smul_mul_assoc]
  have h2 : G⁻¹ * Γ = 1 - dt • (G⁻¹ * A) := by
    have hΓe : Γ = G - dt • A := by rw [hGdef]; abel
    rw [hΓe, Matrix.mul_sub, Matrix.nonsing_inv_mul _ hG, Matrix.mul_smul]
  have e2 : G⁻¹ = Γ⁻¹ - dt • (G⁻¹ * A * Γ⁻¹) := by
    calc G⁻¹ = (G⁻¹ * Γ) * Γ⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hΓ, Matrix.mul_one]
      _ = (1 - dt • (G⁻¹ * A)) * Γ⁻¹ := by rw [h2]
      _ = Γ⁻¹ - dt • (G⁻¹ * A * Γ⁻¹) := by rw [sub_mul, one_mul, smul_mul_assoc]
  exact ⟨e1, e2⟩

/-- The semi-implicit operator `1 + Δt P Hᵀ Γ⁻¹ H` has inverse `1 - Δt K H`, with `K` the
Kalman gain (algebraic core of the Woodbury step of eq. (11)). -/
lemma inv_mul_identity (X : Matrix n k ℝ) (Y : Matrix k n ℝ) {Γ G A : Matrix k k ℝ} {dt : ℝ}
    (hΓ : IsUnit Γ.det) (hG : IsUnit G.det) (hGdef : G = Γ + dt • A) (hA : A = Y * X) :
    (1 + dt • (X * Γ⁻¹ * Y)) * (1 - dt • (X * G⁻¹ * Y)) = 1 := by
  obtain ⟨e1, -⟩ := inv_identities hΓ hG hGdef
  have h0 : Γ⁻¹ - G⁻¹ - dt • (Γ⁻¹ * A * G⁻¹) = 0 := by
    rw [sub_sub, ← e1, sub_self]
  have expand : (1 + dt • (X * Γ⁻¹ * Y)) * (1 - dt • (X * G⁻¹ * Y)) =
      1 + dt • (X * (Γ⁻¹ - G⁻¹ - dt • (Γ⁻¹ * A * G⁻¹)) * Y) := by
    subst hA
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_one, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.sub_mul]
    module
  rw [expand, h0]
  simp

/-- **Woodbury form of the semi-implicit analysis**
(arXiv 2602.06614, Sec. 2.2, eq. (11)).  Let `P` be positive semidefinite
(the sample covariance `P^f`), `Γ` positive definite and `Δt ≥ 0`. If the semi-implicit analysis
`(I + Δt P Hᵀ Γ⁻¹ H) X^a = X^f + P Hᵀ Γ⁻¹ W` holds, then
`X^a = (I - Δt K H) X^f + K W` with `K = P Hᵀ (Γ + Δt H P Hᵀ)⁻¹`.
The residual `W` is arbitrary (it collects the bracket of eq. (11), so the placement of `Δt` in
the paper's bracket is irrelevant).  Invertibility of `Γ` and of `Γ + Δt H P Hᵀ` is derived
from positive definiteness rather than assumed. -/
theorem analysis_woodbury (dt : ℝ) (hdt : 0 ≤ dt) (P : Matrix n n ℝ) (hP : P.PosSemidef)
    (H : Matrix k n ℝ) (Γ : Matrix k k ℝ) (hΓ : Γ.PosDef) (Xf Xa : Matrix n m ℝ)
    (W : Matrix k m ℝ)
    (hscheme : (1 + dt • (P * Hᵀ * Γ⁻¹ * H)) * Xa = Xf + P * Hᵀ * Γ⁻¹ * W) :
    Xa = (1 - dt • (kalmanGain dt P H Γ * H)) * Xf + kalmanGain dt P H Γ * W := by
  have hΓu : IsUnit Γ.det := (Matrix.isUnit_iff_isUnit_det _).mp hΓ.isUnit
  have hA : (H * P * Hᵀ).PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same H
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hGpd : (Γ + dt • (H * P * Hᵀ)).PosDef := hΓ.add_posSemidef (hA.smul hdt)
  obtain ⟨G, hGdef⟩ : ∃ G, G = Γ + dt • (H * P * Hᵀ) := ⟨_, rfl⟩
  have hGu : IsUnit G.det := by
    rw [hGdef]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hGpd.isUnit
  have hMN := inv_mul_identity (P * Hᵀ) H hΓu hGu hGdef (Matrix.mul_assoc _ _ _)
  have hNM : (1 - dt • (P * Hᵀ * G⁻¹ * H)) * (1 + dt • (P * Hᵀ * Γ⁻¹ * H)) = 1 :=
    mul_eq_one_comm.mp hMN
  have hK : (1 - dt • (P * Hᵀ * G⁻¹ * H)) * (P * Hᵀ * Γ⁻¹) = P * Hᵀ * G⁻¹ := by
    obtain ⟨-, e2⟩ := inv_identities hΓu hGu hGdef
    have hprod : (P * Hᵀ * G⁻¹ * H) * (P * Hᵀ * Γ⁻¹) =
        P * Hᵀ * (G⁻¹ * (H * P * Hᵀ) * Γ⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hprod]
    conv_rhs => rw [e2]
    rw [Matrix.mul_sub, Matrix.mul_smul]
  unfold kalmanGain
  rw [← hGdef]
  set A : Matrix n n ℝ := 1 - dt • (P * Hᵀ * G⁻¹ * H) with hAdef
  calc Xa = A * ((1 + dt • (P * Hᵀ * Γ⁻¹ * H)) * Xa) := by
        rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
    _ = A * (Xf + P * Hᵀ * Γ⁻¹ * W) := by rw [hscheme]
    _ = A * Xf + (A * (P * Hᵀ * Γ⁻¹)) * W := by
        rw [Matrix.mul_add, Matrix.mul_assoc A (P * Hᵀ * Γ⁻¹) W]
    _ = A * Xf + P * Hᵀ * G⁻¹ * W := by rw [hK]

/-- Non-vacuity: the hypotheses of `analysis_woodbury` hold for `n = k = m = Fin 1`,
`P = Γ = H = 1`, `Δt = 1`, `X^f = X^a = W = 1`. -/
example : True := by
  have := analysis_woodbury (n := Fin 1) (k := Fin 1) (m := Fin 1) 1 zero_le_one 1
    Matrix.PosSemidef.one 1 1 Matrix.PosDef.one 1 1 1 (by simp)
  trivial

end LeanDLRA.Literature.P2602_06614
