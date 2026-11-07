import LeanDLRA.Matrix.GaugeODE
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2509.11210: DLR Kalman filtering

Deterministic cores of the DLR Kalman–Bucy results (Nobile–Trigo Trindade). Stochastic calculus,
conditional expectations and the Itô derivations are not formalized; each statement below is the
matrix identity behind a result of the paper.

* `physical_modes_orthonormal` (Lemma 3.2, orthonormality part; eq. (4.2)): if the physical modes
  solve `U̇ = (I − U Uᵀ) A U` on `[0, ∞)` with `Uᵀ U = I` at time `0`, then `Uᵀ U = I` for
  all `t ≥ 0`. It reuses `LeanDLRA.transpose_mul_self_eq_one_of_odeSolution` (Grönwall on
  `I − Uᵀ U`), with `G(t) = A U(t)` so that the field is the library's `(1 − X Xᵀ) G t`.
* `covariance_range` (Lemma 3.2, range part; eq. (3.10)): for `Uᵀ U = I` and `P = U M Uᵀ`,
  `Π P = P = P Π` for `Π = U Uᵀ`, and `range P ⊆ range U`. The representation (3.10) itself,
  which the paper derives from the conditional covariance, is taken as the hypothesis `P = U M Uᵀ`.
* `dlr_covariance_hasDerivAt_iff` (Proposition 4.1, deterministic core; eqs. (4.2), (4.8), (4.13)):
  for `P = U M Uᵀ` with `Uᵀ U = I` and `U̇ = (I − U Uᵀ) A U` at time `t`, the Gram equation
  `Ṁ = Uᵀ A U M + M Uᵀ Aᵀ U − M Uᵀ S U M + Uᵀ Sg U` holds iff the covariance equation
  `Ṗ = A P + P Aᵀ − P S P + Π Sg Π` holds. Only the model-noise term is projected. Neither side is
  assumed: the Gram equation is not a hypothesis, the equivalence is proved. The Itô identity that
  gives `Ṗ` from the filter is not formalized.

Core definitions used: `LeanDLRA.transpose_mul_self_eq_one_of_odeSolution`, `ODESolution`
(`LeanDLRA/Foundations/ODE.lean`), and the Frobenius-normed product rule
`LeanDLRA.Frobenius.hasDerivAt_mul_mul` and `hasDerivAt_transpose`. No new structure is defined.
`Uᵀ` is `Matrix.transpose`; `Π = U * Uᵀ` (with `Uᵀ * U = 1`) is the orthogonal projector onto
`range U`. The paper's `S = Hᵀ Γ⁻¹ H` and the noise covariance `Sg` (Σ) are arbitrary real
matrices here (no positivity is needed for the identities). The hypotheses are satisfiable: the
constant `U = (1, 0)ᵀ` satisfies `Uᵀ U = 1` and `U̇ = 0` (`instU_orthonormal`).

Not formalized:
* Proposition 4.3 (convergence of the Oja/Brockett flow for almost every `U₀`): it needs the
  Łojasiewicz/Kurdyka argument and saddle-point measure-zero results, not in Mathlib.
* Proposition 4.4 (moment error bounds with constants `C₁(T), C₂(T)`): the covariance bound
  `(4.12)` is a Grönwall argument on `‖ΔP‖_F²` with the paper's explicit constant, not finished
  here; the mean bound `(4.11)` is stochastic. The library's
  `dlrKalmanBucy_covariance_error_uniform` (`LeanDLRA/Stochastic/KalmanBucy.lean`) proves a
  different, time-uniform estimate.
* Lemma 3.2 for the stochastic modes (conditional mean `E[X_t | 𝒜_{Z_t}] = U_0`, and (3.10) from
  the conditional expectation).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2509_11210

variable {d R : ℕ}

/-- Cancellation `Uᵀ (U X) = X` when `Uᵀ U = I`. -/
private lemma transpose_mul_cancel {n : Type*} {U : Matrix (Fin d) (Fin R) ℝ}
    (hUU : Uᵀ * U = 1) (X : Matrix (Fin R) n ℝ) : Uᵀ * (U * X) = X := by
  rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]

/-- **Physical modes stay orthonormal** (paper Lemma 3.2 and eq. (4.2), orthonormality part).
If `U : [0, ∞) → Mat(d × R)` is continuous, has right derivatives `U̇ = (I − U Uᵀ) A U` on
`[0, ∞)`, and `U(0)ᵀ U(0) = I`, then `U(t)ᵀ U(t) = I` for all `t ≥ 0`. Here `A` is any real
`d × d` matrix (the paper's `A` is not assumed symmetric for this part). -/
theorem physical_modes_orthonormal {A : Matrix (Fin d) (Fin d) ℝ}
    {U : ℝ → Matrix (Fin d) (Fin R) ℝ}
    (hc : ContinuousOn U (Set.Ici 0))
    (hU : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt U ((1 - U t * (U t)ᵀ) * (A * U t))
      (Set.Ici t) t)
    (h0 : (U 0)ᵀ * U 0 = 1) {t : ℝ} (ht : 0 ≤ t) : (U t)ᵀ * U t = 1 := by
  have hode : ODESolution (fun s X => (1 - X * Xᵀ) * (A * U s)) U 0 t :=
    { cont := hc.mono Set.Icc_subset_Ici_self
      deriv := fun s hs => hU s (Set.Ico_subset_Ici_self hs) }
  have hC : ∀ b' < t, ∃ C, ∀ s ∈ Set.Ico (0 : ℝ) b', ‖(U s)ᵀ * (A * U s)‖ ≤ C := by
    intro b' _
    have hcU : ContinuousOn U (Set.Icc 0 b') := hc.mono Set.Icc_subset_Ici_self
    have hg : Continuous fun X : Matrix (Fin d) (Fin R) ℝ => Xᵀ * (A * X) :=
      (continuous_id.matrix_transpose).matrix_mul (continuous_const.matrix_mul continuous_id)
    have hcont : ContinuousOn (fun s => (U s)ᵀ * (A * U s)) (Set.Icc 0 b') :=
      hg.comp_continuousOn hcU
    obtain ⟨C, hC⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
    exact ⟨C, fun s hs => hC s ⟨hs.1, hs.2.le⟩⟩
  exact LeanDLRA.transpose_mul_self_eq_one_of_odeSolution hode hC h0 t ⟨ht, le_rfl⟩

/-- **Range of the DLR covariance** (paper Lemma 3.2, "in particular"; eq. (3.10)). If
`Uᵀ U = I` and `P = U M Uᵀ`, then `Π = U Uᵀ` fixes `P` from both sides, and every vector in the
range of `P` lies in the range of `U`. -/
theorem covariance_range {U : Matrix (Fin d) (Fin R) ℝ} {M : Matrix (Fin R) (Fin R) ℝ}
    {P : Matrix (Fin d) (Fin d) ℝ} (hUU : Uᵀ * U = 1) (hP : P = U * M * Uᵀ) :
    U * Uᵀ * P = P ∧ P * (U * Uᵀ) = P ∧ ∀ x : Fin d → ℝ, ∃ y : Fin R → ℝ, P *ᵥ x = U *ᵥ y := by
  subst hP
  refine ⟨?_, ?_, fun x => ⟨M *ᵥ (Uᵀ *ᵥ x), ?_⟩⟩
  · simp only [Matrix.mul_assoc, transpose_mul_cancel hUU]
  · simp only [Matrix.mul_assoc, transpose_mul_cancel hUU]
  · simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Sandwich cancellation `Uᵀ (U X Uᵀ) U = X` when `Uᵀ U = I`. -/
private lemma sandwich_cancel {U : Matrix (Fin d) (Fin R) ℝ} (hUU : Uᵀ * U = 1)
    (X : Matrix (Fin R) (Fin R) ℝ) : Uᵀ * (U * X * Uᵀ) * U = X := by
  simp only [Matrix.mul_assoc, transpose_mul_cancel hUU, hUU, Matrix.mul_one]

/-- Algebra of the forward direction of Proposition 4.1: the product rule for `U M Uᵀ` with the
physical-mode flow `U̇ = (I − U Uᵀ) A U` and Gram derivative `N` gives the projected covariance
right-hand side. -/
private lemma covariance_deriv_alg {A S Sg : Matrix (Fin d) (Fin d) ℝ}
    {U : Matrix (Fin d) (Fin R) ℝ} {M N : Matrix (Fin R) (Fin R) ℝ} (_hUU : Uᵀ * U = 1)
    (hN : N = Uᵀ * A * U * M + M * (Uᵀ * Aᵀ * U) - M * (Uᵀ * S * U) * M + Uᵀ * Sg * U) :
    (1 - U * Uᵀ) * (A * U) * M * Uᵀ + U * N * Uᵀ + U * M * ((1 - U * Uᵀ) * (A * U))ᵀ
      = A * (U * M * Uᵀ) + U * M * Uᵀ * Aᵀ - U * M * Uᵀ * S * (U * M * Uᵀ)
        + U * Uᵀ * Sg * (U * Uᵀ) := by
  subst hN
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- Algebra of the backward direction of Proposition 4.1: the Gram derivative extracted from
`Uᵀ P U` equals the reduced Gram right-hand side. -/
private lemma gram_deriv_alg {A S Sg : Matrix (Fin d) (Fin d) ℝ}
    {U : Matrix (Fin d) (Fin R) ℝ} {M : Matrix (Fin R) (Fin R) ℝ} (hUU : Uᵀ * U = 1) :
    ((1 - U * Uᵀ) * (A * U))ᵀ * (U * M * Uᵀ) * U
      + Uᵀ * (A * (U * M * Uᵀ) + U * M * Uᵀ * Aᵀ - U * M * Uᵀ * S * (U * M * Uᵀ)
        + U * Uᵀ * Sg * (U * Uᵀ)) * U
      + Uᵀ * (U * M * Uᵀ) * ((1 - U * Uᵀ) * (A * U))
      = Uᵀ * A * U * M + M * (Uᵀ * Aᵀ * U) - M * (Uᵀ * S * U) * M + Uᵀ * Sg * U := by
  simp only [Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, transpose_mul_cancel hUU, hUU]
  abel

/-- **Covariance ODE of the DLR Kalman–Bucy filter, deterministic core** (paper Proposition 4.1,
eqs. (4.7)–(4.8), with the Gram equation (4.13) of Lemma 4.5 derived rather than assumed).

Let `U` be the physical modes with `Uᵀ U = I` and `U̇ = (I − U Uᵀ) A U` at time `t`, and let
`P = U M Uᵀ` with `M` the Gram matrix. Then the Gram derivative `Ṁ` satisfies the reduced equation
`Ṁ = Uᵀ A U M + M Uᵀ Aᵀ U − M Uᵀ S U M + Uᵀ Sg U` if and only if `P` satisfies the covariance
equation `Ṗ = A P + P Aᵀ − P S P + Π Sg Π`, `Π = U Uᵀ`. Only the model-noise term `Sg` is projected.
The Itô derivation of `Ṗ` from the filter is not formalized. -/
theorem dlr_covariance_hasDerivAt_iff {A S Sg : Matrix (Fin d) (Fin d) ℝ}
    {U : ℝ → Matrix (Fin d) (Fin R) ℝ} {M : ℝ → Matrix (Fin R) (Fin R) ℝ}
    {P : ℝ → Matrix (Fin d) (Fin d) ℝ} {t : ℝ} {M' : Matrix (Fin R) (Fin R) ℝ}
    (hUU : ∀ s, (U s)ᵀ * U s = 1)
    (hU : HasDerivAt U ((1 - U t * (U t)ᵀ) * (A * U t)) t)
    (hP : ∀ s, P s = U s * M s * (U s)ᵀ)
    (hM : HasDerivAt M M' t) :
    M' = (U t)ᵀ * A * U t * M t + M t * ((U t)ᵀ * Aᵀ * U t)
        - M t * ((U t)ᵀ * S * U t) * M t + (U t)ᵀ * Sg * U t ↔
      HasDerivAt P
        (A * P t + P t * Aᵀ - P t * S * P t + (U t * (U t)ᵀ) * Sg * (U t * (U t)ᵀ)) t := by
  have hUt := hUU t
  have hPf : P = fun s => U s * M s * (U s)ᵀ := funext hP
  have hPt : P t = U t * M t * (U t)ᵀ := hP t
  have hUd := LeanDLRA.Frobenius.hasDerivAt_transpose hU
  constructor
  · intro hMeq
    rw [hPt, hPf]
    convert LeanDLRA.Frobenius.hasDerivAt_mul_mul hU hM hUd using 1
    rw [hMeq]
    exact (covariance_deriv_alg hUt rfl).symm
  · intro hPd
    have hMf : M = fun s => (U s)ᵀ * P s * U s := by
      funext s
      rw [hP s, sandwich_cancel (hUU s)]
    have hMd := LeanDLRA.Frobenius.hasDerivAt_mul_mul hUd hPd hU
    rw [← hMf] at hMd
    have hMeq := hM.unique hMd
    rw [hMeq, hPt]
    exact gram_deriv_alg hUt

/-- The constant orthonormal column `(1, 0)ᵀ` used to show the hypotheses are satisfiable. -/
private def instU : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The constant column `instU` satisfies `Uᵀ U = I`. -/
private lemma instU_orthonormal : instUᵀ * instU = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [instU, Matrix.mul_apply, Fin.sum_univ_two]

end LeanDLRA.Literature.P2509_11210
