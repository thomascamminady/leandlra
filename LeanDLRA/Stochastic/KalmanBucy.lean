import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.ODE
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.Filtering.Defs

/-!
# Dynamical low-rank Kalman–Bucy filters

One-sided Riccati stability, uniform-in-time covariance bounds and structural negative results
for DLR Kalman–Bucy filters (DLR-KBP of arXiv 2509.11210, the JMCO reduced filter of
arXiv 2607.27432 Sec. 3.6, the DLR-EnKF of arXiv 2602.06614).

**Scope.**  Stochastic content enters only through the deterministic covariance (Riccati)
equations and the Kalman analysis algebra: this file is an algebraic/analytic core on
`Matrix (Fin d) (Fin d) ℝ` with the Frobenius inner product; no stochastic calculus, no
probability spaces.

## Main results

* `riccatiField_isOneSidedLipschitzOn` (OP-SL-01): the Riccati field
  `R(P) = A P + P Aᵀ - ρ P² + Qn` (`ρ ≥ 0`) is one-sided Lipschitz with constant `μ` on the PSD
  cone whenever `xᵀ (A + Aᵀ) x ≤ μ |x|²`.  The proof uses `⟪X Aᵀ, X⟫ = ∑ᵢ xᵢᵀ Aᵀ xᵢ` (rows) and
  `⟪P Δ + Δ P', Δ⟫ ≥ 0` for PSD `P, P'`; no symmetry of `Δ` is required.
* `riccati_forcing_error_uniform`, `dlrKalmanBucy_covariance_error_uniform`,
  `jmcoKalmanBucy_covariance_error_uniform` (OP-SL-01, resolved in the deterministic form stated
  there): for `μ < 0`, `‖P̃ t - P t‖ ≤ e^{μ (t-a)} ‖P̃ a - P a‖ + η / |μ|`, uniformly in time,
  with `η` the DO defect `sup ‖Qn - Π Qn Π‖` resp. the JMCO defect `sup ‖Π⊥ Qn Π⊥‖`.
  **Beyond the literature:** arXiv 2509.11210 Prop. 4.4 has constants `C₁(T), C₂(T)` growing
  exponentially in `T`; here the covariance part is time-uniform under dissipativity, because
  the nonlinear term `-ρ P²` is monotone on the PSD cone (one-sided rather than Lipschitz
  estimate).  It shows that DLR Kalman–Bucy covariances do not drift away over long assimilation
  windows: the error is the noise defect divided by the dissipation rate.
* `dlrKalmanBucy_ne_of_noise_not_in_range` (OP-SL-02 (i), negative result): if `Π Qn ≠ Qn`
  (noise not contained in the DO mode space) and both filters start from the same covariance,
  the DLR-KBP and KBP covariances differ at all small positive times; `mul_eq_of_mul_mul_eq`
  (`Π Q Π = Q ⇒ Π Q = Q`).
* `norm_sq_noiseDefect_eq`, `norm_normalNoise_le_noiseDefect` (OP-SL-02 (ii)): the exact
  Pythagorean identity `‖Q - Π Q Π‖² = ‖Π⊥ Q Π⊥‖² + ‖Π Q Π⊥ + Π⊥ Q Π‖²`, so the JMCO defect never
  exceeds the DO defect, with equality iff the off-diagonal blocks vanish.  Combined with the
  uniform bounds this proves that the JMCO error level `η_J / |μ|` is at most the DO level.
* `hasDerivAt_rotatingMode`, `not_tendsto_rotatingMode_proj`,
  `rotatingMode_proj_periodic_nonconst` (OP-SL-13, negative result): for skew `A` with `A² = -1`
  the rank-one DO basis `U(t) = cos t u₀ + sin t A u₀` solves `U' = (1 - U Uᵀ) A U` exactly; for
  the 2D rotation generator the DO subspace projector is `π`-periodic, non-constant and has no
  limit as `t → ∞` (arXiv 2606.15843 Example 5.9).
* `josephCov_sub_analysisCov`, `josephCov_sub_posSemidef`, `analysisCov_mono` (OP-SL-20 (i),
  resolved): the Joseph identity `J(Π, K) - Σ(Π) = (K - K_Π) S (K - K_Π)ᵀ` and the one-step
  Loewner monotonicity `Πᵣ ⪯ Π ⇒ Σ(Πᵣ) ⪯ Σ(Π)` of the Kalman analysis covariance
  (overconfidence of truncated filters).
* `kalmanGain_lowRank`, `analysisCov_lowRank`, `one_sub_proj_mul_kalmanGain_lowRank`
  (arXiv 2602.06614 eqs. (18)–(21), Sec. 3.1.2): for a low-rank prior `U M Uᵀ` the Kalman
  analysis is the reduced analysis with observation operator `C U`, and the gain has no
  component outside `span U` (only in-range corrections are assimilated).
* `riccati_stationary_unique`, `riccati_attracts_stationary` (OP-SL-32, partial): uniqueness of
  the PSD stationary covariance and exponential attraction to it for `μ < 0` (existence of the
  stationary covariance is not proved).

## What remains open

* OP-SL-01: the mean-error bound (innovation-forced linear dynamics) and the derivation of the
  PSD property of the DLR covariance from the factor equations (assumed here as a hypothesis).
* OP-SL-02 (i): the quantitative claim that accuracy degrades with the noise level (only
  immediate separation is proved); (ii) the converse inequality between actual covariance
  errors (only the error *levels* are compared).
* OP-SL-13: the general rank-`r` formula `U(t) = e^{tA} U₀ e^{-tB}` with matrix exponentials and
  uniqueness of the DO solution (we give the explicit rank-one solution, which is the unique one
  since the field is locally Lipschitz, but uniqueness is not formalised here), and the
  invariant-measure consequence (no Dirac basis marginal), which needs the stochastic DO system.
* OP-SL-01, form of the bound: the defect bound `η` is assumed on the whole window `[a, b)`;
  applying the theorem with `b = t` gives the `sup_{s ≤ t}` form of the open-problem statement.
  The DLR covariance equation (Riccati with forcing `Πᵤ Qn Πᵤ`) is taken as the definition of
  DLR-KBP, as in the open-problem statement; it is exact for `P_D = U M Uᵀ` with `U` solving the
  DO mode equation `U' = (1 - U Uᵀ) A U` and `S = ρ I`, but that derivation is not formalised.
* OP-SL-20 (ii), (iii): multi-step covariance-deficit bounds and tracking of the discarded
  uncertainty.

The statements `riccatiField_isOneSidedLipschitzOn` and
`dlrKalmanBucy_covariance_error_uniform` are proved here
as `LeanDLRA.KalmanBucy.riccatiField_isOneSidedLipschitzOn` and
`LeanDLRA.KalmanBucy.dlrKalmanBucy_covariance_error_uniform`.

The Riccati field `LeanDLRA.riccatiField` (root namespace), the rotating mode `rotatingMode`, the
analysis-step matrices `innovCov`, `kalmanGain`, `analysisCov`, `josephCov` and the projector
`diagProj` are defined in `LeanDLRA/Filtering/Defs.lean`.
-/

open Set Filter Topology
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.KalmanBucy

variable {d : ℕ}

/-- The Frobenius inner product `⟪X M, X⟫` is the sum of the quadratic forms of `M` evaluated at
the rows of `X`. -/
theorem inner_mul_right_self {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ)
    (M : Matrix n n ℝ) : ⟪X * M, X⟫ = ∑ i, X i ⬝ᵥ (M *ᵥ X i) := by
  simp only [Frobenius.inner_def, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The squared Frobenius norm is the sum of the squared Euclidean norms of the rows. -/
theorem norm_sq_eq_sum_dotProduct {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ) :
    ‖X‖ ^ 2 = ∑ i, X i ⬝ᵥ X i := by
  rw [Frobenius.norm_sq_eq_sum]
  simp [dotProduct, sq]

/-- A quadratic form does not see the antisymmetric part: `xᵀ Aᵀ x = xᵀ A x`. -/
theorem dotProduct_transpose_mulVec {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

/-- From the logarithmic-norm bound `xᵀ (A + Aᵀ) x ≤ μ |x|²` to `xᵀ Aᵀ x ≤ (μ/2) |x|²`. -/
theorem dotProduct_transpose_mulVec_le {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ : ℝ}
    (hA : ∀ x : n → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (x : n → ℝ) :
    x ⬝ᵥ (Aᵀ *ᵥ x) ≤ μ / 2 * (x ⬝ᵥ x) := by
  have h := hA x
  rw [Matrix.add_mulVec, dotProduct_add, ← dotProduct_transpose_mulVec A x] at h
  linarith

/-- **Right multiplication by `Aᵀ` is one-sided bounded by `μ/2`:** `⟪X Aᵀ, X⟫ ≤ (μ/2) ‖X‖²`
whenever `xᵀ (A + Aᵀ) x ≤ μ |x|²`.  No symmetry of `X` is needed. -/
theorem inner_mul_transpose_le {m n : Type*} [Fintype m] [Fintype n] {A : Matrix n n ℝ} {μ : ℝ}
    (hA : ∀ x : n → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (X : Matrix m n ℝ) :
    ⟪X * Aᵀ, X⟫ ≤ μ / 2 * ‖X‖ ^ 2 := by
  rw [inner_mul_right_self, norm_sq_eq_sum_dotProduct, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => dotProduct_transpose_mulVec_le hA (X i)

/-- **Left multiplication by `A` is one-sided bounded by `μ/2`:** `⟪A X, X⟫ ≤ (μ/2) ‖X‖²`. -/
theorem inner_mul_left_le {m n : Type*} [Fintype m] [Fintype n] {A : Matrix m m ℝ} {μ : ℝ}
    (hA : ∀ x : m → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (X : Matrix m n ℝ) :
    ⟪A * X, X⟫ ≤ μ / 2 * ‖X‖ ^ 2 := by
  rw [← Frobenius.inner_transpose, Matrix.transpose_mul, ← Frobenius.norm_transpose X]
  exact inner_mul_transpose_le hA Xᵀ

/-- For a PSD matrix `P`, `⟪X P, X⟫ = ∑ᵢ xᵢᵀ P xᵢ ≥ 0` (rows `xᵢ` of `X`). -/
theorem inner_mul_posSemidef_nonneg {m n : Type*} [Fintype m] [Fintype n] {P : Matrix n n ℝ}
    (hP : P.PosSemidef) (X : Matrix m n ℝ) : 0 ≤ ⟪X * P, X⟫ := by
  rw [inner_mul_right_self]
  exact Finset.sum_nonneg fun i _ => by simpa using hP.dotProduct_mulVec_nonneg (X i)

/-- For a PSD matrix `P`, `⟪P X, X⟫ = tr (Xᵀ P X) ≥ 0`. -/
theorem inner_posSemidef_mul_nonneg {m n : Type*} [Fintype m] [Fintype n] {P : Matrix m m ℝ}
    (hP : P.PosSemidef) (X : Matrix m n ℝ) : 0 ≤ ⟪P * X, X⟫ := by
  rw [← Frobenius.inner_transpose, Matrix.transpose_mul]
  exact inner_mul_posSemidef_nonneg hP.transpose Xᵀ

/-! ### The Riccati field and its one-sided Lipschitz constant (OP-SL-01) -/

/-- The difference of two Riccati fields with the same drift: with `Δ = P₁ - P₂`,
`R(P₁) - R'(P₂) = A Δ + Δ Aᵀ - ρ (P₁ Δ + Δ P₂) + (Q₁ - Q₂)`. -/
theorem riccatiField_sub (A : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ) (Q₁ Q₂ : Matrix (Fin d) (Fin d) ℝ)
    (t s : ℝ) (P₁ P₂ : Matrix (Fin d) (Fin d) ℝ) :
    riccatiField A ρ Q₁ t P₁ - riccatiField A ρ Q₂ s P₂ =
      A * (P₁ - P₂) + (P₁ - P₂) * Aᵀ - ρ • (P₁ * (P₁ - P₂) + (P₁ - P₂) * P₂) + (Q₁ - Q₂) := by
  simp only [riccatiField, Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_add]
  abel

/-- **The Riccati field is one-sided Lipschitz with constant `μ` on the PSD cone** (OP-SL-01;
arXiv 2509.11210 Sec. 4, arXiv 2607.27432 Sec. 3.6).  If `xᵀ (A + Aᵀ) x ≤ μ |x|²` and `ρ ≥ 0`,
then `⟪R(P₁) - R(P₂), P₁ - P₂⟫ ≤ μ ‖P₁ - P₂‖²` for PSD `P₁, P₂` in the Frobenius inner product,
because `⟪A Δ + Δ Aᵀ, Δ⟫ ≤ μ ‖Δ‖²` and `⟪P₁ Δ + Δ P₂, Δ⟫ ≥ 0` (the quadratic term
`P₁² - P₂² = P₁ Δ + Δ P₂`).  The noise `Qn` is arbitrary and `μ` may be negative. -/
theorem riccatiField_isOneSidedLipschitzOn {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hρ : 0 ≤ ρ) :
    IsOneSidedLipschitzOn (riccatiField A ρ Qn) {P | P.PosSemidef} μ := by
  intro t P₁ h₁ P₂ h₂
  rw [riccatiField_sub, sub_self, add_zero, inner_sub_left, inner_add_left, inner_smul_left,
    inner_add_left]
  have e1 := inner_mul_left_le hA (P₁ - P₂)
  have e2 := inner_mul_transpose_le hA (P₁ - P₂)
  have e3 := inner_posSemidef_mul_nonneg h₁ (P₁ - P₂)
  have e4 := inner_mul_posSemidef_nonneg h₂ (P₁ - P₂)
  simp only [conj_trivial]
  nlinarith [mul_nonneg hρ (add_nonneg e3 e4)]

/-! ### Uniform-in-time covariance error bounds (OP-SL-01) -/

/-- Two Riccati fields with the same drift differ only by their noise forcings. -/
theorem riccatiField_sub_same (A : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ)
    (Q₁ Q₂ : Matrix (Fin d) (Fin d) ℝ) (t s : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) :
    riccatiField A ρ Q₁ t P - riccatiField A ρ Q₂ s P = Q₁ - Q₂ := by
  simp only [riccatiField]
  abel

/-- **Uniform-in-time covariance error for a perturbed noise forcing** (OP-SL-01, general form).
Let `P` solve the Kalman–Bucy Riccati equation `P' = A P + P Aᵀ - ρ P² + Qn` and `P̃` the Riccati
equation with a time-dependent replacement forcing `Q̃ t`.  If the drift is strictly dissipative
(`xᵀ (A + Aᵀ) x ≤ μ |x|²` with `μ < 0`), `ρ ≥ 0`, both covariances stay PSD and the forcing
defect satisfies `‖Qn - Q̃ t‖ ≤ η`, then for all `t ∈ [a, b]`
`‖P̃ t - P t‖ ≤ e^{μ (t - a)} ‖P̃ a - P a‖ + η / |μ|`,
with no constant growing in `t - a`.  This is the deterministic covariance skeleton of
arXiv 2509.11210 Prop. 4.4 with the exponentially growing constants `C₁(T), C₂(T)` replaced by
time-uniform ones. -/
theorem riccati_forcing_error_uniform {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ η a b : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    {Q' : ℝ → Matrix (Fin d) (Fin d) ℝ} {P PD : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hP : ODESolution (riccatiField A ρ Qn) P a b)
    (hPD : ODESolution (fun t X => riccatiField A ρ (Q' t) t X) PD a b)
    (hpsd : ∀ t ∈ Icc a b, (P t).PosSemidef ∧ (PD t).PosSemidef) (hη0 : 0 ≤ η)
    (hη : ∀ t ∈ Ico a b, ‖Qn - Q' t‖ ≤ η) :
    ∀ t ∈ Icc a b, ‖PD t - P t‖ ≤ Real.exp (μ * (t - a)) * ‖PD a - P a‖ + η / (-μ) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSidedOn
    (riccatiField_isOneSidedLipschitzOn (Qn := Qn) hA hρ)
    (fun s hs => (hpsd s (Ico_subset_Icc_self hs)).2)
    (fun s hs => (hpsd s (Ico_subset_Icc_self hs)).1)
    hPD.cont hPD.deriv (ηy := η)
    (fun s hs => by rw [riccatiField_sub_same, norm_sub_rev]; exact hη s hs)
    hP.cont hP.deriv (ηz := 0) (fun s _ => by simp) le_rfl t ht
  rw [add_zero] at h
  calc ‖PD t - P t‖ ≤ _ := h
    _ ≤ ‖PD a - P a‖ * Real.exp (μ * (t - a)) + η / (-μ) := gronwallBound_le_of_neg hμ hη0
    _ = _ := by ring

/-- **Uniform-in-time covariance error of the DLR Kalman–Bucy filter** (OP-SL-01; DLR-KBP of
arXiv 2509.11210 Sec. 4).  If the drift is strictly dissipative (`μ < 0`) and the DLR
covariance `P_D` solves the Riccati equation with projected model noise `Πᵤ Qn Πᵤ`, then for all
`t`, `‖P_D t - P t‖ ≤ e^{μ (t-a)} ‖P_D a - P a‖ + η / |μ|` with `η` the noise projection defect
`sup ‖Qn - Πᵤ Qn Πᵤ‖` (both covariances assumed PSD; for the DLR filter this holds since
`P_D = U M Uᵀ` with `M` PSD). -/
theorem dlrKalmanBucy_covariance_error_uniform {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ η a b : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    {PU : ℝ → Matrix (Fin d) (Fin d) ℝ} {P PD : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hP : ODESolution (riccatiField A ρ Qn) P a b)
    (hPD : ODESolution (fun t X => riccatiField A ρ (PU t * Qn * PU t) t X) PD a b)
    (hpsd : ∀ t ∈ Icc a b, (P t).PosSemidef ∧ (PD t).PosSemidef) (hη0 : 0 ≤ η)
    (hη : ∀ t ∈ Ico a b, ‖Qn - PU t * Qn * PU t‖ ≤ η) :
    ∀ t ∈ Icc a b, ‖PD t - P t‖ ≤ Real.exp (μ * (t - a)) * ‖PD a - P a‖ + η / (-μ) :=
  riccati_forcing_error_uniform hA hμ hρ hP hPD hpsd hη0 hη

/-- **Uniform-in-time covariance error of the JMCO reduced Kalman–Bucy filter** (OP-SL-01,
second half; arXiv 2607.27432 Sec. 3.6, eqs. (36)–(40)).  The reduced filter is forced by the
tangent projection `Qn - Π⊥ Qn Π⊥` of the model noise (`Π⊥ = 1 - Πᵤ`), so the defect is the
normal block `‖Π⊥ Qn Π⊥‖ ≤ η` and
`‖P_J t - P t‖ ≤ e^{μ (t-a)} ‖P_J a - P a‖ + η / |μ|`. -/
theorem jmcoKalmanBucy_covariance_error_uniform {A Qn : Matrix (Fin d) (Fin d) ℝ}
    {ρ μ η a b : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    {PU : ℝ → Matrix (Fin d) (Fin d) ℝ} {P PJ : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hP : ODESolution (riccatiField A ρ Qn) P a b)
    (hPJ : ODESolution
      (fun t X => riccatiField A ρ (Qn - (1 - PU t) * Qn * (1 - PU t)) t X) PJ a b)
    (hpsd : ∀ t ∈ Icc a b, (P t).PosSemidef ∧ (PJ t).PosSemidef) (hη0 : 0 ≤ η)
    (hη : ∀ t ∈ Ico a b, ‖(1 - PU t) * Qn * (1 - PU t)‖ ≤ η) :
    ∀ t ∈ Icc a b, ‖PJ t - P t‖ ≤ Real.exp (μ * (t - a)) * ‖PJ a - P a‖ + η / (-μ) :=
  riccati_forcing_error_uniform hA hμ hρ hP hPJ hpsd hη0 fun t ht => by
    rw [sub_sub_cancel]; exact hη t ht

/-! ### Noise-blind DO bases (OP-SL-02) -/

/-- (OP-SL-02 (i), algebraic core.)  For an idempotent `Π`, `Π Σ Π = Σ` forces `Π Σ = Σ`.
Contrapositive: if the noise is not contained in the mode space (`Π Σ ≠ Σ`), the projected
forcing `Π Σ Π` differs from `Σ`. -/
theorem mul_eq_of_mul_mul_eq {Pi Q : Matrix (Fin d) (Fin d) ℝ} (hPi : Pi * Pi = Pi)
    (h : Pi * Q * Pi = Q) : Pi * Q = Q := by
  calc Pi * Q = Pi * (Pi * Q * Pi) := by rw [h]
    _ = Pi * Pi * Q * Pi := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hPi, h]

/-- If a curve vanishes at `a` and has a nonzero right derivative there, it is nonzero at all
times slightly after `a`. -/
theorem eventually_ne_zero_of_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {v : E} {a : ℝ} (hf : HasDerivWithinAt f v (Ici a) a)
    (h0 : f a = 0) (hv : v ≠ 0) : ∀ᶠ t in 𝓝[>] a, f t ≠ 0 := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Ioi a)).1 hf.Ioi_of_Ici
  filter_upwards [hs.eventually_ne hv] with t ht hft
  exact ht (by simp [slope_def_module, hft, h0])

/-- **DLR-KBP differs from KBP whenever the noise leaves the mode space** (OP-SL-02 (i);
arXiv 2509.11210 Sec. 4 after (4.4), Sec. 6.1).  Let `P` solve the Kalman–Bucy Riccati equation
and `P_D` the DLR-KBP equation with projected noise `Π(t) Qn Π(t)`, both starting from the same
`P₀` at `a < b`.  If `Π(a)` is idempotent and `Π(a) Qn ≠ Qn`, then `P_D t ≠ P t` for all `t > a`
close enough to `a`: the two covariances separate immediately.  (The right derivatives at `a`
differ by `Π Qn Π - Qn ≠ 0`.) -/
theorem dlrKalmanBucy_ne_of_noise_not_in_range {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ a b : ℝ}
    (hab : a < b) {PU : ℝ → Matrix (Fin d) (Fin d) ℝ} {P PD : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hP : ODESolution (riccatiField A ρ Qn) P a b)
    (hPD : ODESolution (fun t X => riccatiField A ρ (PU t * Qn * PU t) t X) PD a b)
    (h0 : PD a = P a) (hPi : PU a * PU a = PU a) (hQ : PU a * Qn ≠ Qn) :
    ∀ᶠ t in 𝓝[>] a, PD t ≠ P t := by
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have hd := (hPD.deriv a ha).sub (hP.deriv a ha)
  have hv : riccatiField A ρ (PU a * Qn * PU a) a (PD a) - riccatiField A ρ Qn a (P a) ≠ 0 := by
    rw [h0, riccatiField_sub_same, sub_ne_zero]
    exact fun h => hQ (mul_eq_of_mul_mul_eq hPi h)
  filter_upwards [eventually_ne_zero_of_hasDerivWithinAt hd (by simp [h0]) hv] with t ht
  exact fun h => ht (by simp [h])

/-- **The JMCO defect never exceeds the DO defect — exact Pythagorean identity** (OP-SL-02 (ii);
arXiv 2607.27432 Secs. 6.2, 6.4).  For `Π = U Uᵀ` with orthonormal columns (`Uᵀ U = 1`),
`‖Q - Π Q Π‖² = ‖(1 - Π) Q (1 - Π)‖² + ‖Π Q (1 - Π) + (1 - Π) Q Π‖²`.
Hence the JMCO forcing defect `‖Π⊥ Q Π⊥‖` is at most the DO defect `‖Q - Π Q Π‖`, with equality
iff the off-diagonal blocks `Π Q Π⊥ + Π⊥ Q Π` vanish. -/
theorem norm_sq_noiseDefect_eq {k : Type*} [Fintype k] [DecidableEq k]
    {U : Matrix (Fin d) k ℝ} (hU : Uᵀ * U = 1) (Q : Matrix (Fin d) (Fin d) ℝ) :
    ‖Q - U * Uᵀ * Q * (U * Uᵀ)‖ ^ 2 =
      ‖(1 - U * Uᵀ) * Q * (1 - U * Uᵀ)‖ ^ 2 +
        ‖U * Uᵀ * Q * (1 - U * Uᵀ) + (1 - U * Uᵀ) * Q * (U * Uᵀ)‖ ^ 2 := by
  have hU' : ∀ X : Matrix k (Fin d) ℝ, Uᵀ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  set Z := Q - U * Uᵀ * Q * (U * Uᵀ)
  have h := norm_sq_tangentProj_add_normal hU hU Z
  have hN : (1 - U * Uᵀ) * Z * (1 - U * Uᵀ) = (1 - U * Uᵀ) * Q * (1 - U * Uᵀ) := by
    simp only [Z, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, hU']
    abel
  have hT : tangentProj U U Z =
      U * Uᵀ * Q * (1 - U * Uᵀ) + (1 - U * Uᵀ) * Q * (U * Uᵀ) := by
    rw [tangentProj_apply]
    simp only [Z, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, hU']
    abel
  rw [hN, hT] at h
  linarith

/-- The JMCO noise defect is bounded by the DO noise defect (OP-SL-02 (ii)). -/
theorem norm_normalNoise_le_noiseDefect {k : Type*} [Fintype k] [DecidableEq k]
    {U : Matrix (Fin d) k ℝ} (hU : Uᵀ * U = 1) (Q : Matrix (Fin d) (Fin d) ℝ) :
    ‖(1 - U * Uᵀ) * Q * (1 - U * Uᵀ)‖ ≤ ‖Q - U * Uᵀ * Q * (U * Uᵀ)‖ := by
  have h := norm_sq_noiseDefect_eq hU Q
  nlinarith [norm_nonneg ((1 - U * Uᵀ) * Q * (1 - U * Uᵀ)),
    norm_nonneg (Q - U * Uᵀ * Q * (U * Uᵀ)),
    sq_nonneg ‖U * Uᵀ * Q * (1 - U * Uᵀ) + (1 - U * Uᵀ) * Q * (U * Uᵀ)‖]
/-! ### Perpetual rotation of the DO basis for skew drift (OP-SL-13) -/

/-- For a skew-symmetric `A` and a single column `u`, `uᵀ A u = 0` (as a `1 × 1` matrix). -/
theorem transpose_mul_mul_eq_zero_of_skew {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = -A)
    (u : Matrix (Fin d) (Fin 1) ℝ) : uᵀ * A * u = 0 := by
  have h1 : (uᵀ * A * u)ᵀ = -(uᵀ * A * u) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA]
    simp [Matrix.mul_assoc]
  have h2 : (uᵀ * A * u)ᵀ = uᵀ * A * u := by
    ext i j
    rw [Subsingleton.elim i j, Matrix.transpose_apply]
  rw [h2] at h1
  have : (2 : ℝ) • (uᵀ * A * u) = 0 := by rw [two_smul]; nth_rw 1 [h1]; abel
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

/-- **Exact solution of the DO mode equation for skew drift** (OP-SL-13; arXiv 2606.15843
Example 5.9, arXiv 2509.11210 Sec. 4.1.2).  If `Aᵀ = -A` and `A² = -1` (skew and orthogonal),
then the rank-one basis `U(t) = cos t • u₀ + sin t • (A u₀)` solves the deterministic-mode
equation `U' = (1 - U Uᵀ) A U` for every `t` and every initial column `u₀`.  The correction
term `U Uᵀ A U` vanishes identically because `Uᵀ A U = 0` for a single column and skew `A`. -/
theorem hasDerivAt_rotatingMode {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = -A) (hA2 : A * A = -1)
    (u₀ : Matrix (Fin d) (Fin 1) ℝ) (t : ℝ) :
    HasDerivAt (rotatingMode A u₀)
      ((1 - rotatingMode A u₀ t * (rotatingMode A u₀ t)ᵀ) * A * rotatingMode A u₀ t) t := by
  have hd : HasDerivAt (rotatingMode A u₀) (-Real.sin t • u₀ + Real.cos t • (A * u₀)) t :=
    ((Real.hasDerivAt_cos t).smul_const u₀).add ((Real.hasDerivAt_sin t).smul_const (A * u₀))
  convert hd using 1
  have h0 := transpose_mul_mul_eq_zero_of_skew hA (rotatingMode A u₀ t)
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ _ A,
    Matrix.mul_assoc _ (_ * A), h0, Matrix.mul_zero, sub_zero]
  simp only [rotatingMode, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hA2,
    Matrix.neg_mul, Matrix.one_mul, smul_neg, neg_smul]
  abel

/-- The 2 × 2 rotation generator `J = [[0, -1], [1, 0]]`. -/
def rotGen : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The first unit column `e₁ ∈ ℝ^{2×1}`. -/
def unitCol : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

theorem rotGen_transpose : rotGenᵀ = -rotGen := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotGen]

theorem rotGen_mul_self : rotGen * rotGen = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotGen, Matrix.mul_apply, Fin.sum_univ_two]

/-- The projector onto the DO subspace in the 2D example has `(0,0)` entry `cos² t`. -/
theorem rotatingMode_proj_apply_zero (t : ℝ) :
    (rotatingMode rotGen unitCol t * (rotatingMode rotGen unitCol t)ᵀ) 0 0 = Real.cos t ^ 2 := by
  simp [rotatingMode, rotGen, unitCol, Matrix.mul_apply, sq]

/-- **The DO subspace never converges** (OP-SL-13, negative result).  For the skew drift
`A = J` (2D rotation generator) and `U₀ = e₁`, the exact DO basis
`U(t) = (cos t, sin t)ᵀ` (`hasDerivAt_rotatingMode`) spans a line whose orthogonal projector
`Π(t) = U(t) U(t)ᵀ` has no limit as `t → ∞`: its `(0,0)` entry is `cos² t`.  This is the
deterministic-basis core of the paper's remark that the basis marginal of a DO invariant measure
need not be a Dirac mass; the invariant-measure statement itself is not formalised here. -/
theorem not_tendsto_rotatingMode_proj :
    ¬ ∃ L : Matrix (Fin 2) (Fin 2) ℝ, Tendsto
      (fun t => rotatingMode rotGen unitCol t * (rotatingMode rotGen unitCol t)ᵀ) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have he : Tendsto (fun t => Real.cos t ^ 2) atTop (𝓝 (L 0 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hL ⊢
    refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hL
    rw [← rotatingMode_proj_apply_zero, Real.norm_eq_abs]
    exact Frobenius.abs_apply_le_norm (_ - L) 0 0
  have hseq : Tendsto (fun n : ℕ => (n : ℝ) * Real.pi) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const Real.pi_pos
  have h1 : Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * Real.pi) ^ 2) atTop (𝓝 (L 0 0)) :=
    he.comp hseq
  have h2 : Tendsto (fun n : ℕ => Real.cos ((n : ℝ) * Real.pi + Real.pi / 2) ^ 2) atTop
      (𝓝 (L 0 0)) :=
    he.comp (tendsto_atTop_add_const_right _ _ hseq)
  have e1 : (fun n : ℕ => Real.cos ((n : ℝ) * Real.pi) ^ 2) = fun _ => 1 := by
    funext n; rw [Real.cos_nat_mul_pi, ← pow_mul, mul_comm, pow_mul]; simp
  have e2 : (fun n : ℕ => Real.cos ((n : ℝ) * Real.pi + Real.pi / 2) ^ 2) = fun _ => 0 := by
    funext n; rw [Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]; simp
  rw [e1] at h1
  rw [e2] at h2
  exact one_ne_zero
    ((tendsto_nhds_unique tendsto_const_nhds h1).trans
      (tendsto_nhds_unique tendsto_const_nhds h2).symm)

/-- The DO subspace in the 2D example is periodic with period `π` and non-constant. -/
theorem rotatingMode_proj_periodic_nonconst (t : ℝ) :
    rotatingMode rotGen unitCol (t + Real.pi) * (rotatingMode rotGen unitCol (t + Real.pi))ᵀ =
        rotatingMode rotGen unitCol t * (rotatingMode rotGen unitCol t)ᵀ ∧
      rotatingMode rotGen unitCol 0 * (rotatingMode rotGen unitCol 0)ᵀ ≠
        rotatingMode rotGen unitCol (Real.pi / 2) *
          (rotatingMode rotGen unitCol (Real.pi / 2))ᵀ := by
  refine ⟨?_, fun h => ?_⟩
  · have : rotatingMode rotGen unitCol (t + Real.pi) = -rotatingMode rotGen unitCol t := by
      simp [rotatingMode, Real.cos_add_pi, Real.sin_add_pi, neg_smul]; abel
    rw [this, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  · have := congrFun (congrFun h 0) 0
    rw [rotatingMode_proj_apply_zero, rotatingMode_proj_apply_zero] at this
    simp at this

/-! ### Loewner monotonicity of the Kalman analysis covariance (OP-SL-20 (i)) -/

section Analysis

variable {p : ℕ}

/-- **Joseph-form identity** (OP-SL-20 (i)): for symmetric `Π`, `R` and invertible `S = S(Π)`,
`J(Π, K) - Σ(Π) = (K - K(Π)) S (K - K(Π))ᵀ` for every gain `K`. -/
theorem josephCov_sub_analysisCov {C : Matrix (Fin p) (Fin d) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    {Pi : Matrix (Fin d) (Fin d) ℝ} (hPi : Piᵀ = Pi) (hR : Rᵀ = R)
    (hS : IsUnit (innovCov C R Pi).det) (K : Matrix (Fin d) (Fin p) ℝ) :
    josephCov C R Pi K - analysisCov C R Pi =
      (K - kalmanGain C R Pi) * innovCov C R Pi * (K - kalmanGain C R Pi)ᵀ := by
  set S := innovCov C R Pi with hSdef
  have hST : Sᵀ = S := by
    simp [hSdef, innovCov, Matrix.transpose_mul, hPi, hR, Matrix.mul_assoc]
  have hSiT : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hST]
  have h1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS
  have hGT : (kalmanGain C R Pi)ᵀ = S⁻¹ * C * Pi := by
    simp [kalmanGain, ← hSdef, Matrix.transpose_mul, hPi, hSiT, Matrix.mul_assoc]
  have hGS : kalmanGain C R Pi * S = Pi * Cᵀ := by
    rw [kalmanGain, ← hSdef, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hSGT : S * (kalmanGain C R Pi)ᵀ = C * Pi := by
    rw [hGT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hS,
      Matrix.one_mul]
  have hexp : (K - kalmanGain C R Pi) * S * (K - kalmanGain C R Pi)ᵀ =
      K * S * Kᵀ - K * (S * (kalmanGain C R Pi)ᵀ) - (kalmanGain C R Pi * S) * Kᵀ +
        (kalmanGain C R Pi * S) * (kalmanGain C R Pi)ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [hexp, hSGT, hGS, hGT, josephCov, analysisCov, ← hSdef]
  generalize S⁻¹ = Si
  rw [hSdef, innovCov]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  abel

/-- **Loewner monotonicity of the Joseph form in the prior** (OP-SL-20 (i)):
`J(Π, K) - J(Π', K) = (1 - K C)(Π - Π')(1 - K C)ᵀ`, which is PSD when `Π - Π'` is. -/
theorem josephCov_sub_posSemidef {C : Matrix (Fin p) (Fin d) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    {Pi Pi' : Matrix (Fin d) (Fin d) ℝ} (h : (Pi - Pi').PosSemidef)
    (K : Matrix (Fin d) (Fin p) ℝ) : (josephCov C R Pi K - josephCov C R Pi' K).PosSemidef := by
  have e : josephCov C R Pi K - josephCov C R Pi' K =
      (1 - K * C) * (Pi - Pi') * (1 - K * C)ᴴ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [josephCov, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e]
  exact h.mul_mul_conjTranspose_same _

/-- The innovation covariance of a PSD prior with PD observation noise is positive definite. -/
theorem innovCov_posDef {C : Matrix (Fin p) (Fin d) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    {Pi : Matrix (Fin d) (Fin d) ℝ} (hPi : Pi.PosSemidef) (hR : R.PosDef) :
    (innovCov C R Pi).PosDef := by
  have h := hPi.mul_mul_conjTranspose_same C
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact Matrix.PosDef.posSemidef_add h hR

/-- **Overconfidence of truncated Kalman analyses: one-step Loewner monotonicity**
(OP-SL-20 (i); arXiv 2306.07774 Sec. 5, arXiv 2602.06614 Sec. 3.1.2).  If the (e.g. truncated)
prior `Πᵣ` is PSD and Loewner-below the full prior `Π` (`Π - Πᵣ ⪰ 0`) and the observation noise
`R` is positive definite, then the analysis covariances are Loewner-ordered:
`Σ(Πᵣ) ⪯ Σ(Π)`.  Indeed
`Σ(Π) - Σ(Πᵣ) = (1 - K C)(Π - Πᵣ)(1 - K C)ᵀ + (K - Kᵣ) S(Πᵣ) (K - Kᵣ)ᵀ` with `K = K(Π)`,
`Kᵣ = K(Πᵣ)`.  A low-rank filter that underestimates the prior therefore underestimates the
posterior: it is overconfident after every analysis step. -/
theorem analysisCov_mono {C : Matrix (Fin p) (Fin d) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    {Pi Pir : Matrix (Fin d) (Fin d) ℝ} (hr : Pir.PosSemidef) (h : (Pi - Pir).PosSemidef)
    (hR : R.PosDef) : (analysisCov C R Pi - analysisCov C R Pir).PosSemidef := by
  have hPi : Pi.PosSemidef := by simpa using h.add hr
  have hRT : Rᵀ = R := hR.isHermitian.eq
  have hPiT : Piᵀ = Pi := hPi.isHermitian.eq
  have hPirT : Pirᵀ = Pir := hr.isHermitian.eq
  have hS := innovCov_posDef (C := C) hPi hR
  have hSr := innovCov_posDef (C := C) hr hR
  have hSu : IsUnit (innovCov C R Pi).det := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  have hSru : IsUnit (innovCov C R Pir).det := (Matrix.isUnit_iff_isUnit_det _).1 hSr.isUnit
  set K := kalmanGain C R Pi
  have e1 := josephCov_sub_analysisCov hPiT hRT hSu K
  have e2 := josephCov_sub_analysisCov hPirT hRT hSru K
  rw [sub_self, Matrix.zero_mul, Matrix.zero_mul] at e1
  have e : analysisCov C R Pi - analysisCov C R Pir =
      (josephCov C R Pi K - josephCov C R Pir K) +
        (K - kalmanGain C R Pir) * innovCov C R Pir * (K - kalmanGain C R Pir)ᵀ := by
    rw [← e2]
    have : analysisCov C R Pi = josephCov C R Pi K := (sub_eq_zero.1 e1).symm
    rw [this]
    abel
  rw [e]
  refine (josephCov_sub_posSemidef h K).add ?_
  have := hSr.posSemidef.mul_mul_conjTranspose_same (K - kalmanGain C R Pir)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

end Analysis

/-! ### Stationary covariances: uniqueness and exponential attraction (OP-SL-32, partial) -/

/-- **Uniqueness of the PSD stationary covariance** (OP-SL-32, dissipative case).  For
`μ < 0` and `ρ ≥ 0`, the algebraic Riccati equation `R(P) = 0` has at most one PSD solution. -/
theorem riccati_stationary_unique {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    {P₁ P₂ : Matrix (Fin d) (Fin d) ℝ} (h₁ : P₁.PosSemidef) (h₂ : P₂.PosSemidef)
    (e₁ : riccatiField A ρ Qn 0 P₁ = 0) (e₂ : riccatiField A ρ Qn 0 P₂ = 0) : P₁ = P₂ := by
  have h := riccatiField_isOneSidedLipschitzOn (Qn := Qn) hA hρ 0 P₁ h₁ P₂ h₂
  rw [e₁, e₂, sub_self, inner_zero_left] at h
  have h0 : ‖P₁ - P₂‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖P₁ - P₂‖]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
    (le_antisymm h0 (sq_nonneg _))))

/-- **Exponential attraction to a PSD stationary covariance** (OP-SL-32, dissipative case;
attraction half of `riccati_equilibrium_attracts`).  If `P∞ ⪰ 0` solves the
algebraic Riccati equation, every PSD solution of the Riccati ODE satisfies
`‖P t - P∞‖ ≤ e^{μ (t-a)} ‖P a - P∞‖`, independently of the initial covariance.  Existence of
`P∞` is not proved here. -/
theorem riccati_attracts_stationary {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ a b : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hρ : 0 ≤ ρ)
    {Pinf : Matrix (Fin d) (Fin d) ℝ} (hinf : Pinf.PosSemidef)
    (einf : riccatiField A ρ Qn 0 Pinf = 0) {P : ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hP : ODESolution (riccatiField A ρ Qn) P a b) (hpsd : ∀ t ∈ Icc a b, (P t).PosSemidef) :
    ∀ t ∈ Icc a b, ‖P t - Pinf‖ ≤ Real.exp (μ * (t - a)) * ‖P a - Pinf‖ := by
  have hc : ODESolution (riccatiField A ρ Qn) (fun _ => Pinf) a b := by
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    have : riccatiField A ρ Qn t Pinf = 0 := einf
    rw [this]
    exact hasDerivWithinAt_const _ _ _
  exact hP.norm_sub_le_exp_of_oneSidedOn hc (riccatiField_isOneSidedLipschitzOn hA hρ)
    (fun t ht => hpsd t (Ico_subset_Icc_self ht)) (fun _ _ => hinf)

/-! ### The DLR analysis is the Kalman analysis on `span U` (arXiv 2602.06614, eqs. (18)–(21)) -/

section LowRankAnalysis

variable {p r : ℕ}

/-- The innovation covariance of a low-rank prior `U M Uᵀ` is that of the reduced problem. -/
theorem innovCov_lowRank (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) (M : Matrix (Fin r) (Fin r) ℝ) :
    innovCov C R (U * M * Uᵀ) = innovCov (C * U) R M := by
  simp [innovCov, Matrix.transpose_mul, Matrix.mul_assoc]

/-- **Low-rank Kalman gain** (arXiv 2602.06614, eqs. (18)–(21)): for a low-rank prior
`Π = U M Uᵀ`, `K(U M Uᵀ) = U K_r(M)` with `K_r` the Kalman gain of the reduced problem with
observation operator `C U`.  In particular the update `K (z - C x)` lies in `span U`: only the
directions of the current basis are corrected. -/
theorem kalmanGain_lowRank (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) (M : Matrix (Fin r) (Fin r) ℝ) :
    kalmanGain C R (U * M * Uᵀ) = U * kalmanGain (C * U) R M := by
  rw [kalmanGain, kalmanGain, innovCov_lowRank]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- **The DLR analysis covariance is the EnKF/Kalman analysis on `span U`**
(arXiv 2602.06614, eqs. (18)–(21)): `Σ(U M Uᵀ) = U Σ_r(M) Uᵀ`, where `Σ_r` is the analysis
covariance of the reduced problem with observation operator `C U`.  No orthonormality of `U`
is needed. -/
theorem analysisCov_lowRank (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) (M : Matrix (Fin r) (Fin r) ℝ) :
    analysisCov C R (U * M * Uᵀ) = U * analysisCov (C * U) R M * Uᵀ := by
  rw [analysisCov, analysisCov, innovCov_lowRank]
  simp only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- **Only in-range corrections** (arXiv 2602.06614, Sec. 3.1.2): with orthonormal `U`, the
low-rank Kalman gain has no component orthogonal to `span U`: `(1 - U Uᵀ) K(U M Uᵀ) = 0`.
Hence uncertainty and corrections outside the retained subspace are never assimilated. -/
theorem one_sub_proj_mul_kalmanGain_lowRank (C : Matrix (Fin p) (Fin d) ℝ)
    (R : Matrix (Fin p) (Fin p) ℝ) {U : Matrix (Fin d) (Fin r) ℝ} (hU : Uᵀ * U = 1)
    (M : Matrix (Fin r) (Fin r) ℝ) : (1 - U * Uᵀ) * kalmanGain C R (U * M * Uᵀ) = 0 := by
  rw [kalmanGain_lowRank, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, sub_self]

end LowRankAnalysis

/-! ### Non-degenerate satisfiability of the hypotheses -/

/-- The dissipativity hypothesis is satisfiable with a negative rate: `A = -c • 1` (`c > 0`)
gives `xᵀ (A + Aᵀ) x = -2c |x|²`. -/
theorem dissipative_neg_smul_one (c : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (((-c • 1 : Matrix (Fin d) (Fin d) ℝ) + (-c • 1 : Matrix (Fin d) (Fin d) ℝ)ᵀ) *ᵥ x) ≤
      -(2 * c) * (x ⬝ᵥ x) := by
  rw [Matrix.transpose_smul, Matrix.transpose_one, ← two_smul ℝ (-c • (1 : Matrix _ _ ℝ)),
    smul_smul, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  linarith

/-- The noise-separation hypothesis of `dlrKalmanBucy_ne_of_noise_not_in_range` is satisfiable:
the coordinate projector `Π = diag(1, 0)` is idempotent and `Π · 1 ≠ 1`. -/
example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, 0] = !![1, 0; 0, 0] ∧
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * 1 ≠ 1 := by
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply], fun h => ?_⟩
  have := congrFun (congrFun h 1) 1
  simp at this

/-- The hypotheses of `analysisCov_mono` are satisfiable non-trivially: `Πᵣ = 0 ⪯ Π = 1`
with `R = 1`; the conclusion then says `Σ(0) = 0 ⪯ Σ(1)`. -/
example (C : Matrix (Fin 2) (Fin 1) ℝ) :
    (analysisCov C 1 1 - analysisCov C 1 0).PosSemidef :=
  analysisCov_mono Matrix.PosSemidef.zero (by simpa using Matrix.PosSemidef.one)
    Matrix.PosDef.one

/-- A constant curve solves an ODE whose field vanishes at that point. -/
theorem odeSolution_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {c : E} {a b : ℝ} (h : ∀ t, f t c = 0) :
    ODESolution f (fun _ => c) a b :=
  ⟨continuousOn_const, fun t _ => by rw [h t]; exact hasDerivWithinAt_const _ _ _⟩

theorem diagProj_posSemidef : diagProj.PosSemidef := by
  unfold diagProj
  rw [Matrix.posSemidef_diagonal_iff]
  intro i; fin_cases i <;> simp

/-- With `A = -1`, `ρ = 1`, `Qn = 3 • 1`, the identity is a stationary KBP covariance. -/
theorem riccati_one_eq_zero :
    riccatiField ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 ((3 : ℝ) • 1) 0 1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [riccatiField] <;> norm_num

/-- With the same data and DO projector `Π = diag(1, 0)`, `Π` itself is a stationary DLR-KBP
covariance (forcing `Π Qn Π`). -/
theorem riccati_diagProj_eq_zero :
    riccatiField ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1
      (diagProj * ((3 : ℝ) • 1) * diagProj) 0 diagProj = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [riccatiField, diagProj]; norm_num

/-- **Non-vacuity of `dlrKalmanBucy_covariance_error_uniform`.**  All hypotheses hold for a
genuine pair of KBP / DLR-KBP solutions: `A = -1` (`μ = -2`), `ρ = 1`, `Qn = 3 • 1`, mode
projector `Π = diag(1, 0)`, `P ≡ 1`, `P_D ≡ Π` (both PSD, both exact solutions), with a nonzero
noise defect (next example), so the noise is genuinely not in the mode space. -/
example (a b : ℝ) : ∀ t ∈ Icc a b, ‖diagProj - 1‖ ≤
    Real.exp (-(2 * 1) * (t - a)) * ‖diagProj - 1‖ +
      ‖(3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diagProj * ((3 : ℝ) • 1) * diagProj‖ /
        (-(-(2 * 1))) :=
  dlrKalmanBucy_covariance_error_uniform (PU := fun _ => diagProj)
    (P := fun _ => 1) (PD := fun _ => diagProj)
    (dissipative_neg_smul_one 1) (by norm_num) zero_le_one
    (odeSolution_const fun _ => riccati_one_eq_zero)
    (odeSolution_const fun _ => riccati_diagProj_eq_zero)
    (fun _ _ => ⟨Matrix.PosSemidef.one, diagProj_posSemidef⟩) (norm_nonneg _) (fun _ _ => le_rfl)

/-- The noise defect in the previous example is nonzero. -/
example : (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - diagProj * ((3 : ℝ) • 1) * diagProj ≠ 0 := by
  intro h
  have := congrFun (congrFun h 1) 1
  simp [diagProj] at this

/-- The rotating DO mode of the 2D example has unit norm columns at every time:
`U(t)ᵀ U(t) = 1`, so it is a genuine orthonormal DO basis. -/
theorem rotatingMode_orthonormal (t : ℝ) :
    (rotatingMode rotGen unitCol t)ᵀ * rotatingMode rotGen unitCol t = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [rotatingMode, rotGen, unitCol, Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith [Real.sin_sq_add_cos_sq t]

end LeanDLRA.KalmanBucy
