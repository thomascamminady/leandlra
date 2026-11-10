import LeanDLRA.LinearAlgebra.Frobenius.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Filtering: definitions

The vocabulary of the filtering layer: the Kalman–Bucy covariance (differential Riccati) field,
the matrices of one Kalman analysis step, and the deterministic ensemble Kalman–Bucy field. The
theorems are in `Stochastic/KalmanBucy.lean` (one-sided Riccati stability, uniform-in-time
covariance bounds, Loewner monotonicity of the analysis covariance) and in
`OpenProblems/Stiff/Part3*.lean` (ensemble Kalman–Bucy).

## Main definitions

* `KalmanBucy.riccatiField A ρ Qn`: the field `P ↦ A P + P Aᵀ - ρ P² + Qn` of the Kalman–Bucy
  covariance equation with full observation `S = ρ I`.
* `KalmanBucy.innovCov`, `KalmanBucy.kalmanGain`, `KalmanBucy.analysisCov`,
  `KalmanBucy.josephCov`: innovation covariance `C Π Cᵀ + R`, gain `Π Cᵀ S⁻¹`, analysis covariance
  `Π - Π Cᵀ S⁻¹ C Π` and its Joseph form for an arbitrary gain.
* `KalmanBucy.rotatingMode`, `KalmanBucy.diagProj`: the rotating rank-one basis
  `cos t • u₀ + sin t • (A u₀)` and the projector `diag(1, 0)` of the worked examples.
* `OpenProblems.Stiff.ensCentering M`, `OpenProblems.Stiff.enkfField`: the ensemble centring matrix
  `I - (1/M) 𝟙𝟙ᵀ` and the deterministic ensemble Kalman–Bucy field.

* `LeanDLRA.riccatiField`: the same field in the root namespace (from
  `OpenProblems/Curated/StiffAndStochasticDefs.lean`), with the same body as
  `KalmanBucy.riccatiField`; the two are not merged yet (Phase C, batch C13).

The names and namespaces are those of the files the definitions come from (Phase B of
`wip/UNIFY.md`: moves only). Inside `namespace LeanDLRA.KalmanBucy` the bare name
`riccatiField` still means `KalmanBucy.riccatiField` (the innermost namespace wins).
-/

open Set Filter Topology
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.KalmanBucy

open scoped LeanDLRA.Frobenius

variable {d : ℕ}

/-! ### The Riccati field and examples -/

/-- The Kalman–Bucy (differential Riccati) covariance field with full observation `S = ρ I`:
`R(P) = A P + P Aᵀ - ρ P² + Qn` (model-noise covariance `Qn`).  Used by the statements above. -/
def riccatiField (A : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ) (Qn : Matrix (Fin d) (Fin d) ℝ) :
    ℝ → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ :=
  fun _ P => A * P + P * Aᵀ - ρ • (P * P) + Qn

/-- The rotating rank-one DO basis `U(t) = cos t • u₀ + sin t • (A u₀)`. -/
noncomputable def rotatingMode (A : Matrix (Fin d) (Fin d) ℝ) (u₀ : Matrix (Fin d) (Fin 1) ℝ)
    (t : ℝ) : Matrix (Fin d) (Fin 1) ℝ :=
  Real.cos t • u₀ + Real.sin t • (A * u₀)

/-- The rank-one coordinate projector `diag(1, 0)` on `ℝ²`. -/
noncomputable def diagProj : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]

/-! ### One Kalman analysis step -/

section Analysis

variable {p : ℕ}

/-- Innovation covariance `S(Π) = C Π Cᵀ + R`. -/
def innovCov (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (Pi : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  C * Pi * Cᵀ + R

/-- Kalman gain `K(Π) = Π Cᵀ S(Π)⁻¹`. -/
noncomputable def kalmanGain (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (Pi : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin p) ℝ :=
  Pi * Cᵀ * (innovCov C R Pi)⁻¹

/-- Kalman analysis (posterior) covariance `Σ(Π) = Π - Π Cᵀ S(Π)⁻¹ C Π`. -/
noncomputable def analysisCov (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (Pi : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Pi - Pi * Cᵀ * (innovCov C R Pi)⁻¹ * C * Pi

/-- Joseph form of the analysis covariance for an arbitrary gain `K`:
`J(Π, K) = (1 - K C) Π (1 - K C)ᵀ + K R Kᵀ`. -/
def josephCov (C : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin p) (Fin p) ℝ)
    (Pi : Matrix (Fin d) (Fin d) ℝ) (K : Matrix (Fin d) (Fin p) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - K * C) * Pi * (1 - K * C)ᵀ + K * R * Kᵀ

end Analysis

end LeanDLRA.KalmanBucy

/-! ### The Riccati field in the root namespace -/

namespace LeanDLRA

section Riccati

open scoped LeanDLRA.Frobenius

variable {d : ℕ}

/-- The Kalman–Bucy (differential Riccati) covariance field with full observation `S = ρ I`:
`R(P) = A P + P Aᵀ - ρ P² + Qn` (model-noise covariance `Qn`). -/
def riccatiField (A : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ) (Qn : Matrix (Fin d) (Fin d) ℝ) :
    ℝ → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ :=
  fun _ P => A * P + P * Aᵀ - ρ • (P * P) + Qn

end Riccati

end LeanDLRA

/-! ### Ensemble Kalman–Bucy -/

namespace LeanDLRA.OpenProblems.Stiff

open LeanDLRA

section EnKF

/-- The ensemble centring matrix `Π = I - (1/M) 𝟙𝟙ᵀ` (local definition for OP-ST-31). -/
noncomputable def ensCentering (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  1 - (M : ℝ)⁻¹ • Matrix.of fun _ _ => 1

/-- Deterministic ensemble Kalman–Bucy field on ensembles `X ∈ ℝ^{d × M}`:
`F(X) = A X - (M-1)⁻¹ X Π Xᵀ Hᵀ R⁻¹ (H X - Y_obs)` (local definition for OP-ST-31; no inverse
Gram matrix appears). -/
noncomputable def enkfField {d p M : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (H : Matrix (Fin p) (Fin d) ℝ) (Rinv : Matrix (Fin p) (Fin p) ℝ)
    (Yobs : Matrix (Fin p) (Fin M) ℝ) : ℝ → Matrix (Fin d) (Fin M) ℝ → Matrix (Fin d) (Fin M) ℝ :=
  fun _ X => A * X - ((M : ℝ) - 1)⁻¹ • (X * ensCentering M * Xᵀ * Hᵀ * Rinv * (H * X - Yobs))

end EnKF

end LeanDLRA.OpenProblems.Stiff
