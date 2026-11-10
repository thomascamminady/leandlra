import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Frobenius

/-!
# Definitions for Stiff Part3

Local definitions used by the theorems of the corresponding modules.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Stiff

open LeanDLRA

/-- The 1D Dirichlet finite-difference Laplacian `(1, -2, 1)/h²` on `N` interior nodes (local
definition for OP-ST-23). -/
noncomputable def lap1D (N : ℕ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if i = j then -2 / h ^ 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 / h ^ 2 else 0

section DRB

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end DRB

/-- The cyclic shift `S e_i = e_{i-1}` on `Fin n` (`S_{ij} = 1` iff `j = i + 1`; local definition
for OP-ST-26). -/
def cycShift (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j = i + 1 then 1 else 0

section Newton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The residual `G(Z) = Z - Yⁿ - τ F(Z)` of the implicit stage (local definition for
OP-ST-27). -/
def stageResidual (F : E → E) (Yn : E) (τ : ℝ) (Z : E) : E := Z - Yn - τ • F Z

end Newton

section Rank

open scoped LeanDLRA.Frobenius

end Rank

/-- Normalised Hermite functions `φₙ(v) = Heₙ(v) e^{-v²/4} / √(n! √(2π))`, an orthonormal basis
of `L²(ℝ)` (local definition for OP-ST-29; `Heₙ = Polynomial.hermite n`). -/
noncomputable def hermiteFn (n : ℕ) (v : ℝ) : ℝ :=
  (Real.sqrt (n.factorial * Real.sqrt (2 * Real.pi)))⁻¹ *
    Polynomial.aeval v (Polynomial.hermite n) * Real.exp (-(v ^ 2) / 4)

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

open scoped LeanDLRA.Frobenius

end EnKF

/-- `φ₁(z) = (eᶻ - 1)/z`, `φ₁(0) = 1` (local definition for OP-ST-32). -/
noncomputable def phi1 (z : ℝ) : ℝ := if z = 0 then 1 else (Real.exp z - 1) / z

/-- `φ₂(z) = (eᶻ - 1 - z)/z²`, `φ₂(0) = 1/2` (local definition for OP-ST-32). -/
noncomputable def phi2 (z : ℝ) : ℝ := if z = 0 then 1 / 2 else (Real.exp z - 1 - z) / z ^ 2

/-- **Bridge.** The local `φ₁` is the core `LeanDLRA.phi1` (same definition); it is kept under its
name because a catalogue statement of OP-ST-32 is phrased with it. -/
theorem phi1_eq : phi1 = LeanDLRA.phi1 := rfl

/-- **Bridge.** The local `φ₂` is the core `LeanDLRA.phi2` (same definition). -/
theorem phi2_eq : phi2 = LeanDLRA.phi2 := rfl

end LeanDLRA.OpenProblems.Stiff
