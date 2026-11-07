import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2204.10896: DLRA for Vlasov-Ampere-Fokker-Planck (AP, IMEX)

This module proves the exact K/S cancellation of Appendix A (eqs. (A.5)-(A.10) of arXiv 2204.10896).
Let `K^n = X^n S^n` be the factorization at time `t^n`, and let `V^n` be the velocity basis. The
K-step is backward Euler for `∂_t K = (1/ε) K Dᵀ`, the QR step gives `K^{n+1} = X^{n+1} S¹`, and the
S-step is forward Euler for `∂_t S = -(1/ε) S Dᵀ`, with `X^{n+1}` frozen. The theorem
`homogeneous_cancellation` shows `X^{n+1} S² (V^n)ᵀ = K^n (V^n)ᵀ = g^n` for every `Δt/ε`, i.e. the
discrete flow preserves the spatially homogeneous state. The relation is proved for
arbitrary matrices with no invertibility of `I - (Δt/ε) Dᵀ` assumed; the paper's (A.9) is the
inverted form of the backward Euler relation, which holds when that matrix is invertible.

Core definitions: none. The file uses only Mathlib matrices. The ODEs (A.5)-(A.6) and the Euler
schemes are stated as hypotheses. The reduction of (A.2)-(A.4) to these matrix ODEs is not
re-derived.

Left out (not formalized):
* Sec. 2, eqs. (2.5)-(2.18): the three-step projector splitting. The abstract KSL step is the core
  `IsKSLStep`; the coupled Ampère field (2.15) is not modelled.
* Sec. 3.1-3.2, eqs. (3.3)-(3.22): the IMEX K and L steps and the full S-step, which involve the
  velocity-dependent operators and the FFT convolution. No existence or stability claim
  is made here.
  The stability analogues are `hybridKSL_norm_le` and `implicitGalerkin_norm_le`.
* The computational cost counts of Sec. 3.
* The claim `P_1 g^n = g^n` that the header mentioned, which the paper does not state.

No claim in the paper is found to be false.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2204_10896

variable {Nx Nv r : ℕ}

/-- **Appendix A, eqs. (A.5)-(A.10): exact K/S cancellation** (arXiv 2204.10896, App. A).
Hypotheses: `Kn = K^n`, `Kn1 = K^{n+1}`, `X1 = X^{n+1}`, `S1 = S¹`, `S2 = S²`, `Vn = V^n`, and
`D` is the matrix `{d¹_{jl}}` of (3.6).
* `hK` is the backward Euler step of (A.5): `K^{n+1} = K^n + (Δt/ε) K^{n+1} Dᵀ`, which is (A.9)
  written without the inverse.
* `hQR` is the QR step of the K-step, `K^{n+1} = X^{n+1} S¹`.
* `hS` is the forward Euler step of (A.6): `S² = S¹ - (Δt/ε) S¹ Dᵀ`, which is (A.10).
Conclusion: `X^{n+1} S² (V^n)ᵀ = K^n (V^n)ᵀ`, i.e. `g² = g^n` in the paper's notation. -/
theorem homogeneous_cancellation {Δt ε : ℝ} {D : Matrix (Fin r) (Fin r) ℝ}
    {Kn Kn1 X1 : Matrix (Fin Nx) (Fin r) ℝ} {S1 S2 : Matrix (Fin r) (Fin r) ℝ}
    {Vn : Matrix (Fin Nv) (Fin r) ℝ}
    (hK : Kn1 = Kn + (Δt / ε) • (Kn1 * Dᵀ))
    (hQR : X1 * S1 = Kn1)
    (hS : S2 = S1 - (Δt / ε) • (S1 * Dᵀ)) :
    X1 * S2 * Vnᵀ = Kn * Vnᵀ := by
  have h1 : X1 * S2 = Kn := by
    rw [hS, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hQR]
    exact sub_eq_of_eq_add hK
  rw [h1]

/-- Non-vacuity: the hypotheses of `homogeneous_cancellation` hold for the identity matrices with
`D = 0`, so the theorem applies to a genuine instance. -/
example (Δt ε : ℝ) :
    (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
        (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ := by
  apply homogeneous_cancellation (D := 0) (Kn := 1) (Kn1 := 1) (X1 := 1) (S1 := 1) (S2 := 1)
    (Δt := Δt) (ε := ε) <;> simp

end LeanDLRA.Literature.P2204_10896
