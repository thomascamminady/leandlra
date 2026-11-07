import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2306.07774: Rank-reduced Kalman filter

Matrix-algebra cores of Prop. 1, Cor. 1 and the Lyapunov step of Sec. 2.2 / App. C of
Schmidt, Hennig, Nick, Tronarp, *The Rank-Reduced Kalman Filter* (arXiv 2306.07774, NeurIPS 2023).
Everything is stated over `ℝ` with transposition `ᵀ` in place of the paper's `*`.

* **Prop. 1** (static low-rank Gaussian inference, App. A.1). Given the SVD `Wᵀ = U D Vᵀ` of
  `W = R^{-1/2} C Π^{1/2}` (predicate `IsSVDOfW`: `UᵀU = 1`, `VᵀV = 1`, `D = diag d`), we prove
  `(I + WᵀW)⁻¹ = U (I + D²)⁻¹ Uᵀ` (`IsSVDOfW.inv_one_add_wtw`), the gain identity
  `(I + WᵀW)⁻¹ Wᵀ = U (I + D²)⁻¹ D Vᵀ` (`IsSVDOfW.gain`), `det (VD²Vᵀ + I) = ∏ₖ (1 + Dₖₖ²)`
  (`IsSVDOfW.det_add_one`, Eq. (A.8)), the inverse `(VD²Vᵀ + I)⁻¹ = I − V D (D²+I)⁻¹ D Vᵀ`
  (`IsSVDOfW.inv_add_one`, Eq. (A.14)), and the marginal log-likelihood formula (12)
  (`prop1_logLikelihood`), where `log N(y; c, S)` is the standard closed form `gaussLogDensity`.
  Not formalized: the distributional Eqs. (11a), (11b) and the Gaussian conditioning (A.1a)–(A.1b),
  which need a probability layer that the library does not have; only their algebra is proved.
  The paper's `r ≤ m` and `Dₖₖ ≥ 0` are not needed by the algebra and are not assumed.
* **Cor. 1** (low-rank correction, Eqs. (13)–(15)). The matrix parts are proved: the gain
  `Π^{1/2} (I + WᵀW)⁻¹ Wᵀ = Π^{1/2} U (I+D²)⁻¹ D Vᵀ` (`cor1_gain`), the covariance
  `Π^{1/2} (I + WᵀW)⁻¹ Π^{1/2 ᵀ} = Π^{1/2} U (I+D²)⁻¹ Uᵀ Π^{1/2 ᵀ}` (`cor1_cov`), and the square
  root `Σ^{1/2} = Π^{1/2} U (I+D²)^{-1/2}` with `Σ^{1/2} (Σ^{1/2})ᵀ = Σ` (`cor1_sqrt`).
  Not formalized: the claim `x | y ~ N(μ + K e, Σ)` of Eq. (13), which needs a probability layer.
* **Sec. 2.2 / App. C, Lyapunov compression** (S-step of the DLRA integrator for
  `Q̇ = AQ + QAᵀ + BBᵀ`, Eq. (C.4)). `lyapunov_sStep_reduced` proves that for `UᵀU = 1` and
  `Q = U D Uᵀ`, `Uᵀ (AQ + QAᵀ + BBᵀ) U = (UᵀAU) D + D (UᵀAU)ᵀ + (UᵀB)(UᵀB)ᵀ`, i.e. the
  S-step is again a Lyapunov equation with reduced coefficients.  Not restated here: the
  truncated SVD (Eq. (17)), whose optimality is Eckart–Young, and the symmetric BUG, which is
  `LeanDLRA.Integrators.Matrix.Symmetry`.
* **Prop. B.1** (correction for `m < r`, App. B) is **not** formalized.  Its SVD of the
  `m × (r+m)` matrix `(CΠ^{1/2}  R^{1/2})` is written with inconsistent sizes for `D^s` in
  (B.2a)–(B.3), so the Moore–Penrose formula (B.3) cannot be used as stated.

Core definitions reused: the matrix conventions of `LeanDLRA.Matrix` (real `Matrix`, `ᵀ`,
orthonormal columns as `Uᵀ * U = 1`).  Definitions added locally: the SVD predicate `IsSVDOfW`
and the Gaussian log-density `gaussLogDensity` (the standard formula, used only to state (12)).
No `kalmanGain` is restated: the paper's gain is in whitened coordinates (`Π^{1/2}`, `R^{-1/2}`),
not that of `LeanDLRA.KalmanBucy`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2306_07774

/-- The SVD data of Prop. 1 (arXiv 2306.07774, Prop. 1): `W` is `m × r`, `Wᵀ = U D Vᵀ` with
`D = diag d` an `r × r` diagonal matrix, `U` (`r × r`) and `V` (`m × r`) with orthonormal
columns. -/
structure IsSVDOfW {m r : ℕ} (W : Matrix (Fin m) (Fin r) ℝ) (U : Matrix (Fin r) (Fin r) ℝ)
    (d : Fin r → ℝ) (V : Matrix (Fin m) (Fin r) ℝ) : Prop where
  orthU : Uᵀ * U = 1
  orthV : Vᵀ * V = 1
  svd : Wᵀ = U * Matrix.diagonal d * Vᵀ

/-- Gaussian log-density `log N(y; μ, S)` in its standard closed form
`-(m/2) log 2π - (1/2) log |det S| - (1/2) (y-μ)ᵀ S⁻¹ (y-μ)`, the formula behind the paper's (12).
It is a definition only: the paper's probabilistic statements are not formalized. -/
noncomputable def gaussLogDensity {m : ℕ} (y μ : Fin m → ℝ) (S : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  -(m : ℝ) / 2 * Real.log (2 * Real.pi) - 1 / 2 * Real.log |S.det|
    - 1 / 2 * ((y - μ) ⬝ᵥ (S⁻¹ *ᵥ (y - μ)))

section Prop1

variable {m r n : ℕ}

theorem IsSVDOfW.wtw {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V) :
    Wᵀ * W = U * Matrix.diagonal (fun k => d k ^ 2) * Uᵀ := by
  have hW : Wᵀ * W = Wᵀ * Wᵀᵀ := by rw [Matrix.transpose_transpose]
  have e2 : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal (fun k => d k ^ 2) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    ring
  rw [hW, h.svd]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᵀ V, h.orthV, Matrix.one_mul, ← e2]
  simp only [Matrix.mul_assoc]

theorem IsSVDOfW.wwt {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V) :
    W * Wᵀ = V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ := by
  have hW : W * Wᵀ = Wᵀᵀ * Wᵀ := by rw [Matrix.transpose_transpose]
  have e2 : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal (fun k => d k ^ 2) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    ring
  rw [hW, h.svd]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, h.orthU, Matrix.one_mul, ← e2]
  simp only [Matrix.mul_assoc]

/-- **Prop. 1, Eq. (A.2a)–(A.3)**: `(I + WᵀW)⁻¹ = U (I + D²)⁻¹ Uᵀ`. -/
theorem IsSVDOfW.inv_one_add_wtw {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V) :
    (1 + Wᵀ * W)⁻¹ = U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ := by
  have hE : Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) + Matrix.diagonal (fun k => d k ^ 2)
      * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_one]
    congr 1
    funext k
    have hk : (1 + d k ^ 2) ≠ 0 := by positivity
    field_simp
  have hU1 : U * Uᵀ = 1 := mul_eq_one_comm.mp h.orthU
  apply Matrix.inv_eq_right_inv
  rw [h.wtw]
  calc (1 + U * Matrix.diagonal (fun k => d k ^ 2) * Uᵀ)
        * (U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ)
      = U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ
        + U * Matrix.diagonal (fun k => d k ^ 2) * (Uᵀ * U)
          * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ := by
        simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹)
          + Matrix.diagonal (fun k => d k ^ 2) * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹))
          * Uᵀ := by
        rw [h.orthU, Matrix.mul_one]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hE, Matrix.mul_one, hU1]

/-- **Prop. 1, gain (A.4)**: `(I + WᵀW)⁻¹ Wᵀ = U (I + D²)⁻¹ D Vᵀ`. -/
theorem IsSVDOfW.gain {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V) :
    (1 + Wᵀ * W)⁻¹ * Wᵀ = U * Matrix.diagonal (fun k => d k / (1 + d k ^ 2)) * Vᵀ := by
  have hED : Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Matrix.diagonal d
      = Matrix.diagonal (fun k => d k / (1 + d k ^ 2)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    ring
  rw [h.inv_one_add_wtw, h.svd]
  calc U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ * (U * Matrix.diagonal d * Vᵀ)
      = U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * (Uᵀ * U) * Matrix.diagonal d * Vᵀ := by
        simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Matrix.diagonal d) * Vᵀ := by
        rw [h.orthU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun k => d k / (1 + d k ^ 2)) * Vᵀ := by rw [hED]

/-- **Prop. 1, Eq. (A.8)**: `det (VD²Vᵀ + I) = ∏ₖ (1 + Dₖₖ²)`. -/
theorem IsSVDOfW.det_add_one {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V) :
    (V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ + 1).det = ∏ k, (1 + d k ^ 2) := by
  rw [add_comm, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h.orthV,
    Matrix.mul_one, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.det_diagonal]

/-- **Prop. 1, Eq. (A.9)–(A.14)**: `(VD²Vᵀ + I)⁻¹ = I − V D (D²+I)⁻¹ D Vᵀ`. -/
theorem IsSVDOfW.inv_add_one {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V) :
    (V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ + 1)⁻¹
      = 1 - V * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k) * Vᵀ := by
  have hF : Matrix.diagonal (fun k => d k ^ 2)
      - Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k)
      - Matrix.diagonal (fun k => d k ^ 2) * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k)
      = 0 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub, Matrix.diagonal_sub,
      ← Matrix.diagonal_zero]
    congr 1
    funext k
    have hk : (1 + d k ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have key : (1 + V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ)
      * (1 - V * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k) * Vᵀ)
      = 1 + V * (Matrix.diagonal (fun k => d k ^ 2)
          - Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k)
          - Matrix.diagonal (fun k => d k ^ 2)
            * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k))
          * Vᵀ := by
    have h1 : (V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ)
        * (V * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k) * Vᵀ)
        = V * (Matrix.diagonal (fun k => d k ^ 2)
            * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k))
          * Vᵀ := by
      calc (V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ)
            * (V * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k) * Vᵀ)
          = V * Matrix.diagonal (fun k => d k ^ 2) * (Vᵀ * V)
            * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k) * Vᵀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h.orthV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h1]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  apply Matrix.inv_eq_right_inv
  rw [add_comm, key, hF, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- The determinant of `VD²Vᵀ + I` is positive. -/
theorem IsSVDOfW.det_add_one_pos {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V) :
    0 < (V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ + 1).det := by
  rw [h.det_add_one]
  exact Finset.prod_pos (fun k _ => by positivity)

/-- **Prop. 1, marginal log-likelihood (12)**.  With `S = R^{1/2}(VD²Vᵀ + I)R^{1/2 ᵀ}`
(`Rh = R^{1/2}`, `Rhi = R^{-1/2}`, `Rhi Rh = 1`) and the whitened residual
`e = R^{-1/2}(y - Cμ)` (here `c = Cμ`):
`log N(y; c, S) = -(m/2) log 2π - log|R^{1/2}| - (1/2) ∑ₖ log(1 + Dₖₖ²) - (1/2)‖e‖² +
(1/2) eᵀ V D (D²+I)⁻¹ D Vᵀ e`. -/
theorem prop1_logLikelihood {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V)
    (Rh Rhi : Matrix (Fin m) (Fin m) ℝ) (hRi : Rhi * Rh = 1) (y c : Fin m → ℝ) :
    gaussLogDensity y c (Rh * (V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ + 1) * Rhᵀ)
      = -(m : ℝ) / 2 * Real.log (2 * Real.pi) - Real.log |Rh.det|
        - 1 / 2 * ∑ k, Real.log (1 + d k ^ 2)
        - 1 / 2 * ((Rhi *ᵥ (y - c)) ⬝ᵥ (Rhi *ᵥ (y - c)))
        + 1 / 2 * ((Rhi *ᵥ (y - c)) ⬝ᵥ
            ((V * Matrix.diagonal (fun k => d k * (1 + d k ^ 2)⁻¹ * d k) * Vᵀ)
              *ᵥ (Rhi *ᵥ (y - c)))) := by
  have hRh : Rh * Rhi = 1 := mul_eq_one_comm.mp hRi
  have hdetRh : Rh.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hRi
    rw [Matrix.det_mul, Matrix.det_one, h0, mul_zero] at this
    exact zero_ne_one this
  have hMpos := h.det_add_one_pos
  have hMinv := h.inv_add_one
  set M := V * Matrix.diagonal (fun k => d k ^ 2) * Vᵀ + 1 with hMdef
  have hRhT : Rhᵀ * Rhiᵀ = 1 := by rw [← Matrix.transpose_mul, hRi, Matrix.transpose_one]
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hMpos.ne')
  have hSinv : (Rh * M * Rhᵀ)⁻¹ = Rhiᵀ * M⁻¹ * Rhi := by
    apply Matrix.inv_eq_right_inv
    calc Rh * M * Rhᵀ * (Rhiᵀ * M⁻¹ * Rhi)
        = Rh * M * (Rhᵀ * Rhiᵀ) * M⁻¹ * Rhi := by simp only [Matrix.mul_assoc]
      _ = Rh * (M * M⁻¹) * Rhi := by rw [hRhT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMM, Matrix.mul_one, hRh]
  have hdetS : (Rh * M * Rhᵀ).det = Rh.det ^ 2 * M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hq : ∀ v : Fin m → ℝ, v ⬝ᵥ ((Rhiᵀ * M⁻¹ * Rhi) *ᵥ v)
      = (Rhi *ᵥ v) ⬝ᵥ (M⁻¹ *ᵥ (Rhi *ᵥ v)) := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hdetM : M.det = ∏ k, (1 + d k ^ 2) := h.det_add_one
  unfold gaussLogDensity
  rw [hSinv, hq, hdetS, abs_of_nonneg (mul_nonneg (sq_nonneg _) hMpos.le), hMinv,
    Real.log_mul (pow_ne_zero 2 hdetRh) hMpos.ne', Real.log_pow, Real.log_abs, hdetM,
    Real.log_prod (fun k _ => by positivity), Matrix.sub_mulVec, Matrix.one_mulVec,
    dotProduct_sub]
  push_cast
  ring

/-- **Cor. 1, gain (Eq. (14))**: `K = Π^{1/2} (I + WᵀW)⁻¹ Wᵀ = Π^{1/2} U (I+D²)⁻¹ D Vᵀ`. -/
theorem cor1_gain {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V)
    (Pih : Matrix (Fin n) (Fin r) ℝ) :
    Pih * (1 + Wᵀ * W)⁻¹ * Wᵀ = Pih * U * Matrix.diagonal (fun k => d k / (1 + d k ^ 2)) * Vᵀ := by
  rw [Matrix.mul_assoc, h.gain]
  simp only [Matrix.mul_assoc]

/-- **Cor. 1, covariance (Eq. (14))**:
`Σ = Π^{1/2} (I + WᵀW)⁻¹ Π^{1/2 ᵀ} = Π^{1/2} U (I+D²)⁻¹ Uᵀ Π^{1/2 ᵀ}`. -/
theorem cor1_cov {W : Matrix (Fin m) (Fin r) ℝ} {U : Matrix (Fin r) (Fin r) ℝ}
    {d : Fin r → ℝ} {V : Matrix (Fin m) (Fin r) ℝ} (h : IsSVDOfW W U d V)
    (Pih : Matrix (Fin n) (Fin r) ℝ) :
    Pih * (1 + Wᵀ * W)⁻¹ * Pihᵀ
      = Pih * U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ * Pihᵀ := by
  rw [h.inv_one_add_wtw]
  simp only [Matrix.mul_assoc]

/-- **Cor. 1, square root (Eq. (15))**: with `Σ^{1/2} = Π^{1/2} U (I+D²)^{-1/2}`, the product
`Σ^{1/2} (Σ^{1/2})ᵀ` equals the covariance `Π^{1/2} U (I+D²)⁻¹ Uᵀ Π^{1/2 ᵀ}`. -/
theorem cor1_sqrt {U : Matrix (Fin r) (Fin r) ℝ} {d : Fin r → ℝ} (Pih : Matrix (Fin n) (Fin r) ℝ) :
    (Pih * U * Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹))
        * (Pih * U * Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹))ᵀ
      = Pih * U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ * Pihᵀ := by
  have hss : Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹)
      * Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹)
      = Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  calc (Pih * U * Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹))
        * (Pih * U * Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹))ᵀ
      = Pih * U * (Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹)
          * Matrix.diagonal (fun k => (√(1 + d k ^ 2))⁻¹)) * Uᵀ * Pihᵀ := by
        simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = Pih * U * Matrix.diagonal (fun k => (1 + d k ^ 2)⁻¹) * Uᵀ * Pihᵀ := by rw [hss]

/-- **Sec. 2.2 / App. C, Eq. (C.4)**: the S-step of the DLRA integrator for `F(Q) = AQ + QAᵀ + BBᵀ`
at `Q = U D Uᵀ` (`UᵀU = 1`) is the reduced Lyapunov equation
`Uᵀ F(U D Uᵀ) U = (UᵀAU) D + D (UᵀAU)ᵀ + (UᵀB)(UᵀB)ᵀ`. -/
theorem lyapunov_sStep_reduced {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin k) ℝ) (Uh : Matrix (Fin n) (Fin r) ℝ) (hU : Uhᵀ * Uh = 1)
    (D : Matrix (Fin r) (Fin r) ℝ) :
    Uhᵀ * (A * (Uh * D * Uhᵀ) + (Uh * D * Uhᵀ) * Aᵀ + B * Bᵀ) * Uh
      = (Uhᵀ * A * Uh) * D + D * (Uhᵀ * A * Uh)ᵀ + (Uhᵀ * B) * (Uhᵀ * B)ᵀ := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc Uhᵀ Uh, hU, Matrix.one_mul, Matrix.mul_one]

end Prop1

/-- Non-vacuity: the SVD hypotheses of Prop. 1 hold for `W = (2)`, `U = 1`, `d = (2)`, `V = 1`. -/
example : IsSVDOfW (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 1 ![2] 1 := by
  refine ⟨by simp, by simp, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.diagonal]

end LeanDLRA.Literature.P2306_07774
