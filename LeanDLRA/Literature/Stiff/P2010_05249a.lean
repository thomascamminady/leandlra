import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.FixedRank.TangentSpace

/-!
# Results of arXiv 2010.05249: Low-rank Lie-Trotter for fractional Ginzburg-Landau

Formalized here (real matrices, while the paper's `A_x`, `A_y`, `X` are complex; and the scalar
complex nonlinearity, see below):

* **Sec. 2.3, tangent part** (`stiff_derivative_mem_tangent'`): for `X = U S Vᵀ` with orthonormal
  `U`, `V` and two generators `A_x`, `A_y` of possibly different sizes, the stiff vector field
  `A_x X + X A_y` lies in the range of the tangent projector `P(X)` of the rank-`r` manifold.
  The paper's `A_x`, `A_y` are not required to be transposes of each other, so this strictly
  generalizes `LeanDLRA.Literature.P1803_10473.stiff_derivative_mem_tangent`.
* **Sec. 2.3, rank part** (`rank_stiff_flow`): the exact stiff flow `e^{tA_x} X e^{tA_y}` has the
  same rank as `X = U S Vᵀ` for every `t`, since both exponentials are invertible. The statement
  that the explicit formula solves the ODE (2.7) is not formalized, so the rank claim is about the
  closed-form flow only. The `Aᵀ` special case is `P1803_10473.rank_exp_congr`.
* **Property 1(b), local Lipschitz and bounded nonlinearity** (`ginzburgG_lipschitz_on_ball`,
  `ginzburgG_bounded_on_ball`): the nonlinearity `G(u) = -(κ + iξ)|u|² u + γ u` is Lipschitz with
  constant `3δ²|κ + iξ| + |γ|` and bounded by `|κ + iξ| δ³ + |γ| δ` on the ball `|u| ≤ δ` of `ℂ`.
  This is the scalar core on `ℂ`, not the matrix form; the entrywise extension to `ℂ^{m × n}` in
  the Frobenius norm is not formalized because the library has no complex Frobenius setup here.
  The paper gives no proof of Property 1(b) (it says "we omit the proof"); the proof here is new.

Not formalized, and why:

* **Property 1(a) (cited from Zhang, Zhang and Sun, the paper's ref. [19, Theorem 3.1]):
  contraction and smoothing**
  `‖e^{tA_x} Z e^{tA_y}‖_F ≤ ‖Z‖_F` and the `C₁/t` smoothing bound. The paper cites them and they
  need spectral properties of the complex Toeplitz generators, which the library does not have.
* **Eq. (3.4) (cited from Ostermann et al., ref. [37], Sec. 5) and Theorem 3.1** (full-rank
  versus Lie-Trotter error). Their proofs rely on cited local error bounds for the splitting and on
  the second-order consistency of the fractional difference scheme (paper Assumption 1(c)). Taking
  them as hypotheses would assume key steps, so they are left out.
* **Theorem 3.2 (overall error)**, which combines Theorem 3.1, Eq. (3.4) and the stability bound
  `‖E_fl‖ ≤ e^{LT} σ`. Without the cited sub-results it is not provable here.
* **Eq. (2.11)** (the orthogonal projection `P(X₂)G = P₁G - P₁GP₂ + GP₂`) is already the explicit
  formula `LeanDLRA.tangentProj_apply` in `LeanDLRA/Matrix/Projectors.lean`, so it is not restated.

Core definitions used: `LeanDLRA.tangentProj`, `LeanDLRA.mem_range_tangentProj`.
Local definitions added: `ginzburgG`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2010_05249

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-! ### Stiff flow `A_x X + X A_y` (Sec. 2.3) -/

/-- **arXiv 2010.05249, Sec. 2.3 (tangent part).** For `X = U S Vᵀ` with orthonormal `U`, `V`, the
vector field `A_x X + X A_y = (A_x U S) Vᵀ + U (S Vᵀ A_y)` lies in the range of the tangent
projector `P(X)` of the rank-`r` manifold, for arbitrary square generators `A_x`, `A_y` (the core
`LeanDLRA.mul_add_mul_mem_range_tangentProj`). -/
theorem stiff_derivative_mem_tangent' [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k' ℝ)
    (Ax : Matrix m m ℝ) (Ay : Matrix n n ℝ) :
    Ax * (U * S * Vᵀ) + (U * S * Vᵀ) * Ay ∈
      LinearMap.range (tangentProj U V : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) :=
  mul_add_mul_mem_range_tangentProj hU hV S Ax Ay

/-- **arXiv 2010.05249, Sec. 2.3 (rank part).** The exact stiff flow `X ↦ e^{tA_x} X e^{tA_y}` of
`X = U S Vᵀ` has the same rank as `X` for every `t`, because both matrix exponentials are
invertible. -/
theorem rank_stiff_flow [DecidableEq m] [DecidableEq n] {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    (S : Matrix k k' ℝ) (Ax : Matrix m m ℝ) (Ay : Matrix n n ℝ) (t : ℝ) :
    (NormedSpace.exp (t • Ax) * (U * S * Vᵀ) * NormedSpace.exp (t • Ay)).rank =
      (U * S * Vᵀ).rank := by
  have hA : IsUnit (NormedSpace.exp (t • Ax)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  have hB : IsUnit (NormedSpace.exp (t • Ay)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hB, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hA]

/-! ### The nonlinearity `G(u) = -(κ + iξ)|u|² u + γ u` (Property 1(b)) -/

/-- The scalar core of the fractional Ginzburg–Landau nonlinearity
`G(u) = -(κ + iξ)|u|² u + γ u` on `ℂ`. -/
noncomputable def ginzburgG (κ ξ γ : ℝ) (u : ℂ) : ℂ :=
  -(((κ : ℂ) + (ξ : ℂ) * Complex.I) * ((‖u‖ ^ 2 : ℝ) : ℂ) * u) + (γ : ℂ) * u

/-- `|x|² x - |y|² y = |x|² (x - y) + (|x|² - |y|²) y` has norm at most `3 δ² |x - y|` on the ball
`|x|, |y| ≤ δ`. -/
lemma norm_sq_smul_sub_le (x y : ℂ) {δ : ℝ} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖((‖x‖ ^ 2 : ℝ) : ℂ) * x - ((‖y‖ ^ 2 : ℝ) : ℂ) * y‖ ≤ 3 * δ ^ 2 * ‖x - y‖ := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg x) hx
  have h1 : ((‖x‖ ^ 2 : ℝ) : ℂ) * x - ((‖y‖ ^ 2 : ℝ) : ℂ) * y
      = ((‖x‖ ^ 2 : ℝ) : ℂ) * (x - y) + ((‖x‖ ^ 2 - ‖y‖ ^ 2 : ℝ) : ℂ) * y := by
    push_cast; ring
  have hxy : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have hsum : |‖x‖ + ‖y‖| ≤ 2 * δ := by
    rw [abs_of_nonneg (by positivity)]; linarith
  have hdiff : |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ 2 * δ * ‖x - y‖ := by
    have e : ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) := by ring
    rw [e, abs_mul]
    calc |‖x‖ - ‖y‖| * |‖x‖ + ‖y‖| ≤ ‖x - y‖ * (2 * δ) :=
          mul_le_mul hxy hsum (abs_nonneg _) (norm_nonneg _)
      _ = 2 * δ * ‖x - y‖ := by ring
  have hx2 : ‖x‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  rw [h1]
  calc ‖((‖x‖ ^ 2 : ℝ) : ℂ) * (x - y) + ((‖x‖ ^ 2 - ‖y‖ ^ 2 : ℝ) : ℂ) * y‖
      ≤ ‖((‖x‖ ^ 2 : ℝ) : ℂ) * (x - y)‖ + ‖((‖x‖ ^ 2 - ‖y‖ ^ 2 : ℝ) : ℂ) * y‖ :=
        norm_add_le _ _
    _ = ‖x‖ ^ 2 * ‖x - y‖ + |‖x‖ ^ 2 - ‖y‖ ^ 2| * ‖y‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ δ ^ 2 * ‖x - y‖ + (2 * δ * ‖x - y‖) * δ :=
        add_le_add (mul_le_mul_of_nonneg_right hx2 (norm_nonneg _))
          (mul_le_mul hdiff hy (norm_nonneg _) (by positivity))
    _ = 3 * δ ^ 2 * ‖x - y‖ := by ring

/-- **arXiv 2010.05249, Property 1(b) (Lipschitz part).** On the ball `|u| ≤ δ` in `ℂ`, the
nonlinearity `G(u) = -(κ + iξ)|u|² u + γ u` is Lipschitz with constant
`3 δ² |κ + iξ| + |γ|`. The paper states this without proof. -/
theorem ginzburgG_lipschitz_on_ball (κ ξ γ δ : ℝ) {x y : ℂ} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖ginzburgG κ ξ γ x - ginzburgG κ ξ γ y‖ ≤
      (3 * δ ^ 2 * ‖(κ : ℂ) + (ξ : ℂ) * Complex.I‖ + |γ|) * ‖x - y‖ := by
  have e : ginzburgG κ ξ γ x - ginzburgG κ ξ γ y =
      -(((κ : ℂ) + (ξ : ℂ) * Complex.I)) * (((‖x‖ ^ 2 : ℝ) : ℂ) * x - ((‖y‖ ^ 2 : ℝ) : ℂ) * y)
        + (γ : ℂ) * (x - y) := by
    unfold ginzburgG; ring
  rw [e]
  have hA := norm_sq_smul_sub_le x y hx hy
  calc ‖-(((κ : ℂ) + (ξ : ℂ) * Complex.I)) * (((‖x‖ ^ 2 : ℝ) : ℂ) * x - ((‖y‖ ^ 2 : ℝ) : ℂ) * y)
        + (γ : ℂ) * (x - y)‖
      ≤ ‖-(((κ : ℂ) + (ξ : ℂ) * Complex.I)) * (((‖x‖ ^ 2 : ℝ) : ℂ) * x - ((‖y‖ ^ 2 : ℝ) : ℂ) * y)‖
        + ‖(γ : ℂ) * (x - y)‖ := norm_add_le _ _
    _ = ‖(κ : ℂ) + (ξ : ℂ) * Complex.I‖ *
          ‖((‖x‖ ^ 2 : ℝ) : ℂ) * x - ((‖y‖ ^ 2 : ℝ) : ℂ) * y‖ + |γ| * ‖x - y‖ := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖(κ : ℂ) + (ξ : ℂ) * Complex.I‖ * (3 * δ ^ 2 * ‖x - y‖) + |γ| * ‖x - y‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg _)) le_rfl
    _ = (3 * δ ^ 2 * ‖(κ : ℂ) + (ξ : ℂ) * Complex.I‖ + |γ|) * ‖x - y‖ := by ring

/-- **arXiv 2010.05249, Property 1(b) (boundedness part).** On the ball `|u| ≤ δ`, `‖G(u)‖ ≤
|κ + iξ| δ³ + |γ| δ`. The paper states this without proof. -/
theorem ginzburgG_bounded_on_ball (κ ξ γ δ : ℝ) {x : ℂ} (hx : ‖x‖ ≤ δ) :
    ‖ginzburgG κ ξ γ x‖ ≤ ‖(κ : ℂ) + (ξ : ℂ) * Complex.I‖ * δ ^ 3 + |γ| * δ := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg x) hx
  have e : ginzburgG κ ξ γ x =
      -(((κ : ℂ) + (ξ : ℂ) * Complex.I) * ((‖x‖ ^ 2 : ℝ) : ℂ) * x) + (γ : ℂ) * x := rfl
  rw [e]
  have h2 : ‖x‖ ^ 2 * ‖x‖ ≤ δ ^ 3 := by
    have : ‖x‖ ^ 2 * ‖x‖ ≤ δ ^ 2 * δ :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) hx (norm_nonneg _) (by positivity)
    nlinarith
  calc ‖-(((κ : ℂ) + (ξ : ℂ) * Complex.I) * ((‖x‖ ^ 2 : ℝ) : ℂ) * x) + (γ : ℂ) * x‖
      ≤ ‖-(((κ : ℂ) + (ξ : ℂ) * Complex.I) * ((‖x‖ ^ 2 : ℝ) : ℂ) * x)‖ + ‖(γ : ℂ) * x‖ :=
        norm_add_le _ _
    _ = ‖(κ : ℂ) + (ξ : ℂ) * Complex.I‖ * (‖x‖ ^ 2 * ‖x‖) + |γ| * ‖x‖ := by
        rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        ring
    _ ≤ ‖(κ : ℂ) + (ξ : ℂ) * Complex.I‖ * δ ^ 3 + |γ| * δ :=
        add_le_add (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hx (abs_nonneg _))

/-! ### Non-vacuity -/

/-- The nonlinearity vanishes at zero with zero coefficients, and the ball bounds apply to the
unit ball, which contains `0` and `1`. -/
example : ginzburgG 0 0 0 0 = 0 := by simp [ginzburgG]

example (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖ginzburgG 1 1 1 x - ginzburgG 1 1 1 y‖ ≤
      (3 * 1 ^ 2 * ‖((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I‖ + |(1 : ℝ)|) * ‖x - y‖ :=
  ginzburgG_lipschitz_on_ball 1 1 1 1 hx hy

end LeanDLRA.Literature.P2010_05249
