import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature
import LeanDLRA.HighOrder.RungeKuttaBUG
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.ODE
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal

/-!
# Robust high-order projector-splitting integrators (Zhang–Hu, arXiv 2608.17157)

For a prescribed increment `ΔA`, Zhang and Hu reduce the K–S–L projector-splitting step to the
K–L step `Y₁ = U₁ U₁ᵀ (Y₀ + ΔA)` with `U₁ Ŝ₁ = (Y₀ + ΔA) V₀` (`IsKLStep`; the factored output
`U₁ S₁ V₁ᵀ`, `V₁ S₁ᵀ = (Y₀ + ΔA)ᵀ U₁`, is `isKLStep_of_factors`), and use Runge–Kutta increments.
The module works on real `m × n` matrices with the Frobenius norm and the spectral norm
`specNorm`. It proves Theorem 4.1 (`IsKLStep.relaxed_exactness`:
`‖Y₁ - Y⋆‖ ≤ (1 + ‖Q‖₂) ‖Y₀ + ΔA - Y⋆‖` for `Y⋆ = (Y⋆ V₀) Q`); the overlap part of Lemma 4.2
(Appendix A.4, `exists_overlap_of_specNorm_sub_one_le`: `Ỹ = L Y₀ R` with `‖R - I‖₂ ≤ 1/2` gives
`Ỹ = (Ỹ V₀) Q` with `‖Q‖₂ ≤ 3`); Theorem 4.3 (`IsKLStep.one_step_error`:
`‖Y₁ - A(s)‖ ≤ 4 ‖Y₀ + ΔA - A(s)‖ + 5 η`); Theorem 5.1 and Eq. (5.3) (`klStep_global_error`,
`klStep_global_error_of_order`); Theorem 6.1 for Algorithm 6.1 (`IsRKKLStep`):
`rk_increment_error` (increment error `C (h^{p+1} + h² ε)` with the paper's constant
`C = M_p/p! (1/(p+1) + ∑ |bᵢ| cᵢ^p) + L C_st ∑ |bᵢ|`, `rkConst`), `IsRKKLStep.one_step_error`
and `rkKL_global_error`; and the corollaries of Section 6 with explicit stage bounds: the
two-stage family of Remark 6.3 (`IsRK2KLStep.one_step_error`, `rk2KL_global_error`), the
midpoint method (`IsMidpointKLStep.one_step_error`, stage bound `(M₁/2) h² + (5/2) h η` as in
the paper) and Heun's RK3 (`IsHeun3KLStep.one_step_error`, `heun3KL_global_error`), all of
robust order 2, 2 and 3: no constant depends on singular values. Tools: the sharp
vector-valued Taylor bound `norm_sub_taylorWithinEval_le` (`C (x - a)^{n+1}/(n+1)!`) and the
quadrature estimate `norm_quadrature_sub_le`; `exists_isKLStep` shows that every step exists.

Differences from the paper. (1) Lemma 4.2 is proved only in its last part (A.4). Its
differential-inclusion part (Lemmas A.1–A.3: the normal bound on lower-rank strata, the split
`F = G_L X + X G_R + E`, and the curve `Ỹ(s) = L(s) Y₀ R(s)` with `‖R(s) - I‖₂ ≤ e^{K_G s} - 1`
and `‖Ỹ(s) - A(s)‖ ≤ √(mn) ε_r s e^{L_F s}`) is the hypothesis `HasComparisonCurve Y₀ A(s) η`,
and Theorems 4.3, 5.1, 6.1 and the corollaries are proved under it, at `s = h` and, for the stage
bounds, at every `σ ∈ [0, h]` in the form `σ η` with `η = √(mn) ε_r e^{L_F h}` (so the midpoint
stage bound has `e^{L_F h}` where the paper has `e^{L_F h/2}`). `L` need not be invertible.
(2) Lemma 6.2 (bounds on `g_n^{(q)}`, `g_n(s) = F(t_n + s, A_n(s))`) is not proved: the bounds
`‖g^{(q)}‖ ≤ M_q` are hypotheses, as in the statement of Theorem 6.1. For `q ≤ 2` the library
bounds `y''`, `y'''` of solutions (`ODESolution.norm_iteratedDerivWithin_two_le`,
`ODESolution.norm_iteratedDerivWithin_three_le`). (3) Rank-admissibility is never needed. The
nodes are assumed in `[0, 1]` (implicit in the paper). (4) `h ≤ h₀ ≤ 1` is not assumed and all
constants are explicit: `C_T` is `e^{L T}` times the displayed bracket. In the corollaries the
quadrature constants are the generic ones of `norm_quadrature_sub_le` (e.g. `7/81 M₂ h³` for
the Heun stage 3, where the paper uses the sharp midpoint-rule constant `M₂ h³/81`). (5) The
abstract forms of Theorems 4.1 and 5.1 (inner product space, projectors) were already in the
library (`RungeKuttaBUG.relaxed_exactness`, `RungeKuttaBUG.relaxed_global_error`); the first is
used here. Remark 6.4 (RK4) is not formalized; the paper gives no proof. No claim of the paper
was found to be false.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius Nat

namespace LeanDLRA.Literature.P2608_17157

open LeanDLRA LeanDLRA.Curvature

section KL

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- The **reduced K–L step** of arXiv 2608.17157 (Section 3) in relational form: from the
right basis `V₀` (`Y₀ = U₀ S₀ V₀ᵀ`) and the updated matrix `X = Y₀ + ΔA`, the K-step factors
`K₁ = X V₀ = U₁ Ŝ₁` with orthonormal `U₁`, and the step returns `Y₁ = U₁ U₁ᵀ X`
(`= U₁ S₁ V₁ᵀ` with `V₁ S₁ᵀ = Xᵀ U₁`, see `isKLStep_of_factors`). -/
def IsKLStep (V₀ : Matrix n r ℝ) (X Y₁ : Matrix m n ℝ) : Prop :=
  ∃ (U₁ : Matrix m r ℝ) (Ŝ₁ : Matrix r r ℝ), U₁ᵀ * U₁ = 1 ∧ U₁ * Ŝ₁ = X * V₀ ∧
    Y₁ = U₁ * U₁ᵀ * X

/-- The factored output of the reduced K–L step (`K₁ = X V₀ = U₁ Ŝ₁`, `L₁ = Xᵀ U₁ = V₁ S₁ᵀ`,
`Y₁ = U₁ S₁ V₁ᵀ`) satisfies `Y₁ = U₁ U₁ᵀ X` (arXiv 2608.17157, Section 3). -/
theorem isKLStep_of_factors {V₀ : Matrix n r ℝ} {X : Matrix m n ℝ} {U₁ : Matrix m r ℝ}
    {Ŝ₁ S₁ : Matrix r r ℝ} {V₁ : Matrix n r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hK : U₁ * Ŝ₁ = X * V₀)
    (hL : V₁ * S₁ᵀ = Xᵀ * U₁) : IsKLStep V₀ X (U₁ * S₁ * V₁ᵀ) := by
  refine ⟨U₁, Ŝ₁, hU₁, hK, ?_⟩
  have h : S₁ * V₁ᵀ = U₁ᵀ * X := by
    have := congrArg Matrix.transpose hL
    simpa [Matrix.transpose_mul] using this
  rw [Matrix.mul_assoc, h, Matrix.mul_assoc]

/-- **Theorem 4.1 (relaxed exactness)** of arXiv 2608.17157, for the reduced K–L step on real
`m × n` matrices with the Frobenius norm.  Let `V₀` have orthonormal columns, let `Y₁` be the
output of the reduced K–L step from `V₀` with `X = Y₀ + ΔA`, and let `Y⋆` satisfy the row-space
overlap condition `Y⋆ = (Y⋆ V₀) Q`.  Then `‖Y₁ - Y⋆‖ ≤ (1 + ‖Q‖₂) ‖Y₀ + ΔA - Y⋆‖`.
No rank-admissibility is needed: the bound holds for every orthonormal `U₁` with
`U₁ Ŝ₁ = (Y₀ + ΔA) V₀` (rank-admissibility only makes `U₁ U₁ᵀ` unique).  The proof applies the
abstract `RungeKuttaBUG.relaxed_exactness` with `P = U₁U₁ᵀ(·)` and `M = (·) V₀ Q`. -/
theorem IsKLStep.relaxed_exactness [DecidableEq n] {V₀ : Matrix n r ℝ} {X Y₁ Ys : Matrix m n ℝ}
    {Q : Matrix r n ℝ} (hstep : IsKLStep V₀ X Y₁) (hV₀ : V₀ᵀ * V₀ = 1)
    (hstar : Ys = Ys * V₀ * Q) : ‖Y₁ - Ys‖ ≤ (1 + specNorm Q) * ‖X - Ys‖ := by
  obtain ⟨U₁, Ŝ₁, hU₁, hK, rfl⟩ := hstep
  have hM : ∀ z : Matrix m n ℝ, ‖Frobenius.rightMulCLM (V₀ * Q) z‖ ≤ specNorm Q * ‖z‖ := by
    intro z
    rw [Frobenius.rightMulCLM_apply]
    calc ‖z * (V₀ * Q)‖ ≤ ‖z‖ * specNorm (V₀ * Q) := frob_mul_le' _ _
      _ ≤ ‖z‖ * (specNorm V₀ * specNorm Q) :=
          mul_le_mul_of_nonneg_left (specNorm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖z‖ * (1 * specNorm Q) := by
          gcongr
          exacts [specNorm_nonneg _, specNorm_le_one_of_orthonormal hV₀]
      _ = specNorm Q * ‖z‖ := by ring
  have h := RungeKuttaBUG.relaxed_exactness (P := leftProj U₁) (M := Frobenius.rightMulCLM (V₀ * Q))
    (isOrthProj_leftProj hU₁) hM (X := X) (Ys := Ys)
    (by rw [Frobenius.rightMulCLM_apply, ← Matrix.mul_assoc]; exact hstar.symm)
    (by
      rw [Frobenius.rightMulCLM_apply, ← Matrix.mul_assoc X, ← hK, Matrix.mul_assoc U₁]
      exact leftProj_mul_left hU₁ _)
  simpa [leftProj_apply] using h

end KL

/-! ### The comparison curve (Lemma 4.2) and the one-step estimate (Theorem 4.3) -/

section Comparison

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- The spectral norm satisfies the triangle inequality (auxiliary for arXiv 2608.17157,
Lemma 4.2). -/
theorem specNorm_add_le (A B : Matrix m n ℝ) : specNorm (A + B) ≤ specNorm A + specNorm B := by
  unfold specNorm
  rw [map_add, map_add]
  exact norm_add_le _ _

omit [Fintype m] [DecidableEq n] in
/-- A factored matrix `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `V₀` satisfies `Y₀ = Y₀ V₀ V₀ᵀ`, the
hypothesis of Lemma 4.2 of arXiv 2608.17157. -/
theorem mul_mul_transpose_of_factored {k : Type*} [Fintype k] {Y₀ : Matrix m n ℝ}
    {U₀ : Matrix m k ℝ} {S₀ : Matrix k r ℝ} {V₀ : Matrix n r ℝ} (hV₀ : V₀ᵀ * V₀ = 1)
    (hY₀ : Y₀ = U₀ * S₀ * V₀ᵀ) : Y₀ * V₀ * V₀ᵀ = Y₀ := by
  rw [hY₀, Matrix.mul_assoc (U₀ * S₀) V₀ᵀ V₀, hV₀, Matrix.mul_one]

/-- **Lemma 4.2, row-space overlap of the comparison curve** (arXiv 2608.17157, Lemma 4.2 and
Appendix A.4).  If `Y₀ = Y₀ V₀ V₀ᵀ` with orthonormal `V₀` and the comparison curve has the form
`Ỹ = L Y₀ R` with `‖R - I‖₂ ≤ 1/2` (Lemma A.3 gives `‖R(s) - I‖₂ ≤ e^{K_G s} - 1`, which is
`≤ 1/2` for `s ≤ h*`), then `Q = D⁻¹ V₀ᵀ R` with `D = V₀ᵀ R V₀` satisfies `Ỹ = (Ỹ V₀) Q` and
`‖Q‖₂ ≤ 3`.  As in the paper, `‖D - I‖₂ ≤ 1/2` gives `‖D⁻¹‖₂ ≤ 2`, and
`‖Q‖₂ ≤ ‖D⁻¹‖₂ ‖R‖₂ ≤ 2 · 3/2`.  `L` is arbitrary (no invertibility is needed). -/
theorem exists_overlap_of_specNorm_sub_one_le {Y₀ : Matrix m n ℝ} {V₀ : Matrix n r ℝ}
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) (L : Matrix m m ℝ) {R : Matrix n n ℝ}
    (hR : specNorm (R - 1) ≤ 1 / 2) :
    ∃ Q : Matrix r n ℝ, L * Y₀ * R = L * Y₀ * R * V₀ * Q ∧ specNorm Q ≤ 3 := by
  set D : Matrix r r ℝ := V₀ᵀ * R * V₀ with hDdef
  have hD1 : D - 1 = V₀ᵀ * (R - 1) * V₀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV₀]
  have hV₀s : specNorm V₀ ≤ 1 := specNorm_le_one_of_orthonormal hV₀
  have hV₀ts : specNorm V₀ᵀ ≤ 1 := by rw [specNorm_transpose]; exact hV₀s
  have hDs : specNorm (D - 1) ≤ 1 / 2 := by
    rw [hD1]
    calc specNorm (V₀ᵀ * (R - 1) * V₀) ≤ specNorm V₀ᵀ * specNorm (R - 1) * specNorm V₀ :=
          (specNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
      _ ≤ 1 * (1 / 2) * 1 :=
          mul_le_mul (mul_le_mul hV₀ts hR (specNorm_nonneg _) zero_le_one) hV₀s
            (specNorm_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hbelow : ∀ v : EuclideanSpace ℝ r, (1 / 2 : ℝ) * ‖v‖ ≤ ‖Matrix.toEuclideanLin D v‖ := by
    intro v
    have h1 : v = Matrix.toEuclideanLin D v - Matrix.toEuclideanLin (D - 1) v := by
      rw [map_sub, LinearMap.sub_apply, Matrix.toLpLin_one, LinearMap.id_apply, sub_sub_cancel]
    have h2 := norm_toEuclideanLin_le (D - 1) v
    have h3 : ‖v‖ ≤ ‖Matrix.toEuclideanLin D v‖ + ‖Matrix.toEuclideanLin (D - 1) v‖ := by
      conv_lhs => rw [h1]
      exact norm_sub_le _ _
    nlinarith [norm_nonneg v]
  have hdet := isUnit_det_of_bounded_below (by norm_num : (0 : ℝ) < 1 / 2) hbelow
  have hDinv : specNorm D⁻¹ ≤ 2 := by
    have := specNorm_inv_le (by norm_num : (0 : ℝ) < 1 / 2) hbelow
    norm_num at this
    exact this
  have hRs : specNorm R ≤ 3 / 2 := by
    have h := specNorm_add_le (1 : Matrix n n ℝ) (R - 1)
    rw [add_sub_cancel] at h
    linarith [specNorm_one_le (n := n)]
  refine ⟨D⁻¹ * V₀ᵀ * R, ?_, ?_⟩
  · have e1 : Y₀ * R * V₀ = Y₀ * V₀ * D := by
      conv_lhs => rw [← hY₀]
      simp only [hDdef, Matrix.mul_assoc]
    have e2 : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hdet
    calc L * Y₀ * R = L * (Y₀ * V₀ * V₀ᵀ) * R := by rw [hY₀]
      _ = L * (Y₀ * R * V₀) * (D⁻¹ * V₀ᵀ * R) := by
          rw [e1]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc D D⁻¹, e2, Matrix.one_mul]
      _ = L * Y₀ * R * V₀ * (D⁻¹ * V₀ᵀ * R) := by simp only [Matrix.mul_assoc]
  · calc specNorm (D⁻¹ * V₀ᵀ * R) ≤ specNorm D⁻¹ * specNorm V₀ᵀ * specNorm R :=
          (specNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
      _ ≤ 2 * 1 * (3 / 2) :=
          mul_le_mul (mul_le_mul hDinv hV₀ts (specNorm_nonneg _) (by norm_num)) hRs
            (specNorm_nonneg _) (by norm_num)
      _ = 3 := by norm_num

/-- The conclusion of Lemma A.3 of arXiv 2608.17157 at one time `s`, used as a hypothesis: a
comparison point `Ỹ(s) = L Y₀ R` with `‖R - I‖₂ ≤ 1/2` (the paper: `‖R(s) - I‖₂ ≤ e^{K_G s} - 1
≤ 1/2` for `s ≤ h*`) within `η` of the exact value `A(s)` (the paper:
`η = √(mn) ε_r s e^{L_F s}`, Eq. (4.7)). -/
def HasComparisonCurve (Y₀ As : Matrix m n ℝ) (η : ℝ) : Prop :=
  ∃ (L : Matrix m m ℝ) (R : Matrix n n ℝ), specNorm (R - 1) ≤ 1 / 2 ∧ ‖L * Y₀ * R - As‖ ≤ η

/-- **Theorem 4.3 (one-step error)** of arXiv 2608.17157.  Let `V₀` be orthonormal with
`Y₀ = Y₀ V₀ V₀ᵀ` (e.g. `Y₀ = U₀ S₀ V₀ᵀ`, `mul_mul_transpose_of_factored`), let `Y₁` be the
reduced K–L step from `V₀` with `X = Y₀ + ΔA`, and let a comparison point of Lemma 4.2 exist
within `η` of `A(s)` (`HasComparisonCurve`; the paper's Lemma 4.2 gives
`η = √(mn) ε_r s e^{L_F s}`).  Then `‖Y₁ - A(s)‖ ≤ 4 ‖Y₀ + ΔA - A(s)‖ + 5 η`.
The overlap `‖Q_s‖₂ ≤ 3` is derived (`exists_overlap_of_specNorm_sub_one_le`); only the
differential-inclusion part of Lemma 4.2 (Lemmas A.1–A.3) is assumed. -/
theorem IsKLStep.one_step_error {V₀ : Matrix n r ℝ} {Y₀ X Y₁ As : Matrix m n ℝ} {η : ℝ}
    (hstep : IsKLStep V₀ X Y₁) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀)
    (hcmp : HasComparisonCurve Y₀ As η) : ‖Y₁ - As‖ ≤ 4 * ‖X - As‖ + 5 * η := by
  obtain ⟨L, R, hR, hη⟩ := hcmp
  obtain ⟨Q, hQ, hQs⟩ := exists_overlap_of_specNorm_sub_one_le hV₀ hY₀ L hR
  set Ys := L * Y₀ * R
  have h1 := hstep.relaxed_exactness hV₀ hQ
  have h2 : ‖X - Ys‖ ≤ ‖X - As‖ + η := by
    calc ‖X - Ys‖ ≤ ‖X - As‖ + ‖As - Ys‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖X - As‖ + η := by gcongr; rwa [norm_sub_rev]
  have h3 : ‖Y₁ - Ys‖ ≤ 4 * (‖X - As‖ + η) :=
    h1.trans (mul_le_mul (by linarith) h2 (norm_nonneg _) (by norm_num))
  calc ‖Y₁ - As‖ ≤ ‖Y₁ - Ys‖ + ‖Ys - As‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 * (‖X - As‖ + η) + η := add_le_add h3 hη
    _ = 4 * ‖X - As‖ + 5 * η := by ring

end Comparison

/-! ### Global error via the increment error (Theorem 5.1) -/

section Global

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- **Theorem 5.1 (global error via the increment error)** of arXiv 2608.17157, on real `m × n`
matrices with the Frobenius norm.  Step `j` (`t_j = t₀ + j h`) applies the reduced K–L step from
the right basis `V j` of `Y j` (orthonormal, `Y j = Y j V j V jᵀ`) to `Y j + ΔA j`;
`Φ j` is the exact flow from `Y j` on `[t_j, t_{j+1}]`, `A` the exact solution.  Assume the
comparison point of Lemma 4.2 at `s = h` (`HasComparisonCurve`, within `h η`; the paper's
Lemma 4.2 gives `η = √(mn) ε_r e^{L_F h}`) and the increment error
`‖Y j + ΔA j - Φ j(t_{j+1})‖ ≤ d` (the paper's `d_h`).  Then for `j h ≤ T`
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T (4 d / h + 5 η))`,
an explicit form of `C_T (δ + ε_r + d_h / h)`. -/
theorem klStep_global_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L d η t₀ h T : ℝ} {N : ℕ}
    {A : ℝ → Matrix m n ℝ} {Y ΔA : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n r ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 < h) (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j)
    (hV : ∀ j < N, (V j)ᵀ * V j = 1) (hYV : ∀ j < N, Y j * V j * (V j)ᵀ = Y j)
    (hstep : ∀ j < N, IsKLStep (V j) (Y j + ΔA j) (Y (j + 1)))
    (hcmp : ∀ j < N, HasComparisonCurve (Y j) (Φ j (t₀ + (j + 1) * h)) (h * η))
    (hinc : ∀ j < N, ‖Y j + ΔA j - Φ j (t₀ + (j + 1) * h)‖ ≤ d) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (4 * d / h + 5 * η)) := by
  refine lady_windermere_of_le hF hL hh.le hA hΦ hΦ₀ (by positivity) (fun j hj => ?_)
  have h1 := (hstep j hj).one_step_error (hV j hj) (hYV j hj) (hcmp j hj)
  calc _ ≤ 4 * ‖Y j + ΔA j - Φ j (t₀ + (j + 1) * h)‖ + 5 * (h * η) := h1
    _ ≤ 4 * d + 5 * (h * η) := by gcongr; exact hinc j hj
    _ = h * (4 * d / h + 5 * η) := by field_simp

/-- **Theorem 5.1, second part** (Eq. (5.3)) of arXiv 2608.17157: if the increment error is
`d ≤ C_inc (h^{p+1} + h ε)`, the global error is
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T (4 C_inc (h^p + ε) + 5 η))`, i.e. order `p`
(here `η = √(mn) ε_r e^{L_F h}` and `ε = ε_r` in the paper). -/
theorem klStep_global_error_of_order {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L d η ε Cinc t₀ h T : ℝ} {p N : ℕ}
    {A : ℝ → Matrix m n ℝ} {Y ΔA : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n r ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 < h) (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j)
    (hV : ∀ j < N, (V j)ᵀ * V j = 1) (hYV : ∀ j < N, Y j * V j * (V j)ᵀ = Y j)
    (hstep : ∀ j < N, IsKLStep (V j) (Y j + ΔA j) (Y (j + 1)))
    (hcmp : ∀ j < N, HasComparisonCurve (Y j) (Φ j (t₀ + (j + 1) * h)) (h * η))
    (hinc : ∀ j < N, ‖Y j + ΔA j - Φ j (t₀ + (j + 1) * h)‖ ≤ d)
    (hdC : d ≤ Cinc * (h ^ (p + 1) + h * ε)) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤
        Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (4 * (Cinc * (h ^ p + ε)) + 5 * η)) := by
  intro j hj hT
  have h1 := klStep_global_error hF hL hh hd hη hA hΦ hΦ₀ hV hYV hstep hcmp hinc j hj hT
  have hT0 : 0 ≤ T := le_trans (mul_nonneg (Nat.cast_nonneg j) hh.le) hT
  have h2 : d / h ≤ Cinc * (h ^ p + ε) := by
    rw [div_le_iff₀ hh]
    calc d ≤ Cinc * (h ^ (p + 1) + h * ε) := hdC
      _ = Cinc * (h ^ p + ε) * h := by ring
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have : 4 * d / h ≤ 4 * (Cinc * (h ^ p + ε)) := by
    rw [mul_div_assoc]; linarith
  nlinarith

end Global

/-! ### Taylor and quadrature estimates (Section 6) -/

section Quadrature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Taylor's theorem with the sharp Lagrange-type constant** for vector-valued functions
(auxiliary for arXiv 2608.17157, proof of Thm 6.1):
if `f` is `C^{n+1}` on `[a, b]` with `‖f^{(n+1)}‖ ≤ C`, then
`‖f x - T_n f(a; x)‖ ≤ C (x - a)^{n+1} / (n+1)!` on `[a, b]`.  (Mathlib's
`taylor_mean_remainder_bound` has `n!` in place of `(n+1)!`.) -/
theorem norm_sub_taylorWithinEval_le {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / (n + 1)! := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Set.Icc_self, mem_singleton_iff] at hx
    simp [hx]
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_succ_self) (uniqueDiffOn_Icc h)
  have hD : ∀ t ∈ Icc a b, HasDerivWithinAt
      (fun y => taylorWithinEval f n (Icc a b) y x - taylorWithinEval f n (Icc a b) a x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t :=
    fun t ht => (hasDerivWithinAt_taylorWithinEval_at_Icc x h ht hf.of_succ hf').sub_const _
  have hfac : ((n + 1)! : ℝ) = (n + 1) * n ! := by push_cast [Nat.factorial_succ]; ring
  have hn0 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := a) (b := x)
    (f := fun y => taylorWithinEval f n (Icc a b) y x - taylorWithinEval f n (Icc a b) a x)
    (f' := fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t)
    (B := fun y => C * ((x - a) ^ (n + 1) - (x - y) ^ (n + 1)) / (n + 1)!)
    (B' := fun y => C * (x - y) ^ n / n !)
    (fun t ht => (hD t ⟨ht.1, ht.2.trans hx.2⟩).continuousWithinAt.mono
      (Icc_subset_Icc_right hx.2))
    (fun t ht => (hD t ⟨ht.1, ht.2.le.trans hx.2⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le hx.2⟩))
    (by simp)
    (fun t => by
      have h1 : HasDerivAt (fun y => (x - y) ^ (n + 1)) (-((n + 1) * (x - t) ^ n)) t := by
        simpa using ((hasDerivAt_id t).const_sub x).fun_pow (n + 1)
      convert ((h1.const_sub ((x - a) ^ (n + 1))).const_mul C).div_const ((n + 1)! : ℝ) using 1
      rw [hfac]
      field_simp)
    (fun t ht => by
      have hxt : 0 ≤ x - t := sub_nonneg.2 ht.2.le
      have h0 : 0 ≤ (n ! : ℝ)⁻¹ * (x - t) ^ n := by positivity
      calc ‖((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t‖
          = (n ! : ℝ)⁻¹ * (x - t) ^ n * ‖iteratedDerivWithin (n + 1) f (Icc a b) t‖ := by
            rw [norm_smul, Real.norm_of_nonneg h0]
        _ ≤ (n ! : ℝ)⁻¹ * (x - t) ^ n * C :=
            mul_le_mul_of_nonneg_left (hC t ⟨ht.1, ht.2.le.trans hx.2⟩) h0
        _ = C * (x - t) ^ n / n ! := by ring)
    (right_mem_Icc.2 hx.1)
  simp only [taylorWithinEval_self, sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, sub_zero] at key
  exact key.trans_eq (by ring)

/-- **Quadrature error of a Runge–Kutta weight vector** (arXiv 2608.17157, proof of Thm 6.1).
Let `y' = g` on `[a, b]` (right derivatives), `g ∈ C^{q+1}([a, b])` with `‖g^{(q+1)}‖ ≤ M`, and
let the weights `w` and nodes `c ∈ [0, 1]` satisfy the moment conditions
`∑ wᵢ cᵢ^k = 1/(k+1)` for `k ≤ q`.  Then for `0 ≤ H ≤ b - a`
`‖H ∑ wᵢ g(a + cᵢ H) - (y(a + H) - y(a))‖ ≤ M/(q+1)! (1/(q+2) + ∑ |wᵢ| cᵢ^{q+1}) H^{q+2}`,
the constant of the paper with `p = q + 1`. -/
theorem norm_quadrature_sub_le {s q : ℕ} {g y : ℝ → E} {a b H M : ℝ} (w c : Fin s → ℝ)
    (hab : a ≤ b) (hH : 0 ≤ H) (hHb : a + H ≤ b)
    (hg : ContDiffOn ℝ (q + 1) g (Icc a b))
    (hM : ∀ τ ∈ Icc a b, ‖iteratedDerivWithin (q + 1) g (Icc a b) τ‖ ≤ M)
    (hyc : ContinuousOn y (Icc a b))
    (hy : ∀ τ ∈ Ico a b, HasDerivWithinAt y (g τ) (Ici τ) τ)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1)
    (hord : ∀ k ≤ q, ∑ i, w i * c i ^ k = 1 / (k + 1)) :
    ‖H • ∑ i, w i • g (a + c i * H) - (y (a + H) - y a)‖ ≤
      M / (q + 1)! * (1 / (q + 2) + ∑ i, |w i| * c i ^ (q + 1)) * H ^ (q + 2) := by
  have hfac : ∀ k : ℕ, ((k + 1)! : ℝ) = (k + 1) * k ! := fun k => by
    push_cast [Nat.factorial_succ]; ring
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  set D : ℕ → E := fun k => iteratedDerivWithin k g (Icc a b) a with hD
  set T : ℝ → E := fun τ => ∑ k ∈ range (q + 1), ((k ! : ℝ)⁻¹ * (τ - a) ^ k) • D k with hT
  set P : ℝ → E := fun τ => ∑ k ∈ range (q + 1), (((k + 1)! : ℝ)⁻¹ * (τ - a) ^ (k + 1)) • D k
    with hP
  have hrem : ∀ τ ∈ Icc a b, ‖g τ - T τ‖ ≤ M * (τ - a) ^ (q + 1) / (q + 1)! := fun τ hτ => by
    have h := norm_sub_taylorWithinEval_le hab hg hτ hM
    rwa [taylor_within_apply] at h
  -- exactness on the Taylor polynomial
  have hexact : H • ∑ i, w i • T (a + c i * H) = P (a + H) - P a := by
    have hPa : P a = 0 := by simp [hP]
    rw [hPa, sub_zero]
    simp only [hT, hP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.sum_smul]
    congr 1
    have hk' : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : ∑ i, H * (w i * ((k ! : ℝ)⁻¹ * (a + c i * H - a) ^ k)) =
        (k ! : ℝ)⁻¹ * H ^ (k + 1) * ∑ i, w i * c i ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hord k hk', hfac k, add_sub_cancel_left]
    field_simp
  have hdecomp : H • ∑ i, w i • g (a + c i * H) - (y (a + H) - y a) =
      H • ∑ i, w i • (g (a + c i * H) - T (a + c i * H)) -
        ((y (a + H) - P (a + H)) - (y a - P a)) := by
    have h1 : H • ∑ i, w i • g (a + c i * H) =
        H • ∑ i, w i • (g (a + c i * H) - T (a + c i * H)) + H • ∑ i, w i • T (a + c i * H) := by
      rw [← smul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← smul_add, sub_add_cancel]
    rw [h1, hexact]
    abel
  -- the stage (node) term
  have hnode : ∀ i, a + c i * H ∈ Icc a b := fun i => by
    have h1 : 0 ≤ c i * H := mul_nonneg (hc i).1 hH
    have h2 : c i * H ≤ H := by nlinarith [(hc i).2]
    constructor <;> linarith
  have hterm1 : ‖H • ∑ i, w i • (g (a + c i * H) - T (a + c i * H))‖ ≤
      M / (q + 1)! * (∑ i, |w i| * c i ^ (q + 1)) * H ^ (q + 2) := by
    rw [norm_smul, Real.norm_of_nonneg hH]
    calc H * ‖∑ i, w i • (g (a + c i * H) - T (a + c i * H))‖
        ≤ H * ∑ i, |w i| * (M * (a + c i * H - a) ^ (q + 1) / (q + 1)!) := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun i _ => ?_)) hH
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hrem _ (hnode i)) (abs_nonneg _)
      _ = M / (q + 1)! * (∑ i, |w i| * c i ^ (q + 1)) * H ^ (q + 2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
  -- the integral term, by comparison with `M (τ - a)^{q+2} / (q+2)!`
  have hPd : ∀ τ, HasDerivAt P (T τ) τ := by
    intro τ
    refine HasDerivAt.fun_sum (A := fun k τ => (((k + 1)! : ℝ)⁻¹ * (τ - a) ^ (k + 1)) • D k)
      fun k _ => ?_
    have h1 : HasDerivAt (fun x => (x - a) ^ (k + 1)) ((k + 1) * (τ - a) ^ k) τ := by
      simpa using ((hasDerivAt_id τ).sub_const a).fun_pow (k + 1)
    convert (h1.const_mul (((k + 1)! : ℝ)⁻¹)).smul_const (D k) using 2
    rw [hfac k]
    field_simp
  have hsub : Icc a (a + H) ⊆ Icc a b := Icc_subset_Icc_right hHb
  have hterm2 := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := a) (b := a + H)
    (f := fun τ => (y τ - P τ) - (y a - P a)) (f' := fun τ => g τ - T τ)
    (B := fun τ => M * (τ - a) ^ (q + 2) / (q + 2)!)
    (B' := fun τ => M * (τ - a) ^ (q + 1) / (q + 1)!)
    (((hyc.mono hsub).sub (fun τ _ => (hPd τ).continuousAt.continuousWithinAt)).sub
      continuousOn_const)
    (fun τ hτ => ((hy τ ⟨hτ.1, hτ.2.trans_le hHb⟩).sub (hPd τ).hasDerivWithinAt).sub_const _)
    (by simp)
    (fun τ => by
      have h1 : HasDerivAt (fun x => (x - a) ^ (q + 2)) ((q + 2) * (τ - a) ^ (q + 1)) τ := by
        simpa using ((hasDerivAt_id τ).sub_const a).fun_pow (q + 2)
      convert (h1.const_mul M).div_const (((q + 2)! : ℝ)) using 1
      rw [show q + 2 = (q + 1) + 1 from rfl, hfac (q + 1)]
      push_cast
      field_simp
      ring)
    (fun τ hτ => hrem τ (hsub (Ico_subset_Icc_self hτ)))
    (right_mem_Icc.2 (by linarith))
  simp only [add_sub_cancel_left] at hterm2
  rw [hdecomp]
  refine (norm_sub_le _ _).trans ?_
  have hfac2 : ((q + 2)! : ℝ) = (q + 2) * (q + 1)! := by
    rw [show q + 2 = (q + 1) + 1 from rfl, hfac (q + 1)]; push_cast; ring
  calc _ ≤ M / (q + 1)! * (∑ i, |w i| * c i ^ (q + 1)) * H ^ (q + 2) +
        M * H ^ (q + 2) / (q + 2)! := add_le_add hterm1 hterm2
    _ = _ := by
        rw [hfac2]
        field_simp
        ring

/-- **Increment error of a Runge–Kutta increment** (arXiv 2608.17157, proof of Thm 6.1).  Let
`A` solve `A' = F(t, A)` on `[t, t + h]` with `F` `L`-Lipschitz, let `g(τ) = F(τ, A(τ))` be
`C^{q+1}` with `‖g^{(q+1)}‖ ≤ M`, let the weights `b` and nodes `c ∈ [0, 1]` satisfy
`∑ bᵢ cᵢ^k = 1/(k+1)` for `k ≤ q`, and let the stages satisfy `‖Zᵢ - A(t + cᵢ h)‖ ≤ eᵢ` whenever
`bᵢ ≠ 0`.  Then the increment `ΔA = h ∑ bᵢ F(t + cᵢ h, Zᵢ)` satisfies
`‖A(t) + ΔA - A(t + h)‖ ≤ M/(q+1)! (1/(q+2) + ∑ |bᵢ| cᵢ^{q+1}) h^{q+2} + h L ∑ |bᵢ| eᵢ`
(quadrature term plus stage term, as in the paper). -/
theorem rk_increment_error_le {s q : ℕ} {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (b c : Fin s → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1)
    (hord : ∀ k ≤ q, ∑ i, b i * c i ^ k = 1 / (k + 1)) {t h M : ℝ} (hh : 0 ≤ h) {A : ℝ → E}
    (hA : ODESolution F A t (t + h))
    (hg : ContDiffOn ℝ (q + 1) (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin (q + 1) (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M)
    {Z : Fin s → E} {e : Fin s → ℝ} (hZ : ∀ i, b i ≠ 0 → ‖Z i - A (t + c i * h)‖ ≤ e i) :
    ‖A t + h • ∑ i, b i • F (t + c i * h) (Z i) - A (t + h)‖ ≤
      M / (q + 1)! * (1 / (q + 2) + ∑ i, |b i| * c i ^ (q + 1)) * h ^ (q + 2) +
        h * L * ∑ i, |b i| * e i := by
  have hquad := norm_quadrature_sub_le (y := A) (g := fun τ => F τ (A τ)) b c
    (le_add_of_nonneg_right hh) hh le_rfl hg hM hA.cont (fun τ hτ => hA.deriv τ hτ) hc hord
  have hsplit : A t + h • ∑ i, b i • F (t + c i * h) (Z i) - A (t + h) =
      (h • ∑ i, b i • F (t + c i * h) (A (t + c i * h)) - (A (t + h) - A t)) +
        h • ∑ i, b i • (F (t + c i * h) (Z i) - F (t + c i * h) (A (t + c i * h))) := by
    have : ∑ i, b i • F (t + c i * h) (Z i) = ∑ i, b i • F (t + c i * h) (A (t + c i * h)) +
        ∑ i, b i • (F (t + c i * h) (Z i) - F (t + c i * h) (A (t + c i * h))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← smul_add, add_sub_cancel]
    rw [this, smul_add]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add hquad ?_)
  rw [norm_smul, Real.norm_of_nonneg hh, mul_assoc, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)) hh
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hb : b i = 0
  · simp [hb]
  calc |b i| * ‖F (t + c i * h) (Z i) - F (t + c i * h) (A (t + c i * h))‖
      ≤ |b i| * (L * ‖Z i - A (t + c i * h)‖) :=
        mul_le_mul_of_nonneg_left (hF _ _ _) (abs_nonneg _)
    _ ≤ |b i| * (L * e i) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hZ i hb) hL) (abs_nonneg _)
    _ = L * (|b i| * e i) := by ring

/-- The constant of Theorem 6.1 of arXiv 2608.17157:
`C = M_p/p! (1/(p+1) + ∑ |bᵢ| cᵢ^p) + L C_st ∑ |bᵢ|` (quadrature and stage contributions). -/
noncomputable def rkConst {s : ℕ} (p : ℕ) (b c : Fin s → ℝ) (L M Cst : ℝ) : ℝ :=
  M / p ! * (1 / (p + 1) + ∑ i, |b i| * c i ^ p) + L * Cst * ∑ i, |b i|

/-- **Theorem 6.1, increment error** (arXiv 2608.17157).  For an explicit tableau with nodes
`cᵢ ∈ [0, 1]` and the moment conditions `∑ bᵢ cᵢ^k = 1/(k+1)` for `k < p` (`p ≥ 1`), an
`L`-Lipschitz field `F`, `g(τ) = F(τ, A(τ))` of class `C^p` on `[t, t + h]` with
`‖g^{(p)}‖ ≤ M_p`, and stage bounds `‖Zᵢ - A(t + cᵢ h)‖ ≤ C_st (h^p + h ε)` for `bᵢ ≠ 0`, the
increment error is `‖A(t) + h ∑ bᵢ F(t + cᵢ h, Zᵢ) - A(t + h)‖ ≤ C (h^{p+1} + h² ε)` with the
explicit `C = rkConst p b c L M_p C_st`.  Stated on any real normed space. -/
theorem rk_increment_error {s p : ℕ} (hp : 0 < p) {F : ℝ → E → E} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (b c : Fin s → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1)
    (hord : ∀ k < p, ∑ i, b i * c i ^ k = 1 / (k + 1)) {t h M Cst ε : ℝ} (hh : 0 ≤ h)
    (hε : 0 ≤ ε) {A : ℝ → E} (hA : ODESolution F A t (t + h))
    (hg : ContDiffOn ℝ p (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin p (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M)
    {Z : Fin s → E} (hZ : ∀ i, b i ≠ 0 → ‖Z i - A (t + c i * h)‖ ≤ Cst * (h ^ p + h * ε)) :
    ‖A t + h • ∑ i, b i • F (t + c i * h) (Z i) - A (t + h)‖ ≤
      rkConst p b c L M Cst * (h ^ (p + 1) + h ^ 2 * ε) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hg' : ContDiffOn ℝ (q + 1) (fun τ => F τ (A τ)) (Icc t (t + h)) := by exact_mod_cast hg
  have h1 := rk_increment_error_le hF hL b c hc (fun k hk => hord k (by omega)) hh hA hg' hM
    (e := fun _ => Cst * (h ^ (q + 1) + h * ε)) hZ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t ⟨le_rfl, le_add_of_nonneg_right hh⟩)
  have hK : 0 ≤ M / (q + 1)! * (1 / (q + 2) + ∑ i, |b i| * c i ^ (q + 1)) := by
    have : 0 ≤ ∑ i, |b i| * c i ^ (q + 1) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (pow_nonneg (hc i).1 _)
    positivity
  have h2 : ∑ i, |b i| * (Cst * (h ^ (q + 1) + h * ε)) =
      (∑ i, |b i|) * (Cst * (h ^ (q + 1) + h * ε)) := by rw [Finset.sum_mul]
  rw [h2] at h1
  refine h1.trans ?_
  unfold rkConst
  push_cast
  have h3 : (1 : ℝ) / (q + 2) = 1 / (q + 1 + 1) := by ring
  rw [h3] at hK ⊢
  have h4 : 0 ≤ h ^ 2 * ε := by positivity
  set K := M / ((q + 1)! : ℝ) * (1 / (q + 1 + 1) + ∑ i, |b i| * c i ^ (q + 1))
  set S := ∑ i, |b i|
  calc K * h ^ (q + 2) + h * L * (S * (Cst * (h ^ (q + 1) + h * ε)))
      = K * h ^ (q + 2) + L * Cst * S * (h ^ (q + 2) + h ^ 2 * ε) := by ring
    _ ≤ (K + L * Cst * S) * (h ^ (q + 1 + 1) + h ^ 2 * ε) := by
        rw [show q + 1 + 1 = q + 2 from rfl]
        nlinarith [mul_nonneg hK h4]

end Quadrature

/-! ### Runge–Kutta increments with reduced K–L stages (Section 6) -/

section RK

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- **Algorithm 6.1** of arXiv 2608.17157 (one step, relational form): explicit tableau
`(a, b, c)`; stage `i` is the reduced K–L step from `V₀` with the stage increment
`ΔA_i = h ∑_{j<i} aᵢⱼ F(t + cⱼ h, Zⱼ)` (so `Z₁ = Y₀` when `Y₀ = Y₀ V₀ V₀ᵀ`,
`IsKLStep.eq_of_zero`), and the result is the reduced K–L step with
`ΔA = h ∑ bᵢ F(t + cᵢ h, Zᵢ)`. -/
def IsRKKLStep {s : ℕ} (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (a : Fin s → Fin s → ℝ)
    (b c : Fin s → ℝ) (V₀ : Matrix n r ℝ) (t h : ℝ) (Y₀ : Matrix m n ℝ)
    (Z : Fin s → Matrix m n ℝ) (Y₁ : Matrix m n ℝ) : Prop :=
  (∀ i, IsKLStep V₀ (Y₀ + h • ∑ j ∈ Finset.univ.filter (· < i), a i j • F (t + c j * h) (Z j))
      (Z i)) ∧
    IsKLStep V₀ (Y₀ + h • ∑ i, b i • F (t + c i * h) (Z i)) Y₁

omit [DecidableEq n] in
/-- A reduced K–L step with zero increment returns `Y₀` when `Y₀ = Y₀ V₀ V₀ᵀ`: the first stage
of Algorithm 6.1 of arXiv 2608.17157 is `Y_{n,1} = Y_n`, as in the paper. -/
theorem IsKLStep.eq_of_zero {V₀ : Matrix n r ℝ} {Y₀ Z : Matrix m n ℝ} (hstep : IsKLStep V₀ Y₀ Z)
    (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) : Z = Y₀ := by
  obtain ⟨U₁, Ŝ₁, hU₁, hK, rfl⟩ := hstep
  conv_lhs => rw [← hY₀, ← hK]
  have h := leftProj_mul_left (n := n) hU₁ (Ŝ₁ * V₀ᵀ)
  rw [leftProj_apply] at h
  rw [Matrix.mul_assoc U₁ Ŝ₁, h, ← Matrix.mul_assoc, hK, hY₀]

/-- **Theorem 6.1, one-step error** (arXiv 2608.17157).  Under the hypotheses of
`rk_increment_error` (with `A` the exact flow from `A(t) = Y₀`), a comparison point of Lemma 4.2
at `s = h` within `h η` (`η = √(mn) ε_r e^{L_F h}` in the paper), `V₀` orthonormal and
`Y₀ = Y₀ V₀ V₀ᵀ`, one step of Algorithm 6.1 satisfies
`‖Y₁ - A(t + h)‖ ≤ 4 C (h^{p+1} + h² ε) + 5 h η`, i.e. `O(h^{p+1} + h ε_r)`. -/
theorem IsRKKLStep.one_step_error {s p : ℕ} (hp : 0 < p) {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (hord : ∀ k < p, ∑ i, b i * c i ^ k = 1 / (k + 1))
    {t h M Cst ε η : ℝ} (hh : 0 ≤ h) (hε : 0 ≤ ε) {V₀ : Matrix n r ℝ}
    {Y₀ Y₁ : Matrix m n ℝ} {Z : Fin s → Matrix m n ℝ} (hstep : IsRKKLStep F a b c V₀ t h Y₀ Z Y₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t (t + h)) (hA₀ : A t = Y₀)
    (hg : ContDiffOn ℝ p (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin p (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M)
    (hZ : ∀ i, b i ≠ 0 → ‖Z i - A (t + c i * h)‖ ≤ Cst * (h ^ p + h * ε))
    (hcmp : HasComparisonCurve Y₀ (A (t + h)) (h * η)) :
    ‖Y₁ - A (t + h)‖ ≤ 4 * (rkConst p b c L M Cst * (h ^ (p + 1) + h ^ 2 * ε)) + 5 * (h * η) := by
  have h1 := hstep.2.one_step_error hV₀ hY₀ hcmp
  have h2 := rk_increment_error hp hF hL b c hc hord hh hε hA hg hM hZ
  rw [hA₀] at h2
  linarith

/-- **Theorem 6.1, global error** (arXiv 2608.17157): if every step of Algorithm 6.1 satisfies
the hypotheses of `IsRKKLStep.one_step_error` with the same constants (`Φ j` the exact flow from
`Y j` on `[t_j, t_{j+1}]`, `g_j(τ) = F(τ, Φ j τ)`), then for `j h ≤ T`
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T (4 C (h^p + h ε) + 5 η))`,
i.e. `C_T (δ + ε_r + h^p)` (with `η = √(mn) ε_r e^{L_F h}`). -/
theorem rkKL_global_error {s p : ℕ} (hp : 0 < p) {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (hord : ∀ k < p, ∑ i, b i * c i ^ k = 1 / (k + 1))
    {t₀ h M Cst ε η T : ℝ} {N : ℕ} (hh : 0 < h) (hM0 : 0 ≤ M) (hCst : 0 ≤ Cst) (hε : 0 ≤ ε)
    (hη : 0 ≤ η)
    {A : ℝ → Matrix m n ℝ} {Y : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n r ℝ}
    {Z : ℕ → Fin s → Matrix m n ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j)
    (hV : ∀ j < N, (V j)ᵀ * V j = 1) (hYV : ∀ j < N, Y j * V j * (V j)ᵀ = Y j)
    (hstep : ∀ j < N, IsRKKLStep F a b c (V j) (t₀ + j * h) h (Y j) (Z j) (Y (j + 1)))
    (hg : ∀ j < N, ContDiffOn ℝ p (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)))
    (hM : ∀ j < N, ∀ τ ∈ Icc (t₀ + j * h) (t₀ + j * h + h),
      ‖iteratedDerivWithin p (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)) τ‖ ≤ M)
    (hZ : ∀ j < N, ∀ i, b i ≠ 0 →
      ‖Z j i - Φ j (t₀ + j * h + c i * h)‖ ≤ Cst * (h ^ p + h * ε))
    (hcmp : ∀ j < N, HasComparisonCurve (Y j) (Φ j (t₀ + j * h + h)) (h * η)) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) *
        (‖Y 0 - A t₀‖ + T * (4 * (rkConst p b c L M Cst * (h ^ p + h * ε)) + 5 * η)) := by
  have hK : 0 ≤ rkConst p b c L M Cst := by
    unfold rkConst
    have h1 : 0 ≤ ∑ i, |b i| * c i ^ p :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (pow_nonneg (hc i).1 _)
    have h2 : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    positivity
  refine lady_windermere_of_le hF hL hh.le hA hΦ hΦ₀ (by positivity) (fun j hj => ?_)
  have e : t₀ + (j + 1) * h = t₀ + j * h + h := by ring
  rw [e]
  have hΦj := hΦ j hj
  rw [e] at hΦj
  have h1 := (hstep j hj).one_step_error hp hF hL a b c hc hord hh.le hε (hV j hj) (hYV j hj)
    hΦj (hΦ₀ j hj) (hg j hj) (hM j hj) (hZ j hj) (hcmp j hj)
  refine h1.trans_eq ?_
  ring

/-- Taylor/Theorem 4.3 bound for a first stage `Z = KL(Y₀ + σ F(t, Y₀))` at `σ ∈ [0, h]`:
`‖Z - A(t + σ)‖ ≤ 2 M₁ σ² + 5 σ η` (the midpoint and Heun stage bounds of arXiv 2608.17157,
Section 6, with `‖Y₀ + σ g(t) - A(t + σ)‖ ≤ M₁ σ²/2`). -/
theorem first_stage_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t h σ M₁ η : ℝ}
    (hσ : 0 ≤ σ) (hσh : σ ≤ h) {V₀ : Matrix n r ℝ} {Y₀ Z : Matrix m n ℝ}
    (hstep : IsKLStep V₀ (Y₀ + σ • F t Y₀) Z) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t (t + h)) (hA₀ : A t = Y₀)
    (hg : ContDiffOn ℝ 1 (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM₁ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 1 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₁)
    (hcmp : HasComparisonCurve Y₀ (A (t + σ)) (σ * η)) :
    ‖Z - A (t + σ)‖ ≤ 2 * M₁ * σ ^ 2 + 5 * σ * η := by
  have hq := norm_quadrature_sub_le (q := 0) (y := A) (g := fun τ => F τ (A τ)) (H := σ)
    ![1] ![0] (by linarith) hσ (by linarith) (by simpa using hg) (by simpa using hM₁) hA.cont
    (fun τ hτ => hA.deriv τ hτ) (fun i => by fin_cases i; simp) (fun k hk => by
      obtain rfl : k = 0 := by omega
      simp)
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
    zero_mul, add_zero, one_smul, Finset.sum_singleton, zero_add, abs_one, one_mul,
    CharP.cast_eq_zero] at hq
  rw [hA₀] at hq
  have h1 := hstep.one_step_error hV₀ hY₀ hcmp
  have h2 : Y₀ + σ • F t Y₀ - A (t + σ) = σ • F t Y₀ - (A (t + σ) - Y₀) := by abel
  rw [h2] at h1
  nlinarith

/-- **Two-stage RK-K–L step** (arXiv 2608.17157, midpoint method and Remark 6.3): with
`a₂₁ = c₂ = α` and `b₂ = 1/(2α)`, `b₁ = 1 - b₂` (so `a₂₁ b₂ = 1/2`, `b₁ + b₂ = 1`), the stage is
`Z = KL(Y₀ + α h F(t, Y₀))` and the result `Y₁ = KL(Y₀ + h (b₁ F(t, Y₀) + b₂ F(t + α h, Z)))`,
all K–L steps from the same `V₀`.  `α = 1/2` is the midpoint method, `α = 1` Heun's RK2. -/
def IsRK2KLStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (α : ℝ) (V₀ : Matrix n r ℝ) (t h : ℝ)
    (Y₀ Z Y₁ : Matrix m n ℝ) : Prop :=
  IsKLStep V₀ (Y₀ + (α * h) • F t Y₀) Z ∧
    IsKLStep V₀ (Y₀ + h • ((1 - 1 / (2 * α)) • F t Y₀ + (1 / (2 * α)) • F (t + α * h) Z)) Y₁

/-- **Robust order 2 of the two-stage family, one step** (arXiv 2608.17157, midpoint corollary
of Thm 6.1 and Remark 6.3).  For `0 < α ≤ 1`, `F` `L`-Lipschitz, `g(τ) = F(τ, A(τ))` of class
`C²` on `[t, t + h]` with `‖g'‖ ≤ M₁`, `‖g''‖ ≤ M₂` (Lemma 6.2), and comparison points of
Lemma 4.2 at every `σ ∈ [0, h]` within `σ η`:
`‖Z - A(t + α h)‖ ≤ 2 M₁ α² h² + 5 α h η` (stage bound) and
`‖Y₁ - A(t + h)‖ ≤ 4 (M₂/2 (1/3 + α/2) + L M₁ α) h³ + (10 L h + 5) h η`,
i.e. `O(h³ + h ε_r)` with constants independent of the singular values. -/
theorem IsRK2KLStep.one_step_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L α t h M₁ M₂ η : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1) (hh : 0 ≤ h)
    {V₀ : Matrix n r ℝ} {Y₀ Z Y₁ : Matrix m n ℝ} (hstep : IsRK2KLStep F α V₀ t h Y₀ Z Y₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t (t + h)) (hA₀ : A t = Y₀)
    (hg : ContDiffOn ℝ 2 (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM₁ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 1 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₁)
    (hM₂ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 2 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₂)
    (hcmp : ∀ σ ∈ Icc 0 h, HasComparisonCurve Y₀ (A (t + σ)) (σ * η)) :
    ‖Z - A (t + α * h)‖ ≤ 2 * M₁ * α ^ 2 * h ^ 2 + 5 * α * h * η ∧
      ‖Y₁ - A (t + h)‖ ≤
        4 * (M₂ / 2 * (1 / 3 + α / 2) + L * M₁ * α) * h ^ 3 + (10 * L * h + 5) * h * η := by
  have hαh : 0 ≤ α * h := mul_nonneg hα.le hh
  have hαh' : α * h ≤ h := by nlinarith
  have hstage := first_stage_error hαh hαh' hstep.1 hV₀ hY₀ hA hA₀ (hg.of_le (by norm_num)) hM₁
    (hcmp _ ⟨hαh, hαh'⟩)
  refine ⟨by nlinarith [hstage], ?_⟩
  set e₂ := 2 * M₁ * (α * h) ^ 2 + 5 * (α * h) * η
  have hinc := rk_increment_error_le (q := 1) hF hL ![1 - 1 / (2 * α), 1 / (2 * α)] ![0, α]
    (fun i => by fin_cases i <;> simp [hα.le, hα1]) (fun k hk => by
      interval_cases k
      · simp
      · simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          pow_one, mul_zero, zero_add]
        field_simp
        norm_num)
    hh hA (by convert hg using 1; norm_num) (by simpa using hM₂) (Z := ![Y₀, Z]) (e := ![0, e₂])
    (fun i _ => by
      fin_cases i
      · simp [hA₀]
      · simpa using hstage)
  have hsum : A t + h • ∑ i, ![1 - 1 / (2 * α), 1 / (2 * α)] i •
      F (t + ![0, α] i * h) (![Y₀, Z] i) =
      Y₀ + h • ((1 - 1 / (2 * α)) • F t Y₀ + (1 / (2 * α)) • F (t + α * h) Z) := by
    simp [Fin.sum_univ_two, hA₀]
  rw [hsum] at hinc
  have hb2 : |1 / (2 * α)| = 1 / (2 * α) := abs_of_pos (by positivity)
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, hb2,
    zero_pow two_ne_zero, mul_zero, zero_add, Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat,
    Nat.cast_one] at hinc
  have h1 := hstep.2.one_step_error hV₀ hY₀ (hcmp h ⟨hh, le_rfl⟩)
  have he : h * L * (1 / (2 * α) * e₂) = L * M₁ * α * h ^ 3 + 5 / 2 * L * h ^ 2 * η := by
    simp only [e₂]
    field_simp
  have hq : M₂ / 2 * (1 / (1 + 2) + 1 / (2 * α) * α ^ 2) = M₂ / 2 * (1 / 3 + α / 2) := by
    field_simp
    ring
  rw [he, hq] at hinc
  nlinarith

/-- **Robust order 2 of the two-stage family, global error** (arXiv 2608.17157, Thm 6.1 with
Thm 5.1 for the midpoint method and Remark 6.3): if every step satisfies the hypotheses of
`IsRK2KLStep.one_step_error` with the same constants, then for `j h ≤ T`
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T (4 (M₂/2 (1/3 + α/2) + L M₁ α) h² + (10 L h + 5) η))`,
i.e. `C_T (δ + ε_r + h²)` for `h ≤ 1` (with `η = √(mn) ε_r e^{L_F h}` from Lemma 4.2). -/
theorem rk2KL_global_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L α M₁ M₂ η t₀ h T : ℝ}
    {N : ℕ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1) (hh : 0 < h)
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hη : 0 ≤ η)
    {A : ℝ → Matrix m n ℝ} {Y Z : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n r ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j)
    (hV : ∀ j < N, (V j)ᵀ * V j = 1) (hYV : ∀ j < N, Y j * V j * (V j)ᵀ = Y j)
    (hstep : ∀ j < N, IsRK2KLStep F α (V j) (t₀ + j * h) h (Y j) (Z j) (Y (j + 1)))
    (hg : ∀ j < N, ContDiffOn ℝ 2 (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)))
    (hM₁ : ∀ j < N, ∀ τ ∈ Icc (t₀ + j * h) (t₀ + j * h + h),
      ‖iteratedDerivWithin 1 (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)) τ‖ ≤ M₁)
    (hM₂ : ∀ j < N, ∀ τ ∈ Icc (t₀ + j * h) (t₀ + j * h + h),
      ‖iteratedDerivWithin 2 (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)) τ‖ ≤ M₂)
    (hcmp : ∀ j < N, ∀ σ ∈ Icc 0 h,
      HasComparisonCurve (Y j) (Φ j (t₀ + j * h + σ)) (σ * η)) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ +
        T * (4 * (M₂ / 2 * (1 / 3 + α / 2) + L * M₁ * α) * h ^ 2 + (10 * L * h + 5) * η)) := by
  refine lady_windermere_of_le hF hL hh.le hA hΦ hΦ₀ (by positivity) (fun j hj => ?_)
  have e : t₀ + (j + 1) * h = t₀ + j * h + h := by ring
  rw [e]
  have hΦj := hΦ j hj
  rw [e] at hΦj
  have h1 := ((hstep j hj).one_step_error hF hL hα hα1 hh.le (hV j hj) (hYV j hj) hΦj
    (hΦ₀ j hj) (hg j hj) (hM₁ j hj) (hM₂ j hj) (hcmp j hj)).2
  refine h1.trans_eq ?_
  ring

/-- The **midpoint RK-K–L step** of arXiv 2608.17157 (Section 6): `ΔA_{n,2} = (h/2) F(t, Y₀)`,
`Z = KL(Y₀ + ΔA_{n,2})`, `ΔA_n = h F(t + h/2, Z)`, `Y₁ = KL(Y₀ + ΔA_n)`. -/
def IsMidpointKLStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (V₀ : Matrix n r ℝ) (t h : ℝ)
    (Y₀ Z Y₁ : Matrix m n ℝ) : Prop :=
  IsKLStep V₀ (Y₀ + (h / 2) • F t Y₀) Z ∧ IsKLStep V₀ (Y₀ + h • F (t + h / 2) Z) Y₁

omit [DecidableEq n] in
/-- The midpoint step of arXiv 2608.17157 is the member `α = 1/2` of the two-stage family of
its Remark 6.3. -/
theorem IsMidpointKLStep.isRK2KLStep {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {V₀ : Matrix n r ℝ}
    {t h : ℝ} {Y₀ Z Y₁ : Matrix m n ℝ} (hstep : IsMidpointKLStep F V₀ t h Y₀ Z Y₁) :
    IsRK2KLStep F (1 / 2) V₀ t h Y₀ Z Y₁ := by
  have e1 : (1 / 2 : ℝ) * h = h / 2 := by ring
  refine ⟨by rw [e1]; exact hstep.1, ?_⟩
  have e2 : (1 - 1 / (2 * (1 / 2 : ℝ))) • F t Y₀ + (1 / (2 * (1 / 2 : ℝ))) • F (t + 1 / 2 * h) Z =
      F (t + h / 2) Z := by
    rw [e1]; norm_num
  rw [e2]
  exact hstep.2

/-- **Midpoint method, robust order 2** (arXiv 2608.17157, Section 6, midpoint corollary).  Under
the hypotheses of `IsRK2KLStep.one_step_error`, the midpoint stage satisfies the paper's bound
`‖Z - A(t + h/2)‖ ≤ (M₁/2) h² + (5/2) h η` (`η = √(mn) ε_r e^{L_F h}`), and
`‖Y₁ - A(t + h)‖ ≤ 4 (7/24 M₂ + L M₁/2) h³ + (10 L h + 5) h η`. -/
theorem IsMidpointKLStep.one_step_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L t h M₁ M₂ η : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h)
    {V₀ : Matrix n r ℝ} {Y₀ Z Y₁ : Matrix m n ℝ} (hstep : IsMidpointKLStep F V₀ t h Y₀ Z Y₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t (t + h)) (hA₀ : A t = Y₀)
    (hg : ContDiffOn ℝ 2 (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM₁ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 1 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₁)
    (hM₂ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 2 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₂)
    (hcmp : ∀ σ ∈ Icc 0 h, HasComparisonCurve Y₀ (A (t + σ)) (σ * η)) :
    ‖Z - A (t + h / 2)‖ ≤ M₁ / 2 * h ^ 2 + 5 / 2 * h * η ∧
      ‖Y₁ - A (t + h)‖ ≤ 4 * (7 / 24 * M₂ + L * M₁ / 2) * h ^ 3 + (10 * L * h + 5) * h * η := by
  obtain ⟨h1, h2⟩ := hstep.isRK2KLStep.one_step_error hF hL (by norm_num) (by norm_num) hh hV₀
    hY₀ hA hA₀ hg hM₁ hM₂ hcmp
  have e1 : t + 1 / 2 * h = t + h / 2 := by ring
  rw [e1] at h1
  constructor
  · refine h1.trans_eq ?_
    ring
  · refine h2.trans_eq ?_
    ring

/-- The **Heun RK3 K–L step** of arXiv 2608.17157 (Section 6): `c = (0, 1/3, 2/3)`,
`a₂₁ = 1/3`, `a₃₂ = 2/3`, `b = (1/4, 0, 3/4)`; `Z₂ = KL(Y₀ + (h/3) F(t, Y₀))`,
`Z₃ = KL(Y₀ + (2h/3) F(t + h/3, Z₂))`, `Y₁ = KL(Y₀ + h (F(t, Y₀)/4 + 3 F(t + 2h/3, Z₃)/4))`. -/
def IsHeun3KLStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (V₀ : Matrix n r ℝ) (t h : ℝ)
    (Y₀ Z₂ Z₃ Y₁ : Matrix m n ℝ) : Prop :=
  IsKLStep V₀ (Y₀ + (h / 3) • F t Y₀) Z₂ ∧
    IsKLStep V₀ (Y₀ + (2 * h / 3) • F (t + h / 3) Z₂) Z₃ ∧
    IsKLStep V₀ (Y₀ + h • ((1 / 4 : ℝ) • F t Y₀ + (3 / 4 : ℝ) • F (t + 2 * h / 3) Z₃)) Y₁

/-- **Heun RK3, robust order 3, one step** (arXiv 2608.17157, Section 6, Heun RK3 corollary).
For `F` `L`-Lipschitz, `g(τ) = F(τ, A(τ))` of class `C³` on `[t, t + h]` with `‖g'‖ ≤ M₁`,
`‖g''‖ ≤ M₂`, `‖g'''‖ ≤ M₃` (Lemma 6.2), and comparison points of Lemma 4.2 at every
`σ ∈ [0, h]` within `σ η`, the stages and the result satisfy
`‖Z₂ - A(t + h/3)‖ ≤ 2/9 M₁ h² + 5/3 h η` (Taylor and Thm 4.3 at `h/3`),
`‖Z₃ - A(t + 2h/3)‖ ≤ (28/81 M₂ + 16/27 L M₁) h³ + (40/9 L h + 10/3) h η` (midpoint quadrature
on `[0, 2h/3]`, Lipschitz bound for the stage-2 error and Thm 4.3 at `2h/3`), and
`‖Y₁ - A(t + h)‖ ≤ (17/54 M₃ + 28/27 L M₂ + 16/9 L² M₁) h⁴ + (40/3 L² h² + 10 L h + 5) h η`,
i.e. `O(h⁴ + h ε_r)`. -/
theorem IsHeun3KLStep.one_step_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L t h M₁ M₂ M₃ η : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h)
    {V₀ : Matrix n r ℝ} {Y₀ Z₂ Z₃ Y₁ : Matrix m n ℝ}
    (hstep : IsHeun3KLStep F V₀ t h Y₀ Z₂ Z₃ Y₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t (t + h)) (hA₀ : A t = Y₀)
    (hg : ContDiffOn ℝ 3 (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM₁ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 1 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₁)
    (hM₂ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 2 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₂)
    (hM₃ : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin 3 (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M₃)
    (hcmp : ∀ σ ∈ Icc 0 h, HasComparisonCurve Y₀ (A (t + σ)) (σ * η)) :
    ‖Z₂ - A (t + h / 3)‖ ≤ 2 / 9 * M₁ * h ^ 2 + 5 / 3 * h * η ∧
      ‖Z₃ - A (t + 2 * h / 3)‖ ≤
        (28 / 81 * M₂ + 16 / 27 * L * M₁) * h ^ 3 + (40 / 9 * L * h + 10 / 3) * h * η ∧
      ‖Y₁ - A (t + h)‖ ≤ (17 / 54 * M₃ + 28 / 27 * L * M₂ + 16 / 9 * L ^ 2 * M₁) * h ^ 4 +
        (40 / 3 * L ^ 2 * h ^ 2 + 10 * L * h + 5) * h * η := by
  obtain ⟨hs2, hs3, hs⟩ := hstep
  -- stage 2
  have hst2 := first_stage_error (σ := h / 3) (by positivity) (by linarith) hs2 hV₀ hY₀ hA hA₀
    (hg.of_le (by norm_num)) hM₁ (hcmp _ ⟨by positivity, by linarith⟩)
  have hst2' : ‖Z₂ - A (t + h / 3)‖ ≤ 2 / 9 * M₁ * h ^ 2 + 5 / 3 * h * η := by
    refine hst2.trans_eq ?_
    ring
  refine ⟨hst2', ?_⟩
  -- stage 3: midpoint quadrature on `[t, t + 2h/3]`
  have hq := norm_quadrature_sub_le (q := 1) (y := A) (g := fun τ => F τ (A τ))
    (H := 2 * h / 3) ![1] ![1 / 2] (by linarith) (by positivity) (by linarith)
    (by convert hg.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3) using 1; norm_num)
    (by simpa using hM₂) hA.cont (fun τ hτ => hA.deriv τ hτ)
    (fun i => by fin_cases i; norm_num) (fun k hk => by
      interval_cases k <;> norm_num)
  have e1 : t + 1 / 2 * (2 * h / 3) = t + h / 3 := by ring
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
    one_smul, Finset.sum_singleton, abs_one, one_mul, e1] at hq
  rw [hA₀] at hq
  have hdef3 : ‖Y₀ + (2 * h / 3) • F (t + h / 3) Z₂ - A (t + 2 * h / 3)‖ ≤
      7 / 81 * M₂ * h ^ 3 + 2 * h / 3 * L * (2 / 9 * M₁ * h ^ 2 + 5 / 3 * h * η) := by
    have hsplit : Y₀ + (2 * h / 3) • F (t + h / 3) Z₂ - A (t + 2 * h / 3) =
        ((2 * h / 3) • F (t + h / 3) (A (t + h / 3)) - (A (t + 2 * h / 3) - Y₀)) +
          (2 * h / 3) • (F (t + h / 3) Z₂ - F (t + h / 3) (A (t + h / 3))) := by
      rw [smul_sub]; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add (hq.trans_eq ?_) ?_)
    · norm_num; ring
    · rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hF _ _ _).trans
        (mul_le_mul_of_nonneg_left hst2' hL)) (by positivity)
  have hst3 := hs3.one_step_error hV₀ hY₀ (hcmp (2 * h / 3) ⟨by positivity, by linarith⟩)
  have hst3' : ‖Z₃ - A (t + 2 * h / 3)‖ ≤
      (28 / 81 * M₂ + 16 / 27 * L * M₁) * h ^ 3 + (40 / 9 * L * h + 10 / 3) * h * η := by
    refine hst3.trans ?_
    nlinarith [hdef3]
  refine ⟨hst3', ?_⟩
  -- final step
  have hinc := rk_increment_error_le (q := 2) hF hL ![1 / 4, 0, 3 / 4] ![0, 1 / 3, 2 / 3]
    (fun i => by fin_cases i <;> norm_num) (fun k hk => by
      interval_cases k <;> simp [Fin.sum_univ_three] <;> norm_num)
    hh hA (by convert hg using 1; norm_num) (by simpa using hM₃) (Z := ![Y₀, Z₂, Z₃])
    (e := ![0, 0, (28 / 81 * M₂ + 16 / 27 * L * M₁) * h ^ 3 + (40 / 9 * L * h + 10 / 3) * h * η])
    (fun i hb => by
      fin_cases i
      · simp [hA₀]
      · exact absurd rfl hb
      · simpa [show 2 / 3 * h = 2 * h / 3 by ring] using hst3')
  have hsum : A t + h • ∑ i, (![1 / 4, 0, 3 / 4] : Fin 3 → ℝ) i •
      F (t + (![0, 1 / 3, 2 / 3] : Fin 3 → ℝ) i * h) (![Y₀, Z₂, Z₃] i) =
      Y₀ + h • ((1 / 4 : ℝ) • F t Y₀ + (3 / 4 : ℝ) • F (t + 2 * h / 3) Z₃) := by
    simp [Fin.sum_univ_three, hA₀, show 2 / 3 * h = 2 * h / 3 by ring]
  rw [hsum] at hinc
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hinc
  have hfin := hs.one_step_error hV₀ hY₀ (hcmp h ⟨hh, le_rfl⟩)
  norm_num [Nat.factorial] at hinc hfin
  refine hfin.trans ?_
  nlinarith [hinc]

/-- **Heun RK3, robust order 3, global error** (arXiv 2608.17157, Thm 6.1 with Thm 5.1 for Heun
RK3): if every step satisfies the hypotheses of `IsHeun3KLStep.one_step_error` with the same
constants, then for `j h ≤ T`
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T ((17/54 M₃ + 28/27 L M₂ + 16/9 L² M₁) h³ +
(40/3 L² h² + 10 L h + 5) η))`, i.e. `C_T (δ + ε_r + h³)` for `h ≤ 1`
(with `η = √(mn) ε_r e^{L_F h}` from Lemma 4.2). -/
theorem heun3KL_global_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L M₁ M₂ M₃ η t₀ h T : ℝ} {N : ℕ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 < h)
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hM₃0 : 0 ≤ M₃) (hη : 0 ≤ η)
    {A : ℝ → Matrix m n ℝ} {Y Z₂ Z₃ : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n r ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j)
    (hV : ∀ j < N, (V j)ᵀ * V j = 1) (hYV : ∀ j < N, Y j * V j * (V j)ᵀ = Y j)
    (hstep : ∀ j < N, IsHeun3KLStep F (V j) (t₀ + j * h) h (Y j) (Z₂ j) (Z₃ j) (Y (j + 1)))
    (hg : ∀ j < N, ContDiffOn ℝ 3 (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)))
    (hM₁ : ∀ j < N, ∀ τ ∈ Icc (t₀ + j * h) (t₀ + j * h + h),
      ‖iteratedDerivWithin 1 (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)) τ‖ ≤ M₁)
    (hM₂ : ∀ j < N, ∀ τ ∈ Icc (t₀ + j * h) (t₀ + j * h + h),
      ‖iteratedDerivWithin 2 (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)) τ‖ ≤ M₂)
    (hM₃ : ∀ j < N, ∀ τ ∈ Icc (t₀ + j * h) (t₀ + j * h + h),
      ‖iteratedDerivWithin 3 (fun τ => F τ (Φ j τ)) (Icc (t₀ + j * h) (t₀ + j * h + h)) τ‖ ≤ M₃)
    (hcmp : ∀ j < N, ∀ σ ∈ Icc 0 h,
      HasComparisonCurve (Y j) (Φ j (t₀ + j * h + σ)) (σ * η)) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ +
        T * ((17 / 54 * M₃ + 28 / 27 * L * M₂ + 16 / 9 * L ^ 2 * M₁) * h ^ 3 +
          (40 / 3 * L ^ 2 * h ^ 2 + 10 * L * h + 5) * η)) := by
  refine lady_windermere_of_le hF hL hh.le hA hΦ hΦ₀ (by positivity) (fun j hj => ?_)
  have e : t₀ + (j + 1) * h = t₀ + j * h + h := by ring
  rw [e]
  have hΦj := hΦ j hj
  rw [e] at hΦj
  have h1 := ((hstep j hj).one_step_error hF hL hh.le (hV j hj) (hYV j hj) hΦj
    (hΦ₀ j hj) (hg j hj) (hM₁ j hj) (hM₂ j hj) (hM₃ j hj) (hcmp j hj)).2.2
  refine h1.trans_eq ?_
  ring

omit [DecidableEq n] in
/-- The reduced K–L step of arXiv 2608.17157 is always defined when `r ≤ m` (QR factorization
of `K₁ = X V₀`, also for rank-deficient `K₁`), so `IsKLStep` and the step relations of this
module are satisfiable. -/
theorem exists_isKLStep {k : ℕ} (hk : k ≤ Fintype.card m) (V₀ : Matrix n (Fin k) ℝ)
    (X : Matrix m n ℝ) : ∃ Y₁, IsKLStep V₀ X Y₁ := by
  obtain ⟨U, hU, hcap⟩ := exists_orthonormal_capture_of_le_card (X * V₀) hk
  exact ⟨U * Uᵀ * X, U, Uᵀ * (X * V₀), hU, by rw [← Matrix.mul_assoc, hcap], rfl⟩

omit [DecidableEq n] in
/-- Every midpoint step (arXiv 2608.17157, Section 6) exists when `r ≤ m`. -/
example {k : ℕ} (hk : k ≤ Fintype.card m) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (V₀ : Matrix n (Fin k) ℝ) (t h : ℝ) (Y₀ : Matrix m n ℝ) :
    ∃ Z Y₁, IsMidpointKLStep F V₀ t h Y₀ Z Y₁ := by
  obtain ⟨Z, hZ⟩ := exists_isKLStep hk V₀ (Y₀ + (h / 2) • F t Y₀)
  obtain ⟨Y₁, hY₁⟩ := exists_isKLStep hk V₀ (Y₀ + h • F (t + h / 2) Z)
  exact ⟨Z, Y₁, hZ, hY₁⟩

/-- The comparison hypothesis of Theorem 4.3 of arXiv 2608.17157 is satisfiable: it holds with
`η = 0` when the exact value is `Y₀` itself (e.g. for `F = 0`). -/
theorem hasComparisonCurve_self (Y₀ : Matrix m n ℝ) : HasComparisonCurve Y₀ Y₀ 0 := by
  classical
  exact ⟨1, 1, by rw [sub_self]; norm_num [specNorm], by simp⟩

end RK

end LeanDLRA.Literature.P2608_17157
