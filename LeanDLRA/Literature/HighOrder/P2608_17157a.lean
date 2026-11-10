import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature
import LeanDLRA.HighOrder.RungeKuttaBUG
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.ODE
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.SVD
import LeanDLRA.OpenProblems.HighOrder.Part1a
import LeanDLRA.OpenProblems.Curated.HighOrdera

/-!
# Robust high-order projector-splitting integrators (Zhang–Hu, arXiv 2608.17157)

For a prescribed increment `ΔA`, Zhang and Hu reduce the K–S–L projector-splitting step to the
K–L step `Y₁ = U₁ U₁ᵀ (Y₀ + ΔA)` with `U₁ Ŝ₁ = (Y₀ + ΔA) V₀` (`IsKLStep`; Section 2.3: the
factored output is `isKLStep_of_factors`, and every K–S–L step of the library,
`Exactness.IsKSLIncrementStep`, is a reduced K–L step, `isKLStep_of_isKSLIncrementStep`), and use
Runge–Kutta increments.  The module works on real `m × n` matrices with the Frobenius norm and the
spectral norm `specNorm`.

Main results:
* Proposition 2.1 and Theorem 4.1: `IsKLStep.eq_of_overlap`, `IsKLStep.relaxed_exactness`
  (`‖Y₁ - Y⋆‖ ≤ (1 + ‖Q‖₂) ‖Y₀ + ΔA - Y⋆‖` for `Y⋆ = (Y⋆ V₀) Q`).
* Appendix A and Lemma 4.2 (the comparison curve): Lemma A.1 (`factoredNormalBound_of_isUnit`,
  which turns (3.3) into the library's `MatrixBUG.FactoredNormalBound`, and
  `norm_transpose_mul_rhs_mul_le`); Lemma A.2 with the paper's `K_G = (r + √r) L_F` and
  `E_G = √(mn) ε_r` (`exists_generators`); Lemma A.3 at one time (`exists_comparison_point`);
  A.4 (`exists_overlap_of_specNorm_sub_one_le`); Lemma 4.2 in the form the error analysis uses
  (`hasComparisonCurve_of_standing`, `forall_hasComparisonCurve_of_standing`).
* Theorems 4.3, 5.1 (with (5.3)) and 6.1, conditional on a comparison point (`HasComparisonCurve`:
  `IsKLStep.one_step_error`, `klStep_global_error`, `klStep_global_error_of_order`,
  `IsRKKLStep.one_step_error`, `rkKL_global_error`) and unconditional under the standing
  assumptions with the paper's constants (`IsKLStep.one_step_error_of_standing`,
  `klStep_global_error_of_standing`, `IsRKKLStep.one_step_error_of_standing`,
  `rkKL_global_error_of_standing`); the increment error of Theorem 6.1 is `rk_increment_error`
  with the paper's constant `klRKConst`.
* Lemma 6.2 (`exists_norm_iteratedDerivWithin_rhs_le`; explicit constants for `p = 2`:
  `norm_iteratedDerivWithin_rhs_le_two`) and the corollaries of Section 6: the two-stage family
  of Remark 6.3 and the midpoint method (`IsRK2KLStep.one_step_error`, `rk2KL_global_error`,
  `IsMidpointKLStep.one_step_error`), Heun's RK3 (`IsHeun3KLStep.one_step_error`,
  `heun3KL_global_error`), each also under (6.9) with Lemma 6.2 (`_of_contDiff`); robust orders
  2, 2 and 3.
Tools: the sharp vector-valued Taylor bound `norm_sub_taylorWithinEval_le`, the quadrature
estimate `norm_quadrature_sub_le`, `rk_increment_error_le`; `exists_isKLStep` shows that every
step exists.

Differences from the paper.
(1) Lemmas A.3 and 4.2: the paper builds an absolutely continuous curve `Ỹ(s) = L(s) Y₀ R(s)`
from a differential inclusion (Deimling's existence theorem), with invertible `L`, `R` and
`rank Ỹ = r`.  Only what the error analysis uses is proved: at each time `s` with
`e^{K_G s} ≤ 3/2` (the paper's `s ≤ h*`) there are `L`, `R` with `‖R - I‖₂ ≤ e^{K_G s} - 1` and
`‖L Y₀ R - A(s)‖ ≤ η` for every `η > √(mn) ε_r s e^{L_F s}`, from an Euler-type polygon with
generators chosen at grid points.  The unconditional Theorems 4.3, 5.1 and 6.1 recover the paper's
constants by a limit.  The theorems without `_of_standing` keep the comparison point as the
hypothesis `HasComparisonCurve` and are conditional on Lemma 4.2; for the Section 6 corollaries
`forall_hasComparisonCurve_of_standing` discharges it for every `η > √(mn) ε_r e^{L_F h}`.  Their
stage bounds are stated at every `σ ∈ [0, h]` in the form `σ η` with `η = √(mn) ε_r e^{L_F h}`
(so the midpoint stage bound has `e^{L_F h}` where the paper has `e^{L_F h/2}`).
(2) Standing assumptions: `F` jointly continuous and `L_F`-Lipschitz in `X`; the bound
`‖F‖ ≤ B` enters only Lemma 6.2.  (3.3) is stated for `U S Vᵀ` with orthonormal `U`, `V` and
invertible `S`, which parametrizes `M_r` (`SVD.rank_eq_iff_exists_factor`).
(3) Lemma 6.2: (6.9) is stated for the full derivatives `D^j F` of `(t, X) ↦ F(t, X)` on
`ℝ × ℝ^{m×n}` (their restrictions are the mixed partials of (6.9); conversely (6.9) bounds
`‖D^j F‖` by `2^j M`), with `F` of class `C^p` on all of `ℝ × ℝ^{m×n}`.  The `M_q` are explicit
for `q ≤ 2` and existential for `q = 3`.
(4) Rank-admissibility is never needed.  The nodes are assumed in `[0, 1]` (stated in the paper).
`h ≤ h₀ ≤ 1` is not assumed and all constants are explicit: `C_T` is `e^{L T}` times the displayed
bracket.  In the corollaries the quadrature constants are the generic ones of
`norm_quadrature_sub_le` (e.g. `7/81 M₂ h³` for the Heun stage 3, where the paper uses the sharp
midpoint-rule constant `M₂ h³/81`).
(5) The abstract form of Theorem 4.1 is the library's `RungeKuttaBUG.relaxed_exactness`, used
here.  Remark 6.4 (RK4) is not formalized; the paper gives no proof.  No claim of the paper was
found to be false.

Core definitions used: `ODESolution`, `IsLipschitzField`, `IsBoundedField`,
`lady_windermere_of_le`, `specNorm`, `leftProj`, `Exactness.IsKSLIncrementStep`,
`MatrixBUG.FactoredNormalBound`, `SVD.exists_svd`, and the singular-value-free derivative bounds
of `OpenProblems.HighOrder`.  Local definitions: `IsKLStep` (bridged to
`Exactness.IsKSLIncrementStep`), `HasComparisonCurve`, `IsRKKLStep`, `IsRK2KLStep`,
`IsMidpointKLStep`, `IsHeun3KLStep`, `klRKConst`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius Nat

universe u

namespace LeanDLRA.Literature.P2608_17157

open LeanDLRA LeanDLRA.Curvature

section KL

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- The **reduced K–L step** of arXiv 2608.17157 (Section 2.3, Eqs. (2.14)–(2.19)) in relational
form: from the
right basis `V₀` (`Y₀ = U₀ S₀ V₀ᵀ`) and the updated matrix `X = Y₀ + ΔA`, the K-step factors
`K₁ = X V₀ = U₁ Ŝ₁` with orthonormal `U₁`, and the step returns `Y₁ = U₁ U₁ᵀ X`
(`= U₁ S₁ V₁ᵀ` with `V₁ S₁ᵀ = Xᵀ U₁`, see `isKLStep_of_factors`). -/
def IsKLStep (V₀ : Matrix n r ℝ) (X Y₁ : Matrix m n ℝ) : Prop :=
  ∃ (U₁ : Matrix m r ℝ) (Ŝ₁ : Matrix r r ℝ), U₁ᵀ * U₁ = 1 ∧ U₁ * Ŝ₁ = X * V₀ ∧
    Y₁ = U₁ * U₁ᵀ * X

/-- The factored output of the reduced K–L step (`K₁ = X V₀ = U₁ Ŝ₁`, `L₁ = Xᵀ U₁ = V₁ S₁ᵀ`,
`Y₁ = U₁ S₁ V₁ᵀ`) satisfies `Y₁ = U₁ U₁ᵀ X` (arXiv 2608.17157, Section 2.3, Eq. (2.19)). -/
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

/-- **Proposition 2.1 (exactness)** of arXiv 2608.17157, for the reduced K–L step: if
`X = Y₀ + ΔA` satisfies the row-space overlap condition (2.20), `X = (X V₀) Q`, then the step
returns `Y₁ = X`.  This is the case `Y⋆ = X` of `IsKLStep.relaxed_exactness`; the factor form of
the same exactness property (Lubich–Oseledets) is `Exactness.ksl_exact_of_factors`.  No
rank-admissibility is needed. -/
theorem IsKLStep.eq_of_overlap {V₀ : Matrix n r ℝ} {X Y₁ : Matrix m n ℝ}
    {Q : Matrix r n ℝ} (hstep : IsKLStep V₀ X Y₁) (hV₀ : V₀ᵀ * V₀ = 1) (hX : X = X * V₀ * Q) :
    Y₁ = X := by
  classical
  have h := hstep.relaxed_exactness hV₀ hX
  rw [sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **The K–S–L step for a prescribed increment is the reduced K–L step** (arXiv 2608.17157,
Section 2.3, Eqs. (2.12)–(2.13)).  Every K–S–L step of the library
(`Exactness.IsKSLIncrementStep`, the paper's Eqs. (2.6)–(2.11) with `ΔA = A₁ - A₀`) from
`Y₀ = U₀ S₀ V₀ᵀ` with `V₀ᵀ V₀ = 1` is a reduced K–L step from `V₀` with `X = Y₀ + ΔA`, with the
same output `Y₁ = U₁ S₁ V₁ᵀ`: the backward S-step gives `S̃₀ = U₁ᵀ U₀ S₀` and
`L₁ = (Y₀ + ΔA)ᵀ U₁`.  As in the paper's derivation, neither `U₀ᵀ U₀ = 1` nor the invertibility
of `S₀`, `Ŝ₁`, `S₁` is used. -/
theorem isKLStep_of_isKSLIncrementStep {A₀ A₁ : Matrix m n ℝ} {U₀ : Matrix m r ℝ}
    {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {U₁ : Matrix m r ℝ} {Ŝ₁ S₁ : Matrix r r ℝ}
    {V₁ : Matrix n r ℝ} (hstep : Exactness.IsKSLIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ Ŝ₁ S₁ V₁)
    (hV₀ : V₀ᵀ * V₀ = 1) :
    IsKLStep V₀ (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) (U₁ * S₁ * V₁ᵀ) := by
  have hK : U₁ * Ŝ₁ = (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * V₀ := by
    rw [hstep.qrK, Matrix.add_mul, Matrix.mul_assoc (U₀ * S₀), hV₀, Matrix.mul_one]
  refine isKLStep_of_factors hstep.orthU hK ?_
  have hS : Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀ = U₁ᵀ * U₀ * S₀ := by
    have : Ŝ₁ = U₁ᵀ * (U₀ * S₀ + (A₁ - A₀) * V₀) := by
      rw [← hstep.qrK, ← Matrix.mul_assoc, hstep.orthU, Matrix.one_mul]
    rw [this, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, add_sub_cancel_right]
  rw [hstep.qrL, hS, Matrix.transpose_add, Matrix.add_mul]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end KL

/-! ### The normal defect on lower-rank strata (Lemma A.1) -/

section NormalDefect

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- For every square `S`, `S + τ • 1` is invertible for arbitrarily small `τ > 0`: the
`τ` with `det (S + τ • 1) = 0` are roots of the characteristic polynomial of `-S` (auxiliary for
arXiv 2608.17157, Lemma A.1). -/
theorem exists_isUnit_det_add_smul_one {k : Type*} [Fintype k] [DecidableEq k]
    (S : Matrix k k ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ, 0 < τ ∧ τ < δ ∧ IsUnit (S + τ • (1 : Matrix k k ℝ)).det := by
  have hfin : {τ : ℝ | (Matrix.charpoly (-S)).IsRoot τ}.Finite :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic _).ne_zero
  obtain ⟨τ, hτ, hτS⟩ := (Set.Ioo_infinite hδ).exists_notMem_finite hfin
  refine ⟨τ, hτ.1, hτ.2, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hτS
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly]
  convert h0 using 2
  rw [sub_neg_eq_add, add_comm, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/-- **Lemma A.1, matrix form: the normal bound extends to the lower-rank strata** (arXiv
2608.17157, Appendix A.1).  If `F` is `L`-Lipschitz in `X` (standing assumption (3.2)) and the
normal component is at most `ε` at every point of `M_r` (standing assumption (3.3):
`Y = U S Vᵀ` with orthonormal `U`, `V` and invertible `S`, which parametrizes exactly the rank-`r`
matrices, `SVD.rank_eq_iff_exists_factor`), then the bound holds for **every** `S`, i.e. at
every `U S Vᵀ` of rank `≤ r` with `r`-column frames `U ⊇ range Y`, `V ⊇ range Yᵀ`: this is the
library's factored normal-component assumption `MatrixBUG.FactoredNormalBound F r ε`.  The proof
replaces the paper's perturbation `X + τ ∑ ûₗ v̂ₗᵀ` (A.6) by `U (S + τ I) Vᵀ` and lets `τ → 0⁺`
(only the Lipschitz bound is used, as in the paper's limit). -/
theorem factoredNormalBound_of_isUnit {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) {r : ℕ} {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε) :
    MatrixBUG.FactoredNormalBound F r ε := by
  intro t U V S hU hV
  set c : ℝ := |L| * ‖U * Vᵀ‖ + 1 with hc
  have hc0 : 0 < c := by positivity
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨τ, hτ0, hτδ, hτS⟩ := exists_isUnit_det_add_smul_one S (div_pos hδ hc0)
  have h1 := hε t U V _ hU hV hτS
  have hdiff : U * (S + τ • (1 : Matrix (Fin r) (Fin r) ℝ)) * Vᵀ - U * S * Vᵀ =
      τ • (U * Vᵀ) := by
    rw [Matrix.mul_add, Matrix.add_mul, add_sub_cancel_left, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  have h2 : ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ) -
      (1 - U * Uᵀ) * F t (U * (S + τ • 1) * Vᵀ) * (1 - V * Vᵀ)‖ ≤ |L| * (τ * ‖U * Vᵀ‖) := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    refine (MatrixBUG.norm_normal_le hU hV _).trans ?_
    rw [norm_sub_rev]
    refine (hF t _ _).trans ?_
    rw [hdiff, norm_smul, Real.norm_of_nonneg hτ0.le]
    exact mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity)
  have h3 : |L| * (τ * ‖U * Vᵀ‖) ≤ δ := by
    have : τ * c ≤ δ := by
      rw [lt_div_iff₀ hc0] at hτδ
      exact hτδ.le
    nlinarith [norm_nonneg (U * Vᵀ), abs_nonneg L]
  calc _ ≤ ‖(1 - U * Uᵀ) * F t (U * (S + τ • 1) * Vᵀ) * (1 - V * Vᵀ)‖ +
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ) -
          (1 - U * Uᵀ) * F t (U * (S + τ • 1) * Vᵀ) * (1 - V * Vᵀ)‖ := norm_le_insert' _ _
    _ ≤ ε + δ := add_le_add h1 (h2.trans h3)

omit [DecidableEq n] in
private theorem transpose_mul_compl_eq {k : Type*} [Fintype k] {x : Matrix m (Fin 1) ℝ}
    {U : Matrix m k ℝ} (hUx : Uᵀ * x = 0) : xᵀ * (1 - U * Uᵀ) = xᵀ := by
  have : xᵀ * U = 0 := by
    have h := congrArg Matrix.transpose hUx
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, this, Matrix.zero_mul, sub_zero]

/-- The bilinear form of Lemma A.1 of arXiv 2608.17157 under the library's factored
normal-component assumption: if `rank X ≤ r < min(m, n)`, `x`, `y` are unit vectors (single
orthonormal columns) with `x ⊥ range X` (`xᵀ X = 0`) and `y ⊥ range Xᵀ` (`X y = 0`), then
`|xᵀ F(t, X) y| ≤ ε` (the `1 × 1` matrix `xᵀ F(t, X) y` has Frobenius norm `|xᵀ F(t, X) y|`).
The frames `U ⊥ x`, `V ⊥ y` with `U Uᵀ X = X`, `X V Vᵀ = X` come from
`exists_orthonormal_capture_compl`, which is where `r < m`, `r < n` enter (the paper's
dimension count (A.4)–(A.5)). -/
theorem norm_transpose_mul_rhs_mul_le_of_factored {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {r : ℕ} {ε : ℝ} (hN : MatrixBUG.FactoredNormalBound F r ε) (hrm : r < Fintype.card m)
    (hrn : r < Fintype.card n) {X : Matrix m n ℝ} (hX : X.rank ≤ r)
    {x : Matrix m (Fin 1) ℝ} {y : Matrix n (Fin 1) ℝ} (hx : xᵀ * x = 1) (hy : yᵀ * y = 1)
    (hxX : xᵀ * X = 0) (hXy : X * y = 0) (t : ℝ) : ‖xᵀ * F t X * y‖ ≤ ε := by
  have hcX : (1 - x * xᵀ) * X = X := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hxX, Matrix.mul_zero, sub_zero]
  have hcXt : (1 - y * yᵀ) * Xᵀ = Xᵀ := by
    have : yᵀ * Xᵀ = 0 := by
      rw [← Matrix.transpose_mul, hXy, Matrix.transpose_zero]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_zero, sub_zero]
  obtain ⟨U, hU, hUx, hUX⟩ := exists_orthonormal_capture_compl x hx X (s := r)
    (by rwa [hcX]) (by simp only [Fintype.card_fin]; omega)
  obtain ⟨V, hV, hVy, hVX⟩ := exists_orthonormal_capture_compl y hy Xᵀ (s := r)
    (by rwa [hcXt, Matrix.rank_transpose]) (by simp only [Fintype.card_fin]; omega)
  rw [hcX] at hUX
  rw [hcXt] at hVX
  have hXV : X * V * Vᵀ = X := by
    have h := congrArg Matrix.transpose hVX
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h
  have hXeq : X = U * (Uᵀ * X * V) * Vᵀ := by
    calc X = U * Uᵀ * (X * V * Vᵀ) := by rw [hXV, hUX]
      _ = U * (Uᵀ * X * V) * Vᵀ := by simp only [Matrix.mul_assoc]
  have hyV : (1 - V * Vᵀ) * y = y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hVy, Matrix.mul_zero, sub_zero]
  have hmid := hN t U V (Uᵀ * X * V) hU hV
  rw [← hXeq] at hmid
  have heq : xᵀ * F t X * y = xᵀ * ((1 - U * Uᵀ) * F t X * (1 - V * Vᵀ)) * y := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, transpose_mul_compl_eq hUx,
      Matrix.mul_assoc (xᵀ * F t X) (1 - V * Vᵀ) y, hyV]
  rw [heq]
  calc ‖xᵀ * ((1 - U * Uᵀ) * F t X * (1 - V * Vᵀ)) * y‖
      ≤ ‖xᵀ * ((1 - U * Uᵀ) * F t X * (1 - V * Vᵀ))‖ * specNorm y := frob_mul_le' _ _
    _ ≤ (specNorm xᵀ * ‖(1 - U * Uᵀ) * F t X * (1 - V * Vᵀ)‖) * specNorm y :=
        mul_le_mul_of_nonneg_right (frob_mul_le _ _) (specNorm_nonneg _)
    _ ≤ (1 * ‖(1 - U * Uᵀ) * F t X * (1 - V * Vᵀ)‖) * 1 := by
        have hxs : specNorm xᵀ ≤ 1 := by
          rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hx
        exact mul_le_mul (mul_le_mul_of_nonneg_right hxs (norm_nonneg _))
          (specNorm_le_one_of_orthonormal hy) (specNorm_nonneg _) (by positivity)
    _ ≤ ε := by rw [one_mul, mul_one]; exact hmid

/-- **Lemma A.1 (normal defect on lower-rank strata)** of arXiv 2608.17157, as printed: under the
standing assumptions (`F` `L`-Lipschitz, (3.2); normal component at most `ε` on `M_r`, (3.3);
`r < min(m, n)`), for every `X` of rank `≤ r` and unit vectors `x ⊥ range X`, `y ⊥ range Xᵀ`,
`|xᵀ F(t, X) y| ≤ ε`.  Unit vectors are single orthonormal columns, and `|xᵀ F y|` is the
Frobenius norm of the `1 × 1` matrix `xᵀ F y`.  The paper assumes `F` continuous; only its
Lipschitz continuity in `X` is used. -/
theorem norm_transpose_mul_rhs_mul_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) {r : ℕ} {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n) {X : Matrix m n ℝ} (hX : X.rank ≤ r)
    {x : Matrix m (Fin 1) ℝ} {y : Matrix n (Fin 1) ℝ} (hx : xᵀ * x = 1) (hy : yᵀ * y = 1)
    (hxX : xᵀ * X = 0) (hXy : X * y = 0) (t : ℝ) : ‖xᵀ * F t X * y‖ ≤ ε :=
  norm_transpose_mul_rhs_mul_le_of_factored (factoredNormalBound_of_isUnit hF hε) hrm hrn hX hx hy
    hxX hXy t

end NormalDefect

/-! ### Bounded left and right generators (Lemma A.2) -/

section Aux

/-- The `i`-th standard basis column `eᵢ` (auxiliary for arXiv 2608.17157, Lemma A.2). -/
private def ecol {k : Type*} [DecidableEq k] (i : k) : Matrix k (Fin 1) ℝ :=
  Matrix.of fun j _ => if j = i then 1 else 0

private theorem mul_ecol_apply {m k : Type*} [Fintype k] [DecidableEq k] (A : Matrix m k ℝ)
    (i : k) (a : m) (o : Fin 1) : (A * ecol i) a o = A a i := by
  simp [ecol, Matrix.mul_apply]

private theorem ecol_transpose_mul_apply {k n : Type*} [Fintype k] [DecidableEq k]
    (B : Matrix k n ℝ) (i : k) (o : Fin 1) (b : n) : ((ecol i)ᵀ * B) o b = B i b := by
  simp [ecol, Matrix.mul_apply]

/-- The Frobenius norm of a `1 × 1` matrix is the absolute value of its entry. -/
theorem norm_fin_one (M : Matrix (Fin 1) (Fin 1) ℝ) : ‖M‖ = |M 0 0| := by
  have h := frob_sq M
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton] at h
  rw [← Real.sqrt_sq (norm_nonneg M), h, Real.sqrt_sq_eq_abs]

/-- For a column `c`, the `1 × 1` matrix `cᵀ c` is `‖c‖²`. -/
theorem transpose_mul_self_fin_one {m : Type*} [Fintype m] (c : Matrix m (Fin 1) ℝ) :
    (cᵀ * c) 0 0 = ‖c‖ ^ 2 := by
  rw [frob_sq]
  simp [Matrix.mul_apply, sq]

private theorem frob_sq_eq_sum_cols {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (A : Matrix m k ℝ) : ‖A‖ ^ 2 = ∑ i : k, ‖(A * ecol i : Matrix m (Fin 1) ℝ)‖ ^ 2 := by
  rw [frob_sq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_sq]
  simp [mul_ecol_apply]

private theorem frob_sq_eq_sum_rows {k n : Type*} [Fintype k] [DecidableEq k] [Fintype n]
    (B : Matrix k n ℝ) : ‖B‖ ^ 2 = ∑ i : k, ‖((ecol i)ᵀ * B : Matrix (Fin 1) n ℝ)‖ ^ 2 := by
  rw [frob_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_sq]
  simp [ecol_transpose_mul_apply]

private theorem ecol_orthonormal {k : Type*} [Fintype k] [DecidableEq k] (i : k) :
    (ecol i)ᵀ * ecol i = 1 := by
  ext o o'
  rw [Subsingleton.elim o 0, Subsingleton.elim o' 0]
  simp [ecol, Matrix.mul_apply]

private theorem entry_eq_ecol {k l : Type*} [Fintype k] [DecidableEq k] [Fintype l]
    [DecidableEq l] (N : Matrix k l ℝ) (i : k) (j : l) :
    ((ecol i)ᵀ * N * ecol j) 0 0 = N i j := by
  rw [mul_ecol_apply, ecol_transpose_mul_apply]

private theorem ecol_transpose_mul_diagonal {k : Type*} [Fintype k] [DecidableEq k]
    (d : k → ℝ) (i : k) : (ecol i)ᵀ * Matrix.diagonal d = d i • (ecol i)ᵀ := by
  ext o l
  rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases h : l = i
  · subst h; simp [ecol]
  · simp [ecol, h]

private theorem diagonal_mul_ecol {k : Type*} [Fintype k] [DecidableEq k] (d : k → ℝ) (i : k) :
    Matrix.diagonal d * ecol i = d i • ecol i := by
  ext l o
  rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases h : l = i
  · subst h; simp [ecol]
  · simp [ecol, h]

private theorem norm_ecol {k : Type*} [Fintype k] [DecidableEq k] (i : k) : ‖ecol i‖ = 1 := by
  have h := transpose_mul_self_fin_one (ecol i)
  rw [ecol_orthonormal, Matrix.one_apply_eq] at h
  rw [← Real.sqrt_sq (norm_nonneg _), ← h, Real.sqrt_one]

/-- A nonzero column normalized to unit length is a single orthonormal column. -/
theorem transpose_mul_self_smul_inv_norm {m : Type*} [Fintype m] {c : Matrix m (Fin 1) ℝ}
    (hc : c ≠ 0) : (‖c‖⁻¹ • c)ᵀ * (‖c‖⁻¹ • c) = 1 := by
  have h0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hval : ((‖c‖⁻¹ • c)ᵀ * (‖c‖⁻¹ • c)) 0 0 = 1 := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
      Matrix.smul_apply, transpose_mul_self_fin_one, smul_eq_mul, smul_eq_mul]
    field_simp
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, hval, Matrix.one_apply_eq]

/-- Pythagoras for an orthonormal `U`: `‖Z‖² = ‖Uᵀ Z‖² + ‖(I - U Uᵀ) Z‖²`. -/
private theorem frob_sq_eq_proj_add_compl {m k l : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] [Fintype l] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (Z : Matrix m l ℝ) : ‖Z‖ ^ 2 = ‖Uᵀ * Z‖ ^ 2 + ‖(1 - U * Uᵀ) * Z‖ ^ 2 := by
  have hUP : Uᵀ * (1 - U * Uᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self]
  have hZ : U * (Uᵀ * Z) + (1 - U * Uᵀ) * Z = Z := by
    rw [← Matrix.mul_assoc, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  have h0 : (U * (Uᵀ * Z))ᵀ * ((1 - U * Uᵀ) * Z) = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ (1 - U * Uᵀ), hUP,
      Matrix.zero_mul, Matrix.mul_zero]
  calc ‖Z‖ ^ 2 = ‖U * (Uᵀ * Z) + (1 - U * Uᵀ) * Z‖ ^ 2 := by rw [hZ]
    _ = ‖U * (Uᵀ * Z)‖ ^ 2 + ‖(1 - U * Uᵀ) * Z‖ ^ 2 := frob_sq_add_of_orth h0
    _ = ‖Uᵀ * Z‖ ^ 2 + ‖(1 - U * Uᵀ) * Z‖ ^ 2 := by
        rw [Frobenius.norm_mul_of_orthonormal hU]

end Aux

section Generators

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The factored normal-component bound forces `ε ≥ 0` when `r ≤ min(m, n)`. -/
theorem nonneg_of_factoredNormalBound {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ} {ε : ℝ}
    (hN : MatrixBUG.FactoredNormalBound F r ε) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) : 0 ≤ ε := by
  obtain ⟨U, hU, -⟩ := exists_orthonormal_capture_of_le_card (0 : Matrix m (Fin r) ℝ) hrm
  obtain ⟨V, hV, -⟩ := exists_orthonormal_capture_of_le_card (0 : Matrix n (Fin r) ℝ) hrn
  exact (norm_nonneg _).trans (hN 0 U V 0 hU hV)

/-- **Lemma A.1, homogeneous form** (arXiv 2608.17157): for arbitrary columns `x ⊥ range X`,
`y ⊥ range Xᵀ` (not necessarily unit), `|xᵀ F(t, X) y| ≤ ε ‖x‖ ‖y‖`. -/
theorem norm_transpose_mul_rhs_mul_le_mul {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ}
    {ε : ℝ} (hN : MatrixBUG.FactoredNormalBound F r ε) (hrm : r < Fintype.card m)
    (hrn : r < Fintype.card n) {X : Matrix m n ℝ} (hX : X.rank ≤ r)
    {x : Matrix m (Fin 1) ℝ} {y : Matrix n (Fin 1) ℝ} (hxX : xᵀ * X = 0) (hXy : X * y = 0)
    (t : ℝ) : ‖xᵀ * F t X * y‖ ≤ ε * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h := norm_transpose_mul_rhs_mul_le_of_factored hN hrm hrn hX
    (transpose_mul_self_smul_inv_norm hx) (transpose_mul_self_smul_inv_norm hy)
    (by rw [Matrix.transpose_smul, Matrix.smul_mul, hxX, smul_zero])
    (by rw [Matrix.mul_smul, hXy, smul_zero]) t
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, norm_smul,
    Real.norm_eq_abs, abs_mul, abs_inv, abs_norm] at h
  calc ‖xᵀ * F t X * y‖ = (‖x‖ * ‖y‖) * ((‖x‖⁻¹ * ‖y‖⁻¹) * ‖xᵀ * F t X * y‖) := by
        rw [← mul_assoc, mul_mul_mul_comm, mul_inv_cancel₀ hx0.ne', mul_inv_cancel₀ hy0.ne',
          one_mul, one_mul]
    _ ≤ (‖x‖ * ‖y‖) * ε := mul_le_mul_of_nonneg_left (by linarith [h]) (by positivity)
    _ = ε * ‖x‖ * ‖y‖ := by ring

/-- **Normal columns of `F(t, X)`** (Lemma A.1 of arXiv 2608.17157, applied to the vector
`x = (I - U Uᵀ) F(t, X) z`): if `U` is orthonormal with `U Uᵀ X = X` and `X z = 0`, then
`‖(I - U Uᵀ) F(t, X) z‖ ≤ ε ‖z‖`. -/
theorem norm_compl_mul_rhs_mul_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ} {ε : ℝ}
    (hN : MatrixBUG.FactoredNormalBound F r ε) (hrm : r < Fintype.card m)
    (hrn : r < Fintype.card n) {X : Matrix m n ℝ} (hX : X.rank ≤ r) {k : Type*} [Fintype k]
    [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (hUX : U * Uᵀ * X = X)
    {z : Matrix n (Fin 1) ℝ} (hXz : X * z = 0) (t : ℝ) :
    ‖(1 - U * Uᵀ) * F t X * z‖ ≤ ε * ‖z‖ := by
  have hε0 := nonneg_of_factoredNormalBound hN hrm.le hrn.le
  have hP := (isOrthProjMat_mul_transpose hU).compl
  have hPX : (1 - U * Uᵀ) * X = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hUX, sub_self]
  set c := (1 - U * Uᵀ) * F t X * z with hc
  have hcX : cᵀ * X = 0 := by
    rw [hc, Matrix.transpose_mul, Matrix.transpose_mul, hP.symm, Matrix.mul_assoc,
      Matrix.mul_assoc, hPX, Matrix.mul_zero, Matrix.mul_zero]
  have h1 := norm_transpose_mul_rhs_mul_le_mul hN hrm hrn hX hcX hXz t
  have h2 : cᵀ * F t X * z = cᵀ * c := by
    rw [hc, Matrix.transpose_mul, Matrix.transpose_mul, hP.symm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - U * Uᵀ) (1 - U * Uᵀ), hP.idem]
  have h3 : ‖cᵀ * c‖ = ‖c‖ ^ 2 := by
    rw [norm_fin_one, transpose_mul_self_fin_one, abs_of_nonneg (sq_nonneg _)]
  rw [h2, h3] at h1
  rcases eq_or_lt_of_le (norm_nonneg c) with h0 | hpos
  · rw [← h0]; exact mul_nonneg hε0 (norm_nonneg _)
  · have : ‖c‖ * ‖c‖ ≤ ‖c‖ * (ε * ‖z‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- **Normal rows of `F(t, X)`** (Lemma A.1 of arXiv 2608.17157, transposed form): if `V` is
orthonormal with `X V Vᵀ = X` and `wᵀ X = 0`, then `‖wᵀ F(t, X) (I - V Vᵀ)‖ ≤ ε ‖w‖`. -/
theorem norm_mul_rhs_mul_compl_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ} {ε : ℝ}
    (hN : MatrixBUG.FactoredNormalBound F r ε) (hrm : r < Fintype.card m)
    (hrn : r < Fintype.card n) {X : Matrix m n ℝ} (hX : X.rank ≤ r) {k : Type*} [Fintype k]
    [DecidableEq k] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1) (hXV : X * V * Vᵀ = X)
    {w : Matrix m (Fin 1) ℝ} (hwX : wᵀ * X = 0) (t : ℝ) :
    ‖wᵀ * F t X * (1 - V * Vᵀ)‖ ≤ ε * ‖w‖ := by
  have hε0 := nonneg_of_factoredNormalBound hN hrm.le hrn.le
  have hQ := (isOrthProjMat_mul_transpose hV).compl
  have hXQ : X * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hXV, sub_self]
  set y := (1 - V * Vᵀ) * (F t X)ᵀ * w with hy
  have hXy : X * y = 0 := by
    rw [hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXQ, Matrix.zero_mul, Matrix.zero_mul]
  have hyT : yᵀ = wᵀ * F t X * (1 - V * Vᵀ) := by
    rw [hy, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQ.symm,
      Matrix.mul_assoc]
  have h1 := norm_transpose_mul_rhs_mul_le_mul hN hrm hrn hX hwX hXy t
  have h2 : wᵀ * F t X * y = yᵀ * y := by
    rw [hyT, hy]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - V * Vᵀ) (1 - V * Vᵀ), hQ.idem]
  have h3 : ‖yᵀ * y‖ = ‖y‖ ^ 2 := by
    rw [norm_fin_one, transpose_mul_self_fin_one, abs_of_nonneg (sq_nonneg _)]
  rw [h2, h3] at h1
  rw [← hyT, Frobenius.norm_transpose]
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | hpos
  · rw [← h0]; exact mul_nonneg hε0 (norm_nonneg _)
  · have : ‖y‖ * ‖y‖ ≤ ‖y‖ * (ε * ‖w‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- **Lemma A.2 (bounded left and right generators)** of arXiv 2608.17157, in finite dimensions
and with the paper's constants.  Under the standing assumptions in the form "`F` is
`L`-Lipschitz and satisfies the factored normal bound `MatrixBUG.FactoredNormalBound F r ε`" (by
`factoredNormalBound_of_isUnit` this follows from (3.2)–(3.3), Lemma A.1) and `r < min(m, n)`,
every `X` of rank `≤ r` admits `G_L ∈ ℝ^{m×m}`, `G_R ∈ ℝ^{n×n}` with
`F(t, X) = G_L X + X G_R + E`, `‖G_L‖₂, ‖G_R‖₂ ≤ K_G = (r + √r) L_F` and
`‖E‖ ≤ E_G = √(mn) ε_r` (Eqs. (A.8)–(A.9)); no constant involves the singular values of `X`.
The generators are the paper's (A.14)–(A.21), built from a thin SVD `X = U diag(σ) Vᵀ`
(`SVD.exists_svd`), with `X_{ii} = X_i` and the uniform formula `Γᵢⱼ = uᵢᵀ (F(X) - F(X_{ij})) vⱼ /
(σᵢ + σⱼ)`.  The bound on `E` is proved from Lemma A.1 through the orthogonal splitting
`‖E‖² = ‖Uᵀ E V‖² + ‖(I - U Uᵀ) E V‖² + ‖Uᵀ E (I - V Vᵀ)‖² + ‖(I - U Uᵀ) E (I - V Vᵀ)‖²`
(the identities (A.24)–(A.28)), which gives `‖E‖² ≤ (q² + q + n) ε² ≤ mn ε²` (`q = rank X`). -/
theorem exists_generators {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {r : ℕ} {ε : ℝ}
    (hN : MatrixBUG.FactoredNormalBound F r ε) (hrm : r < Fintype.card m)
    (hrn : r < Fintype.card n) (t : ℝ) {X : Matrix m n ℝ} (hX : X.rank ≤ r) :
    ∃ (Gl : Matrix m m ℝ) (Gr : Matrix n n ℝ), specNorm Gl ≤ (r + √r) * L ∧
      specNorm Gr ≤ (r + √r) * L ∧
      ‖F t X - Gl * X - X * Gr‖ ≤ √(Fintype.card m * Fintype.card n) * ε := by
  obtain ⟨q, hq⟩ : ∃ q, X.rank = q := ⟨_, rfl⟩
  obtain ⟨U, V, σ, hU, hV, -, hσ, -, hXeq⟩ := SVD.exists_svd X hq
  have hqr : q ≤ r := hq ▸ hX
  have hε0 : 0 ≤ ε := nonneg_of_factoredNormalBound hN hrm.le hrn.le
  -- the complementary projectors `P = I - U Uᵀ`, `Q = I - V Vᵀ`
  set P : Matrix m m ℝ := 1 - U * Uᵀ with hPdef
  set Q : Matrix n n ℝ := 1 - V * Vᵀ with hQdef
  have hPm : IsOrthProjMat P := (isOrthProjMat_mul_transpose hU).compl
  have hQm : IsOrthProjMat Q := (isOrthProjMat_mul_transpose hV).compl
  have hUP : Uᵀ * P = 0 := by
    rw [hPdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self]
  have hPU : P * U = 0 := by
    rw [hPdef, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hVQ : Vᵀ * Q = 0 := by
    rw [hQdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]
  have hQV : Q * V = 0 := by
    rw [hQdef, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]
  have hUX : U * Uᵀ * X = X := by
    rw [hXeq]; simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc U Uᵀ U, hU, Matrix.mul_one]
  have hXV : X * V * Vᵀ = X := by
    rw [hXeq]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᵀ V Vᵀ, hV, Matrix.one_mul]
  have hXQ : X * Q = 0 := by
    rw [hQdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hXV, sub_self]
  -- singular vectors `uᵢ = U eᵢ`, `vᵢ = V eᵢ`
  have hUe : ∀ i : Fin q, Uᵀ * (U * ecol i) = ecol i := fun i => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hVe : ∀ i : Fin q, Vᵀ * (V * ecol i) = ecol i := fun i => by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have huo : ∀ i : Fin q, (U * ecol i)ᵀ * (U * ecol i) = 1 := fun i => by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hUe, ecol_orthonormal]
  have hvo : ∀ i : Fin q, (V * ecol i)ᵀ * (V * ecol i) = 1 := fun i => by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hVe, ecol_orthonormal]
  have hnu : ∀ i : Fin q, ‖U * ecol i‖ = 1 := fun i => by
    rw [Frobenius.norm_mul_of_orthonormal hU, norm_ecol]
  have hnv : ∀ i : Fin q, ‖V * ecol i‖ = 1 := fun i => by
    rw [Frobenius.norm_mul_of_orthonormal hV, norm_ecol]
  -- the matrices `X_{ij}` with the `i`-th and `j`-th singular triplets removed (`X_{ii} = X_i`)
  set d : Fin q → Fin q → Fin q → ℝ := fun i j l => if l = i ∨ l = j then 0 else σ l with hd
  set Xd : Fin q → Fin q → Matrix m n ℝ := fun i j => U * Matrix.diagonal (d i j) * Vᵀ with hXd
  set D : Fin q → Fin q → Matrix m n ℝ := fun i j => F t X - F t (Xd i j) with hD
  have hFD : ∀ i j : Fin q, F t X - D i j = F t (Xd i j) := fun i j => by
    simp only [hD, sub_sub_cancel]
  have hXdr : ∀ i j : Fin q, (Xd i j).rank ≤ r := fun i j =>
    (rank_mul_mul_transpose_le _ _ _).trans hqr
  have hUXd : ∀ i j : Fin q, U * Uᵀ * Xd i j = Xd i j := fun i j => by
    simp only [hXd, ← Matrix.mul_assoc]; rw [Matrix.mul_assoc U Uᵀ U, hU, Matrix.mul_one]
  have hXdV : ∀ i j : Fin q, Xd i j * V * Vᵀ = Xd i j := fun i j => by
    simp only [hXd, Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᵀ V Vᵀ, hV, Matrix.one_mul]
  have huXd : ∀ i j : Fin q, (U * ecol i)ᵀ * Xd i j = 0 := fun i j => by
    rw [Matrix.transpose_mul]
    simp only [hXd, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, ← Matrix.mul_assoc,
      ecol_transpose_mul_diagonal]
    simp [hd]
  have hXdv : ∀ i j : Fin q, Xd i j * (V * ecol j) = 0 := fun i j => by
    simp only [hXd, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul, diagonal_mul_ecol]
    simp [hd]
  -- `‖X - X_{ij}‖ ≤ σᵢ + σⱼ` and `‖X - X_i‖ ≤ σᵢ`
  have hdiff : ∀ i j : Fin q, X - Xd i j =
      U * Matrix.diagonal (fun l => if l = i ∨ l = j then σ l else 0) * Vᵀ := fun i j => by
    rw [hXeq]
    simp only [hXd]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    have hfun : (fun l => σ l - d i j l) = fun l => if l = i ∨ l = j then σ l else 0 := by
      funext l
      simp only [hd]
      split_ifs <;> ring
    rw [hfun]
  have hnormdiag : ∀ i j : Fin q, ‖X - Xd i j‖ ^ 2 =
      ∑ l, (if l = i ∨ l = j then σ l else 0) ^ 2 := fun i j => by
    rw [hdiff, Frobenius.norm_mul_transpose_of_orthonormal hV,
      Frobenius.norm_mul_of_orthonormal hU, frob_sq]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Matrix.diagonal_apply_eq]
    · intro b _ hba
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hba)]
      ring
    · simp
  have hXd2 : ∀ i j : Fin q, ‖X - Xd i j‖ ≤ σ i + σ j := fun i j => by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (add_pos (hσ i) (hσ j)).le two_ne_zero,
      hnormdiag]
    calc ∑ l, (if l = i ∨ l = j then σ l else 0) ^ 2
        ≤ ∑ l, ((if l = i then σ l ^ 2 else 0) + (if l = j then σ l ^ 2 else 0)) :=
          Finset.sum_le_sum fun l _ => by
            split_ifs <;> first | nlinarith [sq_nonneg (σ l)] | (exfalso; tauto)
      _ = σ i ^ 2 + σ j ^ 2 := by simp [Finset.sum_add_distrib]
      _ ≤ (σ i + σ j) ^ 2 := by nlinarith [hσ i, hσ j]
  have hXd1 : ∀ i : Fin q, ‖X - Xd i i‖ ≤ σ i := fun i => by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (hσ i).le two_ne_zero, hnormdiag]
    simp only [or_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hDn : ∀ i j : Fin q, ‖D i j‖ ≤ L * (σ i + σ j) := fun i j =>
    (hF t _ _).trans (mul_le_mul_of_nonneg_left (hXd2 i j) hL)
  have hDn1 : ∀ i : Fin q, ‖D i i‖ ≤ L * σ i := fun i =>
    (hF t _ _).trans (mul_le_mul_of_nonneg_left (hXd1 i) hL)
  -- the generators (A.14)–(A.21)
  set WL₀ : Matrix m (Fin q) ℝ := Matrix.of fun a i => (D i i * (V * ecol i)) a 0 with hWL₀
  set WR₀ : Matrix (Fin q) n ℝ := Matrix.of fun i b => ((U * ecol i)ᵀ * D i i) 0 b with hWR₀
  set C : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun i j => (Uᵀ * D i j * V) i j with hC
  set Γ : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun i j => C i j / (σ i + σ j) with hΓ
  set Si : Matrix (Fin q) (Fin q) ℝ := Matrix.diagonal fun i => (σ i)⁻¹ with hSi
  set WL : Matrix m (Fin q) ℝ := P * WL₀ with hWL
  set WR : Matrix (Fin q) n ℝ := WR₀ * Q with hWR
  set Gl : Matrix m m ℝ := WL * Si * Uᵀ + U * Γ * Uᵀ with hGl
  set Gr : Matrix n n ℝ := V * Si * WR + V * Γ * Vᵀ with hGr
  have hWL₀e : ∀ i : Fin q, WL₀ * ecol i = D i i * (V * ecol i) := fun i => by
    ext a o
    rw [mul_ecol_apply, hWL₀, Matrix.of_apply, Subsingleton.elim o 0]
  have hWR₀e : ∀ i : Fin q, (ecol i)ᵀ * WR₀ = (U * ecol i)ᵀ * D i i := fun i => by
    ext o b
    rw [ecol_transpose_mul_apply, hWR₀, Matrix.of_apply, Subsingleton.elim o 0]
  -- `|Γᵢⱼ| ≤ L`
  have hCn : ∀ i j : Fin q, |C i j| ≤ L * (σ i + σ j) := fun i j => by
    simp only [hC, Matrix.of_apply]
    refine (Frobenius.abs_apply_le_norm _ i j).trans ?_
    calc ‖Uᵀ * D i j * V‖ ≤ ‖Uᵀ * D i j‖ * specNorm V := frob_mul_le' _ _
      _ ≤ (specNorm Uᵀ * ‖D i j‖) * 1 :=
          mul_le_mul (frob_mul_le _ _) (specNorm_le_one_of_orthonormal hV) (specNorm_nonneg _)
            (mul_nonneg (specNorm_nonneg _) (norm_nonneg _))
      _ ≤ (1 * ‖D i j‖) * 1 := by
          rw [specNorm_transpose]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (specNorm_le_one_of_orthonormal hU) (norm_nonneg _))
            zero_le_one
      _ ≤ L * (σ i + σ j) := by rw [one_mul, mul_one]; exact hDn i j
  have hΓn : ∀ i j : Fin q, |Γ i j| ≤ L := fun i j => by
    have hs : 0 < σ i + σ j := add_pos (hσ i) (hσ j)
    simp only [hΓ, Matrix.of_apply]
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hCn i j
  have hΓF : ‖Γ‖ ≤ q * L := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg q) hL) two_ne_zero,
      frob_sq]
    calc ∑ i, ∑ j, Γ i j ^ 2 ≤ ∑ _i : Fin q, ∑ _j : Fin q, L ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hΓn i j) 2
      _ = (q * L) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the normal columns and rows of the generators: `‖(I - U Uᵀ)(F(X) - F(X_i)) vᵢ‖ ≤ L σᵢ`
  have hcolL : ∀ i : Fin q, ‖P * (D i i * (V * ecol i))‖ ≤ L * σ i := fun i => by
    calc ‖P * (D i i * (V * ecol i))‖ ≤ specNorm P * ‖D i i * (V * ecol i)‖ := frob_mul_le _ _
      _ ≤ 1 * (‖D i i‖ * specNorm (V * ecol i)) :=
          mul_le_mul hPm.specNorm_le_one (frob_mul_le' _ _) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (‖D i i‖ * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (specNorm_le_one_of_orthonormal (hvo i)) (norm_nonneg _)) zero_le_one
      _ ≤ L * σ i := by rw [one_mul, mul_one]; exact hDn1 i
  have hrowL : ∀ i : Fin q, ‖(U * ecol i)ᵀ * D i i * Q‖ ≤ L * σ i := fun i => by
    calc ‖(U * ecol i)ᵀ * D i i * Q‖ ≤ ‖(U * ecol i)ᵀ * D i i‖ * specNorm Q := frob_mul_le' _ _
      _ ≤ (specNorm (U * ecol i)ᵀ * ‖D i i‖) * 1 :=
          mul_le_mul (frob_mul_le _ _) hQm.specNorm_le_one (specNorm_nonneg _)
            (mul_nonneg (specNorm_nonneg _) (norm_nonneg _))
      _ ≤ (1 * ‖D i i‖) * 1 := by
          rw [specNorm_transpose]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (specNorm_le_one_of_orthonormal (huo i)) (norm_nonneg _)) zero_le_one
      _ ≤ L * σ i := by rw [one_mul, mul_one]; exact hDn1 i
  have hWLS : ‖WL * Si‖ ≤ √q * L := by
    have h2 : ‖WL * Si‖ ^ 2 ≤ q * L ^ 2 := by
      rw [frob_sq_eq_sum_cols]
      calc ∑ i : Fin q, ‖WL * Si * ecol i‖ ^ 2 ≤ ∑ _i : Fin q, L ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have hci : WL * Si * ecol i = (σ i)⁻¹ • (P * (D i i * (V * ecol i))) := by
              rw [Matrix.mul_assoc, hSi, diagonal_mul_ecol, Matrix.mul_smul, hWL,
                Matrix.mul_assoc, hWL₀e]
            rw [hci, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hσ i).le)]
            refine pow_le_pow_left₀ (mul_nonneg (inv_nonneg.2 (hσ i).le) (norm_nonneg _)) ?_ 2
            rw [inv_mul_le_iff₀ (hσ i)]
            linarith [hcolL i]
        _ = q * L ^ 2 := by simp
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hL, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt h2
  have hSWR : ‖Si * WR‖ ≤ √q * L := by
    have h2 : ‖Si * WR‖ ^ 2 ≤ q * L ^ 2 := by
      rw [frob_sq_eq_sum_rows]
      calc ∑ i : Fin q, ‖(ecol i)ᵀ * (Si * WR)‖ ^ 2 ≤ ∑ _i : Fin q, L ^ 2 :=
            Finset.sum_le_sum fun i _ => by
            have hri : (ecol i)ᵀ * (Si * WR) = (σ i)⁻¹ • ((U * ecol i)ᵀ * D i i * Q) := by
              rw [← Matrix.mul_assoc, hSi, ecol_transpose_mul_diagonal, Matrix.smul_mul, hWR,
                ← Matrix.mul_assoc (ecol i)ᵀ WR₀ Q, hWR₀e]
            rw [hri, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hσ i).le)]
            refine pow_le_pow_left₀ (mul_nonneg (inv_nonneg.2 (hσ i).le) (norm_nonneg _)) ?_ 2
            rw [inv_mul_le_iff₀ (hσ i)]
            linarith [hrowL i]
        _ = q * L ^ 2 := by simp
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hL, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt h2
  have hqrR : (q : ℝ) ≤ r := by exact_mod_cast hqr
  have hKG : √q * L + q * L ≤ (r + √r) * L := by
    have h1 := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hqrR) hL
    have h2 := mul_le_mul_of_nonneg_right hqrR hL
    linarith
  -- the exact structure `G_L X + X G_R = W_L Vᵀ + U W_R + U C Vᵀ`
  have hUU' : ∀ M : Matrix (Fin q) n ℝ, Uᵀ * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hVV' : ∀ M : Matrix (Fin q) n ℝ, Vᵀ * (V * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hSd : ∀ M : Matrix (Fin q) n ℝ, Si * (Matrix.diagonal σ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hSi, Matrix.diagonal_mul_diagonal]
    convert Matrix.one_mul M
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hσ i).ne'
  have hdS : ∀ M : Matrix (Fin q) n ℝ, Matrix.diagonal σ * (Si * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hSi, Matrix.diagonal_mul_diagonal]
    convert Matrix.one_mul M
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hσ i).ne'
  have e1 : Gl * X = WL * Vᵀ + U * (Γ * (Matrix.diagonal σ * Vᵀ)) := by
    rw [hGl]
    conv_lhs => rw [hXeq]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hUU', hSd]
  have e2 : X * Gr = U * WR + U * (Matrix.diagonal σ * (Γ * Vᵀ)) := by
    rw [hGr]
    conv_lhs => rw [hXeq]
    simp only [Matrix.mul_add, Matrix.mul_assoc, hVV', hdS]
  have e3 : Γ * Matrix.diagonal σ + Matrix.diagonal σ * Γ = C := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [hΓ, Matrix.of_apply]
    have : 0 < σ i + σ j := add_pos (hσ i) (hσ j)
    field_simp
    ring
  have hGlGr : Gl * X + X * Gr = WL * Vᵀ + U * WR + U * C * Vᵀ := by
    rw [e1, e2, ← e3]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  refine ⟨Gl, Gr, ?_, ?_, ?_⟩
  · -- `‖G_L‖₂ ≤ K_G`
    rw [hGl]
    refine (WeylSingular.specNorm_add_le _ _).trans (le_trans ?_ hKG)
    refine add_le_add ?_ ?_
    · calc specNorm (WL * Si * Uᵀ) ≤ specNorm (WL * Si) * specNorm Uᵀ := specNorm_mul_le _ _
        _ ≤ specNorm (WL * Si) * 1 := by
            rw [specNorm_transpose]
            exact mul_le_mul_of_nonneg_left (specNorm_le_one_of_orthonormal hU)
              (specNorm_nonneg _)
        _ ≤ √q * L := by rw [mul_one]; exact (specNorm_le_frob _).trans hWLS
    · calc specNorm (U * Γ * Uᵀ) ≤ specNorm U * specNorm Γ * specNorm Uᵀ :=
            (specNorm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
        _ ≤ 1 * specNorm Γ * 1 := by
            rw [specNorm_transpose]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (specNorm_le_one_of_orthonormal hU)
              (specNorm_nonneg _)) (specNorm_le_one_of_orthonormal hU) (specNorm_nonneg _)
              (mul_nonneg zero_le_one (specNorm_nonneg _))
        _ ≤ q * L := by rw [one_mul, mul_one]; exact (specNorm_le_frob _).trans hΓF
  · -- `‖G_R‖₂ ≤ K_G`
    rw [hGr]
    refine (WeylSingular.specNorm_add_le _ _).trans (le_trans ?_ hKG)
    refine add_le_add ?_ ?_
    · calc specNorm (V * Si * WR) ≤ specNorm V * specNorm (Si * WR) := by
            rw [Matrix.mul_assoc]; exact specNorm_mul_le _ _
        _ ≤ 1 * specNorm (Si * WR) :=
            mul_le_mul_of_nonneg_right (specNorm_le_one_of_orthonormal hV) (specNorm_nonneg _)
        _ ≤ √q * L := by rw [one_mul]; exact (specNorm_le_frob _).trans hSWR
    · calc specNorm (V * Γ * Vᵀ) ≤ specNorm V * specNorm Γ * specNorm Vᵀ :=
            (specNorm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
        _ ≤ 1 * specNorm Γ * 1 := by
            rw [specNorm_transpose]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (specNorm_le_one_of_orthonormal hV)
              (specNorm_nonneg _)) (specNorm_le_one_of_orthonormal hV) (specNorm_nonneg _)
              (mul_nonneg zero_le_one (specNorm_nonneg _))
        _ ≤ q * L := by rw [one_mul, mul_one]; exact (specNorm_le_frob _).trans hΓF
  · -- `‖E‖ ≤ E_G`
    have hE : F t X - Gl * X - X * Gr = F t X - (WL * Vᵀ + U * WR + U * C * Vᵀ) := by
      rw [← hGlGr, sub_sub]
    rw [hE]
    set E := F t X - (WL * Vᵀ + U * WR + U * C * Vᵀ) with hEdef
    -- the columns `E vⱼ` and the block `E (I - V Vᵀ)`
    have hEv : ∀ j : Fin q, E * (V * ecol j) =
        F t X * (V * ecol j) - P * (D j j * (V * ecol j)) - U * (C * ecol j) := fun j => by
      have t1 : WL * Vᵀ * (V * ecol j) = P * (D j j * (V * ecol j)) := by
        rw [Matrix.mul_assoc, hVe, hWL, Matrix.mul_assoc, hWL₀e]
      have t2 : U * WR * (V * ecol j) = 0 := by
        rw [hWR, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Q V, hQV, Matrix.zero_mul,
          Matrix.mul_zero, Matrix.mul_zero]
      have t3 : U * C * Vᵀ * (V * ecol j) = U * (C * ecol j) := by
        rw [Matrix.mul_assoc, hVe, Matrix.mul_assoc]
      rw [hEdef, Matrix.sub_mul, Matrix.add_mul, Matrix.add_mul, t1, t2, t3, add_zero,
        sub_add_eq_sub_sub]
    have hPEv : ∀ j : Fin q, P * (E * (V * ecol j)) = P * F t (Xd j j) * (V * ecol j) := fun j => by
      rw [hEv, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc P P, hPm.idem,
        ← Matrix.mul_assoc P U, hPU, Matrix.zero_mul, sub_zero, ← Matrix.mul_sub,
        ← Matrix.sub_mul, hFD, Matrix.mul_assoc]
    have hUEv : ∀ i j : Fin q, (Uᵀ * (E * (V * ecol j))) i 0 = (Uᵀ * F t (Xd i j) * V) i j := by
      intro i j
      rw [hEv, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc Uᵀ P, hUP, Matrix.zero_mul,
        sub_zero, ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, Matrix.sub_apply, mul_ecol_apply C,
        ← Matrix.mul_assoc Uᵀ (F t X), ← Matrix.mul_assoc (Uᵀ * F t X), mul_ecol_apply]
      simp only [hC, Matrix.of_apply]
      rw [← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub, hFD]
    have hEQ : E * Q = F t X * Q - U * WR := by
      have s1 : WL * Vᵀ * Q = 0 := by rw [Matrix.mul_assoc, hVQ, Matrix.mul_zero]
      have s2 : U * C * Vᵀ * Q = 0 := by rw [Matrix.mul_assoc, hVQ, Matrix.mul_zero]
      have s3 : U * WR * Q = U * WR := by
        rw [Matrix.mul_assoc, hWR, Matrix.mul_assoc, hQm.idem]
      rw [hEdef, Matrix.sub_mul, Matrix.add_mul, Matrix.add_mul, s1, s2, s3, zero_add, add_zero]
    have huEQ : ∀ i : Fin q, (U * ecol i)ᵀ * (E * Q) = (U * ecol i)ᵀ * F t (Xd i i) * Q :=
        fun i => by
      have hu1 : (U * ecol i)ᵀ * U = (ecol i)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
      rw [hEQ, Matrix.mul_sub, ← Matrix.mul_assoc _ U WR, hu1, hWR,
        ← Matrix.mul_assoc (ecol i)ᵀ WR₀ Q, hWR₀e, ← Matrix.mul_assoc (U * ecol i)ᵀ (F t X) Q,
        ← Matrix.sub_mul, ← Matrix.mul_sub, hFD]
    have hPEQ : P * (E * Q) = P * F t X * Q := by
      rw [hEQ, Matrix.mul_sub, ← Matrix.mul_assoc P U, hPU, Matrix.zero_mul, sub_zero,
        Matrix.mul_assoc]
    -- entrywise and columnwise bounds from Lemma A.1
    have hentry : ∀ i j : Fin q, |(Uᵀ * F t (Xd i j) * V) i j| ≤ ε := fun i j => by
      have h1 := norm_transpose_mul_rhs_mul_le_mul hN hrm hrn (hXdr i j) (huXd i j) (hXdv i j) t
      rw [hnu i, hnv j, mul_one, mul_one, norm_fin_one] at h1
      have h2 : ((U * ecol i)ᵀ * F t (Xd i j) * (V * ecol j)) 0 0 =
          (Uᵀ * F t (Xd i j) * V) i j := by
        rw [Matrix.transpose_mul, ← entry_eq_ecol (Uᵀ * F t (Xd i j) * V) i j]
        simp only [Matrix.mul_assoc]
      rwa [h2] at h1
    have hb : ∀ j : Fin q, ‖Uᵀ * (E * (V * ecol j))‖ ^ 2 ≤ q * ε ^ 2 := fun j => by
      rw [frob_sq]
      calc ∑ i : Fin q, ∑ o : Fin 1, (Uᵀ * (E * (V * ecol j))) i o ^ 2
          = ∑ i : Fin q, (Uᵀ * F t (Xd i j) * V) i j ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Fin.sum_univ_one, hUEv]
        _ ≤ ∑ _i : Fin q, ε ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hentry i j) 2
        _ = q * ε ^ 2 := by simp
    have hc : ∀ j : Fin q, ‖P * (E * (V * ecol j))‖ ≤ ε := fun j => by
      rw [hPEv]
      have h : ‖(1 - U * Uᵀ) * F t (Xd j j) * (V * ecol j)‖ ≤ ε * ‖V * ecol j‖ :=
        norm_compl_mul_rhs_mul_le hN hrm hrn (hXdr j j) hU (hUXd j j) (hXdv j j) t
      rw [hnv j, mul_one] at h
      exact h
    have hrow : ∀ i : Fin q, ‖(U * ecol i)ᵀ * (E * Q)‖ ≤ ε := fun i => by
      rw [huEQ]
      have h : ‖(U * ecol i)ᵀ * F t (Xd i i) * (1 - V * Vᵀ)‖ ≤ ε * ‖U * ecol i‖ :=
        norm_mul_rhs_mul_compl_le hN hrm hrn (hXdr i i) hV (hXdV i i) (huXd i i) t
      rw [hnu i, mul_one] at h
      exact h
    have hQnorm : ‖Q‖ ^ 2 = Fintype.card n - q := by
      rw [frob_sq_eq_trace, hQm.symm, hQm.idem, hQdef, Matrix.trace_sub, Matrix.trace_one,
        trace_mul_transpose hV, Fintype.card_fin]
    have hPFQ : ‖P * F t X * Q‖ ^ 2 ≤ (Fintype.card n - q) * ε ^ 2 := by
      rw [frob_sq_eq_sum_cols, ← hQnorm, frob_sq_eq_sum_cols Q, Finset.sum_mul]
      refine Finset.sum_le_sum fun b _ => ?_
      have h : ‖(1 - U * Uᵀ) * F t X * (Q * ecol b)‖ ≤ ε * ‖Q * ecol b‖ :=
        norm_compl_mul_rhs_mul_le hN hrm hrn hX hU hUX
          (by rw [← Matrix.mul_assoc, hXQ, Matrix.zero_mul]) t
      rw [Matrix.mul_assoc (P * F t X)]
      calc ‖P * F t X * (Q * ecol b)‖ ^ 2 ≤ (ε * ‖Q * ecol b‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ‖Q * ecol b‖ ^ 2 * ε ^ 2 := by ring
    -- Pythagoras and the final count
    have hsplitc : ∀ c : Matrix m (Fin 1) ℝ, ‖c‖ ^ 2 = ‖Uᵀ * c‖ ^ 2 + ‖P * c‖ ^ 2 := fun c =>
      frob_sq_eq_proj_add_compl hU c
    have hsplitn : ∀ Z : Matrix m n ℝ, ‖Z‖ ^ 2 = ‖Uᵀ * Z‖ ^ 2 + ‖P * Z‖ ^ 2 := fun Z =>
      frob_sq_eq_proj_add_compl hU Z
    have hsplitE : ‖E‖ ^ 2 = ‖E * V‖ ^ 2 + ‖E * Q‖ ^ 2 := by
      have h : ‖Eᵀ‖ ^ 2 = ‖Vᵀ * Eᵀ‖ ^ 2 + ‖(1 - V * Vᵀ) * Eᵀ‖ ^ 2 :=
        frob_sq_eq_proj_add_compl hV Eᵀ
      have hQE : (1 - V * Vᵀ) * Eᵀ = (E * Q)ᵀ := by rw [Matrix.transpose_mul, hQm.symm]
      rw [hQE, ← Matrix.transpose_mul, Frobenius.norm_transpose, Frobenius.norm_transpose,
        Frobenius.norm_transpose] at h
      exact h
    have hEV : ‖E * V‖ ^ 2 ≤ q * (q * ε ^ 2 + ε ^ 2) := by
      rw [frob_sq_eq_sum_cols]
      calc ∑ j : Fin q, ‖E * V * ecol j‖ ^ 2 ≤ ∑ _j : Fin q, (q * ε ^ 2 + ε ^ 2) :=
            Finset.sum_le_sum fun j _ => by
              rw [Matrix.mul_assoc, hsplitc]
              have h2 := pow_le_pow_left₀ (norm_nonneg _) (hc j) 2
              linarith [hb j]
        _ = q * (q * ε ^ 2 + ε ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hEQn : ‖E * Q‖ ^ 2 ≤ q * ε ^ 2 + (Fintype.card n - q) * ε ^ 2 := by
      rw [hsplitn, hPEQ]
      have hUEQ : ‖Uᵀ * (E * Q)‖ ^ 2 ≤ q * ε ^ 2 := by
        rw [frob_sq_eq_sum_rows]
        calc ∑ i : Fin q, ‖(ecol i)ᵀ * (Uᵀ * (E * Q))‖ ^ 2 ≤ ∑ _i : Fin q, ε ^ 2 :=
              Finset.sum_le_sum fun i _ => by
                rw [← Matrix.mul_assoc, ← Matrix.transpose_mul]
                exact pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
          _ = q * ε ^ 2 := by simp
      linarith [hPFQ]
    have hm1 : (q : ℝ) + 1 ≤ Fintype.card m := by exact_mod_cast (by omega : q + 1 ≤ Fintype.card m)
    have hn1 : (q : ℝ) + 1 ≤ Fintype.card n := by exact_mod_cast (by omega : q + 1 ≤ Fintype.card n)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have htot : ‖E‖ ^ 2 ≤ (Fintype.card m * Fintype.card n) * ε ^ 2 := by
      rw [hsplitE]
      have hcount : (q : ℝ) * (q + 1) + Fintype.card n ≤ Fintype.card m * Fintype.card n := by
        have h1 := mul_le_mul (show (q : ℝ) ≤ Fintype.card m - 1 by linarith) hn1 (by positivity)
          (by linarith)
        have h2 : ((Fintype.card m : ℝ) - 1) * Fintype.card n =
            Fintype.card m * Fintype.card n - Fintype.card n := by ring
        linarith
      have h3 := mul_le_mul_of_nonneg_right hcount (sq_nonneg ε)
      have hsum : (q : ℝ) * (q * ε ^ 2 + ε ^ 2) + (q * ε ^ 2 + (Fintype.card n - q) * ε ^ 2) =
          ((q : ℝ) * (q + 1) + Fintype.card n) * ε ^ 2 := by ring
      linarith [hEV, hEQn]
    have hmn : (0 : ℝ) ≤ Fintype.card m * Fintype.card n := by positivity
    rw [← Real.sqrt_sq (norm_nonneg E), ← Real.sqrt_sq hε0, ← Real.sqrt_mul hmn]
    exact Real.sqrt_le_sqrt htot

end Generators


/-! ### The comparison point without differential inclusions (Lemmas A.3 and 4.2) -/

section Construction

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- `‖c A‖₂ = |c| ‖A‖₂` (auxiliary). -/
private theorem specNorm_smul' (c : ℝ) (A : Matrix m n ℝ) :
    specNorm (c • A) = |c| * specNorm A := by
  unfold specNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

omit [DecidableEq m] in
private theorem specNorm_zero' : specNorm (0 : Matrix m n ℝ) = 0 := by
  unfold specNorm; simp

omit [DecidableEq m] in
private theorem specNorm_one_add_smul_le {G : Matrix n n ℝ} {δ K : ℝ} (hδ : 0 ≤ δ)
    (hG : specNorm G ≤ K) : specNorm (1 + δ • G) ≤ 1 + δ * K := by
  refine (WeylSingular.specNorm_add_le _ _).trans (add_le_add specNorm_one_le ?_)
  rw [specNorm_smul', abs_of_nonneg hδ]
  exact mul_le_mul_of_nonneg_left hG hδ

private theorem expand_step (G : Matrix m m ℝ) (Lm : Matrix m m ℝ) (Y₀ : Matrix m n ℝ)
    (R : Matrix n n ℝ) (H : Matrix n n ℝ) (δ : ℝ) :
    (1 + δ • G) * Lm * Y₀ * (R * (1 + δ • H)) =
      Lm * Y₀ * R + δ • (G * (Lm * Y₀ * R) + Lm * Y₀ * R * H) +
        δ ^ 2 • (G * (Lm * Y₀ * R) * H) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc, smul_add, smul_smul]
  module

/-- The factors of the discrete comparison curve (auxiliary for arXiv 2608.17157, Lemma 4.2):
`L₀ = I`, `R₀ = I`, `L_{k+1} = (I + δ G_L) L_k`, `R_{k+1} = R_k (I + δ G_R)` with the
generators `(G_L, G_R) = (GLf, GRf)(t₀ + k δ, L_k Y₀ R_k)`. -/
private noncomputable def cmpSeq (GLf : ℝ → Matrix m n ℝ → Matrix m m ℝ)
    (GRf : ℝ → Matrix m n ℝ → Matrix n n ℝ) (Y₀ : Matrix m n ℝ) (t₀ δ : ℝ) :
    ℕ → Matrix m m ℝ × Matrix n n ℝ
  | 0 => (1, 1)
  | k + 1 =>
    ((1 + δ • GLf (t₀ + k * δ) ((cmpSeq GLf GRf Y₀ t₀ δ k).1 * Y₀ * (cmpSeq GLf GRf Y₀ t₀ δ k).2))
        * (cmpSeq GLf GRf Y₀ t₀ δ k).1,
      (cmpSeq GLf GRf Y₀ t₀ δ k).2 *
        (1 + δ • GRf (t₀ + k * δ)
          ((cmpSeq GLf GRf Y₀ t₀ δ k).1 * Y₀ * (cmpSeq GLf GRf Y₀ t₀ δ k).2)))

/-- **Comparison point of Lemma 4.2 from bounded generators** (arXiv 2608.17157, Lemma A.3 and
the first part of Lemma 4.2, without differential inclusions).  Let `F` be `L`-Lipschitz in `X`
and jointly continuous, and let every `X` of rank `≤ r` have generators with
`‖G_L‖₂, ‖G_R‖₂ ≤ K` and `‖F(t, X) - G_L X - X G_R‖ ≤ E` (the conclusion of Lemma A.2,
`exists_generators`).  If `rank Y₀ ≤ r` and `A` solves `A' = F(t, A)` on `[t₀, t₀ + s]` with
`A(t₀) = Y₀`, then for every `η > E s e^{L s}` there are `L`, `R` with `‖L‖₂ ≤ e^{K s}`,
`‖R - I‖₂ ≤ e^{K s} - 1` and `‖L Y₀ R - A(t₀ + s)‖ ≤ η`: the bounds (A.33)–(A.34) of the paper's
curve `Ỹ(s) = L(s) Y₀ R(s)` at time `s`.  The paper obtains `L(s)`, `R(s)` from an absolutely
continuous solution of the differential inclusion (A.36) (Deimling's existence theorem); here
they are the factors of an Euler-type polygon `L_{k+1} = (I + δ G_L) L_k`,
`R_{k+1} = R_k (I + δ G_R)` with generators chosen at the grid points, and the discrete Grönwall
argument with a fine grid (uniform continuity of `τ ↦ F(τ, A(τ))`) gives every `η` above the
paper's bound.  Neither invertibility of `L`, `R` nor `rank Ỹ = r` is claimed. -/
theorem exists_comparison_point {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L K E : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hK : 0 ≤ K) (hFc : Continuous (Function.uncurry F))
    {r : ℕ}
    (hgen : ∀ t (X : Matrix m n ℝ), X.rank ≤ r → ∃ (Gl : Matrix m m ℝ) (Gr : Matrix n n ℝ),
      specNorm Gl ≤ K ∧ specNorm Gr ≤ K ∧ ‖F t X - Gl * X - X * Gr‖ ≤ E)
    {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank ≤ r) {A : ℝ → Matrix m n ℝ} {t₀ s : ℝ} (hs : 0 ≤ s)
    (hA : ODESolution F A t₀ (t₀ + s)) (hA₀ : A t₀ = Y₀) {η : ℝ}
    (hη : E * s * Real.exp (L * s) < η) :
    ∃ (Lm : Matrix m m ℝ) (R : Matrix n n ℝ), specNorm Lm ≤ Real.exp (K * s) ∧
      specNorm (R - 1) ≤ Real.exp (K * s) - 1 ∧ ‖Lm * Y₀ * R - A (t₀ + s)‖ ≤ η := by
  choose! GLf GRf hG using hgen
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hG t₀ Y₀ hY₀).2.2
  rcases eq_or_lt_of_le hs with rfl | hs0
  · refine ⟨1, 1, ?_, ?_, ?_⟩
    · rw [mul_zero, Real.exp_zero]; exact specNorm_one_le
    · rw [mul_zero, Real.exp_zero, sub_self, sub_self]
      exact le_of_eq specNorm_zero'
    · rw [add_zero, hA₀, Matrix.one_mul, Matrix.mul_one, sub_self, norm_zero]
      rw [mul_zero, zero_mul] at hη
      exact hη.le
  -- parameters: `γ` for the uniform continuity of `g`, the grid `δ = s / N`
  set g : ℝ → Matrix m n ℝ := fun τ => F τ (A τ) with hg
  have hgc : ContinuousOn g (Icc t₀ (t₀ + s)) :=
    hFc.comp_continuousOn (continuousOn_id.prodMk hA.cont)
  set B₀ : ℝ := Real.exp (2 * K * s) * ‖Y₀‖ with hB₀
  have hB₀0 : 0 ≤ B₀ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hes : 0 < s * Real.exp (L * s) := mul_pos hs0 (Real.exp_pos _)
  have hes' : s * Real.exp (L * s) ≠ 0 := hes.ne'
  set γ : ℝ := (η - E * s * Real.exp (L * s)) / (2 * (s * Real.exp (L * s))) with hγ
  have hγ0 : 0 < γ := div_pos (by linarith) (by linarith)
  have hγη : s * Real.exp (L * s) * (E + 2 * γ) = η := by
    rw [hγ]; field_simp; ring
  obtain ⟨δ₀, hδ₀, huc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hgc) γ hγ0
  have hKB : 0 < K ^ 2 * B₀ + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg K) hB₀0) one_pos
  set δ₁ : ℝ := min δ₀ (γ / (K ^ 2 * B₀ + 1)) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ (div_pos hγ0 hKB)
  obtain ⟨N, hN⟩ := exists_nat_gt (s / δ₁)
  have hN0 : (0 : ℝ) < N := (div_pos hs0 hδ₁0).trans hN
  set δ : ℝ := s / N with hδ
  have hδ0 : 0 < δ := div_pos hs0 hN0
  have hδδ₁ : δ < δ₁ := by
    rw [hδ, div_lt_iff₀ hN0]
    rw [div_lt_iff₀ hδ₁0] at hN
    linarith
  have hδδ₀ : δ < δ₀ := hδδ₁.trans_le (min_le_left _ _)
  have hδγ : δ * (K ^ 2 * B₀) ≤ γ := by
    have h1 : δ < γ / (K ^ 2 * B₀ + 1) := hδδ₁.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hKB] at h1
    have h2 : δ * (K ^ 2 * B₀) ≤ δ * (K ^ 2 * B₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    linarith
  have hN0' : (N : ℝ) ≠ 0 := hN0.ne'
  have hNδ : (N : ℝ) * δ = s := by rw [hδ]; field_simp
  set c : ℝ := E + γ + δ * (K ^ 2 * B₀) with hc
  have hc0 : 0 ≤ c := by
    have := mul_nonneg hδ0.le (mul_nonneg (sq_nonneg K) hB₀0)
    rw [hc]; linarith
  have hK1 : 0 ≤ 1 + δ * K := add_nonneg zero_le_one (mul_nonneg hδ0.le hK)
  have hL1 : 0 ≤ 1 + δ * L := add_nonneg zero_le_one (mul_nonneg hδ0.le hL)
  -- the discrete curve
  set p := cmpSeq GLf GRf Y₀ t₀ δ with hp
  have hp0 : p 0 = (1, 1) := rfl
  have hpS : ∀ k : ℕ, p (k + 1) =
      ((1 + δ • GLf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)) * (p k).1,
        (p k).2 * (1 + δ • GRf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2))) := fun k => rfl
  have hrank : ∀ k : ℕ, ((p k).1 * Y₀ * (p k).2).rank ≤ r := fun k =>
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hY₀
  have hbase : 1 + δ * K ≤ Real.exp (δ * K) := by linarith [Real.add_one_le_exp (δ * K)]
  have hfac : ∀ k : ℕ, specNorm (p k).1 ≤ (1 + δ * K) ^ k ∧ specNorm (p k).2 ≤ (1 + δ * K) ^ k ∧
      specNorm ((p k).2 - 1) ≤ (1 + δ * K) ^ k - 1 := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> simp only [hp0, pow_zero, sub_self]
      · exact specNorm_one_le
      · exact specNorm_one_le
      · exact le_of_eq specNorm_zero'
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hGl := (hG (t₀ + k * δ) _ (hrank k)).1
      have hGr := (hG (t₀ + k * δ) _ (hrank k)).2.1
      rw [hpS k, pow_succ]
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · calc specNorm ((1 + δ • GLf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)) * (p k).1)
            ≤ specNorm (1 + δ • GLf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)) * specNorm (p k).1 :=
              specNorm_mul_le _ _
          _ ≤ (1 + δ * K) * (1 + δ * K) ^ k :=
              mul_le_mul (specNorm_one_add_smul_le hδ0.le hGl) h1 (specNorm_nonneg _) hK1
          _ = (1 + δ * K) ^ k * (1 + δ * K) := by ring
      · calc specNorm ((p k).2 * (1 + δ • GRf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)))
            ≤ specNorm (p k).2 * specNorm (1 + δ • GRf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)) :=
              specNorm_mul_le _ _
          _ ≤ (1 + δ * K) ^ k * (1 + δ * K) :=
              mul_le_mul h2 (specNorm_one_add_smul_le hδ0.le hGr) (specNorm_nonneg _)
                (pow_nonneg hK1 k)
      · have heq : (p k).2 * (1 + δ • GRf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)) - 1 =
            ((p k).2 - 1) + δ • ((p k).2 * GRf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)) := by
          rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]; abel
        rw [heq]
        calc specNorm (((p k).2 - 1) + δ • ((p k).2 * GRf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2)))
            ≤ specNorm ((p k).2 - 1) +
                specNorm (δ • ((p k).2 * GRf (t₀ + k * δ) ((p k).1 * Y₀ * (p k).2))) :=
              WeylSingular.specNorm_add_le _ _
          _ ≤ ((1 + δ * K) ^ k - 1) + δ * ((1 + δ * K) ^ k * K) := by
              refine add_le_add h3 ?_
              rw [specNorm_smul', abs_of_nonneg hδ0.le]
              exact mul_le_mul_of_nonneg_left ((specNorm_mul_le _ _).trans
                (mul_le_mul h2 hGr (specNorm_nonneg _) (pow_nonneg hK1 k))) hδ0.le
          _ = (1 + δ * K) ^ k * (1 + δ * K) - 1 := by ring
  -- growth bounds on the grid
  have hpow : ∀ k ≤ N, (1 + δ * K) ^ k ≤ Real.exp (K * s) := fun k hk => by
    calc (1 + δ * K) ^ k ≤ Real.exp (δ * K) ^ k :=
          pow_le_pow_left₀ hK1 hbase k
      _ = Real.exp (K * (k * δ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (K * s) := by
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hK)
          rw [← hNδ]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hδ0.le
  have hXb : ∀ k ≤ N, ‖(p k).1 * Y₀ * (p k).2‖ ≤ B₀ := fun k hk => by
    obtain ⟨h1, h2, -⟩ := hfac k
    calc ‖(p k).1 * Y₀ * (p k).2‖ ≤ ‖(p k).1 * Y₀‖ * specNorm (p k).2 := frob_mul_le' _ _
      _ ≤ (specNorm (p k).1 * ‖Y₀‖) * specNorm (p k).2 :=
          mul_le_mul_of_nonneg_right (frob_mul_le _ _) (specNorm_nonneg _)
      _ ≤ (Real.exp (K * s) * ‖Y₀‖) * Real.exp (K * s) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (h1.trans (hpow k hk)) (norm_nonneg _))
            (h2.trans (hpow k hk)) (specNorm_nonneg _) (by positivity)
      _ = B₀ := by rw [hB₀, show 2 * K * s = K * s + K * s by ring, Real.exp_add]; ring
  -- the local Euler error of the exact solution
  have heul : ∀ k < N, ‖A (t₀ + (k + 1 : ℕ) * δ) - A (t₀ + k * δ) - δ • g (t₀ + k * δ)‖ ≤
      γ * δ := fun k hk => by
    set a := t₀ + k * δ with ha
    have hk' : ((k : ℝ) + 1) * δ ≤ s := by
      rw [← hNδ]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hδ0.le
    have hae : a + δ = t₀ + ((k : ℝ) + 1) * δ := by rw [ha]; ring
    have hab : a + δ ≤ t₀ + s := by linarith
    have haI : a ∈ Icc t₀ (t₀ + s) :=
      ⟨by rw [ha]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hδ0.le),
        by linarith⟩
    have hsub : Icc a (a + δ) ⊆ Icc t₀ (t₀ + s) := Icc_subset_Icc haI.1 hab
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := fun τ => A τ - (τ - a) • g a) (f' := fun τ => g τ - (1 : ℝ) • g a) (C := γ)
      ((hA.cont.mono hsub).sub
        ((continuous_id.sub continuous_const).smul continuous_const).continuousOn)
      (fun τ hτ => by
        have h1 := hA.deriv τ ⟨haI.1.trans hτ.1, hτ.2.trans_le hab⟩
        have h2 : HasDerivAt (fun τ : ℝ => (τ - a) • g a) ((1 : ℝ) • g a) τ :=
          ((hasDerivAt_id τ).sub_const a).smul_const (g a)
        exact h1.sub h2.hasDerivWithinAt)
      (fun τ hτ => by
        rw [one_smul, ← dist_eq_norm]
        refine (huc τ (hsub (Ico_subset_Icc_self hτ)) a haI ?_).le
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hτ.1])]
        linarith [hτ.2])
      (a + δ) ⟨by linarith, le_rfl⟩
    have e1 : t₀ + ((k + 1 : ℕ) : ℝ) * δ = a + δ := by rw [ha]; push_cast; ring
    rw [e1]
    simp only [sub_self, zero_smul, sub_zero, add_sub_cancel_left] at hmvt
    calc ‖A (a + δ) - A a - δ • g a‖ = ‖A (a + δ) - δ • g a - A a‖ := by congr 1; abel
      _ ≤ γ * δ := hmvt
  -- the discrete Grönwall bound
  have herr : ∀ k ≤ N, ‖(p k).1 * Y₀ * (p k).2 - A (t₀ + k * δ)‖ ≤
      k * δ * (1 + δ * L) ^ k * c := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hp0, Nat.cast_zero, zero_mul, add_zero, Matrix.one_mul, Matrix.mul_one, hA₀,
        sub_self, norm_zero]
      simp
    | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have ihk := ih hkN.le
      set X := (p k).1 * Y₀ * (p k).2 with hX
      set Gl := GLf (t₀ + k * δ) X with hGl
      set Gr := GRf (t₀ + k * δ) X with hGr
      obtain ⟨hGl1, hGr1, hEk⟩ := hG (t₀ + k * δ) X (hrank k)
      have hX1 : (p (k + 1)).1 * Y₀ * (p (k + 1)).2 =
          X + δ • (Gl * X + X * Gr) + δ ^ 2 • (Gl * X * Gr) := by
        rw [hpS k]
        exact expand_step _ _ _ _ _ _
      have hid : (p (k + 1)).1 * Y₀ * (p (k + 1)).2 - A (t₀ + (k + 1 : ℕ) * δ) =
          (X - A (t₀ + k * δ)) + δ • (F (t₀ + k * δ) X - g (t₀ + k * δ)) -
            δ • (F (t₀ + k * δ) X - Gl * X - X * Gr) + δ ^ 2 • (Gl * X * Gr) -
            (A (t₀ + (k + 1 : ℕ) * δ) - A (t₀ + k * δ) - δ • g (t₀ + k * δ)) := by
        rw [hX1]; module
      have hGXG : ‖Gl * X * Gr‖ ≤ K * B₀ * K := by
        calc ‖Gl * X * Gr‖ ≤ ‖Gl * X‖ * specNorm Gr := frob_mul_le' _ _
          _ ≤ (specNorm Gl * ‖X‖) * specNorm Gr :=
              mul_le_mul_of_nonneg_right (frob_mul_le _ _) (specNorm_nonneg _)
          _ ≤ (K * B₀) * K := mul_le_mul (mul_le_mul hGl1 (hXb k hkN.le) (norm_nonneg _) hK)
              hGr1 (specNorm_nonneg _) (mul_nonneg hK hB₀0)
      have hLip : ‖F (t₀ + k * δ) X - g (t₀ + k * δ)‖ ≤ L * ‖X - A (t₀ + k * δ)‖ :=
        hF _ _ _
      have hstep : ‖(p (k + 1)).1 * Y₀ * (p (k + 1)).2 - A (t₀ + (k + 1 : ℕ) * δ)‖ ≤
          (1 + δ * L) * ‖X - A (t₀ + k * δ)‖ + δ * c := by
        have tri5 : ∀ a₁ a₂ a₃ a₄ a₅ : Matrix m n ℝ,
            ‖a₁ + a₂ - a₃ + a₄ - a₅‖ ≤ ‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₄‖ + ‖a₅‖ := by
          intro a₁ a₂ a₃ a₄ a₅
          have h0 := norm_sub_le (a₁ + a₂ - a₃ + a₄) a₅
          have h1 := norm_add_le (a₁ + a₂ - a₃) a₄
          have h2 := norm_sub_le (a₁ + a₂) a₃
          have h3 := norm_add_le a₁ a₂
          linarith
        rw [hid]
        refine (tri5 _ _ _ _ _).trans ?_
        rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hδ0.le,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ δ ^ 2)]
        have h5 := heul k hkN
        have h3 : δ * ‖F (t₀ + k * δ) X - Gl * X - X * Gr‖ ≤ δ * E :=
          mul_le_mul_of_nonneg_left hEk hδ0.le
        have h2 : δ * ‖F (t₀ + k * δ) X - g (t₀ + k * δ)‖ ≤ δ * (L * ‖X - A (t₀ + k * δ)‖) :=
          mul_le_mul_of_nonneg_left hLip hδ0.le
        have h4 : δ ^ 2 * ‖Gl * X * Gr‖ ≤ δ ^ 2 * (K * B₀ * K) :=
          mul_le_mul_of_nonneg_left hGXG (by positivity)
        rw [hc]
        nlinarith [h2, h3, h4, h5]
      have hpow1 : 1 ≤ (1 + δ * L) ^ (k + 1) :=
        one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hδ0.le hL))
      calc _ ≤ (1 + δ * L) * ‖X - A (t₀ + k * δ)‖ + δ * c := hstep
        _ ≤ (1 + δ * L) * (k * δ * (1 + δ * L) ^ k * c) + δ * ((1 + δ * L) ^ (k + 1) * c) :=
            add_le_add (mul_le_mul_of_nonneg_left ihk hL1)
              (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hc0 hpow1) hδ0.le)
        _ = ((k + 1 : ℕ) : ℝ) * δ * (1 + δ * L) ^ (k + 1) * c := by push_cast; ring
  -- conclusion at `k = N`
  obtain ⟨h1, -, h3⟩ := hfac N
  refine ⟨(p N).1, (p N).2, h1.trans (hpow N le_rfl),
    h3.trans (by linarith [hpow N le_rfl]), ?_⟩
  have hfin := herr N le_rfl
  rw [hNδ] at hfin
  have hLpow : (1 + δ * L) ^ N ≤ Real.exp (L * s) := by
    calc (1 + δ * L) ^ N ≤ Real.exp (δ * L) ^ N :=
          pow_le_pow_left₀ hL1 (by linarith [Real.add_one_le_exp (δ * L)]) N
      _ = Real.exp (L * s) := by rw [← Real.exp_nat_mul, ← hNδ]; ring_nf
  calc _ ≤ s * (1 + δ * L) ^ N * c := hfin
    _ ≤ s * Real.exp (L * s) * (E + 2 * γ) := by
        have hc2 : c ≤ E + 2 * γ := by rw [hc]; linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left hLpow hs) hc2 hc0
          (mul_nonneg hs (Real.exp_pos _).le)
    _ = η := hγη

end Construction

/-! ### The comparison curve (Lemma 4.2) and the one-step estimate (Theorem 4.3) -/

section Comparison

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- The spectral norm satisfies the triangle inequality (auxiliary for arXiv 2608.17157,
Lemma 4.2; the library's `WeylSingular.specNorm_add_le`, kept under this name). -/
theorem specNorm_add_le (A B : Matrix m n ℝ) : specNorm (A + B) ≤ specNorm A + specNorm B :=
  WeylSingular.specNorm_add_le A B

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
`η = √(mn) ε_r s e^{L_F s}`, Eq. (4.7)).  The theorems that assume it are conditional on
Lemma 4.2; under the standing assumptions it holds for every `η > √(mn) ε_r s e^{L_F s}`
(`hasComparisonCurve_of_standing`). -/
def HasComparisonCurve (Y₀ As : Matrix m n ℝ) (η : ℝ) : Prop :=
  ∃ (L : Matrix m m ℝ) (R : Matrix n n ℝ), specNorm (R - 1) ≤ 1 / 2 ∧ ‖L * Y₀ * R - As‖ ≤ η

/-- **Theorem 4.3 (one-step error)** of arXiv 2608.17157.  Let `V₀` be orthonormal with
`Y₀ = Y₀ V₀ V₀ᵀ` (e.g. `Y₀ = U₀ S₀ V₀ᵀ`, `mul_mul_transpose_of_factored`), let `Y₁` be the
reduced K–L step from `V₀` with `X = Y₀ + ΔA`, and let a comparison point of Lemma 4.2 exist
within `η` of `A(s)` (`HasComparisonCurve`; the paper's Lemma 4.2 gives
`η = √(mn) ε_r s e^{L_F s}`).  Then `‖Y₁ - A(s)‖ ≤ 4 ‖Y₀ + ΔA - A(s)‖ + 5 η`.
The overlap `‖Q_s‖₂ ≤ 3` is derived (`exists_overlap_of_specNorm_sub_one_le`).  Conditional on
Lemma 4.2: the comparison point is the hypothesis `HasComparisonCurve`; the unconditional form,
with the paper's `η`, is `IsKLStep.one_step_error_of_standing`. -/
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
an explicit form of `C_T (δ + ε_r + d_h / h)`.  Conditional on Lemma 4.2 (hypothesis `hcmp`);
the unconditional form is `klStep_global_error_of_standing`. -/
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
(here `η = √(mn) ε_r e^{L_F h}` and `ε = ε_r` in the paper).  Conditional on Lemma 4.2, as
`klStep_global_error`; combine `klStep_global_error_of_standing` with `hdC` for the
unconditional form. -/
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
`C = M_p/p! (1/(p+1) + ∑ |bᵢ| cᵢ^p) + L C_st ∑ |bᵢ|` (quadrature and stage contributions). It
is a different constant from the core `RungeKuttaBUG.rkConst` (the Lipschitz stage constant of the
RK-BUG perturbation bound), hence the name; an earlier version of this file called it `rkConst`
(unification batch C8). -/
noncomputable def klRKConst {s : ℕ} (p : ℕ) (b c : Fin s → ℝ) (L M Cst : ℝ) : ℝ :=
  M / p ! * (1 / (p + 1) + ∑ i, |b i| * c i ^ p) + L * Cst * ∑ i, |b i|

/-- **Theorem 6.1, increment error** (arXiv 2608.17157).  For an explicit tableau with nodes
`cᵢ ∈ [0, 1]` and the moment conditions `∑ bᵢ cᵢ^k = 1/(k+1)` for `k < p` (`p ≥ 1`), an
`L`-Lipschitz field `F`, `g(τ) = F(τ, A(τ))` of class `C^p` on `[t, t + h]` with
`‖g^{(p)}‖ ≤ M_p`, and stage bounds `‖Zᵢ - A(t + cᵢ h)‖ ≤ C_st (h^p + h ε)` for `bᵢ ≠ 0`, the
increment error is `‖A(t) + h ∑ bᵢ F(t + cᵢ h, Zᵢ) - A(t + h)‖ ≤ C (h^{p+1} + h² ε)` with the
explicit `C = klRKConst p b c L M_p C_st`.  Stated on any real normed space. -/
theorem rk_increment_error {s p : ℕ} (hp : 0 < p) {F : ℝ → E → E} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (b c : Fin s → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1)
    (hord : ∀ k < p, ∑ i, b i * c i ^ k = 1 / (k + 1)) {t h M Cst ε : ℝ} (hh : 0 ≤ h)
    (hε : 0 ≤ ε) {A : ℝ → E} (hA : ODESolution F A t (t + h))
    (hg : ContDiffOn ℝ p (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin p (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M)
    {Z : Fin s → E} (hZ : ∀ i, b i ≠ 0 → ‖Z i - A (t + c i * h)‖ ≤ Cst * (h ^ p + h * ε)) :
    ‖A t + h • ∑ i, b i • F (t + c i * h) (Z i) - A (t + h)‖ ≤
      klRKConst p b c L M Cst * (h ^ (p + 1) + h ^ 2 * ε) := by
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
  unfold klRKConst
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

/-! ### Derivative bounds along the exact flow (Lemma 6.2) -/

section Lemma62

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a solution `A` of `A' = F(t, A)` of class `C¹` on `[a, b]` (`a < b`) with `F` jointly
continuous, the derivative within `[a, b]` is `F(·, A(·))` at every point, including the
endpoints (auxiliary for arXiv 2608.17157, Lemma 6.2). -/
theorem eqOn_derivWithin_of_odeSolution {F : ℝ → E → E} {A : ℝ → E} {a b : ℝ} (hab : a < b)
    (hF : Continuous (Function.uncurry F)) (hA : ODESolution F A a b)
    (hA1 : ContDiffOn ℝ 1 A (Icc a b)) :
    EqOn (derivWithin A (Icc a b)) (fun τ => F τ (A τ)) (Icc a b) := by
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hg : ContinuousOn (fun τ => F τ (A τ)) (Icc a b) :=
    hF.comp_continuousOn (continuousOn_id.prodMk hA.cont)
  have hd : ContinuousOn (derivWithin A (Icc a b)) (Icc a b) :=
    hA1.continuousOn_derivWithin hU le_rfl
  have hIco : EqOn (derivWithin A (Icc a b)) (fun τ => F τ (A τ)) (Ico a b) := by
    intro τ hτ
    have h1 : HasDerivWithinAt A (derivWithin A (Icc a b) τ) (Icc τ b) τ :=
      ((hA1.differentiableOn one_ne_zero τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt).mono
        (Icc_subset_Icc hτ.1 le_rfl)
    have h2 : HasDerivWithinAt A (F τ (A τ)) (Icc τ b) τ :=
      (hA.deriv τ hτ).mono Icc_subset_Ici_self
    exact (uniqueDiffOn_Icc hτ.2 τ (left_mem_Icc.2 hτ.2.le)).eq_deriv _ h1 h2
  exact hIco.of_subset_closure hd hg Ico_subset_Icc_self (by rw [closure_Ico hab.ne])

/-- If the solution `A` of `A' = F(t, A)` is `C^{q+1}` on `[a, b]`, then `g = F(·, A(·))` is
`C^q` there and `g^{(q)} = A^{(q+1)}` (auxiliary for arXiv 2608.17157, Lemma 6.2). -/
theorem rhs_contDiffOn_and_iteratedDerivWithin_eq {F : ℝ → E → E} {A : ℝ → E} {a b : ℝ}
    (hab : a < b) (hF : Continuous (Function.uncurry F)) (hA : ODESolution F A a b) {q : ℕ}
    (hAc : ContDiffOn ℝ (q + 1) A (Icc a b)) :
    ContDiffOn ℝ q (fun τ => F τ (A τ)) (Icc a b) ∧
      ∀ τ ∈ Icc a b, iteratedDerivWithin q (fun τ => F τ (A τ)) (Icc a b) τ =
        iteratedDerivWithin (q + 1) A (Icc a b) τ := by
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hA1 : ContDiffOn ℝ 1 A (Icc a b) :=
    hAc.of_le (by exact_mod_cast (by omega : 1 ≤ q + 1))
  have heq := eqOn_derivWithin_of_odeSolution hab hF hA hA1
  refine ⟨((contDiffOn_succ_iff_derivWithin hU).1 hAc).2.2.congr fun τ hτ => (heq hτ).symm,
    fun τ hτ => ?_⟩
  rw [iteratedDerivWithin_succ']
  exact (iteratedDerivWithin_congr heq hτ).symm

/-- **Lemma 6.2 (derivative bounds of `g_n`)** of arXiv 2608.17157, for every order `p`.  There
are constants `M_q` (`1 ≤ q ≤ p`) depending only on `p`, `B` and `M` such that, on every real
inner product space (e.g. `ℝ^{m×n}` with the Frobenius norm) and for every `F` of class `C^p`
with `‖F‖ ≤ B` and `‖D^j F‖ ≤ M` (`1 ≤ j ≤ p`) and every solution `A` of `A' = F(t, A)` on
`[a, b]`, the function `g(τ) = F(τ, A(τ))` (the paper's `g_n(s) = F(t_n + s, A_n(s))` with
`τ = t_n + s`) is `C^q` on `[a, b]` with `‖g^{(q)}‖ ≤ M_q`, uniformly in the interval and the
initial value.  Deviations: `D^j F` is the full `j`-th derivative of `(t, X) ↦ F(t, X)` on
`ℝ × E` (sup norm on the product); its restrictions are the mixed partials `∂_t^a D_X^b F`
(`a + b = j`) of (6.9), and conversely (6.9) bounds `‖D^j F‖` by `2^j M`.  `F` is `C^p` on all of
`ℝ × E` rather than on `[0, T] × ℝ^{m×n}`.  The Lipschitz constant `L_F` of the paper is not
needed separately (`‖D_X F‖ ≤ ‖DF‖ ≤ M`).  Proof: the library's singular-value-free bound
`OpenProblems.HighOrder.ODESolution.norm_iteratedDerivWithin_le` on `A^{(q+1)} = g^{(q)}`. -/
theorem exists_norm_iteratedDerivWithin_rhs_le (p : ℕ) (B M : ℝ) :
    ∃ Mq : ℕ → ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {F : ℝ → E → E} {A : ℝ → E} {a b : ℝ}, a < b → ContDiff ℝ p (Function.uncurry F) →
      IsBoundedField F B →
      (∀ j, 1 ≤ j → j ≤ p → ∀ x, ‖iteratedFDeriv ℝ j (Function.uncurry F) x‖ ≤ M) →
      ODESolution F A a b → ∀ q, 1 ≤ q → q ≤ p →
        ContDiffOn ℝ q (fun τ => F τ (A τ)) (Icc a b) ∧
          ∀ τ ∈ Icc a b, ‖iteratedDerivWithin q (fun τ => F τ (A τ)) (Icc a b) τ‖ ≤ Mq q := by
  classical
  choose C hC using fun q : ℕ =>
    OpenProblems.HighOrder.ODESolution.norm_iteratedDerivWithin_le.{u} q B
      (fun j => if j = 0 then B else M)
  refine ⟨C, ?_⟩
  intro E _ _ F A a b hab hF hB hM hA q hq1 hqp
  have hFq : ContDiff ℝ q (Function.uncurry F) := hF.of_le (by exact_mod_cast hqp)
  have hFc : Continuous (Function.uncurry F) := hFq.continuous
  have hMj : ∀ j ≤ q, ∀ x, ‖iteratedFDeriv ℝ j (Function.uncurry F) x‖ ≤
      if j = 0 then B else M := by
    intro j hj x
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hite : (if (0 : ℕ) = 0 then B else M) = B := by simp
      rw [hite, norm_iteratedFDeriv_zero]
      exact hB x.1 x.2
    · have hite : (if j = 0 then B else M) = M := by simp [hj0.ne']
      rw [hite]
      exact hM j hj0 (hj.trans hqp) x
  obtain ⟨hAc, hAb⟩ := hC q (R := ContinuousLinearMap.id ℝ E) ContinuousLinearMap.norm_id_le hFq
    hB hMj hA
  obtain ⟨hgc, hgeq⟩ := rhs_contDiffOn_and_iteratedDerivWithin_eq hab hFc hA hAc
  exact ⟨hgc, fun τ hτ => by rw [hgeq τ hτ]; exact hAb τ hτ⟩

/-- **Lemma 6.2 for `p = 2`, explicit constants** (arXiv 2608.17157): for `F` of class `C²` with
`‖F‖ ≤ B`, `‖DF‖ ≤ M`, `‖D²F‖ ≤ M` and a solution `A` on `[a, b]`, `g = F(·, A(·))` is `C²` with
`‖g'‖ ≤ M₁ = M (1 + B)` and `‖g''‖ ≤ M₂ = M (1 + B)² + M² (1 + B)` (the identities (6.11)–(6.12);
from the library bounds `ODESolution.norm_iteratedDerivWithin_two_le` and
`ODESolution.norm_iteratedDerivWithin_three_le` on the second and third derivatives of `A`).
Deviations as in `exists_norm_iteratedDerivWithin_rhs_le`. -/
theorem norm_iteratedDerivWithin_rhs_le_two {F : ℝ → E → E} {A : ℝ → E} {a b B M : ℝ}
    (hab : a < b) (hF : ContDiff ℝ 2 (Function.uncurry F)) (hB : IsBoundedField F B)
    (hD₁ : ∀ x, ‖fderiv ℝ (Function.uncurry F) x‖ ≤ M)
    (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) x‖ ≤ M) (hA : ODESolution F A a b) :
    ContDiffOn ℝ 2 (fun τ => F τ (A τ)) (Icc a b) ∧
      (∀ τ ∈ Icc a b, ‖iteratedDerivWithin 1 (fun τ => F τ (A τ)) (Icc a b) τ‖ ≤ M * (1 + B)) ∧
      ∀ τ ∈ Icc a b, ‖iteratedDerivWithin 2 (fun τ => F τ (A τ)) (Icc a b) τ‖ ≤
        M * (1 + B) ^ 2 + M ^ 2 * (1 + B) := by
  have hA' : ODESolution (fun t x => (ContinuousLinearMap.id ℝ E) (F t x)) A a b := hA
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  obtain ⟨hA2, hb2⟩ := OpenProblems.HighOrder.ODESolution.norm_iteratedDerivWithin_two_le
    ContinuousLinearMap.norm_id_le (hF.of_le (by norm_num)) hB hD₁ hA'
  obtain ⟨hA3, hb3⟩ := hA'.norm_iteratedDerivWithin_three_le ContinuousLinearMap.norm_id_le hF hB
    hD₁ hD₂
  obtain ⟨-, he1⟩ := rhs_contDiffOn_and_iteratedDerivWithin_eq (q := 1) hab hFc hA
    (by convert hA2 using 1; norm_num)
  obtain ⟨hg2, he2⟩ := rhs_contDiffOn_and_iteratedDerivWithin_eq (q := 2) hab hFc hA
    (by convert hA3 using 1; norm_num)
  exact ⟨by exact_mod_cast hg2, fun τ hτ => by rw [he1 τ hτ]; exact hb2 τ hτ,
    fun τ hτ => by rw [he2 τ hτ]; exact hb3 τ hτ⟩

end Lemma62

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
`‖Y₁ - A(t + h)‖ ≤ 4 C (h^{p+1} + h² ε) + 5 h η`, i.e. `O(h^{p+1} + h ε_r)`.  Conditional on
Lemma 4.2 (hypothesis `hcmp`); unconditional form: `IsRKKLStep.one_step_error_of_standing`. -/
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
    ‖Y₁ - A (t + h)‖ ≤ 4 * (klRKConst p b c L M Cst * (h ^ (p + 1) + h ^ 2 * ε)) + 5 * (h * η) := by
  have h1 := hstep.2.one_step_error hV₀ hY₀ hcmp
  have h2 := rk_increment_error hp hF hL b c hc hord hh hε hA hg hM hZ
  rw [hA₀] at h2
  linarith

/-- **Theorem 6.1, global error** (arXiv 2608.17157): if every step of Algorithm 6.1 satisfies
the hypotheses of `IsRKKLStep.one_step_error` with the same constants (`Φ j` the exact flow from
`Y j` on `[t_j, t_{j+1}]`, `g_j(τ) = F(τ, Φ j τ)`), then for `j h ≤ T`
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T (4 C (h^p + h ε) + 5 η))`,
i.e. `C_T (δ + ε_r + h^p)` (with `η = √(mn) ε_r e^{L_F h}`).  Conditional on Lemma 4.2
(hypothesis `hcmp`); unconditional form: `rkKL_global_error_of_standing`. -/
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
        (‖Y 0 - A t₀‖ + T * (4 * (klRKConst p b c L M Cst * (h ^ p + h * ε)) + 5 * η)) := by
  have hK : 0 ≤ klRKConst p b c L M Cst := by
    unfold klRKConst
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
Section 6, with `‖Y₀ + σ g(t) - A(t + σ)‖ ≤ M₁ σ²/2`).  Conditional on Lemma 4.2
(hypothesis `hcmp`). -/
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
i.e. `O(h³ + h ε_r)` with constants independent of the singular values. Conditional on Lemma 4.2
(hypothesis `hcmp`, which `forall_hasComparisonCurve_of_standing` discharges for every
`η > √(mn) ε e^{L h}`). -/
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
i.e. `C_T (δ + ε_r + h²)` for `h ≤ 1` (with `η = √(mn) ε_r e^{L_F h}` from Lemma 4.2).
Conditional on Lemma 4.2 (hypothesis `hcmp`, which `forall_hasComparisonCurve_of_standing`
discharges for every `η > √(mn) ε e^{L h}`). -/
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
`‖Y₁ - A(t + h)‖ ≤ 4 (7/24 M₂ + L M₁/2) h³ + (10 L h + 5) h η`. Conditional on Lemma 4.2
(hypothesis `hcmp`, which `forall_hasComparisonCurve_of_standing` discharges for every
`η > √(mn) ε e^{L h}`). -/
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
i.e. `O(h⁴ + h ε_r)`. Conditional on Lemma 4.2
(hypothesis `hcmp`, which `forall_hasComparisonCurve_of_standing` discharges for every
`η > √(mn) ε e^{L h}`). -/
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
(with `η = √(mn) ε_r e^{L_F h}` from Lemma 4.2). Conditional on Lemma 4.2
(hypothesis `hcmp`, which `forall_hasComparisonCurve_of_standing` discharges for every
`η > √(mn) ε e^{L h}`). -/
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

/-- **Midpoint method under (6.9), one step** (arXiv 2608.17157, Section 6.2 with Lemma 6.2):
the hypotheses on `g = F(·, A(·))` of `IsMidpointKLStep.one_step_error` are derived from
`F ∈ C²` with `‖F‖ ≤ B`, `‖DF‖ ≤ M`, `‖D²F‖ ≤ M` (`norm_iteratedDerivWithin_rhs_le_two`), so
the stage and step bounds hold with `M₁ = M (1 + B)` and `M₂ = M (1 + B)² + M² (1 + B)`.
Conditional on Lemma 4.2 through `HasComparisonCurve` (see the module docstring). -/
theorem IsMidpointKLStep.one_step_error_of_contDiff {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L t h B M η : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 < h)
    (hF2 : ContDiff ℝ 2 (Function.uncurry F)) (hB : IsBoundedField F B)
    (hD₁ : ∀ x, ‖fderiv ℝ (Function.uncurry F) x‖ ≤ M)
    (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) x‖ ≤ M)
    {V₀ : Matrix n r ℝ} {Y₀ Z Y₁ : Matrix m n ℝ} (hstep : IsMidpointKLStep F V₀ t h Y₀ Z Y₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t (t + h)) (hA₀ : A t = Y₀)
    (hcmp : ∀ σ ∈ Icc 0 h, HasComparisonCurve Y₀ (A (t + σ)) (σ * η)) :
    ‖Z - A (t + h / 2)‖ ≤ M * (1 + B) / 2 * h ^ 2 + 5 / 2 * h * η ∧
      ‖Y₁ - A (t + h)‖ ≤
        4 * (7 / 24 * (M * (1 + B) ^ 2 + M ^ 2 * (1 + B)) + L * (M * (1 + B)) / 2) * h ^ 3 +
          (10 * L * h + 5) * h * η := by
  obtain ⟨hg, h1, h2⟩ := norm_iteratedDerivWithin_rhs_le_two (by linarith : t < t + h) hF2 hB
    hD₁ hD₂ hA
  exact hstep.one_step_error hF hL hh.le hV₀ hY₀ hA hA₀ hg h1 h2 hcmp

/-- **Robust order 2 of the two-stage family under (6.9), global error** (arXiv 2608.17157,
Section 6.2 and Remark 6.3 with Lemma 6.2 and Theorem 5.1): `rk2KL_global_error` with the
derivative bounds on `g_j = F(·, Φ j(·))` derived from `F ∈ C²` with `‖F‖ ≤ B`, `‖DF‖ ≤ M`,
`‖D²F‖ ≤ M` (`M₁ = M (1 + B)`, `M₂ = M (1 + B)² + M² (1 + B)`).  Conditional on Lemma 4.2
through `HasComparisonCurve`. -/
theorem rk2KL_global_error_of_contDiff {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L α B M η t₀ h T : ℝ} {N : ℕ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hα : 0 < α)
    (hα1 : α ≤ 1) (hh : 0 < h) (hF2 : ContDiff ℝ 2 (Function.uncurry F))
    (hB : IsBoundedField F B) (hD₁ : ∀ x, ‖fderiv ℝ (Function.uncurry F) x‖ ≤ M)
    (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) x‖ ≤ M) (hη : 0 ≤ η)
    {A : ℝ → Matrix m n ℝ} {Y Z : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n r ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j)
    (hV : ∀ j < N, (V j)ᵀ * V j = 1) (hYV : ∀ j < N, Y j * V j * (V j)ᵀ = Y j)
    (hstep : ∀ j < N, IsRK2KLStep F α (V j) (t₀ + j * h) h (Y j) (Z j) (Y (j + 1)))
    (hcmp : ∀ j < N, ∀ σ ∈ Icc 0 h,
      HasComparisonCurve (Y j) (Φ j (t₀ + j * h + σ)) (σ * η)) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ +
        T * (4 * ((M * (1 + B) ^ 2 + M ^ 2 * (1 + B)) / 2 * (1 / 3 + α / 2) +
          L * (M * (1 + B)) * α) * h ^ 2 + (10 * L * h + 5) * η)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hD₁ 0)
  have key : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + j * h + h) := fun j hj => by
    have := hΦ j hj
    rwa [show t₀ + ((j : ℝ) + 1) * h = t₀ + j * h + h by ring] at this
  exact rk2KL_global_error hF hL hα hα1 hh (by positivity) (by positivity) hη hA hΦ hΦ₀ hV hYV
    hstep
    (fun j hj => (norm_iteratedDerivWithin_rhs_le_two (by linarith) hF2 hB hD₁ hD₂ (key j hj)).1)
    (fun j hj =>
      (norm_iteratedDerivWithin_rhs_le_two (by linarith) hF2 hB hD₁ hD₂ (key j hj)).2.1)
    (fun j hj =>
      (norm_iteratedDerivWithin_rhs_le_two (by linarith) hF2 hB hD₁ hD₂ (key j hj)).2.2) hcmp

/-- **Heun's RK3 under (6.9), one step** (arXiv 2608.17157, Section 6.3 with Lemma 6.2): there
are `M₁, M₂, M₃` depending only on `B` and `M` such that for every `F ∈ C³` with `‖F‖ ≤ B` and
`‖D^j F‖ ≤ M` (`1 ≤ j ≤ 3`) the conclusions of `IsHeun3KLStep.one_step_error` hold.
Conditional on Lemma 4.2 through `HasComparisonCurve`. -/
theorem IsHeun3KLStep.one_step_error_of_contDiff (B M : ℝ) :
    ∃ M₁ M₂ M₃ : ℝ, ∀ {m n r : Type u} [Fintype m] [Fintype n] [Fintype r] [DecidableEq n]
      [DecidableEq r] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L t h η : ℝ} {V₀ : Matrix n r ℝ}
      {Y₀ Z₂ Z₃ Y₁ : Matrix m n ℝ} {A : ℝ → Matrix m n ℝ},
      IsLipschitzField F L → 0 ≤ L → 0 < h → ContDiff ℝ 3 (Function.uncurry F) →
      IsBoundedField F B →
      (∀ j, 1 ≤ j → j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j (Function.uncurry F) x‖ ≤ M) →
      IsHeun3KLStep F V₀ t h Y₀ Z₂ Z₃ Y₁ → V₀ᵀ * V₀ = 1 → Y₀ * V₀ * V₀ᵀ = Y₀ →
      ODESolution F A t (t + h) → A t = Y₀ →
      (∀ σ ∈ Icc 0 h, HasComparisonCurve Y₀ (A (t + σ)) (σ * η)) →
      ‖Z₂ - A (t + h / 3)‖ ≤ 2 / 9 * M₁ * h ^ 2 + 5 / 3 * h * η ∧
        ‖Z₃ - A (t + 2 * h / 3)‖ ≤
          (28 / 81 * M₂ + 16 / 27 * L * M₁) * h ^ 3 + (40 / 9 * L * h + 10 / 3) * h * η ∧
        ‖Y₁ - A (t + h)‖ ≤ (17 / 54 * M₃ + 28 / 27 * L * M₂ + 16 / 9 * L ^ 2 * M₁) * h ^ 4 +
          (40 / 3 * L ^ 2 * h ^ 2 + 10 * L * h + 5) * h * η := by
  obtain ⟨Mq, hMq⟩ := exists_norm_iteratedDerivWithin_rhs_le.{u} 3 B M
  refine ⟨Mq 1, Mq 2, Mq 3, ?_⟩
  intro m n r _ _ _ _ _ F L t h η V₀ Y₀ Z₂ Z₃ Y₁ A hF hL hh hF3 hB hM hstep hV₀ hY₀ hA hA₀ hcmp
  have hd := hMq (by linarith : t < t + h) hF3 hB hM hA
  exact hstep.one_step_error hF hL hh.le hV₀ hY₀ hA hA₀ (hd 3 (by norm_num) le_rfl).1
    (hd 1 le_rfl (by norm_num)).2 (hd 2 (by norm_num) (by norm_num)).2
    (hd 3 (by norm_num) le_rfl).2 hcmp

/-- **Heun's RK3 under (6.9), global error** (arXiv 2608.17157, Section 6.3 with Lemma 6.2 and
Theorem 5.1): with the `M₁, M₂, M₃` of Lemma 6.2 (depending only on `B` and `M`), every
computation as in `heun3KL_global_error` with `F ∈ C³`, `‖F‖ ≤ B`, `‖D^j F‖ ≤ M`
(`1 ≤ j ≤ 3`) satisfies its global bound, i.e. robust order 3.  Conditional on Lemma 4.2
through `HasComparisonCurve`. -/
theorem heun3KL_global_error_of_contDiff (B M : ℝ) :
    ∃ M₁ M₂ M₃ : ℝ, ∀ {m n r : Type u} [Fintype m] [Fintype n] [Fintype r] [DecidableEq n]
      [DecidableEq r] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L η t₀ h T : ℝ} {N : ℕ}
      {A : ℝ → Matrix m n ℝ} {Y Z₂ Z₃ : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n r ℝ}
      {Φ : ℕ → ℝ → Matrix m n ℝ},
      IsLipschitzField F L → 0 ≤ L → 0 < h → ContDiff ℝ 3 (Function.uncurry F) →
      IsBoundedField F B →
      (∀ j, 1 ≤ j → j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j (Function.uncurry F) x‖ ≤ M) →
      0 ≤ η → ODESolution F A t₀ (t₀ + N * h) →
      (∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h)) →
      (∀ j < N, Φ j (t₀ + j * h) = Y j) →
      (∀ j < N, (V j)ᵀ * V j = 1) → (∀ j < N, Y j * V j * (V j)ᵀ = Y j) →
      (∀ j < N, IsHeun3KLStep F (V j) (t₀ + j * h) h (Y j) (Z₂ j) (Z₃ j) (Y (j + 1))) →
      (∀ j < N, ∀ σ ∈ Icc 0 h, HasComparisonCurve (Y j) (Φ j (t₀ + j * h + σ)) (σ * η)) →
      ∀ j ≤ N, (j : ℝ) * h ≤ T →
        ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ +
          T * ((17 / 54 * M₃ + 28 / 27 * L * M₂ + 16 / 9 * L ^ 2 * M₁) * h ^ 3 +
            (40 / 3 * L ^ 2 * h ^ 2 + 10 * L * h + 5) * η)) := by
  obtain ⟨Mq, hMq⟩ := exists_norm_iteratedDerivWithin_rhs_le.{u} 3 B M
  refine ⟨max (Mq 1) 0, max (Mq 2) 0, max (Mq 3) 0, ?_⟩
  intro m n r _ _ _ _ _ F L η t₀ h T N A Y Z₂ Z₃ V Φ hF hL hh hF3 hB hM hη hA hΦ hΦ₀ hV hYV
    hstep hcmp
  have key : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + j * h + h) := fun j hj => by
    have := hΦ j hj
    rwa [show t₀ + ((j : ℝ) + 1) * h = t₀ + j * h + h by ring] at this
  exact heun3KL_global_error hF hL hh (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    hη hA hΦ hΦ₀ hV hYV hstep
    (fun j hj => (hMq (by linarith) hF3 hB hM (key j hj) 3 (by norm_num) le_rfl).1)
    (fun j hj τ hτ => ((hMq (by linarith) hF3 hB hM (key j hj) 1 le_rfl (by norm_num)).2 τ
      hτ).trans (le_max_left _ _))
    (fun j hj τ hτ => ((hMq (by linarith) hF3 hB hM (key j hj) 2 (by norm_num)
      (by norm_num)).2 τ hτ).trans (le_max_left _ _))
    (fun j hj τ hτ => ((hMq (by linarith) hF3 hB hM (key j hj) 3 (by norm_num) le_rfl).2 τ
      hτ).trans (le_max_left _ _)) hcmp

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

/-! ### Unconditional forms under the standing assumptions (Lemma 4.2, Theorems 4.3, 5.1, 6.1) -/

section Standing

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Lemma 4.2, comparison point, unconditional** (arXiv 2608.17157).  Under the standing
assumptions — `F` jointly continuous and `L`-Lipschitz in `X` ((3.2); the bound `‖F‖ ≤ B` is not
needed), normal component at most `ε` on `M_r` ((3.3)), `r < min(m, n)` — let `rank Y₀ ≤ r`, let
`A` solve `A' = F(t, A)` on `[t₀, t₀ + s]` with `A(t₀) = Y₀`, and let `e^{K_G s} ≤ 3/2` with
`K_G = (r + √r) L` (the paper's `s ≤ h*`, (A.47)).  Then `HasComparisonCurve Y₀ (A(t₀ + s)) η`
for every `η > √(mn) ε s e^{L s}` (the bound (4.7)).  Proof: Lemma A.1
(`factoredNormalBound_of_isUnit`), Lemma A.2 (`exists_generators`) and the discrete comparison
curve (`exists_comparison_point`); the overlap `‖Q_s‖₂ ≤ 3` of (4.8) is then
`exists_overlap_of_specNorm_sub_one_le`.  Deviation: the paper's statement has `η` equal to the
bound; here every larger `η` (the one-step and global theorems below recover the paper's bounds by
letting `η` decrease to it). -/
theorem hasComparisonCurve_of_standing {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hFc : Continuous (Function.uncurry F)) {r : ℕ}
    {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) {A : ℝ → Matrix m n ℝ} {t₀ s : ℝ} (hs : 0 ≤ s)
    (hsK : Real.exp ((r + √r) * L * s) ≤ 3 / 2) (hA : ODESolution F A t₀ (t₀ + s))
    (hA₀ : A t₀ = Y₀) {η : ℝ}
    (hη : √(Fintype.card m * Fintype.card n) * ε * s * Real.exp (L * s) < η) :
    HasComparisonCurve Y₀ (A (t₀ + s)) η := by
  have hN := factoredNormalBound_of_isUnit hF hε
  have hK : 0 ≤ ((r : ℝ) + √r) * L := mul_nonneg (by positivity) hL
  obtain ⟨Lm, R, -, hR, hcl⟩ := exists_comparison_point hF hL hK hFc
    (fun t X hX => exists_generators hF hL hN hrm hrn t hX) hY₀ hs hA hA₀ hη
  exact ⟨Lm, R, hR.trans (by linarith), hcl⟩

/-- **The comparison hypothesis of Section 6, discharged** (arXiv 2608.17157, Lemma 4.2 at every
elapsed time `σ ∈ [0, h]`): under the standing assumptions of
`hasComparisonCurve_of_standing`, with `e^{K_G h} ≤ 3/2`, the hypothesis
`∀ σ ∈ [0, h], HasComparisonCurve Y₀ (A(t + σ)) (σ η)` of the stage estimates
(`first_stage_error`, `IsRK2KLStep.one_step_error`, `IsMidpointKLStep.one_step_error`,
`IsHeun3KLStep.one_step_error` and the global theorems built on them) holds for every
`η > √(mn) ε e^{L h}`. -/
theorem forall_hasComparisonCurve_of_standing {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hFc : Continuous (Function.uncurry F)) {r : ℕ}
    {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n) {Y₀ : Matrix m n ℝ}
    (hY₀ : Y₀.rank ≤ r) {A : ℝ → Matrix m n ℝ} {t h : ℝ}
    (hhK : Real.exp ((r + √r) * L * h) ≤ 3 / 2) (hA : ODESolution F A t (t + h))
    (hA₀ : A t = Y₀) {η : ℝ}
    (hη : √(Fintype.card m * Fintype.card n) * ε * Real.exp (L * h) < η) :
    ∀ σ ∈ Icc 0 h, HasComparisonCurve Y₀ (A (t + σ)) (σ * η) := by
  have hε0 : 0 ≤ ε :=
    nonneg_of_factoredNormalBound (factoredNormalBound_of_isUnit hF hε) hrm.le hrn.le
  intro σ hσ
  rcases eq_or_lt_of_le hσ.1 with rfl | hσ0
  · refine ⟨1, 1, ?_, by simp [hA₀]⟩
    rw [sub_self, specNorm_zero']
    norm_num
  · refine hasComparisonCurve_of_standing hF hL hFc hε hrm hrn hY₀ hσ.1 ?_
      (hA.mono le_rfl (by linarith [hσ.2])) hA₀ ?_
    · exact (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ.2
        (mul_nonneg (by positivity) hL))).trans hhK
    · have hS : 0 ≤ √(Fintype.card m * Fintype.card n : ℝ) * ε :=
        mul_nonneg (Real.sqrt_nonneg _) hε0
      calc √(Fintype.card m * Fintype.card n : ℝ) * ε * σ * Real.exp (L * σ)
          ≤ √(Fintype.card m * Fintype.card n : ℝ) * ε * σ * Real.exp (L * h) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ.2 hL))
              (mul_nonneg hS hσ.1)
        _ = σ * (√(Fintype.card m * Fintype.card n : ℝ) * ε * Real.exp (L * h)) := by ring
        _ < σ * η := mul_lt_mul_of_pos_left hη hσ0

/-- **Theorem 4.3 (one-step error), unconditional** (arXiv 2608.17157): under the standing
assumptions (`F` jointly continuous and `L`-Lipschitz in `X`, normal bound `ε` on `M_r`,
`r < min(m, n)`), for `Y₀ = Y₀ V₀ V₀ᵀ` with orthonormal `V₀ ∈ ℝ^{n×r}` (e.g. `Y₀ = U₀ S₀ V₀ᵀ`),
the exact solution `A` from `A(t₀) = Y₀`, `0 ≤ s` with `e^{K_G s} ≤ 3/2`
(`K_G = (r + √r) L`, the paper's `s ≤ h*`) and any increment, the reduced K–L step satisfies
`‖Y₁ - A(t₀ + s)‖ ≤ 4 ‖Y₀ + ΔA - A(t₀ + s)‖ + 5 √(mn) ε s e^{L s}`, the paper's (4.9) with its
constants.  Rank-admissibility is not needed. -/
theorem IsKLStep.one_step_error_of_standing {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hFc : Continuous (Function.uncurry F)) {r : ℕ}
    {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n) {V₀ : Matrix n (Fin r) ℝ}
    {Y₀ X Y₁ : Matrix m n ℝ} (hstep : IsKLStep V₀ X Y₁) (hV₀ : V₀ᵀ * V₀ = 1)
    (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) {A : ℝ → Matrix m n ℝ} {t₀ s : ℝ} (hs : 0 ≤ s)
    (hsK : Real.exp ((r + √r) * L * s) ≤ 3 / 2) (hA : ODESolution F A t₀ (t₀ + s))
    (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A (t₀ + s)‖ ≤ 4 * ‖X - A (t₀ + s)‖ +
      5 * (√(Fintype.card m * Fintype.card n) * ε * s * Real.exp (L * s)) := by
  have hrk : Y₀.rank ≤ r := by
    rw [← hY₀]
    exact (Matrix.rank_mul_le_right _ _).trans (by simpa using V₀ᵀ.rank_le_card_height)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc := hasComparisonCurve_of_standing hF hL hFc hε hrm hrn hrk hs hsK hA hA₀
    (η := √(Fintype.card m * Fintype.card n) * ε * s * Real.exp (L * s) + δ / 5)
    (by linarith)
  have h1 := hstep.one_step_error hV₀ hY₀ hc
  linarith

/-- **Theorem 5.1 (global error via the increment error), unconditional** (arXiv 2608.17157):
`klStep_global_error` with the comparison hypothesis discharged by the standing assumptions
(`IsKLStep.one_step_error_of_standing`), for `0 < h` with `e^{K_G h} ≤ 3/2`
(`K_G = (r + √r) L`; the paper's `h ≤ h₀ ≤ h*`) and right bases `V j ∈ ℝ^{n×r}`:
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T (4 d / h + 5 √(mn) ε e^{L h}))` for `j h ≤ T`, an
explicit form of `C_T (δ + ε_r + d_h / h)`.  Rank-admissibility and `‖F‖ ≤ B` are not needed. -/
theorem klStep_global_error_of_standing {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hFc : Continuous (Function.uncurry F)) {r : ℕ}
    {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n) {d t₀ h T : ℝ} {N : ℕ}
    (hh : 0 < h) (hhK : Real.exp ((r + √r) * L * h) ≤ 3 / 2) (hd : 0 ≤ d)
    {A : ℝ → Matrix m n ℝ} {Y ΔA : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n (Fin r) ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = Y j)
    (hV : ∀ j < N, (V j)ᵀ * V j = 1) (hYV : ∀ j < N, Y j * V j * (V j)ᵀ = Y j)
    (hstep : ∀ j < N, IsKLStep (V j) (Y j + ΔA j) (Y (j + 1)))
    (hinc : ∀ j < N, ‖Y j + ΔA j - Φ j (t₀ + (j + 1) * h)‖ ≤ d) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ +
        T * (4 * d / h + 5 * (√(Fintype.card m * Fintype.card n) * ε * Real.exp (L * h)))) := by
  have hε0 : 0 ≤ ε :=
    nonneg_of_factoredNormalBound (factoredNormalBound_of_isUnit hF hε) hrm.le hrn.le
  have hh' : h ≠ 0 := hh.ne'
  have hη0 : 0 ≤ √(Fintype.card m * Fintype.card n : ℝ) * ε * Real.exp (L * h) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hε0) (Real.exp_pos _).le
  refine lady_windermere_of_le hF hL hh.le hA hΦ hΦ₀
    (add_nonneg (div_nonneg (by linarith) hh.le) (by linarith)) (fun j hj => ?_)
  have e : t₀ + (j + 1) * h = t₀ + j * h + h := by ring
  have hΦj := hΦ j hj
  have h2 := hinc j hj
  rw [e] at hΦj h2 ⊢
  have h1 := (hstep j hj).one_step_error_of_standing hF hL hFc hε hrm hrn (hV j hj) (hYV j hj)
    hh.le hhK hΦj (hΦ₀ j hj)
  have hd' : h * (4 * d / h) = 4 * d := by field_simp
  calc _ ≤ 4 * ‖Y j + ΔA j - Φ j (t₀ + j * h + h)‖ +
        5 * (√(Fintype.card m * Fintype.card n) * ε * h * Real.exp (L * h)) := h1
    _ ≤ 4 * d + 5 * (√(Fintype.card m * Fintype.card n) * ε * h * Real.exp (L * h)) := by
        linarith
    _ = h * (4 * d / h + 5 * (√(Fintype.card m * Fintype.card n) * ε * Real.exp (L * h))) := by
        rw [mul_add, hd']; ring

/-- **Theorem 6.1, unconditional one-step and global error** (arXiv 2608.17157): Algorithm 6.1
(`IsRKKLStep`) under the standing assumptions and the hypotheses of `rk_increment_error`
satisfies `‖Y₁ - A(t + h)‖ ≤ 4 C (h^{p+1} + h² ε) + 5 h √(mn) ε e^{L h}` for `0 < h` with
`e^{K_G h} ≤ 3/2`, i.e. `O(h^{p+1} + h ε_r)`; the comparison hypothesis of
`IsRKKLStep.one_step_error` is discharged by `IsKLStep.one_step_error_of_standing`. -/
theorem IsRKKLStep.one_step_error_of_standing {s p : ℕ} (hp : 0 < p)
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hFc : Continuous (Function.uncurry F)) {r : ℕ}
    {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n)
    (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (hord : ∀ k < p, ∑ i, b i * c i ^ k = 1 / (k + 1))
    {t h M Cst : ℝ} (hh : 0 ≤ h) (hhK : Real.exp ((r + √r) * L * h) ≤ 3 / 2)
    {V₀ : Matrix n (Fin r) ℝ} {Y₀ Y₁ : Matrix m n ℝ} {Z : Fin s → Matrix m n ℝ}
    (hstep : IsRKKLStep F a b c V₀ t h Y₀ Z Y₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : Y₀ * V₀ * V₀ᵀ = Y₀) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t (t + h)) (hA₀ : A t = Y₀)
    (hg : ContDiffOn ℝ p (fun τ => F τ (A τ)) (Icc t (t + h)))
    (hM : ∀ τ ∈ Icc t (t + h),
      ‖iteratedDerivWithin p (fun τ => F τ (A τ)) (Icc t (t + h)) τ‖ ≤ M)
    (hZ : ∀ i, b i ≠ 0 → ‖Z i - A (t + c i * h)‖ ≤ Cst * (h ^ p + h * ε)) :
    ‖Y₁ - A (t + h)‖ ≤ 4 * (klRKConst p b c L M Cst * (h ^ (p + 1) + h ^ 2 * ε)) +
      5 * (h * (√(Fintype.card m * Fintype.card n) * ε * Real.exp (L * h))) := by
  have hε0 : 0 ≤ ε :=
    nonneg_of_factoredNormalBound (factoredNormalBound_of_isUnit hF hε) hrm.le hrn.le
  have h1 := hstep.2.one_step_error_of_standing hF hL hFc hε hrm hrn hV₀ hY₀ hh hhK hA hA₀
  have h2 := rk_increment_error hp hF hL b c hc hord hh hε0 hA hg hM hZ
  rw [hA₀] at h2
  have e : √(Fintype.card m * Fintype.card n : ℝ) * ε * h * Real.exp (L * h) =
      h * (√(Fintype.card m * Fintype.card n : ℝ) * ε * Real.exp (L * h)) := by ring
  rw [e] at h1
  linarith

/-- **Theorem 6.1, unconditional global error** (arXiv 2608.17157): if every step of Algorithm 6.1
satisfies the hypotheses of `IsRKKLStep.one_step_error_of_standing` with the same constants, then
for `j h ≤ T`
`‖Y j - A(t_j)‖ ≤ e^{L T} (‖Y 0 - A(t₀)‖ + T (4 C (h^p + h ε) + 5 √(mn) ε e^{L h}))`,
i.e. `C_T (δ + ε_r + h^p)`. -/
theorem rkKL_global_error_of_standing {s p : ℕ} (hp : 0 < p)
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hFc : Continuous (Function.uncurry F)) {r : ℕ}
    {ε : ℝ}
    (hε : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (hrm : r < Fintype.card m) (hrn : r < Fintype.card n)
    (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (hord : ∀ k < p, ∑ i, b i * c i ^ k = 1 / (k + 1))
    {t₀ h M Cst T : ℝ} {N : ℕ} (hh : 0 < h) (hhK : Real.exp ((r + √r) * L * h) ≤ 3 / 2)
    (hM0 : 0 ≤ M) (hCst : 0 ≤ Cst)
    {A : ℝ → Matrix m n ℝ} {Y : ℕ → Matrix m n ℝ} {V : ℕ → Matrix n (Fin r) ℝ}
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
      ‖Z j i - Φ j (t₀ + j * h + c i * h)‖ ≤ Cst * (h ^ p + h * ε)) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖Y j - A (t₀ + j * h)‖ ≤ Real.exp (L * T) *
        (‖Y 0 - A t₀‖ + T * (4 * (klRKConst p b c L M Cst * (h ^ p + h * ε)) +
          5 * (√(Fintype.card m * Fintype.card n) * ε * Real.exp (L * h)))) := by
  have hε0 : 0 ≤ ε :=
    nonneg_of_factoredNormalBound (factoredNormalBound_of_isUnit hF hε) hrm.le hrn.le
  have hK : 0 ≤ klRKConst p b c L M Cst := by
    unfold klRKConst
    have h1 : 0 ≤ ∑ i, |b i| * c i ^ p :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (pow_nonneg (hc i).1 _)
    have h2 : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    positivity
  have hη0 : 0 ≤ √(Fintype.card m * Fintype.card n : ℝ) * ε * Real.exp (L * h) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hε0) (Real.exp_pos _).le
  refine lady_windermere_of_le hF hL hh.le hA hΦ hΦ₀
    (add_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg hK (add_nonneg (pow_nonneg hh.le p) (mul_nonneg hh.le hε0))))
      (mul_nonneg (by norm_num) hη0)) (fun j hj => ?_)
  have e : t₀ + (j + 1) * h = t₀ + j * h + h := by ring
  rw [e]
  have hΦj := hΦ j hj
  rw [e] at hΦj
  have h1 := (hstep j hj).one_step_error_of_standing hp hF hL hFc hε hrm hrn a b c hc hord hh.le
    hhK (hV j hj) (hYV j hj) hΦj (hΦ₀ j hj) (hg j hj) (hM j hj) (hZ j hj)
  refine h1.trans_eq ?_
  ring

/-- The standing assumptions of the unconditional theorems are satisfiable: `F ≡ 0` is
continuous, `0`-Lipschitz and has normal component `0` on `M_r`. -/
example (r : ℕ) :
    IsLipschitzField (fun (_ : ℝ) (_ : Matrix m n ℝ) => (0 : Matrix m n ℝ)) 0 ∧
      Continuous (Function.uncurry fun (_ : ℝ) (_ : Matrix m n ℝ) => (0 : Matrix m n ℝ)) ∧
      ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
        Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
          ‖(1 - U * Uᵀ) * (fun (_ : ℝ) (_ : Matrix m n ℝ) => (0 : Matrix m n ℝ)) t (U * S * Vᵀ) *
            (1 - V * Vᵀ)‖ ≤ 0 :=
  ⟨fun _ _ _ => by simp, continuous_const, fun _ _ _ _ _ _ _ => by simp⟩

end Standing

/-- The constant of Theorem 6.1 under its earlier name; renamed `klRKConst` to keep it apart from
the core `RungeKuttaBUG.rkConst`. -/
@[deprecated (since := "2026-11-10")] alias rkConst := klRKConst

end LeanDLRA.Literature.P2608_17157
