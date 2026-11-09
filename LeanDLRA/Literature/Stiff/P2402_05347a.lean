import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2402.05347 (Appelö–Cheng): truncation, one-step stability, DLRA failure

Real matrices carry the Frobenius inner product (`open scoped LeanDLRA.Frobenius`). The module
proves three statements of the paper.

* **Section 1, introductory failure example.** `dlra_stationary_of_orthogonal`: if the columns
  of `F` are orthogonal to `U` and its rows to `V`, the tangent projection `tangentProj U V F`
  vanishes, the constant curve has zero DLRA velocity, and the modeling error
  `‖F - tangentProj U V F‖` equals `‖F‖`. The paper's Gaussian instance is not formalized,
  since it needs integrals over a symmetric domain. `failure_example` is a discrete instance
  in which the hypotheses hold and `‖F‖ = 144 > 0`. "Remains stationary" is formalized as zero
  DLRA velocity along the constant curve; uniqueness of the DLRA solution is not formalized.
  The field `F` is a fixed matrix (the value `F(X(t), t)` at the point), and the Lean statement
  does not tie `X` to `U`, `V`: it holds for every `X`, in particular for the paper's
  `X = U Σ Vᵀ`, where `tangentProj U V` is the tangent projector at `X` when `Σ` is invertible.
* **Theorem 3.1, Galerkin and truncation steps of Algorithms 4 and 5** (Steps 4-5 of
  Algorithm 4, Steps 3-4 and 7-8 of Algorithm 5). `norm_step_le_of_dissipative`: for a
  dissipative field `F`, a Galerkin step on the column and row spaces spanned by orthonormal
  `U` and `V`, followed by SVD truncation, does not increase the Frobenius norm. The Galerkin
  step is the weak form (4) of the paper, assumed to hold for the given solution; existence of
  that solution is not claimed. The prediction spaces are arbitrary, so both algorithms are
  covered. `norm_svdTruncation_le` bounds the truncated SVD for every rank `r`, which includes
  the rank selected by the tolerance `ε`. The Galerkin inequality is the library lemma
  `galerkin_implicitEuler_norm_le_of_dissipative`, applied after the weak form is shown to give
  the projector form.

Core definitions used: `LeanDLRA.leftProj`, `LeanDLRA.rightProj`, `LeanDLRA.tangentProj`,
`LeanDLRA.IsOrthProj`, `LeanDLRA.EckartYoung.truncation`. No new structures are defined.

Not repeated here, since the library already has them: a version of Lemma 3.3 (local error with
the cheap prediction space, `ε₁` measured as `‖(1 - P) F(t₀, x₀)‖`) is
`cheapPrediction_local_error_le` in `LeanDLRA/Stiff/ImplicitBUG.lean`. Theorem 3.2 (semi-bounded
`F`) is treated in `LeanDLRA/Stiff/ImplicitSolvability.lean`: `galerkin_implicitEuler_norm_le`
gives the factor `(1 - α Δt)⁻¹` of the paper's proof, and `implicitGalerkin_linear_counterexample`
shows that the printed factor `e^{α Δt}` fails for every `α ≠ 0` already for the Galerkin step,
so whenever the truncation removes nothing.
Not formalized: the convergence estimate of Section 3.3.2, the residual argument of
Section 3.2, and Section 4.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2402_05347

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ### SVD truncation -/

/-- **SVD truncation does not increase the Frobenius norm** (arXiv 2402.05347, proof of
Theorem 3.1: `‖X̂ⁿ⁺¹‖ = ‖T_ε^svd(X^{n+1,pre})‖ ≤ ‖X^{n+1,pre}‖`). The truncation
`truncation A r = A V_r V_rᵀ` is the truncated SVD of rank `r`. -/
theorem norm_svdTruncation_le {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (A : Matrix p q ℝ) (r : ℕ) : ‖EckartYoung.truncation A r‖ ≤ ‖A‖ := by
  have hV := EckartYoung.transpose_mul_topRightSingularVectors A r
  rw [EckartYoung.truncation, Frobenius.norm_mul_transpose_of_orthonormal hV]
  exact norm_mul_le_of_orthonormal hV A

/-! ### Theorem 3.1: Galerkin step followed by truncation -/

/-- **Stability of the Galerkin step with SVD truncation** (arXiv 2402.05347, Theorem 3.1,
Galerkin and truncation steps of Algorithms 4 and 5). Let `U` (`m × k₁`) and `V` (`n × k₂`)
have orthonormal columns, let `X₀ = X̂ⁿ`, and let `X₁ = U C Vᵀ` satisfy the Galerkin equation
(4) of the paper: for every `S`, `⟪X₁, U S Vᵀ⟫ = ⟪X₀ + h F(t, X₁), U S Vᵀ⟫`. If
`⟪F(t, X), X⟫ ≤ 0` for all `t` and `X`, and `h ≥ 0`, then `‖X₁‖ ≤ ‖X₀‖`. The truncated
solution `U (T C) Vᵀ`, with `T` the truncation of rank `r`, also has norm at most `‖X₀‖`. -/
theorem norm_step_le_of_dissipative {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]
    [DecidableEq k₁] [DecidableEq k₂] (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (hF : ∀ t X, ⟪F t X, X⟫ ≤ 0) {h t : ℝ} (hh : 0 ≤ h) {X₀ : Matrix m n ℝ}
    {U : Matrix m k₁ ℝ} (hU : Uᵀ * U = 1) {V : Matrix n k₂ ℝ} (hV : Vᵀ * V = 1)
    {C : Matrix k₁ k₂ ℝ}
    (hG : ∀ S : Matrix k₁ k₂ ℝ,
      ⟪U * C * Vᵀ, U * S * Vᵀ⟫ = ⟪X₀ + h • F t (U * C * Vᵀ), U * S * Vᵀ⟫) (r : ℕ) :
    ‖U * C * Vᵀ‖ ≤ ‖X₀‖ ∧ ‖U * EckartYoung.truncation C r * Vᵀ‖ ≤ ‖X₀‖ := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ,
      Q = leftProj U * rightProj V := ⟨_, rfl⟩
  have hQ : IsOrthProj Q := by
    rw [hQdef]
    exact isOrthProj_leftProj_mul_rightProj hU hV
  have hQapp : ∀ Y : Matrix m n ℝ, Q Y = U * (Uᵀ * Y * V) * Vᵀ := by
    intro Y
    rw [hQdef]
    exact leftProj_rightProj_apply U V Y
  have hcoef : ∀ C' : Matrix k₁ k₂ ℝ, Uᵀ * (U * C' * Vᵀ) * V = C' := by
    intro C'
    simp only [Matrix.mul_assoc]
    rw [hV, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hX1 : Q (U * C * Vᵀ) = U * C * Vᵀ := by
    rw [hQapp, hcoef]
  -- The weak form (4) gives the projector form `X₁ = Q (X₀ + h F(t, X₁))`.
  have hx : U * C * Vᵀ = Q (X₀ + h • F t (U * C * Vᵀ)) := by
    obtain ⟨D, hD⟩ : ∃ D, D = Q (X₀ + h • F t (U * C * Vᵀ)) - U * C * Vᵀ := ⟨_, rfl⟩
    have hQD : Q D = D := by
      rw [hD, map_sub, hQ.idem, hX1]
    have hDform : D = U * (Uᵀ * D * V) * Vᵀ := by
      have h0 := hQD
      rw [hQapp] at h0
      exact h0.symm
    have hweak : ⟪U * C * Vᵀ, D⟫ = ⟪X₀ + h • F t (U * C * Vᵀ), D⟫ := by
      have h1 := hG (Uᵀ * D * V)
      rw [← hDform] at h1
      exact h1
    have hDD : ⟪D, D⟫ = 0 := by
      have h2 : ⟪D, D⟫ = ⟪Q (X₀ + h • F t (U * C * Vᵀ)), D⟫ - ⟪U * C * Vᵀ, D⟫ := by
        rw [← inner_sub_left, ← hD]
      rw [h2, hQ.symm, hQD, hweak, sub_self]
    have hD0 : D = 0 := inner_self_eq_zero.mp hDD
    rw [hD, sub_eq_zero] at hD0
    exact hD0.symm
  have hstep := galerkin_implicitEuler_norm_le_of_dissipative (F := F) (t := t) hQ hh
    (fun x => hF t x) hx
  have hCnorm : ‖C‖ = ‖U * C * Vᵀ‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
  have hTnorm : ‖U * EckartYoung.truncation C r * Vᵀ‖ = ‖EckartYoung.truncation C r‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
  refine ⟨hstep, ?_⟩
  rw [hTnorm]
  calc ‖EckartYoung.truncation C r‖ ≤ ‖C‖ := norm_svdTruncation_le C r
    _ = ‖U * C * Vᵀ‖ := hCnorm
    _ ≤ ‖X₀‖ := hstep

/-! ### Section 1: the introductory failure example -/

/-- **Introductory failure example, tangent-projection form** (arXiv 2402.05347, Section 1).
Let `U` and `V` have orthonormal columns, so `tangentProj U V` is the orthogonal projector onto
the tangent space at `X = U Σ Vᵀ`. If the column space of `F` is orthogonal to `U` (`Uᵀ F = 0`)
and its row space is orthogonal to `V` (`F V = 0`), then the DLRA velocity `Π F` vanishes, the
constant curve `t ↦ X` has DLRA velocity zero at every time, and the modeling error
`‖F - Π F‖` equals `‖F‖`. The statement holds for every `X`; the paper's case is `X = U Σ Vᵀ`. -/
theorem dlra_stationary_of_orthogonal {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]
    [DecidableEq k₁] [DecidableEq k₂] {U : Matrix m k₁ ℝ} (hU : Uᵀ * U = 1)
    {V : Matrix n k₂ ℝ} (hV : Vᵀ * V = 1) (X F : Matrix m n ℝ)
    (hUF : Uᵀ * F = 0) (hFV : F * V = 0) :
    IsOrthProj (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) ∧
      tangentProj U V F = 0 ∧
      (∀ t : ℝ, HasDerivAt (fun _ : ℝ => X) (tangentProj U V F) t) ∧
      ‖F - tangentProj U V F‖ = ‖F‖ := by
  have h1 : U * Uᵀ * F = 0 := by rw [Matrix.mul_assoc, hUF, Matrix.mul_zero]
  have h2 : F * V * Vᵀ = 0 := by rw [hFV, Matrix.zero_mul]
  have h3 : U * Uᵀ * F * V * Vᵀ = 0 := by rw [h1, Matrix.zero_mul, Matrix.zero_mul]
  have hT : tangentProj U V F = 0 := by
    rw [tangentProj_apply, h3, h1, h2, add_zero, sub_zero]
  refine ⟨isOrthProj_tangentProj hU hV, hT, fun t => ?_, ?_⟩
  · rw [hT]
    exact hasDerivAt_const t X
  · rw [hT, sub_zero]

/-- The unit column vector `u = (3/5, 4/5)ᵀ`. -/
noncomputable def exU : Matrix (Fin 2) (Fin 1) ℝ := !![3 / 5; 4 / 5]

/-- The field `F = (A u)(A u)ᵀ` with `A u = (48/5, -36/5)ᵀ`, the value of `A (u uᵀ) Aᵀ` for
`A = diag(16, -9)`. -/
noncomputable def exF : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2304 / 25, -1728 / 25; -1728 / 25, 1296 / 25]

/-- Non-vacuity of `dlra_stationary_of_orthogonal`: for `U = V = u` the hypotheses hold, the
DLRA velocity vanishes, and the modeling error is `‖F‖ = 144`. -/
theorem failure_example :
    tangentProj exU exU exF = 0 ∧ ‖exF - tangentProj exU exU exF‖ = 144 := by
  have hU : exUᵀ * exU = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    all_goals norm_num [exU, Matrix.mul_apply, Fin.sum_univ_two]
  have hUF : exUᵀ * exF = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    all_goals norm_num [exU, exF, Matrix.mul_apply, Fin.sum_univ_two]
  have hFV : exF * exU = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [exU, exF, Matrix.mul_apply, Fin.sum_univ_two]
  have hnorm : ‖exF‖ = 144 := by
    rw [Frobenius.norm_def]
    have hsq : (∑ i, ∑ j, exF i j ^ 2) = (144 : ℝ) ^ 2 := by
      norm_num [exF, Fin.sum_univ_two]
    rw [hsq, Real.sqrt_sq (by norm_num)]
  obtain ⟨_, h2, _, h4⟩ :=
    dlra_stationary_of_orthogonal hU hU (exU * exUᵀ) exF hUF hFV
  exact ⟨h2, by rw [h4, hnorm]⟩

end LeanDLRA.Literature.P2402_05347
