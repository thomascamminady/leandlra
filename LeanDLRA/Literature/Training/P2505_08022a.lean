import LeanDLRA.Analysis.Defs
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.SVD
import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Training.Descent

/-!
# Results of arXiv 2505.08022: Robust DLRT under adversarial attacks

Schotthöfer, Yang, Schnake, *Dynamical low-rank compression of neural networks with robustness under
adversarial attacks*. The module defines the robustness regularizer `R(S) = ‖SᵀS - α_S² I‖`,
`α_S² = ‖S‖² / r` (Frobenius norm, Definition 1), and proves the results of the paper for this
concrete `R`: identity (3), `R(S)² / r` is the variance of the squared singular values
(`robustR_sq_div_card`, with (26) as `robustR_sq`) and orthogonal invariance (`robustR_mul_mul`);
Prop. 1, `∇R(S) = 2 S (SᵀS - α_S² I) / R(S)` where `R(S) ≠ 0` (`hasFDerivAt_robustR`,
`hasGradientAt_robustR`, `gradient_robustR`); Prop. 2, `κ(S) ≤ exp (R(S) / (√2 ς_r(S)²))`
(`kappa_le_exp`, with Szőkefalvi-Nagy's inequality as `sub_sq_div_le_variance`, in the form
`‖S‖₂ ‖S⁻¹‖₂` as
`specNorm_mul_specNorm_inv_le_exp` and for the layer `U S Vᵀ` as
`specNorm_mul_specNorm_pinv_le_exp`); Prop. 3, the long-time stability estimate of the regularized
least-squares flow (`robustR_stability`, and `robustR_stability_filippov` for trajectories through
`R = 0`); and for Algorithm 1 (`IsRobustDLRTStep`): the regularizer does not enter the basis
gradients (`hasFDerivAt_Ltilde_left`, `hasFDerivAt_Ltilde_right`, `hasDerivAt_robustR_bases`),
augmentation is exact (`IsRobustDLRTStep.prolong_zero`) and captures the tangent gradient
(`IsRobustDLRTStep.galerkin_tangentProj`), a coefficient step is a Galerkin projected gradient step
(`IsRobustDLRTStep.prolong_succ_eq_projGradStep`) and a gradient step of the regularized coefficient
objective (`IsRobustDLRTStep.coeff_succ_eq_gradStep`), the bases stay orthonormal and the retraction
is within `ϑ`, and one iteration exists (`exists_isRobustDLRTStep`).

## Differences from the paper and remarks

* `S` is `m × r` with `r` the number of columns, not only `r × r`.  This contains the paper's case
  `m = r` and the regularizer `R(Mat(S)ᵀ)` of a convolutional layer (Sec. 5.1).  Singular values are
  Mathlib's `LinearMap.singularValues`, indexed from `0`, and `κ(S) = ς₁(S) / ς_r(S)`, identified
  with the paper's `‖S‖ ‖S†‖` for invertible `S` by `kappa_eq_specNorm_mul_specNorm_inv`.
* Prop. 1: the formula is undefined at `R(S) = 0`, where `gradR` has the value `0`, and the theorem
  is only for `R(S) ≠ 0`, as in the paper.  `R²` is differentiable everywhere
  (`hasFDerivAt_robustR_sq`, Remark 2).
* Prop. 2 "for any `S`": the case `ς_r(S) = 0` is `0 ≤ 1` here, see `kappa_le_exp`.
* Prop. 3: the abstract energy estimate is the library's `LeanDLRA.robustDLRT_stability`
  (`LeanDLRA.robustDLRT_stability_sharp` has the better constant `1 + β`); here its hypotheses
  (39), (40) and the continuity of `R` are proved for `R`.  The paper's statement presupposes a
  solution, and so does the theorem; `odeSolution_const` and `robustR_diagonal_ne_zero` give
  instances.  The field is discontinuous on `{R = 0}`, where trajectories can slide, so
  `robustR_stability_filippov` proves (5) for the differential inclusion with the
  convexified gradient `filippovGradR` (right differentiable solutions), by re-running the Grönwall
  argument with a time dependent selection.  The final display (42) of the proof is printed with
  `=`; what the Grönwall argument gives, and what (5) and the theorems here state, is `≤`.
* The identity `R(U S Vᵀ) = R(S)` holds for orthogonal `V` (and `U` with orthonormal columns).  For
  rectangular `V`, as in Sec. 5, the identity with `R` of (2) for the large matrix is false
  (`robustR_mul_mul_ne`, exact defect in `robustR_mul_mul_sq`), but `R(U S Vᵀ)` is independent of
  the bases (`robustR_mul_mul_eq`), which is what the paper needs: `∇_U R = ∇_V R = 0`.  With the
  projector `V Vᵀ` in place of the identity the equality holds
  (`norm_transpose_mul_self_sub_mul`).  Also, `R` is not constant under the rank augmentation:
  `R(Ŝ₀) ≠ R(S)` in general (`IsRobustDLRTStep.robustR_coeff_zero_sq`).
* Algorithm 1 is stated as a relation, for an arbitrary gradient map `G` and SGD as the optimizer of
  line 10; the truncation is any factorization with error `≤ ϑ`.  Line 9 is read as eq. (8).  The
  input `S` need not be diagonal.  The latent space (7) is not a subspace of the tangent space (the
  paper's footnote 3); what holds is `IsRobustDLRTStep.galerkin_tangentProj`.
* Not formalized: the sensitivity bound (1), quoted from the literature, and the experiments.
  The paper has no convergence theorem for Algorithm 1, and none is claimed here: `∇R` is not
  Lipschitz, so the descent results of `Training/Descent.lean` do not apply for `β ≠ 0`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2505_08022

variable {m m' n r r' : Type*} [Fintype m] [Fintype m'] [Fintype n] [Fintype r] [Fintype r']
  [DecidableEq r] [DecidableEq r']

/-! ### The regularizer -/

/-- The scale `α_S² = ‖S‖² / r` of Definition 1 of arXiv 2505.08022 (eq. (2)), where `r` is the
number of columns of `S` and `‖·‖` the Frobenius norm. -/
noncomputable def alphaSq (S : Matrix m r ℝ) : ℝ := ‖S‖ ^ 2 / Fintype.card r

/-- The defect `S ᵀ S - α_S² I` (called `W_S` in the proof of Prop. 1 of arXiv 2505.08022). -/
noncomputable def defect (S : Matrix m r ℝ) : Matrix r r ℝ :=
  Sᵀ * S - alphaSq S • (1 : Matrix r r ℝ)

/-- The **robustness regularizer** `R(S) = ‖SᵀS - α_S² I‖` (Definition 1 of arXiv 2505.08022,
eq. (2)).  The paper takes `S` square, `S ∈ ℝ^{r × r}`; here the row index type `m` is arbitrary,
which contains that case and the regularizer `R(Mat(S)ᵀ)` of a convolutional layer (Sec. 5.1). -/
noncomputable def robustR (S : Matrix m r ℝ) : ℝ := ‖defect S‖

/-- The closed form `∇R(S) = 2 S (SᵀS - α_S² I) / R(S)` of Prop. 1 of arXiv 2505.08022.  Where
`R(S) = 0` the division gives the value `0` (Lean's convention `x / 0 = 0`). -/
noncomputable def gradR (S : Matrix m r ℝ) : Matrix m r ℝ := (2 / robustR S) • (S * defect S)

/-- `R(S) ≥ 0`. -/
lemma robustR_nonneg (S : Matrix m r ℝ) : 0 ≤ robustR S := norm_nonneg _

/-- The matrix `SᵀS - α_S² I` is symmetric. -/
lemma defect_transpose (S : Matrix m r ℝ) : (defect S)ᵀ = defect S := by
  simp [defect, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_smul]

/-- `(A, I) = tr A`. -/
lemma inner_one_right (A : Matrix r r ℝ) : ⟪A, (1 : Matrix r r ℝ)⟫ = Matrix.trace A := by
  rw [Frobenius.inner_eq_trace, Matrix.mul_one, Matrix.trace_transpose]

omit [DecidableEq r] in
/-- `tr (SᵀS) = ‖S‖²`. -/
lemma trace_transpose_mul_self (S : Matrix m r ℝ) : Matrix.trace (Sᵀ * S) = ‖S‖ ^ 2 := by
  rw [← Frobenius.inner_eq_trace, real_inner_self_eq_norm_sq]

/-- `‖I‖² = r`. -/
lemma norm_one_sq : ‖(1 : Matrix r r ℝ)‖ ^ 2 = Fintype.card r := by
  rw [← real_inner_self_eq_norm_sq, inner_one_right, Matrix.trace_one]

/-- The orthogonality relation (28) of arXiv 2505.08022: `(SᵀS - α_S² I, I) = 0`. -/
theorem inner_defect_one (S : Matrix m r ℝ) : ⟪defect S, (1 : Matrix r r ℝ)⟫ = 0 := by
  rw [defect, inner_sub_left, real_inner_smul_left, inner_one_right, trace_transpose_mul_self,
    real_inner_self_eq_norm_sq, norm_one_sq, alphaSq]
  rcases isEmpty_or_nonempty r with h | h
  · have : S = 0 := Subsingleton.elim _ _
    simp [this]
  · have : (Fintype.card r : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
    ring

/-- `R(S)² = (SᵀS - α_S² I, SᵀS)`, the first equality of the computation (38). -/
lemma robustR_sq_eq_inner (S : Matrix m r ℝ) : robustR S ^ 2 = ⟪defect S, Sᵀ * S⟫ := by
  have h := inner_defect_one S
  rw [robustR, ← real_inner_self_eq_norm_sq]
  nth_rw 2 [defect]
  rw [inner_sub_right, real_inner_smul_right, h, mul_zero, sub_zero]

/-- `R(S)² = ‖SᵀS‖² - ‖S‖⁴ / r`, the third line of eq. (26) of arXiv 2505.08022. -/
theorem robustR_sq (S : Matrix m r ℝ) :
    robustR S ^ 2 = ‖Sᵀ * S‖ ^ 2 - ‖S‖ ^ 4 / Fintype.card r := by
  rw [robustR_sq_eq_inner, defect, inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_smul_left, real_inner_comm, inner_one_right, trace_transpose_mul_self, alphaSq]
  ring

/-! ### Proposition 1 -/

/-- The derivative of `S ↦ SᵀS - α_S² I` (first line of (27) of arXiv 2505.08022). -/
theorem hasFDerivAt_defect (S : Matrix m r ℝ) :
    ∃ D' : Matrix m r ℝ →L[ℝ] Matrix r r ℝ, HasFDerivAt defect D' S ∧
      ∀ Z, D' Z = Sᵀ * Z + Zᵀ * S -
        ((2 / Fintype.card r * ⟪S, Z⟫) • (1 : Matrix r r ℝ)) := by
  have h1 : HasFDerivAt (fun X : Matrix m r ℝ => Xᵀ * X) _ S :=
    (Frobenius.mulCLM : Matrix r m ℝ →L[ℝ] Matrix m r ℝ →L[ℝ] Matrix r r ℝ).hasFDerivAt_of_bilinear
      (Frobenius.transposeCLM.hasFDerivAt) (hasFDerivAt_id S)
  have h2 : HasFDerivAt (fun X : Matrix m r ℝ => alphaSq X)
      ((Fintype.card r : ℝ)⁻¹ • (2 • innerSL ℝ S)) S := by
    refine ((hasStrictFDerivAt_norm_sq S).hasFDerivAt.const_mul
      (Fintype.card r : ℝ)⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun X => ?_)
    simp [alphaSq, div_eq_inv_mul]
  have h3 := h1.sub (h2.smul_const (1 : Matrix r r ℝ))
  refine ⟨_, h3, fun Z => ?_⟩
  simp only [sub_apply, add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    Frobenius.mulCLM_apply, Frobenius.transposeCLM_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  congr 2
  ring

/-- `(SᵀS - α_S² I, D'(S)[Z]) = 2 (S (SᵀS - α_S² I), Z)`: the computation (27)–(28) of
arXiv 2505.08022. -/
theorem inner_defect_deriv (S Z : Matrix m r ℝ) :
    ⟪defect S, Sᵀ * Z + Zᵀ * S -
      ((2 / Fintype.card r * ⟪S, Z⟫) • (1 : Matrix r r ℝ))⟫ = 2 * ⟪S * defect S, Z⟫ := by
  have e1 : ⟪defect S, Sᵀ * Z⟫ = ⟪S * defect S, Z⟫ := by
    rw [Frobenius.inner_mul_left', Matrix.transpose_transpose]
  have e2 : ⟪defect S, Zᵀ * S⟫ = ⟪S * defect S, Z⟫ := by
    rw [Frobenius.inner_mul_right', ← Frobenius.inner_transpose, Matrix.transpose_mul,
      defect_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [inner_sub_right, inner_add_right, real_inner_smul_right, inner_defect_one, e1, e2]
  ring

/-- `Q = R²` is differentiable everywhere with gradient `∇Q(S) = 4 S (SᵀS - α_S² I)`, eq. (29) of
arXiv 2505.08022 (this is also the differentiability of `R²` claimed in its Remark 2). -/
theorem hasFDerivAt_robustR_sq (S : Matrix m r ℝ) :
    HasFDerivAt (fun X : Matrix m r ℝ => robustR X ^ 2)
      (innerSL ℝ ((4 : ℝ) • (S * defect S))) S := by
  obtain ⟨D', hD', hZ⟩ := hasFDerivAt_defect S
  have h := hD'.norm_sq
  refine h.congr_fderiv ?_
  ext Z
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hZ,
    inner_defect_deriv, real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **Proposition 1 of arXiv 2505.08022**, with `HasFDerivAt`: wherever `R(S) ≠ 0`, the regularizer
is Fréchet differentiable with `∇R(S) = 2 S (SᵀS - α_S² I) / R(S)`.  The paper's `S` is square;
here it is `m × r`. -/
theorem hasFDerivAt_robustR {S : Matrix m r ℝ} (hS : robustR S ≠ 0) :
    HasFDerivAt robustR (innerSL ℝ (gradR S)) S := by
  have h := (hasFDerivAt_robustR_sq S).sqrt (pow_ne_zero 2 hS)
  have e : (fun X : Matrix m r ℝ => √(robustR X ^ 2)) = robustR :=
    funext fun X => Real.sqrt_sq (robustR_nonneg X)
  rw [e] at h
  refine h.congr_fderiv ?_
  rw [Real.sqrt_sq (robustR_nonneg S), ← map_smul, gradR, smul_smul]
  congr 2
  field_simp
  ring

/-- **Proposition 1 of arXiv 2505.08022**, with Mathlib's `HasGradientAt`. -/
theorem hasGradientAt_robustR {S : Matrix m r ℝ} (hS : robustR S ≠ 0) :
    HasGradientAt robustR (gradR S) S :=
  hasGradientAt_iff_hasFDerivAt.2 ((hasFDerivAt_robustR hS).congr_fderiv (by ext Z; simp))

/-- **Proposition 1 of arXiv 2505.08022**: `∇R(S) = 2 S (SᵀS - α_S² I) / R(S)` where `R(S) ≠ 0`,
for Mathlib's `gradient`. -/
theorem gradient_robustR {S : Matrix m r ℝ} (hS : robustR S ≠ 0) :
    gradient robustR S = gradR S :=
  (hasGradientAt_robustR hS).gradient

/-! ### Singular values and the spectral form of the regularizer -/

/-- The singular values `ς₁(S) ≥ ς₂(S) ≥ ⋯` of `S`, as Mathlib's `LinearMap.singularValues`:
`singVal S i` is the paper's `ς_{i+1}(S)` (the indexing starts at `0`).  The `r` values
`singVal S 0, …, singVal S (r - 1)` are the square roots of the eigenvalues of `SᵀS`. -/
noncomputable def singVal (S : Matrix m r ℝ) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin S).singularValues i

/-- The largest singular value `ς₁(S)`. -/
noncomputable def sigmaMax (S : Matrix m r ℝ) : ℝ := singVal S 0

/-- The smallest singular value `ς_r(S)`, `r` being the number of columns of `S`. -/
noncomputable def sigmaMin (S : Matrix m r ℝ) : ℝ := singVal S (Fintype.card r - 1)

/-- The condition number `κ(S) = ς₁(S) / ς_r(S)`.  For invertible square `S` this is
`‖S‖₂ ‖S⁻¹‖₂`, see `kappa_eq_specNorm_mul_specNorm_inv`.  For singular `S` the division gives the
value `0` (Lean's convention), not the paper's `∞`. -/
noncomputable def kappa (S : Matrix m r ℝ) : ℝ := sigmaMax S / sigmaMin S

/-- Singular values are nonnegative. -/
lemma singVal_nonneg (S : Matrix m r ℝ) (i : ℕ) : 0 ≤ singVal S i :=
  LinearMap.singularValues_nonneg _ i

/-- A thin SVD of `S` whose singular values, extended by zero, are the `r` values `singVal S i`. -/
private lemma exists_svd_sum (S : Matrix m r ℝ) :
    ∃ (ρ : ℕ) (U : Matrix m (Fin ρ) ℝ) (V : Matrix r (Fin ρ) ℝ) (σ : Fin ρ → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ S = U * Matrix.diagonal σ * Vᵀ ∧
      ∀ f : ℝ → ℝ, f 0 = 0 → ∑ i ∈ range (Fintype.card r), f (singVal S i) = ∑ i, f (σ i) := by
  classical
  obtain ⟨U, V, σ, hU, hV, -, -, hσ, hS⟩ := SVD.exists_svd S rfl
  refine ⟨S.rank, U, V, σ, hU, hV, hS, fun f hf => ?_⟩
  have hρ : S.rank ≤ Fintype.card r := S.rank_le_card_width
  have h1 : ∑ i, f (σ i) = ∑ i ∈ range S.rank, f (singVal S i) := by
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [hσ i, singVal]
  rw [h1]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hρ) fun i _ hi => ?_
  have h0 : singVal S i = 0 := by
    rw [singVal, LinearMap.singularValues_eq_zero_iff_le_finrank_range,
      ← SVD.rank_eq_finrank_range]
    exact not_lt.1 (by simpa using hi)
  rw [h0, hf]

/-- `‖diag(σ)‖² = ∑ᵢ σᵢ²`. -/
lemma norm_diagonal_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ℝ) :
    ‖(Matrix.diagonal σ : Matrix ι ι ℝ)‖ ^ 2 = ∑ i, σ i ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Matrix.diagonal_apply_ne _ hj.symm]
  · simp

/-- `∑ᵢ ςᵢ(S)² = ‖S‖²`, the sum running over `r` singular values (used in (26) of
arXiv 2505.08022). -/
theorem sum_singVal_sq (S : Matrix m r ℝ) :
    ∑ i ∈ range (Fintype.card r), singVal S i ^ 2 = ‖S‖ ^ 2 := by
  obtain ⟨ρ, U, V, σ, hU, hV, hS, hf⟩ := exists_svd_sum S
  rw [hf (fun x => x ^ 2) (by simp), ← norm_diagonal_sq]
  conv_rhs => rw [hS, Frobenius.norm_mul_transpose_of_orthonormal hV,
    Frobenius.norm_mul_of_orthonormal hU]

/-- `∑ᵢ (ςᵢ(S)²)² = ‖SᵀS‖²`, the sum running over `r` singular values (used in (26) of
arXiv 2505.08022). -/
theorem sum_singVal_sq_sq (S : Matrix m r ℝ) :
    ∑ i ∈ range (Fintype.card r), (singVal S i ^ 2) ^ 2 = ‖Sᵀ * S‖ ^ 2 := by
  obtain ⟨ρ, U, V, σ, hU, hV, hS, hf⟩ := exists_svd_sum S
  have e : Sᵀ * S = V * Matrix.diagonal (fun i => σ i ^ 2) * Vᵀ := by
    have hd : (Matrix.diagonal σ)ᵀ = Matrix.diagonal σ := Matrix.diagonal_transpose σ
    conv_lhs => rw [hS]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hd]
    calc V * (Matrix.diagonal σ * Uᵀ) * (U * Matrix.diagonal σ * Vᵀ)
        = V * (Matrix.diagonal σ * (Uᵀ * U) * Matrix.diagonal σ) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          simp only [sq]
  rw [hf (fun x => (x ^ 2) ^ 2) (by simp), e, Frobenius.norm_mul_transpose_of_orthonormal hV,
    Frobenius.norm_mul_of_orthonormal hV, norm_diagonal_sq]

/-- **Identity (3) of arXiv 2505.08022**: `R(S)² / r` is the variance of the squared singular
values, `R(S)² / r = (1/r) ∑ᵢ (ςᵢ(S)²)² - ((1/r) ∑ᵢ ςᵢ(S)²)²`.  The sums run over the `r` singular
values `ς₁, …, ς_r`, and `S` may be `m × r`. -/
theorem robustR_sq_div_card (S : Matrix m r ℝ) :
    robustR S ^ 2 / Fintype.card r =
      1 / Fintype.card r * ∑ i ∈ range (Fintype.card r), (singVal S i ^ 2) ^ 2 -
        (1 / Fintype.card r * ∑ i ∈ range (Fintype.card r), singVal S i ^ 2) ^ 2 := by
  rw [robustR_sq, sum_singVal_sq, sum_singVal_sq_sq]
  rcases isEmpty_or_nonempty r with h | h
  · simp
  · have : (Fintype.card r : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

/-! ### Orthogonal invariance -/

section Invariance

variable [DecidableEq m]

omit [Fintype r'] [DecidableEq r] [DecidableEq r'] in
/-- `(U S Vᵀ)ᵀ (U S Vᵀ) = V SᵀS Vᵀ` for `U` with orthonormal columns. -/
lemma transpose_mul_self_mul_mul {U : Matrix m' m ℝ} (hU : Uᵀ * U = 1) (S : Matrix m r ℝ)
    (V : Matrix r' r ℝ) : (U * S * Vᵀ)ᵀ * (U * S * Vᵀ) = V * (Sᵀ * S) * Vᵀ := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc V * (Sᵀ * Uᵀ) * (U * S * Vᵀ) = V * (Sᵀ * ((Uᵀ * U) * (S * Vᵀ))) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.one_mul]; simp only [Matrix.mul_assoc]

omit [DecidableEq r'] in
/-- `‖U S Vᵀ‖ = ‖S‖` for `U`, `V` with orthonormal columns. -/
lemma norm_mul_mul {U : Matrix m' m ℝ} {V : Matrix r' r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix m r ℝ) : ‖U * S * Vᵀ‖ = ‖S‖ := by
  rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]

/-- The effect of rectangular bases on the regularizer of arXiv 2505.08022 (not in the paper): for
`U`, `V` with orthonormal columns and `S` with `r` columns, `W = U S Vᵀ` with `r'` columns has
`R(W)² = R(S)² + ‖S‖⁴ (1/r - 1/r')`.  So `R(U S Vᵀ)` depends on `U`, `V` only
through the number `r'` of rows of `V`. -/
theorem robustR_mul_mul_sq {U : Matrix m' m ℝ} {V : Matrix r' r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (S : Matrix m r ℝ) :
    robustR (U * S * Vᵀ) ^ 2 =
      robustR S ^ 2 + ‖S‖ ^ 4 * (1 / Fintype.card r - 1 / Fintype.card r') := by
  rw [robustR_sq, robustR_sq, transpose_mul_self_mul_mul hU,
    Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hV,
    norm_mul_mul hU hV]
  ring

/-- **Orthogonal invariance of the regularizer** (arXiv 2505.08022, Sec. 4, after (3)):
`R(U S Vᵀ) = R(S)` for orthogonal `U`, `V`.  This is the paper's statement with `U ∈ ℝ^{m' × m}`
only required to have orthonormal columns; `V` is orthogonal, i.e. square. -/
theorem robustR_mul_mul {U : Matrix m' m ℝ} {V : Matrix r r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (S : Matrix m r ℝ) : robustR (U * S * Vᵀ) = robustR S := by
  have h := robustR_mul_mul_sq hU hV S
  rw [sub_self, mul_zero, add_zero] at h
  exact (pow_left_inj₀ (robustR_nonneg _) (robustR_nonneg _) two_ne_zero).1 h

/-- The two bases of a low-rank representation do not enter the regularizer (the meaning of "`R` is
unitarily invariant" of arXiv 2505.08022, Sec. 4, for rectangular bases):
`R(U S Vᵀ) = R(U' S V'ᵀ)` for all `U`, `V`, `U'`, `V'` with orthonormal columns. -/
theorem robustR_mul_mul_eq {U U' : Matrix m' m ℝ} {V V' : Matrix r' r ℝ} (hU : Uᵀ * U = 1)
    (hU' : U'ᵀ * U' = 1) (hV : Vᵀ * V = 1) (hV' : V'ᵀ * V' = 1) (S : Matrix m r ℝ) :
    robustR (U * S * Vᵀ) = robustR (U' * S * V'ᵀ) := by
  have h := (robustR_mul_mul_sq hU hV S).trans (robustR_mul_mul_sq hU' hV' S).symm
  exact (pow_left_inj₀ (robustR_nonneg _) (robustR_nonneg _) two_ne_zero).1 h

/-- **`∇_U R = ∇_V R = 0`** (arXiv 2505.08022, Sec. 5, discussion of (6)): along any family of
bases `U(t)`, `V(t)` with orthonormal columns, the map `t ↦ R(U(t) S V(t)ᵀ)` has derivative `0`.
So the Riemannian gradient of `(U, V) ↦ R(U S Vᵀ)` on the Stiefel manifolds vanishes.  See
`hasFDerivAt_Ltilde_left` for the form used in the basis augmentation (6). -/
theorem hasDerivAt_robustR_bases {U : ℝ → Matrix m' m ℝ} {V : ℝ → Matrix r' r ℝ}
    (hU : ∀ t, (U t)ᵀ * U t = 1) (hV : ∀ t, (V t)ᵀ * V t = 1) (S : Matrix m r ℝ) (t : ℝ) :
    HasDerivAt (fun τ => robustR (U τ * S * (V τ)ᵀ)) 0 t := by
  have h : (fun τ => robustR (U τ * S * (V τ)ᵀ)) = fun _ => robustR (U 0 * S * (V 0)ᵀ) :=
    funext fun τ => robustR_mul_mul_eq (hU τ) (hU 0) (hV τ) (hV 0) S
  rw [h]
  exact hasDerivAt_const t _

/-- **The literal identity `R(U S Vᵀ) = R(S)` fails for rectangular bases.**  Sec. 5 of
arXiv 2505.08022 writes `R(U S Vᵀ) = R(S)` for `U, V ∈ ℝ^{n × r}`, but `R` of the `n × n` matrix
`U S Vᵀ`, defined by (2) with `I_n` and `‖·‖²/n`, differs from `R(S)` as soon as `r < n` and
`S ≠ 0`.  The conclusion the paper draws from it is correct, see `hasDerivAt_robustR_bases` and
`robustR_mul_mul_eq`. -/
theorem robustR_mul_mul_ne {U : Matrix m' m ℝ} {V : Matrix r' r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {S : Matrix m r ℝ} (hS : S ≠ 0) (hr : Fintype.card r < Fintype.card r') :
    robustR (U * S * Vᵀ) ≠ robustR S := by
  intro h
  have h1 := robustR_mul_mul_sq hU hV S
  rw [h] at h1
  have hc : (0 : ℝ) < Fintype.card r := by
    have : Nonempty r := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      exact hS (Subsingleton.elim _ _)
    exact_mod_cast Fintype.card_pos
  have hc' : (Fintype.card r : ℝ) < Fintype.card r' := by exact_mod_cast hr
  have h2 : (0 : ℝ) < 1 / Fintype.card r - 1 / Fintype.card r' :=
    sub_pos.2 (one_div_lt_one_div_of_lt hc hc')
  have h3 : 0 < ‖S‖ ^ 4 := pow_pos (norm_pos_iff.2 hS) 4
  have := mul_pos h3 h2
  linarith

omit [DecidableEq r'] in
/-- The correct low-rank form of the identity of arXiv 2505.08022, Sec. 5: with `P = V Vᵀ` in place
of the identity, `‖WᵀW - α_S² P‖ = R(S)` for `W = U S Vᵀ`. -/
theorem norm_transpose_mul_self_sub_mul {U : Matrix m' m ℝ} {V : Matrix r' r ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix m r ℝ) :
    ‖(U * S * Vᵀ)ᵀ * (U * S * Vᵀ) - alphaSq S • (V * Vᵀ)‖ = robustR S := by
  have e : (U * S * Vᵀ)ᵀ * (U * S * Vᵀ) - alphaSq S • (V * Vᵀ) = V * defect S * Vᵀ := by
    rw [transpose_mul_self_mul_mul hU, defect, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
  rw [e, Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hV,
    robustR]

end Invariance

/-! ### Proposition 2 -/

/-- **Szőkefalvi-Nagy's variance inequality**, used for eq. (32) of arXiv 2505.08022: the variance
of `N` numbers is at least `(x_i - x_j)² / (2 N)`, for any two of them. -/
theorem sub_sq_div_le_variance {ι : Type*} (s : Finset ι) (x : ι → ℝ) {i j : ι} (hi : i ∈ s)
    (hj : j ∈ s) :
    (x i - x j) ^ 2 / (2 * s.card) ≤
      1 / s.card * ∑ k ∈ s, x k ^ 2 - (1 / s.card * ∑ k ∈ s, x k) ^ 2 := by
  classical
  have hN : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hi⟩
  set μ : ℝ := 1 / s.card * ∑ k ∈ s, x k with hμ
  have hsum : ∑ k ∈ s, x k = s.card * μ := by rw [hμ]; field_simp
  have hexp : ∑ k ∈ s, (x k - μ) ^ 2 = ∑ k ∈ s, x k ^ 2 - s.card * μ ^ 2 := by
    calc ∑ k ∈ s, (x k - μ) ^ 2 = ∑ k ∈ s, (x k ^ 2 - 2 * μ * x k + μ ^ 2) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k ∈ s, x k ^ 2 - 2 * μ * ∑ k ∈ s, x k + s.card * μ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
          simp
      _ = _ := by rw [hsum]; ring
  have hlow : (x i - x j) ^ 2 / 2 ≤ ∑ k ∈ s, (x k - μ) ^ 2 := by
    by_cases hij : i = j
    · subst hij
      simpa using Finset.sum_nonneg fun k _ => sq_nonneg (x k - μ)
    · have hsub : ({i, j} : Finset ι) ⊆ s := by
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hi
        · rw [Finset.mem_singleton.1 hk]
          exact hj
      have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun k => (x k - μ) ^ 2)
        fun _ _ _ => sq_nonneg _
      rw [Finset.sum_pair hij] at h
      nlinarith [sq_nonneg (x i + x j - 2 * μ)]
  have e : 1 / (s.card : ℝ) * ∑ k ∈ s, x k ^ 2 - μ ^ 2 =
      1 / s.card * ∑ k ∈ s, (x k - μ) ^ 2 := by
    rw [hexp, mul_sub, ← mul_assoc, one_div, inv_mul_cancel₀ hN.ne', one_mul]
  rw [e]
  calc (x i - x j) ^ 2 / (2 * s.card) = 1 / s.card * ((x i - x j) ^ 2 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (one_div_pos.2 hN).le

/-- `ς_r(S) ≤ ς₁(S)`. -/
lemma sigmaMin_le_sigmaMax (S : Matrix m r ℝ) : sigmaMin S ≤ sigmaMax S :=
  LinearMap.singularValues_antitone _ (Nat.zero_le _)

/-- Eq. (33) of arXiv 2505.08022: `ς₁(S)² - ς_r(S)² ≤ √2 R(S)`. -/
theorem sq_sigmaMax_sub_sq_sigmaMin_le [Nonempty r] (S : Matrix m r ℝ) :
    sigmaMax S ^ 2 - sigmaMin S ^ 2 ≤ √2 * robustR S := by
  have hc : 0 < Fintype.card r := Fintype.card_pos
  have h := sub_sq_div_le_variance (range (Fintype.card r)) (fun i => singVal S i ^ 2)
    (i := 0) (j := Fintype.card r - 1) (Finset.mem_range.2 hc) (Finset.mem_range.2 (by omega))
  rw [Finset.card_range, ← robustR_sq_div_card] at h
  have hc' : (0 : ℝ) < Fintype.card r := by exact_mod_cast hc
  have h2 : (sigmaMax S ^ 2 - sigmaMin S ^ 2) ^ 2 ≤ (√2 * robustR S) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [div_le_div_iff₀ (by positivity) hc'] at h
    change (sigmaMax S ^ 2 - sigmaMin S ^ 2) ^ 2 * (Fintype.card r : ℝ) ≤ _ at h
    have : (sigmaMax S ^ 2 - sigmaMin S ^ 2) ^ 2 * (Fintype.card r : ℝ) ≤
        2 * robustR S ^ 2 * (Fintype.card r : ℝ) := by nlinarith
    exact le_of_mul_le_mul_right this hc'
  exact (abs_le_of_sq_le_sq' h2 (mul_nonneg (Real.sqrt_nonneg 2) (robustR_nonneg S))).2

/-- **Proposition 2 of arXiv 2505.08022** (condition number bound):
`κ(S) ≤ exp (R(S) / (√2 ς_r(S)²))`, for `κ(S) = ς₁(S) / ς_r(S)`.  The case of interest is
`ς_r(S) > 0`.  If `ς_r(S) = 0`, the paper's right side is `∞` (or undefined for `S = 0`), while here
both divisions give `0` by Lean's convention and the statement is `0 ≤ 1`.  The paper's `S` is
square; here it is `m × r`.  See `specNorm_mul_specNorm_inv_le_exp` for the spectral norm form. -/
theorem kappa_le_exp [Nonempty r] (S : Matrix m r ℝ) :
    kappa S ≤ Real.exp (robustR S / (√2 * sigmaMin S ^ 2)) := by
  rcases (singVal_nonneg S (Fintype.card r - 1)).eq_or_lt with h | h
  · have h0 : sigmaMin S = 0 := h.symm
    rw [kappa, h0, div_zero]
    exact (Real.exp_pos _).le
  have hb : 0 < sigmaMin S := h
  have ha : 0 < sigmaMax S := hb.trans_le (sigmaMin_le_sigmaMax S)
  have hgap := sq_sigmaMax_sub_sq_sigmaMin_le S
  rw [kappa]
  set a := sigmaMax S
  set b := sigmaMin S
  have hq : 0 < a / b := div_pos ha hb
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hlog : Real.log (a / b) ≤ robustR S / (√2 * b ^ 2) := by
    have h1 := Real.log_le_sub_one_of_pos (pow_pos hq 2)
    rw [Real.log_pow] at h1
    have h3 : (a / b) ^ 2 - 1 = (a ^ 2 - b ^ 2) / b ^ 2 := by field_simp
    have h4 : (a ^ 2 - b ^ 2) / b ^ 2 ≤ √2 * robustR S / b ^ 2 :=
      div_le_div_of_nonneg_right hgap (by positivity)
    have h5 : robustR S / (√2 * b ^ 2) = (√2 * robustR S / b ^ 2) / 2 := by
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
    rw [h5]
    push_cast at h1
    linarith
  calc a / b = Real.exp (Real.log (a / b)) := (Real.exp_log hq).symm
    _ ≤ _ := Real.exp_le_exp.2 hlog

/-- An invertible square matrix has `ς_r(S) > 0`: the case of interest of Prop. 2 of
arXiv 2505.08022. -/
theorem sigmaMin_pos [Nonempty r] {S : Matrix r r ℝ} (hS : IsUnit S.det) : 0 < sigmaMin S := by
  have hc : 0 < Fintype.card r := Fintype.card_pos
  rw [sigmaMin, singVal, LinearMap.singularValues_pos_iff_lt_finrank_range,
    ← SVD.rank_eq_finrank_range, Matrix.rank_of_isUnit S ((Matrix.isUnit_iff_isUnit_det S).2 hS)]
  omega

/-- For invertible `S`, the paper's condition number `κ(S) = ‖S‖ ‖S†‖` (spectral norm, Sec. 2 of
arXiv 2505.08022, with `S† = S⁻¹`) is `ς₁(S) / ς_r(S)`. -/
theorem kappa_eq_specNorm_mul_specNorm_inv [Nonempty r] {S : Matrix r r ℝ} (hS : IsUnit S.det) :
    kappa S = Curvature.specNorm S * Curvature.specNorm S⁻¹ := by
  have hb := sigmaMin_pos hS
  have hbound : ∀ v, sigmaMin S * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖ :=
    (SVD.forall_mul_norm_le_iff S).2 le_rfl
  have hle : Curvature.specNorm S⁻¹ ≤ (sigmaMin S)⁻¹ := Curvature.specNorm_inv_le hb hbound
  have hinv : ∀ v : EuclideanSpace ℝ r,
      Matrix.toEuclideanLin S⁻¹ (Matrix.toEuclideanLin S v) = v := fun v => by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.nonsing_inv_mul _ hS,
      Matrix.toLpLin_one, LinearMap.id_apply]
  have hbd : ∀ v : EuclideanSpace ℝ r,
      ‖v‖ ≤ Curvature.specNorm S⁻¹ * ‖Matrix.toEuclideanLin S v‖ := fun v => by
    have h := Curvature.norm_toEuclideanLin_le S⁻¹ (Matrix.toEuclideanLin S v)
    rwa [hinv] at h
  have hc : 0 < Curvature.specNorm S⁻¹ := by
    obtain ⟨i⟩ := ‹Nonempty r›
    have h1 := hbd (EuclideanSpace.single i 1)
    rcases (Curvature.specNorm_nonneg S⁻¹).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at h1
      simp at h1
      linarith
    · exact h0
  have hge : (sigmaMin S)⁻¹ ≤ Curvature.specNorm S⁻¹ := by
    have h1 : (Curvature.specNorm S⁻¹)⁻¹ ≤ sigmaMin S := by
      refine (SVD.forall_mul_norm_le_iff S).1 fun v => ?_
      rw [inv_mul_eq_div, div_le_iff₀ hc, mul_comm]
      exact hbd v
    exact inv_le_of_inv_le₀ hc h1
  rw [kappa, sigmaMax, singVal, ← EckartYoung.specNorm_eq_singularValues_zero,
    le_antisymm hle hge, div_eq_mul_inv]

/-- **Proposition 2 of arXiv 2505.08022** for invertible `S ∈ ℝ^{r × r}`, with the condition number
in the paper's form `κ(S) = ‖S‖ ‖S⁻¹‖` (spectral norm):
`‖S‖ ‖S⁻¹‖ ≤ exp (R(S) / (√2 ς_r(S)²))`. -/
theorem specNorm_mul_specNorm_inv_le_exp [Nonempty r] {S : Matrix r r ℝ} (hS : IsUnit S.det) :
    Curvature.specNorm S * Curvature.specNorm S⁻¹ ≤
      Real.exp (robustR S / (√2 * sigmaMin S ^ 2)) := by
  rw [← kappa_eq_specNorm_mul_specNorm_inv hS]
  exact kappa_le_exp S

/-! ### The condition number of a low-rank layer -/

section LowRankCondition

variable {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq b]
  [DecidableEq c] [DecidableEq d]

/-- Multiplication by contractions does not increase the spectral norm. -/
lemma specNorm_mul_mul_le {A : Matrix a b ℝ} {B : Matrix c d ℝ} (hA : Curvature.specNorm A ≤ 1)
    (hB : Curvature.specNorm B ≤ 1) (X : Matrix b c ℝ) :
    Curvature.specNorm (A * X * B) ≤ Curvature.specNorm X := by
  have hx := Curvature.specNorm_nonneg X
  have ha := Curvature.specNorm_nonneg A
  have hb := Curvature.specNorm_nonneg B
  calc Curvature.specNorm (A * X * B)
      ≤ Curvature.specNorm (A * X) * Curvature.specNorm B := Curvature.specNorm_mul_le _ _
    _ ≤ (Curvature.specNorm A * Curvature.specNorm X) * Curvature.specNorm B :=
        mul_le_mul_of_nonneg_right (Curvature.specNorm_mul_le _ _) hb
    _ ≤ (1 * Curvature.specNorm X) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hA hx) hB hb (by positivity)
    _ = Curvature.specNorm X := by ring

/-- The spectral norm of `W = U S Vᵀ` is that of `S`, for `U`, `V` with orthonormal columns. -/
lemma specNorm_mul_mul_transpose {U : Matrix a b ℝ} {V : Matrix c b ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (S : Matrix b b ℝ) :
    Curvature.specNorm (U * S * Vᵀ) = Curvature.specNorm S := by
  classical
  have hu := Curvature.specNorm_le_one_of_orthonormal hU
  have hv := Curvature.specNorm_le_one_of_orthonormal hV
  have hu' : Curvature.specNorm Uᵀ ≤ 1 := by rwa [Curvature.specNorm_transpose]
  have hv' : Curvature.specNorm Vᵀ ≤ 1 := by rwa [Curvature.specNorm_transpose]
  refine le_antisymm (specNorm_mul_mul_le hu hv' S) ?_
  have e : S = Uᵀ * (U * S * Vᵀ) * V := by
    calc S = (Uᵀ * U) * S * (Vᵀ * V) := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  conv_lhs => rw [e]
  exact specNorm_mul_mul_le hu' hv _

/-- The pseudo-inverse in the condition number of arXiv 2505.08022, Sec. 2: for `W = U S Vᵀ` with
`U`, `V` orthonormal and `S` invertible, `G = V S⁻¹ Uᵀ` is the Moore–Penrose inverse `W†`. This is
the core `Matrix.isMoorePenrose_mul_mul_transpose`; the copy of an earlier version of this file
stated the four Penrose equations as a conjunction (unification, follow-up of batch C1). -/
@[deprecated Matrix.isMoorePenrose_mul_mul_transpose (since := "2026-11-10")]
alias isMoorePenrose_mul_mul := Matrix.isMoorePenrose_mul_mul_transpose

variable [DecidableEq a]

/-- `κ(U S Vᵀ) = κ(S)` (arXiv 2505.08022, Sec. 2): for `U`, `V` with orthonormal columns and
invertible `S`, `‖U S Vᵀ‖ ‖(U S Vᵀ)†‖ = ς₁(S) / ς_r(S)` in the spectral norm, with the
pseudo-inverse `(U S Vᵀ)† = V S⁻¹ Uᵀ` of `Matrix.isMoorePenrose_mul_mul_transpose`. -/
theorem specNorm_mul_specNorm_pinv [Nonempty b] {U : Matrix a b ℝ} {V : Matrix c b ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {S : Matrix b b ℝ} (hS : IsUnit S.det) :
    Curvature.specNorm (U * S * Vᵀ) * Curvature.specNorm (V * S⁻¹ * Uᵀ) = kappa S := by
  rw [specNorm_mul_mul_transpose hU hV, specNorm_mul_mul_transpose hV hU,
    kappa_eq_specNorm_mul_specNorm_inv hS]

/-- **Proposition 2 of arXiv 2505.08022 for the low-rank layer**: the condition number
`κ(W) = ‖W‖ ‖W†‖` of `W = U S Vᵀ` satisfies `κ(W) ≤ exp (R(S) / (√2 ς_r(S)²))`.  This is the
statement of the paper about the core `S`, together with `κ(U S Vᵀ) = κ(S)`. -/
theorem specNorm_mul_specNorm_pinv_le_exp [Nonempty b] {U : Matrix a b ℝ} {V : Matrix c b ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {S : Matrix b b ℝ} (hS : IsUnit S.det) :
    Curvature.specNorm (U * S * Vᵀ) * Curvature.specNorm (V * S⁻¹ * Uᵀ) ≤
      Real.exp (robustR S / (√2 * sigmaMin S ^ 2)) := by
  rw [specNorm_mul_specNorm_pinv hU hV hS]
  exact kappa_le_exp S

end LowRankCondition

/-! ### Proposition 3 -/

/-- Eq. (39) of arXiv 2505.08022: `(∇R(S), S) = 2 R(S)`.  This also holds where `R(S) = 0`, for
the value `0` of `gradR`. -/
theorem inner_gradR_self (S : Matrix m r ℝ) : ⟪gradR S, S⟫ = 2 * robustR S := by
  rw [gradR, real_inner_smul_left, Frobenius.inner_mul_left, ← robustR_sq_eq_inner]
  by_cases h : robustR S = 0
  · simp [h]
  · field_simp

/-- The first bound of eq. (40) of arXiv 2505.08022: `‖∇R(S)‖ ≤ 2 ‖S‖`. -/
theorem norm_gradR_le (S : Matrix m r ℝ) : ‖gradR S‖ ≤ 2 * ‖S‖ := by
  rw [gradR, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_two (robustR_nonneg S))]
  by_cases h : robustR S = 0
  · simp [h]
  have hpos : 0 < robustR S := lt_of_le_of_ne (robustR_nonneg S) (Ne.symm h)
  calc 2 / robustR S * ‖S * defect S‖ ≤ 2 / robustR S * (‖S‖ * robustR S) :=
        mul_le_mul_of_nonneg_left (Frobenius.norm_mul_le S (defect S)) (by positivity)
    _ = 2 * ‖S‖ := by field_simp

/-- The regularizer of arXiv 2505.08022 is continuous, also on `{R = 0}`. -/
theorem continuous_robustR : Continuous (robustR : Matrix m r ℝ → ℝ) := by
  have h : Continuous fun X : Matrix m r ℝ => robustR X ^ 2 :=
    continuous_iff_continuousAt.2 fun S => (hasFDerivAt_robustR_sq S).continuousAt
  have e : (robustR : Matrix m r ℝ → ℝ) = fun X => √(robustR X ^ 2) :=
    funext fun X => (Real.sqrt_sq (robustR_nonneg X)).symm
  rw [e]
  exact h.sqrt

/-- **Proposition 3 of arXiv 2505.08022** (long-time stability), for the regularizer of Definition 1
itself.  If `S` solves `Ṡ + β ∇R(S) + S = M` on `[0, T]`, with `∇R = gradR` the closed form of
Prop. 1 and `β ≥ 0`, then for `t ∈ [0, T]`
`½‖S(t) - M‖² + 2β ∫₀ᵗ e^{τ-t} R(S(τ)) dτ ≤ ½ e^{-t} ‖S(0) - M‖² + 2 (1 - e^{-t}) β (1 + 2β) ‖M‖²`.
The paper gives no existence statement and neither does this theorem: it holds for every solution.
Where `R(S) = 0` the field uses `gradR S = 0`; `robustR_stability_filippov` allows all selections.
The abstract core is `LeanDLRA.robustDLRT_stability`; the facts about `R` are proved here. -/
theorem robustR_stability {M : Matrix m r ℝ} {β T : ℝ} (hβ : 0 ≤ β) {S : ℝ → Matrix m r ℝ}
    (hS : ODESolution (fun _ X => M - X - β • gradR X) S 0 T) :
    ∀ t ∈ Icc 0 T, ‖S t - M‖ ^ 2 / 2 + 2 * β * ∫ τ in (0 : ℝ)..t, Real.exp (τ - t) * robustR (S τ) ≤
      Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2) +
        2 * (1 - Real.exp (-t)) * β * (1 + 2 * β) * ‖M‖ ^ 2 :=
  robustDLRT_stability hβ continuous_robustR inner_gradR_self norm_gradR_le hS

/-! ### Solutions through the set `R = 0` -/

/-- The convexified (Filippov) gradient of `R`: the limits, as `δ → 0`, of convex combinations of
`∇R(y)`, `‖y - S‖ < δ`.  The field `∇R` is discontinuous on `{R = 0}`, and this set-valued map is
the standard meaning of `Ṡ + β ∇R(S) + S = M` there.  Off that set it is `{∇R(S)}`, see
`filippovGradR_eq_singleton`.  As `gradR` is included at points with `R = 0`, the set can only be
larger than the one that ignores those points, which makes `robustR_stability_filippov` stronger. -/
noncomputable def filippovGradR (S : Matrix m r ℝ) : Set (Matrix m r ℝ) :=
  ⋂ δ > (0 : ℝ), closure (convexHull ℝ (gradR '' Metric.ball S δ))

/-- The closed form of Prop. 1 of arXiv 2505.08022 is a selection of the convexified gradient. -/
theorem gradR_mem_filippovGradR (S : Matrix m r ℝ) : gradR S ∈ filippovGradR S :=
  mem_iInter₂.2 fun _ hδ => subset_closure (subset_convexHull ℝ _ ⟨S, Metric.mem_ball_self hδ, rfl⟩)

/-- The convexified gradient lies in every closed convex set that contains the values of `∇R` near
`S`. -/
private lemma filippovGradR_subset {S : Matrix m r ℝ} {δ : ℝ} (hδ : 0 < δ)
    {C : Set (Matrix m r ℝ)} (hC : Convex ℝ C) (hc : IsClosed C)
    (h : ∀ y ∈ Metric.ball S δ, gradR y ∈ C) : filippovGradR S ⊆ C := fun _ hg =>
  closure_minimal (convexHull_min (by rintro _ ⟨y, hy, rfl⟩; exact h y hy) hC) hc
    (mem_iInter₂.1 hg δ hδ)

/-- `∇R` is continuous off `{R = 0}`. -/
lemma continuousAt_gradR {S : Matrix m r ℝ} (hS : robustR S ≠ 0) : ContinuousAt gradR S := by
  have hD : Continuous fun X : Matrix m r ℝ => defect X := by
    refine continuous_iff_continuousAt.2 fun X => ?_
    obtain ⟨D', hD', -⟩ := hasFDerivAt_defect X
    exact hD'.continuousAt
  have hM : Continuous fun X : Matrix m r ℝ => X * defect X :=
    (Frobenius.mulCLM : Matrix m r ℝ →L[ℝ] Matrix r r ℝ →L[ℝ] Matrix m r ℝ).continuous₂.comp
      (continuous_id.prodMk hD)
  have hR : ContinuousAt (fun X : Matrix m r ℝ => 2 / robustR X) S :=
    continuousAt_const.div continuous_robustR.continuousAt hS
  exact hR.smul hM.continuousAt

/-- Off the set `R = 0` the convexified gradient is the gradient of Prop. 1 of arXiv 2505.08022. -/
theorem filippovGradR_eq_singleton {S : Matrix m r ℝ} (hS : robustR S ≠ 0) :
    filippovGradR S = {gradR S} := by
  refine Subset.antisymm (fun g hg => ?_) (singleton_subset_iff.2 (gradR_mem_filippovGradR S))
  refine mem_singleton_iff.2 (eq_of_forall_dist_le fun ε hε => ?_)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (continuousAt_gradR hS) ε hε
  have h := filippovGradR_subset hδ (convex_closedBall (gradR S) ε) Metric.isClosed_closedBall
    (fun y hy => Metric.mem_closedBall.2 (hδ' (Metric.mem_ball.1 hy)).le) hg
  exact Metric.mem_closedBall.1 h

/-- Eq. (39) of arXiv 2505.08022 for the convexified gradient. -/
theorem inner_self_of_mem_filippovGradR {S g : Matrix m r ℝ} (hg : g ∈ filippovGradR S) :
    ⟪g, S⟫ = 2 * robustR S := by
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, hR⟩ := Metric.continuousAt_iff.1
    (continuous_robustR.continuousAt (x := S)) (ε / 4) (by positivity)
  set c : ℝ := ‖S‖ + 1 with hc
  have hcpos : 0 < c := by positivity
  set δ : ℝ := min (min δ₁ 1) (ε / (8 * c)) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ₁ one_pos) (by positivity)
  have hC : Convex ℝ ((fun h : Matrix m r ℝ => ⟪S, h⟫) ⁻¹'
      Icc (2 * robustR S - ε) (2 * robustR S + ε)) :=
    (convex_Icc _ _).linear_preimage (innerSL ℝ S).toLinearMap
  have hcl : IsClosed ((fun h : Matrix m r ℝ => ⟪S, h⟫) ⁻¹'
      Icc (2 * robustR S - ε) (2 * robustR S + ε)) :=
    isClosed_Icc.preimage (innerSL ℝ S).continuous
  have h := filippovGradR_subset hδ hC hcl (fun y hy => ?_) hg
  · rw [Set.mem_preimage, real_inner_comm] at h
    exact abs_sub_le_iff.2 ⟨by linarith [h.2], by linarith [h.1]⟩
  have hy' : ‖y - S‖ < δ := by simpa [dist_eq_norm] using hy
  have h1 : ‖y - S‖ < δ₁ := hy'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ‖y - S‖ ≤ 1 := hy'.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ‖y - S‖ ≤ ε / (8 * c) := hy'.le.trans (min_le_right _ _)
  have hRy : |robustR y - robustR S| < ε / 4 := by
    simpa [Real.dist_eq, dist_eq_norm] using hR (x := y) (by simpa [dist_eq_norm] using h1)
  have hyn : ‖y‖ ≤ c := by
    calc ‖y‖ = ‖(y - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ c := by rw [hc]; linarith
  have herr : |⟪gradR y, S - y⟫| ≤ ε / 4 := by
    have h4 : |⟪gradR y, S - y⟫| ≤ ‖gradR y‖ * ‖S - y‖ := abs_real_inner_le_norm _ _
    have h5 : ‖gradR y‖ * ‖S - y‖ ≤ (2 * c) * (ε / (8 * c)) := by
      rw [norm_sub_rev S y]
      exact mul_le_mul ((norm_gradR_le y).trans (by linarith)) h3 (norm_nonneg _) (by positivity)
    have h6 : (2 * c) * (ε / (8 * c)) = ε / 4 := by field_simp; ring
    linarith
  have e : ⟪S, gradR y⟫ = 2 * robustR y + ⟪gradR y, S - y⟫ := by
    rw [inner_sub_right, inner_gradR_self, real_inner_comm]
    ring
  have hab := abs_lt.1 hRy
  have herr' := abs_le.1 herr
  change ⟪S, gradR y⟫ ∈ Set.Icc _ _
  rw [e]
  constructor <;> linarith [hab.1, hab.2, herr'.1, herr'.2]

/-- The bound `‖∇R(S)‖ ≤ 2 ‖S‖` of eq. (40) of arXiv 2505.08022 for the convexified gradient. -/
theorem norm_le_of_mem_filippovGradR {S g : Matrix m r ℝ} (hg : g ∈ filippovGradR S) :
    ‖g‖ ≤ 2 * ‖S‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h := filippovGradR_subset (δ := ε / 2) (by positivity)
    (convex_closedBall (0 : Matrix m r ℝ) (2 * ‖S‖ + ε)) Metric.isClosed_closedBall
    (fun y hy => ?_) hg
  · simpa using h
  have hy' : ‖y - S‖ < ε / 2 := by simpa [dist_eq_norm] using hy
  have hyn : ‖y‖ ≤ ‖S‖ + ε / 2 := by
    calc ‖y‖ = ‖(y - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have := norm_gradR_le y
  simp only [mem_closedBall_zero_iff]
  linarith

/-- **Proposition 3 of arXiv 2505.08022 for solutions through `R = 0`.**  Since `∇R` is
discontinuous on `{R = 0}`, a trajectory can reach that set and stay on it.  This theorem proves
(5) for every continuous `S` on `[0, T]` with right derivative `Ṡ = M - S - β g` and
`g(t) ∈ filippovGradR (S t)` (so `g(t) = ∇R(S(t))` whenever `R(S(t)) ≠ 0`).  The selection `g` need
not be continuous or measurable.  Solutions of the differential equation with `gradR` are the
case `g = gradR ∘ S`, by `gradR_mem_filippovGradR`.  The argument is that of the paper, using
`inner_self_of_mem_filippovGradR` and `norm_le_of_mem_filippovGradR` at points with `R = 0`. -/
theorem robustR_stability_filippov {M : Matrix m r ℝ} {β T : ℝ} (hβ : 0 ≤ β)
    {S g : ℝ → Matrix m r ℝ} (hc : ContinuousOn S (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt S (M - S t - β • g t) (Ici t) t)
    (hg : ∀ t ∈ Ico 0 T, g t ∈ filippovGradR (S t)) :
    ∀ t ∈ Icc 0 T, ‖S t - M‖ ^ 2 / 2 + 2 * β * ∫ τ in (0 : ℝ)..t, Real.exp (τ - t) * robustR (S τ) ≤
      Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2) +
        2 * (1 - Real.exp (-t)) * β * (1 + 2 * β) * ‖M‖ ^ 2 := by
  set f : ℝ → ℝ := fun τ => Real.exp τ * robustR (S τ) with hf
  set C : ℝ := 2 * β * (1 + 2 * β) * ‖M‖ ^ 2 with hC
  have hfc : ContinuousOn f (Icc 0 T) :=
    Real.continuous_exp.continuousOn.mul (continuous_robustR.comp_continuousOn hc)
  have hint : ContinuousOn (fun t => ∫ τ in (0 : ℝ)..t, f τ) (Icc 0 T) := by
    rcases le_total 0 T with h0T | hT0
    · have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
        (f := f) (a := 0) (b := T) (by rw [uIcc_of_le h0T]; exact hfc.integrableOn_Icc)
      rwa [uIcc_of_le h0T] at this
    · rcases hT0.eq_or_lt with rfl | hlt
      · simp [continuousOn_singleton]
      · simp [Icc_eq_empty_of_lt hlt]
  set φ : ℝ → ℝ := fun t => Real.exp t * (‖S t - M‖ ^ 2 / 2) + 2 * β * ∫ τ in (0 : ℝ)..t, f τ
  have hφc : ContinuousOn φ (Icc 0 T) :=
    (Real.continuous_exp.continuousOn.mul (((hc.sub continuousOn_const).norm.pow 2).div_const
      2)).add (hint.const_smul (2 * β))
  have hφd : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ
      (Real.exp t * (‖S t - M‖ ^ 2 / 2) +
        Real.exp t * (2 * ⟪S t - M, M - S t - β • g t⟫ / 2) + 2 * β * f t) (Ici t) t := by
    intro t ht
    have hmem : Icc 0 T ∈ nhdsWithin t (Ioi t) :=
      Filter.mem_of_superset (Icc_mem_nhdsGT ht.2) (Icc_subset_Icc_left ht.1)
    have hI : HasDerivWithinAt (fun u => ∫ τ in (0 : ℝ)..u, f τ) (f t) (Ici t) t :=
      intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t)
        ((hfc.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1)
        ((hfc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t).filter_mono
          (nhdsWithin_le_of_mem hmem))
        ((hfc t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin hmem)
    have hu := (((hd t ht).sub_const M).norm_sq).div_const 2
    have he := (Real.hasDerivAt_exp t).hasDerivWithinAt (s := Ici t)
    exact ((he.mul hu).add (hI.const_mul (2 * β))).congr_deriv (by ring)
  have key := image_le_of_deriv_right_le_deriv_boundary hφc hφd
    (B := fun t => ‖S 0 - M‖ ^ 2 / 2 + C * (Real.exp t - 1)) (B' := fun t => C * Real.exp t)
    (by simp [φ]) (Continuous.continuousOn (by fun_prop))
    (fun t _ => by
      simpa using (((Real.hasDerivAt_exp t).hasDerivWithinAt.sub_const 1).const_mul C).const_add
        (‖S 0 - M‖ ^ 2 / 2))
    (fun t ht => by
      set x := S t
      set r₀ := g t
      have hrS : ⟪r₀, x⟫ = 2 * robustR x := inner_self_of_mem_filippovGradR (hg t ht)
      have hr : ‖r₀‖ ≤ 2 * ‖x‖ := norm_le_of_mem_filippovGradR (hg t ht)
      set D := ‖x - M‖ with hD
      have e1 : ⟪x - M, M - x - β • r₀⟫ = -D ^ 2 - 2 * β * robustR x + β * ⟪r₀, M⟫ := by
        have : M - x - β • r₀ = -(x - M) - β • r₀ := by abel
        rw [this, inner_sub_right, inner_neg_right, real_inner_self_eq_norm_sq, inner_smul_right,
          inner_sub_left, real_inner_comm r₀ x, hrS, real_inner_comm r₀ M, hD]
        ring
      have h1 : ⟪r₀, M⟫ ≤ ‖r₀‖ * ‖M‖ := real_inner_le_norm _ _
      have h2 : ‖x‖ ≤ D + ‖M‖ := by
        calc ‖x‖ = ‖(x - M) + M‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖r₀‖ * ‖M‖ ≤ 2 * (D + ‖M‖) * ‖M‖ :=
        mul_le_mul_of_nonneg_right (hr.trans (by linarith)) (norm_nonneg _)
      have h4 : β * ⟪r₀, M⟫ ≤ β * (2 * (D + ‖M‖) * ‖M‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) hβ
      have h5 : 2 * β * D * ‖M‖ ≤ D ^ 2 / 2 + 2 * β ^ 2 * ‖M‖ ^ 2 := by
        nlinarith [sq_nonneg (D - 2 * β * ‖M‖)]
      have h7 : 0 ≤ 2 * β ^ 2 * ‖M‖ ^ 2 := by positivity
      have h6 : -(D ^ 2 / 2) + β * ⟪r₀, M⟫ ≤ C := by rw [hC]; nlinarith
      have e2 : Real.exp t * (D ^ 2 / 2) + Real.exp t * (2 * ⟪x - M, M - x - β • r₀⟫ / 2) +
          2 * β * f t = Real.exp t * (-(D ^ 2 / 2) + β * ⟪r₀, M⟫) := by
        rw [e1, hf]; ring
      rw [e2, mul_comm C]
      exact mul_le_mul_of_nonneg_left h6 (Real.exp_pos t).le)
  intro t ht
  have h1 := key ht
  simp only [φ] at h1
  have hfun : (fun τ => Real.exp (τ - t) * robustR (S τ)) = fun τ => Real.exp (-t) * f τ := by
    funext τ; rw [hf, sub_eq_add_neg, Real.exp_add]; ring
  rw [hfun, intervalIntegral.integral_const_mul]
  set I := ∫ τ in (0 : ℝ)..t, f τ
  have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-t)).le
  have hee : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have e2 : Real.exp (-t) * (Real.exp t * (‖S t - M‖ ^ 2 / 2) + 2 * β * I) =
      ‖S t - M‖ ^ 2 / 2 + 2 * β * (Real.exp (-t) * I) := by
    linear_combination (‖S t - M‖ ^ 2 / 2) * hee
  have e3 : Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2 + C * (Real.exp t - 1)) =
      Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2) +
        2 * (1 - Real.exp (-t)) * β * (1 + 2 * β) * ‖M‖ ^ 2 := by
    rw [hC]; linear_combination (2 * β * (1 + 2 * β) * ‖M‖ ^ 2) * hee
  rw [e2, e3] at hmul
  exact hmul

/-- The hypotheses of Prop. 3 of arXiv 2505.08022 (`robustR_stability`) can hold: for every `S₀`,
the constant curve `S₀` solves the flow for `M = S₀ + β ∇R(S₀)`. -/
theorem odeSolution_const (S₀ : Matrix m r ℝ) (β T : ℝ) :
    ODESolution (fun _ X => (S₀ + β • gradR S₀) - X - β • gradR X) (fun _ => S₀) 0 T := by
  refine ⟨continuousOn_const, fun t _ => ?_⟩
  have e : S₀ + β • gradR S₀ - S₀ - β • gradR S₀ = 0 := by abel
  simpa only [e] using hasDerivWithinAt_const t (Ici t) S₀

/-- `S₀ = diag(2, 1)` has `R(S₀) ≠ 0`, so the hypothesis of Prop. 1 of arXiv 2505.08022 can hold,
and `odeSolution_const` gives an instance of its Prop. 3 with `R ≠ 0` along the solution. -/
theorem robustR_diagonal_ne_zero :
    robustR (Matrix.diagonal ![2, 1] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  intro h
  have h0 : defect (Matrix.diagonal ![2, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := norm_eq_zero.1 h
  have hn : ‖(Matrix.diagonal ![2, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = 5 := by
    rw [norm_diagonal_sq]
    norm_num [Fin.sum_univ_two]
  have h1 := congrFun (congrFun h0 0) 0
  rw [defect, alphaSq, hn] at h1
  norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_transpose] at h1

/-! ### The algorithm RobustDLRT -/

section Algorithm

variable {k k' r₁ : Type*} [Fintype k] [Fintype k'] [Fintype r₁] [DecidableEq k] [DecidableEq k']
  [DecidableEq r₁]

/-- The regularized loss `L̃(U, S, V) = L(U S Vᵀ) + β R(S)` of a low-rank layer: the regularizer
acts on the coefficient matrix only (arXiv 2505.08022, Sec. 5). -/
noncomputable def Ltilde (L : Matrix m n ℝ → ℝ) (β : ℝ) (U : Matrix m k ℝ) (S : Matrix k k' ℝ)
    (V : Matrix n k' ℝ) : ℝ :=
  L (U * S * Vᵀ) + β * robustR S

omit [DecidableEq k] [DecidableEq r₁] in
/-- `∇_U L̃ = ∇_U L = ∇L(U S Vᵀ) V Sᵀ` (arXiv 2505.08022, discussion of (6)): the regularizer does
not enter the augmentation of `U`. -/
theorem hasFDerivAt_Ltilde_left {L : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ} (β : ℝ)
    {U : Matrix m k ℝ} {S : Matrix k k' ℝ} {V : Matrix n k' ℝ}
    (hL : HasFDerivAt L (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun U' => Ltilde L β U' S V) (innerSL ℝ (G * V * Sᵀ)) U := by
  have e : (fun U' : Matrix m k ℝ => U' * S * Vᵀ) = Frobenius.rightMulCLM (S * Vᵀ) := by
    funext U'
    simp [Matrix.mul_assoc]
  have h1 : HasFDerivAt (fun U' : Matrix m k ℝ => U' * S * Vᵀ)
      (Frobenius.rightMulCLM (S * Vᵀ)) U := by
    rw [e]
    exact ContinuousLinearMap.hasFDerivAt _
  have h2 := (hL.comp U h1).add_const (β * robustR S)
  refine h2.congr_fderiv ?_
  ext Z
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Frobenius.rightMulCLM_apply]
  rw [Frobenius.inner_mul_right', Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

omit [DecidableEq k] [DecidableEq r₁] in
/-- `∇_V L̃ = ∇_V L = ∇L(U S Vᵀ)ᵀ U S` (arXiv 2505.08022, discussion of (6)): the regularizer does
not enter the augmentation of `V`. -/
theorem hasFDerivAt_Ltilde_right {L : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ} (β : ℝ)
    {U : Matrix m k ℝ} {S : Matrix k k' ℝ} {V : Matrix n k' ℝ}
    (hL : HasFDerivAt L (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun V' => Ltilde L β U S V') (innerSL ℝ (Gᵀ * U * S)) V := by
  have h1 : HasFDerivAt (fun V' : Matrix n k' ℝ => U * S * V'ᵀ)
      ((Frobenius.leftMulCLM (U * S)).comp Frobenius.transposeCLM) V :=
    ContinuousLinearMap.hasFDerivAt ((Frobenius.leftMulCLM (U * S)).comp Frobenius.transposeCLM)
  have h2 := (hL.comp V h1).add_const (β * robustR S)
  refine h2.congr_fderiv ?_
  ext Z
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Frobenius.leftMulCLM_apply,
    Frobenius.transposeCLM_apply]
  rw [Frobenius.inner_mul_left', ← Frobenius.inner_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]

omit [DecidableEq k] [DecidableEq k'] [DecidableEq r₁] in
/-- The coefficient gradient of the loss: `∇_S L(U S Vᵀ) = Uᵀ ∇L(U S Vᵀ) V`, the Galerkin form of
the right side of the latent space dynamics in arXiv 2505.08022, Sec. 5. -/
theorem hasFDerivAt_loss_core {L : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ} {U : Matrix m k ℝ}
    {S : Matrix k k' ℝ} {V : Matrix n k' ℝ} (hL : HasFDerivAt L (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun S' => L (U * S' * Vᵀ)) (innerSL ℝ (Uᵀ * G * V)) S := by
  have h1 : HasFDerivAt (fun S' : Matrix k k' ℝ => U * S' * Vᵀ)
      ((Frobenius.leftMulCLM U).comp (Frobenius.rightMulCLM Vᵀ)) S := by
    have e : (fun S' : Matrix k k' ℝ => U * S' * Vᵀ) =
        ((Frobenius.leftMulCLM U).comp (Frobenius.rightMulCLM Vᵀ)) := by
      funext S'
      simp [Matrix.mul_assoc]
    rw [e]
    exact ContinuousLinearMap.hasFDerivAt _
  refine (hL.comp S h1).congr_fderiv ?_
  ext Z
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Frobenius.leftMulCLM_apply,
    Frobenius.rightMulCLM_apply]
  rw [Frobenius.inner_mul_left', Frobenius.inner_mul_right', Matrix.transpose_transpose,
    Matrix.mul_assoc]

omit [DecidableEq k] [DecidableEq r₁] in
/-- `∇_S L̃ = Uᵀ ∇L(U S Vᵀ) V + β ∇R(S)` where `R(S) ≠ 0`: the only block of the gradient on which
the regularizer of arXiv 2505.08022 acts. -/
theorem hasFDerivAt_Ltilde_core {L : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ} (β : ℝ)
    {U : Matrix m k ℝ} {S : Matrix k k' ℝ} {V : Matrix n k' ℝ}
    (hL : HasFDerivAt L (innerSL ℝ G) (U * S * Vᵀ)) (hS : robustR S ≠ 0) :
    HasFDerivAt (fun S' => Ltilde L β U S' V) (innerSL ℝ (Uᵀ * G * V + β • gradR S)) S := by
  refine ((hasFDerivAt_loss_core hL).add ((hasFDerivAt_robustR hS).const_mul β)).congr_fderiv ?_
  ext Z
  simp

omit [DecidableEq k] [DecidableEq r₁] in
/-- The lift `W ↦ Û ∇R(Ûᵀ W V̂) V̂ᵀ` of the coefficient gradient of the regularizer to the full
weight matrix. -/
noncomputable def latentGradR (Uh : Matrix m k ℝ) (Vh : Matrix n k' ℝ) (W : Matrix m n ℝ) :
    Matrix m n ℝ :=
  Uh * gradR (Uhᵀ * W * Vh) * Vhᵀ

omit [DecidableEq k] [DecidableEq r₁] in
/-- The gradient of the regularized objective of arXiv 2505.08022 in the latent space (7), on the
full weight matrix: at `W` with
`R(Ûᵀ W V̂) ≠ 0`, the function `W ↦ L(W) + c R(Ûᵀ W V̂)` has gradient
`∇L(W) + c Û ∇R(Ûᵀ W V̂) V̂ᵀ`. -/
theorem hasFDerivAt_latentObjective {L : Matrix m n ℝ → ℝ} {W G' : Matrix m n ℝ}
    (hL : HasFDerivAt L (innerSL ℝ G') W) (c : ℝ) (Uh : Matrix m k ℝ) (Vh : Matrix n k' ℝ)
    (hR : robustR (Uhᵀ * W * Vh) ≠ 0) :
    HasFDerivAt (fun X => L X + c * robustR (Uhᵀ * X * Vh))
      (innerSL ℝ (G' + c • latentGradR Uh Vh W)) W := by
  have h1 : HasFDerivAt (fun X : Matrix m n ℝ => Uhᵀ * X * Vh)
      ((Frobenius.leftMulCLM Uhᵀ).comp (Frobenius.rightMulCLM Vh)) W := by
    have e : (fun X : Matrix m n ℝ => Uhᵀ * X * Vh) =
        ((Frobenius.leftMulCLM Uhᵀ).comp (Frobenius.rightMulCLM Vh)) := by
      funext X
      simp [Matrix.mul_assoc]
    rw [e]
    exact ContinuousLinearMap.hasFDerivAt _
  have h2 := hL.add (((hasFDerivAt_robustR hR).comp W h1).const_mul c)
  refine h2.congr_fderiv ?_
  ext Z
  have e : ∀ X : Matrix k k' ℝ, ⟪Uh * X * Vhᵀ, Z⟫ = ⟪X, Uhᵀ * (Z * Vh)⟫ := fun X => by
    rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, Matrix.transpose_transpose]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    Frobenius.leftMulCLM_apply, Frobenius.rightMulCLM_apply, latentGradR, smul_eq_mul,
    map_add, map_smul, e]

/-- **One iteration of RobustDLRT** (Algorithm 1 of arXiv 2505.08022), as a relation between the
input `(U, S, V)`, the augmented bases `Uh`, `Vh`, the coefficient iterates `Sh 0, …, Sh sstar` and
the truncation `(P, σ, Q)`; the output is `(Uh P, diag σ, Vh Q)`.  `G` is the gradient of the loss
`L` of the layer (for the current batch).

* Lines 2–3, eq. (6): `Uh` has orthonormal columns and its range contains `U` and
  `G_U = ∇_U L(U S Vᵀ) = ∇L(U S Vᵀ) V Sᵀ`, and in the same way for `Vh`, `V`, `G_V`.  By
  `hasFDerivAt_Ltilde_left` and `hasFDerivAt_Ltilde_right` these are the gradients of `L̃`.
  The index types `k`, `k'` play the role of `2 r`.
* Line 4: `Sh 0 = Uhᵀ U S Vᵀ Vh`.
* Lines 5, 7–11, eq. (8), for the SGD optimizer: `Sh (s + 1) = Sh s - λ ∇_Ŝ L - β ∇R (Sh s)`, `s⋆`
  local steps.  (Line 9 of the algorithm has an index shift between the two terms, we follow (8).)
  Note that `λ` does not multiply `β`.  Where `R(Sh s) = 0`, `gradR` takes the value `0`.
* Lines 6, 12–16: `P`, `Q` have orthonormal columns and `‖Sh sstar - P diag(σ) Qᵀ‖ ≤ ϑ`.  This
  covers the truncated SVD with threshold `ϑ` and any other truncation with that accuracy.

The paper's input `S` is diagonal; this is not needed and not assumed. -/
structure IsRobustDLRTStep (G : Matrix m n ℝ → Matrix m n ℝ) (lr β ϑ : ℝ) (sstar : ℕ)
    (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ)
    (Uh : Matrix m k ℝ) (Vh : Matrix n k' ℝ) (Sh : ℕ → Matrix k k' ℝ)
    (P : Matrix k r₁ ℝ) (Q : Matrix k' r₁ ℝ) (σ : r₁ → ℝ) : Prop where
  orth_U : Uᵀ * U = 1
  orth_V : Vᵀ * V = 1
  orth_Uh : Uhᵀ * Uh = 1
  orth_Vh : Vhᵀ * Vh = 1
  capture_U : Uh * Uhᵀ * U = U
  capture_GU : Uh * Uhᵀ * (G (U * S * Vᵀ) * V * Sᵀ) = G (U * S * Vᵀ) * V * Sᵀ
  capture_V : Vh * Vhᵀ * V = V
  capture_GV : Vh * Vhᵀ * ((G (U * S * Vᵀ))ᵀ * U * S) = (G (U * S * Vᵀ))ᵀ * U * S
  coeff_zero : Sh 0 = Uhᵀ * (U * S * Vᵀ) * Vh
  coeff_succ : ∀ s < sstar,
    Sh (s + 1) = Sh s - lr • (Uhᵀ * G (Uh * Sh s * Vhᵀ) * Vh) - β • gradR (Sh s)
  orth_P : Pᵀ * P = 1
  orth_Q : Qᵀ * Q = 1
  truncation : ‖Sh sstar - P * Matrix.diagonal σ * Qᵀ‖ ≤ ϑ

namespace IsRobustDLRTStep

variable {G : Matrix m n ℝ → Matrix m n ℝ} {lr β ϑ : ℝ} {sstar : ℕ}
  {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
  {Uh : Matrix m k ℝ} {Vh : Matrix n k' ℝ} {Sh : ℕ → Matrix k k' ℝ}
  {P : Matrix k r₁ ℝ} {Q : Matrix k' r₁ ℝ} {σ : r₁ → ℝ}


/-- The coefficient augmentation is exact (arXiv 2505.08022, Sec. 5): `Û Ŝ₀ V̂ᵀ = U S Vᵀ`, so the
loss does not change during augmentation. -/
theorem prolong_zero (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ) :
    Uh * Sh 0 * Vhᵀ = U * S * Vᵀ := by
  have hV : Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
    have := congrArg Matrix.transpose h.capture_V
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [h.coeff_zero]
  calc Uh * (Uhᵀ * (U * S * Vᵀ) * Vh) * Vhᵀ = (Uh * Uhᵀ * U) * S * (Vᵀ * (Vh * Vhᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.capture_U, hV]

omit [DecidableEq k] [DecidableEq k'] [DecidableEq r₁] [DecidableEq r] in
/-- The Galerkin projector `Π X = Û (Ûᵀ X V̂) V̂ᵀ` onto the latent space. -/
lemma galerkin_apply (X : Matrix m n ℝ) :
    (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) X =
      Uh * (Uhᵀ * X * Vh) * Vhᵀ :=
  leftProj_rightProj_apply Uh Vh X

/-- The loss does not change during augmentation (arXiv 2505.08022, Sec. 5): the loss at the start
of the coefficient update is the loss at the input. -/
theorem loss_prolong_zero (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ)
    (L : Matrix m n ℝ → ℝ) : L (Uh * Sh 0 * Vhᵀ) = L (U * S * Vᵀ) := by
  rw [h.prolong_zero]

/-- The coefficient of a prolonged matrix: `Ûᵀ (Û X V̂ᵀ) V̂ = X`. -/
lemma restrict_prolong (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ)
    (X : Matrix k k' ℝ) : Uhᵀ * (Uh * X * Vhᵀ) * Vh = X := by
  calc Uhᵀ * (Uh * X * Vhᵀ) * Vh = (Uhᵀ * Uh) * X * (Vhᵀ * Vh) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [h.orth_Uh, h.orth_Vh, Matrix.one_mul, Matrix.mul_one]

/-- `‖Ŝ₀‖ = ‖S‖` in Algorithm 1 of arXiv 2505.08022. -/
theorem norm_coeff_zero (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ) :
    ‖Sh 0‖ = ‖S‖ := by
  have h1 : ‖Uh * Sh 0 * Vhᵀ‖ = ‖Sh 0‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal h.orth_Vh,
      Frobenius.norm_mul_of_orthonormal h.orth_Uh]
  have h2 : ‖U * S * Vᵀ‖ = ‖S‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal h.orth_V,
      Frobenius.norm_mul_of_orthonormal h.orth_U]
  rw [← h1, h.prolong_zero, h2]

/-- The regularizer of arXiv 2505.08022 sees the rank augmentation.  Since
`Ŝ₀ = (Ûᵀ U) S (V̂ᵀ V)ᵀ` has `k'` columns, `R(Ŝ₀)² = R(S)² + ‖S‖⁴ (1/r - 1/k')`; in the paper
`k' = 2 r`.  So `R(Ŝ₀) > 0` at the start of the coefficient update even if `S` is perfectly
conditioned, as `Ŝ₀` has rank at most `r`. -/
theorem robustR_coeff_zero_sq (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ) :
    robustR (Sh 0) ^ 2 =
      robustR S ^ 2 + ‖S‖ ^ 4 * (1 / Fintype.card r - 1 / Fintype.card k') := by
  have hA : (Uhᵀ * U)ᵀ * (Uhᵀ * U) = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Uᵀ * Uh * (Uhᵀ * U) = Uᵀ * (Uh * Uhᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h.capture_U, h.orth_U]
  have hB : (Vhᵀ * V)ᵀ * (Vhᵀ * V) = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Vᵀ * Vh * (Vhᵀ * V) = Vᵀ * (Vh * Vhᵀ * V) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h.capture_V, h.orth_V]
  have e : Sh 0 = Uhᵀ * U * S * (Vhᵀ * V)ᵀ := by
    rw [h.coeff_zero, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact robustR_mul_mul_sq hA hB S

/-- **The Galerkin form of a coefficient step**: with `W_s = Û Ŝ_s V̂ᵀ` and the Galerkin projector
`Π X = Û Ûᵀ X V̂ V̂ᵀ` onto the latent space (7) of arXiv 2505.08022,
`W_{s+1} = W_s - λ Π ∇L(W_s) - β Û ∇R(Ŝ_s) V̂ᵀ`. -/
theorem prolong_succ (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ) {s : ℕ}
    (hs : s < sstar) :
    Uh * Sh (s + 1) * Vhᵀ = Uh * Sh s * Vhᵀ -
      lr • (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
        (G (Uh * Sh s * Vhᵀ)) - β • (Uh * gradR (Sh s) * Vhᵀ) := by
  rw [h.coeff_succ s hs, galerkin_apply]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- **A coefficient step is a Galerkin projected gradient step** (arXiv 2505.08022, eq. (8), with
the structure `projGradStep` of `Training/Descent.lean`, used by FeDLRT and GeoLoRA).  For `λ ≠ 0`,
the prolonged iterates satisfy `W_{s+1} = W_s - λ Π (∇L(W_s) + (β/λ) Û ∇R(Ûᵀ W_s V̂) V̂ᵀ)`.  By
`hasFDerivAt_latentObjective` the argument of `Π` is the gradient of
`W ↦ L(W) + (β/λ) R(Ûᵀ W V̂)`. -/
theorem prolong_succ_eq_projGradStep (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ)
    (hlr : lr ≠ 0) {s : ℕ} (hs : s < sstar) :
    Uh * Sh (s + 1) * Vhᵀ =
      projGradStep (leftProj Uh * rightProj Vh)
        (fun W => G W + (β / lr) • latentGradR Uh Vh W) lr (Uh * Sh s * Vhᵀ) := by
  have hfix : (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
      (latentGradR Uh Vh (Uh * Sh s * Vhᵀ)) = latentGradR Uh Vh (Uh * Sh s * Vhᵀ) := by
    rw [galerkin_apply, latentGradR, h.restrict_prolong, h.restrict_prolong]
  have hg : latentGradR Uh Vh (Uh * Sh s * Vhᵀ) = Uh * gradR (Sh s) * Vhᵀ := by
    rw [latentGradR, h.restrict_prolong]
  rw [h.prolong_succ hs, projGradStep, map_add, map_smul, hfix, hg, smul_add, smul_smul,
    mul_div_cancel₀ _ hlr, sub_sub]

/-- **A coefficient step is a gradient step on the coefficient objective.**  For `λ ≠ 0` and
`R(Ŝ_s) ≠ 0`, eq. (8) of arXiv 2505.08022 is `Ŝ_{s+1} = Ŝ_s - λ ∇J(Ŝ_s)` for
`J(X) = L(Û X V̂ᵀ) + (β/λ) R(X) = L̃(Û, X, V̂)` with weight `β/λ`. -/
theorem coeff_succ_eq_gradStep (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ)
    (hlr : lr ≠ 0) {s : ℕ} (hs : s < sstar) {L : Matrix m n ℝ → ℝ}
    (hL : HasFDerivAt L (innerSL ℝ (G (Uh * Sh s * Vhᵀ))) (Uh * Sh s * Vhᵀ))
    (hR : robustR (Sh s) ≠ 0) :
    ∃ g, HasFDerivAt (fun X => Ltilde L (β / lr) Uh X Vh) (innerSL ℝ g) (Sh s) ∧
      Sh (s + 1) = Sh s - lr • g := by
  refine ⟨_, hasFDerivAt_Ltilde_core (β / lr) hL hR, ?_⟩
  rw [h.coeff_succ s hs, smul_add, smul_smul, mul_div_cancel₀ _ hlr, sub_sub]

/-- Algorithm 1 of arXiv 2505.08022 keeps the bases orthonormal: `(Û P)ᵀ (Û P) = 1`. -/
theorem orth_left (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ) :
    (Uh * P)ᵀ * (Uh * P) = 1 := by
  rw [Matrix.transpose_mul]
  calc Pᵀ * Uhᵀ * (Uh * P) = Pᵀ * ((Uhᵀ * Uh) * P) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h.orth_Uh, Matrix.one_mul, h.orth_P]

/-- Algorithm 1 of arXiv 2505.08022 keeps the bases orthonormal: `(V̂ Q)ᵀ (V̂ Q) = 1`. -/
theorem orth_right (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ) :
    (Vh * Q)ᵀ * (Vh * Q) = 1 := by
  rw [Matrix.transpose_mul]
  calc Qᵀ * Vhᵀ * (Vh * Q) = Qᵀ * ((Vhᵀ * Vh) * Q) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h.orth_Vh, Matrix.one_mul, h.orth_Q]

/-- The retraction error: the output `U₁ S₁ V₁ᵀ` of Algorithm 1 of arXiv 2505.08022 is within `ϑ`
of the latent solution `Û S̃ V̂ᵀ`. -/
theorem norm_output_sub_le (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ) :
    ‖(Uh * P) * Matrix.diagonal σ * (Vh * Q)ᵀ - Uh * Sh sstar * Vhᵀ‖ ≤ ϑ := by
  have e : (Uh * P) * Matrix.diagonal σ * (Vh * Q)ᵀ - Uh * Sh sstar * Vhᵀ =
      Uh * (P * Matrix.diagonal σ * Qᵀ - Sh sstar) * Vhᵀ := by
    rw [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  rw [e, Frobenius.norm_mul_transpose_of_orthonormal h.orth_Vh,
    Frobenius.norm_mul_of_orthonormal h.orth_Uh, norm_sub_rev]
  exact h.truncation

/-- **The augmented latent space captures the tangent gradient** (the role of (6) in
arXiv 2505.08022: the span of `Û` contains `U` and a first-order approximation of the next basis).
For invertible `S`, the Galerkin projector `Π` of the coefficient update fixes the tangent
projection `P(W) ∇L(W)` at `W = U S Vᵀ`. -/
theorem galerkin_tangentProj (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ)
    (hS : IsUnit S.det) :
    (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
        (tangentProj U V (G (U * S * Vᵀ))) = tangentProj U V (G (U * S * Vᵀ)) := by
  set A := G (U * S * Vᵀ) with hA
  have h1 : Uh * Uhᵀ * U = U := h.capture_U
  have h2 : Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
    have := congrArg Matrix.transpose h.capture_V
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have hS' : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
  have h3 : Uh * Uhᵀ * (A * V) = A * V := by
    have hc : Uh * Uhᵀ * (A * V * Sᵀ) = A * V * Sᵀ := h.capture_GU
    calc Uh * Uhᵀ * (A * V) = Uh * Uhᵀ * (A * V * Sᵀ) * (Sᵀ)⁻¹ := by
          rw [Matrix.mul_assoc (Uh * Uhᵀ), Matrix.mul_assoc (A * V),
            Matrix.mul_nonsing_inv _ hS', Matrix.mul_one]
      _ = A * V := by rw [hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS', Matrix.mul_one]
  have h4 : Uᵀ * A * (Vh * Vhᵀ) = Uᵀ * A := by
    have h5 : Vh * Vhᵀ * (Aᵀ * U) = Aᵀ * U := by
      have hc : Vh * Vhᵀ * (Aᵀ * U * S) = Aᵀ * U * S := h.capture_GV
      calc Vh * Vhᵀ * (Aᵀ * U) = Vh * Vhᵀ * (Aᵀ * U * S) * S⁻¹ := by
            rw [Matrix.mul_assoc (Vh * Vhᵀ), Matrix.mul_assoc (Aᵀ * U),
              Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
        _ = Aᵀ * U := by rw [hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
    have h6 := congrArg Matrix.transpose h5
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h6
  have e : ∀ X : Matrix m n ℝ, Uh * (Uhᵀ * X * Vh) * Vhᵀ = (Uh * Uhᵀ) * X * (Vh * Vhᵀ) :=
    fun X => by simp only [Matrix.mul_assoc]
  rw [galerkin_apply, e, tangentProj_apply, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul,
    Matrix.add_mul]
  have t1 : Uh * Uhᵀ * (U * Uᵀ * A) * (Vh * Vhᵀ) = U * Uᵀ * A := by
    calc Uh * Uhᵀ * (U * Uᵀ * A) * (Vh * Vhᵀ) = (Uh * Uhᵀ * U) * (Uᵀ * A * (Vh * Vhᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h4, Matrix.mul_assoc]
  have t2 : Uh * Uhᵀ * (A * V * Vᵀ) * (Vh * Vhᵀ) = A * V * Vᵀ := by
    calc Uh * Uhᵀ * (A * V * Vᵀ) * (Vh * Vhᵀ) = (Uh * Uhᵀ * (A * V)) * (Vᵀ * (Vh * Vhᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, h2]
  have t3 : Uh * Uhᵀ * (U * Uᵀ * A * V * Vᵀ) * (Vh * Vhᵀ) = U * Uᵀ * A * V * Vᵀ := by
    calc Uh * Uhᵀ * (U * Uᵀ * A * V * Vᵀ) * (Vh * Vhᵀ) =
        (Uh * Uhᵀ * U) * (Uᵀ * A * V) * (Vᵀ * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2]; simp only [Matrix.mul_assoc]
  rw [t1, t2, t3]

/-- The stationarity measure of the Galerkin step of arXiv 2505.08022 controls the Riemannian one,
as a consequence of `galerkin_tangentProj`: for invertible `S`,
`‖P(W) ∇L(W)‖ ≤ ‖Π ∇L(W)‖` at `W = U S Vᵀ`. -/
theorem norm_tangentProj_le (h : IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ)
    (hS : IsUnit S.det) :
    ‖tangentProj U V (G (U * S * Vᵀ))‖ ≤
      ‖(leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (G (U * S * Vᵀ))‖ :=
  norm_apply_le_of_absorbs (isOrthProj_tangentProj h.orth_U h.orth_V)
    (isOrthProj_leftProj_mul_rightProj h.orth_Uh h.orth_Vh) (h.galerkin_tangentProj hS)

end IsRobustDLRTStep

/-- **Algorithm 1 of arXiv 2505.08022 is well defined.**  For bases of `ρ` orthonormal columns with
`2 ρ ≤ m, n`, any `S`, any gradient map `G`, step sizes and `ϑ ≥ 0`, one iteration exists, with
augmented rank `2 ρ` as in the paper (rank deficient `[U | G_U]` are completed to `2 ρ` columns).
The truncation in this existence proof is the full SVD of `S̃`. -/
theorem exists_isRobustDLRTStep {ρ : ℕ} (hm : 2 * ρ ≤ Fintype.card m)
    (hn : 2 * ρ ≤ Fintype.card n) (G : Matrix m n ℝ → Matrix m n ℝ) (lr β : ℝ) {ϑ : ℝ}
    (hϑ : 0 ≤ ϑ) (sstar : ℕ) {U : Matrix m (Fin ρ) ℝ} {V : Matrix n (Fin ρ) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix (Fin ρ) (Fin ρ) ℝ) :
    ∃ (Uh : Matrix m (Fin (2 * ρ)) ℝ) (Vh : Matrix n (Fin (2 * ρ)) ℝ)
      (Sh : ℕ → Matrix (Fin (2 * ρ)) (Fin (2 * ρ)) ℝ) (ρ₁ : ℕ)
      (P Q : Matrix (Fin (2 * ρ)) (Fin ρ₁) ℝ) (σ : Fin ρ₁ → ℝ),
      IsRobustDLRTStep G lr β ϑ sstar U S V Uh Vh Sh P Q σ := by
  classical
  obtain ⟨Uh, hUh, hG, hUU⟩ := exists_augmented_basis (G (U * S * Vᵀ) * V * Sᵀ) U hm
  obtain ⟨Vh, hVh, hGV, hVV⟩ := exists_augmented_basis ((G (U * S * Vᵀ))ᵀ * U * S) V hn
  let step : Matrix (Fin (2 * ρ)) (Fin (2 * ρ)) ℝ → Matrix (Fin (2 * ρ)) (Fin (2 * ρ)) ℝ :=
    fun X => X - lr • (Uhᵀ * G (Uh * X * Vhᵀ) * Vh) - β • gradR X
  let Sh : ℕ → Matrix (Fin (2 * ρ)) (Fin (2 * ρ)) ℝ :=
    fun s => step^[s] (Uhᵀ * (U * S * Vᵀ) * Vh)
  obtain ⟨P, Q, σ, hP, hQ, -, -, -, hSVD⟩ := SVD.exists_svd (Sh sstar) rfl
  refine ⟨Uh, Vh, Sh, _, P, Q, σ, hU, hV, hUh, hVh, hUU, hG, hVV, hGV, rfl, fun s _ => ?_, hP, hQ,
    ?_⟩
  · exact Function.iterate_succ_apply' step s _
  · rw [← hSVD, sub_self, norm_zero]
    exact hϑ

end Algorithm

/-- **Bridge.** The convexified gradient `filippovGradR` is the core Filippov regularisation
`LeanDLRA.filippov` of the field `gradR` with respect to the whole space (`M = Set.univ`). The local
name is kept: the statements of this file are phrased with it. -/
theorem filippovGradR_eq_filippov (S : Matrix m r ℝ) :
    filippovGradR S = filippov gradR Set.univ S := by
  simp only [filippovGradR, filippov, inter_univ]

end LeanDLRA.Literature.P2505_08022
