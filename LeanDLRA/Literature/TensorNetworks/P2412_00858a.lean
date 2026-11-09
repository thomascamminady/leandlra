import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Foundations.Existence
import LeanDLRA.Tensor.Tucker.Basic

/-!
# Results of arXiv 2412.00858: Parallel BUG integrator for tree tensor networks

Ceruti–Kusch–Lubich–Sulz, *A parallel basis update and Galerkin integrator for tree tensor
networks*, arXiv 2412.00858. The abstract parallel Tucker BUG step `IsParTuckerBUGStep` and its
robust error bounds (`IsParTuckerBUGStep.local_error_le`, `par_tucker_global_error_le`), the
concrete Tucker instance `Tensor.isParTuckerBUGStep_of_orthonormal`, the abstract parallel TTN BUG
step `IsParTTNBUGStep` with `parTTN_global_error_le`, and its concrete instance on tree tensor
networks (`DimTree.BasisFrame.IsParBUGStep.isParTTNBUGStep`,
`DimTree.BasisFrame.parBUG_global_error`, Theorem 4.5) are in the core. This module adds the
statements of the paper that are not in the core.

## Section 2: the modified parallel matrix BUG integrator

Matrices `Y = U S Vᵀ ∈ ℝ^{m × n}` with the Frobenius norm (the paper allows complex matrices; we
work over `ℝ`). For two modes the parallel Tucker BUG step is the matrix step of Section 2, with
mode projectors `P₀ = (U₀U₀ᵀ ·, · V₀V₀ᵀ)`, new directions `Pa = (ŨŨᵀ ·, · ṼṼᵀ)` and the `K`- and
`L`-step projectors `Q₀ = (· V₀V₀ᵀ, U₀U₀ᵀ ·)`. The substeps are written for the full matrices
`K(t) V₀ᵀ`, `U₀ L(t)ᵀ` and `U₀ S(t) V₀ᵀ` (e.g. `Ẏ = F(Y) V₀ V₀ᵀ` for `Y = K V₀ᵀ`, which is (2.2)
multiplied by `V₀ᵀ`), as everywhere in the library.

* `augmented_eq_parTuckerBUG`: the augmented approximation `Û Ŝ₁ V̂ᵀ` of (2.5), with
  `S̃ᴷ = h Ũᵀ F(Y₀) V₀` and `S̃ᴸ = h U₀ᵀ F(Y₀) Ṽ`, is the abstract parallel result `parTuckerBUG`.
* `norm_newDirection_kstep_sub_le`: the replaced blocks are first-order approximations of the
  original ones (`Ũᵀ K(t₁) = S̃ᴷ + O(h²)`, p. 4), with the explicit bound `(L B + Lₜ) h²`; stated
  for abstract projectors and specialized to matrices in `norm_kstep_coefficient_sub_le`.
* `norm_normal_augmented_eq`: the computable estimate (2.6) of the normal component,
  `‖P^⊥(Y₀)[Û Ûᵀ Z V̂ V̂ᵀ]‖ = ‖Ũᵀ Z Ṽ‖`.
* `isParTuckerBUGStep_matrix`: a matrix step with orthonormal bases is an `IsParTuckerBUGStep`
  (all structural hypotheses derived; the normal-component hypothesis at `Y₀` is the paper's
  assumption with the matrix tangent projector `tangentProj U₀ V₀`).
* `modified_parallel_bug_global_error`: the robust error bound
  `‖Yₖ - A(tₖ)‖ ≤ c₁ h + c₂ ε + c₃ δ + c₄ k ϑ` claimed on p. 4 ("extends straightforwardly"),
  with explicit constants.

## Section 3: Theorem 3.1 on Tucker tensors

* `parallel_tucker_global_error`: Theorem 3.1 for steps of the parallel Tucker integrator built from
  actual basis matrices of tensors (`Tensor ι`), with orthogonality and commutation of all
  projectors derived.

## Deviations from the paper

* Real matrices and tensors instead of complex ones.
* The new directions `Ũ` have orthonormal columns and any number of them, instead of `r` columns
  filled up with zero columns (zero columns contribute nothing to `Û Ŝ₁ V̂ᵀ`).
* The normal-component assumption 2 is used in the library's form: the doubly-normal bound
  `‖(1 - Û Ûᵀ) F(t, K(t₁) V₀ᵀ) (1 - V₀V₀ᵀ)‖ ≤ ε` at the `K`- and `L`-step values (implied by the
  paper's assumption at points of rank `r`, and at rank-deficient points by continuity,
  `OpenProblems.TensorNetworks.factored_normal_of_manifold_normal`), and the tangent bound
  `‖F(Y₀) - P(Y₀) F(Y₀)‖ ≤ ε` at `Y₀`, for the tangent hull `modeProdLeOne P₀ (1 - P₀)` in the
  Tucker case (implied by the paper's assumption, `norm_sub_tangentHull_le`).
* `F` may depend on time with `‖F(t, Y) - F(s, Y)‖ ≤ Lₜ (t - s)` (`Lₜ = 0` is the paper's
  autonomous case); `F` is Lipschitz and bounded on the whole space (as in the paper).
* The truncation is any `Y₁` with `‖Y₁ - Ŷ₁‖ ≤ ϑ`, as the paper's analysis uses it.

## Not formalized

* Theorem 4.3 (rank truncation error `‖X - X̂‖ ≤ c ϑ`, `c = ‖C_τ̄‖(d_τ̄ - 1) + 1`) is quoted from
  [7, Thm A.1] and depends on the truncation Algorithm 7 of [7], which this paper does not state;
  the library's TTN bounds use a truncation tolerance at every node instead.
* The step rejection strategy (§4.6) and Remark 4.4 are algorithmic (Remark 4.4 is OP-TN-29 in
  `OpenProblems/TensorNetworks/Part3c.lean`).
-/

open Set
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Literature.P2412_00858

/-! ### First-order replacement of the off-diagonal blocks (Section 2, p. 4) -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The replaced blocks are first-order approximations** (arXiv 2412.00858, §2, p. 4: the
original block `Ũ₁ᵀ K(t₁)` equals `S̃ᴷ₁ = h Ũ₁ᵀ F(Y₀) V₀` up to `O(h²)`). Abstract form: let `YK`
solve the `K`-step `ẎK = Q F(t, YK)` from `Y₀`, and let `Pa` (the new directions `Ũ Ũᵀ`) be an
orthogonal projector with `Pa Y₀ = 0` (`Ũᵀ U₀ = 0`). If `F` is `L`-Lipschitz, bounded by `B`
and `‖F(t, Y₀) - F(t₀, Y₀)‖ ≤ Lₜ (t - t₀)`, then
`‖Pa YK(t₁) - (t₁ - t₀) Pa Q F(t₀, Y₀)‖ ≤ (L B + Lₜ) (t₁ - t₀)²`. -/
theorem norm_newDirection_kstep_sub_le {F : ℝ → E → E} {L B Lt : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hLt : 0 ≤ Lt) {Q Pa : E →L[ℝ] E} (hQ : IsOrthProj Q)
    (hPa : IsOrthProj Pa) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {Y₀ : E} (hPaY : Pa Y₀ = 0)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {YK : ℝ → E}
    (hK : ODESolution (fun t x => Q (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀) :
    ‖Pa (YK t₁) - (t₁ - t₀) • Pa (Q (F t₀ Y₀))‖ ≤ (L * B + Lt) * (t₁ - t₀) ^ 2 := by
  set w : E := Pa (Q (F t₀ Y₀)) with hw
  set g : ℝ → E := fun t => Pa (YK t) - (t - t₀) • w with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (Pa.continuous.comp_continuousOn hK.cont).sub
      ((continuous_id.sub continuous_const).smul continuous_const).continuousOn
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g (Pa (Q (F t (YK t))) - (1 : ℝ) • w)
      (Ici t) t := fun t ht =>
    (Pa.hasFDerivAt.comp_hasDerivWithinAt t (hK.deriv t ht)).sub
      (((hasDerivWithinAt_id t _).sub_const t₀).smul_const w)
  have hBK := hK.norm_sub_le_of_bounded (hB.comp_contraction Q hQ.norm_le)
  have hB0 : 0 ≤ B := hB.nonneg
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖Pa (Q (F t (YK t))) - (1 : ℝ) • w‖ ≤
      (L * B + Lt) * (t₁ - t₀) := by
    intro t ht
    have h1 : ‖YK t - Y₀‖ ≤ B * (t - t₀) := by rw [← hK₀]; exact hBK t (Ico_subset_Icc_self ht)
    have h2 : ‖F t (YK t) - F t₀ Y₀‖ ≤ L * (B * (t - t₀)) + Lt * (t - t₀) :=
      calc ‖F t (YK t) - F t₀ Y₀‖ ≤ ‖F t (YK t) - F t Y₀‖ + ‖F t Y₀ - F t₀ Y₀‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ L * (B * (t - t₀)) + Lt * (t - t₀) :=
            add_le_add ((hF t _ _).trans (mul_le_mul_of_nonneg_left h1 hL)) (hFt t ht)
    have e : Pa (Q (F t (YK t))) - (1 : ℝ) • w = Pa (Q (F t (YK t) - F t₀ Y₀)) := by
      simp [hw, map_sub]
    rw [e]
    have hts : t - t₀ ≤ t₁ - t₀ := by linarith [ht.2]
    calc ‖Pa (Q (F t (YK t) - F t₀ Y₀))‖ ≤ ‖F t (YK t) - F t₀ Y₀‖ :=
          (hPa.norm_le _).trans (hQ.norm_le _)
      _ ≤ (L * B + Lt) * (t - t₀) := by linarith
      _ ≤ (L * B + Lt) * (t₁ - t₀) :=
          mul_le_mul_of_nonneg_left hts (by positivity)
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨ht, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀, hPaY]
  rw [hg₀, sub_zero] at hmvt
  calc ‖Pa (YK t₁) - (t₁ - t₀) • w‖ = ‖g t₁‖ := rfl
    _ ≤ _ := hmvt
    _ = _ := by ring

end Abstract

/-! ### The modified parallel matrix BUG integrator (Section 2) -/

section Matrix

open scoped LeanDLRA.Frobenius

variable {m n r ra rb : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype ra] [Fintype rb]
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq ra] [DecidableEq rb]

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq ra] [DecidableEq rb] in
/-- **The augmented approximation (2.5) is the parallel result** (arXiv 2412.00858, §2). With the
augmented bases `Û = (U₀, Ũ)`, `V̂ = (V₀, Ṽ)` and the augmented coefficient matrix
`Ŝ₁ = [[S(t₁), S̃ᴸ], [S̃ᴷ, 0]]`, `S̃ᴷ = h Ũᵀ Z V₀`, `S̃ᴸ = h U₀ᵀ Z Ṽ` (`Z = F(Y₀)`), the matrix
`Û Ŝ₁ V̂ᵀ` is `parTuckerBUG P₀ Pa (U₀ S(t₁) V₀ᵀ) h Z` for the mode projectors
`P₀ = (U₀U₀ᵀ ·, · V₀V₀ᵀ)` and `Pa = (ŨŨᵀ ·, · ṼṼᵀ)`. -/
theorem augmented_eq_parTuckerBUG (U₀ : Matrix m r ℝ) (Ũ : Matrix m ra ℝ) (V₀ : Matrix n r ℝ)
    (Vt : Matrix n rb ℝ) (S : Matrix r r ℝ) (h : ℝ) (Z : Matrix m n ℝ) :
    Matrix.fromCols U₀ Ũ * Matrix.fromBlocks S (h • (U₀ᵀ * Z * Vt)) (h • (Ũᵀ * Z * V₀)) 0 *
        (Matrix.fromCols V₀ Vt)ᵀ =
      parTuckerBUG ![leftProj U₀, rightProj V₀] ![leftProj Ũ, rightProj Vt] (U₀ * S * V₀ᵀ) h Z := by
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  simp [parTuckerBUG, modeProdLeOne_succ, modeProd_succ, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, smul_add, smul_sub]
  abel

omit [Fintype m] [DecidableEq m] [DecidableEq r] [DecidableEq ra] in
/-- `(U₀, Ũ)(U₀, Ũ)ᵀ = U₀U₀ᵀ + ŨŨᵀ`. -/
private lemma fromCols_mul_transpose (U₀ : Matrix m r ℝ) (Ũ : Matrix m ra ℝ) :
    Matrix.fromCols U₀ Ũ * (Matrix.fromCols U₀ Ũ)ᵀ = U₀ * U₀ᵀ + Ũ * Ũᵀ := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

omit [DecidableEq m] [DecidableEq n] in
/-- **The normal-component estimate (2.6)** (arXiv 2412.00858, §2). Let `U₀, Ũ` and `V₀, Ṽ` have
orthonormal columns with `U₀ᵀ Ũ = 0`, `V₀ᵀ Ṽ = 0`, and `Û = (U₀, Ũ)`, `V̂ = (V₀, Ṽ)`. Then the
normal projection at `Y₀ = U₀ S₀ V₀ᵀ`, `P^⊥(Y₀) X = (1 - U₀U₀ᵀ) X (1 - V₀V₀ᵀ)`, of `Û Ûᵀ Z V̂ V̂ᵀ`
has norm `‖Ũᵀ Z Ṽ‖ =: η`. -/
theorem norm_normal_augmented_eq {U₀ : Matrix m r ℝ} {Ũ : Matrix m ra ℝ} {V₀ : Matrix n r ℝ}
    {Vt : Matrix n rb ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hŨ : Ũᵀ * Ũ = 1) (hUŨ : U₀ᵀ * Ũ = 0)
    (hV₀ : V₀ᵀ * V₀ = 1) (hVt : Vtᵀ * Vt = 1) (hVVt : V₀ᵀ * Vt = 0) (Z : Matrix m n ℝ) :
    ‖normal (leftProj U₀) (rightProj V₀)
        (Matrix.fromCols U₀ Ũ * (Matrix.fromCols U₀ Ũ)ᵀ * Z *
          (Matrix.fromCols V₀ Vt * (Matrix.fromCols V₀ Vt)ᵀ))‖ = ‖Ũᵀ * Z * Vt‖ := by
  classical
  have hL : (1 - U₀ * U₀ᵀ) * (U₀ * U₀ᵀ + Ũ * Ũᵀ) = Ũ * Ũᵀ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_assoc U₀, ← Matrix.mul_assoc U₀ᵀ,
      hU₀, Matrix.one_mul, Matrix.mul_assoc U₀ U₀ᵀ (Ũ * Ũᵀ), ← Matrix.mul_assoc U₀ᵀ, hUŨ,
      Matrix.zero_mul, Matrix.mul_zero]
    abel
  have hVVt' : Vtᵀ * V₀ = 0 := by
    rw [← Matrix.transpose_transpose V₀, ← Matrix.transpose_mul, hVVt, Matrix.transpose_zero]
  have hR : (V₀ * V₀ᵀ + Vt * Vtᵀ) * (1 - V₀ * V₀ᵀ) = Vt * Vtᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc V₀, ← Matrix.mul_assoc V₀ᵀ,
      hV₀, Matrix.one_mul, Matrix.mul_assoc Vt, ← Matrix.mul_assoc Vtᵀ, hVVt', Matrix.zero_mul,
      Matrix.mul_zero]
    abel
  have heq : normal (leftProj U₀) (rightProj V₀)
      (Matrix.fromCols U₀ Ũ * (Matrix.fromCols U₀ Ũ)ᵀ * Z *
        (Matrix.fromCols V₀ Vt * (Matrix.fromCols V₀ Vt)ᵀ)) = Ũ * ((Ũᵀ * Z * Vt) * Vtᵀ) := by
    rw [normal_leftProj_rightProj_apply, fromCols_mul_transpose, fromCols_mul_transpose,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, Matrix.mul_assoc _ (V₀ * V₀ᵀ + Vt * Vtᵀ), hR]
    simp only [Matrix.mul_assoc]
  rw [heq, Frobenius.norm_mul_of_orthonormal hŨ, ← Frobenius.norm_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Frobenius.norm_mul_of_orthonormal hVt, Frobenius.norm_transpose]

omit [DecidableEq m] [DecidableEq n] in
/-- **First-order replacement for matrices** (arXiv 2412.00858, §2, p. 4): for the `K`-step
`ẎK = F(t, YK) V₀V₀ᵀ` (i.e. `YK = K V₀ᵀ` with (2.2)) from `Y₀ = U₀ S₀ V₀ᵀ` and new directions
`Ũ ⊥ U₀`, the original block `Ũᵀ YK(t₁)` and the replacement `h Ũᵀ F(t₀, Y₀) V₀V₀ᵀ` (that is,
`S̃ᴷ₁ V₀ᵀ`) differ by at most `(L B + Lₜ) h²` in the Frobenius norm. -/
theorem norm_kstep_coefficient_sub_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B Lt : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hLt : 0 ≤ Lt)
    {U₀ : Matrix m r ℝ}
    {Ũ : Matrix m ra ℝ} {V₀ : Matrix n r ℝ} (hŨ : Ũᵀ * Ũ = 1) (hUŨ : U₀ᵀ * Ũ = 0)
    (hV₀ : V₀ᵀ * V₀ = 1) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {Y₀ : Matrix m n ℝ}
    (hY₀ : U₀ * U₀ᵀ * Y₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {YK : ℝ → Matrix m n ℝ}
    (hK : ODESolution (fun t x => rightProj V₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀) :
    ‖Ũᵀ * YK t₁ - (t₁ - t₀) • (Ũᵀ * F t₀ Y₀ * V₀ * V₀ᵀ)‖ ≤ (L * B + Lt) * (t₁ - t₀) ^ 2 := by
  have hŨU : Ũᵀ * U₀ = 0 := by
    rw [← Matrix.transpose_transpose U₀, ← Matrix.transpose_mul, hUŨ, Matrix.transpose_zero]
  have hŨY : Ũᵀ * Y₀ = 0 := by
    rw [← hY₀, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hŨU, Matrix.zero_mul, Matrix.zero_mul]
  have hPaY : leftProj Ũ Y₀ = 0 := by
    rw [leftProj_apply, Matrix.mul_assoc, hŨY, Matrix.mul_zero]
  have h := norm_newDirection_kstep_sub_le hF hL hB hLt (isOrthProj_rightProj hV₀)
    (isOrthProj_leftProj hŨ) ht hPaY hFt hK hK₀
  have e : leftProj Ũ (YK t₁) - (t₁ - t₀) • leftProj Ũ (rightProj V₀ (F t₀ Y₀)) =
      Ũ * (Ũᵀ * YK t₁ - (t₁ - t₀) • (Ũᵀ * F t₀ Y₀ * V₀ * V₀ᵀ)) := by
    simp only [leftProj_apply, rightProj_apply, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
  rw [e, Frobenius.norm_mul_of_orthonormal hŨ] at h
  exact h

omit [DecidableEq m] [DecidableEq n] in
/-- `Aᵀ B = 0` gives `Bᵀ A = 0`. -/
private lemma transpose_mul_eq_zero {k k' : Type*} {A : Matrix m k ℝ} {B : Matrix m k' ℝ}
    (h : Aᵀ * B = 0) : Bᵀ * A = 0 := by
  rw [← Matrix.transpose_transpose A, ← Matrix.transpose_mul, h, Matrix.transpose_zero]

omit [DecidableEq m] [DecidableEq n] in
private lemma leftProj_leftProj_eq_zero {k k' : Type*} [Fintype k] [Fintype k']
    {U : Matrix m k ℝ} {W : Matrix m k' ℝ} (h : Uᵀ * W = 0) (x : Matrix m n ℝ) :
    leftProj U (leftProj W x) = 0 := by
  simp only [leftProj_apply]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc U Uᵀ W, h]
  simp

omit [DecidableEq m] [DecidableEq n] in
private lemma rightProj_rightProj_eq_zero {k k' : Type*} [Fintype k] [Fintype k']
    {V : Matrix n k ℝ} {W : Matrix n k' ℝ} (h : Wᵀ * V = 0) (x : Matrix m n ℝ) :
    rightProj V (rightProj W x) = 0 := by
  simp only [rightProj_apply]
  rw [Matrix.mul_assoc (x * W) Wᵀ V, h]
  simp

local notation "𝕃" => Matrix m n ℝ →L[ℝ] Matrix m n ℝ

omit [DecidableEq m] [DecidableEq n] in
/-- **Matrix steps of the modified parallel BUG integrator are parallel Tucker BUG steps with two
modes** (arXiv 2412.00858, §2). Let `U₀, Ũ` (left) and `V₀, Ṽ` (right) have orthonormal columns
with `U₀ᵀ Ũ = 0`, `V₀ᵀ Ṽ = 0`, and let `Y₀ = U₀U₀ᵀ Y₀ V₀V₀ᵀ`. With the `K`-step `ẎK = F YK V₀V₀ᵀ`
and the `L`-step `ẎL = U₀U₀ᵀ F(YL)` from `Y₀`, captured by the augmented bases with
doubly-normal bound `ε`, the `S`-step `ẎC = U₀U₀ᵀ F(YC) V₀V₀ᵀ` from `Y₀` and the tangent bound
`‖F(t₀, Y₀) - P(Y₀) F(t₀, Y₀)‖ ≤ ε` for the tangent projector `P(Y₀) = tangentProj U₀ V₀`, the step
is an `IsParTuckerBUGStep`: orthogonality, `P₀ Pa = 0` and all commutations are derived. -/
theorem isParTuckerBUGStep_matrix {U₀ : Matrix m r ℝ} {Ũ : Matrix m ra ℝ} {V₀ : Matrix n r ℝ}
    {Vt : Matrix n rb ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hŨ : Ũᵀ * Ũ = 1) (hUŨ : U₀ᵀ * Ũ = 0)
    (hV₀ : V₀ᵀ * V₀ = 1) (hVt : Vtᵀ * Vt = 1) (hVVt : V₀ᵀ * Vt = 0)
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε t₀ t₁ : ℝ} {Y₀ : Matrix m n ℝ}
    (hY₀U : leftProj U₀ Y₀ = Y₀) (hY₀V : rightProj V₀ Y₀ = Y₀) {YK YL YC : ℝ → Matrix m n ℝ}
    (hK : ODESolution (fun t x => rightProj V₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : (leftProj U₀ + leftProj Ũ : 𝕃) (YK t₁) = YK t₁)
    (hKn : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - (leftProj U₀ + leftProj Ũ : 𝕃)) ((1 - rightProj V₀) (F t (YK t₁)))‖ ≤ ε)
    (hL : ODESolution (fun t x => leftProj U₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hLcap : (rightProj V₀ + rightProj Vt : 𝕃) (YL t₁) = YL t₁)
    (hLn : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - (rightProj V₀ + rightProj Vt : 𝕃)) ((1 - leftProj U₀) (F t (YL t₁)))‖ ≤ ε)
    (hC : ODESolution (fun t x => leftProj U₀ (rightProj V₀ (F t x))) YC t₀ t₁) (hC₀ : YC t₀ = Y₀)
    (hn : ‖F t₀ Y₀ - tangentProj U₀ V₀ (F t₀ Y₀)‖ ≤ ε) :
    IsParTuckerBUGStep F ε ![rightProj V₀, leftProj U₀] ![leftProj U₀, rightProj V₀]
      ![leftProj Ũ, rightProj Vt] t₀ t₁ Y₀ ![YK, YL] YC where
  projQ₀ i := by
    fin_cases i
    · exact isOrthProj_rightProj hV₀
    · exact isOrthProj_leftProj hU₀
  projP₀ i := by
    fin_cases i
    · exact isOrthProj_leftProj hU₀
    · exact isOrthProj_rightProj hV₀
  projPa i := by
    fin_cases i
    · exact isOrthProj_leftProj hŨ
    · exact isOrthProj_rightProj hVt
  orth i x := by
    fin_cases i
    · exact leftProj_leftProj_eq_zero hUŨ x
    · exact rightProj_rightProj_eq_zero (transpose_mul_eq_zero hVVt) x
  comm₀₀ i j x := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact leftProj_rightProj_comm U₀ V₀ x
    · exact (leftProj_rightProj_comm U₀ V₀ x).symm
    · rfl
  comm₀a i j x := by
    fin_cases i <;> fin_cases j
    · exact (leftProj_leftProj_eq_zero hUŨ x).trans
        (leftProj_leftProj_eq_zero (transpose_mul_eq_zero hUŨ) x).symm
    · exact leftProj_rightProj_comm U₀ Vt x
    · exact (leftProj_rightProj_comm Ũ V₀ x).symm
    · exact (rightProj_rightProj_eq_zero (transpose_mul_eq_zero hVVt) x).trans
        (rightProj_rightProj_eq_zero hVVt x).symm
  commaa i j x := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact leftProj_rightProj_comm Ũ Vt x
    · exact (leftProj_rightProj_comm Ũ Vt x).symm
    · rfl
  start₀ i := by
    fin_cases i
    · exact hY₀U
    · exact hY₀V
  kSol i := by
    fin_cases i
    · exact hK
    · exact hL
  kStart i := by
    fin_cases i
    · exact hK₀
    · exact hL₀
  kCap i := by
    fin_cases i
    · exact hKcap
    · exact hLcap
  kNormal i := by
    fin_cases i
    · exact hKn
    · exact hLn
  cSol := by simpa using hC
  cStart := hC₀
  normal₀ := by
    rw [modeProdLeOne_compl_two]
    exact hn

/-- Non-vacuity of `isParTuckerBUGStep_matrix`: rank-zero bases, the zero field and the zero
matrix satisfy all its hypotheses. -/
example : IsParTuckerBUGStep (E := Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) 0
    ![rightProj (0 : Matrix (Fin 1) (Fin 0) ℝ), leftProj (0 : Matrix (Fin 1) (Fin 0) ℝ)]
    ![leftProj (0 : Matrix (Fin 1) (Fin 0) ℝ), rightProj (0 : Matrix (Fin 1) (Fin 0) ℝ)]
    ![leftProj (0 : Matrix (Fin 1) (Fin 0) ℝ), rightProj (0 : Matrix (Fin 1) (Fin 0) ℝ)]
    0 1 0 ![fun _ => 0, fun _ => 0] (fun _ => 0) := by
  have hz : ODESolution (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => 0) 0 1 :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  exact isParTuckerBUGStep_matrix (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (Subsingleton.elim _ _) (map_zero _) (map_zero _) (by simpa using hz) rfl (map_zero _)
    (fun _ _ => by simp) (by simpa using hz) rfl (map_zero _) (fun _ _ => by simp)
    (by simpa using hz) rfl (by simp)

omit [DecidableEq m] [DecidableEq n] in
/-- **Robust error bound of the modified parallel matrix BUG integrator** (arXiv 2412.00858, §2,
p. 4: `‖Yₖ - A(tₖ)‖_F ≤ c₁ h + c₂ ε + c₃ δ + c₄ k ϑ`, stated there without proof as a
straightforward extension of [4, Thm 4.1]). Let `F` be `L`-Lipschitz, bounded by `B`, continuous
in time and `Lₜ`-Lipschitz in time, `tₙ = t₀ + n h` with `0 ≤ h ≤ H`, `A` the exact solution on
`[t₀, t_N]` and `‖Y 0 - A t₀‖ ≤ δ`. Let step `n < N` have rank `r n` with old bases `U n`, `V n`,
new directions `Ũ n`, `Ṽ n` (orthonormal columns, `Uᵀ Ũ = 0`, `Vᵀ Ṽ = 0`), the substeps of
`isParTuckerBUGStep_matrix` from `Y n` with bound `ε`, and `Y (n + 1)` within `ϑ` of the
augmented approximation `parTuckerBUG` (2.5) (`augmented_eq_parTuckerBUG`). Then for `n ≤ N`,
`n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ e^{L T} δ + T e^{L T} c₁ ε + T e^{L T} c₂ h + e^{L T} n ϑ,

with `c₁ = parTuckerC₁ 2 L H` and `c₂ = parTuckerC₂ 2 L B Lₜ H`, independent of the singular
values of the approximations. -/
theorem modified_parallel_bug_global_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε Lt : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → ‖F t x - F s x‖ ≤ Lt * (t - s)) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {rk ra rb : ℕ → ℕ} {U : ∀ k, Matrix m (Fin (rk k)) ℝ} {V : ∀ k, Matrix n (Fin (rk k)) ℝ}
    {Ũ : ∀ k, Matrix m (Fin (ra k)) ℝ} {Vt : ∀ k, Matrix n (Fin (rb k)) ℝ}
    (hU : ∀ k < N, (U k)ᵀ * U k = 1) (hŨ : ∀ k < N, (Ũ k)ᵀ * Ũ k = 1)
    (hUŨ : ∀ k < N, (U k)ᵀ * Ũ k = 0) (hV : ∀ k < N, (V k)ᵀ * V k = 1)
    (hVt : ∀ k < N, (Vt k)ᵀ * Vt k = 1) (hVVt : ∀ k < N, (V k)ᵀ * Vt k = 0)
    {Y : ℕ → Matrix m n ℝ} (hYU : ∀ k < N, leftProj (U k) (Y k) = Y k)
    (hYV : ∀ k < N, rightProj (V k) (Y k) = Y k) {YK YL YC : ℕ → ℝ → Matrix m n ℝ}
    (hK : ∀ k < N, ODESolution (fun t x => rightProj (V k) (F t x)) (YK k) (t₀ + k * h)
      (t₀ + (k + 1) * h))
    (hK₀ : ∀ k < N, YK k (t₀ + k * h) = Y k)
    (hKcap : ∀ k < N, (leftProj (U k) + leftProj (Ũ k) : 𝕃) (YK k (t₀ + (k + 1) * h)) =
      YK k (t₀ + (k + 1) * h))
    (hKn : ∀ k < N, ∀ t ∈ Icc (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖(1 - (leftProj (U k) + leftProj (Ũ k) : 𝕃)) ((1 - rightProj (V k))
        (F t (YK k (t₀ + (k + 1) * h))))‖ ≤ ε)
    (hLs : ∀ k < N, ODESolution (fun t x => leftProj (U k) (F t x)) (YL k) (t₀ + k * h)
      (t₀ + (k + 1) * h))
    (hL₀ : ∀ k < N, YL k (t₀ + k * h) = Y k)
    (hLcap : ∀ k < N, (rightProj (V k) + rightProj (Vt k) : 𝕃) (YL k (t₀ + (k + 1) * h)) =
      YL k (t₀ + (k + 1) * h))
    (hLn : ∀ k < N, ∀ t ∈ Icc (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖(1 - (rightProj (V k) + rightProj (Vt k) : 𝕃)) ((1 - leftProj (U k))
        (F t (YL k (t₀ + (k + 1) * h))))‖ ≤ ε)
    (hC : ∀ k < N, ODESolution (fun t x => leftProj (U k) (rightProj (V k) (F t x))) (YC k)
      (t₀ + k * h) (t₀ + (k + 1) * h))
    (hC₀ : ∀ k < N, YC k (t₀ + k * h) = Y k)
    (hn : ∀ k < N, ‖F (t₀ + k * h) (Y k) - tangentProj (U k) (V k) (F (t₀ + k * h) (Y k))‖ ≤ ε)
    {ϑ : ℝ}
    (htr : ∀ k < N, ‖Y (k + 1) - parTuckerBUG ![leftProj (U k), rightProj (V k)]
      ![leftProj (Ũ k), rightProj (Vt k)] (YC k (t₀ + (k + 1) * h)) h (F (t₀ + k * h) (Y k))‖
        ≤ ϑ)
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T →
      ‖Y k - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * parTuckerC₁ 2 L H * ε
        + T * Real.exp (L * T) * parTuckerC₂ 2 L B Lt H * h + Real.exp (L * T) * (k * ϑ) := by
  classical
  have hex : ∀ k : ℕ, ∃ Φ : ℝ → Matrix m n ℝ, ODESolution F Φ (t₀ + k * h) (t₀ + (k + 1) * h) ∧
      Φ (t₀ + k * h) = Y k := fun k =>
    exists_ODESolution hF hB hcont (by nlinarith) (Y k)
  choose Φ hΦ hΦ₀ using hex
  exact par_tucker_global_error_le hF hL hB hcont hε hLt hFt hh hhH hA
    (Q := fun k => ![rightProj (V k), leftProj (U k)])
    (P := fun k => ![leftProj (U k), rightProj (V k)])
    (Pa := fun k => ![leftProj (Ũ k), rightProj (Vt k)]) (YK := fun k => ![YK k, YL k])
    (fun k hk => isParTuckerBUGStep_matrix (hU k hk) (hŨ k hk) (hUŨ k hk) (hV k hk) (hVt k hk)
      (hVVt k hk) (hYU k hk) (hYV k hk) (hK k hk) (hK₀ k hk) (hKcap k hk) (hKn k hk) (hLs k hk)
      (hL₀ k hk) (hLcap k hk) (hLn k hk) (hC k hk) (hC₀ k hk) (hn k hk))
    htr (fun k _ => hΦ k) (fun k _ => hΦ₀ k) hδ

end Matrix

/-! ### Theorem 3.1 on Tucker tensors -/

section Tucker

open Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)]

/-- **Theorem 3.1 of arXiv 2412.00858 on Tucker tensors.** Let `F` be a field on the tensor space
`Tensor ι` (`d` modes) that is `L`-Lipschitz, bounded by `B`, continuous in time and
`Lₜ`-Lipschitz in time, `tₙ = t₀ + n h`, `0 ≤ h ≤ H`, `A` the exact solution and
`‖Y 0 - A t₀‖ ≤ δ`. Let step `n < N` of the parallel Tucker integrator have old mode bases
`U₀ n i`, new directions `Ũ n i` (orthonormal columns, `U₀ᵀ Ũ = 0`) and co-range bases `V₀ n i` of
the `Kᵢ`-steps (orthonormal columns, rows indexed by the modes `≠ i`), with the substeps of
`Tensor.isParTuckerBUGStep_of_orthonormal` (doubly-normal bound `ε` at the `Kᵢ`-values, tangent
hull bound `ε` at `Y n`), and let `Y (n + 1)` be within `ϑ` of the augmented tensor
`parTuckerBUG P₀ Pa (YC n t_{n+1}) h F(tₙ, Yₙ)` (blocks (3.3)–(3.4)). Then for `n ≤ N`, `n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ e^{L T} δ + T e^{L T} c₁ ε + T e^{L T} c₂ h + e^{L T} n ϑ

with `c₁ = parTuckerC₁ d L H`, `c₂ = parTuckerC₂ d L B Lₜ H`; the constants do not depend on
singular values of matricizations of the core tensors. -/
theorem parallel_tucker_global_error {F : ℝ → Tensor ι → Tensor ι} {L B ε Lt : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → ‖F t x - F s x‖ ≤ Lt * (t - s)) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h))
    {r ra s : ℕ → Fin d → ℕ} {U₀ : ∀ n i, Matrix (ι i) (Fin (r n i)) ℝ}
    {Ũ : ∀ n i, Matrix (ι i) (Fin (ra n i)) ℝ}
    {V₀ : ∀ n i, Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (Fin (s n i)) ℝ}
    (hU₀ : ∀ n < N, ∀ i, (U₀ n i)ᵀ * U₀ n i = 1) (hŨ : ∀ n < N, ∀ i, (Ũ n i)ᵀ * Ũ n i = 1)
    (horth : ∀ n < N, ∀ i, (U₀ n i)ᵀ * Ũ n i = 0)
    (hV₀ : ∀ n < N, ∀ i, (V₀ n i)ᵀ * V₀ n i = 1) {Y : ℕ → Tensor ι}
    (h₀ : ∀ n < N, ∀ i, modeProj i (U₀ n i) (Y n) = Y n)
    {YK : ℕ → Fin d → ℝ → Tensor ι} {YC : ℕ → ℝ → Tensor ι}
    (hK : ∀ n < N, ∀ i, ODESolution (fun t x => actOn (· ≠ i) (V₀ n i * (V₀ n i)ᵀ) (F t x))
      (YK n i) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hK₀ : ∀ n < N, ∀ i, YK n i (t₀ + n * h) = Y n)
    (hcap : ∀ n < N, ∀ i, (modeProj i (U₀ n i) + modeProj i (Ũ n i)) (YK n i (t₀ + (n + 1) * h))
      = YK n i (t₀ + (n + 1) * h))
    (hKn : ∀ n < N, ∀ i, ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - (modeProj i (U₀ n i) + modeProj i (Ũ n i)))
        ((1 - actOn (· ≠ i) (V₀ n i * (V₀ n i)ᵀ)) (F t (YK n i (t₀ + (n + 1) * h))))‖ ≤ ε)
    (hC : ∀ n < N, ODESolution (fun t x => modeProd (fun i => modeProj i (U₀ n i)) (F t x))
      (YC n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hC₀ : ∀ n < N, YC n (t₀ + n * h) = Y n)
    (hn : ∀ n < N, ‖F (t₀ + n * h) (Y n) - modeProdLeOne (fun i => modeProj i (U₀ n i))
      (fun i => 1 - modeProj i (U₀ n i)) (F (t₀ + n * h) (Y n))‖ ≤ ε) {ϑ : ℝ}
    (htr : ∀ n < N, ‖Y (n + 1) - parTuckerBUG (fun i => modeProj i (U₀ n i))
      (fun i => modeProj i (Ũ n i)) (YC n (t₀ + (n + 1) * h)) h (F (t₀ + n * h) (Y n))‖ ≤ ϑ)
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * parTuckerC₁ d L H * ε
        + T * Real.exp (L * T) * parTuckerC₂ d L B Lt H * h + Real.exp (L * T) * (n * ϑ) := by
  have hex : ∀ n : ℕ, ∃ Φ : ℝ → Tensor ι, ODESolution F Φ (t₀ + n * h) (t₀ + (n + 1) * h) ∧
      Φ (t₀ + n * h) = Y n := fun n =>
    exists_ODESolution hF hB hcont (by nlinarith) (Y n)
  choose Φ hΦ hΦ₀ using hex
  exact par_tucker_global_error_le hF hL hB hcont hε hLt hFt hh hhH hA
    (fun n hN => isParTuckerBUGStep_of_orthonormal (hU₀ n hN) (hŨ n hN) (horth n hN) (hV₀ n hN)
      (h₀ n hN) (hK n hN) (hK₀ n hN) (hcap n hN) (hKn n hN) (hC n hN) (hC₀ n hN) (hn n hN))
    htr (fun n _ => hΦ n) (fun n _ => hΦ₀ n) hδ

end Tucker

end LeanDLRA.Literature.P2412_00858
