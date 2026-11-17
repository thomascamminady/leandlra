import LeanDLRA.Matrix.Frobenius

/-!
# Fast Forward for factorized (LoRA) versus full-rank training: the quadratic model

Open problem OP-TR-45 of `docs/catalogue/survey/open-problems.json` (arXiv 2409.04206, Sec. 6.1,
Fig. 7–8, App. D).  *Fast Forward* (FF) repeats the last optimizer update,
`x ↦ x + τ (x_t - x_{t-1})`, while a small validation loss keeps decreasing.  Empirically it saves
compute for LoRA (even at full LoRA rank) but "the loss rises at the first simulated step" for
full-rank fine-tuning.  The conjectured explanation is that the factorization makes consecutive
updates nearly collinear through the induced preconditioner `Ẇ = -(B Bᵀ ∇L + ∇L AᵀA)`.

This file analyzes the quadratic model `L(X) = ⟪X - D, H (X - D)⟫ / 2` on the fine-tuning
*increment* `X` (`H` a self-adjoint operator on `ℝ^{m×n}`, `D = W* - W₀` the target increment),
with gradient descent of step `h` either on `X` itself (full rank) or on LoRA factors `X = B A`.
All statements are exact algebraic identities about the actual steps and the actual FF rays.

* `quad_add_smul`: `L(X + s V) = L(X) + s ⟪G, V⟫ + s² ⟪H V, V⟫ / 2`, `G = H (X - D)`.
* `full_ff_loss`, `full_ff_step_lt_iff`, `full_ff_ascends`: the full-rank FF ray is
  `X₀ - (1+τ) h G`; the `k`-th simulated step lowers the loss iff `(2k+3) h ⟪H G, G⟫ < 2 ‖G‖²`,
  and if `‖G‖² ≤ h ⟪H G, G⟫` **no** FF step lowers the loss, while GD itself still converges
  whenever `h μ < 2` for the active curvatures (`full_ff_ascends_scalar`,
  `fullStep_sub_target_scalar`: `H = μ • id`, `1 ≤ h μ < 2`).  This is
  exactly the edge-of-stability regime of full-rank training, where the gradient is dominated by
  curvatures `μ` with `h μ ≈ 2 > 1`.
* `lora_init_step`, `lora_ff_path`: from LoRA's initialization `B = 0` the factor step is
  `B₁ = -h G Aᵀ`, `A₁ = A`, and the FF ray *in factor space* `(B₁ + τ B₁) (A₁ + τ · 0)` is the
  weight-space line `-(1+τ) h G AᵀA`: the fixed preconditioner `AᵀA` replaces the identity.
* `lora_ff_loss`, `lora_ff_step_lt_iff`, `lora_ff_step_of_small`: the `k`-th LoRA FF step lowers
  the loss iff `(2k+3) h ⟪H P, P⟫ < 2 ‖G Aᵀ‖²`, `P = G AᵀA`; a sufficient condition is
  `(2k+3) h Λ ‖A‖² < 2` where `⟪H X, X⟫ ≤ Λ ‖X‖²`.  The number of profitable FF steps is thus
  at least `1 / (h Λ ‖A‖²) - 3/2`, independent of the full-rank criterion: the factorization
  rescales the effective step along every curvature direction by the Gram matrix `AᵀA`.
* `ff_dichotomy`, `ff_dichotomy_instance`: both can happen at the same `H`, `D`, `h`: the
  full-rank first FF step raises the loss and the LoRA first FF step lowers it (instance: `1×1`,
  `H = 15`, `h = 1/10`, `A = 1/2`).
* `factor_loss_expansion`, `factor_curvature_le`: for arbitrary factors the loss along a factor
  direction `(ΔB, ΔA)` is the quartic
  `L(BA) + s ⟪G, M⟫ + s² (⟪H M, M⟫ + 2 ⟪G, N⟫) / 2 + s³ ⟪H M, N⟫ + s⁴ ⟪H N, N⟫ / 2`
  (`M = ΔB A + B ΔA`, `N = ΔB ΔA`), whose curvature is at most
  `(Λ (‖A‖² + ‖B‖²) + ‖G‖) (‖ΔB‖² + ‖ΔA‖²)`, versus `⟪H V, V⟫` (up to `Λ ‖V‖²`) for the full
  space.  For balanced factors `‖A‖ = ‖B‖` and `‖A‖² + ‖B‖² ≤ 2 √r ‖B A‖`
  (`balanced_norm_eq`, `balanced_normSq_add_le`): the curvature seen by the factor dynamics
  is proportional to the size of the *increment* (and of the gradient), not to the curvature of
  the pretrained loss.  This is rank-independent, consistent with FF working at full LoRA rank
  and failing for full-rank fine-tuning, and predicts failure when the increment is `O(1)`
  (training from scratch, the paper's Limitations).
* `full_consecutive_collinear`, `lora_consecutive_orthogonal`: on the isotropic model `H = 1`
  the full-rank consecutive updates are exactly collinear, `ΔX₁ = (1-h) ΔX₀`, and one FF step
  reaches the minimizer (`full_ff_isotropic_exact`), while the LoRA consecutive weight updates
  can be **orthogonal** and the LoRA FF step raises the loss (`lora_ff_isotropic_ascends`).  So
  "the factorization makes consecutive updates collinear" is false as a general mechanism; the
  distinction between the two parametrizations lies in the effective curvature, not in
  collinearity.

What stays open: Adam in place of GD (the paper's optimizer), losses beyond the quadratic
model, and the length of the FF window after several SGD steps (App. D of the paper).  Prior
work: Arora–Cohen–Hazan 2018 (the preconditioner `(WWᵀ)^{1/2} ∇L + ∇L (WᵀW)^{1/2}` of balanced
factor flow), Cohen et al. 2021 (edge of stability), `LeanDLRA.FactorizedDynamics.factorGD_product`.
-/

open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpTR45

open LeanDLRA LeanDLRA.Frobenius

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-! ### The quadratic model -/

/-- The quadratic loss `L(X) = ⟪X - D, H (X - D)⟫ / 2` on the increment `X`. -/
noncomputable def quad (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (D X : Matrix m n ℝ) : ℝ :=
  ⟪X - D, H (X - D)⟫ / 2

/-- Its gradient `G(X) = H (X - D)` (for self-adjoint `H`). -/
noncomputable def grad (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (D X : Matrix m n ℝ) :
    Matrix m n ℝ :=
  H (X - D)

/-- `H` is self-adjoint for the Frobenius inner product. -/
def IsSelfAdj (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) : Prop :=
  ∀ X Y : Matrix m n ℝ, ⟪H X, Y⟫ = ⟪X, H Y⟫

/-- Exact second-order expansion of the quadratic model along a line. -/
theorem quad_add_smul {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D X V : Matrix m n ℝ) (s : ℝ) :
    quad H D (X + s • V) = quad H D X + s * ⟪grad H D X, V⟫ + s ^ 2 * ⟪H V, V⟫ / 2 := by
  simp only [quad, grad]
  have h1 : X + s • V - D = (X - D) + s • V := by abel
  have h2 : ⟪V, H (X - D)⟫ = ⟪X - D, H V⟫ := by rw [← hH, real_inner_comm]
  have h3 : ⟪H V, V⟫ = ⟪V, H V⟫ := real_inner_comm _ _
  rw [h1, map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
    inner_smul_right, inner_smul_left, inner_smul_right, h2, h3, hH (X - D) V]
  simp only [RCLike.conj_to_real]
  ring

/-- Specialization `L(X - s V)`. -/
theorem quad_sub_smul {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D X V : Matrix m n ℝ) (s : ℝ) :
    quad H D (X - s • V) = quad H D X - s * ⟪grad H D X, V⟫ + s ^ 2 * ⟪H V, V⟫ / 2 := by
  rw [sub_eq_add_neg, ← neg_smul, quad_add_smul hH]; ring

/-! ### Full-rank gradient descent and its Fast Forward ray -/

/-- One full-rank GD step on the increment. -/
noncomputable def fullStep (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (D : Matrix m n ℝ) (h : ℝ)
    (X : Matrix m n ℝ) : Matrix m n ℝ :=
  X - h • grad H D X

/-- The FF ray after one full-rank step, `X₁ + τ (X₁ - X₀) = X₀ - (1+τ) h G`. -/
theorem full_ff_path (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (D : Matrix m n ℝ) (h τ : ℝ)
    (X₀ : Matrix m n ℝ) :
    fullStep H D h X₀ + τ • (fullStep H D h X₀ - X₀) = X₀ - ((1 + τ) * h) • grad H D X₀ := by
  simp only [fullStep]; module

/-- Loss along the full-rank FF ray: a parabola in the arc length `s = (1+τ) h`. -/
theorem full_ff_loss {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D X₀ : Matrix m n ℝ) (s : ℝ) :
    quad H D (X₀ - s • grad H D X₀) =
      quad H D X₀ - s * ‖grad H D X₀‖ ^ 2 + s ^ 2 * ⟪H (grad H D X₀), grad H D X₀⟫ / 2 := by
  rw [quad_sub_smul hH, real_inner_self_eq_norm_sq]

/-- The change of loss over the `k`-th simulated full-rank step (`k = 0` is the first). -/
theorem full_ff_step_sub {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D X₀ : Matrix m n ℝ) (h : ℝ) (k : ℕ) :
    quad H D (X₀ - ((k + 2) * h) • grad H D X₀) - quad H D (X₀ - ((k + 1) * h) • grad H D X₀) =
      h / 2 * ((2 * k + 3) * h * ⟪H (grad H D X₀), grad H D X₀⟫ - 2 * ‖grad H D X₀‖ ^ 2) := by
  rw [full_ff_loss hH, full_ff_loss hH]; ring

/-- **Full-rank FF criterion.**  The `k`-th simulated step lowers the loss iff
`(2k+3) h ⟪H G, G⟫ < 2 ‖G‖²`; for `k = 0`: `3 h ⟪H G, G⟫ < 2 ‖G‖²`, which fails as soon as the
gradient is dominated by curvatures `μ` with `h μ ≥ 2/3`. -/
theorem full_ff_step_lt_iff {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D X₀ : Matrix m n ℝ) {h : ℝ} (hh : 0 < h) (k : ℕ) :
    quad H D (X₀ - ((k + 2) * h) • grad H D X₀) < quad H D (X₀ - ((k + 1) * h) • grad H D X₀) ↔
      (2 * k + 3) * h * ⟪H (grad H D X₀), grad H D X₀⟫ < 2 * ‖grad H D X₀‖ ^ 2 := by
  have hp : 0 < h / 2 := by positivity
  rw [← sub_neg, full_ff_step_sub hH, mul_neg_iff]
  have hn : ¬ h / 2 < 0 := not_lt.mpr hp.le
  simp only [hp, true_and, hn, false_and, or_false, sub_neg]

/-- **Full-rank FF fails at every simulated step** when the GD step is already at or beyond the
vertex of the parabola along `G`, i.e. `‖G‖² ≤ h ⟪H G, G⟫`.  This is the edge-of-stability regime
`h μ ∈ [1, 2)` of the dominant curvature, in which GD still converges
(`fullStep_sub_target_scalar`). -/
theorem full_ff_ascends {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D X₀ : Matrix m n ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hG : ‖grad H D X₀‖ ^ 2 ≤ h * ⟪H (grad H D X₀), grad H D X₀⟫) (k : ℕ) :
    quad H D (X₀ - ((k + 1) * h) • grad H D X₀) ≤
      quad H D (X₀ - ((k + 2) * h) • grad H D X₀) := by
  rw [← sub_nonneg, full_ff_step_sub hH]
  have h0 : 0 ≤ h * ⟪H (grad H D X₀), grad H D X₀⟫ := le_trans (sq_nonneg _) hG
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 2 * ‖grad H D X₀‖ ^ 2 ≤ (2 * k + 3) * h * ⟪H (grad H D X₀), grad H D X₀⟫ := by
    nlinarith
  have : 0 ≤ h / 2 := by positivity
  nlinarith

/-- For the scalar Hessian `H = μ • id` the full-rank step contracts the distance to the target by
`1 - h μ`: GD converges for `h μ < 2`, in particular throughout `h μ ∈ [1, 2)` where
`full_ff_ascends` applies (`h ⟪H G, G⟫ = h μ ‖G‖²`). -/
theorem fullStep_sub_target_scalar (D X : Matrix m n ℝ) (h μ : ℝ) :
    fullStep (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D h X - D = (1 - h * μ) • (X - D) := by
  simp only [fullStep, grad, smul_apply, ContinuousLinearMap.id_apply]
  module

/-- `μ • id` is self-adjoint. -/
theorem isSelfAdj_smul_id (μ : ℝ) :
    IsSelfAdj (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) := by
  intro X Y
  simp only [smul_apply, ContinuousLinearMap.id_apply, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]

/-- `⟪H X, X⟫ = μ ‖X‖²` for `H = μ • id`. -/
theorem inner_smul_id_self (μ : ℝ) (X : Matrix m n ℝ) :
    ⟪(μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) X, X⟫ = μ * ‖X‖ ^ 2 := by
  simp only [smul_apply, ContinuousLinearMap.id_apply, inner_smul_left,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]

/-- **Instance**: `H = μ • id`, `1 ≤ h μ < 2` (say `μ = 15`, `h = 1/10`): GD contracts the error
by `|1 - hμ| < 1` at every step, yet every Fast Forward step increases the loss. -/
theorem full_ff_ascends_scalar (D X₀ : Matrix m n ℝ) {h μ : ℝ} (hh : 0 ≤ h) (hμ : 1 ≤ h * μ)
    (k : ℕ) :
    quad (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D
        (X₀ - ((k + 1) * h) • grad (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D X₀) ≤
      quad (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D
        (X₀ - ((k + 2) * h) • grad (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D X₀) := by
  refine full_ff_ascends (isSelfAdj_smul_id μ) D X₀ hh ?_ k
  rw [inner_smul_id_self]
  nlinarith [sq_nonneg ‖grad (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D X₀‖]

/-! ### LoRA factor descent from `B = 0` and its Fast Forward ray -/

/-- One simultaneous GD step on the LoRA factors of the increment `X = B A`:
`B ↦ B - h G Aᵀ`, `A ↦ A - h Bᵀ G` with `G = ∇L(B A)`. -/
noncomputable def factorStep (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (D : Matrix m n ℝ) (h : ℝ)
    (B : Matrix m r ℝ) (A : Matrix r n ℝ) : Matrix m r ℝ × Matrix r n ℝ :=
  (B - h • (grad H D (B * A) * Aᵀ), A - h • (Bᵀ * grad H D (B * A)))

/-- LoRA initialization `B = 0`: the first factor step is `B₁ = -h G Aᵀ`, `A₁ = A` with
`G = ∇L(0) = -H D`. -/
theorem lora_init_step (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (D : Matrix m n ℝ) (h : ℝ)
    (A : Matrix r n ℝ) :
    factorStep H D h 0 A = (-h • (grad H D 0 * Aᵀ), A) := by
  simp [factorStep]

/-- The FF ray in **factor space** after the first LoRA step, `(B₁ + τ (B₁ - 0)) (A₁ + τ (A₁ - A))`,
is the weight-space line `-(1+τ) h G AᵀA`: the identity preconditioner of the full-rank ray
(`full_ff_path`) is replaced by the Gram matrix `AᵀA`. -/
theorem lora_ff_path (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (D : Matrix m n ℝ) (h τ : ℝ)
    (A : Matrix r n ℝ) :
    ((factorStep H D h 0 A).1 + τ • ((factorStep H D h 0 A).1 - 0)) *
        ((factorStep H D h 0 A).2 + τ • ((factorStep H D h 0 A).2 - A)) =
      0 - ((1 + τ) * h) • (grad H D 0 * Aᵀ * A) := by
  rw [lora_init_step]
  simp only [sub_zero, sub_self, smul_zero, add_zero, zero_sub, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_assoc]
  module

/-- Loss along the LoRA FF line, `P = G AᵀA`: the linear coefficient is `‖G Aᵀ‖²` (the squared
factor gradient), not `‖G‖²`. -/
theorem lora_ff_loss {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D : Matrix m n ℝ) (A : Matrix r n ℝ) (s : ℝ) :
    quad H D (0 - s • (grad H D 0 * Aᵀ * A)) =
      quad H D 0 - s * ‖grad H D 0 * Aᵀ‖ ^ 2 +
        s ^ 2 * ⟪H (grad H D 0 * Aᵀ * A), grad H D 0 * Aᵀ * A⟫ / 2 := by
  rw [quad_sub_smul hH, inner_mul_right', real_inner_self_eq_norm_sq]

/-- The change of loss over the `k`-th simulated LoRA step. -/
theorem lora_ff_step_sub {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D : Matrix m n ℝ) (A : Matrix r n ℝ) (h : ℝ) (k : ℕ) :
    quad H D (0 - ((k + 2) * h) • (grad H D 0 * Aᵀ * A)) -
        quad H D (0 - ((k + 1) * h) • (grad H D 0 * Aᵀ * A)) =
      h / 2 * ((2 * k + 3) * h * ⟪H (grad H D 0 * Aᵀ * A), grad H D 0 * Aᵀ * A⟫ -
        2 * ‖grad H D 0 * Aᵀ‖ ^ 2) := by
  rw [lora_ff_loss hH, lora_ff_loss hH]; ring

/-- **LoRA FF criterion.**  The `k`-th simulated LoRA step lowers the loss iff
`(2k+3) h ⟪H P, P⟫ < 2 ‖G Aᵀ‖²`, `P = G AᵀA`. -/
theorem lora_ff_step_lt_iff {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D : Matrix m n ℝ) (A : Matrix r n ℝ) {h : ℝ} (hh : 0 < h) (k : ℕ) :
    quad H D (0 - ((k + 2) * h) • (grad H D 0 * Aᵀ * A)) <
        quad H D (0 - ((k + 1) * h) • (grad H D 0 * Aᵀ * A)) ↔
      (2 * k + 3) * h * ⟪H (grad H D 0 * Aᵀ * A), grad H D 0 * Aᵀ * A⟫ <
        2 * ‖grad H D 0 * Aᵀ‖ ^ 2 := by
  have hp : 0 < h / 2 := by positivity
  have hn : ¬ h / 2 < 0 := not_lt.mpr hp.le
  rw [← sub_neg, lora_ff_step_sub hH, mul_neg_iff]
  simp only [hp, true_and, hn, false_and, or_false, sub_neg]

/-- **LoRA FF succeeds under a condition on the factor alone.**  If `⟪H X, X⟫ ≤ Λ ‖X‖²` and
`(2k+3) h Λ ‖A‖² < 2`, the `k`-th simulated LoRA step lowers the loss, whatever the full-rank
criterion says: the Gram matrix `AᵀA` rescales the step along every curvature direction, so at
least `1 / (h Λ ‖A‖²) - 3/2` simulated steps are profitable. -/
theorem lora_ff_step_of_small {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ X : Matrix m n ℝ, ⟪H X, X⟫ ≤ Λ * ‖X‖ ^ 2)
    (D : Matrix m n ℝ) {A : Matrix r n ℝ} (hA : grad H D 0 * Aᵀ ≠ 0) {h : ℝ} (hh : 0 < h)
    (k : ℕ) (hk : (2 * k + 3) * h * Λ * ‖A‖ ^ 2 < 2) :
    quad H D (0 - ((k + 2) * h) • (grad H D 0 * Aᵀ * A)) <
      quad H D (0 - ((k + 1) * h) • (grad H D 0 * Aᵀ * A)) := by
  rw [lora_ff_step_lt_iff hH D A hh k]
  set G := grad H D 0
  have hGA : 0 < ‖G * Aᵀ‖ ^ 2 := by positivity
  have hP : ‖G * Aᵀ * A‖ ^ 2 ≤ ‖G * Aᵀ‖ ^ 2 * ‖A‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (LeanDLRA.Frobenius.norm_mul_le _ _) 2
  have h1 : ⟪H (G * Aᵀ * A), G * Aᵀ * A⟫ ≤ Λ * (‖G * Aᵀ‖ ^ 2 * ‖A‖ ^ 2) :=
    (hΛ _).trans (mul_le_mul_of_nonneg_left hP hΛ0)
  have hk' : (0 : ℝ) ≤ (2 * k + 3) * h := by positivity
  calc (2 * k + 3) * h * ⟪H (G * Aᵀ * A), G * Aᵀ * A⟫
      ≤ (2 * k + 3) * h * (Λ * (‖G * Aᵀ‖ ^ 2 * ‖A‖ ^ 2)) := mul_le_mul_of_nonneg_left h1 hk'
    _ = ((2 * k + 3) * h * Λ * ‖A‖ ^ 2) * ‖G * Aᵀ‖ ^ 2 := by ring
    _ < 2 * ‖G * Aᵀ‖ ^ 2 := mul_lt_mul_of_pos_right hk hGA

/-- **The dichotomy.**  Same `H`, same target `D`, same step `h`, same start (increment `0`): if
the gradient is beyond the vertex along itself (`2 ‖G‖² ≤ 3 h ⟪H G, G⟫`, the edge-of-stability
regime), the first full-rank FF step does not lower the loss, while under `3 h Λ ‖A‖² < 2` the
first LoRA FF step strictly lowers it.  `ff_dichotomy_instance` shows the hypotheses are
compatible. -/
theorem ff_dichotomy {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ X : Matrix m n ℝ, ⟪H X, X⟫ ≤ Λ * ‖X‖ ^ 2)
    (D : Matrix m n ℝ) {A : Matrix r n ℝ} (hA : grad H D 0 * Aᵀ ≠ 0) {h : ℝ} (hh : 0 < h)
    (hfull : 2 * ‖grad H D 0‖ ^ 2 ≤ 3 * h * ⟪H (grad H D 0), grad H D 0⟫)
    (hlora : 3 * h * Λ * ‖A‖ ^ 2 < 2) :
    quad H D (0 - h • grad H D 0) ≤ quad H D (0 - (2 * h) • grad H D 0) ∧
      quad H D (0 - (2 * h) • (grad H D 0 * Aᵀ * A)) <
        quad H D (0 - h • (grad H D 0 * Aᵀ * A)) := by
  constructor
  · rw [← sub_nonneg]
    have := full_ff_step_sub hH D 0 h 0
    simp only [Nat.cast_zero, zero_add, one_mul, mul_zero] at this
    rw [this]
    have : 0 ≤ h / 2 := by positivity
    nlinarith
  · have := lora_ff_step_of_small hH hΛ0 hΛ D hA hh 0 (by simpa using hlora)
    simpa using this

/-- `‖1‖ = √r` for the Frobenius norm of the identity. -/
theorem norm_one_eq_sqrt_card [DecidableEq r] :
    ‖(1 : Matrix r r ℝ)‖ = Real.sqrt (Fintype.card r) := by
  rw [norm_def]
  congr 1
  simp [Matrix.one_apply, Finset.sum_ite_eq, Finset.card_univ]

/-- **Instance of the dichotomy** (`1 × 1`, LoRA rank `1`): `H = 15`, `h = 1/10` (so `hλ = 3/2`:
GD converges, error halves at each step), target `D = 1`, factor `A = 1/2`.  The first full-rank
FF step does not lower the loss (it raises it, `1.875 → 30`), the first LoRA FF step lowers it
(`2.93 → 0.47`). -/
theorem ff_dichotomy_instance :
    let H : Matrix (Fin 1) (Fin 1) ℝ →L[ℝ] Matrix (Fin 1) (Fin 1) ℝ :=
      (15 : ℝ) • ContinuousLinearMap.id ℝ _
    let D : Matrix (Fin 1) (Fin 1) ℝ := 1
    let A : Matrix (Fin 1) (Fin 1) ℝ := (1 / 2 : ℝ) • 1
    quad H D (0 - (1 / 10 : ℝ) • grad H D 0) ≤ quad H D (0 - (2 * (1 / 10 : ℝ)) • grad H D 0) ∧
      quad H D (0 - (2 * (1 / 10 : ℝ)) • (grad H D 0 * Aᵀ * A)) <
        quad H D (0 - (1 / 10 : ℝ) • (grad H D 0 * Aᵀ * A)) := by
  intro H D A
  have hone : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
    rw [norm_one_eq_sqrt_card]; simp
  have hA : ‖A‖ ^ 2 = 1 / 4 := by
    simp only [A, norm_smul, hone, Real.norm_eq_abs, mul_one]
    norm_num
  have hG : grad H D 0 = (-15 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    simp only [grad, H, D, smul_apply, ContinuousLinearMap.id_apply, zero_sub, smul_neg,
      neg_smul]
  refine ff_dichotomy (isSelfAdj_smul_id 15) (by norm_num) (fun X => (inner_smul_id_self 15 X).le)
    D ?_ (by norm_num) ?_ ?_
  · rw [hG]
    simp only [A, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, mul_one, smul_smul]
    intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
  · rw [inner_smul_id_self]
    nlinarith [sq_nonneg ‖grad H D 0‖]
  · rw [hA]; norm_num

/-! ### General factors: the curvature seen by the factor dynamics -/

omit [Fintype m] [Fintype n] in
/-- The product along a factor-space line is a quadratic in `s`. -/
theorem factor_product_expansion (B ΔB : Matrix m r ℝ) (A ΔA : Matrix r n ℝ) (s : ℝ) :
    (B + s • ΔB) * (A + s • ΔA) = B * A + s • (ΔB * A + B * ΔA) + s ^ 2 • (ΔB * ΔA) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul]
  module

/-- **Exact quartic expansion of the loss along a factor direction.**  With `G = ∇L(BA)`,
`M = ΔB A + B ΔA` (the tangent part) and `N = ΔB ΔA`,
`L((B + sΔB)(A + sΔA)) = L(BA) + s ⟪G, M⟫ + s² (⟪H M, M⟫ + 2 ⟪G, N⟫) / 2 + s³ ⟪H M, N⟫
  + s⁴ ⟪H N, N⟫ / 2`.
The curvature of the factor parametrization is `⟪H M, M⟫ + 2 ⟪G, N⟫`; compare `quad_add_smul`
for the full space, whose curvature is `⟪H V, V⟫`. -/
theorem factor_loss_expansion {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : IsSelfAdj H)
    (D : Matrix m n ℝ) (B ΔB : Matrix m r ℝ) (A ΔA : Matrix r n ℝ) (s : ℝ) :
    quad H D ((B + s • ΔB) * (A + s • ΔA)) =
      quad H D (B * A) + s * ⟪grad H D (B * A), ΔB * A + B * ΔA⟫ +
        s ^ 2 * (⟪H (ΔB * A + B * ΔA), ΔB * A + B * ΔA⟫ +
          2 * ⟪grad H D (B * A), ΔB * ΔA⟫) / 2 +
        s ^ 3 * ⟪H (ΔB * A + B * ΔA), ΔB * ΔA⟫ + s ^ 4 * ⟪H (ΔB * ΔA), ΔB * ΔA⟫ / 2 := by
  rw [factor_product_expansion]
  have h1 : B * A + s • (ΔB * A + B * ΔA) + s ^ 2 • (ΔB * ΔA) =
      B * A + s • ((ΔB * A + B * ΔA) + s • (ΔB * ΔA)) := by
    simp only [smul_add, smul_smul]; module
  set M := ΔB * A + B * ΔA with hM
  set N := ΔB * ΔA with hN
  have h2 : ⟪H N, M⟫ = ⟪H M, N⟫ := by rw [hH, real_inner_comm]
  rw [h1, quad_add_smul hH]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, h2]
  ring

/-- **The factor curvature is controlled by the factor sizes and the gradient**, not by the
curvature `Λ` of the loss alone: if `⟪H X, X⟫ ≤ Λ ‖X‖²`, then
`⟪H M, M⟫ + 2 ⟪G, N⟫ ≤ (Λ (‖A‖² + ‖B‖²) + ‖G‖) (‖ΔB‖² + ‖ΔA‖²)`.
For LoRA's small factors (zero `B`, small increment) this is far below `Λ`, which is attained
in the full space along the top eigendirection: the factor dynamics never reaches the
edge-of-stability regime that makes full-rank Fast Forward fail (`full_ff_ascends`). -/
theorem factor_curvature_le {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ X : Matrix m n ℝ, ⟪H X, X⟫ ≤ Λ * ‖X‖ ^ 2) (G : Matrix m n ℝ)
    (B ΔB : Matrix m r ℝ) (A ΔA : Matrix r n ℝ) :
    ⟪H (ΔB * A + B * ΔA), ΔB * A + B * ΔA⟫ + 2 * ⟪G, ΔB * ΔA⟫ ≤
      (Λ * (‖A‖ ^ 2 + ‖B‖ ^ 2) + ‖G‖) * (‖ΔB‖ ^ 2 + ‖ΔA‖ ^ 2) := by
  have hM : ‖ΔB * A + B * ΔA‖ ≤ ‖ΔB‖ * ‖A‖ + ‖B‖ * ‖ΔA‖ :=
    (norm_add_le _ _).trans
      (add_le_add (LeanDLRA.Frobenius.norm_mul_le _ _) (LeanDLRA.Frobenius.norm_mul_le _ _))
  have hM2 : ‖ΔB * A + B * ΔA‖ ^ 2 ≤ (‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖ΔB‖ ^ 2 + ‖ΔA‖ ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hM 2
    nlinarith [sq_nonneg (‖ΔB‖ * ‖B‖ - ‖A‖ * ‖ΔA‖)]
  have h1 : ⟪H (ΔB * A + B * ΔA), ΔB * A + B * ΔA⟫ ≤
      Λ * ((‖A‖ ^ 2 + ‖B‖ ^ 2) * (‖ΔB‖ ^ 2 + ‖ΔA‖ ^ 2)) :=
    (hΛ _).trans (mul_le_mul_of_nonneg_left hM2 hΛ0)
  have h2 : ⟪G, ΔB * ΔA⟫ ≤ ‖G‖ * (‖ΔB‖ * ‖ΔA‖) :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (LeanDLRA.Frobenius.norm_mul_le _ _) (norm_nonneg _))
  have h3 : 2 * (‖ΔB‖ * ‖ΔA‖) ≤ ‖ΔB‖ ^ 2 + ‖ΔA‖ ^ 2 := by
    have := two_mul_le_add_sq ‖ΔB‖ ‖ΔA‖; rwa [mul_assoc] at this
  have h4 : ‖G‖ * (2 * (‖ΔB‖ * ‖ΔA‖)) ≤ ‖G‖ * (‖ΔB‖ ^ 2 + ‖ΔA‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  nlinarith

/-- Balanced factors (`BᵀB = AAᵀ`) have equal Frobenius norms. -/
theorem balanced_norm_eq {B : Matrix m r ℝ} {A : Matrix r n ℝ} (hbal : Bᵀ * B = A * Aᵀ) :
    ‖B‖ = ‖A‖ := by
  have h1 : ‖B‖ ^ 2 = ‖A‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_eq_trace,
      inner_eq_trace, hbal, Matrix.trace_mul_comm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

/-- For balanced factors the factor sizes are controlled by the increment:
`‖A‖² + ‖B‖² ≤ 2 √r ‖B A‖` (with the operator norm, `‖A‖₂² = ‖B‖₂² = ‖B A‖₂` exactly; a standard
fact not re-proved here).  Together with `factor_curvature_le`: the curvature of the factor
dynamics is `O(Λ √r ‖BA‖ + ‖G‖)`, proportional to the size of the increment and of the gradient,
while the full-space curvature is `Λ` whatever the increment. -/
theorem balanced_normSq_add_le {B : Matrix m r ℝ} {A : Matrix r n ℝ}
    (hbal : Bᵀ * B = A * Aᵀ) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ 2 * Real.sqrt (Fintype.card r) * ‖B * A‖ := by
  classical
  have htrB : ‖B‖ ^ 2 = (Bᵀ * B).trace := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_trace]
  have htrA : ‖A‖ ^ 2 = (Bᵀ * B).trace := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_trace, Matrix.trace_mul_comm, ← hbal]
  have hSn : ‖Bᵀ * B‖ = ‖B * A‖ := by
    have e1 : ‖Bᵀ * B‖ ^ 2 = (Bᵀ * B * (A * Aᵀ)).trace := by
      rw [← real_inner_self_eq_norm_sq, inner_eq_trace, Matrix.transpose_mul,
        Matrix.transpose_transpose, hbal]
    have e2 : ‖B * A‖ ^ 2 = (Bᵀ * B * (A * Aᵀ)).trace := by
      rw [← real_inner_self_eq_norm_sq, inner_eq_trace, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (e1.trans e2.symm)
  have hcs : (Bᵀ * B).trace ≤ ‖(1 : Matrix r r ℝ)‖ * ‖Bᵀ * B‖ := by
    have : (Bᵀ * B).trace = ⟪(1 : Matrix r r ℝ), Bᵀ * B⟫ := by
      rw [inner_eq_trace, Matrix.transpose_one, Matrix.one_mul]
    rw [this]
    exact real_inner_le_norm _ _
  rw [htrA, htrB, hSn, norm_one_eq_sqrt_card] at *
  linarith

/-! ### The isotropic model: collinearity is not the mechanism -/

/-- **Full-rank consecutive updates are exactly collinear** for a scalar Hessian `H = μ • id`:
`X₂ - X₁ = (1 - hμ) (X₁ - X₀)`. -/
theorem full_consecutive_collinear (D X : Matrix m n ℝ) (h μ : ℝ) :
    fullStep (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D h
        (fullStep (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D h X) -
      fullStep (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D h X =
    (1 - h * μ) • (fullStep (μ • ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D h X - X) := by
  simp only [fullStep, grad, smul_apply, ContinuousLinearMap.id_apply]
  module

/-- On the isotropic model `H = id` with `h = 1/2`, **one full-rank FF step reaches the
minimizer**: `X₁ + (X₁ - X₀) = D`, loss `0`. -/
theorem full_ff_isotropic_exact (D X₀ : Matrix m n ℝ) :
    quad (ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D
      (fullStep (ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D (1 / 2) X₀ +
        (1 : ℝ) • (fullStep (ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D (1 / 2) X₀ - X₀)) = 0 := by
  have : fullStep (ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D (1 / 2) X₀ +
      (1 : ℝ) • (fullStep (ContinuousLinearMap.id ℝ (Matrix m n ℝ)) D (1 / 2) X₀ - X₀) = D := by
    simp only [fullStep, grad, ContinuousLinearMap.id_apply]; module
  rw [this]; simp [quad]

/-- The two LoRA steps of the isotropic counterexample: `D = (1, 0)`, `A = (1, 1)`, `B = 0`,
`h = 1/2`, `H = id` on `1 × 2` matrices with rank-`1` factors:
`(B₁, A₁) = (1/2, (1, 1))`, `(B₂, A₂) = (1/2, (9/8, 7/8))`. -/
theorem lora_isotropic_steps :
    let H := ContinuousLinearMap.id ℝ (Matrix (Fin 1) (Fin 2) ℝ)
    let D : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
    let A : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]
    factorStep H D (1 / 2) 0 A = (!![1 / 2], !![1, 1]) ∧
      factorStep H D (1 / 2) !![1 / 2] !![1, 1] = (!![1 / 2], !![9 / 8, 7 / 8]) := by
  intro H D A
  constructor
  · rw [lora_init_step]
    simp only [grad, H, D, A, ContinuousLinearMap.id_apply, zero_sub]
    refine Prod.ext ?_ rfl
    ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.neg_apply]
    simp
  · simp only [factorStep, grad, H, D, ContinuousLinearMap.id_apply]
    refine Prod.ext ?_ ?_
    · ext i j
      fin_cases i; fin_cases j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.sum_univ_one, Matrix.transpose_apply]
      simp
      norm_num
    · ext i j
      fin_cases i; fin_cases j <;>
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_one,
          Matrix.transpose_apply] <;>
        simp <;> norm_num

/-- **LoRA consecutive weight updates can be orthogonal** on the isotropic model, where the
full-rank updates are collinear (`full_consecutive_collinear`): with the steps of
`lora_isotropic_steps`, `ΔX₀ = X₁ - 0 = (1/2, 1/2)` and `ΔX₁ = X₂ - X₁ = (1/16, -1/16)`.  The
conjectured mechanism "the factorization makes consecutive updates nearly collinear" is therefore
not a theorem; see `lora_ff_isotropic_ascends`. -/
theorem lora_consecutive_orthogonal :
    let X₁ : Matrix (Fin 1) (Fin 2) ℝ :=
      (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ) * (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ)
    let X₂ : Matrix (Fin 1) (Fin 2) ℝ :=
      (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ) * (!![9 / 8, 7 / 8] : Matrix (Fin 1) (Fin 2) ℝ)
    ⟪X₂ - X₁, X₁ - 0⟫ = 0 ∧ X₁ - 0 ≠ 0 ∧ X₂ - X₁ ≠ 0 := by
  intro X₁ X₂
  have h1 : X₁ = !![1 / 2, 1 / 2] := by
    ext i j
    fin_cases i; fin_cases j <;> simp only [X₁, Matrix.mul_apply, Fin.sum_univ_one] <;> simp
  have h2 : X₂ = !![9 / 16, 7 / 16] := by
    ext i j
    fin_cases i; fin_cases j <;> simp only [X₂, Matrix.mul_apply, Fin.sum_univ_one] <;> simp <;>
      norm_num
  rw [h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · simp only [inner_def, Fin.sum_univ_one, Fin.sum_univ_two, Matrix.sub_apply]
    simp
    norm_num
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
    norm_num at this

/-- **LoRA Fast Forward raises the loss on the isotropic model** where full-rank FF is exact
(`full_ff_isotropic_exact`): after the first LoRA step `(B₁, A₁) = (1/2, (1, 1))` from
`(0, (1, 1))` (`lora_isotropic_steps`), the FF step `(B₁ + (B₁ - 0)) (A₁ + (A₁ - A)) = (1, 1)`
has loss `1/2 > 1/4`.  The paper's phenomenon is thus reversed on an isotropic loss: it needs the
anisotropic edge-of-stability regime of `full_ff_ascends`, where the factor Gram matrices lower
the effective step (`lora_ff_step_of_small`). -/
theorem lora_ff_isotropic_ascends :
    let H := ContinuousLinearMap.id ℝ (Matrix (Fin 1) (Fin 2) ℝ)
    let D : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
    let A : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]
    let B₁ : Matrix (Fin 1) (Fin 1) ℝ := !![1 / 2]
    quad H D (B₁ * A) < quad H D ((B₁ + (1 : ℝ) • (B₁ - 0)) * (A + (1 : ℝ) • (A - A))) := by
  intro H D A B₁
  have e1 : B₁ * A = !![1 / 2, 1 / 2] := by
    ext i j
    fin_cases i; fin_cases j <;> simp only [B₁, A, Matrix.mul_apply, Fin.sum_univ_one] <;> simp
  have e2 : (B₁ + (1 : ℝ) • (B₁ - 0)) * (A + (1 : ℝ) • (A - A)) = !![1, 1] := by
    ext i j
    fin_cases i; fin_cases j <;>
      simp only [B₁, A, Matrix.mul_apply, Fin.sum_univ_one, Matrix.add_apply, Matrix.smul_apply,
        Matrix.sub_apply] <;>
      simp <;> norm_num
  have h1 : quad H D (B₁ * A) = 1 / 4 := by
    rw [e1]
    simp only [quad, H, D, ContinuousLinearMap.id_apply, inner_def, Fin.sum_univ_one,
      Fin.sum_univ_two, Matrix.sub_apply]
    simp
    norm_num
  have h2 : quad H D ((B₁ + (1 : ℝ) • (B₁ - 0)) * (A + (1 : ℝ) • (A - A))) = 1 / 2 := by
    rw [e2]
    simp only [quad, H, D, ContinuousLinearMap.id_apply, inner_def, Fin.sum_univ_one,
      Fin.sum_univ_two, Matrix.sub_apply]
    simp
  rw [h1, h2]; norm_num

end LeanDLRA.Novel.OpTR45
