import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Orthonormal

/-!
# Results of arXiv 2610.07653: low-rank SI-DSA and GMRES-DSA for radiative transfer

The paper (*Low-rank SI-DSA and GMRES-DSA for Radiative Transfer Equation with Adaptive Accuracy
Control*) states two theorems. Both are finite-dimensional linear algebra and both are proved
here, in the paper's setting (real matrices, `M`-norms, the Euclidean norm, an orthonormal Arnoldi
basis), with the deviations listed in the docstrings.

* **Theorem 4.1** (inexact preconditioned Richardson estimate, PDF p. 10, proof in Appendix C):
  `inexact_preconditioned_richardson`, with the abstract one-step form
  `inexact_richardson_step_le` on a seminormed space and the "in particular" sentence as
  `inexact_preconditioned_richardson_contractive`. The printed sentence asks only
  `η⁽ⁿ⁾ ≤ η̄ = (1 - ρ)/(αK)`; at equality the bound gives the factor `1` and the iteration can
  stall (`inexact_preconditioned_richardson_boundary`). Appendix C has the strict inequality
  `η̄ < (1 - ρ)/(αK)`, which is what the corollary assumes.
* **Theorem 5.1** (residual gap of inexact flexible GMRES with an inexact right-hand side, PDF
  p. 14, proof in Appendix D): `fgmres_residual_gap_le`. Its two steps are proved as separate
  results: the gap identity (D.2), `fgmres_true_residual_sub_computed`, and the coefficient bound
  (D.3), `fgmres_coeff_le`, which the paper takes from Lemma 5.1 of Simoncini and Szyld. The
  latter rests on `norm_sub_le_of_isLeastSquares`: if `y` minimizes `‖c - H y‖` and
  `σ ‖w‖ ≤ ‖H w‖`, then `‖y - z‖ ≤ ‖c - H z‖ / σ` for every `z`.
* The accumulation of absolute sweep errors, i.e. the one-step bound (C.2) iterated:
  `inexact_iteration_error` for a contraction on a normed space and
  `inexact_richardson_error_le` for the Richardson iteration. Neither is a printed statement of
  the paper.

## Core and Mathlib definitions used

`LeanDLRA.discrete_gronwall_le` (Foundations/Gronwall) for every iterated bound;
`LeanDLRA.Curvature.specNorm` and `LeanDLRA.Curvature.norm_toEuclideanLin_le`
(Matrix/Curvature) for `sigma_lowerBound_of_mul_eq_one`, which turns a left inverse `G` of `H̄_m`
into the lower bound `σ = ‖G‖₂⁻¹` used in Theorem 5.1 (for the pseudoinverse this is
`σ_m(H̄_m)`);
`LeanDLRA.inner_toLp_col_col` (Matrix/Orthonormal) for `orthonormal_col_of_transpose_mul_eq_one`,
which turns the library's convention `Qᵀ Q = 1` for orthonormal columns into the orthonormal family
used in Theorem 5.1. The `M`-norm is Mathlib's `Matrix.toSeminormedAddCommGroup`
(`mNorm_eq_norm`).

## Local definitions

`mNorm M x = √(xᵀ M x)` (the library has no weighted vector norm; bridged to Mathlib by
`mNorm_eq_norm`), and the Krylov objects of Theorem 5.1: `hessBlock` (`H̄_k`), `padVec`
(zero padding `ℝᵏ → ℝᵐ`) and `computedResidual` (`r⁽ᵏ⁾ = Q_{k+1}(βe₁ - H̄_k y⁽ᵏ⁾)`). The library has
no Arnoldi, GMRES or Hessenberg notions.

## Not formalized

* The relaxation rules (4.1) and (5.3)/(5.9) and the switching rule (4.6) are heuristics; the paper
  says that (4.1) "does not guarantee" the sufficient condition (4.5). The DEIM bound behind the
  switch is core `LeanDLRA.norm_sub_obliqueProj_mul_le_of_orthonormal` (Matrix/Interpolation),
  and its combination with a contraction is `LeanDLRA.OpenProblems.Randomized.deim_switch_error`.
* The transport discretisation (sweeps, DSA consistency, `M_DSA` SPD) is not modelled; Theorem 4.1
  is stated for any SPD `M`, as printed.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix
open LeanDLRA.Curvature

namespace LeanDLRA.Literature.P2610_07653

/-! ### Inexact fixed-point and Richardson iterations (Section 4) -/

/-- **Inexact contraction iteration** (arXiv 2610.07653; not a printed statement of the paper:
the one-step bound (C.2) from the proof of Theorem 4.1, written for a general contraction and
iterated over `n`; around (4.5) the paper discusses absolute tolerances
`‖r̃⁽ⁿ⁾ - r⁽ⁿ⁾‖_{M⁻¹} ≲ τ` but states no such bound). Let `T` be a `ρ`-contraction with `0 ≤ ρ` and
fixed point `x*`. If `x (k+1) = T (x k) + e k` with `‖e k‖ ≤ τ k`, then
`‖x k - x*‖ ≤ ρ^k ‖x 0 - x*‖ + ∑_{j<k} ρ^(k-1-j) τ j`. The Richardson form is
`inexact_richardson_error_le`; the same bound on an inner product space is
`LeanDLRA.OpenProblems.Randomized.perturbed_contraction_le`. -/
theorem inexact_iteration_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E → E) {ρ : ℝ} (hρ : 0 ≤ ρ) (hT : ∀ x y : E, ‖T x - T y‖ ≤ ρ * ‖x - y‖)
    (xstar : E) (hfix : T xstar = xstar) (x e : ℕ → E) (τ : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = T (x k) + e k) (hτ : ∀ k, ‖e k‖ ≤ τ k) (k : ℕ) :
    ‖x k - xstar‖ ≤ ρ ^ k * ‖x 0 - xstar‖ + ∑ j ∈ range k, ρ ^ (k - 1 - j) * τ j := by
  have hstep : ∀ n < k, ‖x (n + 1) - xstar‖ ≤ ρ * ‖x n - xstar‖ + τ n := by
    intro n _
    calc ‖x (n + 1) - xstar‖ = ‖(T (x n) - T xstar) + e n‖ := by
          rw [hx n, hfix]
          congr 1
          abel
      _ ≤ ‖T (x n) - T xstar‖ + ‖e n‖ := norm_add_le _ _
      _ ≤ ρ * ‖x n - xstar‖ + τ n := add_le_add (hT _ _) (hτ n)
  exact LeanDLRA.discrete_gronwall_le (e := fun n => ‖x n - xstar‖) (b := τ) hρ hstep k le_rfl

/-- Non-vacuity of `inexact_iteration_error`: the contraction `T x = x / 2` on `ℝ` with fixed point
`0`, exact iterates `x n = (1/2)^n` and no error (`e = τ = 0`) satisfies the hypotheses. -/
theorem inexact_iteration_error_example (k : ℕ) :
    ‖(fun n : ℕ => (1 / 2 : ℝ) ^ n) k - 0‖ ≤
      (1 / 2 : ℝ) ^ k * ‖(fun n : ℕ => (1 / 2 : ℝ) ^ n) 0 - 0‖ +
        ∑ j ∈ range k, (1 / 2 : ℝ) ^ (k - 1 - j) * (fun _ : ℕ => (0 : ℝ)) j :=
  inexact_iteration_error (E := ℝ) (fun x => (1 / 2 : ℝ) * x) (ρ := 1 / 2) (by norm_num)
    (fun x y => by
      rw [← mul_sub, norm_mul]
      norm_num)
    0 (by simp) (fun n => (1 / 2 : ℝ) ^ n) (fun _ => 0) (fun _ => 0)
    (fun n => by simp [pow_succ]; ring) (fun _ => by simp) k

section Abstract

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup F]
  [Module ℝ F]

/-- **One step of the inexact preconditioned Richardson iteration, abstract form** (arXiv
2610.07653, the computation (C.1)–(C.3) proving Theorem 4.1). `E` carries the `M`-norm, `P`
plays `M⁻¹` and the `M⁻¹`-norm of a residual `r` is `‖P r‖` (for SPD `M`,
`‖r‖_{M⁻¹} = ‖M⁻¹ r‖_M`, see `mNorm_inv`). If `‖v - α P A v‖ ≤ ρ ‖v‖`, `‖P A v‖ ≤ K ‖v‖`,
`A x* = b` and the residual perturbation satisfies `‖P (r̃ - r)‖ ≤ η ‖P r‖` with `r = b - A x`,
then the step `x + α P r̃` satisfies `‖x + α P r̃ - x*‖ ≤ (ρ + α K η) ‖x - x*‖`. -/
theorem inexact_richardson_step_le (A : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] E) {α ρ K η : ℝ}
    (hα : 0 ≤ α) (hη : 0 ≤ η) (hρ : ∀ v, ‖v - α • P (A v)‖ ≤ ρ * ‖v‖)
    (hK : ∀ v, ‖P (A v)‖ ≤ K * ‖v‖) {b rt : F} {x xs : E} (hxs : A xs = b)
    (hr : ‖P (rt - (b - A x))‖ ≤ η * ‖P (b - A x)‖) :
    ‖x + α • P rt - xs‖ ≤ (ρ + α * K * η) * ‖x - xs‖ := by
  have hres : b - A x = -A (x - xs) := by rw [map_sub, hxs]; abel
  have hsplit : x + α • P rt - xs =
      ((x - xs) - α • P (A (x - xs))) + α • P (rt - (b - A x)) := by
    rw [map_sub P rt, hres, map_neg, smul_sub, smul_neg]; abel
  rw [hsplit]
  have h2 : ‖α • P (rt - (b - A x))‖ ≤ α * (η * (K * ‖x - xs‖)) := by
    rw [norm_smul, Real.norm_of_nonneg hα]
    refine mul_le_mul_of_nonneg_left (hr.trans (mul_le_mul_of_nonneg_left ?_ hη)) hα
    rw [hres, map_neg, norm_neg]
    exact hK _
  calc _ ≤ ‖(x - xs) - α • P (A (x - xs))‖ + ‖α • P (rt - (b - A x))‖ := norm_add_le _ _
    _ ≤ ρ * ‖x - xs‖ + α * (η * (K * ‖x - xs‖)) := add_le_add (hρ _) h2
    _ = (ρ + α * K * η) * ‖x - xs‖ := by ring

/-- **Inexact Richardson iteration with absolute residual tolerances** (arXiv 2610.07653; not a
printed statement: the one-step bound (C.2) iterated, for inner thresholds that ensure
`‖r̃⁽ⁿ⁾ - r⁽ⁿ⁾‖_{M⁻¹} ≤ τ n`, the setting discussed around (4.5)). With
`x (k+1) = x k + α P (r̃ k)`, `‖v - α P A v‖ ≤ ρ ‖v‖` and `‖P (r̃ k - (b - A (x k)))‖ ≤ τ k`,
`‖x k - x*‖ ≤ ρ^k ‖x 0 - x*‖ + ∑_{j<k} ρ^(k-1-j) α τ j`. This is `inexact_iteration_error` for
`T v = v + α P (b - A v)`; it is proved through `LeanDLRA.discrete_gronwall_le` so that it also
holds for the `M`-seminorm. -/
theorem inexact_richardson_error_le (A : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] E) {α ρ : ℝ} (hα : 0 ≤ α)
    (hρ0 : 0 ≤ ρ) (hρ : ∀ v, ‖v - α • P (A v)‖ ≤ ρ * ‖v‖) {b : F} {xs : E} (hxs : A xs = b)
    (x : ℕ → E) (rt : ℕ → F) (τ : ℕ → ℝ) (hx : ∀ k, x (k + 1) = x k + α • P (rt k))
    (hτ : ∀ k, ‖P (rt k - (b - A (x k)))‖ ≤ τ k) (k : ℕ) :
    ‖x k - xs‖ ≤ ρ ^ k * ‖x 0 - xs‖ + ∑ j ∈ range k, ρ ^ (k - 1 - j) * (α * τ j) := by
  have hstep : ∀ n < k, ‖x (n + 1) - xs‖ ≤ ρ * ‖x n - xs‖ + α * τ n := by
    intro n _
    have hres : b - A (x n) = -A (x n - xs) := by rw [map_sub, hxs]; abel
    have hsplit : x (n + 1) - xs =
        ((x n - xs) - α • P (A (x n - xs))) + α • P (rt n - (b - A (x n))) := by
      rw [hx n, map_sub P (rt n), hres, map_neg, smul_sub, smul_neg]; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add (hρ _) ?_)
    rw [norm_smul, Real.norm_of_nonneg hα]
    exact mul_le_mul_of_nonneg_left (hτ n) hα
  exact LeanDLRA.discrete_gronwall_le (e := fun n => ‖x n - xs‖) (b := fun j => α * τ j) hρ0
    hstep k le_rfl

end Abstract

section MNorm

variable {n : Type*} [Fintype n]

/-- The `M`-norm `‖x‖_M = √(xᵀ M x)` of arXiv 2610.07653, Theorem 4.1. For positive
semidefinite `M` it is the norm of Mathlib's `Matrix.toSeminormedAddCommGroup M`
(`mNorm_eq_norm`); the library has no weighted vector norm of its own. -/
noncomputable def mNorm (M : Matrix n n ℝ) (x : n → ℝ) : ℝ := √(x ⬝ᵥ (M *ᵥ x))

/-- Bridge to Mathlib: `mNorm M` is the norm induced by a positive semidefinite `M`. -/
theorem mNorm_eq_norm (M : Matrix n n ℝ) (hM : M.PosSemidef) (x : n → ℝ) :
    mNorm M x = @Norm.norm (n → ℝ) (M.toSeminormedAddCommGroup hM).toNorm x := by
  rw [mNorm, dotProduct_comm]
  rfl

theorem mNorm_nonneg (M : Matrix n n ℝ) (x : n → ℝ) : 0 ≤ mNorm M x := Real.sqrt_nonneg _

theorem mNorm_smul (M : Matrix n n ℝ) (c : ℝ) (x : n → ℝ) :
    mNorm M (c • x) = |c| * mNorm M x := by
  rw [mNorm, mNorm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem mNorm_neg (M : Matrix n n ℝ) (x : n → ℝ) : mNorm M (-x) = mNorm M x := by
  simp [mNorm, Matrix.mulVec_neg]

variable [DecidableEq n]

/-- For invertible `M`, `‖r‖_{M⁻¹} = ‖M⁻¹ r‖_M` (used in (C.3) of arXiv 2610.07653). -/
theorem mNorm_inv (M : Matrix n n ℝ) (hM : IsUnit M.det) (r : n → ℝ) :
    mNorm M⁻¹ r = mNorm M (M⁻¹ *ᵥ r) := by
  rw [mNorm, mNorm, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec,
    dotProduct_comm]

/-- **Theorem 4.1 of arXiv 2610.07653** (inexact preconditioned Richardson estimate). Let `M` be
SPD, `α > 0`, `A x* = b`, and consider one step
`x⁽ⁿ⁺¹⁾ = x⁽ⁿ⁾ + α M⁻¹ (b̃⁽ⁿ⁾ - Ã⁽ⁿ⁾ x⁽ⁿ⁾)` with `r = b - A x⁽ⁿ⁾`, `r̃ = b̃⁽ⁿ⁾ - Ã⁽ⁿ⁾ x⁽ⁿ⁾`. If
`‖r̃ - r‖_{M⁻¹} ≤ η ‖r‖_{M⁻¹}` (4.3), then
`‖x⁽ⁿ⁺¹⁾ - x*‖_M ≤ (ρ + α K η) ‖x⁽ⁿ⁾ - x*‖_M` (4.4).

Deviations from the printed statement: `ρ` and `K` enter only through
`‖(I - α M⁻¹ A) v‖_M ≤ ρ ‖v‖_M` and `‖M⁻¹ A v‖_M ≤ K ‖v‖_M`; the induced norms
`ρ = ‖I - αM⁻¹A‖_M` and `K = ‖M⁻¹A‖_M` of the paper are the least such constants, so the printed
statement is a special case. The assumption `ρ < 1` is not needed for (4.4) and is dropped. (4.3)
is used in the multiplied-out form, which also covers `r = 0` (where the printed quotient is
undefined), with `0 ≤ η` stated explicitly. -/
theorem inexact_preconditioned_richardson {A M At : Matrix n n ℝ} (hM : M.PosDef)
    {α ρ K η : ℝ} (hα : 0 < α) (hη : 0 ≤ η)
    (hρ : ∀ v, mNorm M ((1 - α • (M⁻¹ * A)) *ᵥ v) ≤ ρ * mNorm M v)
    (hK : ∀ v, mNorm M ((M⁻¹ * A) *ᵥ v) ≤ K * mNorm M v)
    {b bt x xs : n → ℝ} (hxs : A *ᵥ xs = b)
    (hr : mNorm M⁻¹ ((bt - At *ᵥ x) - (b - A *ᵥ x)) ≤ η * mNorm M⁻¹ (b - A *ᵥ x)) :
    mNorm M (x + α • (M⁻¹ *ᵥ (bt - At *ᵥ x)) - xs) ≤ (ρ + α * K * η) * mNorm M (x - xs) := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  let _ : SeminormedAddCommGroup (n → ℝ) := M.toSeminormedAddCommGroup hM.posSemidef
  let _ : InnerProductSpace ℝ (n → ℝ) := M.toInnerProductSpace hM.posSemidef
  simp only [mNorm_eq_norm M hM.posSemidef, mNorm_inv M hdet] at hρ hK hr ⊢
  exact inexact_richardson_step_le (Matrix.mulVecLin A) (Matrix.mulVecLin M⁻¹) hα.le hη
    (fun v => by simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec] using hρ v)
    (fun v => by simpa [Matrix.mulVec_mulVec] using hK v) hxs hr

/-- **The "in particular" of Theorem 4.1 of arXiv 2610.07653**, with the strict inequality of
Appendix C. If every step satisfies (4.3) with `η⁽ⁿ⁾ ≤ η̄ < (1 - ρ)/(αK)`, then
`q = ρ + α K η̄ < 1` and `‖x⁽ⁿ⁾ - x*‖_M ≤ qⁿ ‖x⁽⁰⁾ - x*‖_M`: the inexact iteration remains
contractive. Same conventions for `ρ` and `K` as in `inexact_preconditioned_richardson`; `K > 0`
is needed for `(1 - ρ)/(αK)` to make sense, and `0 ≤ ρ` holds for the induced norm. With
`η̄ = (1 - ρ)/(αK)`, as the printed sentence allows, the conclusion fails:
`inexact_preconditioned_richardson_boundary`. -/
theorem inexact_preconditioned_richardson_contractive {A M : Matrix n n ℝ} (hM : M.PosDef)
    {α ρ K ηbar : ℝ} (hα : 0 < α) (hρ0 : 0 ≤ ρ) (hK0 : 0 < K)
    (hρ : ∀ v, mNorm M ((1 - α • (M⁻¹ * A)) *ᵥ v) ≤ ρ * mNorm M v)
    (hK : ∀ v, mNorm M ((M⁻¹ * A) *ᵥ v) ≤ K * mNorm M v) {b xs : n → ℝ} (hxs : A *ᵥ xs = b)
    (bt : ℕ → n → ℝ) (At : ℕ → Matrix n n ℝ) (x : ℕ → n → ℝ) (η : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = x k + α • (M⁻¹ *ᵥ (bt k - At k *ᵥ x k)))
    (hη0 : ∀ k, 0 ≤ η k)
    (hr : ∀ k, mNorm M⁻¹ ((bt k - At k *ᵥ x k) - (b - A *ᵥ x k)) ≤
      η k * mNorm M⁻¹ (b - A *ᵥ x k))
    (hηbar : ∀ k, η k ≤ ηbar) (hbar : ηbar < (1 - ρ) / (α * K)) :
    ρ + α * K * ηbar < 1 ∧
      ∀ k, mNorm M (x k - xs) ≤ (ρ + α * K * ηbar) ^ k * mNorm M (x 0 - xs) := by
  have hαK : 0 < α * K := mul_pos hα hK0
  have hq : ρ + α * K * ηbar < 1 := by
    have := (lt_div_iff₀ hαK).mp hbar
    rw [mul_comm] at this
    linarith
  have hq0 : 0 ≤ ρ + α * K * ηbar :=
    add_nonneg hρ0 (mul_nonneg hαK.le ((hη0 0).trans (hηbar 0)))
  refine ⟨hq, fun k => ?_⟩
  have hstep : ∀ j < k, mNorm M (x (j + 1) - xs) ≤
      (ρ + α * K * ηbar) * mNorm M (x j - xs) + 0 := by
    intro j _
    rw [add_zero, hx j]
    refine (inexact_preconditioned_richardson hM hα (hη0 j) hρ hK hxs (hr j)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (mNorm_nonneg _ _)
    have := mul_le_mul_of_nonneg_left (hηbar j) hαK.le
    linarith
  have := LeanDLRA.discrete_gronwall_le (e := fun j => mNorm M (x j - xs)) (b := fun _ => 0)
    hq0 hstep k le_rfl
  simpa using this

/-- The data of the examples below: on `ℝ¹` with `A = M = 1` and `α = 1/2`,
`‖(I - α M⁻¹ A) v‖_M = ‖v‖_M / 2`. -/
private theorem mNorm_one_sub_half (v : Fin 1 → ℝ) :
    mNorm (1 : Matrix (Fin 1) (Fin 1) ℝ)
        ((1 - (1 / 2 : ℝ) • ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1)) *ᵥ v) =
      1 / 2 * mNorm 1 v := by
  have hv : (1 - (1 / 2 : ℝ) • ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1)) *ᵥ v =
      (1 / 2 : ℝ) • v := by
    rw [inv_one, Matrix.mul_one, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    module
  rw [hv, mNorm_smul]
  norm_num

/-- **The boundary case of Theorem 4.1 of arXiv 2610.07653.** The printed theorem says that
`η⁽ⁿ⁾ ≤ η̄ = (1 - ρ)/(αK)` keeps the iteration contractive. At equality this fails: for
`A = M = 1` on `ℝ¹`, `α = 1/2` (so `ρ = ‖I - αM⁻¹A‖_M = 1/2` and `K = ‖M⁻¹A‖_M = 1`, both
attained), `x* = b = 0`, `x⁽ⁿ⁾ = 1` and the inexact residual `r̃ = 0`, the relative perturbation
is exactly `1 = (1 - ρ)/(αK)`, and `x⁽ⁿ⁺¹⁾ = x⁽ⁿ⁾ ≠ x*`. Appendix C states the strict inequality
`η̄ < (1 - ρ)/(αK)`, under which the claim holds (`inexact_preconditioned_richardson_contractive`).
-/
theorem inexact_preconditioned_richardson_boundary :
    ∃ (A M At : Matrix (Fin 1) (Fin 1) ℝ) (α ρ K : ℝ) (b bt x xs : Fin 1 → ℝ),
      M.PosDef ∧ 0 < α ∧ ρ < 1 ∧ 0 < K ∧
      (∀ v, mNorm M ((1 - α • (M⁻¹ * A)) *ᵥ v) = ρ * mNorm M v) ∧
      (∀ v, mNorm M ((M⁻¹ * A) *ᵥ v) = K * mNorm M v) ∧ A *ᵥ xs = b ∧
      mNorm M⁻¹ ((bt - At *ᵥ x) - (b - A *ᵥ x)) ≤
        (1 - ρ) / (α * K) * mNorm M⁻¹ (b - A *ᵥ x) ∧
      0 < mNorm M (x - xs) ∧
      mNorm M (x + α • (M⁻¹ *ᵥ (bt - At *ᵥ x)) - xs) = mNorm M (x - xs) := by
  refine ⟨1, 1, 0, 1 / 2, 1 / 2, 1, 0, 0, fun _ => 1, 0, Matrix.PosDef.one, by norm_num,
    by norm_num, by norm_num, mNorm_one_sub_half, fun v => by simp, by simp, ?_, ?_, by simp⟩
  · norm_num [mNorm_neg]
  · simp [mNorm, dotProduct]

/-- Non-vacuity of `inexact_preconditioned_richardson` with a genuine perturbation: the data of
`inexact_preconditioned_richardson_boundary` satisfy all its hypotheses with `η = 1`. -/
example : mNorm (1 : Matrix (Fin 1) (Fin 1) ℝ) ((fun _ => (1 : ℝ)) +
      (1 / 2 : ℝ) • ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ (0 - (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
        fun _ => 1)) - 0) ≤
    (1 / 2 + 1 / 2 * 1 * 1) * mNorm (1 : Matrix (Fin 1) (Fin 1) ℝ) ((fun _ => (1 : ℝ)) - 0) := by
  exact inexact_preconditioned_richardson (At := 0) (η := 1) Matrix.PosDef.one
    (by norm_num : (0 : ℝ) < 1 / 2) zero_le_one
    (fun v => (mNorm_one_sub_half v).le) (fun v => by simp) (b := 0) (by simp)
    (by norm_num [mNorm_neg])

/-- Non-vacuity of `inexact_preconditioned_richardson_contractive`: on `ℝ¹` with `A = M = 1`,
`α = 1/2` (`ρ = 1/2`, `K = 1`), `b = x* = 0`, exact residuals (`η = 0`) and `η̄ = 1/2 < 1`, the
iterates `x⁽ⁿ⁾ = 2⁻ⁿ` satisfy every hypothesis. -/
example (k : ℕ) :
    mNorm (1 : Matrix (Fin 1) (Fin 1) ℝ) ((1 / 2 : ℝ) ^ k • (fun _ => (1 : ℝ)) - 0) ≤
      (1 / 2 + 1 / 2 * 1 * (1 / 2)) ^ k *
        mNorm (1 : Matrix (Fin 1) (Fin 1) ℝ) ((1 / 2 : ℝ) ^ 0 • (fun _ => (1 : ℝ)) - 0) :=
  (inexact_preconditioned_richardson_contractive (A := 1) (ηbar := 1 / 2) Matrix.PosDef.one
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) one_pos (fun v => (mNorm_one_sub_half v).le)
    (fun v => by simp) (b := 0) (by simp) (fun _ => 0) (fun _ => 1)
    (fun j => (1 / 2 : ℝ) ^ j • fun _ => (1 : ℝ)) (fun _ => 0)
    (fun j => by
      simp only [Matrix.one_mulVec, inv_one, zero_sub, pow_succ]
      module)
    (fun _ => le_rfl) (fun _ => by simp [mNorm]) (fun _ => by norm_num) (by norm_num)).2 k

end MNorm

/-! ### Least squares and inexact flexible GMRES (Section 5) -/

section LeastSquares

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **Stability of least-squares solutions** (the argument behind Lemma 5.1 of Simoncini and
Szyld, used as (D.3) in arXiv 2610.07653). If `y` minimizes `‖c - H y'‖` over all `y'` and
`σ ‖w‖ ≤ ‖H w‖` with `σ > 0`, then `‖y - z‖ ≤ ‖c - H z‖ / σ` for every `z`: `H (y - z)` is the
orthogonal projection of `c - H z` onto the range of `H`. -/
theorem norm_sub_le_of_isLeastSquares (H : F →ₗ[ℝ] G) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ w, σ * ‖w‖ ≤ ‖H w‖) {c : G} {y : F} (hy : ∀ y', ‖c - H y‖ ≤ ‖c - H y'‖) (z : F) :
    ‖y - z‖ ≤ ‖c - H z‖ / σ := by
  have hmem : H y ∈ LinearMap.range H := LinearMap.mem_range_self H y
  have horth : ∀ w ∈ LinearMap.range H, ⟪c - H y, w⟫ = 0 := by
    rw [← Submodule.norm_eq_iInf_iff_real_inner_eq_zero _ hmem]
    refine le_antisymm (le_ciInf ?_) (ciInf_le ⟨0, ?_⟩ (⟨H y, hmem⟩ : LinearMap.range H))
    · rintro ⟨w, hw⟩
      obtain ⟨y', rfl⟩ := LinearMap.mem_range.mp hw
      exact hy y'
    · rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
  have hd : c - H z = (c - H y) + H (y - z) := by rw [map_sub]; abel
  have hpy : ‖c - H z‖ ^ 2 = ‖c - H y‖ ^ 2 + ‖H (y - z)‖ ^ 2 := by
    rw [hd, norm_add_sq_real, horth _ (LinearMap.mem_range_self H _)]
    ring
  have h1 : ‖H (y - z)‖ ≤ ‖c - H z‖ := by
    nlinarith [norm_nonneg (H (y - z)), norm_nonneg (c - H z), sq_nonneg ‖c - H y‖]
  rw [le_div_iff₀ hσ, mul_comm]
  exact (hH _).trans h1

end LeastSquares

/-- Coordinate form of `norm_sub_le_of_isLeastSquares`: if `z j = 0`, then
`|y j| ≤ ‖c - H z‖ / σ`. -/
theorem abs_apply_le_of_isLeastSquares {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ κ) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ w, σ * ‖w‖ ≤ ‖H w‖) {c : EuclideanSpace ℝ κ} {y : EuclideanSpace ℝ ι}
    (hy : ∀ y', ‖c - H y‖ ≤ ‖c - H y'‖) {z : EuclideanSpace ℝ ι} {j : ι} (hz : z j = 0) :
    |y j| ≤ ‖c - H z‖ / σ := by
  have h : ‖(y - z) j‖ ≤ ‖y - z‖ := PiLp.norm_apply_le (y - z) j
  rw [PiLp.sub_apply, hz, sub_zero, Real.norm_eq_abs] at h
  exact h.trans (norm_sub_le_of_isLeastSquares H hσ hH hy z)

/-- A left inverse gives the lower bound of Theorem 5.1 of arXiv 2610.07653: if `G H = 1`, then
`‖w‖ ≤ ‖G‖₂ ‖H w‖` (core `specNorm`). For the pseudoinverse `G = H⁺` of a full-column-rank `H`,
`‖G‖₂⁻¹ = σ_min(H)`, the constant of (5.8). -/
theorem sigma_lowerBound_of_mul_eq_one {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {H : Matrix κ ι ℝ} {G : Matrix ι κ ℝ} (hGH : G * H = 1)
    (w : EuclideanSpace ℝ ι) : ‖w‖ ≤ specNorm G * ‖Matrix.toEuclideanLin H w‖ := by
  have h : Matrix.toEuclideanLin G (Matrix.toEuclideanLin H w) = w := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hGH, Matrix.toLpLin_one,
      LinearMap.id_apply]
  calc ‖w‖ = ‖Matrix.toEuclideanLin G (Matrix.toEuclideanLin H w)‖ := by rw [h]
    _ ≤ specNorm G * ‖Matrix.toEuclideanLin H w‖ := norm_toEuclideanLin_le G _

/-- Bridge from the library's convention for orthonormal columns: if `Qᵀ Q = 1`, the columns of
`Q` form an orthonormal family in `EuclideanSpace` (the basis `Q_{m+1}` of (5.5)). -/
theorem orthonormal_col_of_transpose_mul_eq_one {N ι : Type*} [Fintype N] [DecidableEq ι]
    {Q : Matrix N ι ℝ} (hQ : Qᵀ * Q = 1) :
    Orthonormal ℝ fun i => WithLp.toLp 2 (Q.col i) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_toLp_col_col, hQ, Matrix.one_apply]

section FGMRES

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m : ℕ}

/-- `‖∑ aᵢ qᵢ‖ = ‖a‖₂` for an orthonormal family `q`. -/
theorem norm_sum_smul_of_orthonormal {ι : Type*} [Fintype ι] {q : ι → V}
    (hq : Orthonormal ℝ q) (a : EuclideanSpace ℝ ι) : ‖∑ i, a i • q i‖ = ‖a‖ := by
  have h1 : ‖∑ i, a i • q i‖ ^ 2 = ∑ i, a i * a i := by
    rw [← real_inner_self_eq_norm_sq, hq.inner_sum a a Finset.univ]
    simp
  have h2 : ‖a‖ ^ 2 = ∑ i, a i * a i := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h1.trans h2.symm)

/-- `H` (of size `(m+1) × m`) is upper Hessenberg: `H i k = 0` whenever `i > k + 1`. -/
def IsUpperHessenberg (H : Matrix (Fin (m + 1)) (Fin m) ℝ) : Prop :=
  ∀ (i : Fin (m + 1)) (k : Fin m), (k : ℕ) + 1 < i → H i k = 0

/-- The leading block `H̄_k = H̄_m(1:k+1, 1:k)` of an `(m+1) × m` matrix (arXiv 2610.07653,
Theorem 5.1). -/
def hessBlock (H : Matrix (Fin (m + 1)) (Fin m) ℝ) (k : Fin (m + 1)) :
    Matrix (Fin (k + 1)) (Fin k) ℝ :=
  Matrix.of fun i j => H (Fin.castLE (Nat.succ_le_succ k.is_le) i) (Fin.castLE k.is_le j)

/-- The computed residual `r⁽ᵏ⁾ = Q_{k+1} (β e₁ - H̄_k y)` of (5.7) in arXiv 2610.07653, for an
Arnoldi basis `q₀, …, q_m` (the paper's `q⁽¹⁾, …, q⁽ᵐ⁺¹⁾`) and `y ∈ ℝᵏ`. -/
noncomputable def computedResidual (q : Fin (m + 1) → V) (H : Matrix (Fin (m + 1)) (Fin m) ℝ)
    (β : ℝ) (k : Fin (m + 1)) (y : EuclideanSpace ℝ (Fin k)) : V :=
  ∑ i : Fin (k + 1),
    (EuclideanSpace.single (0 : Fin (k + 1)) β - Matrix.toEuclideanLin (hessBlock H k) y) i •
      q (Fin.castLE (Nat.succ_le_succ k.is_le) i)

/-- Zero padding of `y ∈ ℝᵏ` to `ℝᵐ`. -/
def padVec (k : Fin (m + 1)) (y : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j => if h : (j : ℕ) < k then y ⟨j, h⟩ else 0

theorem padVec_apply_of_le (k : Fin (m + 1)) (y : EuclideanSpace ℝ (Fin k)) {j : Fin m}
    (hj : (k : ℕ) ≤ j) : padVec k y j = 0 := by
  simp [padVec, not_lt.mpr hj]

theorem padVec_last (y : EuclideanSpace ℝ (Fin m)) : padVec (Fin.last m) y = y := by
  ext j
  simp [padVec]

/-- `H̄_m (y padded) = (H̄_k y)` in the first `k+1` rows. -/
theorem toEuclideanLin_padVec_castLE (H : Matrix (Fin (m + 1)) (Fin m) ℝ) (k : Fin (m + 1))
    (y : EuclideanSpace ℝ (Fin k)) (i : Fin (k + 1)) :
    Matrix.toEuclideanLin H (padVec k y) (Fin.castLE (Nat.succ_le_succ k.is_le) i) =
      Matrix.toEuclideanLin (hessBlock H k) y i := by
  simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  symm
  refine Fintype.sum_of_injective (Fin.castLE k.is_le) (Fin.castLE_injective _) _ _ ?_ ?_
  · intro j hj
    have hkj : (k : ℕ) ≤ j := by
      by_contra h
      exact hj ⟨⟨j, by omega⟩, rfl⟩
    simp [padVec_apply_of_le k y hkj]
  · intro j
    simp [hessBlock, padVec, Matrix.of_apply]

/-- For upper Hessenberg `H`, `H̄_m (y padded)` vanishes below row `k+1`. -/
theorem toEuclideanLin_padVec_eq_zero {H : Matrix (Fin (m + 1)) (Fin m) ℝ}
    (hHess : IsUpperHessenberg H) (k : Fin (m + 1))
    (y : EuclideanSpace ℝ (Fin k)) {i : Fin (m + 1)} (hi : (k : ℕ) < i) :
    Matrix.toEuclideanLin H (padVec k y) i = 0 := by
  simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : (j : ℕ) < k
  · rw [hHess i j (by omega), zero_mul]
  · rw [show (padVec k y).ofLp j = 0 from padVec_apply_of_le k y (not_lt.mp hj), mul_zero]

/-- For upper Hessenberg `H`, the computed residual (5.7) is `Q_{m+1}` applied to the padded
least-squares residual `β e₁ - H̄_m (y padded)`. -/
theorem computedResidual_eq {H : Matrix (Fin (m + 1)) (Fin m) ℝ} (hHess : IsUpperHessenberg H)
    (q : Fin (m + 1) → V) (β : ℝ) (k : Fin (m + 1)) (y : EuclideanSpace ℝ (Fin k)) :
    computedResidual q H β k y =
      ∑ i, (EuclideanSpace.single (0 : Fin (m + 1)) β -
        Matrix.toEuclideanLin H (padVec k y)) i • q i := by
  refine Fintype.sum_of_injective (Fin.castLE (Nat.succ_le_succ k.is_le))
    (Fin.castLE_injective _)
    (fun i : Fin (k + 1) => (EuclideanSpace.single (0 : Fin (k + 1)) β -
      Matrix.toEuclideanLin (hessBlock H k) y) i • q (Fin.castLE (Nat.succ_le_succ k.is_le) i))
    (fun i : Fin (m + 1) => (EuclideanSpace.single (0 : Fin (m + 1)) β -
      Matrix.toEuclideanLin H (padVec k y)) i • q i) ?_ ?_
  · intro i hi
    have hki : (k : ℕ) < i := by
      by_contra h
      exact hi ⟨⟨i, by omega⟩, rfl⟩
    have hi0 : i ≠ 0 := by
      intro h
      rw [h] at hki
      simp at hki
    have h0 := toEuclideanLin_padVec_eq_zero hHess k y hki
    simp [h0, hi0]
  · intro i
    have h2 : (Fin.castLE (Nat.succ_le_succ k.is_le) i = 0) ↔ i = 0 := by
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_castLE, Fin.val_zero, Fin.val_zero]
    simp only [PiLp.sub_apply, toEuclideanLin_padVec_castLE, PiLp.single_apply, h2]

/-- The norm of the computed residual is the norm of the padded least-squares residual. -/
theorem norm_computedResidual {H : Matrix (Fin (m + 1)) (Fin m) ℝ}
    (hHess : IsUpperHessenberg H) {q : Fin (m + 1) → V}
    (hq : Orthonormal ℝ q) (β : ℝ) (k : Fin (m + 1)) (y : EuclideanSpace ℝ (Fin k)) :
    ‖computedResidual q H β k y‖ =
      ‖EuclideanSpace.single (0 : Fin (m + 1)) β - Matrix.toEuclideanLin H (padVec k y)‖ := by
  rw [computedResidual_eq hHess, norm_sum_smul_of_orthonormal hq]

/-- **The residual-gap identity (D.2) of arXiv 2610.07653.** Let `A Z + E = Q H` column by column
(5.5), `r⁽⁰⁾ = b̃ - a₀` with `a₀ = A_lr(φ⁽⁰⁾; τ₀)`, `β = ‖r⁽⁰⁾‖ > 0` and `q₀ = r⁽⁰⁾/β`. For
every `y ∈ ℝᵐ`, `b - A (φ⁽⁰⁾ + Z y) - Q (β e₁ - H y) = (b - b̃) + (a₀ - A φ⁽⁰⁾) + E y`. The
paper's `ϵ₀ = A_lr(φ⁽⁰⁾) - Aφ⁽⁰⁾` is `a₀ - A φ⁽⁰⁾`. -/
theorem fgmres_true_residual_sub_computed (A : V →ₗ[ℝ] V) {b bt φ0 a0 : V} {β : ℝ}
    (hβ : β ≠ 0) {q : Fin (m + 1) → V}
    (hq0 : q 0 = β⁻¹ • (bt - a0)) {Z E : Fin m → V} {H : Matrix (Fin (m + 1)) (Fin m) ℝ}
    (hArn : ∀ k, A (Z k) + E k = ∑ i, H i k • q i) (y : EuclideanSpace ℝ (Fin m)) :
    (b - A (φ0 + ∑ j, y j • Z j)) -
        ∑ i, (EuclideanSpace.single (0 : Fin (m + 1)) β - Matrix.toEuclideanLin H y) i • q i =
      (b - bt) + (a0 - A φ0) + ∑ j, y j • E j := by
  have h1 : ∑ i, (EuclideanSpace.single (0 : Fin (m + 1)) β - Matrix.toEuclideanLin H y) i • q i =
      (bt - a0) - ∑ j, y j • ∑ i, H i j • q i := by
    simp only [PiLp.sub_apply, PiLp.single_apply, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [hq0, smul_smul, mul_inv_cancel₀ hβ, one_smul, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 : A (φ0 + ∑ j, y j • Z j) =
      A φ0 + ∑ j, y j • ∑ i, H i j • q i - ∑ j, y j • E j := by
    rw [map_add, map_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hArn j, smul_add, add_sub_cancel_right]
  rw [h1, h2]
  abel

/-- **The coefficient bound (D.3) of arXiv 2610.07653** (Lemma 5.1 of Simoncini and Szyld, for
FGMRES). If `y⁽ᵐ⁾` minimizes `‖β e₁ - H̄_m y‖` and `σ ‖w‖ ≤ ‖H̄_m w‖` (so `σ ≤ σ_m(H̄_m)`), then
`|(y⁽ᵐ⁾)_k| ≤ ‖r⁽ᵏ⁻¹⁾‖₂ / σ` for `k = 1, …, m` (here the 0-based index `j = k - 1`), where
`r⁽ᵏ⁻¹⁾` is the computed residual (5.7) of an arbitrary `y⁽ᵏ⁻¹⁾ ∈ ℝᵏ⁻¹`. The paper takes
`y⁽ᵏ⁻¹⁾` to be the least-squares solution; that is not needed. -/
theorem fgmres_coeff_le {H : Matrix (Fin (m + 1)) (Fin m) ℝ}
    (hHess : IsUpperHessenberg H) {q : Fin (m + 1) → V}
    (hq : Orthonormal ℝ q) {β σ : ℝ} (hσ : 0 < σ)
    (hHσ : ∀ w, σ * ‖w‖ ≤ ‖Matrix.toEuclideanLin H w‖)
    (y : (k : Fin (m + 1)) → EuclideanSpace ℝ (Fin k))
    (hy : ∀ z, ‖EuclideanSpace.single (0 : Fin (m + 1)) β -
        Matrix.toEuclideanLin H (y (Fin.last m))‖ ≤
      ‖EuclideanSpace.single (0 : Fin (m + 1)) β - Matrix.toEuclideanLin H z‖) (j : Fin m) :
    |y (Fin.last m) j| ≤ ‖computedResidual q H β j.castSucc (y j.castSucc)‖ / σ := by
  rw [norm_computedResidual hHess hq]
  exact abs_apply_le_of_isLeastSquares _ hσ hHσ hy
    (padVec_apply_of_le _ _ (by simp))

/-- **Theorem 5.1 of arXiv 2610.07653** (residual-gap estimate for inexact FGMRES with an inexact
right-hand side). Let `‖b - b̃‖ ≤ ε₀` and `‖A φ⁽⁰⁾ - a₀‖ ≤ ε₀` (5.4), where
`a₀ = A_lr(φ⁽⁰⁾; τ₀)`; let `β = ‖b̃ - a₀‖ > 0` and `q₀ = (b̃ - a₀)/β`. Suppose `m` steps of the
inexact flexible Arnoldi process give `A Z_m + E_m = Q_{m+1} H̄_m` (5.5), with orthonormal
`q₀, …, q_m` and upper Hessenberg `H̄_m`, and let `y⁽ᵐ⁾` minimize `‖β e₁ - H̄_m y‖` (5.6). If
`σ ‖w‖ ≤ ‖H̄_m w‖` with `σ > 0`, `2 ε₀ ≤ ε_gap`, and every matvec error satisfies (5.8),
`‖ϵ_k‖ ≤ (σ/m) (ε_gap - 2ε₀) / ‖r⁽ᵏ⁻¹⁾‖`, then the true residual
`b - A φ⁽ᵐ⁾`, `φ⁽ᵐ⁾ = φ⁽⁰⁾ + Z_m y⁽ᵐ⁾`, differs from the computed one `r⁽ᵐ⁾` (5.7) by at most
`ε_gap`.

Indices are 0-based: `q 0` is `q⁽¹⁾`, `E j` is `ϵ_{j+1}` and is paired with `r⁽ʲ⁾`. Deviations,
all making the statement more general: `σ` is any constant with `σ ‖w‖ ≤ ‖H̄_m w‖` (the paper's
`σ_m(H̄_m)` is the largest one, and `σ > 0` is full column rank); `y⁽ᵏ⁾` for `k < m` may be any
vectors (the paper's least-squares solutions are a special case); `ε₀ ≥ 0` and `ε₀ < ε_gap/2`
are weakened to `2ε₀ ≤ ε_gap`; `‖r⁽ᵏ⁻¹⁾‖ > 0` is dropped (with `x / 0 = 0`, (5.8) then forces
`ϵ_k = 0`); `β = ‖r⁽⁰⁾‖` is not assumed (it follows from `‖q₀‖ = 1`). The exact solution
`Aφ = b` plays no role. -/
theorem fgmres_residual_gap_le (A : V →ₗ[ℝ] V) {b bt φ0 a0 : V} {ε0 εgap β σ : ℝ}
    (hb : ‖b - bt‖ ≤ ε0) (ha0 : ‖A φ0 - a0‖ ≤ ε0) (hβ : 0 < β)
    {q : Fin (m + 1) → V} (hq : Orthonormal ℝ q) (hq0 : q 0 = β⁻¹ • (bt - a0))
    {Z E : Fin m → V} {H : Matrix (Fin (m + 1)) (Fin m) ℝ}
    (hArn : ∀ k, A (Z k) + E k = ∑ i, H i k • q i)
    (hHess : IsUpperHessenberg H)
    (hσ : 0 < σ) (hHσ : ∀ w, σ * ‖w‖ ≤ ‖Matrix.toEuclideanLin H w‖)
    (y : (k : Fin (m + 1)) → EuclideanSpace ℝ (Fin k))
    (hy : ∀ z, ‖EuclideanSpace.single (0 : Fin (m + 1)) β -
        Matrix.toEuclideanLin H (y (Fin.last m))‖ ≤
      ‖EuclideanSpace.single (0 : Fin (m + 1)) β - Matrix.toEuclideanLin H z‖)
    (hgap : 2 * ε0 ≤ εgap)
    (hE : ∀ k : Fin m, ‖E k‖ ≤
      σ / m * ((εgap - 2 * ε0) / ‖computedResidual q H β k.castSucc (y k.castSucc)‖)) :
    ‖(b - A (φ0 + ∑ j, y (Fin.last m) j • Z j)) -
      computedResidual q H β (Fin.last m) (y (Fin.last m))‖ ≤ εgap := by
  set ym : EuclideanSpace ℝ (Fin m) := y (Fin.last m) with hym
  have hres : computedResidual q H β (Fin.last m) (y (Fin.last m)) =
      ∑ i, (EuclideanSpace.single (0 : Fin (m + 1)) β - Matrix.toEuclideanLin H ym) i • q i := by
    rw [computedResidual_eq hHess, padVec_last]
  rw [hres]
  refine (le_of_eq (congrArg norm
    (fgmres_true_residual_sub_computed (b := b) (φ0 := φ0) A hβ.ne' hq0 hArn ym))).trans ?_
  set x := εgap - 2 * ε0 with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hterm : ∀ j : Fin m, ‖ym j • E j‖ ≤ x / m := by
    intro j
    set R := ‖computedResidual q H β j.castSucc (y j.castSucc)‖ with hR
    have hc : |ym j| ≤ R / σ := fgmres_coeff_le hHess hq hσ hHσ y hy j
    rw [norm_smul, Real.norm_eq_abs]
    calc |ym j| * ‖E j‖ ≤ R / σ * (σ / m * (x / R)) :=
          mul_le_mul hc (hE j) (norm_nonneg _) (div_nonneg (norm_nonneg _) hσ.le)
      _ ≤ x / m := by
          have hR0 : 0 ≤ R := norm_nonneg _
          rcases hR0.eq_or_lt with h | h
          · rw [← h]
            simp only [zero_div, zero_mul]
            exact div_nonneg hx0 (Nat.cast_nonneg _)
          · rcases Nat.eq_zero_or_pos m with hm | hm
            · simp [hm]
            · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
              apply le_of_eq
              field_simp
  have hsum : ‖∑ j, ym j • E j‖ ≤ x := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hterm j).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm, hx0]
    · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      rw [mul_div_cancel₀ _ hm'.ne']
  have ha0' : ‖a0 - A φ0‖ ≤ ε0 := by rwa [norm_sub_rev]
  calc ‖(b - bt) + (a0 - A φ0) + ∑ j, ym j • E j‖
      ≤ ‖b - bt‖ + ‖a0 - A φ0‖ + ‖∑ j, ym j • E j‖ := norm_add₃_le
    _ ≤ ε0 + ε0 + x := by gcongr
    _ = εgap := by rw [hx]; ring

end FGMRES

/-- Non-vacuity of `fgmres_residual_gap_le` with an inexact right-hand side and an inexact
matvec (one Arnoldi step in `ℝ²`, zero initial guess as in Section 6 of the paper): `A = I`,
`φ⁽⁰⁾ = a₀ = 0`, `b̃ = e₁`, `b = e₁ + e₂/4` (`ε₀ = 1/4`), `Z = q₀ = e₁`, matvec error
`ϵ₁ = e₂/2`, so `H̄₁ = (1, 1/2)ᵀ`, `σ = 1`, `y⁽¹⁾ = 4/5`, `ε_gap = 2`. -/
example : True := by
  have hq : Orthonormal ℝ fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ) :=
    EuclideanSpace.orthonormal_single
  have hHess : IsUpperHessenberg !![(1 : ℝ); 1 / 2] := fun i k h => by
    fin_cases i <;> fin_cases k <;> simp_all
  have hpad : ∀ v : EuclideanSpace ℝ (Fin ((0 : Fin 2) : ℕ)), padVec (m := 1) 0 v = 0 := by
    intro v
    ext j
    simp [padVec]
  have := fgmres_residual_gap_le (V := EuclideanSpace ℝ (Fin 2)) (m := 1) LinearMap.id
    (b := EuclideanSpace.single 0 1 + (1 / 4 : ℝ) • EuclideanSpace.single 1 1)
    (bt := EuclideanSpace.single 0 1) (φ0 := 0) (a0 := 0)
    (ε0 := 1 / 4) (εgap := 2) (β := 1) (σ := 1) (by simp [norm_smul]) (by norm_num) one_pos hq
    (by simp) (Z := fun _ => EuclideanSpace.single 0 1)
    (E := fun _ => (1 / 2 : ℝ) • EuclideanSpace.single 1 1)
    (H := !![1; 1 / 2]) (fun k => by fin_cases k; simp [Fin.sum_univ_two]) hHess
    one_pos (fun w => by
      rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq]
      simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs,
        Fin.sum_univ_one]
      simp [Matrix.mulVec, dotProduct]
      nlinarith [sq_nonneg (w 0)])
    (fun _ => WithLp.toLp 2 fun _ => 4 / 5)
    (fun z => by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      simp [Matrix.toLpLin_apply, dotProduct]
      nlinarith [sq_nonneg (z 0 - 4 / 5)])
    (by norm_num) (fun k => by
      fin_cases k
      rw [norm_computedResidual hHess hq]
      simp [hpad, norm_smul]
      norm_num)
  trivial

end LeanDLRA.Literature.P2610_07653
