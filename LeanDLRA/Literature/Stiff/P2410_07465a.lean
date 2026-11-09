import Mathlib.Analysis.Matrix.Order
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Stiff.ImplicitBUG

/-!
# Meng–Appelö–Cheng (arXiv 2410.07465): stability, convergence and the ES-preconditioner lemma

S. Meng, D. Appelö, Y. Cheng, *Preconditioning low rank GMRES for implicit discretizations of
matrix differential equations*, arXiv:2410.07465v1.  Statements checked against the printed PDF
(page images), 2026-11-09.

The setting is (1.1), `Ẋ = F(X, t) = ∑ⱼ Aⱼ X Bⱼᵀ + G(t)` on `ℝ^{m×n}` with the Frobenius inner
product (`open scoped LeanDLRA.Frobenius`), and Algorithm 4.2 with `θ = 1/2` (implicit midpoint):
at step `n`, lrGMRES solves `𝒜 X = b`, `𝒜 X = X - (Δt/2) ∑ⱼ Aⱼ X Bⱼᵀ`,
`b = Xⁿ + (Δt/2) ∑ⱼ Aⱼ Xⁿ Bⱼᵀ + Δt Gⁿ`, until `‖𝒜 X̃ - b‖ ≤ δ (‖𝒜‖₂ ‖X̃‖ + ‖b‖)` with `δ = ε`;
then `X^{n+1} = T_{ε₂}(X̃)` (truncated SVD).  Hypotheses are stated as in the paper: the field
through `hF : F t X = ∑ⱼ Aⱼ X Bⱼᵀ + G t`, the one-sided Lipschitz condition as the core
`IsOneSidedLipschitzField F α`, `‖𝒜‖₂ ≤ a` as `ha`, convergence of Line 7 as the stopping
criterion `hconv`, and the truncation by the properties the paper's proofs use
(`‖X^{n+1}‖ ≤ ‖X̃‖` for Theorem 4.1, `‖X^{n+1} - X̃‖ ≤ ε₂` for Theorem 4.2).  Index `k` of the
sequences `Xt`, `t` stands for the paper's `X̃^{k+1}`, `t^{k+1/2}`.

## Main results

* **Theorem 4.1 (p. 8) is false as printed when `G ≠ 0`**: `stability_false_with_source` (every
  problem, every converged lrGMRES run from `X⁰ = 0` with a truncation tolerance below an
  explicit data bound gives `X¹ ≠ 0`, so `‖Xⁿ‖ ≤ C ‖X⁰‖` fails for every `C`), with
  `gmres_iterate_ne_zero_of_source`, `gmres_iterate_norm_ge_of_source` and
  `stability_counterexample_instance` (an instance satisfying every printed hypothesis, for every
  mesh size `h ≤ 1/2`).  The source `G` is part of (1.1) (p. 1), an input of Algorithm 4.2 (p. 7)
  and nonzero in the experiments ((5.1), (5.3), p. 10).  The proof breaks at p. 9, first display,
  third line (`⟨Δt F(z, t), 2z⟩ ≤ (α Δt/2) ‖2z‖²` needs `F(0, t) = 0`) and at (4.4) (p. 8, last
  line, which drops `Δt Gⁿ` from `‖b‖`).  The scalar zero-operator case is already the core
  `LeanDLRA.midpoint_forcing_counterexample`.
* **Theorem 4.1, corrected**: `stability_with_source` (from the core
  `LeanDLRA.midpoint_forcing_global`), `stability_with_source_uniform`
  (`‖Xᵏ‖ ≤ e^{(2α + 4K) T} (‖X⁰‖ + 4 T Γ)`, `C` independent of `Δt, h`), and
  `stability_homogeneous` (the printed bound holds for `G = 0`).  Ingredients:
  `gmres_residual_eq` (the residual of Line 7 is the paper's `rⁿ`), `residual_norm_le` ((4.4) with
  the source term) and `residual_const_le_of_mesh` (the paper's scalings `ε = O(h³)`,
  `‖𝒜‖₂ ≤ C Δt/h²`, `Δt ≍ h` give the `C Δt²` of (4.4)).
* **Theorem 4.2 (p. 9), conditional**: `convergence_conditional`, `convergence_conditional_order`
  (eq. (4.5), `‖Xⁿ - X(tⁿ)‖ ≤ C Δt` given `‖X⁰ - X(t⁰)‖ = O(Δt)`).  **Conditional on the local
  truncation bound** `‖Gⁿ‖ ≤ τ = O(Δt²)` for the exact solution (hypothesis `hcons`), which the
  paper asserts "from local truncation analysis" without proof and which includes the spatial
  error of the PDE, so it cannot be derived here.  The residual bound that the paper takes from
  (4.4) and stability is derived.  The theorem is not affected by the error in Theorem 4.1: only
  differences of `F` enter, and the source cancels.
* **Lemma A.2 (p. 21)**: `spectral_comparison_inv` and `spectral_comparison_inv_kroneckerSum`
  (corrected statement; `f(A)` is Mathlib's continuous functional calculus `cfc f A`),
  `spectral_comparison_inv_lower` (what the printed one-sided hypothesis gives) and
  `spectral_comparison_printed_upper_counterexample` (typo: the printed hypothesis
  `t⁻¹ - f̃(t) ≤ δ t⁻¹` lacks the absolute value of Lemma A.1, and the upper bound then fails).
  The assumptions `δ* ∈ (0,1)`, `σ(A) ⊂ [1, cond A]` and continuity and positivity of `f̃` are
  not needed; the Kronecker structure enters only through `posDef_kroneckerSum`.

## Not formalized

* Lemma A.1 (p. 21), the sinc-quadrature bound `|t⁻¹ - S(t)| ≤ δ* t⁻¹` on `[1, T]`: an analytic
  quadrature estimate quoted from [3, Cor. 4.3] without proof; not specific to low-rank methods.
* Algorithm 4.1 (BUG preconditioner): the paper states no theorem; its exactness is the core
  `LeanDLRA.bugPreconditioner_exact` (`Stiff/ImplicitSolvability`).
* The estimate `cond(𝒜 M) ≈ (1 + δ*)/(1 - δ*)` (p. 22) is stated as "expected from [3]", not
  claimed.

## Connection to the library

Core definitions: `IsOneSidedLipschitzField`, the Frobenius inner product space of
`LeanDLRA.Matrix.Frobenius`; core theorems: `midpoint_forcing_global`, `midpoint_norm_le_forcing`,
`amplified_sum_le`, `one_add_div_one_sub_le_exp` (`Stiff/ImplicitBUG`).  Mathlib: `cfc`,
`Matrix.PosDef`, `Matrix.PosDef.kronecker`.  No local definitions.
-/

open Set Finset
open scoped RealInnerProductSpace Matrix Kronecker

namespace LeanDLRA.Literature.P2410_07465

open LeanDLRA

/-! ### Appendix A, Lemma A.2 -/

section SpectralComparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma star_eq_transpose_real {κ : Type*} (M : Matrix κ κ ℝ) : star M = Mᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- `cfc f A = U diag(f λ) Uᵀ` for a real symmetric matrix `A` with eigenvector matrix `U`. -/
private lemma cfc_eq_conj {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, star_eq_transpose_real]
  rfl

/-- The quadratic form of `f(A)` is the eigenvalue-weighted sum of squared coordinates. -/
private lemma dot_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) (v : ι → ℝ) :
    v ⬝ᵥ (cfc f A *ᵥ v) =
      ∑ i, f (hA.eigenvalues i) * ((hA.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ *ᵥ v) i ^ 2 := by
  rw [cfc_eq_conj hA, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `A⁻¹ = f(A)` for `f(t) = t⁻¹` and positive definite `A`. -/
private lemma inv_eq_cfc {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A⁻¹ = cfc (fun t : ℝ => t⁻¹) A := by
  rw [cfc_ringInverse_id A hA.isUnit hA.1.isSelfAdjoint, Matrix.nonsing_inv_eq_ringInverse]

/-- **Lemma A.2, lower half, under the printed one-sided hypothesis** (arXiv 2410.07465, p. 21).
For real symmetric positive definite `A` and any `f : ℝ → ℝ` with `t⁻¹ - f t ≤ δ t⁻¹` on the
spectrum of `A` (the hypothesis exactly as printed, without absolute value),
`(1 - δ) ⟨A⁻¹ v, v⟩ ≤ ⟨f(A) v, v⟩` for every `v`; `f(A)` is Mathlib's `cfc f A`.  This is the
half of the conclusion that the printed hypothesis supports; for the other half see
`spectral_comparison_printed_upper_counterexample`.  The Kronecker form of `A`, `δ ∈ (0, 1)`,
`σ(A) ⊂ [1, cond A]` and continuity and positivity of `f` are not needed. -/
theorem spectral_comparison_inv_lower {A : Matrix ι ι ℝ} (hA : A.PosDef) {δ : ℝ} (f : ℝ → ℝ)
    (happrox : ∀ t ∈ spectrum ℝ A, t⁻¹ - f t ≤ δ * t⁻¹) (v : ι → ℝ) :
    (1 - δ) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) ≤ v ⬝ᵥ (cfc f A *ᵥ v) := by
  rw [inv_eq_cfc hA, dot_cfc hA.1, dot_cfc hA.1, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := happrox _ (hA.1.eigenvalues_mem_spectrum_real i)
  have hf : (1 - δ) * (hA.1.eigenvalues i)⁻¹ ≤ f (hA.1.eigenvalues i) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hf
    (sq_nonneg (((hA.1.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ *ᵥ v) i))]

/-- **Lemma A.2, upper half** (arXiv 2410.07465, p. 21), under the other half `f t - t⁻¹ ≤ δ t⁻¹`
of the corrected two-sided hypothesis: `⟨f(A) v, v⟩ ≤ (1 + δ) ⟨A⁻¹ v, v⟩`. -/
theorem spectral_comparison_inv_upper {A : Matrix ι ι ℝ} (hA : A.PosDef) {δ : ℝ} (f : ℝ → ℝ)
    (happrox : ∀ t ∈ spectrum ℝ A, f t - t⁻¹ ≤ δ * t⁻¹) (v : ι → ℝ) :
    v ⬝ᵥ (cfc f A *ᵥ v) ≤ (1 + δ) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by
  rw [inv_eq_cfc hA, dot_cfc hA.1, dot_cfc hA.1, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := happrox _ (hA.1.eigenvalues_mem_spectrum_real i)
  have hf : f (hA.1.eigenvalues i) ≤ (1 + δ) * (hA.1.eigenvalues i)⁻¹ := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hf
    (sq_nonneg (((hA.1.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ *ᵥ v) i))]

/-- **Lemma A.2, corrected** (arXiv 2410.07465, p. 21; the paper cites [3, Prop. 4.1]).  For
real symmetric positive definite `A` and `f` with `|t⁻¹ - f t| ≤ δ t⁻¹` on the spectrum of `A`,
`(1 - δ) ⟨A⁻¹ v, v⟩ ≤ ⟨f(A) v, v⟩ ≤ (1 + δ) ⟨A⁻¹ v, v⟩` for every `v`, with `f(A) = cfc f A`.
Deviation: the printed hypothesis has no absolute value (a typo: Lemma A.1, which supplies the
hypothesis, has it, and without it the upper bound is false,
`spectral_comparison_printed_upper_counterexample`).  Stated for every positive definite `A`;
the paper's extra assumptions are not needed (see `spectral_comparison_inv_lower`). -/
theorem spectral_comparison_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) {δ : ℝ} (f : ℝ → ℝ)
    (happrox : ∀ t ∈ spectrum ℝ A, |t⁻¹ - f t| ≤ δ * t⁻¹) (v : ι → ℝ) :
    (1 - δ) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) ≤ v ⬝ᵥ (cfc f A *ᵥ v) ∧
      v ⬝ᵥ (cfc f A *ᵥ v) ≤ (1 + δ) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) :=
  ⟨spectral_comparison_inv_lower hA f (fun t ht => (abs_le.1 (happrox t ht)).2) v,
    spectral_comparison_inv_upper hA f (fun t ht => by
      have := (abs_le.1 (happrox t ht)).1; linarith) v⟩

/-- The Kronecker sum `A₁ ⊗ I + I ⊗ A₂` of positive definite matrices is positive definite: the
operator `A = ∑ᵢ ⊗ⱼ Bᵢⱼ` of Appendix A of arXiv 2410.07465 (two factors) satisfies the
hypothesis of `spectral_comparison_inv`. -/
theorem posDef_kroneckerSum {κ : Type*} [Finite κ] [DecidableEq κ] {A₁ A₂ : Matrix κ κ ℝ}
    (h₁ : A₁.PosDef) (h₂ : A₂.PosDef) :
    (A₁ ⊗ₖ (1 : Matrix κ κ ℝ) + (1 : Matrix κ κ ℝ) ⊗ₖ A₂).PosDef :=
  (h₁.kronecker Matrix.PosDef.one).add (Matrix.PosDef.one.kronecker h₂)

/-- **Lemma A.2, corrected, in the paper's Kronecker form** (arXiv 2410.07465, p. 21):
`A = A₁ ⊗ I + I ⊗ A₂` with `A₁, A₂ ∈ ℝ^{N×N}` positive definite.  Deviations: absolute value in
the hypothesis (see `spectral_comparison_inv`); `v ∈ ℝ^{N²}` (the printed `v ∈ ℝ^N` does not match
the size of `A`); `δ* ∈ (0,1)`, `σ(A) ⊂ [1, cond A]`, continuity and positivity of `f` dropped. -/
theorem spectral_comparison_inv_kroneckerSum {N : ℕ} {A₁ A₂ : Matrix (Fin N) (Fin N) ℝ}
    (h₁ : A₁.PosDef) (h₂ : A₂.PosDef) {δ : ℝ} (f : ℝ → ℝ)
    (happrox : ∀ t ∈ spectrum ℝ (A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂), |t⁻¹ - f t| ≤ δ * t⁻¹)
    (v : Fin N × Fin N → ℝ) :
    (1 - δ) * (v ⬝ᵥ ((A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂)⁻¹ *ᵥ v)) ≤ v ⬝ᵥ (cfc f (A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂) *ᵥ v) ∧
      v ⬝ᵥ (cfc f (A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂) *ᵥ v) ≤
        (1 + δ) * (v ⬝ᵥ ((A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂)⁻¹ *ᵥ v)) :=
  spectral_comparison_inv (posDef_kroneckerSum h₁ h₂) f happrox v

/-- **Lemma A.2 as printed is false (upper bound)** (arXiv 2410.07465, p. 21, last eight lines).
The printed hypothesis is one-sided, `t⁻¹ - f̃(t) ≤ δ t⁻¹` (checked in the page image).  Take
`N = 1`, `A₁ = A₂ = 1/2`, so `A = A₁ ⊗ I + I ⊗ A₂ = I` with `σ(A) = {1} ⊂ [1, cond A] = [1, 1]`,
the continuous positive `f̃ ≡ 2` and `δ* = 1/2`: the hypothesis `1 - 2 ≤ 1/2` holds, but
`⟨f̃(A) v, v⟩ = 2 > 3/2 = (1 + δ*) ⟨A⁻¹ v, v⟩` for `v = 1`.  With the absolute value the lemma
holds (`spectral_comparison_inv_kroneckerSum`); the lower bound holds as printed
(`spectral_comparison_inv_lower`).  Severity: typo. -/
theorem spectral_comparison_printed_upper_counterexample :
    ∃ A₁ A₂ : Matrix (Fin 1) (Fin 1) ℝ, A₁.PosDef ∧ A₂.PosDef ∧
      spectrum ℝ (A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂) = {1} ∧
      ∃ f : ℝ → ℝ, Continuous f ∧ (∀ t, 0 < f t) ∧ ∃ δ ∈ Ioo (0 : ℝ) 1,
        (∀ t ∈ spectrum ℝ (A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂), t⁻¹ - f t ≤ δ * t⁻¹) ∧
        ∃ v : Fin 1 × Fin 1 → ℝ, (1 + δ) * (v ⬝ᵥ ((A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂)⁻¹ *ᵥ v)) <
          v ⬝ᵥ (cfc f (A₁ ⊗ₖ 1 + 1 ⊗ₖ A₂) *ᵥ v) := by
  have hhalf : ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  have hA : ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) ⊗ₖ 1 +
      1 ⊗ₖ ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) = 1 := by
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, ← add_smul]
    norm_num
  refine ⟨_, _, hhalf, hhalf, by rw [hA, spectrum.one_eq], fun _ => 2, continuous_const,
    fun _ => by norm_num, 1 / 2, ⟨by norm_num, by norm_num⟩, ?_, fun _ => 1, ?_⟩
  · rw [hA, spectrum.one_eq]
    rintro t rfl
    norm_num
  · rw [hA, inv_one, cfc_const (2 : ℝ) (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℝ),
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [dotProduct]
    norm_num

end SpectralComparison

/-! ### Section 4.1: the implicit midpoint scheme with low-rank GMRES (Theorems 4.1 and 4.2) -/

section Midpoint

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] {s : ℕ}

/-- The operator `X ↦ ∑ⱼ Aⱼ X Bⱼᵀ` of (1.1) maps differences to differences. -/
private lemma opSum_sub (A : Fin s → Matrix m m ℝ) (B : Fin s → Matrix n n ℝ)
    (X Y : Matrix m n ℝ) :
    ∑ j, A j * (X - Y) * (B j)ᵀ = ∑ j, A j * X * (B j)ᵀ - ∑ j, A j * Y * (B j)ᵀ := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_sub, Matrix.sub_mul]

/-- The operator `X ↦ ∑ⱼ Aⱼ X Bⱼᵀ` of (1.1) is homogeneous. -/
private lemma opSum_smul (A : Fin s → Matrix m m ℝ) (B : Fin s → Matrix n n ℝ) (c : ℝ)
    (X : Matrix m n ℝ) :
    ∑ j, A j * (c • X) * (B j)ᵀ = c • ∑ j, A j * X * (B j)ᵀ := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The operator `X ↦ ∑ⱼ Aⱼ X Bⱼᵀ` of (1.1) is additive. -/
private lemma opSum_add (A : Fin s → Matrix m m ℝ) (B : Fin s → Matrix n n ℝ)
    (X Y : Matrix m n ℝ) :
    ∑ j, A j * (X + Y) * (B j)ᵀ = ∑ j, A j * X * (B j)ᵀ + ∑ j, A j * Y * (B j)ᵀ := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_add, Matrix.add_mul]

private lemma opSum_zero (A : Fin s → Matrix m m ℝ) (B : Fin s → Matrix n n ℝ) :
    ∑ j, A j * (0 : Matrix m n ℝ) * (B j)ᵀ = 0 := by
  simp

/-- **The lrGMRES residual is the paper's `rⁿ`** (arXiv 2410.07465, Algorithm 4.2 with `θ = 1/2`,
p. 7, and the proof of Theorem 4.1, p. 8).  For `F(t, X) = ∑ⱼ Aⱼ X Bⱼᵀ + G(t)` (eq. (1.1)), the
residual `𝒜 X̃ - b` of the linear system of Lines 1 and 5, `𝒜 X = X - (Δt/2) ∑ⱼ Aⱼ X Bⱼᵀ` and
`b = Xⁿ + (Δt/2) ∑ⱼ Aⱼ Xⁿ Bⱼᵀ + Δt Gⁿ`, equals `X̃ - Xⁿ - Δt F(t, (Xⁿ + X̃)/2)`.  (Line 5 prints
`+ Gⁿ_θ` without the factor `Δt` that (4.1) has; we follow (4.1).) -/
theorem gmres_residual_eq {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) (Δt t : ℝ) (X Xt : Matrix m n ℝ) :
    (Xt - (Δt / 2) • ∑ j, A j * Xt * (B j)ᵀ) -
        (X + (Δt / 2) • ∑ j, A j * X * (B j)ᵀ + Δt • G t) =
      Xt - X - Δt • F t ((1 / 2 : ℝ) • (X + Xt)) := by
  rw [hF, opSum_smul, opSum_add]
  module

/-- **Eq. (4.4) with the source restored** (arXiv 2410.07465, p. 8, last line).  If `‖𝒜‖₂ ≤ a`
(`ha`) and the lrGMRES stopping criterion `‖r‖ ≤ δ (a ‖X̃‖ + ‖b‖)` holds, then
`‖r‖ ≤ δ (2 + a) (‖X̃‖ + ‖Xⁿ‖) + δ Δt ‖Gⁿ‖`.  The printed (4.4) has no term in `Gⁿ`; it is right
for `G = 0`.  (`a` is any upper bound of the operator norm; the paper's sampled estimate of `‖𝒜‖₂`
is a lower bound of it, so the paper's criterion implies the one used here.) -/
theorem residual_norm_le {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ} {Δt δ a : ℝ}
    (hΔt : 0 ≤ Δt) (hδ : 0 ≤ δ)
    (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖)
    {X Xt r g : Matrix m n ℝ}
    (hconv : ‖r‖ ≤ δ * (a * ‖Xt‖ + ‖X + (Δt / 2) • ∑ j, A j * X * (B j)ᵀ + Δt • g‖)) :
    ‖r‖ ≤ δ * (2 + a) * (‖Xt‖ + ‖X‖) + δ * Δt * ‖g‖ := by
  have hb : ‖X + (Δt / 2) • ∑ j, A j * X * (B j)ᵀ + Δt • g‖ ≤ (2 + a) * ‖X‖ + Δt * ‖g‖ := by
    have e : X + (Δt / 2) • ∑ j, A j * X * (B j)ᵀ + Δt • g =
        ((2 : ℝ) • X - (X - (Δt / 2) • ∑ j, A j * X * (B j)ᵀ)) + Δt • g := by module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hΔt]
    have := norm_sub_le ((2 : ℝ) • X) (X - (Δt / 2) • ∑ j, A j * X * (B j)ᵀ)
    rw [norm_smul, Real.norm_two] at this
    nlinarith [ha X]
  have hXt := norm_nonneg Xt
  nlinarith [mul_le_mul_of_nonneg_left hb hδ, mul_nonneg hδ hXt]

/-- **The paper's parameter scalings make the residual constant `O(Δt²)`** (arXiv 2410.07465,
p. 8, before Theorem 4.1): from `δ = ε ≤ c₁ h³`, `‖𝒜‖₂ ≤ a ≤ c₂ Δt / h²`, `h ≤ c₀ Δt` and
`h ≤ 1`, the constant of `residual_norm_le` satisfies `δ (2 + a) ≤ c₁ c₀ (2 c₀ + c₂) Δt²`,
which is the `C Δt²` of (4.4).  The paper writes `Δt = O(h)`; its estimate needs `Δt` and `h` of
the same order ("We assume the time step and spatial mesh is on the same order"), used here as
`h ≤ c₀ Δt`. -/
theorem residual_const_le_of_mesh {δ a Δt h c₀ c₁ c₂ : ℝ} (hh : 0 < h) (h1 : h ≤ 1)
    (ha0 : 0 ≤ a) (hc₁ : 0 ≤ c₁) (hδ : δ ≤ c₁ * h ^ 3)
    (ha : a ≤ c₂ * Δt / h ^ 2) (hΔt : h ≤ c₀ * Δt) :
    δ * (2 + a) ≤ c₁ * c₀ * (2 * c₀ + c₂) * Δt ^ 2 := by
  have hh2 : 0 < h ^ 2 := by positivity
  have hah : a * h ^ 2 ≤ c₂ * Δt := by rwa [le_div_iff₀ hh2] at ha
  have hΔ0 : 0 ≤ c₀ * Δt := hh.le.trans hΔt
  have e1 : δ * (2 + a) ≤ c₁ * h ^ 3 * (2 + a) := mul_le_mul_of_nonneg_right hδ (by linarith)
  have e2 : c₁ * h ^ 3 * (2 + a) = 2 * c₁ * h ^ 3 + c₁ * h * (a * h ^ 2) := by ring
  have e3 : c₁ * h * (a * h ^ 2) ≤ c₁ * h * (c₂ * Δt) :=
    mul_le_mul_of_nonneg_left hah (by positivity)
  have hh3 : h ^ 3 ≤ h * (c₀ * Δt) ^ 2 := by
    have : h ^ 2 ≤ (c₀ * Δt) ^ 2 := pow_le_pow_left₀ hh.le hΔt 2
    nlinarith
  have hh4 : h * (c₀ * Δt) ^ 2 ≤ (c₀ * Δt) ^ 2 := by nlinarith [sq_nonneg (c₀ * Δt)]
  have hc2Δ : 0 ≤ c₂ * Δt := (mul_nonneg ha0 hh2.le).trans hah
  have hh5 : c₁ * h * (c₂ * Δt) ≤ c₁ * (c₀ * Δt) * (c₂ * Δt) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔt hc₁) hc2Δ
  have hh6 : 2 * c₁ * h ^ 3 ≤ 2 * c₁ * (c₀ * Δt) ^ 2 :=
    mul_le_mul_of_nonneg_left (hh3.trans hh4) (by positivity)
  calc δ * (2 + a) ≤ 2 * c₁ * h ^ 3 + c₁ * h * (a * h ^ 2) := e2 ▸ e1
    _ ≤ 2 * c₁ * (c₀ * Δt) ^ 2 + c₁ * (c₀ * Δt) * (c₂ * Δt) := by linarith
    _ = c₁ * c₀ * (2 * c₀ + c₂) * Δt ^ 2 := by ring

/-- **Theorem 4.1, corrected: stability with the source term** (arXiv 2410.07465, p. 8).
`F(t, X) = ∑ⱼ Aⱼ X Bⱼᵀ + G(t)` one-sided Lipschitz with `α ≥ 0` (for `α < 0` use `α = 0`),
`‖𝒜‖₂ ≤ a`, lrGMRES converged at every step (`hconv`, the stopping criterion with `δ = ε`), and
the truncation `X^{k+1} = T_{ε₂}(X̃^{k+1})` non-expansive (`htr`, the property used on p. 8).  If
`Δt α/2 + δ (2 + a) ≤ 1/2`, then
`‖Xᵏ‖ ≤ exp (4 (Δt α/2 + δ (2 + a)) k) (‖X⁰‖ + ∑_{i<k} 2 (1 + δ) Δt ‖G(tᵢ)‖)`.
Indexing: `Xt k` is the paper's `X̃^{k+1}`, `t k` its `t^{k+1/2}`.  Proof: the core theorem
`LeanDLRA.midpoint_forcing_global` with `residual_norm_le`.  The printed `‖Xⁿ‖ ≤ C ‖X⁰‖` lacks the
source term and is false for `G ≠ 0` (`stability_false_with_source`); see
`stability_with_source_uniform` for a mesh-independent constant. -/
theorem stability_with_source {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {α Δt δ a : ℝ}
    (hos : IsOneSidedLipschitzField F α) (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hδ : 0 ≤ δ)
    (ha0 : 0 ≤ a) (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖)
    (hq : Δt * α / 2 + δ * (2 + a) ≤ 1 / 2) {N : ℕ} {X Xt : ℕ → Matrix m n ℝ} {t : ℕ → ℝ}
    (hconv : ∀ k < N, ‖Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k))‖ ≤
      δ * (a * ‖Xt k‖ + ‖X k + (Δt / 2) • ∑ j, A j * X k * (B j)ᵀ + Δt • G (t k)‖))
    (htr : ∀ k < N, ‖X (k + 1)‖ ≤ ‖Xt k‖) :
    ∀ k ≤ N, ‖X k‖ ≤ Real.exp (4 * (Δt * α / 2 + δ * (2 + a)) * k) *
      (‖X 0‖ + ∑ i ∈ range k, 2 * (1 + δ) * Δt * ‖G (t i)‖) := by
  have hF0 : ∀ τ, F τ 0 = G τ := fun τ => by rw [hF, opSum_zero, zero_add]
  have key := midpoint_forcing_global (h := Δt) (κ := δ * (2 + a)) hα (by positivity) hΔt hq hos
    (r := fun k => Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k)))
    (η := fun k => δ * Δt * ‖G (t k)‖) (fun k => by positivity)
    (fun k _ => by abel) (fun k hk => residual_norm_le hΔt hδ ha (hconv k hk)) htr
  intro k hk
  refine (key k hk).trans_eq ?_
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF0]
  ring

/-- `exp (4 (Δt α/2 + κ) k) ≤ exp ((2 α + 4 K) T)` when `κ ≤ K Δt` and `k Δt ≤ N Δt ≤ T`. -/
private lemma exp_step_le {α Δt κ K T : ℝ} {k N : ℕ} (hα : 0 ≤ α) (hΔt : 0 ≤ Δt)
    (hK0 : 0 ≤ K) (hκ : κ ≤ K * Δt) (hk : k ≤ N) (hT : N * Δt ≤ T) :
    Real.exp (4 * (Δt * α / 2 + κ) * k) ≤ Real.exp ((2 * α + 4 * K) * T) := by
  refine Real.exp_le_exp.2 ?_
  have hkN : (k : ℝ) * Δt ≤ N * Δt :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔt
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 4 * (Δt * α / 2 + κ) * k ≤ (2 * α + 4 * K) * (k * Δt) := by nlinarith
  have h2 : (2 * α + 4 * K) * (k * Δt) ≤ (2 * α + 4 * K) * T :=
    mul_le_mul_of_nonneg_left (hkN.trans hT) (by positivity)
  linarith

/-- **Theorem 4.1, corrected, with a mesh-independent constant** (arXiv 2410.07465, p. 8).
Under the hypotheses of `stability_with_source`, if moreover `δ (2 + a) ≤ K Δt` (which the
paper's scalings give, `residual_const_le_of_mesh`), `δ ≤ 1`, `N Δt ≤ T` and `‖G‖ ≤ Γ` at the
evaluation times, then `‖Xᵏ‖ ≤ exp ((2 α + 4 K) T) (‖X⁰‖ + 4 T Γ)` for `k ≤ N`.  The constant does
not depend on `Δt` or `h`; the printed statement omits the term `4 T Γ`. -/
theorem stability_with_source_uniform {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {α Δt δ a K T Γ : ℝ}
    (hos : IsOneSidedLipschitzField F α) (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (ha0 : 0 ≤ a)
    (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖)
    (hq : Δt * α / 2 + δ * (2 + a) ≤ 1 / 2) (hK0 : 0 ≤ K) (hK : δ * (2 + a) ≤ K * Δt)
    (hΓ : 0 ≤ Γ) {N : ℕ} (hT : N * Δt ≤ T) {X Xt : ℕ → Matrix m n ℝ} {t : ℕ → ℝ}
    (hG : ∀ k < N, ‖G (t k)‖ ≤ Γ)
    (hconv : ∀ k < N, ‖Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k))‖ ≤
      δ * (a * ‖Xt k‖ + ‖X k + (Δt / 2) • ∑ j, A j * X k * (B j)ᵀ + Δt • G (t k)‖))
    (htr : ∀ k < N, ‖X (k + 1)‖ ≤ ‖Xt k‖) :
    ∀ k ≤ N, ‖X k‖ ≤ Real.exp ((2 * α + 4 * K) * T) * (‖X 0‖ + 4 * T * Γ) := by
  intro k hk
  have h1 := stability_with_source hF hos hα hΔt hδ ha0 ha hq hconv htr k hk
  have hsum : ∑ i ∈ range k, 2 * (1 + δ) * Δt * ‖G (t i)‖ ≤ 4 * T * Γ := by
    have hterm : ∀ i ∈ range k, 2 * (1 + δ) * Δt * ‖G (t i)‖ ≤ 4 * Δt * Γ := fun i hi => by
      have hi' : i < N := (Finset.mem_range.1 hi).trans_le hk
      have := hG i hi'
      have hn := norm_nonneg (G (t i))
      have e1 : 2 * (1 + δ) * Δt * ‖G (t i)‖ ≤ 4 * Δt * ‖G (t i)‖ := by
        have : 2 * (1 + δ) ≤ 4 := by linarith
        have := mul_le_mul_of_nonneg_right this (mul_nonneg hΔt hn)
        linarith
      have e2 : 4 * Δt * ‖G (t i)‖ ≤ 4 * Δt * Γ :=
        mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hkN : (k : ℝ) * Δt ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔt).trans hT
    nlinarith
  have hS : 0 ≤ ‖X 0‖ + ∑ i ∈ range k, 2 * (1 + δ) * Δt * ‖G (t i)‖ :=
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => by positivity)
  calc ‖X k‖ ≤ Real.exp (4 * (Δt * α / 2 + δ * (2 + a)) * k) *
        (‖X 0‖ + ∑ i ∈ range k, 2 * (1 + δ) * Δt * ‖G (t i)‖) := h1
    _ ≤ Real.exp ((2 * α + 4 * K) * T) *
        (‖X 0‖ + ∑ i ∈ range k, 2 * (1 + δ) * Δt * ‖G (t i)‖) :=
      mul_le_mul_of_nonneg_right (exp_step_le hα hΔt hK0 hK hk hT) hS
    _ ≤ Real.exp ((2 * α + 4 * K) * T) * (‖X 0‖ + 4 * T * Γ) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

/-- **Theorem 4.1 as printed, for `G = 0`** (arXiv 2410.07465, p. 8): without a source the
printed bound holds, `‖Xᵏ‖ ≤ C ‖X⁰‖` with `C = exp ((2 α + 4 K) T)` independent of `Δt` and `h`
(hypotheses as in `stability_with_source_uniform`). -/
theorem stability_homogeneous {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {α Δt δ a K T : ℝ}
    (hos : IsOneSidedLipschitzField F α) (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (ha0 : 0 ≤ a)
    (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖)
    (hq : Δt * α / 2 + δ * (2 + a) ≤ 1 / 2) (hK0 : 0 ≤ K) (hK : δ * (2 + a) ≤ K * Δt)
    {N : ℕ} (hT : N * Δt ≤ T) {X Xt : ℕ → Matrix m n ℝ} {t : ℕ → ℝ}
    (hG : ∀ k < N, G (t k) = 0)
    (hconv : ∀ k < N, ‖Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k))‖ ≤
      δ * (a * ‖Xt k‖ + ‖X k + (Δt / 2) • ∑ j, A j * X k * (B j)ᵀ + Δt • G (t k)‖))
    (htr : ∀ k < N, ‖X (k + 1)‖ ≤ ‖Xt k‖) :
    ∀ k ≤ N, ‖X k‖ ≤ Real.exp ((2 * α + 4 * K) * T) * ‖X 0‖ := by
  intro k hk
  have := stability_with_source_uniform hF hos hα hΔt hδ hδ1 ha0 ha hq hK0 hK le_rfl hT
    (fun i hi => by rw [hG i hi, norm_zero]) hconv htr k hk
  simpa using this

/-- **From `X⁰ = 0` a converged lrGMRES iterate is bounded below by the source** (arXiv 2410.07465,
Algorithm 4.2, first step).  If `‖𝒜‖₂ ≤ a` and `X̃` meets the stopping criterion with right-hand
side `b = Δt G`, then `(1 - δ) ‖Δt G‖ ≤ (1 + δ) a ‖X̃‖`. -/
theorem gmres_iterate_norm_ge_of_source {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {Δt δ a t : ℝ}
    (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖) {Xt : Matrix m n ℝ}
    (hconv : ‖Xt - 0 - Δt • F t ((1 / 2 : ℝ) • (0 + Xt))‖ ≤
      δ * (a * ‖Xt‖ + ‖(0 : Matrix m n ℝ) +
        (Δt / 2) • ∑ j, A j * (0 : Matrix m n ℝ) * (B j)ᵀ + Δt • G t‖)) :
    (1 - δ) * ‖Δt • G t‖ ≤ (1 + δ) * a * ‖Xt‖ := by
  rw [← gmres_residual_eq hF] at hconv
  rw [opSum_zero, smul_zero, add_zero, zero_add] at hconv
  have e : Δt • G t = (Xt - (Δt / 2) • ∑ j, A j * Xt * (B j)ᵀ) -
      ((Xt - (Δt / 2) • ∑ j, A j * Xt * (B j)ᵀ) - Δt • G t) := by abel
  have h0 := norm_sub_le (Xt - (Δt / 2) • ∑ j, A j * Xt * (B j)ᵀ)
    ((Xt - (Δt / 2) • ∑ j, A j * Xt * (B j)ᵀ) - Δt • G t)
  rw [← e] at h0
  have := ha Xt
  linarith

/-- **From `X⁰ = 0` a converged lrGMRES iterate is nonzero when `G ≠ 0`** (arXiv 2410.07465,
Algorithm 4.2): for every operator, every `Δt ≠ 0` and every tolerance `δ < 1`, any `X̃` meeting
the stopping criterion (with any value `a` in place of `‖𝒜‖₂`) is nonzero. -/
theorem gmres_iterate_ne_zero_of_source {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {Δt δ a t : ℝ} (hΔt : Δt ≠ 0)
    (hδ : δ < 1) (hG : G t ≠ 0) {Xt : Matrix m n ℝ}
    (hconv : ‖Xt - 0 - Δt • F t ((1 / 2 : ℝ) • (0 + Xt))‖ ≤
      δ * (a * ‖Xt‖ + ‖(0 : Matrix m n ℝ) +
        (Δt / 2) • ∑ j, A j * (0 : Matrix m n ℝ) * (B j)ᵀ + Δt • G t‖)) :
    Xt ≠ 0 := by
  rintro rfl
  have hpos : 0 < ‖Δt • G t‖ := norm_pos_iff.2 (smul_ne_zero hΔt hG)
  rw [← gmres_residual_eq hF] at hconv
  simp only [opSum_zero, smul_zero, sub_zero, add_zero, zero_add, zero_sub, norm_neg,
    norm_zero, mul_zero] at hconv
  nlinarith

/-- **Theorem 4.1 is false as printed when `G ≠ 0`** (arXiv 2410.07465, p. 8, Theorem 4.1:
`‖Xⁿ‖ ≤ C ‖X⁰‖`, `C` independent of `Δt, h`).  For every problem (1.1) with `‖𝒜‖₂ ≤ a`, start
`X⁰ = 0`, any converged lrGMRES iterate `X̃` (tolerance `0 ≤ δ < 1`) and any truncation `X¹` with
`‖X¹ - X̃‖ ≤ ε₂`, where `(1 + δ) a ε₂ < (1 - δ) ‖Δt G‖` (e.g. `ε₂ = 0`, or `ε₂ = c h²` with `c`
small when `a ≤ C Δt/h²`), we get `X¹ ≠ 0`, so `‖X¹‖ ≤ C ‖X⁰‖ = 0` fails for every `C`.  The
proof of Theorem 4.1 (p. 9, first display, third line) uses
`⟨Δt F((Xⁿ + X̃)/2), X̃ + Xⁿ⟩ ≤ (α Δt/2) ‖Xⁿ + X̃‖²`, which needs `F(0, t) = G(t) = 0`, and (4.4)
(p. 8, last line) drops `Δt Gⁿ` from `‖b‖`.  Corrected statement: `stability_with_source`.  The
scalar case with zero operator is the core `LeanDLRA.midpoint_forcing_counterexample`; an
instance satisfying every printed hypothesis is `stability_counterexample_instance`. -/
theorem stability_false_with_source {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {Δt δ a t ε₂ : ℝ} (hδ0 : 0 ≤ δ)
    (ha0 : 0 ≤ a) (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖)
    {Xt X1 : Matrix m n ℝ}
    (hconv : ‖Xt - 0 - Δt • F t ((1 / 2 : ℝ) • (0 + Xt))‖ ≤
      δ * (a * ‖Xt‖ + ‖(0 : Matrix m n ℝ) +
        (Δt / 2) • ∑ j, A j * (0 : Matrix m n ℝ) * (B j)ᵀ + Δt • G t‖))
    (htr : ‖X1 - Xt‖ ≤ ε₂) (hε₂ : (1 + δ) * a * ε₂ < (1 - δ) * ‖Δt • G t‖) :
    X1 ≠ 0 ∧ ∀ C : ℝ, ¬ ‖X1‖ ≤ C * ‖(0 : Matrix m n ℝ)‖ := by
  have hge := gmres_iterate_norm_ge_of_source hF ha hconv
  have hne : X1 ≠ 0 := by
    rintro rfl
    rw [zero_sub, norm_neg] at htr
    have : (1 + δ) * a * ‖Xt‖ ≤ (1 + δ) * a * ε₂ :=
      mul_le_mul_of_nonneg_left htr (mul_nonneg (by linarith) ha0)
    linarith
  refine ⟨hne, fun C hC => hne ?_⟩
  rw [norm_zero, mul_zero] at hC
  exact norm_le_zero_iff.1 hC

/-- The `1 × 1` Frobenius norm of the identity is `1`. -/
private lemma norm_one_fin_one : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
  rw [Frobenius.norm_def]
  simp

/-- **An instance with every hypothesis of Theorem 4.1 (arXiv 2410.07465, p. 8) and `X¹ ≠ 0`
from `X⁰ = 0`.**  For each mesh size `h ∈ (0, 1/2]`: `1 × 1` matrices, `s = 1`,
`A₁ = -h⁻² I` (dissipative, eigenvalue of size `h⁻²` as for a diffusion matrix), `B₁ = I`,
`G ≡ I`, `Δt = h`, tolerance `δ = ε = h³` (`O(h³)`), truncation tolerance `ε₂ = h³ ≤ h²`.
Then `F` is one-sided Lipschitz with `α = 0`, `‖𝒜‖₂ ≤ (3/2) Δt/h²`, the exact solve
`X̃ = 2h²/(2h+1) I` meets the stopping criterion (residual `0`), `‖X̃‖ > ε₂`, so the truncated
SVD keeps it (`X¹ = X̃`), and `‖X¹‖ ≤ C ‖X⁰‖` fails for every `C`. -/
theorem stability_counterexample_instance {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) :
    ∃ (A B : Fin 1 → Matrix (Fin 1) (Fin 1) ℝ) (G : ℝ → Matrix (Fin 1) (Fin 1) ℝ)
      (F : ℝ → Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ),
      (∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) ∧ IsOneSidedLipschitzField F 0 ∧
      (∀ Y : Matrix (Fin 1) (Fin 1) ℝ,
        ‖Y - (h / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ 3 / 2 * (h / h ^ 2) * ‖Y‖) ∧
      ∃ Xt : Matrix (Fin 1) (Fin 1) ℝ,
        ‖Xt - 0 - h • F 0 ((1 / 2 : ℝ) • (0 + Xt))‖ ≤
          h ^ 3 * (3 / 2 * (h / h ^ 2) * ‖Xt‖ + ‖(0 : Matrix (Fin 1) (Fin 1) ℝ) +
            (h / 2) • ∑ j, A j * (0 : Matrix (Fin 1) (Fin 1) ℝ) * (B j)ᵀ + h • G 0‖) ∧
        h ^ 3 < ‖Xt‖ ∧ ∀ C : ℝ, ¬ ‖Xt‖ ≤ C * ‖(0 : Matrix (Fin 1) (Fin 1) ℝ)‖ := by
  set c : ℝ := -(h ^ 2)⁻¹ with hc
  have hL : ∀ X : Matrix (Fin 1) (Fin 1) ℝ,
      ∑ _j : Fin 1, (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * X * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ =
        c • X := fun X => by simp
  have hh2 : 0 < h ^ 2 := by positivity
  set x : ℝ := 2 * h ^ 2 / (2 * h + 1) with hx
  have hx0 : 0 < x := by positivity
  refine ⟨fun _ => c • 1, fun _ => 1, fun _ => 1,
    fun _ X => ∑ _j : Fin 1, (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * X *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + 1, fun _ _ => rfl, ?_, ?_, x • 1, ?_, ?_, ?_⟩
  · intro t X Y
    simp only [hL, add_sub_add_right_eq_sub, ← smul_sub, real_inner_smul_left,
      real_inner_self_eq_norm_sq, zero_mul]
    have : c ≤ 0 := by rw [hc]; exact neg_nonpos.2 (inv_nonneg.2 hh2.le)
    nlinarith [sq_nonneg ‖X - Y‖]
  · intro Y
    rw [hL]
    have hh0 : h ≠ 0 := hh.ne'
    have e : Y - (h / 2) • (c • Y) = (1 + 1 / (2 * h)) • Y := by
      have : (1 + 1 / (2 * h)) = 1 - h / 2 * c := by rw [hc]; field_simp; ring
      rw [this, sub_smul, one_smul, smul_smul]
    rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have e' : 3 / 2 * (h / h ^ 2) = 1 / (2 * h) + 1 / h := by field_simp; ring
    have : 1 ≤ 1 / h := by rw [le_div_iff₀ hh]; linarith
    rw [e']
    linarith
  · have hres : x • (1 : Matrix (Fin 1) (Fin 1) ℝ) - 0 - h • (∑ _j : Fin 1,
        (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * ((1 / 2 : ℝ) • (0 + x • 1)) *
          (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + 1) = 0 := by
      rw [hL]
      have hs : x - h * (c * (1 / 2 * x)) - h = 0 := by
        have h0 : h ≠ 0 := hh.ne'
        have h1 : 2 * h + 1 ≠ 0 := by positivity
        rw [hx, hc]; field_simp; ring
      calc _ = (x - h * (c * (1 / 2 * x)) - h) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by module
        _ = 0 := by rw [hs, zero_smul]
    rw [hres, norm_zero]
    positivity
  · rw [norm_smul, norm_one_fin_one, mul_one, Real.norm_of_nonneg hx0.le, hx,
      lt_div_iff₀ (by positivity)]
    have : h * (2 * h + 1) ≤ 1 := by nlinarith
    nlinarith
  · intro C hC
    rw [norm_zero, mul_zero, norm_smul, norm_one_fin_one, mul_one] at hC
    have := norm_pos_iff.2 hx0.ne'
    linarith

/-- **Theorem 4.2, conditional on the local truncation bound** (arXiv 2410.07465, p. 9).
Hypotheses as in `stability_with_source`, but with the truncation property used in the proof of
Theorem 4.2, `‖X^{k+1} - X̃^{k+1}‖ ≤ ε₂` (`htr`), and, as a **hypothesis**, the bound
`‖Gᵏ‖ ≤ τ` on the defect `Gᵏ = X(t_{k+1}) - X(t_k) - Δt F((X(t_k) + X(t_{k+1}))/2, t^{k+1/2})`
of the exact solution values `Xex k` (`hcons`).  The paper takes `Gⁿ = C Δt²` "from local
truncation analysis" (p. 9) without proof; it contains the spatial error of the PDE (5.1) and the
norm rescaling, so it is not derivable in this finite-dimensional setting.  The residual bound
that the paper takes from "(4.4) and the stability result" is derived (`residual_norm_le`).
Conclusion: `‖Xᵏ - X(tₖ)‖ ≤ exp (4 q k) (‖X⁰ - X(t₀)‖ + ∑_{i<k} (2 cᵢ + ε₂))` with
`q = Δt α/2 + δ (2 + a)` and `cᵢ = δ (2 + a) (‖X(tᵢ)‖ + ‖X(t_{i+1})‖) + δ Δt ‖G(tᵢ)‖ + τ`.
Proof: core `LeanDLRA.midpoint_norm_le_forcing` and `LeanDLRA.amplified_sum_le`. -/
theorem convergence_conditional {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {α Δt δ a τ ε₂ : ℝ}
    (hos : IsOneSidedLipschitzField F α) (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hδ : 0 ≤ δ)
    (ha0 : 0 ≤ a) (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖)
    (hq : Δt * α / 2 + δ * (2 + a) ≤ 1 / 2) (hτ : 0 ≤ τ) (hε₂ : 0 ≤ ε₂) {N : ℕ}
    {X Xt Xex : ℕ → Matrix m n ℝ} {t : ℕ → ℝ}
    (hconv : ∀ k < N, ‖Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k))‖ ≤
      δ * (a * ‖Xt k‖ + ‖X k + (Δt / 2) • ∑ j, A j * X k * (B j)ᵀ + Δt • G (t k)‖))
    (htr : ∀ k < N, ‖X (k + 1) - Xt k‖ ≤ ε₂)
    (hcons : ∀ k < N, ‖Xex (k + 1) - Xex k -
      Δt • F (t k) ((1 / 2 : ℝ) • (Xex k + Xex (k + 1)))‖ ≤ τ) :
    ∀ k ≤ N, ‖X k - Xex k‖ ≤ Real.exp (4 * (Δt * α / 2 + δ * (2 + a)) * k) *
      (‖X 0 - Xex 0‖ + ∑ i ∈ range k, (2 * (δ * (2 + a) * (‖Xex i‖ + ‖Xex (i + 1)‖) +
        δ * Δt * ‖G (t i)‖ + τ) + ε₂)) := by
  set κ := δ * (2 + a) with hκ
  set q := Δt * α / 2 + κ with hqdef
  have hκ0 : 0 ≤ κ := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hpos : 0 < 1 - q := by linarith
  set b := (1 + q) / (1 - q) with hb
  have hb1 : 1 ≤ b := by rw [hb, le_div_iff₀ hpos]; linarith
  have hlin : ∀ τ' (z : Matrix m n ℝ), F τ' z - F τ' 0 = ∑ j, A j * z * (B j)ᵀ :=
    fun τ' z => by rw [hF, hF, opSum_zero, zero_add, add_sub_cancel_right]
  have hc0 : ∀ i, 0 ≤ 2 * (κ * (‖Xex i‖ + ‖Xex (i + 1)‖) + δ * Δt * ‖G (t i)‖ + τ) + ε₂ :=
    fun i => by positivity
  have key := amplified_sum_le (e := fun k => ‖X k - Xex k‖)
    (c := fun i => 2 * (κ * (‖Xex i‖ + ‖Xex (i + 1)‖) + δ * Δt * ‖G (t i)‖ + τ) + ε₂)
    (a := b) (N := N) (fun _ => norm_nonneg _) hc0 (fun k hk => by
      have hL : ∑ j, A j * ((1 / 2 : ℝ) • ((X k - Xex k) + (Xt k - Xex (k + 1)))) * (B j)ᵀ =
          ∑ j, A j * ((1 / 2 : ℝ) • (X k + Xt k)) * (B j)ᵀ -
            ∑ j, A j * ((1 / 2 : ℝ) • (Xex k + Xex (k + 1))) * (B j)ᵀ := by
        rw [← opSum_sub]
        congr 1
        funext j
        congr 2
        module
      have hstep : Xt k - Xex (k + 1) = (X k - Xex k) +
          Δt • (fun _ z => ∑ j, A j * z * (B j)ᵀ) (t k)
            ((1 / 2 : ℝ) • ((X k - Xex k) + (Xt k - Xex (k + 1)))) +
          ((Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k))) -
            (Xex (k + 1) - Xex k - Δt • F (t k) ((1 / 2 : ℝ) • (Xex k + Xex (k + 1))))) := by
        simp only [hF]
        rw [hL]
        module
      have hos' : ⟪(fun _ z => ∑ j, A j * z * (B j)ᵀ) (t k)
            ((1 / 2 : ℝ) • ((X k - Xex k) + (Xt k - Xex (k + 1)))) -
          (fun _ (z : Matrix m n ℝ) => ∑ j, A j * z * (B j)ᵀ) (t k) 0,
          (1 / 2 : ℝ) • ((X k - Xex k) + (Xt k - Xex (k + 1)))⟫ ≤
          α * ‖(1 / 2 : ℝ) • ((X k - Xex k) + (Xt k - Xex (k + 1)))‖ ^ 2 := by
        have := hos (t k) ((1 / 2 : ℝ) • ((X k - Xex k) + (Xt k - Xex (k + 1)))) 0
        simp only [sub_zero, hlin] at this
        simpa only [opSum_zero, sub_zero] using this
      have h1 := midpoint_norm_le_forcing (F := fun _ z => ∑ j, A j * z * (B j)ᵀ) (t := t k)
        (X := X k - Xex k) (Xt := Xt k - Xex (k + 1)) hα hΔt hstep hos'
      simp only [opSum_zero, norm_zero, mul_zero, add_zero] at h1
      have hr := residual_norm_le hΔt hδ ha (hconv k hk)
      have hΓ := hcons k hk
      have hrΓ := norm_sub_le (Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k)))
        (Xex (k + 1) - Xex k - Δt • F (t k) ((1 / 2 : ℝ) • (Xex k + Xex (k + 1))))
      have hXt : ‖Xt k‖ ≤ ‖Xt k - Xex (k + 1)‖ + ‖Xex (k + 1)‖ := by
        simpa using norm_add_le (Xt k - Xex (k + 1)) (Xex (k + 1))
      have hX : ‖X k‖ ≤ ‖X k - Xex k‖ + ‖Xex k‖ := by
        simpa using norm_add_le (X k - Xex k) (Xex k)
      set Ck := κ * (‖Xex k‖ + ‖Xex (k + 1)‖) + δ * Δt * ‖G (t k)‖ + τ with hCk
      have hC0 : 0 ≤ Ck := by positivity
      have h3 : (1 - q) * ‖Xt k - Xex (k + 1)‖ ≤ (1 + q) * ‖X k - Xex k‖ + Ck := by
        have e1 : κ * ‖Xt k‖ ≤ κ * (‖Xt k - Xex (k + 1)‖ + ‖Xex (k + 1)‖) :=
          mul_le_mul_of_nonneg_left hXt hκ0
        have e2 : κ * ‖X k‖ ≤ κ * (‖X k - Xex k‖ + ‖Xex k‖) :=
          mul_le_mul_of_nonneg_left hX hκ0
        rw [hqdef, hCk]
        nlinarith
      have h4 : ‖Xt k - Xex (k + 1)‖ ≤ b * ‖X k - Xex k‖ + 2 * Ck := by
        have e1 : (1 - q) * ‖Xt k - Xex (k + 1)‖ ≤
            (1 - q) * (b * ‖X k - Xex k‖ + 2 * Ck) := by
          have : (1 - q) * b = 1 + q := by rw [hb]; field_simp
          have e0 : (1 - q) * (b * ‖X k - Xex k‖) = (1 + q) * ‖X k - Xex k‖ := by
            rw [← mul_assoc, this]
          have e4 := mul_le_mul_of_nonneg_right hq hC0
          rw [mul_add, e0]
          nlinarith
        exact le_of_mul_le_mul_left e1 hpos
      have h5 : ‖X (k + 1) - Xex (k + 1)‖ ≤ ‖X (k + 1) - Xt k‖ + ‖Xt k - Xex (k + 1)‖ := by
        simpa using norm_add_le (X (k + 1) - Xt k) (Xt k - Xex (k + 1))
      have h6 := htr k hk
      change ‖X (k + 1) - Xex (k + 1)‖ ≤ b * (‖X k - Xex k‖ + (2 * Ck + ε₂))
      have h7 : 0 ≤ 2 * Ck + ε₂ := by positivity
      nlinarith)
  intro k hk
  have h1 := key k hk
  rw [max_eq_right hb1] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (add_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => hc0 i)))
  rw [show 4 * q * k = k * (4 * q) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (one_add_div_one_sub_le_exp hq0 (by linarith)) k

/-- **Theorem 4.2, eq. (4.5), conditional** (arXiv 2410.07465, p. 9): if every per-step term of
`convergence_conditional` is at most `c Δt²` (`hlocal`; in the paper `δ (2 + a) = O(Δt²)` by
`residual_const_le_of_mesh`, the exact solution is bounded, `δ = O(h³)`, `ε₂ = O(Δt²)`, and
`τ = O(Δt²)` is the unproved local truncation bound `hcons`), `δ (2 + a) ≤ K Δt` and `N Δt ≤ T`,
then `‖Xᵏ - X(tₖ)‖ ≤ exp ((2 α + 4 K) T) (‖X⁰ - X(t₀)‖ + c T Δt)`.  With
`‖X⁰ - X(t₀)‖ = O(Δt)` this is (4.5), `‖Xⁿ - X(tⁿ)‖ ≤ C Δt`.  (The paper's initial condition
reads `‖Xⁿ - X(tⁿ)‖ ≤ C h`, an index typo for `n = 0`.) -/
theorem convergence_conditional_order {A : Fin s → Matrix m m ℝ} {B : Fin s → Matrix n n ℝ}
    {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : ∀ t X, F t X = ∑ j, A j * X * (B j)ᵀ + G t) {α Δt δ a τ ε₂ K T c : ℝ}
    (hos : IsOneSidedLipschitzField F α) (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hδ : 0 ≤ δ)
    (ha0 : 0 ≤ a) (ha : ∀ Y : Matrix m n ℝ, ‖Y - (Δt / 2) • ∑ j, A j * Y * (B j)ᵀ‖ ≤ a * ‖Y‖)
    (hq : Δt * α / 2 + δ * (2 + a) ≤ 1 / 2) (hτ : 0 ≤ τ) (hε₂ : 0 ≤ ε₂) (hK0 : 0 ≤ K)
    (hK : δ * (2 + a) ≤ K * Δt) (hc : 0 ≤ c) {N : ℕ} (hT : N * Δt ≤ T)
    {X Xt Xex : ℕ → Matrix m n ℝ} {t : ℕ → ℝ}
    (hconv : ∀ k < N, ‖Xt k - X k - Δt • F (t k) ((1 / 2 : ℝ) • (X k + Xt k))‖ ≤
      δ * (a * ‖Xt k‖ + ‖X k + (Δt / 2) • ∑ j, A j * X k * (B j)ᵀ + Δt • G (t k)‖))
    (htr : ∀ k < N, ‖X (k + 1) - Xt k‖ ≤ ε₂)
    (hcons : ∀ k < N, ‖Xex (k + 1) - Xex k -
      Δt • F (t k) ((1 / 2 : ℝ) • (Xex k + Xex (k + 1)))‖ ≤ τ)
    (hlocal : ∀ k < N, 2 * (δ * (2 + a) * (‖Xex k‖ + ‖Xex (k + 1)‖) +
      δ * Δt * ‖G (t k)‖ + τ) + ε₂ ≤ c * Δt ^ 2) :
    ∀ k ≤ N, ‖X k - Xex k‖ ≤ Real.exp ((2 * α + 4 * K) * T) * (‖X 0 - Xex 0‖ + c * T * Δt) := by
  intro k hk
  have h1 := convergence_conditional hF hos hα hΔt hδ ha0 ha hq hτ hε₂ hconv htr hcons k hk
  have hsum : ∑ i ∈ range k, (2 * (δ * (2 + a) * (‖Xex i‖ + ‖Xex (i + 1)‖) +
      δ * Δt * ‖G (t i)‖ + τ) + ε₂) ≤ c * T * Δt := by
    refine (Finset.sum_le_sum fun i hi =>
      hlocal i ((Finset.mem_range.1 hi).trans_le hk)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hkN : (k : ℝ) * Δt ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔt).trans hT
    have : (k : ℝ) * (c * Δt ^ 2) = c * Δt * ((k : ℝ) * Δt) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hkN (mul_nonneg hc hΔt)
    linarith
  have hS : 0 ≤ ‖X 0 - Xex 0‖ + ∑ i ∈ range k, (2 * (δ * (2 + a) * (‖Xex i‖ + ‖Xex (i + 1)‖) +
      δ * Δt * ‖G (t i)‖ + τ) + ε₂) :=
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => by positivity)
  calc ‖X k - Xex k‖ ≤ _ := h1
    _ ≤ Real.exp ((2 * α + 4 * K) * T) * (‖X 0 - Xex 0‖ +
        ∑ i ∈ range k, (2 * (δ * (2 + a) * (‖Xex i‖ + ‖Xex (i + 1)‖) +
          δ * Δt * ‖G (t i)‖ + τ) + ε₂)) :=
      mul_le_mul_of_nonneg_right (exp_step_le hα hΔt hK0 hK hk hT) hS
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

/-- Non-vacuity of `convergence_conditional`: the hypotheses hold for the zero problem and zero
iterates (the hypotheses of the stability theorems are realized with nonzero data in
`stability_counterexample_instance`). -/
example (N : ℕ) :
    ∀ k ≤ N, ‖(0 : Matrix m n ℝ) - 0‖ ≤ Real.exp (4 * (0 * 0 / 2 + 0 * (2 + 1)) * k) *
      (‖(0 : Matrix m n ℝ) - 0‖ + ∑ _i ∈ range k, (2 * (0 * (2 + 1) *
        (‖(0 : Matrix m n ℝ)‖ + ‖(0 : Matrix m n ℝ)‖) + 0 * 0 * ‖(0 : Matrix m n ℝ)‖ + 0) + 0)) :=
  convergence_conditional (s := s) (A := fun _ => 0) (B := fun _ => 0) (G := fun _ => 0)
    (F := fun _ _ => 0) (X := fun _ => 0) (Xt := fun _ => 0) (Xex := fun _ => 0)
    (t := fun _ => 0) (α := 0) (Δt := 0) (δ := 0) (a := 1) (τ := 0) (ε₂ := 0)
    (fun _ _ => by simp) (fun _ _ _ => by simp) le_rfl le_rfl le_rfl zero_le_one
    (fun Y => by simp) (by norm_num) le_rfl le_rfl (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => by simp)

end Midpoint

end LeanDLRA.Literature.P2410_07465
