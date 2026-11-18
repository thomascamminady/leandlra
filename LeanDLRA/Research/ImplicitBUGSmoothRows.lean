import LeanDLRA.Research.ImplicitBUGStiffLemmas

/-!
# The implicit BUG integrator with a stiff row operator: smooth reference rows

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary: the matrix
`N = -CᵀC` acting on the rows is symmetric negative semidefinite of any norm (the stiffness). This
file compares the fixed-rank BUG integrator with backward Euler substeps (exact capture, no
truncation) with a reference whose rows are smooth but need not lie in the kernel of `N`: a
sequence with `X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j` (backward Euler steps of the full
problem up to defects `δ_j`) and `‖X_j CᵀC‖ ≤ κ`. With `e_j = Y_j - X_j` and
`Ψ_j = √(‖e_j‖² + h ‖e_j Cᵀ‖²)` (the error with its stiff energy), for `h μ ≤ 1/2`,

  `(1 - h μ) Ψ₁ ≤ (1 + 6 h μ) (‖e₀‖ + ‖δ‖) +`
  `    h μ (min(‖Y₀‖, √h ‖e₀ Cᵀ‖ / 2 + h ‖X₀ CᵀC‖) + 6 h ‖X₁ CᵀC‖ + 3 ‖X₁ - X₀‖)`     (one step),

and along a run with `h μ ≤ 1/8`, `‖X_{j+1} - X_j‖ ≤ h ω`, `‖δ_j‖ ≤ d`,

  `‖Y_N - X_N‖ ≤ (1 + 9 h μ)^N (‖Y₀ - X₀‖ + 2 h μ ‖Y₀‖ + N (2 d + 2 h μ h (7 κ + 3 ω)))`.

Neither `C` nor the singular values of the numerical solution enter, and the rank is arbitrary.
Every loss of a step carries the factor `h μ` and is bounded by the current error with its stiff
energy, by `h ‖X CᵀC‖` and by `‖X₁ - X₀‖`; no summability of energies is needed.

## Main results

* `IsMatrixImplicitBUGStep.sqrt_sq_norm_sub_add_le_of_sylvester`: the step inequality.
* `sqrt_sq_norm_implicitBUG_run_sub_add_le_of_sylvester`: the run bound for the error with its
  stiff energy.
* `norm_implicitBUG_run_sub_le_of_sylvester_of_norm_mul_gram_le`: the run bound.
* `norm_implicitBUG_run_sub_backwardEuler_le_of_sylvester`: the run bound against the backward
  Euler steps of the full problem, in terms of `‖X₀‖` and `‖X₀ CᵀC‖` only.

## Implementation notes

The proofs work with the orthogonal projectors `P₀ = U₀ U₀ᵀ`, `P₁ = U₁ U₁ᵀ`, `Q₀`, `Q₁` and the
matrices `Y_K = K₁ V₀ᵀ`, `Y_L = U₀ L₁ᵀ`, `Y₁ = U₁ S₁ V₁ᵀ`. With the Galerkin resolvent `Ξ` of the
new column space, `Ξ - h P₁ M Ξ = P₁ (1 - h P₀ M)`, and `D = Y₁ - Ξ Y_L`, the residual of the step
in the backward Euler equation of the full problem is

  `Y₁ - h M Y₁ + h Y₁ CᵀC - Y₀ = D - h P₁ M D + h (1 - P₁) M (Y_K - Y₁) + h D CᵀC`
  `    + h (Ξ - P₁) Y_L CᵀC`,

and the error equation is tested with the error. The stiff term `Λ = h Y_K CᵀC Q₀` of the K-step
solves the K-step equation with the right-hand side `h Y₀ CᵀC Q₀`, which gives
`‖Λ‖ ≤ √h ‖(Y₀ - X₀) Cᵀ‖ / 2 + h ‖X₀ CᵀC‖` for every matrix `X₀`: no inverse of the matrix of
singular values appears. The L-step is compared with `P₀ X₁` by its energy estimate.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA

open ImplicitBUGStiffLemmas

section Step

variable {m n k k₁ k₂ : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k₁] [Fintype k₂]
  [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {ε t₁ h μ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ X₀ X₁ δ : Matrix m n ℝ}

/-- **The step inequality against a reference with smooth rows.** Let `F(Z) = M Z - Z CᵀC` with
`M` dissipative and bounded by `μ`, `h μ ≤ 1/2`, and let `X₁ - h M X₁ + h X₁ CᵀC = X₀ + δ` (a
backward Euler step of the full problem with defect `δ`; the rows of `X` need not lie in the
kernel of `CᵀC`, and no rank condition on `X` is needed). For a step `Y₀ = U₀ S₀ V₀ᵀ → Y₁` with
exact capture and without truncation, of any rank, and `e_i = Y_i - X_i`,

  `(1 - h μ) √(‖e₁‖² + h ‖e₁ Cᵀ‖²) ≤ (1 + 6 h μ) (‖e₀‖ + ‖δ‖) +`
  `    h μ (min(‖Y₀‖, √h ‖e₀ Cᵀ‖ / 2 + h ‖X₀ CᵀC‖) + 6 h ‖X₁ CᵀC‖ + 3 ‖X₁ - X₀‖)`.

The matrix `C` enters only through the stiff energy of the error and through `‖X CᵀC‖`, and the
singular values of `S₀` do not enter. -/
theorem IsMatrixImplicitBUGStep.sqrt_sq_norm_sub_add_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 0
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 2) (hX : X₁ - h • (M * X₁) + h • (X₁ * (Cᵀ * C)) = X₀ + δ) :
    (1 - h * μ) * √(‖Y₁ - X₁‖ ^ 2 + h * ‖(Y₁ - X₁) * Cᵀ‖ ^ 2) ≤
      (1 + 6 * (h * μ)) * (‖U₀ * S₀ * V₀ᵀ - X₀‖ + ‖δ‖) +
        h * μ * (min ‖U₀ * S₀ * V₀ᵀ‖
          (√h * ‖(U₀ * S₀ * V₀ᵀ - X₀) * Cᵀ‖ / 2 + h * ‖X₀ * (Cᵀ * C)‖) +
          6 * (h * ‖X₁ * (Cᵀ * C)‖) + 3 * ‖X₁ - X₀‖) := by
  rw [sub_eq_zero.1 (norm_le_zero_iff.1 hs.trunc)]
  exact hs.sqrt_sq_norm_galerkin_sub_add_le_of_sylvester hdiss hμ0 hμ hh hhμ hX X₀

end Step

section Run

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  {r N : ℕ} {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ κ ω d : ℝ} {ε t : ℕ → ℝ}
  {U K : ℕ → Matrix m (Fin r) ℝ} {L V : ℕ → Matrix n (Fin r) ℝ}
  {S : ℕ → Matrix (Fin r) (Fin r) ℝ} {Y X δ : ℕ → Matrix m n ℝ}

/-- **Run bound for the error with its stiff energy, uniform in the stiffness and in the singular
values.** Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, `h μ ≤ 1/8`, and let
`X_j` be a reference with `X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`, `‖δ_j‖ ≤ d`,
`‖X_j CᵀC‖ ≤ κ` and `‖X_{j+1} - X_j‖ ≤ h ω`. For `N ≥ 1` steps of the rank-`r` integrator with
backward Euler substeps (exact capture, no truncation), `Y_j = U_j S_j V_jᵀ`, `e_j = Y_j - X_j`,

  `√(‖e_N‖² + h ‖e_N Cᵀ‖²) ≤ (1 + 9 h μ)^N (‖e₀‖ + 2 h μ ‖Y₀‖ + N (2 d + 2 h μ h (7 κ + 3 ω)))`.

The term `2 h μ ‖Y₀‖` is the loss of the first step from a start value of any stiff energy. -/
theorem sqrt_sq_norm_implicitBUG_run_sub_add_le_of_sylvester
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep
      (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) (ε j) 0 0 (t j) h (U j) (S j) (V j)
      (K j) (L j) (U (j + 1)) (V (j + 1)) (S (j + 1)) (Y j))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 8)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hκ : ∀ j ≤ N, ‖X j * (Cᵀ * C)‖ ≤ κ) (hω : ∀ j < N, ‖X (j + 1) - X j‖ ≤ h * ω)
    (hδ : ∀ j < N, ‖δ j‖ ≤ d) (hN : 0 < N) :
    √(‖U N * S N * (V N)ᵀ - X N‖ ^ 2 + h * ‖(U N * S N * (V N)ᵀ - X N) * Cᵀ‖ ^ 2) ≤
      (1 + 9 * (h * μ)) ^ N * (‖U 0 * S 0 * (V 0)ᵀ - X 0‖ + 2 * (h * μ) * ‖U 0 * S 0 * (V 0)ᵀ‖ +
        N * (2 * d + 2 * (h * μ) * (h * (7 * κ + 3 * ω)))) := by
  obtain ⟨η, hη⟩ : ∃ η, η = h * μ := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hη]; exact mul_nonneg hh.le hμ0
  rw [← hη] at hhμ ⊢
  have hκ0 : 0 ≤ κ := (norm_nonneg (X 0 * (Cᵀ * C))).trans (hκ 0 (Nat.zero_le N))
  have hω0 : 0 ≤ ω := by
    have := (norm_nonneg (X (0 + 1) - X 0)).trans (hω 0 hN)
    exact (mul_nonneg_iff_of_pos_left hh).1 this
  have hd0 : 0 ≤ d := (norm_nonneg (δ 0)).trans (hδ 0 hN)
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, Ψ = fun j => √(‖U j * S j * (V j)ᵀ - X j‖ ^ 2 +
      h * ‖(U j * S j * (V j)ᵀ - X j) * Cᵀ‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * d + 2 * η * (h * (7 * κ + 3 * ω)) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ‖U 0 * S 0 * (V 0)ᵀ - X 0‖ + 2 * η * ‖U 0 * S 0 * (V 0)ᵀ‖ :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hYeq : ∀ j < N, Y j = U (j + 1) * S (j + 1) * (V (j + 1))ᵀ := fun j hj =>
    sub_eq_zero.1 (norm_le_zero_iff.1 (hstep j hj).trunc)
  have hΨe : ∀ j, ‖U j * S j * (V j)ᵀ - X j‖ ≤ Ψ j := fun j => by
    have := le_sqrt_sq_add_sq_left (c := √h * ‖(U j * S j * (V j)ᵀ - X j) * Cᵀ‖)
      (norm_nonneg (U j * S j * (V j)ᵀ - X j))
    rw [mul_pow, hs2] at this
    rw [hΨ]; exact this
  have hΨE : ∀ j, √h * ‖(U j * S j * (V j)ᵀ - X j) * Cᵀ‖ ≤ Ψ j := fun j => by
    have := le_sqrt_sq_add_sq_right (d := ‖U j * S j * (V j)ᵀ - X j‖)
      (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg ((U j * S j * (V j)ᵀ - X j) * Cᵀ)))
    rw [mul_pow, hs2] at this
    rw [hΨ]; exact this
  -- one step, with the bounds of the reference
  have hI : ∀ j < N, (1 - η) * Ψ (j + 1) ≤
      (1 + 6 * η) * (‖U j * S j * (V j)ᵀ - X j‖ + d) +
        η * (min ‖U j * S j * (V j)ᵀ‖
          (√h * ‖(U j * S j * (V j)ᵀ - X j) * Cᵀ‖ / 2 + h * κ) + 6 * (h * κ) + 3 * (h * ω)) := by
    intro j hj
    have h1 := (hstep j hj).sqrt_sq_norm_sub_add_le_of_sylvester hdiss hμ0 hμ hh
      (by rw [← hη]; linarith) (hX j hj)
    rw [hYeq j hj, ← hη] at h1
    have k0 := mul_le_mul_of_nonneg_left (hκ j (Nat.le_of_lt hj)) hh.le
    have k1 := mul_le_mul_of_nonneg_left (hκ (j + 1) hj) hh.le
    have m1 : min ‖U j * S j * (V j)ᵀ‖ (√h * ‖(U j * S j * (V j)ᵀ - X j) * Cᵀ‖ / 2 +
        h * ‖X j * (Cᵀ * C)‖) ≤ min ‖U j * S j * (V j)ᵀ‖
        (√h * ‖(U j * S j * (V j)ᵀ - X j) * Cᵀ‖ / 2 + h * κ) :=
      min_le_min le_rfl (by linarith)
    have a1 := mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖U j * S j * (V j)ᵀ - X j‖)
      (hδ j hj)) (by linarith : (0 : ℝ) ≤ 1 + 6 * η)
    have a2 := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add m1 (mul_le_mul_of_nonneg_left k1 (by norm_num : (0 : ℝ) ≤ 6)))
        (mul_le_mul_of_nonneg_left (hω j hj) (by norm_num : (0 : ℝ) ≤ 3))) hη0
    rw [hΨ]
    exact h1.trans (add_le_add a1 a2)
  have hpos : 0 < 1 - η := by linarith
  have key : ∀ n : ℕ, n + 1 ≤ N → Ψ (n + 1) ≤ (1 + 9 * η) ^ (n + 1) * (A + ((n : ℝ) + 1) * c) := by
    intro n
    induction n with
    | zero =>
      intro hn
      have h1 := hI 0 hn
      have m1 := mul_le_mul_of_nonneg_left (min_le_left ‖U 0 * S 0 * (V 0)ᵀ‖
        (√h * ‖(U 0 * S 0 * (V 0)ᵀ - X 0) * Cᵀ‖ / 2 + h * κ)) hη0
      obtain ⟨e0, he0⟩ : ∃ e0, e0 = ‖U 0 * S 0 * (V 0)ᵀ - X 0‖ := ⟨_, rfl⟩
      obtain ⟨y0, hy0⟩ : ∃ y0, y0 = ‖U 0 * S 0 * (V 0)ᵀ‖ := ⟨_, rfl⟩
      have he00 : 0 ≤ e0 := by rw [he0]; exact norm_nonneg _
      have hy00 : 0 ≤ y0 := by rw [hy0]; exact norm_nonneg _
      rw [← he0] at h1 hA
      rw [← hy0] at h1 m1 hA
      have hφ : 1 + 6 * η ≤ (1 - η) * (1 + 9 * η) := by nlinarith
      have hAc : 0 ≤ A + c := add_nonneg hA0 hc0
      have t1 := mul_le_mul_of_nonneg_right hφ hAc
      have goal' : (1 - η) * Ψ (0 + 1) ≤ (1 - η) * ((1 + 9 * η) * (A + c)) := by
        rw [← mul_assoc]
        refine le_trans ?_ t1
        rw [hA, hc]
        nlinarith [mul_nonneg hη0 hy00, mul_nonneg (mul_nonneg hη0 hη0) hy00,
          mul_nonneg hη0 (mul_nonneg hh.le hκ0), mul_nonneg hη0 (mul_nonneg hh.le hω0),
          mul_nonneg (mul_nonneg hη0 hη0) (mul_nonneg hh.le hκ0),
          mul_nonneg (mul_nonneg hη0 hη0) (mul_nonneg hh.le hω0), mul_nonneg hη0 hd0]
      have := le_of_mul_le_mul_left goal' hpos
      simpa using this
    | succ n ih =>
      intro hn
      have ih' := ih (Nat.le_of_succ_le hn)
      have h1 := hI (n + 1) hn
      have m1 := mul_le_mul_of_nonneg_left (min_le_right ‖U (n + 1) * S (n + 1) * (V (n + 1))ᵀ‖
        (√h * ‖(U (n + 1) * S (n + 1) * (V (n + 1))ᵀ - X (n + 1)) * Cᵀ‖ / 2 + h * κ)) hη0
      have e1 := hΨe (n + 1)
      have e2 := hΨE (n + 1)
      obtain ⟨G, hG⟩ : ∃ G, G = (1 + 9 * η) ^ (n + 1) := ⟨_, rfl⟩
      have hG1 : 1 ≤ G := by rw [hG]; exact one_le_pow₀ (by linarith)
      obtain ⟨B, hB⟩ : ∃ B, B = G * (A + ((n : ℝ) + 1) * c) := ⟨_, rfl⟩
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      rw [← hG, ← hB] at ih'
      have hφ : 1 + 13 / 2 * η ≤ (1 - η) * (1 + 9 * η) := by nlinarith
      have t1 := mul_le_mul_of_nonneg_right hφ hB0
      have t2 := mul_le_mul_of_nonneg_right hG1 hc0
      have t3 := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ (1 - η) * (1 + 9 * η))
        (mul_nonneg (by linarith : (0 : ℝ) ≤ G) hc0)
      have hc1 : (1 + 6 * η) * d + η * (7 * (h * κ) + 3 * (h * ω)) ≤ c := by
        rw [hc]
        nlinarith [mul_le_mul_of_nonneg_right hhμ hd0, mul_nonneg hη0 (mul_nonneg hh.le hκ0),
          mul_nonneg hη0 (mul_nonneg hh.le hω0)]
      have eR : (1 - η) * ((1 + 9 * η) ^ (n + 1 + 1) * (A + (((n + 1 : ℕ) : ℝ) + 1) * c)) =
          (1 - η) * (1 + 9 * η) * B + (1 - η) * (1 + 9 * η) * (G * c) := by
        rw [hB, hG, pow_succ]; push_cast; ring
      have goal' : (1 - η) * Ψ (n + 1 + 1) ≤
          (1 - η) * ((1 + 9 * η) ^ (n + 1 + 1) * (A + (((n + 1 : ℕ) : ℝ) + 1) * c)) := by
        rw [eR]
        have u1 := mul_le_mul_of_nonneg_left (e1.trans ih') (by linarith : (0 : ℝ) ≤ 1 + 6 * η)
        have u2 := mul_le_mul_of_nonneg_left (e2.trans ih') hη0
        linarith
      exact le_of_mul_le_mul_left goal' hpos
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := key n le_rfl
  rw [hΨ, hA, hc] at this
  simpa using this

/-- **Run bound against a reference with smooth rows, uniform in the stiffness and in the
singular values.** Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, `h μ ≤ 1/8`,
and let `X_j` be a reference with `X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`,
`‖δ_j‖ ≤ d`, `‖X_j CᵀC‖ ≤ κ` and `‖X_{j+1} - X_j‖ ≤ h ω`; the rows of the reference need not lie
in the kernel of `CᵀC`. For `N` steps of the rank-`r` integrator with backward Euler substeps
(exact capture, no truncation), `Y_j = U_j S_j V_jᵀ`,

  `‖Y_N - X_N‖ ≤ (1 + 9 h μ)^N (‖Y₀ - X₀‖ + 2 h μ ‖Y₀‖ + N (2 d + 2 h μ h (7 κ + 3 ω)))`.

With `N h = T` this is `e^{9 μ T} (‖Y₀ - X₀‖ + 2 h μ ‖Y₀‖ + 2 T d / h + 2 μ T h (7 κ + 3 ω))`.
The matrix `C` enters only through `κ`, and the singular values of the `S_j` do not enter. -/
theorem norm_implicitBUG_run_sub_le_of_sylvester_of_norm_mul_gram_le
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep
      (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) (ε j) 0 0 (t j) h (U j) (S j) (V j)
      (K j) (L j) (U (j + 1)) (V (j + 1)) (S (j + 1)) (Y j))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 8)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hκ : ∀ j ≤ N, ‖X j * (Cᵀ * C)‖ ≤ κ) (hω : ∀ j < N, ‖X (j + 1) - X j‖ ≤ h * ω)
    (hδ : ∀ j < N, ‖δ j‖ ≤ d) :
    ‖U N * S N * (V N)ᵀ - X N‖ ≤
      (1 + 9 * (h * μ)) ^ N * (‖U 0 * S 0 * (V 0)ᵀ - X 0‖ + 2 * (h * μ) * ‖U 0 * S 0 * (V 0)ᵀ‖ +
        N * (2 * d + 2 * (h * μ) * (h * (7 * κ + 3 * ω)))) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    rw [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
    linarith [mul_nonneg (mul_nonneg zero_le_two (mul_nonneg hh.le hμ0))
      (norm_nonneg (U 0 * S 0 * (V 0)ᵀ))]
  · have h1 := sqrt_sq_norm_implicitBUG_run_sub_add_le_of_sylvester hstep hdiss hμ0 hμ hh hhμ hX
      hκ hω hδ hN
    have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
    have h2 := le_sqrt_sq_add_sq_left (c := √h * ‖(U N * S N * (V N)ᵀ - X N) * Cᵀ‖)
      (norm_nonneg (U N * S N * (V N)ᵀ - X N))
    rw [mul_pow, hs2] at h2
    exact h2.trans h1

/-- **Run bound against the backward Euler steps of the full problem.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, `h μ ≤ 1/8`, and let
`X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j` (backward Euler for the full matrix equation, from
any `X₀`). For `N` steps of the rank-`r` integrator with backward Euler substeps (exact capture,
no truncation), `Y_j = U_j S_j V_jᵀ`,

  `‖Y_N - X_N‖ ≤ (1 + 9 h μ)^N (‖Y₀ - X₀‖ + 2 h μ ‖Y₀‖ + 2 N h μ h (10 ‖X₀ CᵀC‖ + 3 μ ‖X₀‖))`.

Only `‖X₀‖` and `‖X₀ CᵀC‖` (the start value of the reference and its smoothness along the rows)
enter: neither `C` itself, nor the singular values, nor the rank. -/
theorem norm_implicitBUG_run_sub_backwardEuler_le_of_sylvester
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep
      (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) (ε j) 0 0 (t j) h (U j) (S j) (V j)
      (K j) (L j) (U (j + 1)) (V (j + 1)) (S (j + 1)) (Y j))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 8)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j) :
    ‖U N * S N * (V N)ᵀ - X N‖ ≤
      (1 + 9 * (h * μ)) ^ N * (‖U 0 * S 0 * (V 0)ᵀ - X 0‖ + 2 * (h * μ) * ‖U 0 * S 0 * (V 0)ᵀ‖ +
        N * (2 * (h * μ) * (h * (10 * ‖X 0 * (Cᵀ * C)‖ + 3 * (μ * ‖X 0‖))))) := by
  have hb : ∀ j, j ≤ N → ‖X j * (Cᵀ * C)‖ ≤ ‖X 0 * (Cᵀ * C)‖ ∧ ‖X j‖ ≤ ‖X 0‖ := by
    intro j
    induction j with
    | zero => intro _; exact ⟨le_rfl, le_rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2⟩ := ih (Nat.le_of_succ_le hj)
      have e1 := congrArg (fun A => A * (Cᵀ * C)) (hX j hj)
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.mul_assoc M] at e1
      exact ⟨(norm_le_of_backwardEuler hdiss hh.le e1).trans i1,
        (norm_le_of_backwardEuler hdiss hh.le (hX j hj)).trans i2⟩
  have hω : ∀ j < N, ‖X (j + 1) - X j‖ ≤ h * (μ * ‖X 0‖ + ‖X 0 * (Cᵀ * C)‖) := by
    intro j hj
    obtain ⟨i1, i2⟩ := hb (j + 1) hj
    have e1 : X (j + 1) - X j = h • (M * X (j + 1)) - h • (X (j + 1) * (Cᵀ * C)) := by
      rw [← hX j hj]; abel
    have n1 : ‖h • (M * X (j + 1))‖ ≤ h * (μ * ‖X 0‖) := by
      rw [norm_smul, Real.norm_of_nonneg hh.le]
      exact mul_le_mul_of_nonneg_left ((norm_mul_le_mul_norm hμ0 hμ (X (j + 1))).trans
        (mul_le_mul_of_nonneg_left i2 hμ0)) hh.le
    have n2 : ‖h • (X (j + 1) * (Cᵀ * C))‖ ≤ h * ‖X 0 * (Cᵀ * C)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hh.le]
      exact mul_le_mul_of_nonneg_left i1 hh.le
    have := norm_sub_le (h • (M * X (j + 1))) (h • (X (j + 1) * (Cᵀ * C)))
    rw [e1]; linarith
  have hX' : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) =
      X j + (fun _ : ℕ => (0 : Matrix m n ℝ)) j := fun j hj => by rw [hX j hj, add_zero]
  have := norm_implicitBUG_run_sub_le_of_sylvester_of_norm_mul_gram_le hstep hdiss hμ0 hμ hh hhμ
    hX' (fun j hj => (hb j hj).1) hω (d := 0) (fun _ _ => by simp)
  refine this.trans (le_of_eq ?_)
  ring

end Run

/-! ### Non-vacuity -/

section Example

/-- The hypotheses of the step inequality hold for a family of `2 × 2` steps of rank `1` with an
arbitrary stiffness `lam > 0` and a reference whose rows are not in the kernel of the stiff
matrix: `M = diag(0, -1)`, `C = (0, √lam)` (so `-CᵀC = diag(0, -lam)`), `μ = 1`, start value
`(3/5, 4/5)ᵀ (c, s)`, reference `X₀ = e₁ (1, 1)`, `X₁ = e₁ (1, 1 / (1 + h lam))` (a backward Euler
step of the full problem, `X₁ CᵀC ≠ 0`); a step exists for every `h ∈ (0, 1/2]`. -/
example {h lam c s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hlam : 0 < lam)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ (Y₁ X₁ : Matrix (Fin 2) (Fin 2) ℝ),
      X₁ * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam]) ≠ 0 ∧
      (1 - h * 1) * √(‖Y₁ - X₁‖ ^ 2 +
        h * ‖(Y₁ - X₁) * (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ‖ ^ 2) ≤
        (1 + 6 * (h * 1)) *
          (‖(!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
            (!![c; s] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ - !![1, 1; 0, 0]‖ +
            ‖(0 : Matrix (Fin 2) (Fin 2) ℝ)‖) +
          h * 1 * (min ‖(!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
              (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![c; s] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ‖
            (√h * ‖((!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
              (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![c; s] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ -
                !![1, 1; 0, 0]) * (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ‖ / 2 +
              h * ‖(!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
                ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam])‖) +
            6 * (h * ‖X₁ * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam])‖) +
            3 * ‖X₁ - !![1, 1; 0, 0]‖) := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ :=
    StiffRowsExample.exists_isMatrixImplicitBUGStep hh.le hlam.le hcs 0
  have hC : (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam] = -!![0, 0; 0, -lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.mul_self_sqrt hlam.le]
  have hF : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      !![0, 0; 0, -1] * Z + Z * !![0, 0; 0, -lam]) = fun _ Z =>
      !![0, 0; 0, -1] * Z - Z * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam]) := by
    funext _ Z
    rw [hC, Matrix.mul_neg, sub_neg_eq_add]
  rw [hF] at hs
  have hdiss : ∀ x : Fin 2 → ℝ, x ⬝ᵥ (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ≤ 0 := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [mul_self_nonneg (x 1)]
  have hμ : ∀ x : Fin 2 → ℝ, (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ⬝ᵥ
      (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ≤ 1 ^ 2 * (x ⬝ᵥ x) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [mul_self_nonneg (x 0)]
  have hq : (1 : ℝ) + h * lam ≠ 0 := by positivity
  have hX : (!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
      h • (!![0, 0; 0, -1] * !![1, 1 / (1 + h * lam); 0, 0]) +
      h • (!![1, 1 / (1 + h * lam); 0, 0] *
        ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam])) =
      !![1, 1; 0, 0] + 0 := by
    rw [hC]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    field_simp
  refine ⟨Y₁, !![1, 1 / (1 + h * lam); 0, 0], ?_, ?_⟩
  · rw [hC]
    intro h0
    have e : ((!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        -!![0, 0; 0, -lam]) 0 1 = 1 / (1 + h * lam) * lam := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h0, Matrix.zero_apply] at e
    have : 0 < 1 / (1 + h * lam) * lam := by positivity
    linarith
  · exact hs.sqrt_sq_norm_sub_add_le_of_sylvester hdiss zero_le_one hμ hh (by simpa using hh1) hX

/-- The hypotheses of the run bounds hold with `N = 1` for the same family: a step of the
integrator and a backward Euler step of the full problem whose result has rows outside the
kernel of the stiff matrix. -/
example {h lam c s : ℝ} (hh : 0 < h) (hlam : 0 < lam) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ (ε t : ℕ → ℝ) (U K L V : ℕ → Matrix (Fin 2) (Fin 1) ℝ)
      (S : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (Y X : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ j < 1, IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        !![0, 0; 0, -1] * Z - Z * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam]))
        (ε j) 0 0 (t j) h (U j) (S j) (V j) (K j) (L j) (U (j + 1)) (V (j + 1)) (S (j + 1))
        (Y j)) ∧
      (∀ j < 1, X (j + 1) - h • (!![0, 0; 0, -1] * X (j + 1)) +
        h • (X (j + 1) * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam])) = X j) ∧
      X 1 * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam]) ≠ 0 := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ :=
    StiffRowsExample.exists_isMatrixImplicitBUGStep hh.le hlam.le hcs 0
  have hC : (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam] = -!![0, 0; 0, -lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.mul_self_sqrt hlam.le]
  have hF : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      !![0, 0; 0, -1] * Z + Z * !![0, 0; 0, -lam]) = fun _ Z =>
      !![0, 0; 0, -1] * Z - Z * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam]) := by
    funext _ Z
    rw [hC, Matrix.mul_neg, sub_neg_eq_add]
  rw [hF] at hs
  have hq : (1 : ℝ) + h * lam ≠ 0 := by positivity
  have hX : (!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
      h • (!![0, 0; 0, -1] * !![1, 1 / (1 + h * lam); 0, 0]) +
      h • (!![1, 1 / (1 + h * lam); 0, 0] *
        ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam])) = !![1, 1; 0, 0] := by
    rw [hC]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    field_simp
  refine ⟨fun _ => ε, fun _ => 0, fun j => if j = 0 then !![3 / 5; 4 / 5] else U₁, fun _ => K₁,
    fun _ => L₁, fun j => if j = 0 then !![c; s] else V₁, fun j => if j = 0 then 1 else S₁,
    fun _ => Y₁, fun j => if j = 0 then !![1, 1; 0, 0] else !![1, 1 / (1 + h * lam); 0, 0],
    ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact hs
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact hX
  · rw [hC]
    intro h0
    have e : ((!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        -!![0, 0; 0, -lam]) 0 1 = 1 / (1 + h * lam) * lam := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h0' : (!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        -!![0, 0; 0, -lam] = 0 := h0
    rw [h0', Matrix.zero_apply] at e
    have : 0 < 1 / (1 + h * lam) * lam := by positivity
    linarith

end Example

end LeanDLRA
