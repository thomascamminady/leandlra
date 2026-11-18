import LeanDLRA.Research.ImplicitBUGStiffLocal

/-!
# The implicit BUG integrator with a stiff row operator: run bounds with the factor one

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary. Backward Euler
of the full problem is linear and does not increase the Frobenius norm, so the error of any
sequence against a backward Euler reference is the start error plus the defects plus the sum of
the local errors: the start error enters with the factor one. For the BUG integrator with
backward Euler substeps the local error of a step is bounded by `h μ` times the stiff energy of
the start value of the step minus a free comparison matrix, which gives a bound that can be
evaluated along the run and, with the energy identity of backward Euler, a closed bound whose
growth factor is `(1 + c² (h μ)² / 16)^N`, `c = 27/4 + 2 h μ`, instead of an exponential in `μ t`.

## Main results

* `ImplicitBUGStiffSharpRun.norm_sub_le_add_sum_of_backwardEuler`: for any sequence `Y_j`,
  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑ (‖δ_j‖ + ‖Y_{j+1} - W_j‖)`, where `W_j` is the backward Euler step of
  the full problem from `Y_j`.
* `norm_implicitBUG_run_sub_le_add_sum_of_sylvester`: for a run of the integrator with any
  truncation, `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑ (‖δ_j‖ + ϑ_j + c h μ λ_j)` with
  `λ_j = min(‖Y_j‖, √h ‖(Y_j - Z_j) Cᵀ‖ / 2 + h ‖Z_j CᵀC‖)` for every sequence `Z_j`; no restriction
  on `h μ`.
* `norm_implicitBUG_run_sub_le_add_sum_of_resolvent`: the same with the local errors bounded by
  the stiff source of the S-step and the normal part of the K-step, computable from the factors.
* `norm_implicitBUG_truncated_run_sub_le_of_sylvester_of_sq`: for a run with truncation by
  projectors acting from the left, the closed bound in terms of `κ = sup ‖X_j CᵀC‖`.
* `norm_implicitBUG_truncated_run_sub_solution_le_of_sylvester_of_sq`: the same against an exact
  solution with a bounded second derivative.

## Implementation notes

The closed bound uses the functional `√(‖e‖² + 2 h ‖e Cᵀ‖²)` of the error before the truncation:
backward Euler maps the norm of its right-hand side to this functional, the local error is
bounded in it, and `‖e‖ + β √h ‖e Cᵀ‖ ≤ (1 + β²/4) √(‖e‖² + 2 h ‖e Cᵀ‖²)`.

## References

* [CerutiLubich2022], [CerutiKuschLubich2022] for the BUG integrator and its rank-adaptive
  variant; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas ImplicitBUGStiffLocal Curvature

namespace ImplicitBUGStiffSharpRun

/-- The triangle inequality for `√(x² + w y²)`. -/
theorem sqrt_sq_add_mul_sq_le {a b α β w x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hw : 0 ≤ w) (hx0 : 0 ≤ x) (hx : x ≤ a + b) (hy0 : 0 ≤ y) (hy : y ≤ α + β) :
    √(x ^ 2 + w * y ^ 2) ≤ √(a ^ 2 + w * α ^ 2) + √(b ^ 2 + w * β ^ 2) := by
  obtain ⟨s, hs⟩ : ∃ s, s = √w := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg w
  have hs2 : s ^ 2 = w := by rw [hs]; exact Real.sq_sqrt hw
  have e : ∀ u : ℝ, w * u ^ 2 = (s * u) ^ 2 := fun u => by rw [mul_pow, hs2]
  rw [e y, e α, e β]
  have cs := mul_add_mul_le_sqrt_mul_sqrt ha (mul_nonneg hs0 hα) hb (mul_nonneg hs0 hβ)
  have qA : √(a ^ 2 + (s * α) ^ 2) ^ 2 = a ^ 2 + (s * α) ^ 2 := Real.sq_sqrt (by positivity)
  have qB : √(b ^ 2 + (s * β) ^ 2) ^ 2 = b ^ 2 + (s * β) ^ 2 := Real.sq_sqrt (by positivity)
  have hx2 : x ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hy2 : (s * y) ^ 2 ≤ (s * α + s * β) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hs0 hy0) (by nlinarith) 2
  refine Real.sqrt_le_iff.2 ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith

/-- `n + β e ≤ (1 + β²/4) √(n² + 2 e²)`: the price of a loss proportional to the square root of
the stiff energy. -/
theorem add_mul_le_mul_sqrt {n e β : ℝ} (hn : 0 ≤ n) (he : 0 ≤ e) (hβ : 0 ≤ β) :
    n + β * e ≤ (1 + β ^ 2 / 4) * √(n ^ 2 + 2 * e ^ 2) := by
  have hΦ : √(n ^ 2 + 2 * e ^ 2) ^ 2 = n ^ 2 + 2 * e ^ 2 := Real.sq_sqrt (by positivity)
  have key : (n + β * e) ^ 2 ≤ ((1 + β ^ 2 / 4) * √(n ^ 2 + 2 * e ^ 2)) ^ 2 := by
    rw [mul_pow, hΦ]
    nlinarith [sq_nonneg (β * n - 2 * e), sq_nonneg β,
      mul_nonneg (sq_nonneg (β ^ 2)) (by positivity : (0 : ℝ) ≤ n ^ 2 + 2 * e ^ 2)]
  have := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at this

section Abstract

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] {M : Matrix m m ℝ}
  {C : Matrix k n ℝ} {h : ℝ}

/-- The triangle inequality for the functional `√(‖A‖² + 2 h ‖A Cᵀ‖²)`. -/
theorem sqrt_sq_norm_add_add_le (hh : 0 ≤ h) (A B : Matrix m n ℝ) :
    √(‖A + B‖ ^ 2 + 2 * (h * ‖(A + B) * Cᵀ‖ ^ 2)) ≤
      √(‖A‖ ^ 2 + 2 * (h * ‖A * Cᵀ‖ ^ 2)) + √(‖B‖ ^ 2 + 2 * (h * ‖B * Cᵀ‖ ^ 2)) := by
  have hy : ‖(A + B) * Cᵀ‖ ≤ ‖A * Cᵀ‖ + ‖B * Cᵀ‖ := by
    rw [Matrix.add_mul]; exact norm_add_le _ _
  have := sqrt_sq_add_mul_sq_le (w := 2 * h) (norm_nonneg A) (norm_nonneg B)
    (norm_nonneg (A * Cᵀ)) (norm_nonneg (B * Cᵀ)) (by positivity) (norm_nonneg (A + B))
    (norm_add_le A B) (norm_nonneg ((A + B) * Cᵀ)) hy
  simpa only [mul_assoc] using this

/-- **Error of any sequence against a backward Euler reference: the factor one.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative, let `X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`
and let `W_j` be the backward Euler step of the full problem from `Y_j`. Then

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑_{j<N} (‖δ_j‖ + ‖Y_{j+1} - W_j‖)`.

The start error is not amplified, whatever the sequence `Y_j` is. -/
theorem norm_sub_le_add_sum_of_backwardEuler {N : ℕ} {Y W X δ : ℕ → Matrix m n ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤ ‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖δ j‖ + ‖Y (j + 1) - W j‖) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hW j (Nat.lt_succ_of_lt hj)) fun j hj => hX j (Nat.lt_succ_of_lt hj)
    have e : W n - X (n + 1) - h • (M * (W n - X (n + 1))) +
        h • ((W n - X (n + 1)) * (Cᵀ * C)) = Y n - (X n + δ n) := by
      rw [← hW n (Nat.lt_succ_self n), ← hX n (Nat.lt_succ_self n)]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    have n1 := norm_le_of_backwardEuler hdiss hh e
    have n2 : ‖Y n - (X n + δ n)‖ ≤ ‖Y n - X n‖ + ‖δ n‖ := by
      rw [← sub_sub]; exact norm_sub_le _ _
    have e3 : Y (n + 1) - X (n + 1) = Y (n + 1) - W n + (W n - X (n + 1)) := by abel
    have n3 := norm_add_le (Y (n + 1) - W n) (W n - X (n + 1))
    rw [← e3] at n3
    rw [Finset.sum_range_succ]
    linarith

end Abstract

end ImplicitBUGStiffSharpRun

open ImplicitBUGStiffSharpRun

section Run

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  {N : ℕ} {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ κ : ℝ} {ϑ : ℕ → ℝ}
  {T : ℕ → Matrix m m ℝ} {Y Yh X δ : ℕ → Matrix m n ℝ}

/-- **Run bound that can be evaluated along the run, with the factor one on the start error.**
Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, and let `X_j` be a reference with
`X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`. Let step `j` of the integrator with backward
Euler substeps start from `Y_j` (in any factorisation, of any rank), with exact capture by bases
of any size, and let `Y_{j+1}` differ from the result of the Galerkin step by at most `ϑ_j` (any
truncation). Then for every sequence of comparison matrices `Z_j`

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑_{j<N} (‖δ_j‖ + ϑ_j + (27/4 + 2 h μ) h μ λ_j)`,
  `λ_j = min(‖Y_j‖, √h ‖(Y_j - Z_j) Cᵀ‖ / 2 + h ‖Z_j CᵀC‖)`.

There is no restriction on `h μ`, no exponential factor, and the reference enters only through
its defects; with `Z_j = 0` or `Z_j = Y_j` the right-hand side is computable from the run. -/
theorem norm_implicitBUG_run_sub_le_add_sum_of_sylvester
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (Z : ℕ → Matrix m n ℝ) :
    ‖Y N - X N‖ ≤ ‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖δ j‖ + ϑ j +
      (27 / 4 + 2 * (h * μ)) * (h * μ) *
        min ‖Y j‖ (√h * ‖(Y j - Z j) * Cᵀ‖ / 2 + h * ‖Z j * (Cᵀ * C)‖)) := by
  choose W hW using fun j => exists_backwardEuler (C := C) hdiss hh.le (Y j)
  refine (norm_sub_le_add_sum_of_backwardEuler hdiss hh.le (fun j _ => hW j) hX).trans ?_
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
  have hjN : j < N := Finset.mem_range.1 hj
  obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, hY, hs⟩ := hstep j hjN
  have h1 := hs.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester hdiss hμ0 hμ hh
    (Yt := W j) (by rw [← hY]; exact hW j) (Z j)
  rw [← hY] at h1
  have h2 : ‖U₁ * S₁ * V₁ᵀ - W j‖ ≤
      √(‖U₁ * S₁ * V₁ᵀ - W j‖ ^ 2 + 2 * (h * ‖(U₁ * S₁ * V₁ᵀ - W j) * Cᵀ‖ ^ 2)) :=
    Real.le_sqrt_of_sq_le (by
      have : 0 ≤ 2 * (h * ‖(U₁ * S₁ * V₁ᵀ - W j) * Cᵀ‖ ^ 2) := by positivity
      linarith)
  have e : Y (j + 1) - W j = Y (j + 1) - U₁ * S₁ * V₁ᵀ + (U₁ * S₁ * V₁ᵀ - W j) := by abel
  have h3 := norm_add_le (Y (j + 1) - U₁ * S₁ * V₁ᵀ) (U₁ * S₁ * V₁ᵀ - W j)
  rw [← e] at h3
  have h4 := hs.trunc
  linarith

/-- **Run bound in terms of quantities of the steps, with the factor one on the start error.**
Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, and let `X_j` be a reference with
`X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`. Let step `j` of the integrator with backward
Euler substeps start from `Y_j`, with exact capture by bases of any size, and let `Y_{j+1}` differ
from the result `Ŷ_{j+1} = U₁ S₁ V₁ᵀ` of the Galerkin step by at most `ϑ_j`. If `b_j` bounds the
estimator of step `j`,

  `(2 + h μ) ‖h (Ξ - P₁) U₀ L₁ᵀ CᵀC‖ + ‖h (1 - P₁) M (K₁ V₀ᵀ - Ŷ_{j+1})‖ ≤ b_j`,

with `P₀ = U₀ U₀ᵀ`, `P₁ = U₁ U₁ᵀ` and the Galerkin resolvent `Ξ` of the new column space
(`P₁ Ξ = Ξ`, `Ξ - h P₁ M Ξ = P₁ (1 - h P₀ M)`), then

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑_{j<N} (‖δ_j‖ + ϑ_j + b_j)`.

The estimator is computable from the factors of the step; the reference enters only through its
defects. -/
theorem norm_implicitBUG_run_sub_le_add_sum_of_resolvent {b : ℕ → ℝ}
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)) ∧
        ∀ Ξ : Matrix m m ℝ, U₁ * U₁ᵀ * Ξ = Ξ →
          Ξ - h • (U₁ * U₁ᵀ * (M * Ξ)) = U₁ * U₁ᵀ * (1 - h • (U₀ * U₀ᵀ * M)) →
          (2 + h * μ) * ‖h • ((Ξ - U₁ * U₁ᵀ) * (U₀ * L₁ᵀ) * (Cᵀ * C))‖ +
            ‖h • (M * (K₁ * V₀ᵀ - U₁ * S₁ * V₁ᵀ) -
              U₁ * U₁ᵀ * (M * (K₁ * V₀ᵀ - U₁ * S₁ * V₁ᵀ)))‖ ≤ b j)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤ ‖Y 0 - X 0‖ + ∑ j ∈ range N, (‖δ j‖ + ϑ j + b j) := by
  choose W hW using fun j => exists_backwardEuler (C := C) hdiss hh.le (Y j)
  refine (norm_sub_le_add_sum_of_backwardEuler hdiss hh.le (fun j _ => hW j) hX).trans ?_
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
  have hjN : j < N := Finset.mem_range.1 hj
  obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, hY, hs, hb⟩ := hstep j hjN
  obtain ⟨Ξ, hΞP, hΞ, h1⟩ := hs.exists_sqrt_sq_norm_galerkin_sub_backwardEuler_add_le hdiss hμ0
    hμ hh (Yt := W j) (by rw [← hY]; exact hW j)
  have h2 : ‖U₁ * S₁ * V₁ᵀ - W j‖ ≤
      √(‖U₁ * S₁ * V₁ᵀ - W j‖ ^ 2 + h * ‖(U₁ * S₁ * V₁ᵀ - W j) * Cᵀ‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by
      have : 0 ≤ h * ‖(U₁ * S₁ * V₁ᵀ - W j) * Cᵀ‖ ^ 2 := by positivity
      linarith)
  have e : Y (j + 1) - W j = Y (j + 1) - U₁ * S₁ * V₁ᵀ + (U₁ * S₁ * V₁ᵀ - W j) := by abel
  have h3 := norm_add_le (Y (j + 1) - U₁ * S₁ * V₁ᵀ) (U₁ * S₁ * V₁ᵀ - W j)
  rw [← e] at h3
  have h4 := hs.trunc
  have h5 := hb Ξ hΞP hΞ
  linarith

/-- **Closed run bound with truncation: the growth factor is `1 + O((h μ)²)` per step.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, and let `X_j` be a reference with
`X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j` and `‖X_j CᵀC‖ ≤ κ`; the rows of the reference
need not lie in the kernel of `CᵀC`. Let step `j` of the integrator with backward Euler substeps
start from `Y_j` (of any rank), with exact capture by bases of any size, result
`Ŷ_{j+1} = U₁ S₁ V₁ᵀ` and truncated value `Y_{j+1} = T_j Ŷ_{j+1}`, `T_j` an orthogonal projector,
`‖Y_{j+1} - Ŷ_{j+1}‖ ≤ ϑ_j`. Then, with `c = 27/4 + 2 h μ` and without a restriction on `h μ`,

  `‖Y_N - X_N‖ ≤ (1 + (c h μ)² / 16)^N (‖Y₀ - X₀‖ + c h μ λ₀ + ∑_{j<N} ‖δ_j‖ + ∑_{j<N} ϑ_j`
  `    + N c h μ h κ)`,   `λ₀ = min(‖Y₀‖, √h ‖(Y₀ - X₀) Cᵀ‖ / 2 + h ‖X₀ CᵀC‖)`.

With `N h = t` the factor is at most `exp(c² μ² t h / 16)`: it tends to one with `h`. -/
theorem norm_implicitBUG_truncated_run_sub_le_of_sylvester_of_sq
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (htrunc : ∀ j < N, IsOrthProjMat (T j) ∧ Y (j + 1) = T j * Yh (j + 1))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hκ : ∀ j ≤ N, ‖X j * (Cᵀ * C)‖ ≤ κ) :
    ‖Y N - X N‖ ≤
      (1 + ((27 / 4 + 2 * (h * μ)) * (h * μ)) ^ 2 / 16) ^ N * (‖Y 0 - X 0‖ +
        (27 / 4 + 2 * (h * μ)) * (h * μ) *
          min ‖Y 0‖ (√h * ‖(Y 0 - X 0) * Cᵀ‖ / 2 + h * ‖X 0 * (Cᵀ * C)‖) +
        ∑ j ∈ range N, ‖δ j‖ + ∑ j ∈ range N, ϑ j +
        N * ((27 / 4 + 2 * (h * μ)) * (h * μ) * (h * κ))) := by
  obtain ⟨q, hq⟩ : ∃ q, q = (27 / 4 + 2 * (h * μ)) * (h * μ) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by
    rw [hq]; have := mul_nonneg hh.le hμ0; positivity
  rw [← hq]
  have hκ0 : 0 ≤ κ := (norm_nonneg (X 0 * (Cᵀ * C))).trans (hκ 0 (Nat.zero_le N))
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  obtain ⟨G, hG⟩ : ∃ G, G = 1 + q ^ 2 / 16 := ⟨_, rfl⟩
  have hG1 : 1 ≤ G := by rw [hG]; have := sq_nonneg q; linarith
  rw [← hG]
  obtain ⟨b, hb⟩ : ∃ b, b = q * (h * κ) := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb]; exact mul_nonneg hq0 (mul_nonneg hh.le hκ0)
  rw [← hb]
  obtain ⟨A, hA⟩ : ∃ A, A = ‖Y 0 - X 0‖ +
      q * min ‖Y 0‖ (√h * ‖(Y 0 - X 0) * Cᵀ‖ / 2 + h * ‖X 0 * (Cᵀ * C)‖) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : 0 ≤ min ‖Y 0‖ (√h * ‖(Y 0 - X 0) * Cᵀ‖ / 2 + h * ‖X 0 * (Cᵀ * C)‖) :=
      le_min (norm_nonneg _) (by positivity)
    positivity
  rw [← hA]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ, Φ = fun j => √(‖Yh j - X j‖ ^ 2 +
      2 * (h * ‖(Yh j - X j) * Cᵀ‖ ^ 2)) := ⟨_, rfl⟩
  have hϑ : ∀ j < N, ‖Y (j + 1) - Yh (j + 1)‖ ≤ ϑ j := by
    intro j hj
    obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, -, hYh, hs⟩ := hstep j hj
    rw [hYh]; exact hs.trunc
  have hϑ0 : ∀ j < N, 0 ≤ ϑ j := fun j hj => (norm_nonneg _).trans (hϑ j hj)
  -- one step: the functional after the step against the error before it
  have hI : ∀ j < N, ∀ Z : Matrix m n ℝ, Φ (j + 1) ≤ ‖Y j - X j‖ + ‖δ j‖ +
      q * min ‖Y j‖ (√h * ‖(Y j - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖) := by
    intro j hj Z
    obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, hY, hYh, hs⟩ := hstep j hj
    obtain ⟨W, hW⟩ := exists_backwardEuler (C := C) hdiss hh.le (Y j)
    have h1 := hs.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester hdiss hμ0 hμ hh
      (Yt := W) (by rw [← hY]; exact hW) Z
    rw [← hY, ← hYh, ← hq] at h1
    have e : W - X (j + 1) - h • (M * (W - X (j + 1))) +
        h • ((W - X (j + 1)) * (Cᵀ * C)) = Y j - (X j + δ j) := by
      rw [← hW, ← hX j hj]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    have n1 := sqrt_sq_norm_add_le_of_backwardEuler hdiss hh.le e
    have n2 : ‖Y j - (X j + δ j)‖ ≤ ‖Y j - X j‖ + ‖δ j‖ := by
      rw [← sub_sub]; exact norm_sub_le _ _
    have e3 : Yh (j + 1) - X (j + 1) = W - X (j + 1) + (Yh (j + 1) - W) := by abel
    have n3 := sqrt_sq_norm_add_add_le (C := C) hh.le (W - X (j + 1)) (Yh (j + 1) - W)
    rw [← e3] at n3
    rw [hΦ]
    linarith
  have key : ∀ n : ℕ, n + 1 ≤ N → Φ (n + 1) ≤
      G ^ n * (A + ∑ j ∈ range (n + 1), ‖δ j‖ + ∑ j ∈ range n, ϑ j + (n : ℝ) * b) := by
    intro n
    induction n with
    | zero =>
      intro hn
      have h1 := hI 0 hn (X 0)
      simp only [zero_add, pow_zero, one_mul, Finset.sum_range_one, Finset.range_zero,
        Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero] at h1 ⊢
      rw [hA]
      linarith
    | succ n ih =>
      intro hn
      have ih' := ih (Nat.le_of_succ_le hn)
      have hn' : n < N := by omega
      obtain ⟨hT, hYT⟩ := htrunc n hn'
      have h1 := hI (n + 1) hn (T n * X (n + 1))
      have m1 := mul_le_mul_of_nonneg_left (min_le_right ‖Y (n + 1)‖
        (√h * ‖(Y (n + 1) - T n * X (n + 1)) * Cᵀ‖ / 2 +
          h * ‖T n * X (n + 1) * (Cᵀ * C)‖)) hq0
      -- the truncation: the error grows by `ϑ`, the stiff energy and `‖· CᵀC‖` do not grow
      have e3 : ‖Y (n + 1) - X (n + 1)‖ ≤ ‖Yh (n + 1) - X (n + 1)‖ + ϑ n := by
        have e : Y (n + 1) - X (n + 1) = Yh (n + 1) - X (n + 1) + (Y (n + 1) - Yh (n + 1)) := by
          abel
        rw [e]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (hϑ n hn'))
      have e4 : √h * ‖(Y (n + 1) - T n * X (n + 1)) * Cᵀ‖ ≤
          √h * ‖(Yh (n + 1) - X (n + 1)) * Cᵀ‖ := by
        have e : (Y (n + 1) - T n * X (n + 1)) * Cᵀ = T n * ((Yh (n + 1) - X (n + 1)) * Cᵀ) := by
          rw [hYT, ← Matrix.mul_sub, Matrix.mul_assoc]
        rw [e]
        exact mul_le_mul_of_nonneg_left (norm_proj_mul_le hT.idem hT.symm _) (Real.sqrt_nonneg h)
      have e5 : h * ‖T n * X (n + 1) * (Cᵀ * C)‖ ≤ h * κ := by
        rw [Matrix.mul_assoc]
        exact mul_le_mul_of_nonneg_left
          ((norm_proj_mul_le hT.idem hT.symm _).trans (hκ (n + 1) (Nat.le_of_succ_le hn))) hh.le
      -- the loss proportional to the square root of the stiff energy
      have a1 := add_mul_le_mul_sqrt (norm_nonneg (Yh (n + 1) - X (n + 1)))
        (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg ((Yh (n + 1) - X (n + 1)) * Cᵀ)))
        (by positivity : (0 : ℝ) ≤ q / 2)
      have a2 : 1 + (q / 2) ^ 2 / 4 = G := by rw [hG]; ring
      have a3 : √(‖Yh (n + 1) - X (n + 1)‖ ^ 2 +
          2 * (√h * ‖(Yh (n + 1) - X (n + 1)) * Cᵀ‖) ^ 2) = Φ (n + 1) := by
        rw [hΦ, mul_pow, hs2]
      rw [a2, a3] at a1
      have u1 := mul_le_mul_of_nonneg_left ih' (le_trans zero_le_one hG1)
      have u2 := mul_le_mul_of_nonneg_left e4 hq0
      have u3 := mul_le_mul_of_nonneg_left e5 hq0
      have hGn : 1 ≤ G ^ (n + 1) := one_le_pow₀ hG1
      have t1 := mul_le_mul_of_nonneg_right hGn (hϑ0 n hn')
      have t2 := mul_le_mul_of_nonneg_right hGn (norm_nonneg (δ (n + 1)))
      have t3 := mul_le_mul_of_nonneg_right hGn hb0
      have eR : G ^ (n + 1) * (A + ∑ j ∈ range (n + 1 + 1), ‖δ j‖ + ∑ j ∈ range (n + 1), ϑ j +
          ((n + 1 : ℕ) : ℝ) * b) =
          G * (G ^ n * (A + ∑ j ∈ range (n + 1), ‖δ j‖ + ∑ j ∈ range n, ϑ j + (n : ℝ) * b)) +
            G ^ (n + 1) * ϑ n + G ^ (n + 1) * ‖δ (n + 1)‖ + G ^ (n + 1) * b := by
        rw [Finset.sum_range_succ (fun j => ‖δ j‖) (n + 1), Finset.sum_range_succ ϑ n, pow_succ]
        push_cast
        ring
      rw [← hb] at u3
      rw [eR]
      linarith
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul,
      add_zero]
    rw [hA]
    have : 0 ≤ q * min ‖Y 0‖ (√h * ‖(Y 0 - X 0) * Cᵀ‖ / 2 + h * ‖X 0 * (Cᵀ * C)‖) :=
      mul_nonneg hq0 (le_min (norm_nonneg _) (by positivity))
    linarith
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have h1 := key n le_rfl
    have h2 : ‖Yh (n + 1) - X (n + 1)‖ ≤ Φ (n + 1) := by
      rw [hΦ]
      exact Real.le_sqrt_of_sq_le (by
        have : 0 ≤ 2 * (h * ‖(Yh (n + 1) - X (n + 1)) * Cᵀ‖ ^ 2) := by positivity
        linarith)
    have e : Y (n + 1) - X (n + 1) = Yh (n + 1) - X (n + 1) + (Y (n + 1) - Yh (n + 1)) := by
      abel
    have h3 := norm_add_le (Yh (n + 1) - X (n + 1)) (Y (n + 1) - Yh (n + 1))
    rw [← e] at h3
    have h4 := hϑ n (Nat.lt_succ_self n)
    have hth0 := hϑ0 n (Nat.lt_succ_self n)
    obtain ⟨S, hS⟩ : ∃ S, S = A + ∑ j ∈ range (n + 1), ‖δ j‖ + ∑ j ∈ range n, ϑ j +
        (n : ℝ) * b := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by
      rw [hS]
      have s1 : 0 ≤ ∑ j ∈ range (n + 1), ‖δ j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
      have s2 : 0 ≤ ∑ j ∈ range n, ϑ j :=
        Finset.sum_nonneg fun j hj => hϑ0 j (by have := Finset.mem_range.1 hj; omega)
      positivity
    rw [← hS] at h1
    have hGn : 1 ≤ G ^ n := one_le_pow₀ hG1
    have hGn1 : G ^ n ≤ G ^ (n + 1) := by
      rw [pow_succ]; nlinarith
    have t1 := mul_le_mul_of_nonneg_right hGn1 hS0
    have t2 := mul_le_mul_of_nonneg_right (hGn.trans hGn1) hth0
    have t3 := mul_nonneg (le_trans zero_le_one (hGn.trans hGn1)) hb0
    have eR : G ^ (n + 1) * (A + ∑ j ∈ range (n + 1), ‖δ j‖ + ∑ j ∈ range (n + 1), ϑ j +
        ((n + 1 : ℕ) : ℝ) * b) = G ^ (n + 1) * S + G ^ (n + 1) * ϑ n + G ^ (n + 1) * b := by
      rw [hS, Finset.sum_range_succ ϑ n]
      push_cast
      ring
    rw [eR]
    linarith

/-- **Closed run bound with truncation against an exact solution.** Let `F(Z) = M Z - Z CᵀC` with
`M` dissipative and bounded by `μ`, and let `A` solve `A' = M A - A CᵀC` on `[0, N h]` with
`‖A(s) CᵀC‖ ≤ κ` and velocity `K₂`-Lipschitz in time (a bound of the second derivative). For a run
of the integrator with backward Euler substeps, exact capture, bases of any size and truncation
by orthogonal projectors with tolerances `ϑ_j` (as in
`norm_implicitBUG_truncated_run_sub_le_of_sylvester_of_sq`), with `c = 27/4 + 2 h μ`,

  `‖Y_N - A(N h)‖ ≤ (1 + (c h μ)² / 16)^N (‖Y₀ - A(0)‖ + c h μ λ₀ + N K₂ h² + ∑_{j<N} ϑ_j`
  `    + N c h μ h κ)`,   `λ₀ = min(‖Y₀‖, √h ‖(Y₀ - A(0)) Cᵀ‖ / 2 + h ‖A(0) CᵀC‖)`.

With `N h = t`: `N K₂ h² + N c h μ h κ = t h (K₂ + c μ κ)`, first order in `h`, and the factor is at
most `exp(c² μ² t h / 16)`; there is no restriction on `h μ`. -/
theorem norm_implicitBUG_truncated_run_sub_solution_le_of_sylvester_of_sq
    {A : ℝ → Matrix m n ℝ} {K₂ : ℝ}
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (htrunc : ∀ j < N, IsOrthProjMat (T j) ∧ Y (j + 1) = T j * Yh (j + 1))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) A 0 (N * h))
    (hκ : ∀ s ∈ Set.Icc 0 (N * h), ‖A s * (Cᵀ * C)‖ ≤ κ)
    (hK₂ : ∀ s ∈ Set.Icc 0 (N * h), ∀ s' ∈ Set.Icc 0 (N * h), s ≤ s' →
      ‖M * A s - A s * (Cᵀ * C) - (M * A s' - A s' * (Cᵀ * C))‖ ≤ K₂ * (s' - s))
    (hK₂0 : 0 ≤ K₂) :
    ‖Y N - A (N * h)‖ ≤
      (1 + ((27 / 4 + 2 * (h * μ)) * (h * μ)) ^ 2 / 16) ^ N * (‖Y 0 - A 0‖ +
        (27 / 4 + 2 * (h * μ)) * (h * μ) *
          min ‖Y 0‖ (√h * ‖(Y 0 - A 0) * Cᵀ‖ / 2 + h * ‖A 0 * (Cᵀ * C)‖) +
        N * (K₂ * h ^ 2) + ∑ j ∈ range N, ϑ j +
        N * ((27 / 4 + 2 * (h * μ)) * (h * μ) * (h * κ))) := by
  have ht : ∀ j : ℕ, j ≤ N → (j : ℝ) * h ∈ Set.Icc 0 (N * h) := fun j hj =>
    ⟨by positivity, mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le⟩
  have hsub : ∀ j < N, ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) A
      (j * h) ((j + 1 : ℕ) * h) := fun j hj => hA.mono (ht j hj.le).1 (ht (j + 1) hj).2
  have hlen : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) * h = j * h + h := fun j => by push_cast; ring
  have hdef : ∀ j < N, ‖A ((j + 1 : ℕ) * h) - h • (M * A ((j + 1 : ℕ) * h)) +
      h • (A ((j + 1 : ℕ) * h) * (Cᵀ * C)) - A (j * h)‖ ≤ K₂ * h ^ 2 := by
    intro j hj
    have e : A ((j + 1 : ℕ) * h) - h • (M * A ((j + 1 : ℕ) * h)) +
        h • (A ((j + 1 : ℕ) * h) * (Cᵀ * C)) - A (j * h) =
        A ((j + 1 : ℕ) * h) - A (j * h) -
          h • (M * A ((j + 1 : ℕ) * h) - A ((j + 1 : ℕ) * h) * (Cᵀ * C)) := by
      rw [smul_sub]; abel
    rw [e]
    refine (hsub j hj).implicitEuler_defect_le_of_smooth (hlen j) hh.le ?_ hK₂0
    intro s hs
    exact hK₂ s ⟨(ht j hj.le).1.trans hs.1, hs.2.trans (ht (j + 1) hj).2⟩ _ (ht (j + 1) hj) hs.2
  have hsum : ∑ j ∈ range N, ‖A ((j + 1 : ℕ) * h) - h • (M * A ((j + 1 : ℕ) * h)) +
      h • (A ((j + 1 : ℕ) * h) * (Cᵀ * C)) - A (j * h)‖ ≤ N * (K₂ * h ^ 2) := by
    refine (Finset.sum_le_sum fun j hj => hdef j (Finset.mem_range.1 hj)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have key := norm_implicitBUG_truncated_run_sub_le_of_sylvester_of_sq
    (X := fun j => A (j * h))
    (δ := fun j => A ((j + 1 : ℕ) * h) - h • (M * A ((j + 1 : ℕ) * h)) +
      h • (A ((j + 1 : ℕ) * h) * (Cᵀ * C)) - A (j * h)) (κ := κ)
    hstep htrunc hdiss hμ0 hμ hh (fun j _ => (add_sub_cancel _ _).symm)
    (fun j hj => hκ _ (ht j hj))
  simp only [Nat.cast_zero, zero_mul] at key
  refine key.trans (mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by positivity) N))

end Run

/-! ### Non-vacuity -/

namespace ImplicitBUGStiffSharpRunExample

open ImplicitBUGStiffLemmasExample ImplicitBUGStiffLocalExample

local notation "Mᵣ" => (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Cᵣ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

local notation "Bᵣ" => (!![9 / 25, 12 / 25; 12 / 25, 16 / 25] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The hypotheses of the run bounds hold with `N = 1`, for every stiffness `lam > 0` and every
`h > 0`: `M = diag(0, -1)`, `C = (0, √lam)`, a step from `(3/5, 4/5)ᵀ (3/5, 4/5)`, whose rows are
not in the kernel of `CᵀC`, without truncation (`T = 1`), and a backward Euler step of the full
problem from the same matrix as reference. -/
example {h lam : ℝ} (hh : 0 < h) (hlam : 0 < lam) :
    ∃ (ϑ : ℕ → ℝ) (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
      (Y Yh X δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ j < 1, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix (Fin 2) (Fin r) ℝ)
        (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix (Fin 2) (Fin r) ℝ)
        (K₁ : Matrix (Fin 2) (Fin r) ℝ) (L₁ : Matrix (Fin 2) (Fin r) ℝ)
        (U₁ : Matrix (Fin 2) (Fin k₁) ℝ) (V₁ : Matrix (Fin 2) (Fin k₂) ℝ)
        (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ) (ε t : ℝ),
        Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
          IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
            Mᵣ * Z - Z * ((Cᵣ lam)ᵀ * (Cᵣ lam))) ε 0 (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁
            (Y (j + 1))) ∧
      (∀ j < 1, IsOrthProjMat (T j) ∧ Y (j + 1) = T j * Yh (j + 1)) ∧
      (∀ j < 1, X (j + 1) - h • (Mᵣ * X (j + 1)) +
        h • (X (j + 1) * ((Cᵣ lam)ᵀ * (Cᵣ lam))) = X j + δ j) ∧
      Y 0 * ((Cᵣ lam)ᵀ * (Cᵣ lam)) ≠ 0 ∧ X 0 * ((Cᵣ lam)ᵀ * (Cᵣ lam)) ≠ 0 := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ :=
    ImplicitBUGStiffLocalExample.exists_isMatrixImplicitBUGStep hh hlam.le
  obtain ⟨X₁, hX₁⟩ := exists_backwardEuler (C := Cᵣ lam) dotProduct_mulVec_nonpos hh.le Bᵣ
  refine ⟨fun _ => 0, fun _ => 1,
    fun j => if j = 0 then (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ
      else U₁ * S₁ * V₁ᵀ,
    fun _ => U₁ * S₁ * V₁ᵀ, fun j => if j = 0 then Bᵣ else X₁, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨1, 1, 1, !![3 / 5; 4 / 5], 1, !![3 / 5; 4 / 5], K₁, L₁, U₁, V₁, S₁, ε, 0, rfl, rfl,
      ⟨hs.orthU₀, hs.orthV₀, hs.kstep, hs.lstep, hs.orthU₁, hs.orthV₁, hs.kcap, hs.lcap,
        hs.knormal, hs.lnormal, hs.sstep, by simp⟩⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨⟨Matrix.transpose_one, Matrix.one_mul 1⟩, by simp⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa using hX₁
  · simp only [ite_true]
    rw [start_eq]
    exact start_mul_gram_ne_zero hlam
  · simp only [ite_true]
    exact start_mul_gram_ne_zero hlam

end ImplicitBUGStiffSharpRunExample

end LeanDLRA
