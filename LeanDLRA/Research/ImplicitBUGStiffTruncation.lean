import LeanDLRA.Research.ImplicitBUGStiffLemmas

/-!
# The implicit BUG integrator with a stiff row operator: runs with truncation

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary (the matrix
`-CᵀC` acting on the rows is the stiffness). This file bounds the error of a run of the BUG
integrator with backward Euler substeps in which the rank may change from step to step: step `j`
starts from `Y_j` (any rank), uses bases of any size with exact capture (the fixed-rank bases or
the augmented ones), gives `Ŷ_{j+1} = U₁ S₁ V₁ᵀ`, and is followed by a truncation
`Y_{j+1} = T_j Ŷ_{j+1}` with an orthogonal projector `T_j` acting from the left (the truncated
singular value decomposition is of this form) and `‖Y_{j+1} - Ŷ_{j+1}‖ ≤ ϑ_j`. Against a reference
with `X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`, `‖δ_j‖ ≤ d`, `‖X_j CᵀC‖ ≤ κ`,
`‖X_{j+1} - X_j‖ ≤ h ω`, and for `h μ ≤ 1/8`,

  `‖Y_N - X_N‖ ≤ (1 + 9 h μ)^N (‖Y₀ - X₀‖ + 2 h μ ‖Y₀‖ + N (2 d + 2 h μ h (7 κ + 3 ω)) + 2 ∑ ϑ_j)`.

Neither `C` nor the singular values of the numerical solution enter. For an exact solution `A`
of the differential equation whose velocity is `K₂`-Lipschitz in time the same bound holds for
`‖Y_N - A(N h)‖` with `d = K₂ h²`.

## Main results

* `sqrt_sq_norm_implicitBUG_truncated_run_sub_add_le_of_sylvester`: the run bound for the error
  before the last truncation, with its stiff energy.
* `norm_implicitBUG_truncated_run_sub_le_of_sylvester`: the run bound.
* `norm_implicitBUG_truncated_run_sub_solution_le_of_sylvester`: the run bound against an exact
  solution of the differential equation.

## Implementation notes

The error functional of a step contains the stiff energy `h ‖(Y_j - X_j) Cᵀ‖²` of the start
error, and the stiff energy of a truncation defect is not bounded by its norm. A projector `T`
acting from the left commutes with the right multiplication by `C`: the stiff term of the K-step
is compared with `Z = T X_j`, for which `(Y_j - Z) Cᵀ = T (Ŷ_j - X_j) Cᵀ` and
`‖Z CᵀC‖ ≤ ‖X_j CᵀC‖`. So only the stiff energy of the error before the truncation is needed, and
the truncation enters through `‖Y_j - Ŷ_j‖ ≤ ϑ_{j-1}` alone.

## References

* [CerutiLubich2022], [CerutiKuschLubich2022] for the BUG integrator and its rank-adaptive
  variant; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas Curvature

namespace ImplicitBUGStiffTruncation

/-- The scalar form of the first step of a run: the start value may have any stiff energy. -/
private theorem start_scalar {η Ψ e y d k w : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (he : 0 ≤ e)
    (hy : 0 ≤ y) (hd : 0 ≤ d) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (h : (1 - η) * Ψ ≤ (1 + 6 * η) * (e + d) + η * (y + 6 * k + 3 * w)) :
    Ψ ≤ (1 + 9 * η) * (e + 2 * η * y + (2 * d + 2 * η * (7 * k + 3 * w))) := by
  have hφ : 1 + 6 * η ≤ (1 - η) * (1 + 9 * η) := by nlinarith
  have hφ1 : 1 ≤ (1 - η) * (1 + 9 * η) := by nlinarith
  have hc0 : 0 ≤ 2 * η * y + (2 * d + 2 * η * (7 * k + 3 * w)) := by positivity
  have t1 := mul_le_mul_of_nonneg_right hφ he
  have t2 := mul_le_mul_of_nonneg_right hφ1 hc0
  have t3 := mul_le_mul_of_nonneg_right hη hd
  have eR : (1 - η) * ((1 + 9 * η) * (e + 2 * η * y + (2 * d + 2 * η * (7 * k + 3 * w)))) =
      (1 - η) * (1 + 9 * η) * e +
        (1 - η) * (1 + 9 * η) * (2 * η * y + (2 * d + 2 * η * (7 * k + 3 * w))) := by ring
  have goal' : (1 - η) * Ψ ≤
      (1 - η) * ((1 + 9 * η) * (e + 2 * η * y + (2 * d + 2 * η * (7 * k + 3 * w)))) := by
    rw [eR]
    linarith [mul_nonneg hη0 hy, mul_nonneg hη0 hk, mul_nonneg hη0 hw]
  exact le_of_mul_le_mul_left goal' (by linarith)

/-- The scalar form of a later step of a run: `B` bounds the error before the truncation with
its stiff energy, `th` the truncation. -/
private theorem step_scalar {η Ψ B th d k w : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hB : 0 ≤ B)
    (hth : 0 ≤ th) (hd : 0 ≤ d) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (h : (1 - η) * Ψ ≤ (1 + 6 * η) * (B + th + d) + η * (B / 2 + k + 6 * k + 3 * w)) :
    Ψ ≤ (1 + 9 * η) * (B + (2 * d + 2 * η * (7 * k + 3 * w)) + 2 * th) := by
  have hφ : 1 + 13 / 2 * η ≤ (1 - η) * (1 + 9 * η) := by nlinarith
  have hφ1 : 1 ≤ (1 - η) * (1 + 9 * η) := by nlinarith
  have hc0 : 0 ≤ 2 * d + 2 * η * (7 * k + 3 * w) := by positivity
  have t1 := mul_le_mul_of_nonneg_right hφ hB
  have t2 := mul_le_mul_of_nonneg_right hφ1 hc0
  have t3 := mul_le_mul_of_nonneg_right hφ1 hth
  have t4 := mul_le_mul_of_nonneg_right hη hth
  have t5 := mul_le_mul_of_nonneg_right hη hd
  have eR : (1 - η) * ((1 + 9 * η) * (B + (2 * d + 2 * η * (7 * k + 3 * w)) + 2 * th)) =
      (1 - η) * (1 + 9 * η) * B + (1 - η) * (1 + 9 * η) * (2 * d + 2 * η * (7 * k + 3 * w)) +
        2 * ((1 - η) * (1 + 9 * η) * th) := by ring
  have goal' : (1 - η) * Ψ ≤
      (1 - η) * ((1 + 9 * η) * (B + (2 * d + 2 * η * (7 * k + 3 * w)) + 2 * th)) := by
    rw [eR]
    linarith [mul_nonneg hη0 hk, mul_nonneg hη0 hw]
  exact le_of_mul_le_mul_left goal' (by linarith)

end ImplicitBUGStiffTruncation

open ImplicitBUGStiffTruncation

section Run

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  {N : ℕ} {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ κ ω d : ℝ} {ϑ : ℕ → ℝ}
  {T : ℕ → Matrix m m ℝ} {Y Yh X δ : ℕ → Matrix m n ℝ}

/-- **Run bound with truncation for the error with its stiff energy.** Let `F(Z) = M Z - Z CᵀC`
with `M` dissipative and bounded by `μ`, `h μ ≤ 1/8`, and let `X_j` be a reference with
`X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`, `‖δ_j‖ ≤ d`, `‖X_j CᵀC‖ ≤ κ` and
`‖X_{j+1} - X_j‖ ≤ h ω`. Let step `j` of the integrator with backward Euler substeps start from
`Y_j` (in any factorisation, of any rank), with exact capture by bases of any size, result
`Ŷ_{j+1} = U₁ S₁ V₁ᵀ` and truncated value `Y_{j+1} = T_j Ŷ_{j+1}`, `T_j` an orthogonal projector,
`‖Y_{j+1} - Ŷ_{j+1}‖ ≤ ϑ_j`. Then for `N ≥ 1`, with `ê_N = Ŷ_N - X_N`,

  `√(‖ê_N‖² + h ‖ê_N Cᵀ‖²) ≤`
  `    (1 + 9 h μ)^N (‖Y₀ - X₀‖ + 2 h μ ‖Y₀‖ + N (2 d + 2 h μ h (7 κ + 3 ω)) + 2 ∑_{j<N-1} ϑ_j)`. -/
theorem sqrt_sq_norm_implicitBUG_truncated_run_sub_add_le_of_sylvester
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (htrunc : ∀ j < N, IsOrthProjMat (T j) ∧ Y (j + 1) = T j * Yh (j + 1))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 8)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hκ : ∀ j ≤ N, ‖X j * (Cᵀ * C)‖ ≤ κ) (hω : ∀ j < N, ‖X (j + 1) - X j‖ ≤ h * ω)
    (hδ : ∀ j < N, ‖δ j‖ ≤ d) (hN : 0 < N) :
    √(‖Yh N - X N‖ ^ 2 + h * ‖(Yh N - X N) * Cᵀ‖ ^ 2) ≤
      (1 + 9 * (h * μ)) ^ N * (‖Y 0 - X 0‖ + 2 * (h * μ) * ‖Y 0‖ +
        N * (2 * d + 2 * (h * μ) * (h * (7 * κ + 3 * ω))) + 2 * ∑ j ∈ range (N - 1), ϑ j) := by
  obtain ⟨η, hη⟩ : ∃ η, η = h * μ := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hη]; exact mul_nonneg hh.le hμ0
  rw [← hη] at hhμ ⊢
  have hκ0 : 0 ≤ κ := (norm_nonneg (X 0 * (Cᵀ * C))).trans (hκ 0 (Nat.zero_le N))
  have hω0 : 0 ≤ ω := by
    have := (norm_nonneg (X (0 + 1) - X 0)).trans (hω 0 hN)
    exact (mul_nonneg_iff_of_pos_left hh).1 this
  have hd0 : 0 ≤ d := (norm_nonneg (δ 0)).trans (hδ 0 hN)
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, Ψ = fun j => √(‖Yh j - X j‖ ^ 2 +
      h * ‖(Yh j - X j) * Cᵀ‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * d + 2 * η * (h * (7 * κ + 3 * ω)) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ‖Y 0 - X 0‖ + 2 * η * ‖Y 0‖ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hΨe : ∀ j, ‖Yh j - X j‖ ≤ Ψ j := fun j => by
    have := le_sqrt_sq_add_sq_left (c := √h * ‖(Yh j - X j) * Cᵀ‖) (norm_nonneg (Yh j - X j))
    rw [mul_pow, hs2] at this
    rw [hΨ]; exact this
  have hΨE : ∀ j, √h * ‖(Yh j - X j) * Cᵀ‖ ≤ Ψ j := fun j => by
    have := le_sqrt_sq_add_sq_right (d := ‖Yh j - X j‖)
      (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg ((Yh j - X j) * Cᵀ)))
    rw [mul_pow, hs2] at this
    rw [hΨ]; exact this
  have hϑ : ∀ j < N, ‖Y (j + 1) - Yh (j + 1)‖ ≤ ϑ j := by
    intro j hj
    obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, -, hYh, hs⟩ := hstep j hj
    rw [hYh]; exact hs.trunc
  have hϑ0 : ∀ j < N, 0 ≤ ϑ j := fun j hj => (norm_nonneg _).trans (hϑ j hj)
  -- one step, with the bounds of the reference and a free comparison matrix
  have hI : ∀ j < N, ∀ Z : Matrix m n ℝ, (1 - η) * Ψ (j + 1) ≤
      (1 + 6 * η) * (‖Y j - X j‖ + d) +
        η * (min ‖Y j‖ (√h * ‖(Y j - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖) + 6 * (h * κ) +
          3 * (h * ω)) := by
    intro j hj Z
    obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, hY, hYh, hs⟩ := hstep j hj
    have h1 := hs.sqrt_sq_norm_galerkin_sub_add_le_of_sylvester hdiss hμ0 hμ hh
      (by rw [← hη]; linarith) (hX j hj) Z
    rw [← hY, ← hYh, ← hη] at h1
    have k1 := mul_le_mul_of_nonneg_left (hκ (j + 1) hj) hh.le
    have a1 := mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖Y j - X j‖)
      (hδ j hj)) (by linarith : (0 : ℝ) ≤ 1 + 6 * η)
    have a2 := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl (min ‖Y j‖ (√h * ‖(Y j - Z) * Cᵀ‖ / 2 +
        h * ‖Z * (Cᵀ * C)‖))) (mul_le_mul_of_nonneg_left k1 (by norm_num : (0 : ℝ) ≤ 6)))
        (mul_le_mul_of_nonneg_left (hω j hj) (by norm_num : (0 : ℝ) ≤ 3))) hη0
    rw [hΨ]
    exact h1.trans (add_le_add a1 a2)
  have hk0 : 0 ≤ h * κ := mul_nonneg hh.le hκ0
  have hw0 : 0 ≤ h * ω := mul_nonneg hh.le hω0
  have hcc : 2 * d + 2 * η * (7 * (h * κ) + 3 * (h * ω)) = c := by rw [hc]; ring
  have key : ∀ n : ℕ, n + 1 ≤ N → Ψ (n + 1) ≤
      (1 + 9 * η) ^ (n + 1) * (A + ((n : ℝ) + 1) * c + 2 * ∑ j ∈ range n, ϑ j) := by
    intro n
    induction n with
    | zero =>
      intro hn
      have h1 := hI 0 hn (X 0)
      have m1 := mul_le_mul_of_nonneg_left (min_le_left ‖Y 0‖
        (√h * ‖(Y 0 - X 0) * Cᵀ‖ / 2 + h * ‖X 0 * (Cᵀ * C)‖)) hη0
      have := start_scalar (Ψ := Ψ (0 + 1)) hη0 hhμ (norm_nonneg (Y 0 - X 0)) (norm_nonneg (Y 0))
        hd0 hk0 hw0 (by linarith)
      rw [hcc, ← hA] at this
      simpa using this
    | succ n ih =>
      intro hn
      have ih' := ih (Nat.le_of_succ_le hn)
      have hn' : n < N := by omega
      obtain ⟨hT, hYT⟩ := htrunc n hn'
      have h1 := hI (n + 1) hn (T n * X (n + 1))
      have m1 := mul_le_mul_of_nonneg_left (min_le_right ‖Y (n + 1)‖
        (√h * ‖(Y (n + 1) - T n * X (n + 1)) * Cᵀ‖ / 2 +
          h * ‖T n * X (n + 1) * (Cᵀ * C)‖)) hη0
      have e1 := hΨe (n + 1)
      have e2 := hΨE (n + 1)
      obtain ⟨G, hG⟩ : ∃ G, G = (1 + 9 * η) ^ (n + 1) := ⟨_, rfl⟩
      have hG1 : 1 ≤ G := by rw [hG]; exact one_le_pow₀ (by linarith)
      have hsum0 : 0 ≤ ∑ j ∈ range n, ϑ j :=
        Finset.sum_nonneg fun j hj => hϑ0 j (by have := Finset.mem_range.1 hj; omega)
      obtain ⟨B, hB⟩ : ∃ B, B = G * (A + ((n : ℝ) + 1) * c + 2 * ∑ j ∈ range n, ϑ j) :=
        ⟨_, rfl⟩
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      rw [← hG, ← hB] at ih'
      obtain ⟨th, hth⟩ : ∃ th, th = ϑ n := ⟨_, rfl⟩
      have hth0 : 0 ≤ th := by rw [hth]; exact hϑ0 n hn'
      -- the truncation: the error grows by `ϑ`, the stiff energy and `‖· CᵀC‖` do not grow
      have e3 : ‖Y (n + 1) - X (n + 1)‖ ≤ B + th := by
        have e : Y (n + 1) - X (n + 1) = Yh (n + 1) - X (n + 1) + (Y (n + 1) - Yh (n + 1)) := by
          abel
        rw [e, hth]
        exact (norm_add_le _ _).trans (add_le_add (e1.trans ih') (hϑ n hn'))
      have e4 : √h * ‖(Y (n + 1) - T n * X (n + 1)) * Cᵀ‖ ≤ B := by
        have e : (Y (n + 1) - T n * X (n + 1)) * Cᵀ = T n * ((Yh (n + 1) - X (n + 1)) * Cᵀ) := by
          rw [hYT, ← Matrix.mul_sub, Matrix.mul_assoc]
        rw [e]
        exact ((mul_le_mul_of_nonneg_left (norm_proj_mul_le hT.idem hT.symm _)
          (Real.sqrt_nonneg h)).trans e2).trans ih'
      have e5 : h * ‖T n * X (n + 1) * (Cᵀ * C)‖ ≤ h * κ := by
        rw [Matrix.mul_assoc]
        exact mul_le_mul_of_nonneg_left
          ((norm_proj_mul_le hT.idem hT.symm _).trans (hκ (n + 1) (Nat.le_of_succ_le hn))) hh.le
      have u1 := mul_le_mul_of_nonneg_left e3 (by linarith : (0 : ℝ) ≤ 1 + 6 * η)
      have u2 := mul_le_mul_of_nonneg_left e4 hη0
      have u3 := mul_le_mul_of_nonneg_left e5 hη0
      have hS := step_scalar (Ψ := Ψ (n + 1 + 1)) hη0 hhμ hB0 hth0 hd0 hk0 hw0 (by linarith)
      rw [hcc] at hS
      have t2 := mul_le_mul_of_nonneg_right hG1 hc0
      have t5 := mul_le_mul_of_nonneg_right hG1 hth0
      have eR : (1 + 9 * η) ^ (n + 1 + 1) *
          (A + (((n + 1 : ℕ) : ℝ) + 1) * c + 2 * ∑ j ∈ range (n + 1), ϑ j) =
          (1 + 9 * η) * (B + G * c + 2 * (G * th)) := by
        rw [hB, hG, hth, pow_succ, Finset.sum_range_succ]; push_cast; ring
      rw [eR]
      exact hS.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := key n le_rfl
  rw [hΨ, hA, hc] at this
  simpa using this

/-- **Run bound with truncation, uniform in the stiffness and in the singular values.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, `h μ ≤ 1/8`, and let `X_j` be a
reference with `X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`, `‖δ_j‖ ≤ d`, `‖X_j CᵀC‖ ≤ κ`
and `‖X_{j+1} - X_j‖ ≤ h ω`; the rows of the reference need not lie in the kernel of `CᵀC`. Let
step `j` of the integrator with backward Euler substeps start from `Y_j` (of any rank), with
exact capture by bases of any size (fixed rank or augmented), result `Ŷ_{j+1} = U₁ S₁ V₁ᵀ` and
truncated value `Y_{j+1} = T_j Ŷ_{j+1}`, `T_j` an orthogonal projector (as for the truncated
singular value decomposition), `‖Y_{j+1} - Ŷ_{j+1}‖ ≤ ϑ_j`. Then

  `‖Y_N - X_N‖ ≤`
  `    (1 + 9 h μ)^N (‖Y₀ - X₀‖ + 2 h μ ‖Y₀‖ + N (2 d + 2 h μ h (7 κ + 3 ω)) + 2 ∑_{j<N} ϑ_j)`.

The matrix `C` enters only through `κ`; the singular values and the ranks do not enter. -/
theorem norm_implicitBUG_truncated_run_sub_le_of_sylvester
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (htrunc : ∀ j < N, IsOrthProjMat (T j) ∧ Y (j + 1) = T j * Yh (j + 1))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 8)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hκ : ∀ j ≤ N, ‖X j * (Cᵀ * C)‖ ≤ κ) (hω : ∀ j < N, ‖X (j + 1) - X j‖ ≤ h * ω)
    (hδ : ∀ j < N, ‖δ j‖ ≤ d) :
    ‖Y N - X N‖ ≤
      (1 + 9 * (h * μ)) ^ N * (‖Y 0 - X 0‖ + 2 * (h * μ) * ‖Y 0‖ +
        N * (2 * d + 2 * (h * μ) * (h * (7 * κ + 3 * ω))) + 2 * ∑ j ∈ range N, ϑ j) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    rw [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero, Finset.sum_range_zero, mul_zero,
      add_zero]
    linarith [mul_nonneg (mul_nonneg zero_le_two (mul_nonneg hh.le hμ0)) (norm_nonneg (Y 0))]
  · have h1 := sqrt_sq_norm_implicitBUG_truncated_run_sub_add_le_of_sylvester hstep htrunc hdiss
      hμ0 hμ hh hhμ hX hκ hω hδ hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h1
    obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, -, hYh, hs⟩ :=
      hstep n (Nat.lt_succ_self n)
    have hϑn : ‖Y (n + 1) - Yh (n + 1)‖ ≤ ϑ n := by rw [hYh]; exact hs.trunc
    have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
    have h2 := le_sqrt_sq_add_sq_left (c := √h * ‖(Yh (n + 1) - X (n + 1)) * Cᵀ‖)
      (norm_nonneg (Yh (n + 1) - X (n + 1)))
    rw [mul_pow, hs2] at h2
    have e : Y (n + 1) - X (n + 1) = Yh (n + 1) - X (n + 1) + (Y (n + 1) - Yh (n + 1)) := by
      abel
    have h3 := norm_add_le (Yh (n + 1) - X (n + 1)) (Y (n + 1) - Yh (n + 1))
    rw [← e] at h3
    obtain ⟨G, hG⟩ : ∃ G, G = (1 + 9 * (h * μ)) ^ (n + 1) := ⟨_, rfl⟩
    have hG1 : 1 ≤ G := by
      rw [hG]; exact one_le_pow₀ (by linarith [mul_nonneg hh.le hμ0])
    have hth0 : 0 ≤ ϑ n := (norm_nonneg _).trans hϑn
    have t5 := mul_le_mul_of_nonneg_right hG1 hth0
    rw [← hG] at h1 ⊢
    rw [Finset.sum_range_succ]
    obtain ⟨a, ha⟩ : ∃ a, a = ‖Y 0 - X 0‖ + 2 * (h * μ) * ‖Y 0‖ +
        ((n + 1 : ℕ) : ℝ) * (2 * d + 2 * (h * μ) * (h * (7 * κ + 3 * ω))) := ⟨_, rfl⟩
    rw [← ha] at h1 ⊢
    have e2 : G * (a + 2 * (∑ j ∈ range n, ϑ j + ϑ n)) =
        G * (a + 2 * ∑ j ∈ range n, ϑ j) + 2 * (G * ϑ n) := by ring
    rw [e2]
    linarith

/-- **Run bound with truncation against an exact solution.** Let `F(Z) = M Z - Z CᵀC` with `M`
dissipative and bounded by `μ`, `h μ ≤ 1/8`, and let `A` solve `A' = M A - A CᵀC` on `[0, N h]`
with `‖A(s) CᵀC‖ ≤ κ`, velocity bounded by `ω` and `K₂`-Lipschitz in time (a bound of the second
derivative). For a run of the integrator with backward Euler substeps, exact capture, bases of
any size and truncation by orthogonal projectors with tolerances `ϑ_j` (as in
`norm_implicitBUG_truncated_run_sub_le_of_sylvester`),

  `‖Y_N - A(N h)‖ ≤ (1 + 9 h μ)^N (‖Y₀ - A(0)‖ + 2 h μ ‖Y₀‖ +`
  `    N (2 K₂ h² + 2 h μ h (7 κ + 3 ω)) + 2 ∑_{j<N} ϑ_j)`.

With `N h = t` the factor is at most `e^{9 μ t}` and `N (2 K₂ h² + …) = 2 t h (K₂ + μ (7 κ + 3 ω))`:
first order in `h`, with constants that do not depend on `C` beyond `κ` and `K₂`, nor on the
singular values. -/
theorem norm_implicitBUG_truncated_run_sub_solution_le_of_sylvester {A : ℝ → Matrix m n ℝ}
    {K₂ : ℝ}
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (htrunc : ∀ j < N, IsOrthProjMat (T j) ∧ Y (j + 1) = T j * Yh (j + 1))
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hhμ : h * μ ≤ 1 / 8)
    (hA : ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) A 0 (N * h))
    (hκ : ∀ s ∈ Set.Icc 0 (N * h), ‖A s * (Cᵀ * C)‖ ≤ κ)
    (hω : ∀ s ∈ Set.Icc 0 (N * h), ‖M * A s - A s * (Cᵀ * C)‖ ≤ ω)
    (hK₂ : ∀ s ∈ Set.Icc 0 (N * h), ∀ s' ∈ Set.Icc 0 (N * h), s ≤ s' →
      ‖M * A s - A s * (Cᵀ * C) - (M * A s' - A s' * (Cᵀ * C))‖ ≤ K₂ * (s' - s))
    (hK₂0 : 0 ≤ K₂) :
    ‖Y N - A (N * h)‖ ≤
      (1 + 9 * (h * μ)) ^ N * (‖Y 0 - A 0‖ + 2 * (h * μ) * ‖Y 0‖ +
        N * (2 * (K₂ * h ^ 2) + 2 * (h * μ) * (h * (7 * κ + 3 * ω))) +
          2 * ∑ j ∈ range N, ϑ j) := by
  have ht : ∀ j : ℕ, j ≤ N → (j : ℝ) * h ∈ Set.Icc 0 (N * h) := fun j hj =>
    ⟨by positivity, mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le⟩
  have hsub : ∀ j < N, ODESolution (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) A
      (j * h) ((j + 1 : ℕ) * h) := fun j hj => hA.mono (ht j hj.le).1 (ht (j + 1) hj).2
  have hlen : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) * h = j * h + h := fun j => by push_cast; ring
  have hdef : ∀ j < N, ‖A ((j + 1 : ℕ) * h) - A (j * h) -
      h • (M * A ((j + 1 : ℕ) * h) - A ((j + 1 : ℕ) * h) * (Cᵀ * C))‖ ≤ K₂ * h ^ 2 := by
    intro j hj
    refine (hsub j hj).implicitEuler_defect_le_of_smooth (hlen j) hh.le ?_ hK₂0
    intro s hs
    exact hK₂ s ⟨(ht j hj.le).1.trans hs.1, hs.2.trans (ht (j + 1) hj).2⟩ _ (ht (j + 1) hj) hs.2
  have hspeed : ∀ j < N, ‖A ((j + 1 : ℕ) * h) - A (j * h)‖ ≤ h * ω := by
    intro j hj
    have := (hsub j hj).norm_sub_sub_smul_le (hlen j) hh.le (0 : Matrix m n ℝ) (M := ω)
      (fun s hs => by
        rw [sub_zero]
        exact hω s ⟨(ht j hj.le).1.trans hs.1, hs.2.le.trans (ht (j + 1) hj).2⟩)
    rw [smul_zero, sub_zero] at this
    linarith
  have key := norm_implicitBUG_truncated_run_sub_le_of_sylvester (X := fun j => A (j * h))
    (δ := fun j => A ((j + 1 : ℕ) * h) - h • (M * A ((j + 1 : ℕ) * h)) +
      h • (A ((j + 1 : ℕ) * h) * (Cᵀ * C)) - A (j * h)) (κ := κ) (ω := ω) (d := K₂ * h ^ 2)
    hstep htrunc hdiss hμ0 hμ hh hhμ (fun j _ => (add_sub_cancel _ _).symm)
    (fun j hj => hκ _ (ht j hj)) hspeed (fun j hj => by
      have e : A ((j + 1 : ℕ) * h) - h • (M * A ((j + 1 : ℕ) * h)) +
          h • (A ((j + 1 : ℕ) * h) * (Cᵀ * C)) - A (j * h) =
          A ((j + 1 : ℕ) * h) - A (j * h) -
            h • (M * A ((j + 1 : ℕ) * h) - A ((j + 1 : ℕ) * h) * (Cᵀ * C)) := by
        rw [smul_sub]; abel
      rw [e]
      exact hdef j hj)
  simp only [Nat.cast_zero, zero_mul] at key
  exact key

end Run

/-! ### Non-vacuity -/

namespace ImplicitBUGStiffTruncationExample

local notation "Mₑ" => (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Cₑ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

local notation "Aₑ" => (!![3 / 5, 0; 4 / 5, 0] : Matrix (Fin 2) (Fin 2) ℝ)

open ImplicitBUGStiffLemmasExample

/-- The result of the Galerkin step of this family is not zero for `h ≤ 1/4`: it is within
`3 h²/(1 - h)` of a backward Euler step of the full problem, whose norm is at least `1 - h`. -/
private theorem galerkin_ne_zero {h lam ε ϑ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 4) (hlam : 0 ≤ lam)
    {K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ} {S₁ : Matrix (Fin 1) (Fin 1) ℝ}
    {Y₁ : Matrix (Fin 2) (Fin 2) ℝ}
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      Mₑ * Z - Z * ((Cₑ lam)ᵀ * (Cₑ lam))) ε 0 ϑ 0 h !![3 / 5; 4 / 5] 1 !![1; 0] K₁ L₁ U₁ V₁
      S₁ Y₁) : U₁ * S₁ * V₁ᵀ ≠ 0 := by
  intro h0
  have hq : (1 : ℝ) + h ≠ 0 := by positivity
  have z0 : Aₑ * ((Cₑ lam)ᵀ * (Cₑ lam)) = 0 := by
    rw [transpose_mul_self_eq lam hlam]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have z1 : (!![3 / 5, 0; 4 / 5 / (1 + h), 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      ((Cₑ lam)ᵀ * (Cₑ lam)) = 0 := by
    rw [transpose_mul_self_eq lam hlam]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hX : (!![3 / 5, 0; 4 / 5 / (1 + h), 0] : Matrix (Fin 2) (Fin 2) ℝ) -
      h • (Mₑ * !![3 / 5, 0; 4 / 5 / (1 + h), 0]) +
      h • (!![3 / 5, 0; 4 / 5 / (1 + h), 0] * ((Cₑ lam)ᵀ * (Cₑ lam))) = Aₑ + 0 := by
    rw [z1, smul_zero, add_zero, add_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    field_simp
  have hY : (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ = Aₑ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  have key := hs.sqrt_sq_norm_galerkin_sub_add_le_of_sylvester dotProduct_mulVec_nonpos
    zero_le_one dotProduct_mulVec_mulVec_le hh (by linarith) hX Aₑ
  rw [h0, hY, z0, z1, sub_self, Matrix.zero_mul, norm_zero, norm_zero, zero_sub, norm_neg] at key
  -- the reference step: `‖X₁‖ ≤ ‖X₀‖` and `X₁ - X₀ = h M X₁`
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : Matrix (Fin 2) (Fin 2) ℝ, X₁ = !![3 / 5, 0; 4 / 5 / (1 + h), 0] :=
    ⟨_, rfl⟩
  rw [← hX₁] at key hX z1
  have b1 : ‖X₁‖ ≤ ‖Aₑ‖ := by
    have := norm_le_of_backwardEuler dotProduct_mulVec_nonpos hh.le hX
    rwa [add_zero] at this
  have b2 : ‖X₁ - Aₑ‖ ≤ h * ‖Aₑ‖ := by
    have e : X₁ - Aₑ = h • (Mₑ * X₁) := by
      rw [z1, smul_zero, add_zero, add_zero] at hX
      rw [← hX]; abel
    rw [e, norm_smul, Real.norm_of_nonneg hh.le]
    have n1 := norm_mul_le_mul_norm zero_le_one dotProduct_mulVec_mulVec_le X₁
    rw [one_mul] at n1
    exact mul_le_mul_of_nonneg_left (n1.trans b1) hh.le
  have b3 : ‖Aₑ‖ ≤ ‖X₁‖ + ‖X₁ - Aₑ‖ := by
    have := norm_sub_le X₁ (X₁ - Aₑ)
    rwa [sub_sub_cancel] at this
  have b4 : 0 < ‖Aₑ‖ := by
    refine norm_pos_iff.2 fun h1 => ?_
    have := congrFun (congrFun h1 0) 0
    norm_num at this
  have b5 : ‖X₁‖ ≤ √(‖X₁‖ ^ 2 + h * ‖(-X₁) * (Cₑ lam)ᵀ‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖(-X₁) * (Cₑ lam)ᵀ‖])
  have b6 := mul_le_mul_of_nonneg_left b5 (by linarith : (0 : ℝ) ≤ 1 - h * 1)
  have b7 := min_le_right ‖Aₑ‖ (√h * 0 / 2 + h * 0)
  have b8 := mul_le_mul_of_nonneg_left b7 (by linarith : (0 : ℝ) ≤ h * 1)
  nlinarith [mul_le_mul_of_nonneg_left b2 hh.le, mul_pos hh b4,
    mul_le_mul_of_nonneg_right hh1 b4.le, mul_nonneg hh.le (norm_nonneg X₁)]

/-- The hypotheses of the run bounds hold with `N = 1` and an active truncation, for every
stiffness `lam > 0` and `h ∈ (0, 1/4]`: `M = diag(0, -1)`, `C = (0, √lam)`, a step from
`(3/5, 4/5)ᵀ (1, 0)` whose result is truncated to rank `0` by the projector `T = 0` (so that
`Y₁ ≠ Ŷ₁` and the tolerance is positive), and a backward Euler step of the full problem from
`e₁ (1, 1)` whose result has rows outside the kernel of `CᵀC`. -/
example {h lam : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 4) (hlam : 0 < lam) :
    ∃ (ϑ : ℕ → ℝ) (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
      (Y Yh X δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ j < 1, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix (Fin 2) (Fin r) ℝ)
        (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix (Fin 2) (Fin r) ℝ)
        (K₁ : Matrix (Fin 2) (Fin r) ℝ) (L₁ : Matrix (Fin 2) (Fin r) ℝ)
        (U₁ : Matrix (Fin 2) (Fin k₁) ℝ) (V₁ : Matrix (Fin 2) (Fin k₂) ℝ)
        (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ) (ε t : ℝ),
        Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
          IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
            Mₑ * Z - Z * ((Cₑ lam)ᵀ * (Cₑ lam))) ε 0 (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁
            (Y (j + 1))) ∧
      (∀ j < 1, IsOrthProjMat (T j) ∧ Y (j + 1) = T j * Yh (j + 1)) ∧
      (∀ j < 1, X (j + 1) - h • (Mₑ * X (j + 1)) +
        h • (X (j + 1) * ((Cₑ lam)ᵀ * (Cₑ lam))) = X j + δ j) ∧
      X 1 * ((Cₑ lam)ᵀ * (Cₑ lam)) ≠ 0 ∧ Y 1 ≠ Yh 1 ∧ 0 < ϑ 0 := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ := exists_isMatrixImplicitBUGStep hh hlam.le
  have hne := galerkin_ne_zero hh hh1 hlam.le hs
  have hq : (1 : ℝ) + h * lam ≠ 0 := by positivity
  have hX : (!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
      h • (Mₑ * !![1, 1 / (1 + h * lam); 0, 0]) +
      h • (!![1, 1 / (1 + h * lam); 0, 0] * ((Cₑ lam)ᵀ * (Cₑ lam))) = !![1, 1; 0, 0] + 0 := by
    rw [transpose_mul_self_eq lam hlam.le]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    field_simp
  refine ⟨fun _ => ‖(0 : Matrix (Fin 2) (Fin 2) ℝ) - U₁ * S₁ * V₁ᵀ‖, fun _ => 0,
    fun j => if j = 0 then (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ else 0,
    fun _ => U₁ * S₁ * V₁ᵀ,
    fun j => if j = 0 then !![1, 1; 0, 0] else !![1, 1 / (1 + h * lam); 0, 0], fun _ => 0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨1, 1, 1, !![3 / 5; 4 / 5], 1, !![1; 0], K₁, L₁, U₁, V₁, S₁, ε, 0, rfl, rfl,
      ⟨hs.orthU₀, hs.orthV₀, hs.kstep, hs.lstep, hs.orthU₁, hs.orthV₁, hs.kcap, hs.lcap,
        hs.knormal, hs.lnormal, hs.sstep, le_rfl⟩⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨⟨Matrix.transpose_zero, Matrix.zero_mul 0⟩, (Matrix.zero_mul _).symm⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact hX
  · rw [transpose_mul_self_eq lam hlam.le]
    intro h0
    have e : ((!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        -!![0, 0; 0, -lam]) 0 1 = 1 / (1 + h * lam) * lam := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h0' : (!![1, 1 / (1 + h * lam); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        -!![0, 0; 0, -lam] = 0 := h0
    rw [h0', Matrix.zero_apply] at e
    have : 0 < 1 / (1 + h * lam) * lam := by positivity
    linarith
  · exact fun h0 => hne h0.symm
  · rw [zero_sub, norm_neg]
    exact norm_pos_iff.2 hne

end ImplicitBUGStiffTruncationExample

end LeanDLRA
