import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityWeingartenStep
import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityTruncation
import LeanDLRA.DLRA.QuasiOptimalityDefect

/-!
# Quasi-optimality of the BUG integrator: the tail seen from the old reference as source

`norm_bugRun_sub_truncation_le_of_norm_sub_tangentProjAt_le` bounds the error of the fixed-rank
BUG integrator of [CerutiLubich2022] for given data against the truncated singular value
decomposition `X k = T_r(A k)` with the source `9/4 h lam σ_r` per step (the tail times the whole
velocity of the data) in a tube of relative radius `1/16`. In this file the source of the step
`k` is the tail at the new time seen from the row and the column space of the old reference,

  `ω k² ≥ ‖(A (k+1) - X (k+1)) Pv k‖² + ‖Pu k (A (k+1) - X (k+1))‖²`,
  `Pu k = X k (X k)⁺`, `Pv k = (X k)⁺ X k`,

and the relative radius `θ k` of the tube is restricted by `θ k < 1/2` and `η_F k + θ k < 1`
only. The hypotheses are on the data at the grid points: `ρ k ≤ σ_{r-1}(A k), σ_{r-1}(A (k+1))`
(indices start at `0`) and

  `‖X (k+1) - X k‖₂ ≤ η_X k ρ k`,   `‖ΔR k‖₂ ≤ η_R k ρ k`,
  `‖X (k+1) - X k‖, ‖A (k+1) - A k‖ ≤ η_F k ρ k`,

`ΔR k` the increment of the tail `A - X`. Every sequence `B` with `‖Y 0 - X 0‖ ≤ B 0`,
`B k ≤ θ k ρ k` and

  `(1 + 3/2 η_R + κ (1 + η_R)² + c η_F (η_R + η_X (d (1 + η_R) + 1))) B k
      + (1 + β + c η_F (1 + d η_X)) ω k + c² η_F² η_R ρ k ≤ B (k+1)`

(`c ≥ 1/(1 - 2 θ)`, `d ≥ 1/(1 - η_F - θ)`, `κ = η_X (η_X + θ) d (1 + d)`, `β² ≥ 2 κ`, all at the
step `k`) bounds the error: `‖Y n - X n‖ ≤ B n`. At first order in the step the recursion is
`B (k+1) = (1 + 3/2 η_R + η_X θ d (1 + d)) B k + ω k`. All norms `‖·‖` are Frobenius norms and
`‖·‖₂` is the spectral norm.

## Main results

* `EckartYoung.sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le`: the Moore–Penrose inverse
  of the truncated singular value decomposition annihilates the tail, has norm at most `ρ⁻¹`,
  and its projectors have trace `r`.
* `Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_norm_tail_sq_le`: one step.
* `EckartYoung.sq_mul_norm_sub_truncation_mul_pinv_mul_sq_add_le`: the source in the increment
  of the data, `(1 - q)² (‖R Pv₀‖² + ‖Pu₀ R‖²) ≤ ‖R ΔAᵀ (X₀⁺)ᵀ‖² + ‖(X₀⁺)ᵀ ΔAᵀ R‖²` for
  `R = A₁ - T_r(A₁)`, `σ_r(A₁) ≤ q ρ`.
* `norm_bugRun_sub_truncation_le_of_norm_tail_sq_le`: `N` steps, for every majorant `B` of the
  recursion.

## Implementation notes

The step is `MatrixBUG.norm_projStep_sub_le_of_trace_of_norm_tail_sq_le` with the Moore–Penrose
inverses of the references. No curve through the data is used: the data enter at the grid points
only, and the bound is a recursion that can be evaluated before the integrator is run. The
right-hand side of `EckartYoung.sq_mul_norm_sub_truncation_mul_pinv_mul_sq_add_le` has the two
parts of the map `Z ↦ (X⁺)ᵀ Zᵀ R + R Zᵀ (X⁺)ᵀ` of `LeanDLRA/DLRA/QuasiOptimalityDefect.lean` at
the increment of the data, with the inverse at the old and the tail at the new time.

## References

* [CerutiLubich2022]
-/

open Finset Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

section Run

open EckartYoung Curvature MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The Moore–Penrose inverse has the projectors of every generalized inverse with symmetric
projectors, and annihilates what such an inverse annihilates. -/
private theorem mul_pinv_eq_zero_of_ginv {X R : Matrix m n ℝ} {G : Matrix n m ℝ}
    (hX : X * G * X = X) (hc : (X * G)ᵀ = X * G) (hr : (G * X)ᵀ = G * X) (hRG : R * G = 0)
    (hGR : G * R = 0) :
    R * X.pinv = 0 ∧ X.pinv * R = 0 ∧ X * X.pinv = X * G ∧ X.pinv * X = G * X := by
  have hP : X * X.pinv = X * G := by
    have h1 : X * G * (X * X.pinv) = X * X.pinv := by rw [← Matrix.mul_assoc, hX]
    have h2 : X * X.pinv * (X * G) = X * G := by
      rw [← Matrix.mul_assoc, Matrix.mul_pinv_mul_self]
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, hc, Matrix.transpose_mul_pinv] at h3
    rw [← h3]
    exact h2
  have hQ : X.pinv * X = G * X := by
    have h1 : X.pinv * X * (G * X) = X.pinv * X := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc X G X, hX]
    have h2 : G * X * (X.pinv * X) = G * X := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc X X.pinv X, Matrix.mul_pinv_mul_self]
    have h3 := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, hr, Matrix.transpose_pinv_mul] at h3
    rw [← h1]
    exact h3
  refine ⟨?_, ?_, hP, hQ⟩
  · calc R * X.pinv = R * (X.pinv * X * X.pinv) := by rw [Matrix.pinv_mul_self_mul_pinv]
      _ = R * G * X * X.pinv := by rw [hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = 0 := by rw [hRG, Matrix.zero_mul, Matrix.zero_mul]
  · calc X.pinv * R = X.pinv * X * X.pinv * R := by rw [Matrix.pinv_mul_self_mul_pinv]
      _ = X.pinv * (X * G * R) := by
        rw [Matrix.mul_assoc X.pinv X X.pinv, hP, Matrix.mul_assoc X.pinv (X * G) R]
      _ = 0 := by rw [Matrix.mul_assoc X G R, hGR, Matrix.mul_zero, Matrix.mul_zero]

/-- **The Moore–Penrose inverse of the truncated singular value decomposition.** If `0 < r` and
`0 < ρ ≤ σ_{r-1}(A)` (indices start at `0`), then `G = X⁺` for `X = T_r(A)` satisfies
`(A - X) G = 0`, `G (A - X) = 0`, `‖G‖₂ ≤ ρ⁻¹`, and the projectors `X G`, `G X` have trace
`r`. -/
theorem EckartYoung.sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le {r : ℕ} (hr : 0 < r)
    {A : Matrix m n ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1)) :
    (A - truncation A r) * (truncation A r).pinv = 0 ∧
      (truncation A r).pinv * (A - truncation A r) = 0 ∧
      specNorm (truncation A r).pinv ≤ ρ⁻¹ ∧
      trace (truncation A r * (truncation A r).pinv) = r ∧
      trace ((truncation A r).pinv * truncation A r) = r := by
  obtain ⟨G, hX, hc, hrw, hRG, hGR, -, htc, htr⟩ := exists_ginv_truncation (r := r) hρ hσ
  obtain ⟨h1, h2, hP, hQ⟩ := mul_pinv_eq_zero_of_ginv hX hc hrw hRG hGR
  refine ⟨h1, h2, specNorm_pinv_le (rank_truncation_of_le_singularValues hρ hσ) hρ
    (le_singularValues_truncation hr hρ hσ), ?_, ?_⟩
  · rw [hP, htc]
  · rw [hQ, htr]

omit [DecidableEq m] in
/-- **One BUG step for given data against the truncated singular value decomposition: the tail
seen from the old reference as source.** Let `0 < r`, `0 < ρ ≤ σ_{r-1}(A₀), σ_{r-1}(A₁)` (indices
start at `0`), `X₀ = T_r(A₀)`, `X₁ = T_r(A₁)`, `ΔR = (A₁ - X₁) - (A₀ - X₀)` and

  `‖X₁ - X₀‖₂ ≤ η_X ρ`, `‖ΔR‖₂ ≤ η_R ρ`, `‖X₁ - X₀‖ ≤ η_F ρ`, `‖A₁ - A₀‖ ≤ η_F ρ`.

For a BUG step `(U₀, S₀, V₀) ↦ (U₁, S₁, V₁)` with exact substeps for the increment `A₁ - A₀`,
bases with `r` orthonormal columns and `‖Y₀ - X₀‖ ≤ θ ρ`, and for `c`, `d`, `β`, `ω` with
`1 ≤ (1 - 2 θ) c`, `1 ≤ (1 - (η_F + θ)) d`, `2 η_X (η_X + θ) d (1 + d) ≤ β²` and
`‖(A₁ - X₁) X₀⁺ X₀‖² + ‖X₀ X₀⁺ (A₁ - X₁)‖² ≤ ω²`,

  `‖Y₁ - X₁‖ ≤ (1 + 3/2 η_R + η_X (η_X + θ) d (1 + d) (1 + η_R)²
        + c η_F (η_R + η_X (d (1 + η_R) + 1))) ‖Y₀ - X₀‖
      + (1 + β + c η_F (1 + d η_X)) ω + c² η_F² η_R ρ`. -/
theorem Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_norm_tail_sq_le {r : ℕ}
    (hr : 0 < r) {A₀ A₁ : Matrix m n ℝ} {ρ ηX ηR ηF θ c d β ω : ℝ}
    {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ S₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ}
    (hs : Exactness.IsBUGIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ S₁ V₁) (hρ : 0 < ρ)
    (hσ₀ : ρ ≤ (toEuclideanLin A₀).singularValues (r - 1))
    (hσ₁ : ρ ≤ (toEuclideanLin A₁).singularValues (r - 1))
    (hηX : specNorm (truncation A₁ r - truncation A₀ r) ≤ ηX * ρ)
    (hηR : specNorm (A₁ - truncation A₁ r - (A₀ - truncation A₀ r)) ≤ ηR * ρ)
    (hηF : ‖truncation A₁ r - truncation A₀ r‖ ≤ ηF * ρ) (hηA : ‖A₁ - A₀‖ ≤ ηF * ρ)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (he : ‖U₀ * S₀ * V₀ᵀ - truncation A₀ r‖ ≤ θ * ρ) (hc0 : 0 ≤ c)
    (hc : 1 ≤ (1 - 2 * θ) * c) (hd0 : 0 ≤ d) (hd : 1 ≤ (1 - (ηF + θ)) * d) (hβ0 : 0 ≤ β)
    (hβ : 2 * (ηX * (ηX + θ) * d * (1 + d)) ≤ β ^ 2) (hω0 : 0 ≤ ω)
    (hω : ‖(A₁ - truncation A₁ r) * ((truncation A₀ r).pinv * truncation A₀ r)‖ ^ 2 +
      ‖truncation A₀ r * (truncation A₀ r).pinv * (A₁ - truncation A₁ r)‖ ^ 2 ≤ ω ^ 2) :
    ‖U₁ * S₁ * V₁ᵀ - truncation A₁ r‖ ≤
      (1 + 3 / 2 * ηR + ηX * (ηX + θ) * d * (1 + d) * (1 + ηR) ^ 2 +
          c * ηF * (ηR + ηX * (d * (1 + ηR) + 1))) * ‖U₀ * S₀ * V₀ᵀ - truncation A₀ r‖ +
        (1 + β + c * ηF * (1 + d * ηX)) * ω + c ^ 2 * ηF ^ 2 * (ηR * ρ) := by
  classical
  obtain ⟨hRG₀, hGR₀, hG₀, htc₀, htr₀⟩ :=
    sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le hr hρ hσ₀
  obtain ⟨-, -, hG₁, -, -⟩ := sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le hr hρ hσ₁
  have hρi : 0 ≤ ρ⁻¹ := (inv_pos.mpr hρ).le
  have conv : ∀ {x y : ℝ}, x ≤ y * ρ → ρ⁻¹ * x ≤ y := fun {x y} h => by
    have h1 := mul_le_mul_of_nonneg_left h hρi
    have e : ρ⁻¹ * (y * ρ) = y := by field_simp
    linarith
  have htrU : ∀ {W : Matrix m (Fin r) ℝ}, Wᵀ * W = 1 → trace (W * Wᵀ) = (r : ℝ) := fun hW => by
    rw [trace_mul_transpose hW, Fintype.card_fin]
  have htrV : ∀ {W : Matrix n (Fin r) ℝ}, Wᵀ * W = 1 → trace (W * Wᵀ) = (r : ℝ) := fun hW => by
    rw [trace_mul_transpose hW, Fintype.card_fin]
  have h := norm_projStep_sub_le_of_trace_of_norm_tail_sq_le (X₀ := truncation A₀ r)
    (X₁ := truncation A₁ r) (G₀ := (truncation A₀ r).pinv) (G₁ := (truncation A₁ r).pinv)
    (g := ρ⁻¹) (isOrthProjMat_mul_transpose hU₁)
    (isOrthProjMat_mul_transpose hV₁) (isOrthProjMat_mul_transpose hU₀)
    (isOrthProjMat_mul_transpose hV₀) (colProj_mul_factor hU₀) (factor_mul_rowProj hV₀)
    (hs.proj_capK hV₀) (hs.proj_capL hU₀) (Matrix.mul_pinv_mul_self _)
    (Matrix.transpose_mul_pinv _) (Matrix.transpose_pinv_mul _) (Matrix.mul_pinv_mul_self _)
    (Matrix.transpose_mul_pinv _) (Matrix.transpose_pinv_mul _) hRG₀ hGR₀
    ((htrU hU₁).trans (htrU hU₀).symm) ((htrV hV₁).trans (htrV hV₀).symm)
    ((htrU hU₀).trans htc₀.symm) ((htrV hV₀).trans htr₀.symm) hG₀ hG₁
    (conv hηX) (conv hηR) (conv hηF) (conv hηA) (conv he) hc0 hc hd0 hd hβ0 hβ hω0 hω
  rw [← hs.eq_proj_mul] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hηR (by positivity)))

omit [DecidableEq m] in
/-- **The source of the BUG step in the increment of the data.** Let `0 < r`,
`0 < ρ ≤ σ_{r-1}(A₀), σ_{r-1}(A₁)` and `σ_r(A₁) ≤ q ρ` with `q ≤ 1` (indices start at `0`). With
`X₀ = T_r(A₀)` and the tail `R = A₁ - T_r(A₁)` at the new time,

  `(1 - q)² (‖R X₀⁺ X₀‖² + ‖X₀ X₀⁺ R‖²) ≤ ‖R (A₁ - A₀)ᵀ (X₀⁺)ᵀ‖² + ‖(X₀⁺)ᵀ (A₁ - A₀)ᵀ R‖²`:

the tail seen from the row and the column space of the old reference is at most `1/(1 - q)`
times the two parts of the map `Z ↦ (X₀⁺)ᵀ Zᵀ R + R Zᵀ (X₀⁺)ᵀ` at the increment of the data. -/
theorem EckartYoung.sq_mul_norm_sub_truncation_mul_pinv_mul_sq_add_le {r : ℕ} (hr : 0 < r)
    {A₀ A₁ : Matrix m n ℝ} {ρ q : ℝ} (hρ : 0 < ρ)
    (hσ₀ : ρ ≤ (toEuclideanLin A₀).singularValues (r - 1))
    (hσ₁ : ρ ≤ (toEuclideanLin A₁).singularValues (r - 1))
    (hq : (toEuclideanLin A₁).singularValues r ≤ q * ρ) (hq1 : q ≤ 1) :
    (1 - q) ^ 2 *
        (‖(A₁ - truncation A₁ r) * ((truncation A₀ r).pinv * truncation A₀ r)‖ ^ 2 +
          ‖truncation A₀ r * (truncation A₀ r).pinv * (A₁ - truncation A₁ r)‖ ^ 2) ≤
      ‖(A₁ - truncation A₁ r) * (A₁ - A₀)ᵀ * (truncation A₀ r).pinvᵀ‖ ^ 2 +
        ‖(truncation A₀ r).pinvᵀ * (A₁ - A₀)ᵀ * (A₁ - truncation A₁ r)‖ ^ 2 := by
  classical
  obtain ⟨hRG₀, hGR₀, hG₀, -, -⟩ :=
    sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le hr hρ hσ₀
  obtain ⟨hRG₁, hGR₁, -, -, -⟩ :=
    sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le hr hρ hσ₁
  refine sq_mul_norm_tail_mul_rowProj_sq_add_le (G₁ := (truncation A₁ r).pinv)
    (Matrix.pinv_mul_self_mul_pinv _) (Matrix.transpose_mul_pinv _)
    (Matrix.transpose_pinv_mul _) (Matrix.mul_pinv_mul_self _) (Matrix.transpose_mul_pinv _)
    (Matrix.transpose_pinv_mul _) hRG₀ hGR₀ hRG₁ hGR₁ hG₀ ?_ hq1
  rw [specNorm_sub_truncation]
  have h1 := mul_le_mul_of_nonneg_left hq (inv_pos.mpr hρ).le
  have e : ρ⁻¹ * (q * ρ) = q := by field_simp
  linarith

omit [DecidableEq m] in
/-- **Quasi-optimality of the BUG integrator for given data with the tail seen from the old
reference as source.** Let `Y k = U k S k (V k)ᵀ` be `N` steps of the BUG integrator of
[CerutiLubich2022] with exact substeps for the data `A k`, with bases of `r > 0` orthonormal
columns, and let `X k = T_r(A k)`. On the step `k < N` let
`0 < ρ k ≤ σ_{r-1}(A k), σ_{r-1}(A (k+1))` (indices start at `0`),

  `‖X (k+1) - X k‖₂ ≤ η_X k ρ k`, `‖ΔR k‖₂ ≤ η_R k ρ k`,
  `‖X (k+1) - X k‖ ≤ η_F k ρ k`, `‖A (k+1) - A k‖ ≤ η_F k ρ k`

for the increment `ΔR k` of the tail `A - X`, and let `θ k`, `c k`, `d k`, `β k`, `ω k` satisfy
`1 ≤ (1 - 2 θ) c`, `1 ≤ (1 - (η_F + θ)) d`, `2 η_X (η_X + θ) d (1 + d) ≤ β²` and
`‖(A (k+1) - X (k+1)) (X k)⁺ X k‖² + ‖X k (X k)⁺ (A (k+1) - X (k+1))‖² ≤ (ω k)²`. If a sequence
`B` satisfies `‖Y 0 - X 0‖ ≤ B 0` and for `k < N`

  `B k ≤ θ k ρ k`,
  `(1 + 3/2 η_R + η_X (η_X + θ) d (1 + d) (1 + η_R)² + c η_F (η_R + η_X (d (1 + η_R) + 1))) B k
      + (1 + β + c η_F (1 + d η_X)) ω k + c² η_F² η_R ρ k ≤ B (k+1)`,

then `‖Y n - X n‖ ≤ B n` for `n ≤ N`. All hypotheses are on the data at the grid points; the
error of the integrator enters through the initial value only. -/
theorem norm_bugRun_sub_truncation_le_of_norm_tail_sq_le {r N : ℕ} (hr : 0 < r)
    {A : ℕ → Matrix m n ℝ} {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {ρ ηX ηR ηF θ c d β ω B : ℕ → ℝ} (hρ : ∀ k < N, 0 < ρ k)
    (hσ₀ : ∀ k < N, ρ k ≤ (toEuclideanLin (A k)).singularValues (r - 1))
    (hσ₁ : ∀ k < N, ρ k ≤ (toEuclideanLin (A (k + 1))).singularValues (r - 1))
    (hηX : ∀ k < N,
      specNorm (truncation (A (k + 1)) r - truncation (A k) r) ≤ ηX k * ρ k)
    (hηR : ∀ k < N, specNorm (A (k + 1) - truncation (A (k + 1)) r -
      (A k - truncation (A k) r)) ≤ ηR k * ρ k)
    (hηF : ∀ k < N, ‖truncation (A (k + 1)) r - truncation (A k) r‖ ≤ ηF k * ρ k)
    (hηA : ∀ k < N, ‖A (k + 1) - A k‖ ≤ ηF k * ρ k)
    (hc0 : ∀ k < N, 0 ≤ c k) (hc : ∀ k < N, 1 ≤ (1 - 2 * θ k) * c k)
    (hd0 : ∀ k < N, 0 ≤ d k) (hd : ∀ k < N, 1 ≤ (1 - (ηF k + θ k)) * d k)
    (hβ0 : ∀ k < N, 0 ≤ β k)
    (hβ : ∀ k < N, 2 * (ηX k * (ηX k + θ k) * d k * (1 + d k)) ≤ β k ^ 2)
    (hω0 : ∀ k < N, 0 ≤ ω k)
    (hω : ∀ k < N, ‖(A (k + 1) - truncation (A (k + 1)) r) *
          ((truncation (A k) r).pinv * truncation (A k) r)‖ ^ 2 +
        ‖truncation (A k) r * (truncation (A k) r).pinv *
          (A (k + 1) - truncation (A (k + 1)) r)‖ ^ 2 ≤ ω k ^ 2)
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (hs : ∀ k < N, Exactness.IsBUGIncrementStep (A k) (A (k + 1)) (U k) (S k) (V k)
      (U (k + 1)) (S (k + 1)) (V (k + 1)))
    (h0 : ‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ ≤ B 0)
    (htube : ∀ k < N, B k ≤ θ k * ρ k)
    (hB : ∀ k < N,
      (1 + 3 / 2 * ηR k + ηX k * (ηX k + θ k) * d k * (1 + d k) * (1 + ηR k) ^ 2 +
          c k * ηF k * (ηR k + ηX k * (d k * (1 + ηR k) + 1))) * B k +
        (1 + β k + c k * ηF k * (1 + d k * ηX k)) * ω k +
        c k ^ 2 * ηF k ^ 2 * (ηR k * ρ k) ≤ B (k + 1)) :
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - truncation (A n) r‖ ≤ B n := by
  intro n
  induction n with
  | zero =>
    intro _
    exact h0
  | succ n ih =>
    intro hn
    have hnN : n < N := hn
    have ihn := ih hnN.le
    have hρn := hρ n hnN
    have hηX0 : 0 ≤ ηX n :=
      nonneg_of_mul_nonneg_left ((specNorm_nonneg _).trans (hηX n hnN)) hρn
    have hηR0 : 0 ≤ ηR n :=
      nonneg_of_mul_nonneg_left ((specNorm_nonneg _).trans (hηR n hnN)) hρn
    have hηF0 : 0 ≤ ηF n :=
      nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hηF n hnN)) hρn
    have hθ0 : 0 ≤ θ n :=
      nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (ihn.trans (htube n hnN))) hρn
    have hc0n := hc0 n hnN
    have hd0n := hd0 n hnN
    have key := (hs n hnN).norm_sub_truncation_le_of_norm_tail_sq_le hr hρn (hσ₀ n hnN)
      (hσ₁ n hnN) (hηX n hnN) (hηR n hnN) (hηF n hnN) (hηA n hnN) (hU n hnN.le) (hV n hnN.le)
      (hU (n + 1) hn) (hV (n + 1) hn) (ihn.trans (htube n hnN)) hc0n (hc n hnN) hd0n
      (hd n hnN) (hβ0 n hnN) (hβ n hnN) (hω0 n hnN) (hω n hnN)
    have hcoef : 0 ≤ 1 + 3 / 2 * ηR n + ηX n * (ηX n + θ n) * d n * (1 + d n) * (1 + ηR n) ^ 2 +
        c n * ηF n * (ηR n + ηX n * (d n * (1 + ηR n) + 1)) := by positivity
    exact key.trans (le_trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left ihn hcoef)
      le_rfl) le_rfl) (hB n hnN))

end Run

/-! ### Examples -/

namespace BUGQuasiOptimalityWeingartenExamples

open scoped LeanDLRA.Frobenius
open BUGQuasiOptimalityExamples EckartYoung Curvature

/-- `σ₀(diag(c, w)) ≥ c`: the matrix maps the first unit vector to `c` times itself. -/
private theorem le_singularValues_diag₂ {c w : ℝ} :
    c ≤ (toEuclideanLin (!![c, 0; 0, w] : Matrix (Fin 2) (Fin 2) ℝ)).singularValues 0 := by
  rw [← EckartYoung.specNorm_eq_singularValues_zero]
  have hs : toEuclideanLin (!![c, 0; 0, w] : Matrix (Fin 2) (Fin 2) ℝ)
      (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 c := by
    ext i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have h := Curvature.norm_toEuclideanLin_le (!![c, 0; 0, w] : Matrix (Fin 2) (Fin 2) ℝ)
    (EuclideanSpace.single 0 1)
  rw [hs] at h
  exact (le_abs_self c).trans (by simpa using h)

/-- **The rank-one truncation of `diag(c, w)`, `c > 0`, `w² < c²`**, is `diag(c, 0)`: the top
right singular vector is plus or minus the first unit vector, because `σ₀² ≥ c² > w²`. -/
private theorem truncation_diag₂ {c w : ℝ} (hc : 0 < c) (hw : w * w < c * c) :
    EckartYoung.truncation (!![c, 0; 0, w] : Matrix (Fin 2) (Fin 2) ℝ) 1 =
      !![c, 0; 0, 0] := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![c, 0; 0, w] with hA
  have hAA : Aᵀ * A = !![c * c, 0; 0, w * w] := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hσ : c ≤ (toEuclideanLin A).singularValues 0 := le_singularValues_diag₂
  let i0 : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := ⟨0, by simp⟩
  let j0 : {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) // (i : ℕ) < 1} :=
    ⟨i0, Nat.zero_lt_one⟩
  have hP : EckartYoung.topRightSingularVectors A 1 *
      (EckartYoung.topRightSingularVectors A 1)ᵀ =
      Matrix.of fun a b => EckartYoung.rightSingularVectors A i0 a *
        EckartYoung.rightSingularVectors A i0 b := by
    ext a b
    rw [Matrix.mul_apply, Fintype.sum_eq_single j0]
    · rfl
    · intro x hx
      exact absurd (Subtype.ext (Fin.ext (by have := x.2; change (x.1 : ℕ) = 0; omega))) hx
  have hE := EckartYoung.transpose_mul_self_mulVec_rightSingularVectors A i0
  rw [hAA] at hE
  have hn : EckartYoung.rightSingularVectors A i0 0 ^ 2 +
      EckartYoung.rightSingularVectors A i0 1 ^ 2 = 1 := by
    have h1 := (EckartYoung.rightSingularVectors A).orthonormal.1 i0
    have h2 : ‖EckartYoung.rightSingularVectors A i0‖ ^ 2 =
        EckartYoung.rightSingularVectors A i0 0 ^ 2 +
          EckartYoung.rightSingularVectors A i0 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [h1] at h2
    linarith
  have h1 := congrFun hE 1
  simp only [mulVec, dotProduct, Fin.isValue, of_apply, cons_val', cons_val_fin_one,
    cons_val_one, Fin.sum_univ_two, cons_val_zero, zero_mul, zero_add, Pi.smul_apply,
    smul_eq_mul] at h1
  have hσ' : c ≤ (toEuclideanLin A).singularValues ↑i0 := hσ
  have hs2 : c * c ≤ (toEuclideanLin A).singularValues ↑i0 ^ 2 := by nlinarith
  have hx1 : EckartYoung.rightSingularVectors A i0 1 = 0 := by
    have hm : ((toEuclideanLin A).singularValues ↑i0 ^ 2 - w * w) *
        EckartYoung.rightSingularVectors A i0 1 = 0 := by
      linear_combination (-1 : ℝ) * h1
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · exact h
  have hx00 : EckartYoung.rightSingularVectors A i0 0 *
      EckartYoung.rightSingularVectors A i0 0 = 1 := by
    rw [hx1] at hn
    nlinarith
  unfold EckartYoung.truncation
  rw [Matrix.mul_assoc, hP]
  generalize EckartYoung.rightSingularVectors A i0 = e at hx1 hx00 ⊢
  rw [hA]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx1, hx00]

/-- The rank-one truncation of `diag(c, w)`, `c > 0`, `w² < c²`, is `diag(c, 0)`. -/
private theorem truncation_dg {c w : ℝ} (hc : 0 < c) (hw : w * w < c * c) :
    truncation (dg c w) 1 = dg c 0 :=
  truncation_diag₂ hc hw

/-- `σ₀(diag(c, w)) ≥ ρ` for `c ≥ ρ`. -/
private theorem le_singularValues_dg {c w ρ : ℝ} (h : ρ ≤ c) :
    ρ ≤ (toEuclideanLin (dg c w)).singularValues (1 - 1) :=
  h.trans le_singularValues_diag₂

/-- `‖diag(s, t)‖ ≤ b` for `s² + t² ≤ b²`. -/
private theorem norm_dg_le {s t b : ℝ} (hb : 0 ≤ b) (h : s ^ 2 + t ^ 2 ≤ b ^ 2) :
    ‖dg s t‖ ≤ b := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero).mp ?_
  rw [Curvature.frob_sq]
  simpa [dg, Fin.sum_univ_two] using h

/-- `e₁ (s) e₁ᵀ = diag(s, 0)`. -/
private theorem e₁_mul_sc_mul (s : ℝ) : e₁ * sc s * e₁ᵀ = dg s 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, dg, sc, Matrix.mul_apply]

/-- A BUG step with exact substeps for the data `diag(a, w) ↦ diag(a', w')` from
`Y₀ = diag(s, 0)`: the core becomes `s + (a' - a)` and the bases stay `e₁`. -/
private theorem isBUGIncrementStep_dg_dg (a w a' w' s : ℝ) :
    Exactness.IsBUGIncrementStep (dg a w) (dg a' w') e₁ (sc s) e₁ e₁ (sc (s + (a' - a)))
      e₁ := by
  have hk : e₁ * sc s + (dg a' w' - dg a w) * e₁ = e₁ * sc (s + (a' - a)) := by
    rw [dg_sub, dg_mul_e₁, ← Matrix.mul_add, sc_add]
  have hcap : e₁ * e₁ᵀ * (e₁ * sc (s + (a' - a))) = e₁ * sc (s + (a' - a)) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc e₁ᵀ, e₁_orth, Matrix.one_mul]
  refine ⟨by rw [hk, hcap], ?_, ?_⟩
  · rw [sc_transpose, dg_sub, dg_transpose, ← dg_sub, hk, hcap]
  · rw [e₁_orth, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, dg_sub,
      Matrix.mul_assoc, dg_mul_e₁, ← Matrix.mul_assoc, e₁_orth, Matrix.one_mul, sc_add]

/-- The data of the examples: `A₀ = diag(1, 1/16)`, `A₁ = diag(33/32, 1/8)`; the reference
moves from `diag(1, 0)` to `diag(33/32, 0)` and the tail from `diag(0, 1/16)` to
`diag(0, 1/8)`. -/
private theorem truncation_dg₀ : truncation (dg 1 (1 / 16)) 1 = dg 1 0 :=
  truncation_dg (by norm_num) (by norm_num)

private theorem truncation_dg₁ : truncation (dg (33 / 32) (1 / 8)) 1 = dg (33 / 32) 0 :=
  truncation_dg (by norm_num) (by norm_num)

private theorem one_le_singularValues_dg₀ :
    (1 : ℝ) ≤ (toEuclideanLin (dg 1 (1 / 16))).singularValues (1 - 1) :=
  le_singularValues_dg le_rfl

private theorem one_le_singularValues_dg₁ :
    (1 : ℝ) ≤ (toEuclideanLin (dg (33 / 32) (1 / 8))).singularValues (1 - 1) :=
  le_singularValues_dg (by norm_num)

private theorem specNorm_truncation_sub_le :
    specNorm (truncation (dg (33 / 32) (1 / 8)) 1 - truncation (dg 1 (1 / 16)) 1) ≤
      1 / 32 * 1 := by
  rw [truncation_dg₁, truncation_dg₀, dg_sub]
  exact (specNorm_le_frob _).trans (norm_dg_le (by norm_num) (by norm_num))

private theorem specNorm_tail_sub_le :
    specNorm (dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1 -
      (dg 1 (1 / 16) - truncation (dg 1 (1 / 16)) 1)) ≤ 1 / 16 * 1 := by
  rw [truncation_dg₁, truncation_dg₀, dg_sub, dg_sub, dg_sub]
  exact (specNorm_le_frob _).trans (norm_dg_le (by norm_num) (by norm_num))

private theorem norm_truncation_sub_le :
    ‖truncation (dg (33 / 32) (1 / 8)) 1 - truncation (dg 1 (1 / 16)) 1‖ ≤ 1 / 8 * 1 := by
  rw [truncation_dg₁, truncation_dg₀, dg_sub]
  exact norm_dg_le (by norm_num) (by norm_num)

private theorem norm_data_sub_le : ‖dg (33 / 32) (1 / 8) - dg 1 (1 / 16)‖ ≤ 1 / 8 * 1 := by
  rw [dg_sub]
  exact norm_dg_le (by norm_num) (by norm_num)

/-- The tail `diag(0, 1/8)` at the new time is not seen from the row and the column space of
the old reference `diag(1, 0)`. -/
private theorem norm_tail_mul_pinv_mul_sq_add_le :
    ‖(dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1) *
          ((truncation (dg 1 (1 / 16)) 1).pinv * truncation (dg 1 (1 / 16)) 1)‖ ^ 2 +
        ‖truncation (dg 1 (1 / 16)) 1 * (truncation (dg 1 (1 / 16)) 1).pinv *
          (dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1)‖ ^ 2 ≤
      ((1 : ℝ) / 128) ^ 2 := by
  obtain ⟨hRG, hGR, -, -, -⟩ := sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le
    (r := 1) one_pos one_pos one_le_singularValues_dg₀
  have e : dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1 =
      (2 : ℝ) • (dg 1 (1 / 16) - truncation (dg 1 (1 / 16)) 1) := by
    rw [truncation_dg₁, truncation_dg₀, dg_sub, dg_sub]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [dg]
  rw [e, Matrix.smul_mul, ← Matrix.mul_assoc, hRG, Matrix.zero_mul, smul_zero, Matrix.mul_smul,
    Matrix.mul_assoc _ _ (dg 1 (1 / 16) - truncation (dg 1 (1 / 16)) 1), hGR, Matrix.mul_zero,
    smul_zero, norm_zero]
  norm_num

private theorem norm_factor_sub_truncation_le :
    ‖e₁ * sc (33 / 32) * e₁ᵀ - truncation (dg 1 (1 / 16)) 1‖ ≤ 1 / 32 := by
  rw [truncation_dg₀, e₁_mul_sc_mul, dg_sub]
  exact norm_dg_le (by norm_num) (by norm_num)

/-- **Non-vacuity of `norm_bugRun_sub_truncation_le_of_norm_tail_sq_le`** (and of
`Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_norm_tail_sq_le`,
`EckartYoung.sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le`,
`MatrixBUG.norm_projStep_sub_le_of_trace_of_norm_tail_sq_le` and the lemmas they use): one step
for the data `A₀ = diag(1, 1/16)`, `A₁ = diag(33/32, 1/8)`, `r = 1`, from
`Y₀ = diag(33/32, 0)`, with `ρ = 1`, `η_X = 1/32`, `η_R = 1/16`, `η_F = 1/8`, `θ = 1/32`,
`c = d = 2`, `β = 1/4`, `ω = 1/128` and the majorant `B 0 = 1/32`, `B 1 = 1/16`. The reference
moves, the tail moves (the increment of the data has a component normal to the manifold of
rank-one matrices at the reference), and the iterates differ from the reference. -/
example : ‖e₁ * sc (33 / 32 + (33 / 32 - 1)) * e₁ᵀ - truncation (dg (33 / 32) (1 / 8)) 1‖ ≤
    1 / 16 := by
  have h := norm_bugRun_sub_truncation_le_of_norm_tail_sq_le (r := 1) (N := 1)
    (A := fun k => if k = 0 then dg 1 (1 / 16) else dg (33 / 32) (1 / 8))
    (U := fun _ => e₁)
    (S := fun k => if k = 0 then sc (33 / 32) else sc (33 / 32 + (33 / 32 - 1)))
    (V := fun _ => e₁) (ρ := fun _ => 1) (ηX := fun _ => 1 / 32) (ηR := fun _ => 1 / 16)
    (ηF := fun _ => 1 / 8) (θ := fun _ => 1 / 32) (c := fun _ => 2) (d := fun _ => 2)
    (β := fun _ => 1 / 4) (ω := fun _ => 1 / 128)
    (B := fun k => if k = 0 then 1 / 32 else 1 / 16) one_pos (fun _ _ => one_pos)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using one_le_singularValues_dg₀)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using one_le_singularValues_dg₁)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using specNorm_truncation_sub_le)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using specNorm_tail_sub_le)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using norm_truncation_sub_le)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using norm_data_sub_le)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using norm_tail_mul_pinv_mul_sq_add_le)
    (fun _ _ => e₁_orth) (fun _ _ => e₁_orth)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      simpa using isBUGIncrementStep_dg_dg 1 (1 / 16) (33 / 32) (1 / 8) (33 / 32))
    (by simpa using norm_factor_sub_truncation_le)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      norm_num)
    (fun k hk => by
      obtain rfl := Nat.lt_one_iff.mp hk
      norm_num) 1 le_rfl
  simpa using h

/-- **Non-vacuity of `EckartYoung.sq_mul_norm_sub_truncation_mul_pinv_mul_sq_add_le`** (and of
`MatrixBUG.sq_mul_norm_tail_mul_rowProj_sq_add_le`): the data of the example above with
`ρ = 1` and `q = 1/8`. -/
example : (1 - 1 / 8 : ℝ) ^ 2 *
      (‖(dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1) *
          ((truncation (dg 1 (1 / 16)) 1).pinv * truncation (dg 1 (1 / 16)) 1)‖ ^ 2 +
        ‖truncation (dg 1 (1 / 16)) 1 * (truncation (dg 1 (1 / 16)) 1).pinv *
          (dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1)‖ ^ 2) ≤
    ‖(dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1) *
        (dg (33 / 32) (1 / 8) - dg 1 (1 / 16))ᵀ * (truncation (dg 1 (1 / 16)) 1).pinvᵀ‖ ^ 2 +
      ‖(truncation (dg 1 (1 / 16)) 1).pinvᵀ * (dg (33 / 32) (1 / 8) - dg 1 (1 / 16))ᵀ *
        (dg (33 / 32) (1 / 8) - truncation (dg (33 / 32) (1 / 8)) 1)‖ ^ 2 := by
  refine sq_mul_norm_sub_truncation_mul_pinv_mul_sq_add_le (r := 1) (ρ := 1) one_pos one_pos
    one_le_singularValues_dg₀ one_le_singularValues_dg₁ ?_ (by norm_num)
  rw [← specNorm_sub_truncation, truncation_dg₁, dg_sub]
  exact (specNorm_le_frob _).trans (norm_dg_le (by norm_num) (by norm_num))

end BUGQuasiOptimalityWeingartenExamples

end LeanDLRA
