import LeanDLRA.Integrators.Matrix.BUGHybridQuasiOptimality
import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityWeingartenTruncation

/-!
# An error certificate for rank-adaptive BUG runs with the tail seen from the old reference

`norm_bugRun_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step` combines the robust bound
by the local errors with the quasi-optimal BUG step of rate `9/2 μ / (ρ - τ)` on one run with
changing rank, for the matrix approximation problem (data `A k` at the grid points, field
`F(t, Y) = Ȧ(t)`). In this file the certified steps are

* a step whose result is within `γ k` of a step of the BUG integrator of [CerutiLubich2022] at
  the current rank `r k`, bounded by
  `Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_norm_tail_sq_le` (source: the tail at
  the new time seen from the row and the column space of the old reference),
  with the lower bound `ρ k` of the singular value `σ_{r k - 1}` of the data (indices start at
  `0`) checked on the iterate: `ρ k + Ed k + τ k + ψ k ≤ σ_{r k - 1}(Y k)`, where
  `σ_{r k}(A k) ≤ τ k` and `‖A (k+1) - A k‖₂ ≤ ψ k`;
* a truncation `Y (k+1) = T_{r (k+1)}(Z k)` of a matrix `Z k` with `‖Z k - Y k - ΔA‖ ≤ ζ k`
  (the augmented solution of the rank-adaptive BUG integrator of [CerutiKuschLubich2022], or
  the result of another step), to a lower, the same or a higher rank, with the gap at the new
  rank checked on `Z k`: `ρT k + e ≤ σ_{r (k+1) - 1}(Z k)` and `τT k + 2 e < ρT k` for
  `e = Ea k + ζ k`, `σ_{r (k+1)}(A (k+1)) ≤ τT k`.

On every other step the bound continues with the local error `δ k` and the tail. The sequences
`Ed` (for `‖Y k - T_{r k}(A k)‖`) and `Ea` (for `‖Y k - A k‖`) are any solution of the
inequalities; all hypotheses are on the data at the grid points and on the iterates. If `Ea`
is chosen with `Ea (k+1) ≤ Ea k + δ k`, it is at most the robust bound `Ea 0 + ∑ δ`.

## Main results

* `le_and_le_of_forall_hybrid_step_of_le`,
  `norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step_of_le`: the frame, with certified
  steps that may use both bounds of the old step.
* `le_add_sum_range_of_forall_le_add`: comparison with the sum of the local errors.
* `EckartYoung.le_singularValues_and_le_singularValues_of_norm_sub_truncation_le`: the lower
  bound of `σ_{r-1}` of the data at both ends of a step from the iterate.
* `EckartYoung.norm_truncation_sub_truncation_le_of_add_le_singularValues`: the truncation step
  with the gap checked on the truncated matrix.
* `Exactness.IsBUGIncrementStep.norm_sub_truncation_le_add_of_le_singularValues`: the BUG step
  with the gap checked on the iterate, for a result within `γ` of the BUG result.
* `norm_adaptiveBugRun_sub_truncation_le_and_norm_sub_le`: the run.

## Implementation notes

The step of the rank-adaptive integrator that keeps the rank (Galerkin step in the augmented
bases, truncation to the old rank) enters through its distance `γ k` to the fixed-rank BUG
result from the same iterate; this distance is computable from the augmented core matrix. No
bound of `γ k` in terms of the data is proved here.

## References

* [CerutiLubich2022]
* [CerutiKuschLubich2022]
-/

open Finset Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### Real sequences -/

section Sequences

/-- **Robust and certified steps on one run, with certified steps that use both bounds.** Let
`a (k + 1) ≤ a k + δ k` and `|a k - d k| ≤ s k`. On the steps in `g` let
`d k ≤ Ed k → a k ≤ Ea k → d (k + 1) ≤ Ed (k + 1)`. If
`Ed (k + 1) ≥ Ea k + δ k + s (k + 1)` on the other steps, and on every step
`Ea (k + 1) ≥ Ea k + δ k` or `Ea (k + 1) ≥ Ed (k + 1) + s (k + 1)`, then `d n ≤ Ed n` and
`a n ≤ Ea n` for `n ≤ N`. -/
theorem le_and_le_of_forall_hybrid_step_of_le {N : ℕ} {a d s δ Ea Ed : ℕ → ℝ} {g : ℕ → Prop}
    (ha : ∀ k < N, a (k + 1) ≤ a k + δ k)
    (hda : ∀ k ≤ N, d k ≤ a k + s k) (had : ∀ k ≤ N, a k ≤ d k + s k)
    (hq : ∀ k < N, g k → d k ≤ Ed k → a k ≤ Ea k → d (k + 1) ≤ Ed (k + 1))
    (h0a : a 0 ≤ Ea 0) (h0d : d 0 ≤ Ed 0)
    (hEd : ∀ k < N, g k ∨ Ea k + δ k + s (k + 1) ≤ Ed (k + 1))
    (hEa : ∀ k < N, Ea k + δ k ≤ Ea (k + 1) ∨ Ed (k + 1) + s (k + 1) ≤ Ea (k + 1)) :
    ∀ n ≤ N, d n ≤ Ed n ∧ a n ≤ Ea n := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨h0d, h0a⟩
  | succ k ih =>
    intro hk
    have hk' : k < N := hk
    obtain ⟨hd, hak⟩ := ih hk'.le
    have h1 : a (k + 1) ≤ Ea k + δ k := (ha k hk').trans (by linarith)
    have hd1 : d (k + 1) ≤ Ed (k + 1) := by
      rcases hEd k hk' with hg | h
      · exact hq k hk' hg hd hak
      · exact ((hda (k + 1) hk).trans (by linarith)).trans h
    refine ⟨hd1, ?_⟩
    rcases hEa k hk' with h | h
    · exact h1.trans h
    · exact ((had (k + 1) hk).trans (by linarith)).trans h

/-- **A bound that never exceeds the sum of the local errors.** If `Ea (k + 1) ≤ Ea k + δ k`
for `k < N`, then `Ea n ≤ Ea 0 + ∑ k < n, δ k` for `n ≤ N`. -/
theorem le_add_sum_range_of_forall_le_add {N : ℕ} {Ea δ : ℕ → ℝ}
    (h : ∀ k < N, Ea (k + 1) ≤ Ea k + δ k) : ∀ n ≤ N, Ea n ≤ Ea 0 + ∑ k ∈ range n, δ k := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.sum_range_zero, add_zero]
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ]
    linarith [h k hk, ih (Nat.le_of_succ_le hk)]

end Sequences

/-! ### Matrices -/

section Matrices

open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Robust and certified steps on one run with changing rank, with certified steps that use
both bounds.** Let `A k` be the data and `Y k` the iterates at the grid points, `r k` the ranks,
`X k = T_{r k}(A k)`, and `δ k ≥ ‖Y (k + 1) - Y k - (A (k + 1) - A k)‖` the local errors. On the
steps in `g` let `‖Y k - X k‖ ≤ Ed k → ‖Y k - A k‖ ≤ Ea k → ‖Y (k + 1) - X (k + 1)‖ ≤ Ed (k + 1)`.
If `Ed (k + 1) ≥ Ea k + δ k + ‖A (k + 1) - X (k + 1)‖` on the other steps, and on every step
`Ea (k + 1) ≥ Ea k + δ k` or `Ea (k + 1) ≥ Ed (k + 1) + ‖A (k + 1) - X (k + 1)‖`, then for
`n ≤ N`

  `‖Y n - X n‖ ≤ Ed n`  and  `‖Y n - A n‖ ≤ Ea n`. -/
theorem norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step_of_le {N : ℕ}
    {A Y : ℕ → Matrix m n ℝ} {r : ℕ → ℕ} {δ Ea Ed : ℕ → ℝ} {g : ℕ → Prop}
    (hδ : ∀ k < N, ‖Y (k + 1) - Y k - (A (k + 1) - A k)‖ ≤ δ k)
    (hq : ∀ k < N, g k → ‖Y k - truncation (A k) (r k)‖ ≤ Ed k → ‖Y k - A k‖ ≤ Ea k →
      ‖Y (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ed (k + 1))
    (h0a : ‖Y 0 - A 0‖ ≤ Ea 0) (h0d : ‖Y 0 - truncation (A 0) (r 0)‖ ≤ Ed 0)
    (hEd : ∀ k < N, g k ∨
      Ea k + δ k + ‖A (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ed (k + 1))
    (hEa : ∀ k < N, Ea k + δ k ≤ Ea (k + 1) ∨
      Ed (k + 1) + ‖A (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ea (k + 1)) :
    ∀ n ≤ N, ‖Y n - truncation (A n) (r n)‖ ≤ Ed n ∧ ‖Y n - A n‖ ≤ Ea n := by
  refine le_and_le_of_forall_hybrid_step_of_le (a := fun k => ‖Y k - A k‖)
    (d := fun k => ‖Y k - truncation (A k) (r k)‖)
    (s := fun k => ‖A k - truncation (A k) (r k)‖) (δ := δ) (g := g)
    (fun k hk => ?_) (fun k _ => ?_) (fun k _ => ?_) hq h0a h0d hEd hEa
  · have e : Y (k + 1) - A (k + 1) = Y k - A k + (Y (k + 1) - Y k - (A (k + 1) - A k)) := by
      abel
    change ‖Y (k + 1) - A (k + 1)‖ ≤ ‖Y k - A k‖ + δ k
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hδ k hk))
  · have e : Y k - truncation (A k) (r k) = Y k - A k + (A k - truncation (A k) (r k)) := by
      abel
    change ‖Y k - truncation (A k) (r k)‖ ≤ ‖Y k - A k‖ + ‖A k - truncation (A k) (r k)‖
    rw [e]
    exact norm_add_le _ _
  · have e : Y k - A k = Y k - truncation (A k) (r k) - (A k - truncation (A k) (r k)) := by
      abel
    change ‖Y k - A k‖ ≤ ‖Y k - truncation (A k) (r k)‖ + ‖A k - truncation (A k) (r k)‖
    rw [e]
    exact norm_sub_le _ _

/-- **The lower bound of the gap at both ends of a step from the iterate.** Let
`σ_r(A₀) ≤ τ`, `‖A₁ - A₀‖₂ ≤ ψ` and `‖Y - T_r(A₀)‖ ≤ E`. If
`ρ + E + τ + ψ ≤ σ_{r-1}(Y)` (indices start at `0`), then `ρ ≤ σ_{r-1}(A₀)` and
`ρ ≤ σ_{r-1}(A₁)`. The hypothesis is on the singular value of the iterate `Y`; of the data only
the neglected singular value and the increment enter. -/
theorem EckartYoung.le_singularValues_and_le_singularValues_of_norm_sub_truncation_le {r : ℕ}
    {A₀ A₁ Y : Matrix m n ℝ} {ρ τ ψ E : ℝ}
    (hτ : (toEuclideanLin A₀).singularValues r ≤ τ)
    (hψ : Curvature.specNorm (A₁ - A₀) ≤ ψ) (hE : ‖Y - truncation A₀ r‖ ≤ E)
    (hY : ρ + E + τ + ψ ≤ (toEuclideanLin Y).singularValues (r - 1)) :
    ρ ≤ (toEuclideanLin A₀).singularValues (r - 1) ∧
      ρ ≤ (toEuclideanLin A₁).singularValues (r - 1) := by
  have h2 : Curvature.specNorm (Y - A₀) ≤ E + τ := by
    have e : Y - A₀ = Y - truncation A₀ r + (truncation A₀ r - A₀) := by abel
    rw [e]
    refine (WeylSingular.specNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Curvature.specNorm_le_frob _).trans hE
    · rw [Curvature.specNorm_sub_comm, specNorm_sub_truncation]
      exact hτ
  have h3 := (abs_le.1 (WeylSingular.abs_singularValues_sub_le Y A₀ (r - 1))).2
  have h4 := (abs_le.1 (WeylSingular.abs_singularValues_sub_le A₁ A₀ (r - 1))).1
  have hψ0 : 0 ≤ ψ := (Curvature.specNorm_nonneg _).trans hψ
  exact ⟨by linarith, by linarith⟩

/-- **A truncation step with the gap checked on the truncated matrix.** If `‖Z - A‖ ≤ e`,
`ρ + e ≤ σ_{r-1}(Z)`, `σ_r(A) ≤ τ` (indices start at `0`) and `τ + 2 e < ρ`, then

  `‖T_r(Z) - T_r(A)‖ ≤ (ρ - e) / (ρ - τ - 2 e) e`.

No lower bound of a singular value of `A` is assumed. -/
theorem EckartYoung.norm_truncation_sub_truncation_le_of_add_le_singularValues {r : ℕ}
    {A Z : Matrix m n ℝ} {e ρ τ : ℝ} (he : ‖Z - A‖ ≤ e)
    (hZ : ρ + e ≤ (toEuclideanLin Z).singularValues (r - 1))
    (hτ : (toEuclideanLin A).singularValues r ≤ τ) (hgap : τ + 2 * e < ρ) :
    ‖truncation Z r - truncation A r‖ ≤ (ρ - e) / (ρ - τ - 2 * e) * e := by
  have h := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius Z A (r - 1))).2
  exact norm_truncation_sub_truncation_le_of_norm_sub_le he (by linarith) hτ hgap

/-- **One BUG step against the truncated singular value decomposition with the tail seen from
the old reference as source, the gap checked on the iterate.** Let `0 < r`, `0 < ρ`,
`σ_r(A₀) ≤ τ` (indices start at `0`), `‖A₁ - A₀‖₂ ≤ ψ`, `X₀ = T_r(A₀)`, `X₁ = T_r(A₁)`,
`ΔR = (A₁ - X₁) - (A₀ - X₀)` and

  `‖X₁ - X₀‖₂ ≤ η_X ρ`, `‖ΔR‖₂ ≤ η_R ρ`, `‖X₁ - X₀‖ ≤ η_F ρ`, `‖A₁ - A₀‖ ≤ η_F ρ`.

For a BUG step `(U₀, S₀, V₀) ↦ (U₁, S₁, V₁)` with exact substeps for the increment `A₁ - A₀` and
bases with `r` orthonormal columns let `‖Y₀ - X₀‖ ≤ E ≤ θ ρ` and
`ρ + E + τ + ψ ≤ σ_{r-1}(Y₀)`, and let `Y₁` be a matrix with `‖Y₁ - U₁ S₁ V₁ᵀ‖ ≤ γ`. Then for
`c`, `d`, `β`, `ω` with `1 ≤ (1 - 2 θ) c`, `1 ≤ (1 - (η_F + θ)) d`,
`2 η_X (η_X + θ) d (1 + d) ≤ β²` and `‖(A₁ - X₁) X₀⁺ X₀‖² + ‖X₀ X₀⁺ (A₁ - X₁)‖² ≤ ω²`,

  `‖Y₁ - X₁‖ ≤ (1 + 3/2 η_R + η_X (η_X + θ) d (1 + d) (1 + η_R)²
        + c η_F (η_R + η_X (d (1 + η_R) + 1))) E
      + (1 + β + c η_F (1 + d η_X)) ω + c² η_F² η_R ρ + γ`.

No lower bound of a singular value of the data is assumed. -/
theorem Exactness.IsBUGIncrementStep.norm_sub_truncation_le_add_of_le_singularValues {r : ℕ}
    (hr : 0 < r) {A₀ A₁ Y₁ : Matrix m n ℝ} {ρ τ ψ ηX ηR ηF θ c d β ω γ E : ℝ}
    {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ S₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ}
    (hs : Exactness.IsBUGIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ S₁ V₁) (hρ : 0 < ρ)
    (hτ : (toEuclideanLin A₀).singularValues r ≤ τ)
    (hψ : Curvature.specNorm (A₁ - A₀) ≤ ψ)
    (hY : ρ + E + τ + ψ ≤ (toEuclideanLin (U₀ * S₀ * V₀ᵀ)).singularValues (r - 1))
    (hηX : Curvature.specNorm (truncation A₁ r - truncation A₀ r) ≤ ηX * ρ)
    (hηR : Curvature.specNorm (A₁ - truncation A₁ r - (A₀ - truncation A₀ r)) ≤ ηR * ρ)
    (hηF : ‖truncation A₁ r - truncation A₀ r‖ ≤ ηF * ρ) (hηA : ‖A₁ - A₀‖ ≤ ηF * ρ)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (hE : ‖U₀ * S₀ * V₀ᵀ - truncation A₀ r‖ ≤ E) (hEθ : E ≤ θ * ρ) (hc0 : 0 ≤ c)
    (hc : 1 ≤ (1 - 2 * θ) * c) (hd0 : 0 ≤ d) (hd : 1 ≤ (1 - (ηF + θ)) * d) (hβ0 : 0 ≤ β)
    (hβ : 2 * (ηX * (ηX + θ) * d * (1 + d)) ≤ β ^ 2) (hω0 : 0 ≤ ω)
    (hω : ‖(A₁ - truncation A₁ r) * ((truncation A₀ r).pinv * truncation A₀ r)‖ ^ 2 +
      ‖truncation A₀ r * (truncation A₀ r).pinv * (A₁ - truncation A₁ r)‖ ^ 2 ≤ ω ^ 2)
    (hγ : ‖Y₁ - U₁ * S₁ * V₁ᵀ‖ ≤ γ) :
    ‖Y₁ - truncation A₁ r‖ ≤
      (1 + 3 / 2 * ηR + ηX * (ηX + θ) * d * (1 + d) * (1 + ηR) ^ 2 +
          c * ηF * (ηR + ηX * (d * (1 + ηR) + 1))) * E +
        (1 + β + c * ηF * (1 + d * ηX)) * ω + c ^ 2 * ηF ^ 2 * (ηR * ρ) + γ := by
  obtain ⟨hσ₀, hσ₁⟩ :=
    le_singularValues_and_le_singularValues_of_norm_sub_truncation_le hτ hψ hE hY
  have key := hs.norm_sub_truncation_le_of_norm_tail_sq_le hr hρ hσ₀ hσ₁ hηX hηR hηF hηA hU₀ hV₀
    hU₁ hV₁ (hE.trans hEθ) hc0 hc hd0 hd hβ0 hβ hω0 hω
  have hηX0 : 0 ≤ ηX :=
    nonneg_of_mul_nonneg_left ((Curvature.specNorm_nonneg _).trans hηX) hρ
  have hηR0 : 0 ≤ ηR :=
    nonneg_of_mul_nonneg_left ((Curvature.specNorm_nonneg _).trans hηR) hρ
  have hηF0 : 0 ≤ ηF := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hηF) hρ
  have hθ0 : 0 ≤ θ :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hE.trans hEθ)) hρ
  have hcoef : 0 ≤ 1 + 3 / 2 * ηR + ηX * (ηX + θ) * d * (1 + d) * (1 + ηR) ^ 2 +
      c * ηF * (ηR + ηX * (d * (1 + ηR) + 1)) := by positivity
  have e : Y₁ - truncation A₁ r =
      Y₁ - U₁ * S₁ * V₁ᵀ + (U₁ * S₁ * V₁ᵀ - truncation A₁ r) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := mul_le_mul_of_nonneg_left hE hcoef
  linarith

/-- **A run of a rank-adaptive BUG integrator: robust everywhere, with the tail seen from the old
reference as source where the iterate shows a gap.** Let `A k` be the data and `Y k` the
iterates at the grid points, with local errors `δ k ≥ ‖Y (k + 1) - Y k - (A (k + 1) - A k)‖`,
ranks `r k` and `X k = T_{r k}(A k)`.

On the steps `k` in `g` the rank `r k > 0` does not change and `Y (k + 1)` is within `γ k` of the
result of a step of the BUG integrator of [CerutiLubich2022] from `Y k` with exact substeps and
bases with `r k` orthonormal columns; with `σ_{r k}(A k) ≤ τ k` (indices start at `0`) and
`‖A (k + 1) - A k‖₂ ≤ ψ k` the iterate satisfies `ρ k + Ed k + τ k + ψ k ≤ σ_{r k - 1}(Y k)`,
`ρ k > 0`; the numbers `η_X k`, `η_R k`, `η_F k`, `θ k`, `c k`, `d k`, `β k`, `ω k` are those of
`Exactness.IsBUGIncrementStep.norm_sub_truncation_le_add_of_le_singularValues` at the rank `r k`,
`Ed k ≤ θ k ρ k`, and

  `(1 + 3/2 η_R + η_X (η_X + θ) d (1 + d) (1 + η_R)² + c η_F (η_R + η_X (d (1 + η_R) + 1))) Ed k
      + (1 + β + c η_F (1 + d η_X)) ω k + c² η_F² η_R ρ k + γ k ≤ Ed (k + 1)`.

On the steps `k` in `t` the iterate `Y (k + 1) = T_{r (k + 1)}(Z k)` is a truncation of a matrix
`Z k` with `‖Z k - Y k - (A (k + 1) - A k)‖ ≤ ζ k`; with `e = Ea k + ζ k` and
`σ_{r (k + 1)}(A (k + 1)) ≤ τT k`, `ρT k + e ≤ σ_{r (k + 1) - 1}(Z k)`, `τT k + 2 e < ρT k` and

  `(ρT k - e) / (ρT k - τT k - 2 e) e ≤ Ed (k + 1)`.

On the other steps `Ed (k + 1) ≥ Ea k + δ k + ‖A (k + 1) - X (k + 1)‖`, and on every step
`Ea (k + 1) ≥ Ea k + δ k` or `Ea (k + 1) ≥ Ed (k + 1) + ‖A (k + 1) - X (k + 1)‖`. Then for
`n ≤ N`

  `‖Y n - X n‖ ≤ Ed n`  and  `‖Y n - A n‖ ≤ Ea n`.

No lower bound of a singular value of the data is assumed, and the ranks outside `g` are
arbitrary. With `g` and `t` empty this is the robust bound by the sum of the local errors. -/
theorem norm_adaptiveBugRun_sub_truncation_le_and_norm_sub_le {N : ℕ}
    {A Y Z : ℕ → Matrix m n ℝ} {r : ℕ → ℕ}
    {U₀ U₁ : ∀ k, Matrix m (Fin (r k)) ℝ} {S₀ S₁ : ∀ k, Matrix (Fin (r k)) (Fin (r k)) ℝ}
    {V₀ V₁ : ∀ k, Matrix n (Fin (r k)) ℝ}
    {ρ τ ψ ηX ηR ηF θ c d β ω γ ρT τT ζ δ Ea Ed : ℕ → ℝ} {g t : ℕ → Prop}
    (hδ : ∀ k < N, ‖Y (k + 1) - Y k - (A (k + 1) - A k)‖ ≤ δ k)
    (hr : ∀ k < N, g k → r (k + 1) = r k) (hr0 : ∀ k < N, g k → 0 < r k)
    (hY₀ : ∀ k < N, g k → Y k = U₀ k * S₀ k * (V₀ k)ᵀ)
    (hγ : ∀ k < N, g k → ‖Y (k + 1) - U₁ k * S₁ k * (V₁ k)ᵀ‖ ≤ γ k)
    (hU₀ : ∀ k < N, g k → (U₀ k)ᵀ * U₀ k = 1) (hV₀ : ∀ k < N, g k → (V₀ k)ᵀ * V₀ k = 1)
    (hU₁ : ∀ k < N, g k → (U₁ k)ᵀ * U₁ k = 1) (hV₁ : ∀ k < N, g k → (V₁ k)ᵀ * V₁ k = 1)
    (hs : ∀ k < N, g k → Exactness.IsBUGIncrementStep (A k) (A (k + 1))
      (U₀ k) (S₀ k) (V₀ k) (U₁ k) (S₁ k) (V₁ k))
    (hρ : ∀ k < N, g k → 0 < ρ k)
    (hτ : ∀ k < N, g k → (toEuclideanLin (A k)).singularValues (r k) ≤ τ k)
    (hψ : ∀ k < N, g k → Curvature.specNorm (A (k + 1) - A k) ≤ ψ k)
    (hgap : ∀ k < N, g k → ρ k + Ed k + τ k + ψ k ≤
      (toEuclideanLin (Y k)).singularValues (r k - 1))
    (hηX : ∀ k < N, g k → Curvature.specNorm
      (truncation (A (k + 1)) (r k) - truncation (A k) (r k)) ≤ ηX k * ρ k)
    (hηR : ∀ k < N, g k → Curvature.specNorm (A (k + 1) - truncation (A (k + 1)) (r k) -
      (A k - truncation (A k) (r k))) ≤ ηR k * ρ k)
    (hηF : ∀ k < N, g k →
      ‖truncation (A (k + 1)) (r k) - truncation (A k) (r k)‖ ≤ ηF k * ρ k)
    (hηA : ∀ k < N, g k → ‖A (k + 1) - A k‖ ≤ ηF k * ρ k)
    (htube : ∀ k < N, g k → Ed k ≤ θ k * ρ k)
    (hc0 : ∀ k < N, g k → 0 ≤ c k) (hc : ∀ k < N, g k → 1 ≤ (1 - 2 * θ k) * c k)
    (hd0 : ∀ k < N, g k → 0 ≤ d k) (hd : ∀ k < N, g k → 1 ≤ (1 - (ηF k + θ k)) * d k)
    (hβ0 : ∀ k < N, g k → 0 ≤ β k)
    (hβ : ∀ k < N, g k → 2 * (ηX k * (ηX k + θ k) * d k * (1 + d k)) ≤ β k ^ 2)
    (hω0 : ∀ k < N, g k → 0 ≤ ω k)
    (hω : ∀ k < N, g k → ‖(A (k + 1) - truncation (A (k + 1)) (r k)) *
          ((truncation (A k) (r k)).pinv * truncation (A k) (r k))‖ ^ 2 +
        ‖truncation (A k) (r k) * (truncation (A k) (r k)).pinv *
          (A (k + 1) - truncation (A (k + 1)) (r k))‖ ^ 2 ≤ ω k ^ 2)
    (hB : ∀ k < N, g k →
      (1 + 3 / 2 * ηR k + ηX k * (ηX k + θ k) * d k * (1 + d k) * (1 + ηR k) ^ 2 +
          c k * ηF k * (ηR k + ηX k * (d k * (1 + ηR k) + 1))) * Ed k +
        (1 + β k + c k * ηF k * (1 + d k * ηX k)) * ω k +
        c k ^ 2 * ηF k ^ 2 * (ηR k * ρ k) + γ k ≤ Ed (k + 1))
    (hZ : ∀ k < N, t k → Y (k + 1) = truncation (Z k) (r (k + 1)))
    (hζ : ∀ k < N, t k → ‖Z k - Y k - (A (k + 1) - A k)‖ ≤ ζ k)
    (hτT : ∀ k < N, t k → (toEuclideanLin (A (k + 1))).singularValues (r (k + 1)) ≤ τT k)
    (hρT : ∀ k < N, t k → ρT k + (Ea k + ζ k) ≤
      (toEuclideanLin (Z k)).singularValues (r (k + 1) - 1))
    (hgapT : ∀ k < N, t k → τT k + 2 * (Ea k + ζ k) < ρT k)
    (hT : ∀ k < N, t k →
      (ρT k - (Ea k + ζ k)) / (ρT k - τT k - 2 * (Ea k + ζ k)) * (Ea k + ζ k) ≤ Ed (k + 1))
    (h0a : ‖Y 0 - A 0‖ ≤ Ea 0) (h0d : ‖Y 0 - truncation (A 0) (r 0)‖ ≤ Ed 0)
    (hEd : ∀ k < N, g k ∨ t k ∨
      Ea k + δ k + ‖A (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ed (k + 1))
    (hEa : ∀ k < N, Ea k + δ k ≤ Ea (k + 1) ∨
      Ed (k + 1) + ‖A (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ea (k + 1)) :
    ∀ n ≤ N, ‖Y n - truncation (A n) (r n)‖ ≤ Ed n ∧ ‖Y n - A n‖ ≤ Ea n := by
  refine norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step_of_le
    (g := fun k => g k ∨ t k) hδ (fun k hk hgt hdk hak => ?_) h0a h0d
    (fun k hk => (hEd k hk).elim (fun h => Or.inl (Or.inl h))
      (fun h => h.elim (fun h' => Or.inl (Or.inr h')) Or.inr)) hEa
  rcases hgt with hg | ht
  · have hgapk : ρ k + Ed k + τ k + ψ k ≤
        (toEuclideanLin (U₀ k * S₀ k * (V₀ k)ᵀ)).singularValues (r k - 1) := by
      rw [← hY₀ k hk hg]
      exact hgap k hk hg
    have hd' : ‖U₀ k * S₀ k * (V₀ k)ᵀ - truncation (A k) (r k)‖ ≤ Ed k := by
      rw [← hY₀ k hk hg]
      exact hdk
    have key := (hs k hk hg).norm_sub_truncation_le_add_of_le_singularValues (hr0 k hk hg)
      (hρ k hk hg) (hτ k hk hg) (hψ k hk hg) hgapk (hηX k hk hg) (hηR k hk hg) (hηF k hk hg)
      (hηA k hk hg) (hU₀ k hk hg) (hV₀ k hk hg) (hU₁ k hk hg) (hV₁ k hk hg) hd'
      (htube k hk hg) (hc0 k hk hg) (hc k hk hg) (hd0 k hk hg) (hd k hk hg) (hβ0 k hk hg)
      (hβ k hk hg) (hω0 k hk hg) (hω k hk hg) (hγ k hk hg)
    rw [hr k hk hg]
    exact key.trans (hB k hk hg)
  · have he : ‖Z k - A (k + 1)‖ ≤ Ea k + ζ k := by
      have e : Z k - A (k + 1) = Y k - A k + (Z k - Y k - (A (k + 1) - A k)) := by abel
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add hak (hζ k hk ht))
    rw [hZ k hk ht]
    exact (norm_truncation_sub_truncation_le_of_add_le_singularValues he (hρT k hk ht)
      (hτT k hk ht) (hgapT k hk ht)).trans (hT k hk ht)

end Matrices

/-! ### Examples -/

namespace BUGAdaptiveQuasiOptimalityExamples

open scoped LeanDLRA.Frobenius
open BUGQuasiOptimalityExamples EckartYoung Curvature

/-- The unit vector `u = (399/401, 40/401)` as a column. -/
private noncomputable def u₂ : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of fun i _ => ![399 / 401, 40 / 401] i

/-- The data at the last grid point, `33/32 u uᵀ + 1/32 (1 - u uᵀ)` for `u = (399/401, 40/401)`:
the singular vectors of `diag(33/32, 1/16)` are rotated. -/
private noncomputable def A₂ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 32 + 159201 / 160801, 15960 / 160801; 15960 / 160801, 1 / 32 + 1600 / 160801]

/-- The rank-one matrix `33/32 u uᵀ`. -/
private noncomputable def X₂ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![33 / 32 * (159201 / 160801), 33 / 32 * (15960 / 160801);
    33 / 32 * (15960 / 160801), 33 / 32 * (1600 / 160801)]

/-- The Frobenius norm of a `2 × 2` matrix from its entries. -/
private theorem norm_le_of_sq_le {M : Matrix (Fin 2) (Fin 2) ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : M 0 0 ^ 2 + M 0 1 ^ 2 + (M 1 0 ^ 2 + M 1 1 ^ 2) ≤ b ^ 2) : ‖M‖ ≤ b := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero).mp ?_
  rw [frob_sq]
  simpa [Fin.sum_univ_two] using h

/-- `σ₀(diag(a, w)) ≥ a`: the matrix maps the first unit vector to `a` times itself. -/
private theorem le_singularValues_dg (a w : ℝ) :
    a ≤ (toEuclideanLin (dg a w)).singularValues 0 := by
  rw [← specNorm_eq_singularValues_zero]
  have hs : toEuclideanLin (dg a w) (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 a := by
    ext i
    fin_cases i <;> simp [dg, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have h := norm_toEuclideanLin_le (dg a w) (EuclideanSpace.single 0 1)
  rw [hs] at h
  exact (le_abs_self a).trans (by simpa using h)

/-- A unit vector orthogonal to `(-q, p)` has the outer product of `(p, q)`. -/
private theorem mul_eq_of_mul_sub_mul_eq_zero {p q x y : ℝ} (hpq : p ^ 2 + q ^ 2 = 1)
    (hn : x ^ 2 + y ^ 2 = 1) (h : p * y - q * x = 0) :
    x * x = p * p ∧ x * y = p * q ∧ y * y = q * q := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(p * y + q * x)) * h - x ^ 2 * hpq + p ^ 2 * hn
  · linear_combination (p * x - q * y) * h - x * y * hpq + p * q * hn
  · linear_combination (p * y + q * x) * h - y ^ 2 * hpq + q ^ 2 * hn

/-- **The rank-one truncation of a `2 × 2` matrix with rotated singular vectors.** If
`Aᵀ A = c v vᵀ + w v⊥ v⊥ᵀ` for the unit vector `v = (p, q)` and `w < σ₀(A)²`, then
`T₁(A) = A v vᵀ`: the top right singular vector is orthogonal to `v⊥ = (-q, p)`. -/
private theorem truncation_one_eq_mul {A : Matrix (Fin 2) (Fin 2) ℝ} {p q c w : ℝ}
    (hpq : p ^ 2 + q ^ 2 = 1)
    (hAA : Aᵀ * A = !![c * (p * p) + w * (q * q), (c - w) * (p * q);
      (c - w) * (p * q), c * (q * q) + w * (p * p)])
    (hσ : w < (toEuclideanLin A).singularValues 0 ^ 2) :
    truncation A 1 = A * !![p * p, p * q; p * q, q * q] := by
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
  have h0 := congrFun hE 0
  have h1 := congrFun hE 1
  simp only [mulVec, dotProduct, Fin.isValue, of_apply, cons_val', cons_val_fin_one,
    cons_val_one, Fin.sum_univ_two, cons_val_zero, Pi.smul_apply, smul_eq_mul] at h0 h1
  have hσ' : w < (toEuclideanLin A).singularValues ↑i0 ^ 2 := hσ
  have hperp : p * EckartYoung.rightSingularVectors A i0 1 -
      q * EckartYoung.rightSingularVectors A i0 0 = 0 := by
    have hm : ((toEuclideanLin A).singularValues ↑i0 ^ 2 - w) *
        (p * EckartYoung.rightSingularVectors A i0 1 -
          q * EckartYoung.rightSingularVectors A i0 0) = 0 := by
      linear_combination (-p) * h1 + q * h0 +
        (w * (p * EckartYoung.rightSingularVectors A i0 1 -
          q * EckartYoung.rightSingularVectors A i0 0)) * hpq
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · exact h
  obtain ⟨h00, h01, h11⟩ := mul_eq_of_mul_sub_mul_eq_zero hpq hn hperp
  have hM : (Matrix.of fun a b => EckartYoung.rightSingularVectors A i0 a *
      EckartYoung.rightSingularVectors A i0 b) = !![p * p, p * q; p * q, q * q] := by
    ext a b
    fin_cases a <;> fin_cases b
    · exact h00
    · exact h01
    · exact (mul_comm _ _).trans h01
    · exact h11
  unfold EckartYoung.truncation
  rw [Matrix.mul_assoc, hP, hM]

/-- The rank-one truncation of `diag(a, w)`, `a ≥ 0`, `w² < a²`, is `diag(a, 0)`. -/
private theorem truncation_dg {a w : ℝ} (ha : 0 ≤ a) (hw : w ^ 2 < a ^ 2) :
    truncation (dg a w) 1 = dg a 0 := by
  have h := truncation_one_eq_mul (A := dg a w) (p := 1) (q := 0) (c := a ^ 2) (w := w ^ 2)
    (by norm_num)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two, pow_two])
    (hw.trans_le (pow_le_pow_left₀ ha (le_singularValues_dg a w) 2))
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

private theorem truncation_A₀ : truncation (dg 1 (1 / 16)) 2 = dg 1 (1 / 16) :=
  truncation_eq_self (Matrix.rank_le_width _)

private theorem truncation_Z₀ : truncation (dg 1 (1 / 16)) 1 = dg 1 0 :=
  truncation_dg (by norm_num) (by norm_num)

private theorem truncation_A₁ : truncation (dg (33 / 32) (1 / 16)) 1 = dg (33 / 32) 0 :=
  truncation_dg (by norm_num) (by norm_num)

private theorem norm_A₂_sub_le : ‖A₂ - dg (33 / 32) (1 / 16)‖ ≤ 3 / 20 :=
  norm_le_of_sq_le (by norm_num) (by norm_num [A₂, dg])

/-- `σ₀(A₂) ≥ 3/4`, from `σ₀(diag(33/32, 1/16)) ≥ 33/32` and the distance of the two matrices. -/
private theorem le_singularValues_A₂ : (3 / 4 : ℝ) ≤ (toEuclideanLin A₂).singularValues 0 := by
  have h := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius A₂
    (dg (33 / 32) (1 / 16)) 0)).1
  have h1 := le_singularValues_dg (33 / 32) (1 / 16)
  have h2 := norm_A₂_sub_le
  linarith

/-- The rank-one truncation of `A₂` is `33/32 u uᵀ`. -/
private theorem truncation_A₂ : truncation A₂ 1 = X₂ := by
  have h := truncation_one_eq_mul (A := A₂) (p := 399 / 401) (q := 40 / 401)
    (c := (33 / 32) ^ 2) (w := (1 / 32) ^ 2) (by norm_num)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [A₂, Matrix.mul_apply, Fin.sum_univ_two])
    (lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) le_singularValues_A₂ 2))
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A₂, X₂, Matrix.mul_apply, Fin.sum_univ_two]

private theorem singularValues_one_A₁_le :
    (toEuclideanLin (dg (33 / 32) (1 / 16))).singularValues 1 ≤ 1 / 16 := by
  rw [← specNorm_sub_truncation, truncation_A₁]
  exact (specNorm_le_frob _).trans (norm_le_of_sq_le (by norm_num) (by norm_num [dg]))

private theorem u₂_orth : u₂ᵀ * u₂ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [u₂, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]

private theorem e₁_mul_sc_mul (s : ℝ) : e₁ * sc s * e₁ᵀ = dg s 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, dg, sc, Matrix.mul_apply]

/-- A BUG step with exact substeps for the data `diag(33/32, 1/16) ↦ A₂` from `Y = diag(1, 0)`:
both bases turn from the first unit vector to `u`. -/
private theorem isBUGIncrementStep_rot :
    Exactness.IsBUGIncrementStep (dg (33 / 32) (1 / 16)) A₂ e₁ (sc 1) e₁ u₂
      (sc (160751 / 160801)) u₂ := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A₂, dg, e₁, sc, u₂, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
  · rw [sc_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A₂, dg, e₁, sc, u₂, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
  · ext i j
    fin_cases i; fin_cases j
    norm_num [A₂, dg, e₁, sc, u₂, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]

/-- The projectors of a generalized inverse `G` of `diag(a, 0)` with symmetric projectors of
trace one are `diag(1, 0)`. -/
private theorem mul_eq_dg_of_trace {a : ℝ} {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hc : (dg a 0 * G)ᵀ = dg a 0 * G) (hr : (G * dg a 0)ᵀ = G * dg a 0)
    (htc : trace (dg a 0 * G) = 1) (htr : trace (G * dg a 0) = 1) :
    dg a 0 * G = dg 1 0 ∧ G * dg a 0 = dg 1 0 := by
  have e1 : dg a 0 * G = !![a * G 0 0, a * G 0 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : G * dg a 0 = !![G 0 0 * a, 0; G 1 0 * a, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e1] at hc htc
  rw [e2] at hr htr
  rw [Matrix.trace_fin_two] at htc htr
  have h00 : a * G 0 0 = 1 := by simpa using htc
  have h00' : G 0 0 * a = 1 := by simpa using htr
  have h01 : a * G 0 1 = 0 := by simpa using congrFun (congrFun hc 1) 0
  have h10 : G 1 0 * a = 0 := by simpa using congrFun (congrFun hr 0) 1
  exact ⟨by rw [e1, h00, h01]; rfl, by rw [e2, h00', h10]; rfl⟩

/-- The tail `1/32 (1 - u uᵀ)` at the last grid point seen from the row and the column space of
the old reference `diag(33/32, 0)`: it is not zero, because the singular vectors rotate. -/
private theorem norm_tail_mul_pinv_mul_sq_add_le :
    ‖(A₂ - truncation A₂ 1) * ((truncation (dg (33 / 32) (1 / 16)) 1).pinv *
          truncation (dg (33 / 32) (1 / 16)) 1)‖ ^ 2 +
        ‖truncation (dg (33 / 32) (1 / 16)) 1 * (truncation (dg (33 / 32) (1 / 16)) 1).pinv *
          (A₂ - truncation A₂ 1)‖ ^ 2 ≤ ((1 : ℝ) / 200) ^ 2 := by
  obtain ⟨-, -, -, htc, htr⟩ := sub_truncation_mul_pinv_eq_zero_and_specNorm_pinv_le
    (r := 1) one_pos one_pos ((by norm_num : (1 : ℝ) ≤ 33 / 32).trans
      (le_singularValues_dg (33 / 32) (1 / 16)))
  rw [truncation_A₁] at htc htr ⊢
  obtain ⟨hP, hQ⟩ := mul_eq_dg_of_trace (Matrix.transpose_mul_pinv _)
    (Matrix.transpose_pinv_mul _) (htc.trans Nat.cast_one) (htr.trans Nat.cast_one)
  rw [hP, hQ, truncation_A₂, frob_sq, frob_sq]
  norm_num [A₂, X₂, dg, Matrix.mul_apply, Fin.sum_univ_two]

private theorem specNorm_A₂_sub_le : specNorm (A₂ - dg (33 / 32) (1 / 16)) ≤ 3 / 20 :=
  (specNorm_le_frob _).trans norm_A₂_sub_le

private theorem norm_truncation_sub_le :
    ‖truncation A₂ 1 - truncation (dg (33 / 32) (1 / 16)) 1‖ ≤ 1 / 5 * (3 / 4) := by
  rw [truncation_A₂, truncation_A₁]
  exact norm_le_of_sq_le (by norm_num) (by norm_num [X₂, dg])

private theorem specNorm_tail_sub_le :
    specNorm (A₂ - truncation A₂ 1 -
      (dg (33 / 32) (1 / 16) - truncation (dg (33 / 32) (1 / 16)) 1)) ≤ 1 / 20 * (3 / 4) := by
  rw [truncation_A₂, truncation_A₁]
  exact (specNorm_le_frob _).trans (norm_le_of_sq_le (by norm_num) (by norm_num [A₂, X₂, dg]))

private theorem norm_tail₂_le : ‖A₂ - truncation A₂ 1‖ ≤ 1 / 32 := by
  rw [truncation_A₂]
  exact norm_le_of_sq_le (by norm_num) (by norm_num [A₂, X₂])

private theorem norm_step₀_le :
    ‖dg 1 0 - dg 1 (1 / 16) - (dg (33 / 32) (1 / 16) - dg 1 (1 / 16))‖ ≤ 9 / 128 :=
  norm_le_of_sq_le (by norm_num) (by norm_num [dg])

private theorem norm_step₁_le :
    ‖u₂ * sc (160751 / 160801) * u₂ᵀ - dg 1 0 - (A₂ - dg (33 / 32) (1 / 16))‖ ≤ 1 / 16 :=
  norm_le_of_sq_le (by norm_num) (by norm_num [A₂, dg, sc, u₂, Matrix.mul_apply, Function.swap])

private theorem norm_Z₀_le :
    ‖dg 1 (1 / 16) - dg 1 (1 / 16) - (dg (33 / 32) (1 / 16) - dg 1 (1 / 16))‖ ≤ 1 / 32 :=
  norm_le_of_sq_le (by norm_num) (by norm_num [dg])

/-- The ranks of the example: `2` at the first grid point, then `1`. -/
private def rk : ℕ → ℕ
  | 0 => 2
  | _ + 1 => 1

/-- The data of the example. -/
private noncomputable def Ak : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => dg 1 (1 / 16)
  | 1 => dg (33 / 32) (1 / 16)
  | _ + 2 => A₂

/-- The iterates of the example. -/
private noncomputable def Yk : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => dg 1 (1 / 16)
  | 1 => dg 1 0
  | _ + 2 => u₂ * sc (160751 / 160801) * u₂ᵀ

/-- The old bases of the BUG step of the example. -/
private def U₀k : ∀ k : ℕ, Matrix (Fin 2) (Fin (rk k)) ℝ
  | 0 => 0
  | _ + 1 => e₁

/-- The new bases of the BUG step of the example. -/
private noncomputable def U₁k : ∀ k : ℕ, Matrix (Fin 2) (Fin (rk k)) ℝ
  | 0 => 0
  | _ + 1 => u₂

/-- The old core of the BUG step of the example. -/
private def S₀k : ∀ k : ℕ, Matrix (Fin (rk k)) (Fin (rk k)) ℝ
  | 0 => 0
  | _ + 1 => sc 1

/-- The new core of the BUG step of the example. -/
private noncomputable def S₁k : ∀ k : ℕ, Matrix (Fin (rk k)) (Fin (rk k)) ℝ
  | 0 => 0
  | _ + 1 => sc (160751 / 160801)

/-- The local errors of the example. -/
private noncomputable def δk : ℕ → ℝ
  | 0 => 9 / 128
  | _ + 1 => 1 / 16

/-- The bound of the distance to the truncation in the example. -/
private noncomputable def Edk : ℕ → ℝ
  | 0 => 0
  | 1 => 5 / 144
  | _ + 2 => 1 / 16

/-- The bound of the error in the example. -/
private noncomputable def Eak : ℕ → ℝ
  | 0 => 0
  | 1 => 9 / 128
  | _ + 2 => 3 / 32

/-- **Non-vacuity of `norm_adaptiveBugRun_sub_truncation_le_and_norm_sub_le`** (and of
`Exactness.IsBUGIncrementStep.norm_sub_truncation_le_add_of_le_singularValues`,
`EckartYoung.norm_truncation_sub_truncation_le_of_add_le_singularValues`,
`EckartYoung.le_singularValues_and_le_singularValues_of_norm_sub_truncation_le`,
`norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step_of_le` and
`le_and_le_of_forall_hybrid_step_of_le`): two steps with a change of the rank and rotating
singular vectors. The data are `diag(1, 1/16)`, `diag(33/32, 1/16)` and
`33/32 u uᵀ + 1/32 (1 - u uᵀ)` with `u = (399/401, 40/401)`. The iterate `Y 0 = diag(1, 1/16)`
has rank two; the first step is the truncation of `Z 0 = diag(1, 1/16)` to rank one
(`ζ = 1/32`, `ρT = 31/32`, `τT = 1/16`), which gives `Ed 1 = 5/144`. The second step is a BUG
step at rank one whose bases turn from the first unit vector to `u`, certified from the
singular value of `Y 1 = diag(1, 0)` with `ρ = 3/4`, `τ = 1/16`, `ψ = 3/20`, `η_X = η_F = 1/5`,
`η_R = θ = 1/20`, `c = 5/4`, `d = 3/2`, `β = 5/8`, and the source `ω = 1/200` is not zero. The
bounds are `Ed = 0, 5/144, 1/16` and `Ea = 0, 9/128, 3/32`; the last one uses the bound of the
distance to the truncation and the tail. -/
example : ∀ n ≤ 2, ‖Yk n - truncation (Ak n) (rk n)‖ ≤ Edk n ∧ ‖Yk n - Ak n‖ ≤ Eak n :=
  norm_adaptiveBugRun_sub_truncation_le_and_norm_sub_le (N := 2) (A := Ak) (Y := Yk)
    (Z := fun _ => dg 1 (1 / 16)) (r := rk) (U₀ := U₀k) (U₁ := U₁k) (S₀ := S₀k) (S₁ := S₁k)
    (V₀ := U₀k) (V₁ := U₁k) (ρ := fun _ => 3 / 4) (τ := fun _ => 1 / 16)
    (ψ := fun _ => 3 / 20) (ηX := fun _ => 1 / 5) (ηR := fun _ => 1 / 20)
    (ηF := fun _ => 1 / 5) (θ := fun _ => 1 / 20) (c := fun _ => 5 / 4) (d := fun _ => 3 / 2)
    (β := fun _ => 5 / 8) (ω := fun _ => 1 / 200) (γ := fun _ => 0) (ρT := fun _ => 31 / 32)
    (τT := fun _ => 1 / 16) (ζ := fun _ => 1 / 32) (δ := δk) (Ea := Eak) (Ed := Edk)
    (g := fun k => k = 1) (t := fun k => k = 0)
    (hδ := fun k hk => by
      interval_cases k
      · exact norm_step₀_le
      · exact norm_step₁_le)
    (hr := fun k _ hg => by subst hg; rfl)
    (hr0 := fun k _ hg => by subst hg; exact Nat.one_pos)
    (hY₀ := fun k _ hg => by subst hg; exact (e₁_mul_sc_mul 1).symm)
    (hγ := fun k _ hg => by
      subst hg
      change ‖u₂ * sc (160751 / 160801) * u₂ᵀ - u₂ * sc (160751 / 160801) * u₂ᵀ‖ ≤ (0 : ℝ)
      rw [sub_self, norm_zero])
    (hU₀ := fun k _ hg => by subst hg; exact e₁_orth)
    (hV₀ := fun k _ hg => by subst hg; exact e₁_orth)
    (hU₁ := fun k _ hg => by subst hg; exact u₂_orth)
    (hV₁ := fun k _ hg => by subst hg; exact u₂_orth)
    (hs := fun k _ hg => by subst hg; exact isBUGIncrementStep_rot)
    (hρ := fun _ _ _ => by norm_num)
    (hτ := fun k _ hg => by subst hg; exact singularValues_one_A₁_le)
    (hψ := fun k _ hg => by subst hg; exact specNorm_A₂_sub_le)
    (hgap := fun k _ hg => by
      subst hg
      exact (by norm_num : (3 / 4 : ℝ) + 5 / 144 + 1 / 16 + 3 / 20 ≤ 1).trans
        (le_singularValues_dg 1 0))
    (hηX := fun k _ hg => by
      subst hg
      exact (specNorm_le_frob _).trans norm_truncation_sub_le)
    (hηR := fun k _ hg => by subst hg; exact specNorm_tail_sub_le)
    (hηF := fun k _ hg => by subst hg; exact norm_truncation_sub_le)
    (hηA := fun k _ hg => by
      subst hg
      exact norm_A₂_sub_le.trans (by norm_num))
    (htube := fun k _ hg => by
      subst hg
      change (5 / 144 : ℝ) ≤ 1 / 20 * (3 / 4)
      norm_num)
    (hc0 := fun _ _ _ => by norm_num) (hc := fun _ _ _ => by norm_num)
    (hd0 := fun _ _ _ => by norm_num) (hd := fun _ _ _ => by norm_num)
    (hβ0 := fun _ _ _ => by norm_num) (hβ := fun _ _ _ => by norm_num)
    (hω0 := fun _ _ _ => by norm_num)
    (hω := fun k _ hg => by subst hg; exact norm_tail_mul_pinv_mul_sq_add_le)
    (hB := fun k _ hg => by
      subst hg
      change (1 + 3 / 2 * (1 / 20) + 1 / 5 * (1 / 5 + 1 / 20) * (3 / 2) * (1 + 3 / 2) *
            (1 + 1 / 20) ^ 2 + 5 / 4 * (1 / 5) * (1 / 20 + 1 / 5 * (3 / 2 * (1 + 1 / 20) + 1))) *
          (5 / 144) + (1 + 5 / 8 + 5 / 4 * (1 / 5) * (1 + 3 / 2 * (1 / 5))) * (1 / 200) +
          (5 / 4) ^ 2 * (1 / 5) ^ 2 * (1 / 20 * (3 / 4)) + 0 ≤ (1 / 16 : ℝ)
      norm_num)
    (hZ := fun k _ ht => by subst ht; exact truncation_Z₀.symm)
    (hζ := fun k _ ht => by subst ht; exact norm_Z₀_le)
    (hτT := fun k _ ht => by subst ht; exact singularValues_one_A₁_le)
    (hρT := fun k _ ht => by
      subst ht
      exact (by norm_num : (31 / 32 : ℝ) + (0 + 1 / 32) ≤ 1).trans
        (le_singularValues_dg 1 (1 / 16)))
    (hgapT := fun k _ ht => by
      subst ht
      change (1 / 16 : ℝ) + 2 * (0 + 1 / 32) < 31 / 32
      norm_num)
    (hT := fun k _ ht => by
      subst ht
      change (31 / 32 - (0 + 1 / 32)) / (31 / 32 - 1 / 16 - 2 * (0 + 1 / 32)) * (0 + 1 / 32) ≤
        (5 / 144 : ℝ)
      norm_num)
    (h0a := by
      change ‖dg 1 (1 / 16) - dg 1 (1 / 16)‖ ≤ (0 : ℝ)
      rw [sub_self, norm_zero])
    (h0d := by
      change ‖dg 1 (1 / 16) - truncation (dg 1 (1 / 16)) 2‖ ≤ (0 : ℝ)
      rw [truncation_A₀, sub_self, norm_zero])
    (hEd := fun k hk => by
      interval_cases k
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl)
    (hEa := fun k hk => by
      interval_cases k
      · refine Or.inl ?_
        change (0 : ℝ) + 9 / 128 ≤ 9 / 128
        norm_num
      · refine Or.inr ?_
        change (1 / 16 : ℝ) + ‖A₂ - truncation A₂ 1‖ ≤ 3 / 32
        linarith [norm_tail₂_le])

/-- **Non-vacuity of `le_add_sum_range_of_forall_le_add`**: the bound `Ea = 0, 9/128, 3/32` of
the example above and its local errors `9/128`, `1/16`. -/
example : ∀ n ≤ 2, Eak n ≤ Eak 0 + ∑ k ∈ range n, δk k :=
  le_add_sum_range_of_forall_le_add fun k hk => by
    interval_cases k
    · change (9 / 128 : ℝ) ≤ 0 + 9 / 128
      norm_num
    · change (3 / 32 : ℝ) ≤ 9 / 128 + 1 / 16
      norm_num

end BUGAdaptiveQuasiOptimalityExamples

end LeanDLRA
