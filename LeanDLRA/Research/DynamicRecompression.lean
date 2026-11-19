import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.WeylSingular

/-!
# Tolerance truncation in time stepping: rank freeze and dynamic recompression

Let `T_ϑ` be the truncated singular value decomposition at the tolerance rank
(`EckartYoung.truncation` at the rank `epsRank ϑ`, the truncation of the rank-adaptive BUG
integrator [CerutiKuschLubich2022]), and let `rank_ε` be the `ε`-rank (`epsRank`). For a stationary
iteration the recompression lemma of Bachmayr and Dahmen (arXiv 1304.7796; for matrices it is
`epsRank_sandwich`) says that truncating an approximation with error `ζ` at a tolerance `θ ≥ ζ`
gives the error `θ + ζ` and a rank between `rank_{θ+ζ}` and `rank_{θ-ζ}` of the exact object.
This file treats the two sides of the same question for a time-stepping method
`Y_{k+1} = T_ϑ(Z_k)`.

## Rank freeze

If the matrix `Z_k` that is truncated lies within `ϑ` of the previous iterate `Y_k`, the rank
does not grow (`rank_truncation_epsRank_le_of_norm_sub_le`): `Y_k` itself is a competitor within the
tolerance. For a step-truncation method or an augmented BUG step, `‖Z_k - Y_k‖` is at most the
step size times a bound of the vector field. Hence a tolerance that does not decrease with the
step size freezes the rank (`rank_le_rank_zero_of_forall_norm_sub_le`), and the error is at least
the distance of the exact solution to the matrices of the initial rank
(`distLR_le_norm_sub_of_forall_norm_sub_le`). For step truncation of exact increments the error
is at most the sum of the tolerances (`norm_sub_le_add_mul_of_stepTruncation`), and this is
attained: `norm_sub_eq_mul_of_stepTruncation` (start at zero, any direction) and
`exists_stepTruncation_norm_sub_eq_mul` (start `diag(1, 0)`, a spectral gap of size one) give
`‖A_k - Y_k‖ = k ϑ`. The term `n ϑ` of the error bound of [CerutiKuschLubich2022] is therefore
sharp with constant one for methods that decide from the truncated iterate alone.

## Dynamic recompression

Let `V_{k+1} = V_k + h F_k(W_k)` be an explicit Euler sequence whose field is evaluated at
matrices `W_k` with `‖W_k - V_k‖ ≤ η_k` (in the application `W_k` is the iterate `Y_k` plus a
reconstruction of the remainder `V_k - Y_k` from a linear sketch, and `V_k` is never formed), and
let `Y_{k+1} = T_θ(W_k + h F_k(W_k))`. Then `norm_sub_le_and_epsRank_le_rank_and_rank_le_epsRank`
gives, with `ζ_k = η_k + E_{k+1}` and `E` any solution of
`E_{k+1} ≥ (1 + h L) E_k + h L η_k + δ_k`, `E_0 ≥ ‖V_0 - A_0‖`,

  `‖Y_{k+1} - A_{k+1}‖ ≤ θ + ζ_k`,  `rank_{θ+ζ_k}(A_{k+1}) ≤ rank Y_{k+1} ≤ rank_{θ-ζ_k}(A_{k+1})`.

The tolerance `θ` enters once and is not multiplied by the number of steps; the reconstruction
errors `η_k` enter through the Lipschitz constant only.
-/

open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.DynamicRecompression

open LeanDLRA.EckartYoung

section Freeze

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The truncated singular value decomposition at the tolerance rank is within the tolerance. -/
theorem norm_truncation_epsRank_sub_le {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (X : Matrix m n ℝ) :
    ‖truncation X (epsRank ϑ X) - X‖ ≤ ϑ := by
  rw [norm_sub_rev, ← WeylSingular.tailNorm_eq_norm_sub_truncation,
    WeylSingular.tailNorm_eq_infDist]
  exact distLR_epsRank_le hϑ

/-- The truncated singular value decomposition at the tolerance rank has the tolerance rank. -/
theorem rank_truncation_epsRank {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (X : Matrix m n ℝ) :
    (truncation X (epsRank ϑ X)).rank = epsRank ϑ X := by
  refine le_antisymm (rank_truncation_le X _) (epsRank_le_of_norm_sub_le le_rfl ?_)
  rw [norm_sub_rev]
  exact norm_truncation_epsRank_sub_le hϑ X

/-- **A tolerance truncation does not raise the rank of a nearby matrix.** If `Z` is within the
tolerance `ϑ` of `Y`, the truncated singular value decomposition of `Z` at the tolerance `ϑ` has
at most the rank of `Y`. -/
theorem rank_truncation_epsRank_le_of_norm_sub_le {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {Y Z : Matrix m n ℝ}
    (h : ‖Z - Y‖ ≤ ϑ) : (truncation Z (epsRank ϑ Z)).rank ≤ Y.rank := by
  rw [rank_truncation_epsRank hϑ]
  exact epsRank_le_of_norm_sub_le le_rfl h

/-- **Rank freeze.** If every step truncates, at the tolerance `ϑ`, a matrix `Z_k` within `ϑ` of
the previous iterate, the rank never exceeds the initial rank. -/
theorem rank_le_rank_zero_of_forall_norm_sub_le {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {N : ℕ}
    {Y Z : ℕ → Matrix m n ℝ} (hY : ∀ k < N, Y (k + 1) = truncation (Z k) (epsRank ϑ (Z k)))
    (hZ : ∀ k < N, ‖Z k - Y k‖ ≤ ϑ) : ∀ k ≤ N, (Y k).rank ≤ (Y 0).rank := by
  intro k
  induction k with
  | zero => exact fun _ => le_rfl
  | succ k ih =>
    intro hk
    rw [hY k (Nat.lt_of_succ_le hk)]
    exact (rank_truncation_epsRank_le_of_norm_sub_le hϑ (hZ k (Nat.lt_of_succ_le hk))).trans
      (ih (Nat.le_of_succ_le hk))

/-- **Lower bound of the error under a rank freeze.** Under the hypotheses of
`rank_le_rank_zero_of_forall_norm_sub_le` the distance of the iterate to any matrix `A` is at
least the distance of `A` to the matrices of the initial rank. -/
theorem distLR_le_norm_sub_of_forall_norm_sub_le {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {N : ℕ}
    {Y Z : ℕ → Matrix m n ℝ} (hY : ∀ k < N, Y (k + 1) = truncation (Z k) (epsRank ϑ (Z k)))
    (hZ : ∀ k < N, ‖Z k - Y k‖ ≤ ϑ) (A : Matrix m n ℝ) {k : ℕ} (hk : k ≤ N) :
    distLR (Y 0).rank A ≤ ‖A - Y k‖ :=
  distLR_le_norm_sub (rank_le_rank_zero_of_forall_norm_sub_le hϑ hY hZ k hk)

/-- **Step truncation of exact increments: the truncation errors add up at most.**
For `Y_{k+1} = T_ϑ(Y_k + A_{k+1} - A_k)` the error after `k` steps is at most the initial error
plus `k ϑ`. -/
theorem norm_sub_le_add_mul_of_stepTruncation {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {N : ℕ}
    {A Y : ℕ → Matrix m n ℝ} (hY : ∀ k < N, Y (k + 1) = truncation (Y k + (A (k + 1) - A k))
          (epsRank ϑ (Y k + (A (k + 1) - A k)))) :
    ∀ k ≤ N, ‖A k - Y k‖ ≤ ‖A 0 - Y 0‖ + k * ϑ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := norm_truncation_epsRank_sub_le hϑ (Y k + (A (k + 1) - A k))
    have h2 : A (k + 1) - Y (k + 1) = (A k - Y k)
        - (truncation (Y k + (A (k + 1) - A k))
              (epsRank ϑ (Y k + (A (k + 1) - A k))) - (Y k + (A (k + 1) - A k))) := by
      rw [hY k (Nat.lt_of_succ_le hk)]; abel
    have h3 := norm_sub_le (A k - Y k)
      (truncation (Y k + (A (k + 1) - A k))
            (epsRank ϑ (Y k + (A (k + 1) - A k))) - (Y k + (A (k + 1) - A k)))
    have h4 := ih (Nat.le_of_succ_le hk)
    rw [h2]
    push_cast
    linarith

/-- **The sum of the tolerances is attained, start at zero.** For the data `A_k = k ϑ E` with
`‖E‖ = 1` and the start `Y_0 = 0`, step truncation of the exact increments at the tolerance `ϑ`
stays at zero, and the error after `k` steps is exactly `k ϑ`. -/
theorem norm_sub_eq_mul_of_stepTruncation {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {E : Matrix m n ℝ} (hE : ‖E‖ = 1)
    {A Y : ℕ → Matrix m n ℝ} (hA : ∀ k : ℕ, A k = ((k : ℝ) * ϑ) • E) (hY0 : Y 0 = 0)
    (hY : ∀ k, Y (k + 1) = truncation (Y k + (A (k + 1) - A k))
          (epsRank ϑ (Y k + (A (k + 1) - A k)))) :
    ∀ k : ℕ, Y k = 0 ∧ ‖A k - Y k‖ = k * ϑ := by
  have hzero : ∀ k : ℕ, Y k = 0 := by
    intro k
    induction k with
    | zero => exact hY0
    | succ k ih =>
      have hinc : A (k + 1) - A k = ϑ • E := by
        rw [hA, hA, ← sub_smul]; push_cast; ring_nf
      have hle : ‖(Y k + (A (k + 1) - A k)) - Y k‖ ≤ ϑ := by
        rw [add_sub_cancel_left, hinc, norm_smul, hE, mul_one, Real.norm_of_nonneg hϑ]
      have hr := rank_truncation_epsRank_le_of_norm_sub_le hϑ hle
      rw [ih, Matrix.rank_zero] at hr
      rw [rank_truncation_epsRank hϑ] at hr
      rw [hY k, ih, Nat.le_zero.mp hr, truncation_zero]
  intro k
  refine ⟨hzero k, ?_⟩
  rw [hzero k, sub_zero, hA, norm_smul, hE, mul_one,
    Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg k) hϑ)]

end Freeze

section Recompression

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **Explicit Euler with the field evaluated at perturbed arguments.** If the reference satisfies
`‖A_{k+1} - (A_k + h F_k(A_k))‖ ≤ δ_k`, the field is `L`-Lipschitz, `V_{k+1} = V_k + h F_k(W_k)`
with `‖W_k - V_k‖ ≤ η_k`, then every `E` with `E_0 ≥ ‖V_0 - A_0‖` and
`E_{k+1} ≥ (1 + h L) E_k + h L η_k + δ_k` bounds `‖V_k - A_k‖`. -/
theorem norm_sub_le_of_forall_add_smul {F : ℕ → Matrix m n ℝ → Matrix m n ℝ} {h L : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hF : ∀ k X X', ‖F k X - F k X'‖ ≤ L * ‖X - X'‖) {N : ℕ}
    {A V W : ℕ → Matrix m n ℝ} {δ η E : ℕ → ℝ}
    (hA : ∀ k < N, ‖A (k + 1) - (A k + h • F k (A k))‖ ≤ δ k)
    (hV : ∀ k < N, V (k + 1) = V k + h • F k (W k))
    (hW : ∀ k < N, ‖W k - V k‖ ≤ η k) (hE0 : ‖V 0 - A 0‖ ≤ E 0)
    (hE : ∀ k < N, (1 + h * L) * E k + h * L * η k + δ k ≤ E (k + 1)) :
    ∀ k ≤ N, ‖V k - A k‖ ≤ E k := by
  intro k
  induction k with
  | zero => exact fun _ => hE0
  | succ k ih =>
    intro hk
    have hk' := Nat.lt_of_succ_le hk
    have he := ih hk'.le
    have h1 : V (k + 1) - A (k + 1) = (V k - A k) + h • (F k (W k) - F k (A k))
        - (A (k + 1) - (A k + h • F k (A k))) := by
      rw [hV k hk', smul_sub]; abel
    have h2 : ‖W k - A k‖ ≤ η k + E k := by
      have : W k - A k = (W k - V k) + (V k - A k) := by abel
      rw [this]
      exact (norm_add_le _ _).trans (add_le_add (hW k hk') he)
    have h3 : ‖h • (F k (W k) - F k (A k))‖ ≤ h * (L * (η k + E k)) := by
      rw [norm_smul, Real.norm_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left
        ((hF k _ _).trans (mul_le_mul_of_nonneg_left h2 hL)) hh
    have h4 := norm_sub_le ((V k - A k) + h • (F k (W k) - F k (A k)))
      (A (k + 1) - (A k + h • F k (A k)))
    have h5 := norm_add_le (V k - A k) (h • (F k (W k) - F k (A k)))
    rw [h1]
    nlinarith [hA k hk', hE k hk']

/-- **Dynamic recompression.** Let `V_{k+1} = V_k + h F_k(W_k)` with `‖W_k - V_k‖ ≤ η_k` (the
matrices `W_k` at which the field is evaluated are reconstructions of an Euler sequence that is
not stored), let `Y_{k+1} = T_θ(W_k + h F_k(W_k))` be the truncated singular value decomposition
at the tolerance `θ`, and let `E` bound the Euler sequence as in `norm_sub_le_of_forall_add_smul`.
With `ζ_k = η_k + E_{k+1}`:

* `‖Y_{k+1} - A_{k+1}‖ ≤ θ + ζ_k`;
* `rank_{θ+ζ_k}(A_{k+1}) ≤ rank Y_{k+1}`, and `rank Y_{k+1} ≤ rank_{θ-ζ_k}(A_{k+1})` if `ζ_k ≤ θ`.

The tolerance `θ` enters once at every time, whatever the number of steps. -/
theorem norm_sub_le_and_epsRank_le_rank_and_rank_le_epsRank
    {F : ℕ → Matrix m n ℝ → Matrix m n ℝ} {h L θ : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hθ : 0 ≤ θ)
    (hF : ∀ k X X', ‖F k X - F k X'‖ ≤ L * ‖X - X'‖) {N : ℕ}
    {A V W Y : ℕ → Matrix m n ℝ} {δ η E : ℕ → ℝ}
    (hA : ∀ k < N, ‖A (k + 1) - (A k + h • F k (A k))‖ ≤ δ k)
    (hV : ∀ k < N, V (k + 1) = V k + h • F k (W k))
    (hW : ∀ k < N, ‖W k - V k‖ ≤ η k)
    (hY : ∀ k < N, Y (k + 1) = truncation (W k + h • F k (W k)) (epsRank θ (W k + h • F k (W k))))
    (hE0 : ‖V 0 - A 0‖ ≤ E 0)
    (hE : ∀ k < N, (1 + h * L) * E k + h * L * η k + δ k ≤ E (k + 1)) :
    ∀ k < N, ‖Y (k + 1) - A (k + 1)‖ ≤ θ + (η k + E (k + 1)) ∧
      epsRank (θ + (η k + E (k + 1))) (A (k + 1)) ≤ (Y (k + 1)).rank ∧
      (η k + E (k + 1) ≤ θ →
        (Y (k + 1)).rank ≤ epsRank (θ - (η k + E (k + 1))) (A (k + 1))) := by
  intro k hk
  have hVA := norm_sub_le_of_forall_add_smul hh hL hF hA hV hW hE0 hE (k + 1) hk
  have hZ : ‖(W k + h • F k (W k)) - A (k + 1)‖ ≤ η k + E (k + 1) := by
    have : (W k + h • F k (W k)) - A (k + 1) = (W k - V k) + (V (k + 1) - A (k + 1)) := by
      rw [hV k hk]; abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add (hW k hk) hVA)
  rw [hY k hk, rank_truncation_epsRank hθ]
  refine ⟨?_, epsRank_add_le hθ hZ, fun hζ => epsRank_le_sub hζ hZ⟩
  have h1 := norm_truncation_epsRank_sub_le hθ (W k + h • F k (W k))
  have h2 := norm_sub_le_norm_sub_add_norm_sub (truncation (W k + h • F k (W k))
        (epsRank θ (W k + h • F k (W k))))
    (W k + h • F k (W k)) (A (k + 1))
  linarith

end Recompression

section Examples

open Matrix

/-- **The sum of the tolerances is attained, with a spectral gap.** For the data
`A_k = diag(1, k ϑ)` and the start `Y_0 = A_0 = diag(1, 0)`, step truncation of the exact
increments at the tolerance `ϑ` keeps a rank of at most one, and the error after `k ≤ N` steps is
exactly `k ϑ`, as long as `N ϑ ≤ 1`: the gap between the first and the second singular value of
the iterate is one throughout. -/
theorem exists_stepTruncation_norm_sub_eq_mul {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {N : ℕ} (hN : N * ϑ ≤ 1) :
    ∃ A Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
      A 0 = diagonal ![1, 0] ∧ Y 0 = A 0 ∧
      (∀ k, Y (k + 1) = truncation (Y k + (A (k + 1) - A k))
            (epsRank ϑ (Y k + (A (k + 1) - A k)))) ∧
      ∀ k ≤ N, (Y k).rank ≤ 1 ∧ ‖A k - Y k‖ = k * ϑ := by
  let A : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun k => diagonal ![1, k * ϑ]
  let Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun k =>
    Nat.rec (A 0) (fun j Yj => truncation (Yj + (A (j + 1) - A j))
          (epsRank ϑ (Yj + (A (j + 1) - A j)))) k
  have hY : ∀ k, Y (k + 1) = truncation (Y k + (A (k + 1) - A k))
        (epsRank ϑ (Y k + (A (k + 1) - A k))) := fun k => rfl
  have hA0 : A 0 = diagonal ![1, 0] := by simp [A]
  have hinc : ∀ k, ‖(Y k + (A (k + 1) - A k)) - Y k‖ ≤ ϑ := by
    intro k
    have h1 : A (k + 1) - A k = diagonal ![0, ϑ] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A]
      ring
    have h2 : ‖(diagonal ![0, ϑ] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = ϑ ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp [Fin.sum_univ_two]
    rw [add_sub_cancel_left, h1]
    exact le_of_eq ((sq_eq_sq₀ (norm_nonneg _) hϑ).mp h2)
  have hr0 : (Y 0).rank ≤ 1 := by
    have h1 : Y 0 = vecMulVec ![1, 0] ![1, 0] := by
      change A 0 = _
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A, vecMulVec_apply]
    rw [h1]
    exact rank_vecMulVec_le _ _
  refine ⟨A, Y, hA0, rfl, hY, fun k hk => ?_⟩
  have hr : (Y k).rank ≤ 1 :=
    (rank_le_rank_zero_of_forall_norm_sub_le hϑ (N := N)
      (Z := fun k => Y k + (A (k + 1) - A k)) (fun k _ => hY k) (fun k _ => hinc k) k hk).trans hr0
  refine ⟨hr, le_antisymm ?_ ?_⟩
  · have h := norm_sub_le_add_mul_of_stepTruncation hϑ (N := N) (A := A) (Y := Y)
      (fun k _ => hY k) k hk
    have h0 : A 0 - Y 0 = 0 := sub_self _
    rw [h0, norm_zero, zero_add] at h
    exact h
  · have hkN : (k : ℝ) * ϑ ≤ 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hϑ).trans hN
    have h := le_distLR_diagonal (d := ![1, (k : ℝ) * ϑ]) (c := (k : ℝ) * ϑ)
      (mul_nonneg (Nat.cast_nonneg k) hϑ)
      (fun i => by fin_cases i <;> simp [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) hϑ), hkN])
      (r := 1) (by simp)
    exact h.trans (distLR_le_norm_sub hr)

/-- The hypotheses of `norm_sub_le_and_epsRank_le_rank_and_rank_le_epsRank` can hold with a
change of the rank: for the constant field `F = 1` on `2 × 2` matrices, `h = 1`, `L = 1`,
`θ = 1/2`, a reconstruction error bound `η = 1/8` and the start at zero, the iterate has rank
zero at step zero and rank two at step one, and `ζ = 1/4 ≤ θ`. -/
example : ∃ (A V W Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (η E : ℕ → ℝ),
    (∀ k < 1, ‖A (k + 1) - (A k + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))‖ ≤ 0) ∧
    (∀ k < 1, V (k + 1) = V k + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ k < 1, ‖W k - V k‖ ≤ η k) ∧
    (∀ k < 1, Y (k + 1) = truncation (W k + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (epsRank (1 / 2) (W k + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))) ∧
    ‖V 0 - A 0‖ ≤ E 0 ∧ (∀ k < 1, (1 + 1 * 1) * E k + 1 * 1 * η k + 0 ≤ E (k + 1)) ∧
    0 < η 0 + E 1 ∧ η 0 + E 1 ≤ 1 / 2 ∧ (Y 0).rank = 0 ∧ (Y 1).rank = 2 := by
  refine ⟨fun k => (k : ℝ) • 1, fun k => (k : ℝ) • 1, fun k => (k : ℝ) • 1,
    fun k => if k = 0 then 0 else
      truncation 1 (epsRank (1 / 2) (1 : Matrix (Fin 2) (Fin 2) ℝ)),
    fun _ => 1 / 8,
    fun k => if k = 0 then 0 else 1 / 8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain rfl : k = 0 := by omega
    simp
  · intro k hk
    obtain rfl : k = 0 := by omega
    simp
  · intro k hk
    simp
  · intro k hk
    obtain rfl : k = 0 := by omega
    simp
  · simp
  · intro k hk
    obtain rfl : k = 0 := by omega
    norm_num
  · norm_num
  · norm_num
  · simp
  · have h2 : epsRank (1 / 2) (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
      refine le_antisymm ((epsRank_le_rank (by norm_num)).trans
        ((rank_le_card_width _).trans (by simp))) ?_
      by_contra hlt
      have h1 : epsRank (1 / 2) (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ 1 := by omega
      have h3 := (epsRank_le_iff (by norm_num)).mp h1
      have h4 := le_distLR_diagonal (d := fun _ : Fin 2 => (1 : ℝ)) (c := 1) zero_le_one
        (fun i => by simp) (r := 1) (by simp)
      rw [diagonal_one] at h4
      linarith
    have h5 : (truncation (1 : Matrix (Fin 2) (Fin 2) ℝ)
          (epsRank (1 / 2) (1 : Matrix (Fin 2) (Fin 2) ℝ))).rank = 2 := by
      rw [rank_truncation_epsRank (by norm_num)]; exact h2
    simpa using h5

end Examples

end LeanDLRA.DynamicRecompression
