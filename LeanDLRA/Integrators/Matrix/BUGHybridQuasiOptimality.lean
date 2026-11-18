import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityTruncation

/-!
# Error certificates that are robust and quasi-optimal for runs with changing rank

For the matrix approximation problem (given data `A(t)`, field `F(t, Y) = Ȧ(t)`) two kinds of
error bounds are known. The robust bounds ([CerutiLubich2022], [CerutiKuschLubich2022]) add up
local errors and hold without a condition on singular values; they bound `‖Y_n - A(t_n)‖`. The
quasi-optimal bound `Exactness.IsBUGIncrementStep.norm_sub_truncation_le` bounds the distance
`‖Y_n - T_r(A(t_n))‖` to the best approximation of rank `r` by a multiple of the neglected
singular value, and needs a gap `σ_r(A) ≤ τ < ρ ≤ σ_{r-1}(A)` (indices start at `0`) on every
step. This file combines them on one run in which the rank `r n` may change from step to step.

With `a n = ‖Y n - A n‖`, `d n = ‖Y n - T_{r n}(A n)‖`, the tail `s n = ‖A n - T_{r n}(A n)‖` and
the local errors `δ n ≥ ‖Y (n + 1) - Y n - (A (n + 1) - A n)‖`, every step satisfies
`a (n + 1) ≤ a n + δ n` and `|a n - d n| ≤ s n`, whatever the method and the ranks. A step may in
addition be certified: `d n ≤ Ed n → d (n + 1) ≤ Ed (n + 1)`. Then every pair of sequences `Ea`,
`Ed` that dominates the initial errors and satisfies on every step

* `Ed (n + 1) ≥ Ea n + δ n + s (n + 1)`, or the step is certified, and
* `Ea (n + 1) ≥ Ea n + δ n` or `Ea (n + 1) ≥ Ed (n + 1) + s (n + 1)`

bounds both errors: `d n ≤ Ed n` and `a n ≤ Ea n`. The choice `Ea n = a 0 + ∑ δ` is the robust
bound; a pair that uses certified steps where a gap exists and the local errors elsewhere costs,
for a window without a gap or a change of the rank, the local errors in the window and the tails
at its two ends.

## Main results

* `le_and_le_of_forall_hybrid_step`: the statement above for real sequences.
* `norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step`: the statement for matrices.
* `EckartYoung.norm_truncation_sub_truncation_le_of_norm_sub_le`: if `‖Y - A‖ ≤ e`,
  `σ_r(A) ≤ τ`, `ρ ≤ σ_{r-1}(A)` and `τ + 2 e < ρ`, then
  `‖T_r(Y) - T_r(A)‖ ≤ (ρ - e) / (ρ - τ - 2 e) e`. With it, a truncation of an iterate to a
  lower rank is a certified step.
* `EckartYoung.le_singularValues_of_norm_sub_truncation_le`: the lower bound `ρ` of the gap on a
  step `[a, b]` from the singular value of the iterate:
  `ρ + E + τ + μ (b - a) ≤ σ_{r-1}(Y)` and `‖Y - T_r(A a)‖ ≤ E` give `ρ ≤ σ_{r-1}(A t)`.
* `Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_le_singularValues`: one BUG step with
  this lower bound.
* `norm_bugRun_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step`: a run on the grid
  `t_n = n h` whose certified steps are steps of the BUG integrator of [CerutiLubich2022] at the
  current rank, with the gap checked on the iterate.

## Implementation notes

The certified steps are a hypothesis of the form `d n ≤ Ed n → d (n + 1) ≤ Ed (n + 1)`, so steps
of other integrators with a bound of this kind can be used in the same way. On a certified BUG
step the data enter through the speed `μ`, the upper bound `τ` of the neglected singular value
(the quantity the bound is expressed in) and the local errors; the lower bound `ρ` is checked on
the computed iterate. The sequences `Ea`, `Ed` are any solution of the inequalities, so the
smallest one (a dynamic programme over the steps) is a bound, and so is every other one.

## References

* [CerutiLubich2022]
* [CerutiKuschLubich2022]
-/

open Set Finset Matrix Filter
open scoped Topology LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### Real sequences -/

section Sequences

/-- **Robust and certified steps on one run, for real sequences.** Let `a (k + 1) ≤ a k + δ k`
and `|a k - d k| ≤ s k`. On the steps in `g` let a bound of `d` propagate:
`d k ≤ Ed k → d (k + 1) ≤ Ed (k + 1)`. If `Ed (k + 1) ≥ Ea k + δ k + s (k + 1)` on the other
steps, and on every step `Ea (k + 1) ≥ Ea k + δ k` or `Ea (k + 1) ≥ Ed (k + 1) + s (k + 1)`,
then `d n ≤ Ed n` and `a n ≤ Ea n` for `n ≤ N`. -/
theorem le_and_le_of_forall_hybrid_step {N : ℕ} {a d s δ Ea Ed : ℕ → ℝ} {g : ℕ → Prop}
    (ha : ∀ k < N, a (k + 1) ≤ a k + δ k)
    (hda : ∀ k ≤ N, d k ≤ a k + s k) (had : ∀ k ≤ N, a k ≤ d k + s k)
    (hq : ∀ k < N, g k → d k ≤ Ed k → d (k + 1) ≤ Ed (k + 1))
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
      · exact hq k hk' hg hd
      · exact ((hda (k + 1) hk).trans (by linarith)).trans h
    refine ⟨hd1, ?_⟩
    rcases hEa k hk' with h | h
    · exact h1.trans h
    · exact ((had (k + 1) hk).trans (by linarith)).trans h

end Sequences

/-! ### Matrices -/

section Matrices

open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Robust and certified steps on one run with changing rank.** Let `A k` be the data and
`Y k` the iterates at the grid points, `r k` the ranks, `X k = T_{r k}(A k)`, and let
`δ k ≥ ‖Y (k + 1) - Y k - (A (k + 1) - A k)‖` be the local errors (for `F(t, Y) = Ȧ(t)` the
exact flow adds the increment of the data). On the steps in `g` let a bound of the distance to
the best approximation propagate: `‖Y k - X k‖ ≤ Ed k → ‖Y (k + 1) - X (k + 1)‖ ≤ Ed (k + 1)`.
If `Ed (k + 1) ≥ Ea k + δ k + ‖A (k + 1) - X (k + 1)‖` on the other steps, and on every step
`Ea (k + 1) ≥ Ea k + δ k` or `Ea (k + 1) ≥ Ed (k + 1) + ‖A (k + 1) - X (k + 1)‖`, then for
`n ≤ N`

  `‖Y n - X n‖ ≤ Ed n`  and  `‖Y n - A n‖ ≤ Ea n`.

Nothing is assumed on singular values outside the steps in `g`, and the ranks are arbitrary. -/
theorem norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step {N : ℕ}
    {A Y : ℕ → Matrix m n ℝ} {r : ℕ → ℕ} {δ Ea Ed : ℕ → ℝ} {g : ℕ → Prop}
    (hδ : ∀ k < N, ‖Y (k + 1) - Y k - (A (k + 1) - A k)‖ ≤ δ k)
    (hq : ∀ k < N, g k → ‖Y k - truncation (A k) (r k)‖ ≤ Ed k →
      ‖Y (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ed (k + 1))
    (h0a : ‖Y 0 - A 0‖ ≤ Ea 0) (h0d : ‖Y 0 - truncation (A 0) (r 0)‖ ≤ Ed 0)
    (hEd : ∀ k < N, g k ∨
      Ea k + δ k + ‖A (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ed (k + 1))
    (hEa : ∀ k < N, Ea k + δ k ≤ Ea (k + 1) ∨
      Ed (k + 1) + ‖A (k + 1) - truncation (A (k + 1)) (r (k + 1))‖ ≤ Ea (k + 1)) :
    ∀ n ≤ N, ‖Y n - truncation (A n) (r n)‖ ≤ Ed n ∧ ‖Y n - A n‖ ≤ Ea n := by
  refine le_and_le_of_forall_hybrid_step (a := fun k => ‖Y k - A k‖)
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

/-- **The truncated singular value decomposition is Lipschitz with a constant near one under a
relative gap.** If `‖Y - A‖ ≤ e`, `σ_r(A) ≤ τ`, `ρ ≤ σ_{r-1}(A)` (indices start at `0`) and
`τ + 2 e < ρ`, then

  `‖T_r(Y) - T_r(A)‖ ≤ (ρ - e) / (ρ - τ - 2 e) e`.

For an iterate `Y` of rank above `r` with `‖Y - A‖ ≤ e` this bounds the distance of its
truncation to the best approximation of rank `r`, so a truncation to a lower rank is a
certified step of `norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step`. -/
theorem EckartYoung.norm_truncation_sub_truncation_le_of_norm_sub_le {r : ℕ}
    {A Y : Matrix m n ℝ} {e ρ τ : ℝ} (he : ‖Y - A‖ ≤ e)
    (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1))
    (hτ : (toEuclideanLin A).singularValues r ≤ τ) (hgap : τ + 2 * e < ρ) :
    ‖truncation Y r - truncation A r‖ ≤ (ρ - e) / (ρ - τ - 2 * e) * e := by
  have hBd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => A + t • (Y - A)) (Y - A) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const (Y - A)).const_add A
  have hW : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : ℕ,
      |(toEuclideanLin (A + t • (Y - A))).singularValues i -
        (toEuclideanLin A).singularValues i| ≤ e := fun t ht i => by
    have h := WeylSingular.abs_singularValues_sub_le_frobenius (A + t • (Y - A)) A i
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
    exact h.trans ((mul_le_of_le_one_left (norm_nonneg _) ht.2).trans he)
  have key := (norm_truncation_sub_truncation_le_mul_sub (r := r)
    (A := fun t : ℝ => A + t • (Y - A)) (A' := fun _ => Y - A) (a := 0) (b := 1)
    (ρ := ρ - e) (μ := e) (τ := τ + e) zero_le_one
    (fun t _ => (hBd t).continuousAt.continuousWithinAt)
    (fun t _ => (hBd t).hasDerivWithinAt) (fun _ _ => he)
    (fun t ht => by linarith [(abs_le.1 (hW t ht (r - 1))).1])
    (fun t ht => by linarith [(abs_le.1 (hW t ht r)).2]) (by linarith)).1
  have e1 : A + (1 : ℝ) • (Y - A) = Y := by
    rw [one_smul, add_sub_cancel]
  have e0 : A + (0 : ℝ) • (Y - A) = A := by
    rw [zero_smul, add_zero]
  simp only [e1, e0] at key
  refine key.trans (le_of_eq ?_)
  have e2 : ρ - e - (τ + e) = ρ - τ - 2 * e := by ring
  rw [e2]
  ring

/-- **The lower bound of the gap from the iterate.** Let `A` be continuous on `[a, b]` with
right derivative `A'`, `‖A'‖ ≤ μ`, `σ_r(A a) ≤ τ`, and let `‖Y - T_r(A a)‖ ≤ E`. If
`ρ + E + τ + μ (b - a) ≤ σ_{r-1}(Y)` (indices start at `0`), then `ρ ≤ σ_{r-1}(A t)` on
`[a, b]`. The hypothesis is on the singular value of the iterate `Y`; of the data only the
speed and the neglected singular value enter. -/
theorem EckartYoung.le_singularValues_of_norm_sub_truncation_le {r : ℕ}
    {A A' : ℝ → Matrix m n ℝ} {Y : Matrix m n ℝ} {a b ρ μ τ E : ℝ} (hab : a ≤ b)
    (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ)
    (hτ : (toEuclideanLin (A a)).singularValues r ≤ τ)
    (hE : ‖Y - truncation (A a) r‖ ≤ E)
    (hY : ρ + E + τ + μ * (b - a) ≤ (toEuclideanLin Y).singularValues (r - 1)) :
    ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1) := by
  intro t ht
  have h1 : ‖A t - A a‖ ≤ μ * (t - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hAc hA hμ t ht
  have h1' : μ * (t - a) ≤ μ * (b - a) := by
    rcases hab.eq_or_lt with h | h
    · have hta : t = a := le_antisymm (ht.2.trans h.ge) ht.1
      rw [hta, ← h]
    · have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, h⟩)
      exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hμ0
  have h2 : Curvature.specNorm (Y - A a) ≤ E + τ := by
    have e : Y - A a = Y - truncation (A a) r + (truncation (A a) r - A a) := by abel
    rw [e]
    refine (WeylSingular.specNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Curvature.specNorm_le_frob _).trans hE
    · rw [Curvature.specNorm_sub_comm, specNorm_sub_truncation]
      exact hτ
  have h3 := (abs_le.1 (WeylSingular.abs_singularValues_sub_le Y (A a) (r - 1))).2
  have h4 := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius (A t) (A a) (r - 1))).1
  linarith

/-- **One BUG step against the truncated singular value decomposition, with the gap checked on
the iterate.** Let `A` be continuous on `[a, b]`, `a < b`, with right derivative `A'`,
`‖A'‖ ≤ μ` and `σ_r(A t) ≤ τ < ρ` on `[a, b]` (indices start at `0`), and let
`lam ≥ μ / (ρ - τ)` with `(b - a) lam ≤ 1/16`. For a BUG step
`(U₀, S₀, V₀) ↦ (U₁, S₁, V₁)` with exact substeps for `F(t, Y) = Ȧ(t)` and bases with `r`
orthonormal columns, let `‖Y₀ - T_r(A a)‖ ≤ E ≤ ρ/16` and
`ρ + E + τ + μ (b - a) ≤ σ_{r-1}(Y₀)`. Then, with `η = (b - a) lam`,

  `‖Y₁ - T_r(A b)‖ ≤ (1 + 9/2 η) E + 11/5 η σ_r(A b) + 4/3 η² (σ_r(A a) + σ_r(A b))`.

No lower bound of a singular value of the data is assumed. -/
theorem Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_le_singularValues {r : ℕ}
    {A A' : ℝ → Matrix m n ℝ} {a b ρ μ τ lam E : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
    {S₀ S₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ}
    (hs : Exactness.IsBUGIncrementStep (A a) (A b) U₀ S₀ V₀ U₁ S₁ V₁) (hab : a < b)
    (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ)
    (hτ : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ)
    (hlam : μ ≤ lam * (ρ - τ)) (hstep : (b - a) * lam ≤ 1 / 16)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (hE : ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ ≤ E) (hE16 : E ≤ ρ / 16)
    (hY : ρ + E + τ + μ * (b - a) ≤
      (toEuclideanLin (U₀ * S₀ * V₀ᵀ)).singularValues (r - 1)) :
    ‖U₁ * S₁ * V₁ᵀ - truncation (A b) r‖ ≤
      (1 + 9 / 2 * ((b - a) * lam)) * E +
        11 / 5 * ((b - a) * lam) * (toEuclideanLin (A b)).singularValues r +
        4 / 3 * ((b - a) * lam) ^ 2 * ((toEuclideanLin (A a)).singularValues r +
          (toEuclideanLin (A b)).singularValues r) := by
  have hσ := le_singularValues_of_norm_sub_truncation_le hab.le hAc hA hμ
    (hτ a ⟨le_rfl, hab.le⟩) hE hY
  have key := hs.norm_sub_truncation_le hab hAc hA hμ hσ hτ hτρ hlam hstep hU₀ hV₀ hU₁ hV₁
    (hE.trans hE16)
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have hlam0 : 0 ≤ lam := nonneg_of_mul_nonneg_left (hμ0.trans hlam) (sub_pos.mpr hτρ)
  have hη : 0 ≤ 1 + 9 / 2 * ((b - a) * lam) := by
    have := mul_nonneg (sub_nonneg.mpr hab.le) hlam0
    linarith
  refine key.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  exact mul_le_mul_of_nonneg_left hE hη

/-- **A run with changing rank: robust everywhere, quasi-optimal where the iterate shows a
gap.** Let `A` be continuous on `[0, N h]` with right derivative `A'`, and let `Y k` be
matrices at the grid points `k h` with local errors
`δ k ≥ ‖Y (k + 1) - Y k - (A ((k + 1) h) - A (k h))‖`; `r k` are the ranks and
`X k = T_{r k}(A (k h))`. On the steps `k` in `g` the rank does not change, the step is a step of
the BUG integrator of [CerutiLubich2022] with exact substeps for `F(t, Y) = Ȧ(t)` and bases with
`r k` orthonormal columns, `‖A'‖ ≤ μ k` and `σ_{r k}(A t) ≤ τ k < ρ k` on the step (indices
start at `0`), `lam k ≥ μ k / (ρ k - τ k)`, `h lam k ≤ 1/16`, `Ed k ≤ ρ k / 16`, the iterate
satisfies `ρ k + Ed k + τ k + μ k h ≤ σ_{r k - 1}(Y k)`, and

  `Ed (k + 1) ≥ (1 + 9/2 η) Ed k + 11/5 η s₁ + 4/3 η² (s₀ + s₁)`,   `η = h lam k`,

with `s₀`, `s₁` the neglected singular values `σ_{r k}(A)` at the two ends of the step. On the
other steps `Ed (k + 1) ≥ Ea k + δ k + ‖A ((k + 1) h) - X (k + 1)‖`, and on every step
`Ea (k + 1) ≥ Ea k + δ k` or `Ea (k + 1) ≥ Ed (k + 1) + ‖A ((k + 1) h) - X (k + 1)‖`. Then for
`n ≤ N`

  `‖Y n - X n‖ ≤ Ed n`  and  `‖Y n - A (n h)‖ ≤ Ea n`.

With `g` empty this is the robust bound by the sum of the local errors. No lower bound of a
singular value of the data is assumed: where the iterate has no gap the bound continues with
the local errors, and a later step in `g` costs the tail of the rank used there. -/
theorem norm_bugRun_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step {N : ℕ}
    {A A' : ℝ → Matrix m n ℝ} {Y : ℕ → Matrix m n ℝ} {r : ℕ → ℕ}
    {U₀ U₁ : ∀ k, Matrix m (Fin (r k)) ℝ} {S₀ S₁ : ∀ k, Matrix (Fin (r k)) (Fin (r k)) ℝ}
    {V₀ V₁ : ∀ k, Matrix n (Fin (r k)) ℝ} {h : ℝ} {ρ μ τ lam δ Ea Ed : ℕ → ℝ} {g : ℕ → Prop}
    (hh : 0 < h) (hAc : ContinuousOn A (Icc 0 (N * h)))
    (hA : ∀ t ∈ Ico 0 (N * h), HasDerivWithinAt A (A' t) (Ici t) t)
    (hδ : ∀ k < N, ‖Y (k + 1) - Y k - (A ((k + 1 : ℕ) * h) - A (k * h))‖ ≤ δ k)
    (hμ : ∀ k < N, g k → ∀ t ∈ Ico (k * h) ((k + 1 : ℕ) * h), ‖A' t‖ ≤ μ k)
    (hτ : ∀ k < N, g k → ∀ t ∈ Icc (k * h) ((k + 1 : ℕ) * h),
      (toEuclideanLin (A t)).singularValues (r k) ≤ τ k)
    (hτρ : ∀ k < N, g k → τ k < ρ k) (hlam : ∀ k < N, g k → μ k ≤ lam k * (ρ k - τ k))
    (hstep : ∀ k < N, g k → h * lam k ≤ 1 / 16)
    (hr : ∀ k < N, g k → r (k + 1) = r k)
    (hY₀ : ∀ k < N, g k → Y k = U₀ k * S₀ k * (V₀ k)ᵀ)
    (hY₁ : ∀ k < N, g k → Y (k + 1) = U₁ k * S₁ k * (V₁ k)ᵀ)
    (hU₀ : ∀ k < N, g k → (U₀ k)ᵀ * U₀ k = 1) (hV₀ : ∀ k < N, g k → (V₀ k)ᵀ * V₀ k = 1)
    (hU₁ : ∀ k < N, g k → (U₁ k)ᵀ * U₁ k = 1) (hV₁ : ∀ k < N, g k → (V₁ k)ᵀ * V₁ k = 1)
    (hs : ∀ k < N, g k → Exactness.IsBUGIncrementStep (A (k * h)) (A ((k + 1 : ℕ) * h))
      (U₀ k) (S₀ k) (V₀ k) (U₁ k) (S₁ k) (V₁ k))
    (hgap : ∀ k < N, g k → ρ k + Ed k + τ k + μ k * h ≤
      (toEuclideanLin (Y k)).singularValues (r k - 1))
    (hE16 : ∀ k < N, g k → Ed k ≤ ρ k / 16)
    (hQ : ∀ k < N, g k → (1 + 9 / 2 * (h * lam k)) * Ed k +
        11 / 5 * (h * lam k) * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues (r k) +
        4 / 3 * (h * lam k) ^ 2 * ((toEuclideanLin (A (k * h))).singularValues (r k) +
          (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues (r k)) ≤ Ed (k + 1))
    (h0a : ‖Y 0 - A ((0 : ℕ) * h)‖ ≤ Ea 0)
    (h0d : ‖Y 0 - truncation (A ((0 : ℕ) * h)) (r 0)‖ ≤ Ed 0)
    (hEd : ∀ k < N, g k ∨ Ea k + δ k +
      ‖A ((k + 1 : ℕ) * h) - truncation (A ((k + 1 : ℕ) * h)) (r (k + 1))‖ ≤ Ed (k + 1))
    (hEa : ∀ k < N, Ea k + δ k ≤ Ea (k + 1) ∨ Ed (k + 1) +
      ‖A ((k + 1 : ℕ) * h) - truncation (A ((k + 1 : ℕ) * h)) (r (k + 1))‖ ≤ Ea (k + 1)) :
    ∀ n ≤ N, ‖Y n - truncation (A (n * h)) (r n)‖ ≤ Ed n ∧ ‖Y n - A (n * h)‖ ≤ Ea n := by
  refine norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step
    (A := fun k : ℕ => A (k * h)) (Y := Y) (r := r) (g := g) hδ (fun k hk hg hd => ?_)
    h0a h0d hEd hEa
  have hab : (k : ℝ) * h < ((k + 1 : ℕ) : ℝ) * h := by
    push_cast
    linarith
  have hba : ((k + 1 : ℕ) : ℝ) * h - k * h = h := by
    push_cast
    ring
  have ha0 : (0 : ℝ) ≤ k * h := mul_nonneg (Nat.cast_nonneg k) hh.le
  have hbN : ((k + 1 : ℕ) : ℝ) * h ≤ N * h :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh.le
  have hstepk : (((k + 1 : ℕ) : ℝ) * h - k * h) * lam k ≤ 1 / 16 := by
    rw [hba]
    exact hstep k hk hg
  have hgapk : ρ k + Ed k + τ k + μ k * (((k + 1 : ℕ) : ℝ) * h - k * h) ≤
      (toEuclideanLin (U₀ k * S₀ k * (V₀ k)ᵀ)).singularValues (r k - 1) := by
    rw [hba, ← hY₀ k hk hg]
    exact hgap k hk hg
  have hd' : ‖U₀ k * S₀ k * (V₀ k)ᵀ - truncation (A (k * h)) (r k)‖ ≤ Ed k := by
    rw [← hY₀ k hk hg]
    exact hd
  have key := (hs k hk hg).norm_sub_truncation_le_of_le_singularValues hab
    (hAc.mono (Icc_subset_Icc ha0 hbN))
    (fun t ht => hA t ⟨ha0.trans ht.1, ht.2.trans_le hbN⟩) (hμ k hk hg) (hτ k hk hg)
    (hτρ k hk hg) (hlam k hk hg) hstepk (hU₀ k hk hg) (hV₀ k hk hg) (hU₁ k hk hg)
    (hV₁ k hk hg) hd' (hE16 k hk hg) hgapk
  rw [hba, ← hY₁ k hk hg] at key
  change ‖Y (k + 1) - truncation (A ((k + 1 : ℕ) * h)) (r (k + 1))‖ ≤ Ed (k + 1)
  rw [hr k hk hg]
  exact key.trans (hQ k hk hg)

end Matrices

/-! ### Examples -/

namespace BUGHybridQuasiOptimalityExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples EckartYoung BUGQuasiOptimalityTruncationExamples

/-- The tail `diag(0, 1/16)` of the examples. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem hasDerivAt_smul_e₁_add_N₁₆ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆

private theorem singularValues_one_le {t : ℝ} (ht : 0 ≤ t) :
    (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1 ≤ 1 / 16 := by
  rw [← specNorm_sub_truncation, truncation_smul_e₁_add ht, Curvature.specNorm_sub_comm]
  exact (Curvature.specNorm_le_frob _).trans (norm_smul_e₁_sub_add_le t)

private theorem norm_smul_e₁_le : ‖(1 / 100 : ℝ) • (e₁ * e₁ᵀ)‖ ≤ 1 / 100 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  nlinarith [norm_e₁_mul_le, norm_nonneg (e₁ * e₁ᵀ)]

private theorem norm_iterate_sub_le (t : ℝ) :
    ‖(101 / 100 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)‖ ≤ 1 / 100 + 1 / 16 := by
  have e : (101 / 100 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) =
      (1 / 100 : ℝ) • (e₁ * e₁ᵀ) + ((1 + t) • (e₁ * e₁ᵀ) - ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)) := by
    rw [← add_sub_assoc, ← add_smul]
    congr 2
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add norm_smul_e₁_le (norm_smul_e₁_sub_add_le t))

private theorem norm_iterate_sub_truncation_le {t : ℝ} (ht : 0 ≤ t) :
    ‖(101 / 100 + t) • (e₁ * e₁ᵀ) - truncation ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤ 1 / 100 := by
  have e : (101 / 100 + t) - (1 + t) = 1 / 100 := by ring
  rw [truncation_smul_e₁_add ht, ← sub_smul, e]
  exact norm_smul_e₁_le

private theorem norm_sub_truncation_le {t : ℝ} (ht : 0 ≤ t) :
    ‖(1 + t) • (e₁ * e₁ᵀ) + N₁₆ - truncation ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤ 1 / 16 := by
  rw [truncation_smul_e₁_add ht, norm_sub_rev]
  exact norm_smul_e₁_sub_add_le t

/-- **Non-vacuity of `EckartYoung.norm_truncation_sub_truncation_le_of_norm_sub_le`**: the
data `A = e₁ e₁ᵀ + diag(0, 1/16)` and `Y = A + 1/100 e₁ e₁ᵀ`, with `r = 1`, `e = 1/100`,
`ρ = 1` and `τ = 1/16`. -/
example : ‖truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆ + (1 / 100 : ℝ) • (e₁ * e₁ᵀ)) 1 -
      truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤
    (1 - 1 / 100) / (1 - 1 / 16 - 2 * (1 / 100)) * (1 / 100) := by
  refine norm_truncation_sub_truncation_le_of_norm_sub_le ?_
    (one_le_singularValues_smul_e₁_add le_rfl) (singularValues_one_le le_rfl) (by norm_num)
  rw [add_sub_cancel_left]
  exact norm_smul_e₁_le

/-- **Non-vacuity of `norm_bugRun_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step`**
(and of `Exactness.IsBUGIncrementStep.norm_sub_truncation_le_of_le_singularValues`,
`EckartYoung.le_singularValues_of_norm_sub_truncation_le`,
`norm_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step` and
`le_and_le_of_forall_hybrid_step`): one step of size `h = 1/32` for the data
`A(t) = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` and the iterates `Y n = (101/100 + n h) e₁ e₁ᵀ`, `r = 1`,
`ρ = 3/4`, `μ = 1`, `τ = 1/16`, `lam = 16/11`. The step is certified from the singular value
of the iterate, `Ed = 1/100, 2/100`, and the bound of the error `Ea = 10/100, 9/100` uses the
bound of the distance to the truncation and the tail, which is not zero. -/
example : ∀ n : ℕ, n ≤ 1 →
    ‖(101 / 100 + (n : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) -
        truncation ((1 + (n : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤ 1 / 100 + (n : ℝ) / 100 ∧
      ‖(101 / 100 + (n : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) -
        ((1 + (n : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) + N₁₆)‖ ≤ 1 / 10 - (n : ℝ) / 100 := by
  have hk0 : ∀ k : ℕ, k < 1 → (k : ℝ) = 0 := fun k hk => by
    rw [Nat.lt_one_iff.mp hk, Nat.cast_zero]
  exact norm_bugRun_sub_truncation_le_and_norm_sub_le_of_forall_hybrid_step (N := 1)
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (A' := fun _ => e₁ * e₁ᵀ)
    (Y := fun k : ℕ => (101 / 100 + (k : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ)) (r := fun _ => 1)
    (U₀ := fun _ => e₁) (U₁ := fun _ => e₁)
    (S₀ := fun k : ℕ => (101 / 100 + (k : ℝ) * (1 / 32)) • 1)
    (S₁ := fun k : ℕ => (101 / 100 + ((k + 1 : ℕ) : ℝ) * (1 / 32)) • 1)
    (V₀ := fun _ => e₁) (V₁ := fun _ => e₁) (h := 1 / 32) (ρ := fun _ => 3 / 4)
    (μ := fun _ => 1) (τ := fun _ => 1 / 16) (lam := fun _ => 16 / 11) (δ := fun _ => 0)
    (Ea := fun k : ℕ => 1 / 10 - (k : ℝ) / 100) (Ed := fun k : ℕ => 1 / 100 + (k : ℝ) / 100)
    (g := fun _ => True) (by norm_num)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).hasDerivWithinAt)
    (fun k _ => by
      have e : (101 / 100 + ((k + 1 : ℕ) : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) -
          (101 / 100 + (k : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) -
          ((1 + ((k + 1 : ℕ) : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) + N₁₆ -
            ((1 + (k : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) + N₁₆)) = 0 := by
        rw [add_sub_add_right_eq_sub, ← sub_smul, ← sub_smul, ← sub_smul]
        have e' : (101 / 100 + ((k + 1 : ℕ) : ℝ) * (1 / 32)) - (101 / 100 + (k : ℝ) * (1 / 32)) -
            ((1 + ((k + 1 : ℕ) : ℝ) * (1 / 32)) - (1 + (k : ℝ) * (1 / 32))) = 0 := by ring
        rw [e', zero_smul]
      exact (norm_eq_zero.mpr e).le)
    (fun _ _ _ _ _ => norm_e₁_mul_le)
    (fun k _ _ t ht => singularValues_one_le
      ((mul_nonneg (Nat.cast_nonneg k) (by norm_num)).trans ht.1))
    (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)
    (fun _ _ _ => rfl) (fun _ _ _ => smul_e₁_mul _) (fun _ _ _ => smul_e₁_mul _)
    (fun _ _ _ => e₁_transpose_mul_self) (fun _ _ _ => e₁_transpose_mul_self)
    (fun _ _ _ => e₁_transpose_mul_self) (fun _ _ _ => e₁_transpose_mul_self)
    (fun k _ _ => by
      have h := isBUGIncrementStep_smul_e₁ (101 / 100 + (k : ℝ) * (1 / 32)) ((k : ℝ) * (1 / 32))
        (((k + 1 : ℕ) : ℝ) * (1 / 32))
      have e : 101 / 100 + (k : ℝ) * (1 / 32) +
          (((k + 1 : ℕ) : ℝ) * (1 / 32) - (k : ℝ) * (1 / 32)) =
          101 / 100 + ((k + 1 : ℕ) : ℝ) * (1 / 32) := by ring
      rw [e] at h
      exact h)
    (fun k hk _ => by
      have h1 := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius
        ((101 / 100 + (k : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ))
        ((1 + (k : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) + N₁₆) (1 - 1))).1
      have h2 := norm_iterate_sub_le ((k : ℝ) * (1 / 32))
      have h3 := one_le_singularValues_smul_e₁_add
        (mul_nonneg (Nat.cast_nonneg k) (by norm_num : (0 : ℝ) ≤ 1 / 32))
      have h4 := hk0 k hk
      change (3 / 4 : ℝ) + (1 / 100 + (k : ℝ) / 100) + 1 / 16 + 1 * (1 / 32) ≤
        (toEuclideanLin ((101 / 100 + (k : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ))).singularValues (1 - 1)
      linarith)
    (fun k hk _ => by
      have h4 := hk0 k hk
      change (1 / 100 : ℝ) + (k : ℝ) / 100 ≤ 3 / 4 / 16
      linarith)
    (fun k hk _ => by
      have h0 := singularValues_one_le
        (mul_nonneg (Nat.cast_nonneg k) (by norm_num : (0 : ℝ) ≤ 1 / 32))
      have h1 := singularValues_one_le
        (mul_nonneg (Nat.cast_nonneg (k + 1)) (by norm_num : (0 : ℝ) ≤ 1 / 32))
      have h4 := hk0 k hk
      refine (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 (by norm_num)))
        (mul_le_mul_of_nonneg_left (add_le_add h0 h1) (by norm_num))).trans ?_
      change (1 + 9 / 2 * (1 / 32 * (16 / 11))) * (1 / 100 + (k : ℝ) / 100) +
          11 / 5 * (1 / 32 * (16 / 11)) * (1 / 16) +
          4 / 3 * (1 / 32 * (16 / 11)) ^ 2 * (1 / 16 + 1 / 16) ≤
        1 / 100 + ((k + 1 : ℕ) : ℝ) / 100
      push_cast
      rw [h4]
      norm_num)
    ((norm_iterate_sub_le _).trans (by norm_num))
    ((norm_iterate_sub_truncation_le (by norm_num)).trans (by norm_num))
    (fun _ _ => Or.inl trivial)
    (fun k hk => Or.inr (by
      have h1 := norm_sub_truncation_le
        (mul_nonneg (Nat.cast_nonneg (k + 1)) (by norm_num : (0 : ℝ) ≤ 1 / 32))
      have h4 := hk0 k hk
      refine (add_le_add le_rfl h1).trans ?_
      change (1 / 100 : ℝ) + ((k + 1 : ℕ) : ℝ) / 100 + 1 / 16 ≤
        1 / 10 - ((k + 1 : ℕ) : ℝ) / 100
      push_cast
      rw [h4]
      norm_num))

end BUGHybridQuasiOptimalityExamples

end LeanDLRA
