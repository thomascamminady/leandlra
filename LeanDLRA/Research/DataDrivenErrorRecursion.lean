import LeanDLRA.Integrators.Exactness

/-!
# Pythagorean error recursion for data-driven BUG and KSL

## Setting and motivation

Data-driven dynamical low-rank approximation is the case `F(t, Y) = Ȧ(t)` of Koch and Lubich:
the right-hand side is the time derivative of given data `A(t)` and does not depend on the
state `Y`.  This covers streaming data, incremental updates of recommender systems and the
compression of simulation snapshots.  We study what happens away from the exact case
`A(t) ∈ M_r`.

Write `A n = A(t n)`.  We show below (`bug_step_eq`, `ksl_step_eq`) that one BUG step and one
projector-splitting (KSL) step started from an arbitrary `Y n` are given exactly by

  `Y (n + 1) = Π (n + 1) (Y n + (A (n + 1) - A n))`,

where `Π (n + 1) = P (n + 1) Q (n + 1)` for BUG and `Π (n + 1) = P (n + 1)` for KSL.  These
formulas need neither a rank condition nor a capture condition: they hold for any new
projectors.  So both integrators are Galerkin recursions with orthogonal projectors `Π n`.
For such recursions, with `e n = A n - Y n`, `d n = ‖(1 - Π n) A n‖` (`subErr`) and
`s n = ‖Π (n + 1) (1 - Π n)‖` (`drift`), we prove:

* `err_succ` and `norm_sq_err_succ` (**Pythagorean recursion**):
  `e (n + 1) = (1 - Π (n + 1)) A (n + 1) + Π (n + 1) e n`, and
  `‖e (n + 1)‖² = d (n + 1)² + ‖Π (n + 1) e n‖²`.
* `norm_sq_err_add_sum` (**energy identity**):
  `‖e N‖² + ∑_{n < N} ‖(1 - Π (n + 1)) e n‖² = ‖e 0‖² + ∑_{n < N} d (n + 1)²`.
  Its corollary `norm_sq_err_le` gives `‖e N‖² ≤ ‖e 0‖² + ∑ d²`.  Local subspace errors add up
  in `ℓ²`, not linearly as in Lady Windermere's fan.
* `norm_proj_err_le_drift` and `norm_sq_err_le_drift` (**drift quasi-optimality**):
  `‖e (N + 1)‖² ≤ d (N + 1)² + (‖Π 1 e 0‖ + ∑_{n=1}^{N} s n d n)²`, and
  `subErr_le_norm_err` gives the matching lower bound `d (N + 1) ≤ ‖e (N + 1)‖`.
  The total error is the best error in the current Galerkin space, plus the past subspace errors
  carried along by the rotation of the Galerkin spaces.  The constant is the total variation of
  the subspaces.  It involves neither curvature nor `1 / σ_r`.
* `eq_proj_of_drift_eq_zero`: if `Π 1 e 0 = 0` and the spaces do not rotate
  (`s n = 0` for `1 ≤ n ≤ N`), the integrator returns **exactly** the orthogonal projection
  `Y (N + 1) = Π (N + 1) A (N + 1)`.
* For KSL and BUG with their capture conditions we also prove **dual (increment) identities**
  (`ksl_err_eq_sum`, `bug_err_eq_sum`).  They give the error without Grönwall's lemma:
  `e N = e 0 + ∑ (1 - P (n + 1)) (1 - Q n) ΔA (n + 1)` for KSL, and for BUG
  `e N = e 0 + ∑ [(1 - P (n + 1)) (1 - Q n) + P (n + 1) (1 - Q (n + 1)) (1 - P n)] ΔA (n + 1)`.
  The BUG identity was not part of the original idea; it is new here.
* `bug_run_eq`, `ksl_run_eq`, `bug_norm_sq_err_le`, `bug_norm_sq_err_le_drift`,
  `ksl_norm_sq_err_le` and `ksl_norm_sq_err_le_drift` connect the abstract recursion to the ODE
  formulation of the substeps (`ODESolution`, `IsDerivRHS`).  They reuse
  `Exactness.galerkin_eq_add`.

## What changed with respect to the original idea

The idea (I2-1) is proved as stated, with these refinements.

1. The initial term in (ii) is sharpened from `‖e 0‖` to `‖Π 1 e 0‖`.
2. (iii) is strengthened to an exact energy *identity*.  Its defect is the dissipated mass
   `∑ ‖(1 - Π (n + 1)) e n‖²`.
3. The heuristic "if the bases stabilise (`s n → 0`), the error tends to `d N`" is **false**.
   The in-space error `Π e` is transported but never damped.  See `proj_err_stationary`
   (constant Galerkin space: `‖e (N + 1)‖² = d (N + 1)² + ‖Π e 0‖²` for all `N`) and the
   counterexample `not_tendsto_subErr_of_drift_eq_zero`, where `s n = d n = 0` for all `n` but
   `‖e n‖ = 1`.  The correct statement is `eq_proj_of_drift_eq_zero`: the error equals `d` when
   `Π 1 e 0 = 0` and the spaces stop rotating.  In general, `norm_sq_err_le_drift` bounds the
   plateau.
4. The dual KSL identity needs the KSL capture condition `P (n + 1) K(t (n + 1)) = K(t (n + 1))`.
   This holds by construction (QR of the K-step result).  It is an explicit hypothesis here.

## Relation to the literature

* Koch–Lubich, *Dynamical low-rank approximation*, SIAM J. Matrix Anal. Appl. 29 (2007): the
  data-driven setting `F = Ȧ`.
* Lubich–Oseledets, [LubichOseledets2014], and Ceruti–Lubich, [CerutiLubich2022], prove *exactness*
  for `A(t) ∈ M_r`. The library has this as `Exactness.ksl_exact_multistep` and
  `Exactness.bug_exact_multistep`. The present recursion is the inexact version: exactness is the
  special case `d n = 0`, `e 0 = 0`.
* The robust error bounds (Kieri–Lubich–Walach arXiv:1507.07953, Ceruti–Lubich
  [CerutiLubich2022]), and the high-order projector-splitting analysis of Zhang–Hu
  [ZhangHu2026b], accumulate local errors *linearly* via Lady Windermere's fan / Grönwall
  (`lady_windermere` in this library).  For data-driven problems, `norm_sq_err_le` replaces this
  by `ℓ²` accumulation of subspace errors.
* [Goutaudier2026] uses `‖(I - P_r) P_l‖ = sin θ` once, to glue two regimes.  [FrohlichEtAl2026]
  records a Pythagorean identity for basis transport, not for errors.  Here the drift
  `s n = ‖Π (n + 1) (1 - Π n)‖` is used recursively.  For equal-dimensional subspaces of a
  finite-dimensional space it is the sine of the largest principal angle (not formalized).
* Open problems OP-HO-27 and OP-OT-26 (plateau versus best approximation): for data-driven DLRA,
  `subErr_le_norm_err` and `norm_sq_err_le_drift` give a two-sided answer relative to the
  *own-subspace* best error `d n ≥ dist(A n, M_r)`.  OP-SB-14 is the one-step KSL increment
  identity, which `ksl_err_succ` generalizes to the error.

## Follow-up questions

* Compare `d n = ‖(1 - P n Q n) A n‖` with `dist(A n, M_r)`.  When the BUG bases capture the
  dominant singular subspaces (gap condition), is `d n ≤ (1 + C s) dist(A n, M_r)`?  That would
  give true quasi-optimality with respect to `M_r`.
* Rank-adaptive BUG (truncation after augmentation) adds a truncation projector.  Does the
  recursion survive with an additional `ℓ²` truncation term?
* For a non-data-driven `F`, combine the recursion with a Lipschitz perturbation: does the
  `ℓ²` structure survive at order `h`?
* Is the drift bound sharp?  Find examples where `‖Π e‖` grows like `∑ s n d n`, or prove an
  `ℓ²` version `(∑ (s n d n)²)^{1/2}` under extra structure.
-/

open scoped RealInnerProductSpace
open Set Finset

namespace LeanDLRA

namespace DataDriven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The local subspace error `d n = ‖(1 - Π n) A n‖`: the best-approximation error of the data
`A n` in the range of the Galerkin projector `Π n` (`IsOrthProj.norm_sub_le_of_mem_range`). -/
noncomputable def subErr (Pg : ℕ → E →L[ℝ] E) (A : ℕ → E) (n : ℕ) : ℝ :=
  ‖A n - Pg n (A n)‖

/-- The drift `s n = ‖Π (n + 1) (1 - Π n)‖` of consecutive Galerkin spaces.  For subspaces of
equal finite dimension this is the sine of the largest principal angle between them. -/
noncomputable def drift (Pg : ℕ → E →L[ℝ] E) (n : ℕ) : ℝ :=
  ‖Pg (n + 1) * (1 - Pg n)‖

/-! ## The abstract Galerkin recursion -/

section Recursion

variable {Pg : ℕ → E →L[ℝ] E} {A Y : ℕ → E}

/-- **Error recursion** of the data-driven Galerkin iteration
`Y (n + 1) = Π (n + 1) (Y n + (A (n + 1) - A n))`: the new error is the new subspace error plus
the old error projected onto the new space. -/
theorem err_succ (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (n : ℕ) :
    A (n + 1) - Y (n + 1) = (A (n + 1) - Pg (n + 1) (A (n + 1))) + Pg (n + 1) (A n - Y n) := by
  rw [hY n]
  simp only [map_add, map_sub]
  abel

/-- **Pythagorean error recursion**: `‖e (n + 1)‖² = d (n + 1)² + ‖Π (n + 1) e n‖²`. -/
theorem norm_sq_err_succ (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (n : ℕ) :
    ‖A (n + 1) - Y (n + 1)‖ ^ 2 = subErr Pg A (n + 1) ^ 2 + ‖Pg (n + 1) (A n - Y n)‖ ^ 2 := by
  have h : ⟪A (n + 1) - Pg (n + 1) (A (n + 1)), Pg (n + 1) (A n - Y n)⟫ = 0 := by
    rw [real_inner_comm]; exact (hPg (n + 1)).inner_sub_self _ _
  rw [err_succ hY n, norm_add_sq_real, h, subErr]
  ring

/-- **Lower bound**: the iterate is never better than the best approximation in its own
Galerkin space. -/
theorem subErr_le_norm_err (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (n : ℕ) :
    subErr Pg A (n + 1) ≤ ‖A (n + 1) - Y (n + 1)‖ := by
  have h := norm_sq_err_succ hPg hY n
  have h2 : 0 ≤ ‖Pg (n + 1) (A n - Y n)‖ ^ 2 := by positivity
  exact (abs_le_of_sq_le_sq' (by linarith) (norm_nonneg _)).2

/-- **Energy identity** of the data-driven Galerkin iteration:
`‖e N‖² + ∑_{n < N} ‖(1 - Π (n + 1)) e n‖² = ‖e 0‖² + ∑_{n < N} d (n + 1)²`. -/
theorem norm_sq_err_add_sum (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    ‖A N - Y N‖ ^ 2 + ∑ n ∈ range N, ‖(A n - Y n) - Pg (n + 1) (A n - Y n)‖ ^ 2 =
      ‖A 0 - Y 0‖ ^ 2 + ∑ n ∈ range N, subErr Pg A (n + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, norm_sq_err_succ hPg hY N]
    have h := (hPg (N + 1)).norm_sq_add (A N - Y N)
    linarith

/-- **`ℓ²` accumulation of subspace errors**: `‖e N‖² ≤ ‖e 0‖² + ∑_{n=1}^{N} d n²`. -/
theorem norm_sq_err_le (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    ‖A N - Y N‖ ^ 2 ≤ ‖A 0 - Y 0‖ ^ 2 + ∑ n ∈ range N, subErr Pg A (n + 1) ^ 2 := by
  have h := norm_sq_err_add_sum hPg hY N
  have h0 : 0 ≤ ∑ n ∈ range N, ‖(A n - Y n) - Pg (n + 1) (A n - Y n)‖ ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  linarith

/-- One step of the recursion for the in-space error `g n = ‖Π (n + 1) e n‖`. -/
theorem norm_proj_err_succ_le (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (n : ℕ) :
    ‖Pg (n + 2) (A (n + 1) - Y (n + 1))‖ ≤
      ‖Pg (n + 2) (A (n + 1) - Pg (n + 1) (A (n + 1)))‖ + ‖Pg (n + 1) (A n - Y n)‖ := by
  rw [err_succ hY n, map_add]
  exact (norm_add_le _ _).trans (by gcongr; exact (hPg (n + 2)).norm_le _)

/-- The part of a subspace error that is transported into the next Galerkin space is bounded
by the drift: `‖Π (n + 1) (1 - Π n) x‖ ≤ s n ‖(1 - Π n) x‖`. -/
theorem norm_transport_le (hPg : ∀ n, IsOrthProj (Pg n)) (n : ℕ) (x : E) :
    ‖Pg (n + 1) (x - Pg n x)‖ ≤ drift Pg n * ‖x - Pg n x‖ := by
  have h : (Pg (n + 1) * (1 - Pg n)) (x - Pg n x) = Pg (n + 1) (x - Pg n x) := by
    simp [map_sub, (hPg n).idem]
  rw [← h]
  exact (Pg (n + 1) * (1 - Pg n)).le_opNorm _

/-- **In-space error bound**:
`‖Π (N + 1) e N‖ ≤ ‖Π 1 e 0‖ + ∑_{n=1}^{N} ‖Π (n + 1) (1 - Π n) A n‖`. -/
theorem norm_proj_err_le (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    ‖Pg (N + 1) (A N - Y N)‖ ≤ ‖Pg 1 (A 0 - Y 0)‖ +
      ∑ n ∈ range N, ‖Pg (n + 2) (A (n + 1) - Pg (n + 1) (A (n + 1)))‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have := norm_proj_err_succ_le hPg hY N
    linarith

/-- **In-space error bound via the drift**:
`‖Π (N + 1) e N‖ ≤ ‖Π 1 e 0‖ + ∑_{n=1}^{N} s n d n`. -/
theorem norm_proj_err_le_drift (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    ‖Pg (N + 1) (A N - Y N)‖ ≤ ‖Pg 1 (A 0 - Y 0)‖ +
      ∑ n ∈ range N, drift Pg (n + 1) * subErr Pg A (n + 1) :=
  (norm_proj_err_le hPg hY N).trans (by gcongr with n; exact norm_transport_le hPg (n + 1) _)

/-- **Drift quasi-optimality** of the data-driven Galerkin iteration:
`‖e (N + 1)‖² ≤ d (N + 1)² + (‖Π 1 e 0‖ + ∑_{n=1}^{N} s n d n)²`. -/
theorem norm_sq_err_le_drift (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    ‖A (N + 1) - Y (N + 1)‖ ^ 2 ≤ subErr Pg A (N + 1) ^ 2 +
      (‖Pg 1 (A 0 - Y 0)‖ + ∑ n ∈ range N, drift Pg (n + 1) * subErr Pg A (n + 1)) ^ 2 := by
  rw [norm_sq_err_succ hPg hY N]
  gcongr
  exact norm_proj_err_le_drift hPg hY N

/-- Linear form of the drift bound:
`‖e (N + 1)‖ ≤ d (N + 1) + ‖Π 1 e 0‖ + ∑_{n=1}^{N} s n d n`. -/
theorem norm_err_le_drift (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    ‖A (N + 1) - Y (N + 1)‖ ≤ subErr Pg A (N + 1) +
      (‖Pg 1 (A 0 - Y 0)‖ + ∑ n ∈ range N, drift Pg (n + 1) * subErr Pg A (n + 1)) := by
  rw [err_succ hY N]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_proj_err_le_drift hPg hY N))

/-- **Exact quasi-optimality without drift.**  If the initial error has no component in the
first Galerkin space and the Galerkin spaces do not rotate (`s n = 0` for `1 ≤ n ≤ N`), the
iterate is the orthogonal projection of the data: `Y (N + 1) = Π (N + 1) A (N + 1)`. -/
theorem eq_proj_of_drift_eq_zero (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) {N : ℕ}
    (h0 : Pg 1 (A 0 - Y 0) = 0) (hs : ∀ n < N, drift Pg (n + 1) = 0) :
    Y (N + 1) = Pg (N + 1) (A (N + 1)) := by
  have hb := norm_proj_err_le_drift hPg hY N
  have hsum : ∑ n ∈ range N, drift Pg (n + 1) * subErr Pg A (n + 1) = 0 :=
    sum_eq_zero fun n hn => by rw [hs n (mem_range.1 hn), zero_mul]
  rw [h0, norm_zero, hsum, add_zero] at hb
  have hg : Pg (N + 1) (A N - Y N) = 0 := norm_le_zero_iff.1 hb
  have h := err_succ hY N
  rw [hg, add_zero] at h
  exact sub_right_injective h

/-- Under the hypotheses of `eq_proj_of_drift_eq_zero` the error equals the subspace error. -/
theorem norm_err_eq_subErr_of_drift_eq_zero (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) {N : ℕ}
    (h0 : Pg 1 (A 0 - Y 0) = 0) (hs : ∀ n < N, drift Pg (n + 1) = 0) :
    ‖A (N + 1) - Y (N + 1)‖ = subErr Pg A (N + 1) := by
  rw [eq_proj_of_drift_eq_zero hPg hY h0 hs, subErr]

/-- **Stationary Galerkin space**: if `Π n = Π` for all `n ≥ 1`, the in-space error is frozen,
`Π (N + 1) e N = Π e 0`.  It is transported but never damped. -/
theorem proj_err_stationary {Pr : E →L[ℝ] E} (hPr : IsOrthProj Pr)
    (hc : ∀ n, Pg (n + 1) = Pr)
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    Pg (N + 1) (A N - Y N) = Pr (A 0 - Y 0) := by
  induction N with
  | zero => rw [hc 0]
  | succ N ih =>
    rw [hc N] at ih
    rw [err_succ hY N, hc (N + 1), hc N]
    simp only [map_add, map_sub, hPr.idem, sub_self, zero_add] at ih ⊢
    exact ih

/-- **Stationary Galerkin space, norm form**: `‖e (N + 1)‖² = d (N + 1)² + ‖Π e 0‖²` for every
`N`.  So `s n = 0` alone does not make the error tend to the subspace error. -/
theorem norm_sq_err_stationary {Pr : E →L[ℝ] E} (hPr : IsOrthProj Pr)
    (hc : ∀ n, Pg (n + 1) = Pr) (hPg : ∀ n, IsOrthProj (Pg n))
    (hY : ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) (N : ℕ) :
    ‖A (N + 1) - Y (N + 1)‖ ^ 2 = subErr Pg A (N + 1) ^ 2 + ‖Pr (A 0 - Y 0)‖ ^ 2 := by
  rw [norm_sq_err_succ hPg hY N, proj_err_stationary hPr hc hY N]

end Recursion

/-- **Counterexample**: vanishing drift and vanishing subspace errors do not force the error to
zero.  With `E = ℝ`, `Π n = 1`, `A = 0` and `Y = 1`, `s n = d n = 0` for all `n`, but
`‖e n‖ = 1`. -/
theorem not_tendsto_subErr_of_drift_eq_zero :
    ∃ (Pg : ℕ → ℝ →L[ℝ] ℝ) (A Y : ℕ → ℝ), (∀ n, IsOrthProj (Pg n)) ∧
      (∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n))) ∧ (∀ n, drift Pg n = 0) ∧
      (∀ n, subErr Pg A n = 0) ∧ ∀ n, ‖A n - Y n‖ = 1 :=
  ⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => IsOrthProj.one, fun _ => by simp,
    fun _ => by simp [drift], fun _ => by simp [subErr], fun _ => by simp⟩

/-! ## One step of BUG and KSL for data-driven problems -/

section Steps

/-- A Galerkin substep `y' = Q F(t, y)` with `F(t,Y) = Ȧ(t)` started at an arbitrary `Y₀` ends
at `Y₀ + Q (A t₁ - A t₀)` (the K- and L-steps). -/
theorem galerkin_step_eq {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Q : E →L[ℝ] E} {Y₀ : E} {y : ℝ → E}
    (hy : ODESolution (fun t Y => Q (F t Y)) y t₀ t₁) (h0 : y t₀ = Y₀) :
    y t₁ = Y₀ + Q (A t₁ - A t₀) := by
  rw [Exactness.galerkin_eq_add hA Q (fun _ _ => rfl) hy t₁ ⟨ht, le_rfl⟩, h0]

/-- **The data-driven BUG step from an arbitrary start.**  The S-step `YS' = P₁ Q₁ F(t, YS)`,
`YS(t₀) = P₁ Q₁ Y₀`, with `F(t,Y) = Ȧ(t)` ends at `P₁ Q₁ (Y₀ + (A t₁ - A t₀))`.  This holds
whatever the new projectors are; their capture properties play no role. -/
theorem bug_step_eq {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YS : ℝ → E}
    (hYS : ODESolution (fun t Y => P₁ (Q₁ (F t Y))) YS t₀ t₁) (h0 : YS t₀ = P₁ (Q₁ Y₀)) :
    YS t₁ = (P₁ * Q₁) (Y₀ + (A t₁ - A t₀)) := by
  rw [Exactness.galerkin_eq_add (Pg := P₁ * Q₁) hA (fun _ _ => rfl) hYS t₁ ⟨ht, le_rfl⟩, h0,
    map_add]
  rfl

/-- **The data-driven KSL step from an arbitrary start.**  K-step `YK' = Q₀ F`, `YK(t₀) = Y₀`;
backward S-step `YS' = -P₁ Q₀ F`, `YS(t₀) = P₁ YK(t₁)`; L-step `YL' = P₁ F`, `YL(t₀) = YS(t₁)`.
For `F(t,Y) = Ȧ(t)` the result is `P₁ (Y₀ + (A t₁ - A t₀))`, for any projectors.  (Compare
`Exactness.ksl_eq_abstract`, which starts at `Y₀ = A t₀`.) -/
theorem ksl_step_eq {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₀ : E →L[ℝ] E} {Y₀ : E} {YK YS YL : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYS : ODESolution (fun t Y => -P₁ (Q₀ (F t Y))) YS t₀ t₁)
    (hYL : ODESolution (fun t Y => P₁ (F t Y)) YL t₀ t₁)
    (hK0 : YK t₀ = Y₀) (hS0 : YS t₀ = P₁ (YK t₁)) (hL0 : YL t₀ = YS t₁) :
    YL t₁ = P₁ (Y₀ + (A t₁ - A t₀)) := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hK := galerkin_step_eq ht hA hYK hK0
  have eS := Exactness.galerkin_eq_add hA (-(P₁ * Q₀)) (fun _ _ => rfl) hYS t₁ h1
  have eL := Exactness.galerkin_eq_add hA P₁ (fun _ _ => rfl) hYL t₁ h1
  have eS' : YS t₁ = YS t₀ - P₁ (Q₀ (A t₁ - A t₀)) := by
    rw [eS, sub_eq_add_neg (YS t₀)]; rfl
  rw [eL, hL0, eS', hS0, hK]
  simp only [map_add, map_sub]
  abel

/-- **Dual one-step identity for KSL.**  If `Y₁ = P₁ (Y₀ + ΔA)` and `P₁` captures the K-step
result `Y₀ + Q₀ ΔA`, then `e₁ = e₀ + (1 - P₁) (1 - Q₀) ΔA`. -/
theorem ksl_err_succ {P₁ Q₀ : E →L[ℝ] E} {Y₀ Y₁ A₀ A₁ : E} (hY : Y₁ = P₁ (Y₀ + (A₁ - A₀)))
    (hcap : P₁ (Y₀ + Q₀ (A₁ - A₀)) = Y₀ + Q₀ (A₁ - A₀)) :
    A₁ - Y₁ = (A₀ - Y₀) + ((1 - P₁) * (1 - Q₀)) (A₁ - A₀) := by
  set Δ := A₁ - A₀ with hΔ
  have hA : A₁ = A₀ + Δ := by rw [hΔ]; abel
  rw [map_add] at hcap
  have hP : P₁ Y₀ = Y₀ + Q₀ Δ - P₁ (Q₀ Δ) := eq_sub_of_add_eq hcap
  rw [hY, map_add, hP, hA]
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub]
  abel

/-- **Dual one-step identity for BUG.**  If `Y₁ = P₁ Q₁ (Y₀ + ΔA)`, `P₁` captures the K-step
result `Y₀ + Q₀ ΔA` and `Q₁` captures the L-step result `Y₀ + P₀ ΔA`, then
`e₁ = e₀ + (1 - P₁) (1 - Q₀) ΔA + P₁ (1 - Q₁) (1 - P₀) ΔA`. -/
theorem bug_err_succ {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ Y₁ A₀ A₁ : E}
    (hY : Y₁ = P₁ (Q₁ (Y₀ + (A₁ - A₀))))
    (hcapP : P₁ (Y₀ + Q₀ (A₁ - A₀)) = Y₀ + Q₀ (A₁ - A₀))
    (hcapQ : Q₁ (Y₀ + P₀ (A₁ - A₀)) = Y₀ + P₀ (A₁ - A₀)) :
    A₁ - Y₁ = (A₀ - Y₀) + ((1 - P₁) * (1 - Q₀)) (A₁ - A₀) +
      (P₁ * (1 - Q₁) * (1 - P₀)) (A₁ - A₀) := by
  set Δ := A₁ - A₀ with hΔ
  have hA : A₁ = A₀ + Δ := by rw [hΔ]; abel
  rw [map_add] at hcapP hcapQ
  have hP : P₁ Y₀ = Y₀ + Q₀ Δ - P₁ (Q₀ Δ) := eq_sub_of_add_eq hcapP
  have hQ : Q₁ Y₀ = Y₀ + P₀ Δ - Q₁ (P₀ Δ) := eq_sub_of_add_eq hcapQ
  rw [hY, map_add, hQ]
  simp only [map_add, map_sub]
  rw [hP, hA]
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub]
  abel

end Steps

/-! ## Multistep dual identities -/

section Dual

variable {P Q : ℕ → E →L[ℝ] E} {A Y : ℕ → E}

/-- **Dual multistep identity for KSL**: a discrete `∫ (I - P)(I - Q) Ȧ`, without Grönwall:
`e N = e 0 + ∑_{n < N} (1 - P (n + 1)) (1 - Q n) (A (n + 1) - A n)`. -/
theorem ksl_err_eq_sum (hY : ∀ n, Y (n + 1) = P (n + 1) (Y n + (A (n + 1) - A n)))
    (hcap : ∀ n, P (n + 1) (Y n + Q n (A (n + 1) - A n)) = Y n + Q n (A (n + 1) - A n))
    (N : ℕ) :
    A N - Y N = (A 0 - Y 0) + ∑ n ∈ range N, ((1 - P (n + 1)) * (1 - Q n)) (A (n + 1) - A n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ksl_err_succ (hY N) (hcap N), ih]
    abel

/-- Norm form of `ksl_err_eq_sum`:
`‖e N‖ ≤ ‖e 0‖ + ∑_{n < N} ‖(1 - P (n + 1)) (1 - Q n) (A (n + 1) - A n)‖`. -/
theorem ksl_norm_err_le_sum (hY : ∀ n, Y (n + 1) = P (n + 1) (Y n + (A (n + 1) - A n)))
    (hcap : ∀ n, P (n + 1) (Y n + Q n (A (n + 1) - A n)) = Y n + Q n (A (n + 1) - A n))
    (N : ℕ) :
    ‖A N - Y N‖ ≤
      ‖A 0 - Y 0‖ + ∑ n ∈ range N, ‖((1 - P (n + 1)) * (1 - Q n)) (A (n + 1) - A n)‖ := by
  rw [ksl_err_eq_sum hY hcap N]
  exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)

/-- **Dual multistep identity for BUG**:
`e N = e 0 + ∑_{n < N} [(1 - P (n + 1)) (1 - Q n) + P (n + 1) (1 - Q (n + 1)) (1 - P n)] ΔA`. -/
theorem bug_err_eq_sum (hY : ∀ n, Y (n + 1) = P (n + 1) (Q (n + 1) (Y n + (A (n + 1) - A n))))
    (hcapP : ∀ n, P (n + 1) (Y n + Q n (A (n + 1) - A n)) = Y n + Q n (A (n + 1) - A n))
    (hcapQ : ∀ n, Q (n + 1) (Y n + P n (A (n + 1) - A n)) = Y n + P n (A (n + 1) - A n))
    (N : ℕ) :
    A N - Y N = (A 0 - Y 0) + ∑ n ∈ range N, (((1 - P (n + 1)) * (1 - Q n)) (A (n + 1) - A n) +
      (P (n + 1) * (1 - Q (n + 1)) * (1 - P n)) (A (n + 1) - A n)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, bug_err_succ (hY N) (hcapP N) (hcapQ N), ih]
    abel

end Dual

/-! ## Data-driven BUG and KSL runs -/

section Runs

variable {F : ℝ → E → E} {a : ℝ → E} {t : ℕ → ℝ} {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}

/-- A run of data-driven BUG S-steps on the grid `t` is the Galerkin recursion with
`Π (n + 1) = P (n + 1) Q (n + 1)`. -/
theorem bug_run_eq (ht : ∀ n, t n ≤ t (n + 1)) (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1)))
    {YS : ℕ → ℝ → E}
    (hYS : ∀ n, ODESolution (fun s Z => P (n + 1) (Q (n + 1) (F s Z))) (YS n) (t n) (t (n + 1)))
    (hS0 : ∀ n, YS n (t n) = P (n + 1) (Q (n + 1) (Y n)))
    (hY : ∀ n, Y (n + 1) = YS n (t (n + 1))) (n : ℕ) :
    Y (n + 1) = (P (n + 1) * Q (n + 1)) (Y n + (a (t (n + 1)) - a (t n))) := by
  rw [hY n]
  exact bug_step_eq (ht n) (ha n) (hYS n) (hS0 n)

/-- **`ℓ²` error bound for data-driven BUG**: with commuting orthogonal projectors `P n`, `Q n`,
`‖a(t N) - Y N‖² ≤ ‖a(t 0) - Y 0‖² + ∑_{n=1}^{N} ‖(1 - P n Q n) a(t n)‖²`. -/
theorem bug_norm_sq_err_le (ht : ∀ n, t n ≤ t (n + 1))
    (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1))) (hP : ∀ n, IsOrthProj (P n))
    (hQ : ∀ n, IsOrthProj (Q n)) (hc : ∀ n x, P n (Q n x) = Q n (P n x)) {YS : ℕ → ℝ → E}
    (hYS : ∀ n, ODESolution (fun s Z => P (n + 1) (Q (n + 1) (F s Z))) (YS n) (t n) (t (n + 1)))
    (hS0 : ∀ n, YS n (t n) = P (n + 1) (Q (n + 1) (Y n)))
    (hY : ∀ n, Y (n + 1) = YS n (t (n + 1))) (N : ℕ) :
    ‖a (t N) - Y N‖ ^ 2 ≤ ‖a (t 0) - Y 0‖ ^ 2 +
      ∑ n ∈ range N, subErr (fun n => P n * Q n) (fun n => a (t n)) (n + 1) ^ 2 :=
  norm_sq_err_le (Pg := fun n => P n * Q n) (A := fun n => a (t n))
    (fun n => (hP n).mul (hQ n) (hc n)) (bug_run_eq ht ha hYS hS0 hY) N

/-- **Drift quasi-optimality for data-driven BUG** with `Π n = P n Q n`. -/
theorem bug_norm_sq_err_le_drift (ht : ∀ n, t n ≤ t (n + 1))
    (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1))) (hP : ∀ n, IsOrthProj (P n))
    (hQ : ∀ n, IsOrthProj (Q n)) (hc : ∀ n x, P n (Q n x) = Q n (P n x)) {YS : ℕ → ℝ → E}
    (hYS : ∀ n, ODESolution (fun s Z => P (n + 1) (Q (n + 1) (F s Z))) (YS n) (t n) (t (n + 1)))
    (hS0 : ∀ n, YS n (t n) = P (n + 1) (Q (n + 1) (Y n)))
    (hY : ∀ n, Y (n + 1) = YS n (t (n + 1))) (N : ℕ) :
    ‖a (t (N + 1)) - Y (N + 1)‖ ^ 2 ≤
      subErr (fun n => P n * Q n) (fun n => a (t n)) (N + 1) ^ 2 +
      (‖(P 1 * Q 1) (a (t 0) - Y 0)‖ + ∑ n ∈ range N, drift (fun n => P n * Q n) (n + 1) *
        subErr (fun n => P n * Q n) (fun n => a (t n)) (n + 1)) ^ 2 :=
  norm_sq_err_le_drift (Pg := fun n => P n * Q n) (A := fun n => a (t n))
    (fun n => (hP n).mul (hQ n) (hc n)) (bug_run_eq ht ha hYS hS0 hY) N

/-- **Dual identity for a data-driven BUG run.**  K-step `YK n` (`Q n F`, from `Y n`) and
L-step `YL n` (`P n F`, from `Y n`), new projectors capturing their end values, and S-step
`YS n`.  Then `e N = e 0 + ∑ [(1 - P (n + 1)) (1 - Q n) + P (n + 1) (1 - Q (n + 1)) (1 - P n)] ΔA`
exactly. -/
theorem bug_run_err_eq_sum (ht : ∀ n, t n ≤ t (n + 1))
    (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1))) {YK YL YS : ℕ → ℝ → E}
    (hYK : ∀ n, ODESolution (fun s Z => Q n (F s Z)) (YK n) (t n) (t (n + 1)))
    (hYL : ∀ n, ODESolution (fun s Z => P n (F s Z)) (YL n) (t n) (t (n + 1)))
    (hK0 : ∀ n, YK n (t n) = Y n) (hL0 : ∀ n, YL n (t n) = Y n)
    (hcapK : ∀ n, P (n + 1) (YK n (t (n + 1))) = YK n (t (n + 1)))
    (hcapL : ∀ n, Q (n + 1) (YL n (t (n + 1))) = YL n (t (n + 1)))
    (hYS : ∀ n, ODESolution (fun s Z => P (n + 1) (Q (n + 1) (F s Z))) (YS n) (t n) (t (n + 1)))
    (hS0 : ∀ n, YS n (t n) = P (n + 1) (Q (n + 1) (Y n)))
    (hY : ∀ n, Y (n + 1) = YS n (t (n + 1))) (N : ℕ) :
    a (t N) - Y N = (a (t 0) - Y 0) + ∑ n ∈ range N,
      (((1 - P (n + 1)) * (1 - Q n)) (a (t (n + 1)) - a (t n)) +
        (P (n + 1) * (1 - Q (n + 1)) * (1 - P n)) (a (t (n + 1)) - a (t n))) := by
  refine bug_err_eq_sum (A := fun n => a (t n)) (fun n => ?_) (fun n => ?_) (fun n => ?_) N
  · exact bug_run_eq ht ha hYS hS0 hY n
  · rw [← galerkin_step_eq (ht n) (ha n) (hYK n) (hK0 n)]; exact hcapK n
  · rw [← galerkin_step_eq (ht n) (ha n) (hYL n) (hL0 n)]; exact hcapL n

/-- A run of data-driven KSL steps on the grid `t` is the Galerkin recursion with
`Π (n + 1) = P (n + 1)`. -/
theorem ksl_run_eq (ht : ∀ n, t n ≤ t (n + 1)) (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1)))
    {YK YS YL : ℕ → ℝ → E}
    (hYK : ∀ n, ODESolution (fun s Z => Q n (F s Z)) (YK n) (t n) (t (n + 1)))
    (hYS : ∀ n, ODESolution (fun s Z => -P (n + 1) (Q n (F s Z))) (YS n) (t n) (t (n + 1)))
    (hYL : ∀ n, ODESolution (fun s Z => P (n + 1) (F s Z)) (YL n) (t n) (t (n + 1)))
    (hK0 : ∀ n, YK n (t n) = Y n) (hS0 : ∀ n, YS n (t n) = P (n + 1) (YK n (t (n + 1))))
    (hL0 : ∀ n, YL n (t n) = YS n (t (n + 1))) (hY : ∀ n, Y (n + 1) = YL n (t (n + 1)))
    (n : ℕ) : Y (n + 1) = P (n + 1) (Y n + (a (t (n + 1)) - a (t n))) := by
  rw [hY n]
  exact ksl_step_eq (ht n) (ha n) (hYK n) (hYS n) (hYL n) (hK0 n) (hS0 n) (hL0 n)

/-- **`ℓ²` error bound for data-driven KSL**:
`‖a(t N) - Y N‖² ≤ ‖a(t 0) - Y 0‖² + ∑_{n=1}^{N} ‖(1 - P n) a(t n)‖²`. -/
theorem ksl_norm_sq_err_le (ht : ∀ n, t n ≤ t (n + 1))
    (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1))) (hP : ∀ n, IsOrthProj (P n))
    {YK YS YL : ℕ → ℝ → E}
    (hYK : ∀ n, ODESolution (fun s Z => Q n (F s Z)) (YK n) (t n) (t (n + 1)))
    (hYS : ∀ n, ODESolution (fun s Z => -P (n + 1) (Q n (F s Z))) (YS n) (t n) (t (n + 1)))
    (hYL : ∀ n, ODESolution (fun s Z => P (n + 1) (F s Z)) (YL n) (t n) (t (n + 1)))
    (hK0 : ∀ n, YK n (t n) = Y n) (hS0 : ∀ n, YS n (t n) = P (n + 1) (YK n (t (n + 1))))
    (hL0 : ∀ n, YL n (t n) = YS n (t (n + 1))) (hY : ∀ n, Y (n + 1) = YL n (t (n + 1)))
    (N : ℕ) :
    ‖a (t N) - Y N‖ ^ 2 ≤ ‖a (t 0) - Y 0‖ ^ 2 +
      ∑ n ∈ range N, subErr P (fun n => a (t n)) (n + 1) ^ 2 :=
  norm_sq_err_le (A := fun n => a (t n)) hP
    (ksl_run_eq ht ha hYK hYS hYL hK0 hS0 hL0 hY) N

/-- **Drift quasi-optimality for data-driven KSL** with `Π n = P n`. -/
theorem ksl_norm_sq_err_le_drift (ht : ∀ n, t n ≤ t (n + 1))
    (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1))) (hP : ∀ n, IsOrthProj (P n))
    {YK YS YL : ℕ → ℝ → E}
    (hYK : ∀ n, ODESolution (fun s Z => Q n (F s Z)) (YK n) (t n) (t (n + 1)))
    (hYS : ∀ n, ODESolution (fun s Z => -P (n + 1) (Q n (F s Z))) (YS n) (t n) (t (n + 1)))
    (hYL : ∀ n, ODESolution (fun s Z => P (n + 1) (F s Z)) (YL n) (t n) (t (n + 1)))
    (hK0 : ∀ n, YK n (t n) = Y n) (hS0 : ∀ n, YS n (t n) = P (n + 1) (YK n (t (n + 1))))
    (hL0 : ∀ n, YL n (t n) = YS n (t (n + 1))) (hY : ∀ n, Y (n + 1) = YL n (t (n + 1)))
    (N : ℕ) :
    ‖a (t (N + 1)) - Y (N + 1)‖ ^ 2 ≤ subErr P (fun n => a (t n)) (N + 1) ^ 2 +
      (‖P 1 (a (t 0) - Y 0)‖ +
        ∑ n ∈ range N, drift P (n + 1) * subErr P (fun n => a (t n)) (n + 1)) ^ 2 :=
  norm_sq_err_le_drift (A := fun n => a (t n)) hP
    (ksl_run_eq ht ha hYK hYS hYL hK0 hS0 hL0 hY) N

/-- **Dual identity for a data-driven KSL run** (the KSL capture condition
`P (n + 1) YK(t (n + 1)) = YK(t (n + 1))` holds by construction, via QR of `K(t (n + 1))`):
`e N = e 0 + ∑_{n < N} (1 - P (n + 1)) (1 - Q n) (a(t (n + 1)) - a(t n))`. -/
theorem ksl_run_err_eq_sum (ht : ∀ n, t n ≤ t (n + 1))
    (ha : ∀ n, IsDerivRHS F a (t n) (t (n + 1))) {YK YS YL : ℕ → ℝ → E}
    (hYK : ∀ n, ODESolution (fun s Z => Q n (F s Z)) (YK n) (t n) (t (n + 1)))
    (hYS : ∀ n, ODESolution (fun s Z => -P (n + 1) (Q n (F s Z))) (YS n) (t n) (t (n + 1)))
    (hYL : ∀ n, ODESolution (fun s Z => P (n + 1) (F s Z)) (YL n) (t n) (t (n + 1)))
    (hK0 : ∀ n, YK n (t n) = Y n) (hS0 : ∀ n, YS n (t n) = P (n + 1) (YK n (t (n + 1))))
    (hL0 : ∀ n, YL n (t n) = YS n (t (n + 1))) (hY : ∀ n, Y (n + 1) = YL n (t (n + 1)))
    (hcap : ∀ n, P (n + 1) (YK n (t (n + 1))) = YK n (t (n + 1))) (N : ℕ) :
    a (t N) - Y N = (a (t 0) - Y 0) +
      ∑ n ∈ range N, ((1 - P (n + 1)) * (1 - Q n)) (a (t (n + 1)) - a (t n)) := by
  refine ksl_err_eq_sum (A := fun n => a (t n)) (fun n => ?_) (fun n => ?_) N
  · exact ksl_run_eq ht ha hYK hYS hYL hK0 hS0 hL0 hY n
  · rw [← galerkin_step_eq (ht n) (ha n) (hYK n) (hK0 n)]; exact hcap n

end Runs

/-! ## Examples -/

/-- The hypotheses of the abstract recursion are satisfiable for any projectors, data and
initial value: the iteration defines the sequence. -/
example (Pg : ℕ → E →L[ℝ] E) (A : ℕ → E) (Y₀ : E) :
    ∃ Y : ℕ → E, Y 0 = Y₀ ∧ ∀ n, Y (n + 1) = Pg (n + 1) (Y n + (A (n + 1) - A n)) :=
  ⟨fun n => Nat.rec Y₀ (fun k y => Pg (k + 1) (y + (A (k + 1) - A k))) n, rfl, fun _ => rfl⟩

/-- A non-trivial instance of the exact quasi-optimality theorem: on `ℝ` with `Π = 0`, data
`A n = n` and `Y = 0`, the iterate is the projection and the error equals the subspace error
`d (N + 1) = N + 1 ≠ 0`. -/
example (N : ℕ) :
    ‖((N + 1 : ℕ) : ℝ) - (0 : ℝ)‖ =
      subErr (fun _ => (0 : ℝ →L[ℝ] ℝ)) (fun n => (n : ℝ)) (N + 1) :=
  norm_err_eq_subErr_of_drift_eq_zero (Pg := fun _ => (0 : ℝ →L[ℝ] ℝ)) (A := fun n => (n : ℝ))
    (Y := fun _ => 0) (fun _ => IsOrthProj.zero) (fun _ => by simp) (by simp)
    (fun _ _ => by simp [drift])

/-- The data-driven BUG step formula on a concrete straight-line data path `A t = t`, with the
exact affine S-step trajectory, starting from an arbitrary `Y₀`. -/
example (Y₀ : ℝ) :
    Y₀ + (1 : ℝ) • (1 : ℝ) = ((1 : ℝ →L[ℝ] ℝ) * 1) (Y₀ + ((0 + (1 : ℝ) • (1 : ℝ)) -
      (0 + (0 : ℝ) • (1 : ℝ)))) :=
  bug_step_eq (F := fun _ _ => (1 : ℝ)) (A := fun t => 0 + t • (1 : ℝ)) zero_le_one
    (Exactness.isDerivRHS_add_smul 0 1 0 1) (P₁ := 1) (Q₁ := 1) (YS := fun t => Y₀ + t • 1)
    (Exactness.odeSolution_add_smul_of_const (fun _ _ => by simp) Y₀ 0 1) (by simp)

end DataDriven

end LeanDLRA
