import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Integrators.Matrix.Defs
import LeanDLRA.LinearAlgebra.LowRank.Defs

/-!
# Distance to the low-rank set

For real `m × n` matrices with the Frobenius norm (`open scoped LeanDLRA.Frobenius`) this file
studies the set `M_{≤ r} = {Y : rank Y ≤ r}` (`lowRankSet`) and the distance
`dist(X, M_{≤ r})` (`distLR`), defined as an infimum (`Metric.infDist`).  No singular value
decomposition is used: by Eckart–Young `distLR r X` is the tail `(∑_{j>r} σ_j²)^{1/2}`, but every
result below is proved from the definition.  The distance is the robust replacement for "the
rank-`r` DLRA solution" in several error analyses whose hypotheses fail when singular values
become small.

`lowRankSet`, `distLR` and `epsRank` are defined in `LeanDLRA/LinearAlgebra/LowRank/Defs.lean`,
`NearNormalBound` and `nearNormalBound_of_factored` in `LeanDLRA/Integrators/Matrix/Defs.lean`.

## Main results

* **Basic facts.** `distLR_le_add`, `lipschitzWith_distLR` (`1`-Lipschitz), `distLR_antitone`
  (monotone in the rank), `le_distLR_of_le_mulVec` (lower bound `c` when `‖A x‖ ≥ c ‖x‖`, a
  singular-value-free form of `σ_min`), `le_distLR_diagonal`.
* **OP-RA-03 (rank tracking).** `epsRank ε X = min {k : dist(X, M_{≤ k}) ≤ ε}` and the sandwich
  `epsRank_sandwich`: `‖X - Y‖ ≤ e ≤ ε ⇒ rank_{ε+e}(Y) ≤ rank_ε(X) ≤ rank_{ε-e}(Y)`; exact rank
  identification near a rank-`(k+1)` target (`epsRank_eq_of_norm_sub_le`, FeDLRT
  arXiv 2410.18720); geometric convergence to a rank-one equilibrium
  (`distLR_one_le_of_geometric`, `epsRank_le_one_of_geometric`, arXiv 2308.05914 Sec. 5).
* **OP-EX-02 (robust flow capture).** `exists_capture_flow`, `exists_lowRank_near_flow`,
  `distLR_flow_le`: for every exact solution `A` on `[t₀, t₀ + h]` starting at a matrix of rank
  `≤ r` (arbitrarily small singular values allowed),
  `dist(A(t₁), M_{≤ r}) ≤ ‖A(t₁) - U₁U₁ᵀ A(t₁) V₁V₁ᵀ‖ ≤ 2 h (4 L B h + ε)`, with the factored
  normal-component bound `ε` needed only within distance `B h` of `A(t₀)` (`NearNormalBound`);
  flow form `exists_flow_distLR_le`, quasi-best truncation `norm_quasiBest_flow_le`.
  Proof: one BUG step from `A(t₀)` exists (`MatrixBUG.exists_isStep`), `bug_capture`
  (arXiv 2010.02022, Lemma 3) and `rank_mul_mul_transpose_le`.
* **`h²`-free robust bound** (new).  `distLR_flow_le_exp`: under the global factored
  normal-component bound, `dist(A(t₁), M_{≤ r}) ≤ 2 h ε e^{L h}` (`distLR_flow_step`: one-step
  recursion from almost-nearest points and flow stability `norm_sub_le_exp_of_odeSolution`;
  `distLR_flow_le_grid`: discrete Grönwall; then `N → ∞` substeps).  Two-sided sharpness
  `h/3 ≤ dist(A(h), M_{≤ 1}) ≤ 2 h ‖F‖` in an explicit example.
* **OP-RA-07 / rank-`r` truncation** (arXiv 2402.08607, Remark 4; arXiv 2608.27749, Remark 2).
  `norm_trunc_sub_le`: `‖T - A₁‖ ≤ κ dist(A₁, M_{≤ r}) + (1 + κ) ‖Ŷ - A₁‖` for every
  `κ`-quasi-best rank-`r` approximation `T` of `Ŷ`; `norm_trunc_flow_le`,
  `fixedRank_trunc_local_error_le`: the augmented BUG step truncated back to rank `r` has local
  error `O(h (h + ε_r))` without a tolerance term and without a rank-`r` DLRA solution;
  `norm_trunc_flow_le_exp`: `‖T - A(t₁)‖ ≤ 2 κ h ε_r e^{L h} + (1 + κ) ‖Ŷ - A(t₁)‖`, the papers'
  bound `h ε_r + 2 ‖Ŷ - A(t₁)‖` up to the constant `2 e^{L h}`.
  Counterexample `trunc_bound_fails_of_normal_at_start`: with `ε` measured only at `(t₀, Y₀)`
  the claimed bound fails (`F = [[0,1],[1,0]]`, `Y₀ = diag(δ, 0)`).
* **Closedness and best approximation.** `isClosed_lowRankSet` (via compactness of the Stiefel
  set, `isCompact_stiefel`), `distLR_eq_zero_iff`, `exists_best_approx` (existence part of
  Eckart–Young without SVD), `epsRank_le_iff_exists` (`rank_ε(X)` is the smallest rank within
  distance `ε`), `exists_epsRank_approx`, `epsRank_zero`.
* **Fixed-rank truncated augmented BUG** (new).  `fixedRank_global_error_le`,
  `fixedRank_global_error_le'`: augment, Galerkin step, truncate back to rank `r` with any
  `κ`-quasi-best truncation; the global error is `O(δ + ε + h)` with no tolerance term and no
  rank-`r` DLRA solution (truncation defect `fixedRankDefect = O(h (h + ε))` from
  `distLR_flow_le_exp`, then `MatrixBUG.rankAdaptive_global_error_le`);
  `exists_bestTrunc_flow_le`.
* **OP-RA-16 (rank doubling).** `rank_augmented_le` (`rank Û Ŝ V̂ᵀ ≤ 2r`),
  `le_pow_mul_of_doubling` (`r_j ≤ 2^j r_0`), `clog_le_of_doubling` (reaching `r*` needs
  `≥ ⌈log₂ ⌈r*/r₀⌉⌉` steps), `norm_residual_le_norm_sub` (error `≥ ‖(1 - P̂Q̂) A₁‖`, independent
  of the tolerance), `distLR_le_residual`, the explicit tolerance-independent lower bound
  `rankAdaptive_error_ge` (`F ≡ I₃`, `Y₀ = e₁e₁ᵀ`: every rank-`≤ 2` result has error `≥ h`), and
  the truncation rule (22) of arXiv 2602.06614 Sec. 3.1.1 as an `ε`-rank (`epsRank_augmented_le`).
* **OP-OT-19 (monotonicity).** `norm_one_sub_le_of_le`, `norm_normal_le_of_le`,
  `norm_sub_apply_apply_le_of_le` (capture residuals and doubly-normal parts decrease under basis
  enrichment, abstract inner product spaces), `galerkin_step_error_of_le`, `IsBUGStep.enrich`
  (every enrichment of a BUG step is a BUG step with the same `ε`), `bug_bound_mono`,
  `distLR_flow_le_of_le` (rank monotonicity).

## Open-problem status (see `docs/survey/open-problems.json`)

* OP-RA-03: the sandwich is proved for the distance-defined `ε`-rank.  The identification of
  `epsRank` with the singular-value tolerance rule needs Eckart–Young, which is not formalised.
* OP-EX-02: the robust capture statement is proved as stated (local `ε`, any rank `≤ r`).
  Re-deriving each cited paper's convergence theorem from it is not done here.
* OP-RA-07: the gap-free truncation inequality, the robust bound
  `dist(A(t₁), M_{≤ r}) ≤ 2 h ε_r e^{L h}` (no `h²` term, so the high-order claims
  `O(h (h² + ε_r))` of arXiv 2402.08607 hold robustly) and the counterexample for `ε` measured
  only at `(t₀, Y₀)` are formalised.  Open: the constant `ε_r (e^{L h} - 1) / L` of the
  conjectured Dini-derivative bound (ours is at most `2 e^{L h}` times larger), and the version
  with `ε_r` assumed only near the exact solution (the `h²`-free bound uses the global factored
  assumption; the `O(h (h + ε))` bound `distLR_flow_le` is local).
* OP-RA-16: the structural rank bound, the step count and the error lower bound are proved.
  Open: whether `r*` is reached in about `log₂` steps for generic gradient fields.
* OP-OT-19: monotonicity of all robust bounds under enrichment and in the rank is proved.  Open:
  an explicit example where the errors themselves are not monotone in the rank.
-/

open Set Metric
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### The low-rank set and the distance to it -/

section Basic

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
lemma zero_mem_lowRankSet (r : ℕ) : (0 : Matrix m n ℝ) ∈ lowRankSet m n r := by simp

omit [Fintype m] in
lemma lowRankSet_nonempty (r : ℕ) : (lowRankSet m n r).Nonempty := ⟨0, zero_mem_lowRankSet r⟩

omit [Fintype m] in
lemma lowRankSet_mono {r r' : ℕ} (h : r ≤ r') : lowRankSet m n r ⊆ lowRankSet m n r' :=
  fun _ hY => le_trans hY h

variable {r r' k : ℕ} {X Y Z : Matrix m n ℝ}

lemma distLR_nonneg : 0 ≤ distLR r X := infDist_nonneg

/-- Every matrix of rank `≤ r` bounds the distance: `dist(X, M_{≤ r}) ≤ ‖X - Z‖`. -/
lemma distLR_le_norm_sub (hZ : Z.rank ≤ r) : distLR r X ≤ ‖X - Z‖ := by
  rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hZ

lemma distLR_eq_zero_of_rank_le (h : X.rank ≤ r) : distLR r X = 0 := infDist_zero_of_mem h

lemma distLR_le_norm : distLR r X ≤ ‖X‖ := by
  simpa using distLR_le_norm_sub (X := X) (zero_mem_lowRankSet (m := m) (n := n) r)

/-- Characterisation of lower bounds of the distance. -/
lemma le_distLR_iff {c : ℝ} : c ≤ distLR r X ↔ ∀ Z : Matrix m n ℝ, Z.rank ≤ r → c ≤ ‖X - Z‖ := by
  rw [distLR, le_infDist (lowRankSet_nonempty r)]
  simp only [mem_lowRankSet, dist_eq_norm]

/-- **The distance to `M_{≤ r}` is `1`-Lipschitz**: `dist(X, M_{≤ r}) ≤ dist(Y, M_{≤ r}) + ‖X - Y‖`
(`Metric.infDist_le_infDist_add_dist`; no singular value decomposition is involved). -/
theorem distLR_le_add (X Y : Matrix m n ℝ) : distLR r X ≤ distLR r Y + ‖X - Y‖ := by
  rw [← dist_eq_norm]; exact infDist_le_infDist_add_dist

theorem abs_distLR_sub_le (X Y : Matrix m n ℝ) : |distLR r X - distLR r Y| ≤ ‖X - Y‖ := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [distLR_le_add (r := r) X Y]
  · linarith [distLR_le_add (r := r) Y X, norm_sub_rev X Y]

theorem lipschitzWith_distLR (r : ℕ) : LipschitzWith 1 (distLR (m := m) (n := n) r) :=
  lipschitz_infDist_pt _

/-- **Monotonicity in the rank**: `dist(X, M_{≤ r'}) ≤ dist(X, M_{≤ r})` for `r ≤ r'`. -/
theorem distLR_antitone (h : r ≤ r') : distLR r' X ≤ distLR r X :=
  infDist_le_infDist_of_subset (lowRankSet_mono h) (lowRankSet_nonempty r)

lemma distLR_eq_zero_of_card_width_le (h : Fintype.card n ≤ r) : distLR r X = 0 :=
  distLR_eq_zero_of_rank_le (X.rank_le_card_width.trans h)

lemma distLR_eq_zero_of_card_height_le (h : Fintype.card m ≤ r) : distLR r X = 0 :=
  distLR_eq_zero_of_rank_le (X.rank_le_card_height.trans h)

end Basic

/-! ### The `ε`-rank and the rank-tracking sandwich (OP-RA-03) -/

section EpsRank

variable {m n : Type*} [Fintype m] [Fintype n] {r k : ℕ} {ε ε' e θ : ℝ} {X Y Xs : Matrix m n ℝ}

lemma epsRank_set_nonempty (hε : 0 ≤ ε) : {k | distLR k X ≤ ε}.Nonempty :=
  ⟨X.rank, by simp [distLR_eq_zero_of_rank_le le_rfl, hε]⟩

/-- The `ε`-rank is admissible: `dist(X, M_{≤ rank_ε X}) ≤ ε`. -/
theorem distLR_epsRank_le (hε : 0 ≤ ε) : distLR (epsRank ε X) X ≤ ε :=
  Nat.sInf_mem (epsRank_set_nonempty hε)

theorem epsRank_le_of_distLR_le (h : distLR k X ≤ ε) : epsRank ε X ≤ k := Nat.sInf_le h

/-- Below the `ε`-rank the distance exceeds `ε`. -/
theorem lt_distLR_of_lt_epsRank (h : k < epsRank ε X) : ε < distLR k X :=
  lt_of_not_ge (Nat.notMem_of_lt_sInf h)

theorem epsRank_le_iff (hε : 0 ≤ ε) : epsRank ε X ≤ k ↔ distLR k X ≤ ε :=
  ⟨fun h => (distLR_antitone h).trans (distLR_epsRank_le hε), epsRank_le_of_distLR_le⟩

/-- The `ε`-rank never exceeds the rank. -/
theorem epsRank_le_rank (hε : 0 ≤ ε) : epsRank ε X ≤ X.rank :=
  epsRank_le_of_distLR_le (by rw [distLR_eq_zero_of_rank_le le_rfl]; exact hε)

/-- The `ε`-rank is antitone in the tolerance. -/
theorem epsRank_anti (hε : 0 ≤ ε) (h : ε ≤ ε') : epsRank ε' X ≤ epsRank ε X :=
  epsRank_le_of_distLR_le ((distLR_epsRank_le hε).trans h)

/-- A matrix `ε`-close to a matrix of rank `≤ r` has `ε`-rank `≤ r`. -/
theorem epsRank_le_of_norm_sub_le (hY : Y.rank ≤ r) (h : ‖X - Y‖ ≤ ε) : epsRank ε X ≤ r :=
  epsRank_le_of_distLR_le ((distLR_le_norm_sub hY).trans h)

/-- **Rank-tracking sandwich, lower half** (OP-RA-03). If `‖X - Y‖ ≤ e` and `ε ≥ 0`, then
`rank_{ε+e}(Y) ≤ rank_ε(X)`. -/
theorem epsRank_add_le (hε : 0 ≤ ε) (hXY : ‖X - Y‖ ≤ e) : epsRank (ε + e) Y ≤ epsRank ε X :=
  epsRank_le_of_distLR_le <|
    calc distLR (epsRank ε X) Y ≤ distLR (epsRank ε X) X + ‖Y - X‖ := distLR_le_add Y X
      _ ≤ ε + e := add_le_add (distLR_epsRank_le hε) (by rwa [norm_sub_rev])

/-- **Rank-tracking sandwich, upper half** (OP-RA-03). If `‖X - Y‖ ≤ e ≤ ε`, then
`rank_ε(X) ≤ rank_{ε-e}(Y)`. -/
theorem epsRank_le_sub (he : e ≤ ε) (hXY : ‖X - Y‖ ≤ e) : epsRank ε X ≤ epsRank (ε - e) Y :=
  epsRank_le_of_distLR_le <|
    calc distLR (epsRank (ε - e) Y) X ≤ distLR (epsRank (ε - e) Y) Y + ‖X - Y‖ :=
          distLR_le_add X Y
      _ ≤ (ε - e) + e := add_le_add (distLR_epsRank_le (by linarith)) hXY
      _ = ε := by ring

/-- **The `ε`-rank sandwich** (OP-RA-03, statement of the open-problem catalogue).  If the
numerical value `X` is `e`-close to the exact value `Y` and `e ≤ ε`, then

    rank_{ε+e}(Y) ≤ rank_ε(X) ≤ rank_{ε-e}(Y).

So the numerical `ε`-rank of a convergent method tracks the exact `ε`-ranks, with the tolerance
shifted by the error.  No singular value decomposition is used: the proof is the `1`-Lipschitz
property of `dist(·, M_{≤ k})`. -/
theorem epsRank_sandwich (he : e ≤ ε) (hXY : ‖X - Y‖ ≤ e) :
    epsRank (ε + e) Y ≤ epsRank ε X ∧ epsRank ε X ≤ epsRank (ε - e) Y :=
  ⟨epsRank_add_le (((norm_nonneg _).trans hXY).trans he) hXY, epsRank_le_sub he hXY⟩

/-- **Exact rank identification** (OP-RA-03 (v); FeDLRT, arXiv 2410.18720).  Let `Xs` have rank
`≤ k + 1` and be separated from `M_{≤ k}` by `dist(Xs, M_{≤ k}) > θ + e` (by Eckart–Young the
left-hand side is `≥ σ_{k+1}(Xs)`).  Then every `X` with `‖X - Xs‖ ≤ e ≤ θ` has `θ`-rank exactly
`k + 1`: tolerance truncation identifies the exact target rank once the iterate is close. -/
theorem epsRank_eq_of_norm_sub_le (hXs : Xs.rank ≤ k + 1) (hXY : ‖X - Xs‖ ≤ e) (he : e ≤ θ)
    (hgap : θ + e < distLR k Xs) : epsRank θ X = k + 1 := by
  have hθ : 0 ≤ θ := ((norm_nonneg _).trans hXY).trans he
  apply le_antisymm
  · exact (epsRank_le_sub he hXY).trans (epsRank_le_rank (by linarith) |>.trans hXs)
  · by_contra hlt
    have hk : epsRank θ X ≤ k := by omega
    have h1 := (epsRank_le_iff hθ).1 hk
    have h2 := distLR_le_add (r := k) Xs X
    rw [norm_sub_rev] at h2
    linarith

/-- **Geometric convergence to a rank-one equilibrium** (OP-RA-03 (iv); arXiv 2308.05914,
Sec. 5): if `‖F_j - F_eq‖ ≤ c^j C` with `rank F_eq ≤ 1`, then `dist(F_j, M_{≤ 1}) ≤ c^j C`
(by Eckart–Young: `(σ₂² + σ₃² + ⋯)^{1/2}(F_j) ≤ c^j C`). -/
theorem distLR_one_le_of_geometric {F : ℕ → Matrix m n ℝ} {Feq : Matrix m n ℝ}
    (hFeq : Feq.rank ≤ 1) {c C : ℝ} (hconv : ∀ j, ‖F j - Feq‖ ≤ c ^ j * C) (j : ℕ) :
    distLR 1 (F j) ≤ c ^ j * C :=
  (distLR_le_norm_sub hFeq).trans (hconv j)

/-- Under geometric convergence to a rank-one equilibrium, the numerical `ε`-rank is at most `1`
as soon as `c^j C ≤ ε` (OP-RA-03 (iv)). -/
theorem epsRank_le_one_of_geometric {F : ℕ → Matrix m n ℝ} {Feq : Matrix m n ℝ}
    (hFeq : Feq.rank ≤ 1) {c C : ℝ} (hconv : ∀ j, ‖F j - Feq‖ ≤ c ^ j * C) {j : ℕ}
    (hj : c ^ j * C ≤ ε) : epsRank ε (F j) ≤ 1 :=
  epsRank_le_of_distLR_le ((distLR_one_le_of_geometric hFeq hconv j).trans hj)

end EpsRank

/-! ### Lower bounds for the distance -/

section LowerBound

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
/-- A matrix of rank `< card n` has a nontrivial kernel. -/
theorem exists_mulVec_eq_zero_of_rank_lt {Z : Matrix m n ℝ} (h : Z.rank < Fintype.card n) :
    ∃ x : n → ℝ, x ≠ 0 ∧ Z *ᵥ x = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker Z.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hrk : Z.rank = Module.finrank ℝ (LinearMap.range Z.mulVecLin) := rfl
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker Z.mulVecLin) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine ⟨x, fun h0 => hx0 (by simp [h0]), by simpa using hx⟩

/-- Cauchy–Schwarz for the Frobenius norm: `‖M x‖₂² ≤ ‖M‖_F² ‖x‖₂²`. -/
theorem sum_sq_mulVec_le (M : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (M *ᵥ x) i ^ 2 ≤ ‖M‖ ^ 2 * ∑ j, x j ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa [Matrix.mulVec, dotProduct] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) x

/-- **Lower bound by the smallest singular value, without SVD.**  If `‖A x‖₂ ≥ c ‖x‖₂` for all
`x` (`c ≥ 0`) and `r < card n`, then `dist(A, M_{≤ r}) ≥ c`.  (Every `Z` of rank `≤ r` has a
kernel vector `x`, and `‖A - Z‖_F ‖x‖ ≥ ‖(A - Z) x‖ = ‖A x‖ ≥ c ‖x‖`.) -/
theorem le_distLR_of_le_mulVec {A : Matrix m n ℝ} {r : ℕ} (hr : r < Fintype.card n) {c : ℝ}
    (hc : 0 ≤ c) (hA : ∀ x : n → ℝ, c ^ 2 * ∑ j, x j ^ 2 ≤ ∑ i, (A *ᵥ x) i ^ 2) :
    c ≤ distLR r A := by
  rw [le_distLR_iff]
  intro Z hZ
  obtain ⟨x, hx0, hZx⟩ := exists_mulVec_eq_zero_of_rank_lt (lt_of_le_of_lt hZ hr)
  have hxpos : 0 < ∑ j, x j ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
    have hj' : 0 < x j ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))
    exact lt_of_lt_of_le hj'
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ j))
  have h1 : (A - Z) *ᵥ x = A *ᵥ x := by rw [Matrix.sub_mulVec, hZx, sub_zero]
  have h2 := sum_sq_mulVec_le (A - Z) x
  rw [h1] at h2
  have h3 : c ^ 2 ≤ ‖A - Z‖ ^ 2 := le_of_mul_le_mul_right (by linarith [hA x]) hxpos
  exact (pow_le_pow_iff_left₀ hc (norm_nonneg _) two_ne_zero).mp h3

/-- **Diagonal matrices**: if `|d i| ≥ c ≥ 0` for all `i` and `r < card n`, then
`dist(diag d, M_{≤ r}) ≥ c`. -/
theorem le_distLR_diagonal [DecidableEq n] {d : n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ i, c ≤ |d i|) {r : ℕ} (hr : r < Fintype.card n) :
    c ≤ distLR r (Matrix.diagonal d) := by
  refine le_distLR_of_le_mulVec hr hc fun x => ?_
  simp only [Matrix.mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : c ^ 2 ≤ d i ^ 2 := by
    rw [← sq_abs (d i)]; exact pow_le_pow_left₀ hc (hd i) 2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

end LowerBound

/-! ### Closedness of `M_{≤ r}`, best approximations and the `ε`-rank -/

section Closed

open Filter Topology

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Stiefel set `{U ∈ ℝ^{m×r} : Uᵀ U = I}` is compact (closed, and bounded by `‖I_r‖`). -/
theorem isCompact_stiefel (r : ℕ) : IsCompact {U : Matrix m (Fin r) ℝ | Uᵀ * U = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Matrix m (Fin r) ℝ))
      (r := ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖)).subset fun U hU => ?_
    rw [mem_closedBall, dist_zero_right]
    have := Frobenius.norm_mul_of_orthonormal (show Uᵀ * U = 1 from hU)
      (1 : Matrix (Fin r) (Fin r) ℝ)
    rw [Matrix.mul_one] at this
    exact this.le

/-- **`M_{≤ r}` is closed** (lower semicontinuity of the rank).  For `r ≤ card m`, a limit `X` of
`X_k ∈ M_{≤ r}` is captured by a limit `U₀` of orthonormal bases `U_k` (`U_k U_kᵀ X_k = X_k`,
compactness of the Stiefel set), so `X = U₀ U₀ᵀ X` has rank `≤ r`. -/
theorem isClosed_lowRankSet (r : ℕ) : IsClosed (lowRankSet m n r) := by
  by_cases hrm : r ≤ Fintype.card m
  · apply isClosed_of_closure_subset
    intro X hX
    rw [mem_closure_iff_seq_limit] at hX
    obtain ⟨Xs, hXs, hlim⟩ := hX
    choose U hU hUX using fun k => exists_orthonormal_capture (Xs k) (hXs k) hrm
    obtain ⟨U₀, hU₀, φ, hφ, hUlim⟩ := (isCompact_stiefel (m := m) r).tendsto_subseq hU
    have hcont : Continuous fun V : Matrix m (Fin r) ℝ => V * Vᵀ := by fun_prop
    have hP : Tendsto (fun k => ‖U (φ k) * (U (φ k))ᵀ - U₀ * U₀ᵀ‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 ((hcont.tendsto U₀).comp hUlim)
    have hXk : Tendsto (fun k => ‖Xs (φ k) - X‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hlim.comp hφ.tendsto_atTop)
    have hg : Tendsto (fun k => ‖U (φ k) * (U (φ k))ᵀ - U₀ * U₀ᵀ‖ * ‖X‖ + 2 * ‖Xs (φ k) - X‖)
        atTop (𝓝 0) := by
      simpa using (hP.mul_const ‖X‖).add (hXk.const_mul 2)
    have hbound : ∀ k, ‖U₀ * U₀ᵀ * X - X‖ ≤
        ‖U (φ k) * (U (φ k))ᵀ - U₀ * U₀ᵀ‖ * ‖X‖ + 2 * ‖Xs (φ k) - X‖ := by
      intro k
      set V := U (φ k)
      set Y := Xs (φ k)
      have hV : Vᵀ * V = 1 := hU (φ k)
      have hVY : V * Vᵀ * Y = Y := hUX (φ k)
      have hdec : U₀ * U₀ᵀ * X - X =
          -((V * Vᵀ - U₀ * U₀ᵀ) * X) + V * Vᵀ * (X - Y) + (Y - X) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, hVY]; abel
      have h1 : ‖(V * Vᵀ - U₀ * U₀ᵀ) * X‖ ≤ ‖V * Vᵀ - U₀ * U₀ᵀ‖ * ‖X‖ :=
        Frobenius.norm_mul_le _ _
      have h2 : ‖V * Vᵀ * (X - Y)‖ ≤ ‖X - Y‖ := by
        simpa using (isOrthProj_leftProj (n := n) hV).norm_le (X - Y)
      rw [hdec]
      calc _ ≤ ‖-((V * Vᵀ - U₀ * U₀ᵀ) * X) + V * Vᵀ * (X - Y)‖ + ‖Y - X‖ := norm_add_le _ _
        _ ≤ ‖(V * Vᵀ - U₀ * U₀ᵀ) * X‖ + ‖V * Vᵀ * (X - Y)‖ + ‖Y - X‖ := by
          gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ _ := by rw [norm_sub_rev X Y] at h2; linarith
    have hfix : U₀ * U₀ᵀ * X = X := by
      have := ge_of_tendsto' hg hbound
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    change X.rank ≤ r
    rw [← hfix]
    calc (U₀ * U₀ᵀ * X).rank ≤ (U₀ * U₀ᵀ).rank := Matrix.rank_mul_le_left _ _
      _ ≤ U₀.rank := Matrix.rank_mul_le_left _ _
      _ ≤ r := by simpa using U₀.rank_le_card_width
  · have : lowRankSet m n r = univ :=
      eq_univ_of_forall fun X => (X.rank_le_card_height.trans (by omega) : X.rank ≤ r)
    rw [this]; exact isClosed_univ
variable {r k : ℕ} {ε : ℝ} {X : Matrix m n ℝ}

/-- `dist(X, M_{≤ r}) = 0` iff `rank X ≤ r`. -/
theorem distLR_eq_zero_iff : distLR r X = 0 ↔ X.rank ≤ r :=
  ((isClosed_lowRankSet r).mem_iff_infDist_zero (lowRankSet_nonempty r)).symm

/-- **Existence of a best rank-`r` approximation** (the existence part of Eckart–Young, without
SVD): there is `Z` with `rank Z ≤ r` and `‖X - Z‖ = dist(X, M_{≤ r})`.  So the quasi-best
truncation hypotheses with `κ = 1` (truncated SVD) are always satisfiable. -/
theorem exists_best_approx (r : ℕ) (X : Matrix m n ℝ) :
    ∃ Z : Matrix m n ℝ, Z.rank ≤ r ∧ ‖X - Z‖ = distLR r X := by
  obtain ⟨Z, hZ, h⟩ := (isClosed_lowRankSet r).exists_infDist_eq_dist (lowRankSet_nonempty r) X
  exact ⟨Z, hZ, by rw [distLR, h, dist_eq_norm]⟩

/-- **The `ε`-rank is the smallest rank within distance `ε`**: `rank_ε(X) ≤ k` iff some `Z` of
rank `≤ k` satisfies `‖X - Z‖ ≤ ε`.  This is the matrix form of the tolerance truncation rule
(eq. (22) of arXiv 2602.06614, step 3 of arXiv 2104.05247) without singular values. -/
theorem epsRank_le_iff_exists (hε : 0 ≤ ε) :
    epsRank ε X ≤ k ↔ ∃ Z : Matrix m n ℝ, Z.rank ≤ k ∧ ‖X - Z‖ ≤ ε := by
  rw [epsRank_le_iff hε]
  constructor
  · intro h
    obtain ⟨Z, hZ, hXZ⟩ := exists_best_approx k X
    exact ⟨Z, hZ, hXZ ▸ h⟩
  · rintro ⟨Z, hZ, hXZ⟩
    exact (distLR_le_norm_sub hZ).trans hXZ

/-- **Tolerance truncation is realised**: there is `Z` of rank `≤ rank_ε(X)` with
`‖X - Z‖ ≤ ε`. -/
theorem exists_epsRank_approx (hε : 0 ≤ ε) :
    ∃ Z : Matrix m n ℝ, Z.rank ≤ epsRank ε X ∧ ‖X - Z‖ ≤ ε :=
  (epsRank_le_iff_exists hε).1 le_rfl

/-- The `0`-rank is the rank. -/
theorem epsRank_zero : epsRank 0 X = X.rank :=
  le_antisymm (epsRank_le_rank le_rfl)
    (distLR_eq_zero_iff.1 (le_antisymm (distLR_epsRank_le le_rfl) distLR_nonneg))

end Closed

/-! ### Robust capture of the exact flow by the low-rank set (OP-EX-02) -/

section FlowCapture

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

omit [DecidableEq m] [DecidableEq n] in
/-- **Factorisation of a matrix of rank `≤ r`.**  If `rank Y ≤ r ≤ min(card m, card n)`, then
`Y = U S Vᵀ` with `U : m × r`, `V : n × r` with orthonormal columns and `S : r × r` (possibly
singular). -/
theorem exists_factor_of_rank_le {Y : Matrix m n ℝ} (hY : Y.rank ≤ r)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Y = U * S * Vᵀ := by
  obtain ⟨U, hU, hUY⟩ := exists_orthonormal_capture Y hY hrm
  obtain ⟨V, hV, hVY⟩ := exists_orthonormal_capture Yᵀ (by rwa [Matrix.rank_transpose]) hrn
  have hYV : Y * V * Vᵀ = Y := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hVY
  refine ⟨U, Uᵀ * Y * V, V, hU, hV, ?_⟩
  calc Y = U * Uᵀ * (Y * V * Vᵀ) := by rw [hYV, hUY]
    _ = U * (Uᵀ * Y * V) * Vᵀ := by simp only [Matrix.mul_assoc]

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε h t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Robust flow capture** (OP-EX-02, main form).  Let `F` be `L`-Lipschitz (`L ≥ 0`), bounded
by `B` and continuous in time, and let `A` be an exact solution of `A' = F(t, A)` on
`[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, starting at a matrix of rank `≤ r ≤ min(m, n)`.  If the
factored normal component is `ε`-small within distance `B h` of `A(t₀)`, then there are
`U₁ : m × r`, `V₁ : n × r` with orthonormal columns (the bases of one BUG step from `A(t₀)`) with

    ‖A(t₁) - U₁ U₁ᵀ A(t₁) V₁ V₁ᵀ‖ ≤ 2 h (4 L B h + ε).

No rank-`r` DLRA solution and no lower bound on singular values are needed: the BUG substeps
exist by `MatrixBUG.exists_isStep` (rank-deficient `K(t₁)` allowed), the normal-component bound
is used only at the end points `K(t₁) V₀ᵀ` and `U₀ L(t₁)ᵀ` of the K- and L-steps (which are
within `B h` of `A(t₀)` by the speed lemma), and `bug_capture` concludes. -/
theorem exists_capture_flow (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (hε : NearNormalBound F r ε t₀ t₁ (A t₀) (B * h)) :
    ∃ (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ), U₁ᵀ * U₁ = 1 ∧ V₁ᵀ * V₁ = 1 ∧
      ‖A t₁ - U₁ * U₁ᵀ * A t₁ * V₁ * V₁ᵀ‖ ≤ 2 * (h * (4 * L * B * h + ε)) := by
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, hY⟩ := exists_factor_of_rank_le hrank hrm hrn
  have h01 : t₀ ≤ t₁ := by linarith
  have ht₁mem : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  obtain ⟨U₁, V₁, K, Lf, S, hs⟩ := MatrixBUG.exists_isStep hF hB hc h01 S₀ hU₀ hV₀ hrm hrn
  have hb := hs.isBUGStep_of_normal (ε := ε) (fun t ht => ?_) (fun t ht => ?_)
  · have hcap := bug_capture hF hL hB hb.projP₀ hb.projQ₀ hb.projP₁ hb.projQ₁ ht₁ hh hA hb.kSol
      (hb.kStart.trans hY.symm) hb.kCap hb.kNormal hb.lSol (hb.lStart.trans hY.symm) hb.lCap
      hb.lNormal
    refine ⟨U₁, V₁, hs.orthU₁, hs.orthV₁, ?_⟩
    simpa [Matrix.mul_assoc] using hcap
  · have hK : K t₁ * V₀ᵀ = U₁ * (U₁ᵀ * K t₁) * V₀ᵀ := by rw [← Matrix.mul_assoc, hs.kCap]
    have hdist : ‖K t₁ * V₀ᵀ - A t₀‖ ≤ B * h := by
      have := (MatrixBUG.odeSolution_kField hs.kSol).norm_sub_start_le_of_proj hB
        (isOrthProj_rightProj hs.orthV₀) ht₁ t₁ ht₁mem
      rwa [hs.yk_start, ← hY] at this
    rw [hK] at hdist ⊢
    exact hε t ht U₁ V₀ _ hs.orthU₁ hs.orthV₀ hdist
  · have hT : (Lf t₁)ᵀ * V₁ * V₁ᵀ = (Lf t₁)ᵀ := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
    have hLL : U₀ * (Lf t₁)ᵀ = U₀ * ((Lf t₁)ᵀ * V₁) * V₁ᵀ := by
      rw [Matrix.mul_assoc U₀, hT]
    have hdist : ‖U₀ * (Lf t₁)ᵀ - A t₀‖ ≤ B * h := by
      have := (MatrixBUG.odeSolution_lField hs.lSol).norm_sub_start_le_of_proj hB
        (isOrthProj_leftProj hs.orthU₀) ht₁ t₁ ht₁mem
      rwa [hs.yl_start, ← hY] at this
    rw [hLL] at hdist ⊢
    exact hε t ht U₀ V₁ _ hs.orthU₀ hs.orthV₁ hdist

/-- **Robust flow capture, existential form** (OP-EX-02): under the hypotheses of
`exists_capture_flow` there is `Z` of rank `≤ r` with `‖A(t₁) - Z‖ ≤ 2 h (4 L B h + ε)`. -/
theorem exists_lowRank_near_flow (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n)
    (hε : NearNormalBound F r ε t₀ t₁ (A t₀) (B * h)) :
    ∃ Z : Matrix m n ℝ, Z.rank ≤ r ∧ ‖A t₁ - Z‖ ≤ 2 * (h * (4 * L * B * h + ε)) := by
  obtain ⟨U₁, V₁, -, -, hcap⟩ :=
    exists_capture_flow hF hL hB hc ht₁ hh hA hrank hrm hrn hε
  refine ⟨U₁ * (U₁ᵀ * A t₁ * V₁) * V₁ᵀ, rank_mul_mul_transpose_le _ _ _, ?_⟩
  simpa [Matrix.mul_assoc] using hcap

/-- **Robust substitute for the existence of the projected DLRA flow** (OP-EX-02).  For every
exact solution `A` on `[t₀, t₁]`, `t₁ = t₀ + h`, starting at a matrix of rank `≤ r`,

    dist(A(t₁), M_{≤ r}) ≤ 2 h (4 L B h + ε),

where `ε` bounds the factored normal component within distance `B h` of `A(t₀)`.  This holds
for *every* rank `r` (if `r ≥ min(m, n)` the distance is `0`) and every starting value of rank
`≤ r`, however small its singular values.  It is the consequence of the (in general
unavailable) rank-`r` DLRA flow `X(t)` from `A(t₀)` that the convergence proofs listed in
OP-EX-02 use, namely `dist(A(t₁), M_r) ≤ ‖A(t₁) - X(t₁)‖ = O(h ε)`, with an additional
`O(h²)` term. -/
theorem distLR_flow_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (hε0 : 0 ≤ ε)
    (hε : NearNormalBound F r ε t₀ t₁ (A t₀) (B * h)) :
    distLR r (A t₁) ≤ 2 * (h * (4 * L * B * h + ε)) := by
  by_cases hrm : r ≤ Fintype.card m
  · by_cases hrn : r ≤ Fintype.card n
    · obtain ⟨Z, hZ, hAZ⟩ := exists_lowRank_near_flow hF hL hB hc ht₁ hh hA hrank hrm hrn hε
      exact (distLR_le_norm_sub hZ).trans hAZ
    · rw [distLR_eq_zero_of_card_width_le (by omega)]
      have := hB.nonneg
      positivity
  · rw [distLR_eq_zero_of_card_height_le (by omega)]
    have := hB.nonneg
    positivity

/-- **Robust flow capture under the global factored assumption** (OP-EX-02):
`dist(A(t₁), M_{≤ r}) ≤ 2 h (4 L B h + ε)` for every exact solution starting in `M_{≤ r}`. -/
theorem distLR_flow_le_of_factored (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) :
    distLR r (A t₁) ≤ 2 * (h * (4 * L * B * h + ε)) :=
  distLR_flow_le hF hL hB hc ht₁ hh hA hrank hε0 (nearNormalBound_of_factored hε _ _ _ _)

/-- **The exact flow from every low-rank value stays close to the low-rank set** (OP-EX-02,
flow form).  For every `Y` of rank `≤ r` there is an exact solution `A` on `[t₀, t₁]` with
`A(t₀) = Y`, and every such solution satisfies `dist(A(t₁), M_{≤ r}) ≤ 2 h (4 L B h + ε)`. -/
theorem exists_flow_distLR_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hε0 : 0 ≤ ε) (hε : MatrixBUG.FactoredNormalBound F r ε) (Y : Matrix m n ℝ)
    (hY : Y.rank ≤ r) :
    ∃ A : ℝ → Matrix m n ℝ, ODESolution F A t₀ t₁ ∧ A t₀ = Y ∧
      distLR r (A t₁) ≤ 2 * (h * (4 * L * B * h + ε)) := by
  obtain ⟨A, hA, hA₀⟩ := exists_ODESolution hF hB hc (by linarith : t₀ ≤ t₁) Y
  exact ⟨A, hA, hA₀, distLR_flow_le_of_factored hF hL hB hc ht₁ hh hA (hA₀ ▸ hY) hε0 hε⟩

/-- **Quasi-best truncation of the exact flow** (OP-EX-02, consequence for truncation-based
schemes such as randomized low-rank Runge–Kutta or PRK-DEIM).  If `T` is a `κ`-quasi-best
rank-`r` approximation of `A(t₁)`, `‖T - A(t₁)‖ ≤ κ dist(A(t₁), M_{≤ r})`, then
`‖T - A(t₁)‖ ≤ 2 κ h (4 L B h + ε)`. -/
theorem norm_quasiBest_flow_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (hε0 : 0 ≤ ε)
    (hε : NearNormalBound F r ε t₀ t₁ (A t₀) (B * h)) {κ : ℝ} (hκ : 0 ≤ κ)
    {T : Matrix m n ℝ} (hT : ‖T - A t₁‖ ≤ κ * distLR r (A t₁)) :
    ‖T - A t₁‖ ≤ κ * (2 * (h * (4 * L * B * h + ε))) :=
  hT.trans (mul_le_mul_of_nonneg_left (distLR_flow_le hF hL hB hc ht₁ hh hA hrank hε0 hε) hκ)

end FlowCapture

/-! ### Rank-`r` truncation without a rank-`r` DLRA solution (OP-RA-07) -/

section Truncation

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **Gap-free truncation inequality** (arXiv 2402.08607, Remark 4; arXiv 2608.27749,
Remark 2, abstract core).  If `T` is a `κ`-quasi-best rank-`r` approximation of `Ŷ`,
`‖T - Ŷ‖ ≤ κ dist(Ŷ, M_{≤ r})` (`κ = 1`: truncated SVD), then for every `A₁`

    ‖T - A₁‖ ≤ κ dist(A₁, M_{≤ r}) + (1 + κ) ‖Ŷ - A₁‖.

The papers state this for `κ = 1` with `dist(A₁, M_r) ≤ ‖X(t₁) - A(t₁)‖ = O(h ε_r)` imported from
a rank-`r` DLRA solution `X`; here the distance is kept, and bounded robustly in
`norm_trunc_flow_le`. -/
theorem norm_trunc_sub_le {Yh A₁ T : Matrix m n ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hT : ‖T - Yh‖ ≤ κ * distLR r Yh) :
    ‖T - A₁‖ ≤ κ * distLR r A₁ + (1 + κ) * ‖Yh - A₁‖ := by
  have h1 := mul_le_mul_of_nonneg_left (distLR_le_add (r := r) Yh A₁) hκ
  have h2 := norm_sub_le_norm_sub_add_norm_sub T Yh A₁
  nlinarith

/-- The best-approximation case `κ = 1` of `norm_trunc_sub_le`:
`‖T - A₁‖ ≤ dist(A₁, M_{≤ r}) + 2 ‖Ŷ - A₁‖` (the inequality of arXiv 2608.27749, Remark 2). -/
theorem norm_bestTrunc_sub_le {Yh A₁ T : Matrix m n ℝ} (hT : ‖T - Yh‖ ≤ distLR r Yh) :
    ‖T - A₁‖ ≤ distLR r A₁ + 2 * ‖Yh - A₁‖ := by
  have := norm_trunc_sub_le (r := r) (A₁ := A₁) zero_le_one (by rwa [one_mul])
  linarith

variable [DecidableEq m] [DecidableEq n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L B ε h t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Robust rank-`r` truncation bound** (OP-RA-07, robust part; arXiv 2402.08607, Remark 4 and
arXiv 2608.27749, Remark 2 without a rank-`r` DLRA solution).  Let `A` be the exact solution on
`[t₀, t₁]` from a value of rank `≤ r`, `Ŷ` any approximation of `A(t₁)` (e.g. the augmented,
midpoint or parallel BUG result), and `T` a `κ`-quasi-best rank-`r` approximation of `Ŷ`.  Then

    ‖T - A(t₁)‖ ≤ 2 κ h (4 L B h + ε_r) + (1 + κ) ‖Ŷ - A(t₁)‖,

with `ε_r` the factored normal-component bound at rank `r` within `B h` of `A(t₀)`.  Compared with
the papers' `h ε_r + 2 ‖Ŷ - A(t₁)‖`, the constant in front of `h ε_r` is `2 κ` and there is an
extra `8 κ L B h²` term; no singular value of the exact or approximate solution enters. -/
theorem norm_trunc_flow_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (hε0 : 0 ≤ ε)
    (hε : NearNormalBound F r ε t₀ t₁ (A t₀) (B * h)) {κ : ℝ} (hκ : 0 ≤ κ)
    {Yh T : Matrix m n ℝ} (hT : ‖T - Yh‖ ≤ κ * distLR r Yh) :
    ‖T - A t₁‖ ≤ κ * (2 * (h * (4 * L * B * h + ε))) + (1 + κ) * ‖Yh - A t₁‖ := by
  have h1 := norm_trunc_sub_le (A₁ := A t₁) hκ hT
  have h2 := mul_le_mul_of_nonneg_left
    (distLR_flow_le hF hL hB hc ht₁ hh hA hrank hε0 hε) hκ
  linarith

/-- **Fixed-rank truncation of the rank-adaptive (augmented) BUG step** (OP-RA-07; the
"rank truncation" of arXiv 2402.08607, Remark 4 for the augmented BUG integrator of
arXiv 2104.05247).  If the augmented result `Ŷ₁ = Û Ŝ(t₁) V̂ᵀ` is truncated back to rank `r`
by a `κ`-quasi-best approximation `T`, then for step sizes `0 ≤ h ≤ H`

    ‖T - A(t₁)‖ ≤ 2 κ h (4 L B h + ε) + (1 + κ) h (c₁ ε + c₂ h),

an `O(h (h + ε))` local error with **no tolerance term `ϑ`**, under the factored
normal-component assumption at rank `r` only.  (The truncation tolerance of the step,
`hs.trunc`, is irrelevant here: only the untruncated `Ŷ₁` enters.) -/
theorem fixedRank_trunc_local_error_le {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k]
    [DecidableEq k'] {ϑ : ℝ} {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ}
    {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ}
    {Y₁ : Matrix m n ℝ} (hs : MatrixBUG.IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : MatrixBUG.FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) {κ : ℝ} (hκ : 0 ≤ κ) {T : Matrix m n ℝ}
    (hT : ‖T - Ua * Sa t₁ * Vaᵀ‖ ≤ κ * distLR r (Ua * Sa t₁ * Vaᵀ)) :
    ‖T - A t₁‖ ≤ κ * (2 * (h * (4 * L * B * h + ε)))
      + (1 + κ) * (h * (bugC₁ L H * ε + bugC₂ L B H * h)) := by
  have hs' : MatrixBUG.IsRankAdaptiveStep F 0 t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa
      (Ua * Sa t₁ * Vaᵀ) := { hs with trunc := by simp }
  have hloc := hs'.local_error_le hε hF hL hB ht₁ hh hhH hA hA₀
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε t₀ U₀ V₀ S₀ hs.orthU₀ hs.orthV₀)
  have hrank : (A t₀).rank ≤ r := hA₀ ▸ rank_mul_mul_transpose_le U₀ S₀ V₀
  have h1 := norm_trunc_flow_le hF hL hB hc ht₁ hh hA hrank hε0
    (nearNormalBound_of_factored hε _ _ _ _) hκ hT
  have h2 := mul_le_mul_of_nonneg_left (by simpa using hloc) (by linarith : (0 : ℝ) ≤ 1 + κ)
  linarith

end Truncation

/-! ### The counterexample: `ε` measured only at the starting point (OP-RA-07) -/

section Counterexample

open MatrixBUG

/-- The constant field `F ≡ [[0, 1], [1, 0]]` of the counterexample (`L = 0`). -/
def swapMat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The starting value `Y₀ = diag(δ, 0) = e₁ (δ) e₁ᵀ` of rank `≤ 1`. -/
noncomputable def cxY₀ (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  unitCol * (Matrix.of (fun _ _ => δ) : Matrix (Fin 1) (Fin 1) ℝ) * unitColᵀ

lemma cxY₀_apply (δ : ℝ) (i j : Fin 2) : cxY₀ δ i j = if i = 0 ∧ j = 0 then δ else 0 := by
  fin_cases i <;> fin_cases j <;> simp [cxY₀, Matrix.mul_apply]

/-- The exact solution at `t₁ = h` is `A(h) = [[δ, h], [h, 0]]`; it is `h/3`-far from rank one
for `0 ≤ δ ≤ h`. -/
theorem le_distLR_cx {δ h : ℝ} (hδ : 0 ≤ δ) (hδh : δ ≤ h) :
    h / 3 ≤ distLR 1 (cxY₀ δ + (h - 0) • swapMat) := by
  have hh : 0 ≤ h := hδ.trans hδh
  refine le_distLR_of_le_mulVec (by simp) (by positivity) fun x => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
    cxY₀_apply, swapMat]
  simp
  nlinarith [sq_nonneg (δ * x 0 + h * x 1 + δ * x 0), sq_nonneg (x 0), sq_nonneg (x 1),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hδh) (add_nonneg hδ hh)) (sq_nonneg (x 0))]

/-- **Counterexample to the rank-`r` truncation bound with `ε` measured only at `(t₀, Y₀)`**
(OP-RA-07).  Take `F ≡ [[0, 1], [1, 0]]` (`L = 0`), `Y₀ = diag(δ, 0)` of rank `≤ 1` with
`0 ≤ δ ≤ h`, `h > 0`.  Then

* the normal component of `F` at `Y₀ = e₁ δ e₁ᵀ` vanishes: `(I - e₁e₁ᵀ) F (I - e₁e₁ᵀ) = 0`;
* `A(t) = Y₀ + t F` is the exact solution, and `A(h) = [[δ, h], [h, 0]]` (this is also the result
  `Ŷ₁` of the augmented BUG step with the full bases `Û = V̂ = I`, `cx_isRankAdaptiveStep`, so
  `‖Ŷ₁ - A(h)‖ = 0`);
* `dist(A(h), M_{≤ 1}) ≥ h/3`.

Hence the claimed bound `‖T_1(Ŷ₁) - A(t₁)‖ ≤ h ε + 2 ‖Ŷ₁ - A(t₁)‖` with `ε = 0` measured at
`(t₀, Y₀)` fails for every rank-one `T`.  (The robust bound `norm_trunc_flow_le` is not
contradicted: the factored normal component of `F` at rank one is `1` at `U = e₁`, `V = e₂`.) -/
theorem trunc_bound_fails_of_normal_at_start {δ h : ℝ} (hδ : 0 ≤ δ) (hδh : δ ≤ h) (hh : 0 < h) :
    (cxY₀ δ).rank ≤ 1 ∧
    (1 - unitCol * unitColᵀ) * swapMat * (1 - unitCol * unitColᵀ) = 0 ∧
    ODESolution (fun _ _ => swapMat) (fun t => cxY₀ δ + (t - 0) • swapMat) 0 h ∧
    ¬ ∃ T : Matrix (Fin 2) (Fin 2) ℝ, T.rank ≤ 1 ∧
      ‖T - (cxY₀ δ + (h - 0) • swapMat)‖ ≤
        h * 0 + 2 * ‖(cxY₀ δ + (h - 0) • swapMat) - (cxY₀ δ + (h - 0) • swapMat)‖ := by
  refine ⟨rank_mul_mul_transpose_le _ _ _, ?_, odeSolution_affine _ _ _ _, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, swapMat, Matrix.sub_apply, Matrix.one_apply]
  · rintro ⟨T, hT, hle⟩
    have h1 := le_distLR_cx hδ hδh
    have h2 := distLR_le_norm_sub (X := cxY₀ δ + (h - 0) • swapMat) hT
    rw [norm_sub_rev] at h2
    simp only [mul_zero, sub_self, norm_zero, zero_add] at hle
    linarith

/-- The coefficient of the counterexample starting value, `S₀ = (δ)`. -/
def cxS₀ (δ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => δ

/-- **The augmented BUG step of the counterexample is exact** (OP-RA-07): from
`Y₀ = e₁ (δ) e₁ᵀ` with `F ≡ [[0, 1], [1, 0]]`, the rank-adaptive BUG step with the full augmented
bases `Û = V̂ = I` (they capture `K(h)`, `U₀`, `L(h)`, `V₀`) has untruncated result
`Ŷ₁ = Y₀ + h F = A(h)`, so `‖Ŷ₁ - A(h)‖ = 0` in `trunc_bound_fails_of_normal_at_start`. -/
theorem cx_isRankAdaptiveStep (δ h : ℝ) :
    IsRankAdaptiveStep (fun _ _ => swapMat) 0 0 h unitCol (cxS₀ δ) unitCol
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (fun t => unitCol * cxS₀ δ + (t - 0) • (swapMat * unitCol))
      (fun t => unitCol * (cxS₀ δ)ᵀ + (t - 0) • (swapMatᵀ * unitCol))
      (fun t => cxY₀ δ + (t - 0) • swapMat) (cxY₀ δ + (h - 0) • swapMat) where
  orthU₀ := unitCol_orth
  orthV₀ := unitCol_orth
  kSol := odeSolution_of_const (fun _ _ => by simp [kField]) _ _ _
  kStart := by simp
  lSol := odeSolution_of_const (fun _ _ => by simp [lField]) _ _ _
  lStart := by simp
  orthUa := by simp
  kCap := by simp
  augU := by simp
  orthVa := by simp
  lCap := by simp
  augV := by simp
  sSol := odeSolution_of_const (fun _ _ => by simp [sField]) _ _ _
  sStart := by simp [cxY₀, cxS₀, Matrix.mul_assoc]
  trunc := by simp

end Counterexample

/-! ### Rank growth of augmented steps (OP-RA-16) -/

section RankGrowth

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
/-- **Rank at most doubles** (OP-RA-16; arXiv 2602.06614, Sec. 3.1.1; arXiv 2104.05247,
Sec. 5): the augmented (or parallel) BUG result `Û Ŝ V̂ᵀ` with `2 r`-column bases has rank
`≤ 2 r`. -/
theorem rank_augmented_le {r : ℕ} (Ua : Matrix m (Fin (2 * r)) ℝ)
    (Sa : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (Va : Matrix n (Fin (2 * r)) ℝ) :
    (Ua * Sa * Vaᵀ).rank ≤ 2 * r :=
  rank_mul_mul_transpose_le Ua Sa Va

/-- **Rank after `j` doubling steps**: if the ranks satisfy `r_{i+1} ≤ 2 r_i`, then
`r_j ≤ 2^j r_0`. -/
theorem le_pow_mul_of_doubling {R : ℕ → ℕ} (h : ∀ i, R (i + 1) ≤ 2 * R i) (j : ℕ) :
    R j ≤ 2 ^ j * R 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc R (j + 1) ≤ 2 * R j := h j
      _ ≤ 2 * (2 ^ j * R 0) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (j + 1) * R 0 := by ring

/-- **Minimal number of steps to reach a target rank** (OP-RA-16 (i)): with rank doubling from
`r_0 > 0`, reaching rank `r* ≤ r_j` needs `j ≥ ⌈log₂ ⌈r*/r_0⌉⌉` steps
(`(r* + r_0 - 1) / r_0 = ⌈r*/r_0⌉`). -/
theorem clog_le_of_doubling {R : ℕ → ℕ} (h : ∀ i, R (i + 1) ≤ 2 * R i) (h0 : 0 < R 0)
    {rs j : ℕ} (hreach : rs ≤ R j) : Nat.clog 2 ((rs + R 0 - 1) / R 0) ≤ j := by
  apply Nat.clog_le_of_le_pow
  have hj := le_pow_mul_of_doubling h j
  have : (rs + R 0 - 1) / R 0 < 2 ^ j + 1 := by
    rw [Nat.div_lt_iff_lt_mul h0]
    have : rs + R 0 - 1 < 2 ^ j * R 0 + R 0 := by omega
    linarith [show (2 ^ j + 1) * R 0 = 2 ^ j * R 0 + R 0 by ring]
  omega

variable [DecidableEq m] [DecidableEq n] {k k' : Type*} [Fintype k] [Fintype k']
  [DecidableEq k] [DecidableEq k']

omit [DecidableEq m] [DecidableEq n] in
/-- **Error lower bound by the augmented subspace** (OP-RA-16; arXiv 2602.06614, Sec. 3.1.1,
second limitation).  Any matrix of the form `Ŷ = Û Ŝ V̂ᵀ` with orthonormal `Û`, `V̂` (the
augmented BUG result and all of its truncations) satisfies

    ‖A₁ - Û Ûᵀ A₁ V̂ V̂ᵀ‖ ≤ ‖A₁ - Ŷ‖,

so the error is bounded below by the part of `A₁` outside the augmented subspace, independently
of the truncation tolerance (best approximation by the orthogonal projector `P̂ Q̂`). -/
theorem norm_residual_le_norm_sub {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} (hUa : Uaᵀ * Ua = 1)
    (hVa : Vaᵀ * Va = 1) (Sa : Matrix k k' ℝ) (A₁ : Matrix m n ℝ) :
    ‖A₁ - Ua * Uaᵀ * A₁ * Va * Vaᵀ‖ ≤ ‖A₁ - Ua * Sa * Vaᵀ‖ := by
  have hfix : (leftProj Ua * rightProj Va : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (Ua * Sa * Vaᵀ) =
      Ua * Sa * Vaᵀ := by
    change leftProj Ua (rightProj Va (Ua * Sa * Vaᵀ)) = _
    rw [rightProj_mul_transpose hVa, Matrix.mul_assoc, leftProj_mul_left hUa]
  have h := (isOrthProj_leftProj_mul_rightProj (n := n) hUa hVa).norm_sub_le_of_mem_range A₁ _
    hfix
  simpa [Matrix.mul_assoc] using h

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq k'] in
/-- The residual outside a `card k`-dimensional left subspace dominates the distance to
`M_{≤ card k}`: `dist(A₁, M_{≤ card k}) ≤ ‖A₁ - Û Ûᵀ A₁ V̂ V̂ᵀ‖`. -/
theorem distLR_le_residual (Ua : Matrix m k ℝ) (Va : Matrix n k' ℝ) (A₁ : Matrix m n ℝ) :
    distLR (Fintype.card k) A₁ ≤ ‖A₁ - Ua * Uaᵀ * A₁ * Va * Vaᵀ‖ := by
  refine distLR_le_norm_sub ?_
  calc (Ua * Uaᵀ * A₁ * Va * Vaᵀ).rank ≤ (Ua * Uaᵀ * A₁ * Va).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Ua * Uaᵀ * A₁).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Ua * Uaᵀ).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Ua.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card k := Ua.rank_le_card_width

/-- The first unit vector of `ℝ³` as a `3 × 1` matrix. -/
def rgU : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

/-- The three-dimensional example of OP-RA-16 (ii): `Y₀ = e₁ e₁ᵀ` (rank one) and `F ≡ I₃`. -/
def rgY₀ : Matrix (Fin 3) (Fin 3) ℝ := rgU * (1 : Matrix (Fin 1) (Fin 1) ℝ) * rgUᵀ

/-- **Tolerance-independent error of one rank-adaptive step from rank one** (OP-RA-16 (ii)).
For `F ≡ I₃` (`L = 0`) and `Y₀ = e₁ e₁ᵀ` (rank one), the exact solution is `A(t) = Y₀ + t I`,
and **every** matrix of rank `≤ 2` — in particular every rank-adaptive BUG result with
`2`-column augmented bases, for every truncation tolerance — has error `≥ h` at `t₁ = h`.  The
rank-adaptive BUG integrator therefore cannot reach the exact rank `3` in one step. -/
theorem rankAdaptive_error_ge {h : ℝ} (hh : 0 ≤ h) :
    rgY₀.rank ≤ 1 ∧
    ODESolution (fun _ _ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun t => rgY₀ + (t - 0) • 1) 0 h ∧
    ∀ Y₁ : Matrix (Fin 3) (Fin 3) ℝ, Y₁.rank ≤ 2 → h ≤ ‖Y₁ - (rgY₀ + (h - 0) • 1)‖ := by
  refine ⟨rank_mul_mul_transpose_le _ _ _, MatrixBUG.odeSolution_affine _ _ _ _, ?_⟩
  intro Y₁ hY₁
  have hdiag : rgY₀ + (h - 0) • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.diagonal (fun i => if i = 0 then 1 + h else h) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rgY₀, rgU, Matrix.mul_apply]
  rw [hdiag, norm_sub_rev]
  refine (le_distLR_diagonal hh (fun i => ?_) (by simp : 2 < Fintype.card (Fin 3))).trans
    (distLR_le_norm_sub hY₁)
  split_ifs
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonneg hh]

/-- **The `ε`-rank truncation rule of arXiv 2602.06614, eq. (22)** (rank-adaptive BUG of
arXiv 2104.05247, step 3), in distance form: `R_new = rank_ϑ(Ŝ(t₁))` for the `2 R_old × 2 R_old`
coefficient matrix `Ŝ(t₁)`.  Then `R_new ≤ 2 R_old` (rank at most doubles) and the discarded
part is within tolerance, `dist(Ŝ(t₁), M_{≤ R_new}) ≤ ϑ`. -/
theorem epsRank_augmented_le {R : ℕ} (S : Matrix (Fin (2 * R)) (Fin (2 * R)) ℝ) {ϑ : ℝ}
    (hϑ : 0 ≤ ϑ) : epsRank ϑ S ≤ 2 * R ∧ distLR (epsRank ϑ S) S ≤ ϑ :=
  ⟨(epsRank_le_rank hϑ).trans (by simpa using S.rank_le_card_width), distLR_epsRank_le hϑ⟩

end RankGrowth

/-! ### Monotonicity under basis enrichment and in the rank (OP-OT-19) -/

section Monotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {P P' Q Q' : E →L[ℝ] E}

/-- If `P' P = P` then `1 - P' = (1 - P') (1 - P)`. -/
lemma one_sub_apply_one_sub_of_le (hle : ∀ x, P' (P x) = P x) (x : E) :
    (1 - P') ((1 - P) x) = (1 - P') x := by
  simp only [sub_apply, one_apply_eq_self, map_sub, hle]
  abel

/-- **Enrichment decreases the projection residual** (OP-OT-19): if the range of the
orthogonal projector `P'` contains the range of `P` (`P' P = P`), then
`‖(1 - P') x‖ ≤ ‖(1 - P) x‖`. -/
theorem norm_one_sub_le_of_le (hP' : IsOrthProj P') (hle : ∀ x, P' (P x) = P x) (x : E) :
    ‖(1 - P') x‖ ≤ ‖(1 - P) x‖ := by
  rw [← one_sub_apply_one_sub_of_le hle]
  exact hP'.compl.norm_le _

/-- **Enrichment decreases the doubly-normal component** (OP-OT-19): if `P' P = P`,
`Q' Q = Q` and `P` commutes with `Q'` (automatic for left and right matrix projectors), then
`‖(1 - P') (1 - Q') x‖ ≤ ‖(1 - P) (1 - Q) x‖`; i.e. the normal-component bound `ε` can only
decrease when the bases are enlarged. -/
theorem norm_normal_le_of_le (hP' : IsOrthProj P') (hQ' : IsOrthProj Q')
    (hPle : ∀ x, P' (P x) = P x) (hQle : ∀ x, Q' (Q x) = Q x) (hc : ∀ x, P (Q' x) = Q' (P x))
    (x : E) : ‖(1 - P') ((1 - Q') x)‖ ≤ ‖(1 - P) ((1 - Q) x)‖ := by
  have e3 : ∀ y, (1 - Q') ((1 - P) y) = (1 - P) ((1 - Q') y) := by
    intro y
    simp only [sub_apply, one_apply_eq_self, map_sub, hc]
    abel
  have hx : (1 - P') ((1 - Q') x) = (1 - P') ((1 - Q') ((1 - P) ((1 - Q) x))) := by
    rw [e3, one_sub_apply_one_sub_of_le hPle, one_sub_apply_one_sub_of_le hQle]
  rw [hx]
  exact (hP'.compl.norm_le _).trans (hQ'.compl.norm_le _)

/-- **Enrichment decreases the Galerkin capture residual** (OP-OT-19): if `P' Q'` is an
orthogonal projector (commuting `P'`, `Q'`) whose range contains that of `P Q`
(`P' P = P`, `Q' Q = Q`, `Q'` commutes with `P`), then `‖x - P' Q' x‖ ≤ ‖x - P Q x‖`. -/
theorem norm_sub_apply_apply_le_of_le (hP' : IsOrthProj P') (hQ' : IsOrthProj Q')
    (hc' : ∀ x, P' (Q' x) = Q' (P' x)) (hPle : ∀ x, P' (P x) = P x)
    (hQle : ∀ x, Q' (Q x) = Q x) (hc : ∀ x, Q' (P x) = P (Q' x)) (x : E) :
    ‖x - P' (Q' x)‖ ≤ ‖x - P (Q x)‖ :=
  (hP'.mul hQ' hc').norm_sub_le_of_mem_range x (P (Q x)) (by
    change P' (Q' (P (Q x))) = P (Q x)
    rw [hc, hQle, hPle])

variable {F : ℝ → E → E} {L B ε h t₀ t₁ : ℝ} {A : ℝ → E}

/-- **A Galerkin step in an enriched space inherits the error bound** (OP-OT-19).  If the
orthogonal projector `R'` fixes the range of `R` (`R' R = R`; `R` need not be a projector) and
`‖A(t₁) - R A(t₁)‖ ≤ θ`, then the Galerkin step `YS' = R' F(t, YS)`, `YS(t₀) = R' A(t₀)` satisfies
the bound of `galerkin_step_error` with the same `θ`:
`‖YS(t₁) - A(t₁)‖ ≤ (e^{L h} - 1) (B h + θ) + θ`. -/
theorem galerkin_step_error_of_le {R R' : E →L[ℝ] E} (hR' : IsOrthProj R')
    (hle : ∀ x, R' (R x) = R x) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    {YS : ℝ → E} (hS : ODESolution (fun t x => R' (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = R' (A t₀)) {θ : ℝ} (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + θ) + θ :=
  galerkin_step_error hR' hF hL hB ht₁ hh hA hS hS₀
    ((hR'.norm_sub_le_of_mem_range _ _ (hle _)).trans hθ)

/-- **Enriched BUG step** (OP-OT-19; covers the augmented BUG of arXiv 2104.05247 and any
further enrichment).  If `IsBUGStep` holds with new projectors `P₁`, `Q₁`, and `P₁'`, `Q₁'` are
commuting orthogonal projectors with larger ranges (`P₁' P₁ = P₁`, `Q₁' Q₁ = Q₁`), then the
Galerkin step `YS'` in the enriched space is again a BUG step with the **same** `ε`.  In
particular all robust bounds (`IsBUGStep.local_error`, `IsBUGStep.local_error_le`,
`bug_global_error`) hold verbatim for every enrichment of the bases. -/
theorem IsBUGStep.enrich {P₀ Q₀ P₁ Q₁ P₁' Q₁' : E →L[ℝ] E} {Y₀ : E} {YK YL YS YS' : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (hP₁' : IsOrthProj P₁')
    (hQ₁' : IsOrthProj Q₁') (hc' : ∀ x, P₁' (Q₁' x) = Q₁' (P₁' x))
    (hPle : ∀ x, P₁' (P₁ x) = P₁ x) (hQle : ∀ x, Q₁' (Q₁ x) = Q₁ x)
    (hS : ODESolution (fun t x => P₁' (Q₁' (F t x))) YS' t₀ t₁) (hS₀ : YS' t₀ = P₁' (Q₁' Y₀)) :
    IsBUGStep F ε P₀ Q₀ P₁' Q₁' t₀ t₁ Y₀ YK YL YS' where
  projP₀ := hs.projP₀
  projQ₀ := hs.projQ₀
  projP₁ := hP₁'
  projQ₁ := hQ₁'
  comm₁ := hc'
  kSol := hs.kSol
  kStart := hs.kStart
  kCap := by rw [← hs.kCap, hPle]
  kNormal t ht := (norm_one_sub_le_of_le hP₁' hPle _).trans (hs.kNormal t ht)
  lSol := hs.lSol
  lStart := hs.lStart
  lCap := by rw [← hs.lCap, hQle]
  lNormal t ht := (norm_one_sub_le_of_le hQ₁' hQle _).trans (hs.lNormal t ht)
  sSol := hS
  sStart := hS₀

/-- **The robust BUG bound is monotone in `ε`** (OP-OT-19): the local bound
`(e^{L h} - 1) (B h + 2ϑ) + 2ϑ`, `ϑ = h (4 L B h + ε)`, is nondecreasing in `ε`. -/
theorem bug_bound_mono {ε' : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hεε' : ε ≤ ε') :
    (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε))) + 2 * (h * (4 * L * B * h + ε))
      ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε')))
        + 2 * (h * (4 * L * B * h + ε')) := by
  have he : 0 ≤ Real.exp (L * h) - 1 := by
    have := Real.add_one_le_exp (L * h); nlinarith [mul_nonneg hL hh]
  have hd : 0 ≤ h * (ε' - ε) := mul_nonneg hh (by linarith)
  nlinarith [mul_nonneg he hd]

end Monotone

section MonotoneRank

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r r' : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε h t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **The robust capture bound is monotone in the rank** (OP-OT-19): for `r ≤ r'`,
`dist(A(t₁), M_{≤ r'}) ≤ 2 h (4 L B h + ε_r)` whenever `A(t₀)` has rank `≤ r`; so the rank-`r'`
capture is at least as good as the best of the rank-`r` bounds over all `r ≤ r'`. -/
theorem distLR_flow_le_of_le (hrr' : r ≤ r') (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (hε0 : 0 ≤ ε)
    (hε : NearNormalBound F r ε t₀ t₁ (A t₀) (B * h)) :
    distLR r' (A t₁) ≤ 2 * (h * (4 * L * B * h + ε)) :=
  (distLR_antitone hrr').trans (distLR_flow_le hF hL hB hc ht₁ hh hA hrank hε0 hε)

end MonotoneRank

/-! ### The `h²`-free robust bound `dist(A(t₁), M_{≤ r}) ≤ 2 h ε e^{L h}` (OP-RA-07, OP-EX-02) -/

section Sharp

/-- **Stability of exact flows** (Grönwall): two solutions of `y' = F(t, y)` on `[a, b]` with
`L`-Lipschitz `F` satisfy `‖y(b) - z(b)‖ ≤ e^{L (b - a)} ‖y(a) - z(a)‖`. -/
theorem norm_sub_le_exp_of_odeSolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) {y z : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hy : ODESolution F y a b) (hz : ODESolution F z a b) :
    ‖y b - z b‖ ≤ Real.exp (L * (b - a)) * ‖y a - z a‖ := by
  have h := norm_sub_le_gronwallBound hF hL (u := fun t => F t (y t)) (w := fun t => F t (z t))
    (ηy := 0) (ηz := 0) hy.cont hy.deriv (fun _ _ => by simp) hz.cont hz.deriv
    (fun _ _ => by simp) le_rfl b ⟨hab, le_rfl⟩
  rw [add_zero, gronwallBound_ε0] at h
  linarith [mul_comm (Real.exp (L * (b - a))) ‖y a - z a‖]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **One-step recursion for the distance to `M_{≤ r}` along the exact flow.**  On a step
`[a, a + τ]`, `dist(A(a + τ), M_{≤ r}) ≤ e^{L τ} dist(A(a), M_{≤ r}) + 2 τ (4 L B τ + ε)`: start the
exact flow from (almost) nearest points `Z` of rank `≤ r`, use `distLR_flow_le` for it and the
stability of the flow.  No closedness of `M_{≤ r}` or attainment of the distance is needed. -/
theorem distLR_flow_step (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {a b τ : ℝ} (hb : b = a + τ) (hτ : 0 ≤ τ)
    (hA : ODESolution F A a b) :
    distLR r (A b) ≤ Real.exp (L * τ) * distLR r (A a) + 2 * (τ * (4 * L * B * τ + ε)) := by
  set c := 2 * (τ * (4 * L * B * τ + ε)) with hcdef
  have hab : a ≤ b := by linarith
  have hexp : 0 < Real.exp (L * τ) := Real.exp_pos _
  have key : ∀ Z : Matrix m n ℝ, Z.rank ≤ r →
      distLR r (A b) ≤ Real.exp (L * τ) * ‖A a - Z‖ + c := by
    intro Z hZ
    obtain ⟨Φ, hΦ, hΦ₀⟩ := exists_ODESolution hF hB hc hab Z
    have h1 := distLR_flow_le_of_factored hF hL hB hc hb hτ hΦ (hΦ₀ ▸ hZ) hε0 hε
    have h2 := norm_sub_le_exp_of_odeSolution hF hL hab hA hΦ
    rw [hΦ₀, show b - a = τ by linarith] at h2
    have h3 := distLR_le_add (r := r) (A b) (Φ b)
    linarith
  have h4 : (distLR r (A b) - c) / Real.exp (L * τ) ≤ distLR r (A a) := by
    rw [le_distLR_iff]
    intro Z hZ
    rw [div_le_iff₀ hexp]
    linarith [key Z hZ, mul_comm (Real.exp (L * τ)) ‖A a - Z‖]
  rw [div_le_iff₀ hexp] at h4
  linarith [mul_comm (Real.exp (L * τ)) (distLR r (A a))]

/-- **Grid version**: on the grid `t₀ + j τ`, `j ≤ N`, starting in `M_{≤ r}`,
`dist(A(t₀ + j τ), M_{≤ r}) ≤ j · 2 τ (4 L B τ + ε) · e^{L j τ}` (discrete Grönwall). -/
theorem distLR_flow_le_grid (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ τ : ℝ} (hτ : 0 ≤ τ) {N : ℕ}
    (hA : ODESolution F A t₀ (t₀ + N * τ)) (hrank : (A t₀).rank ≤ r) :
    ∀ j ≤ N, distLR r (A (t₀ + j * τ)) ≤
      j * (2 * (τ * (4 * L * B * τ + ε))) * Real.exp (L * (j * τ)) := by
  have hB0 := hB.nonneg
  intro j
  induction j with
  | zero => intro _; simp [distLR_eq_zero_of_rank_le hrank]
  | succ j ih =>
    intro hj
    have hj' : j ≤ N := by omega
    have hjτ : 0 ≤ (j : ℝ) * τ := by positivity
    have hle : ((j + 1 : ℕ) : ℝ) * τ ≤ N * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hτ
    have hsub : ODESolution F A (t₀ + j * τ) (t₀ + ((j + 1 : ℕ) : ℝ) * τ) :=
      hA.mono (by linarith) (by linarith)
    have hstep := distLR_flow_step hF hL hB hc hε0 hε (by push_cast; ring) hτ hsub
    have hih := ih hj'
    set c := 2 * (τ * (4 * L * B * τ + ε)) with hcdef
    have hc0 : 0 ≤ c := by positivity
    have e1 : Real.exp (L * τ) * Real.exp (L * (j * τ)) =
        Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have e2 : 1 ≤ Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := Real.one_le_exp (by positivity)
    have hexp0 : 0 ≤ Real.exp (L * τ) := (Real.exp_pos _).le
    have h5 : Real.exp (L * τ) * distLR r (A (t₀ + j * τ)) ≤
        Real.exp (L * τ) * (j * c * Real.exp (L * (j * τ))) :=
      mul_le_mul_of_nonneg_left hih hexp0
    have h6 : Real.exp (L * τ) * (j * c * Real.exp (L * (j * τ))) =
        j * c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by
      rw [← e1]; ring
    have h7 : c ≤ c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := le_mul_of_one_le_right hc0 e2
    calc distLR r (A (t₀ + ((j + 1 : ℕ) : ℝ) * τ))
        ≤ Real.exp (L * τ) * distLR r (A (t₀ + j * τ)) + c := hstep
      _ ≤ j * c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ))
          + c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by linarith
      _ = ((j + 1 : ℕ) : ℝ) * c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by push_cast; ring

/-- **The `h²`-free robust distance bound** (OP-RA-07, robust replacement of the rank-`r` DLRA
solution; sharpens OP-EX-02).  Let `F` be `L`-Lipschitz (`L ≥ 0`), bounded by `B`, continuous in
time, with the factored normal-component bound `ε` at rank `r`.  For every exact solution `A` on
`[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, starting at a matrix of rank `≤ r`,

    dist(A(t₁), M_{≤ r}) ≤ 2 h ε e^{L h}.

The open-problem catalogue conjectures `ε (e^{L h} - 1) / L` (`≤ h ε e^{L h}`) via a
Dini-derivative argument; here the constant is `2 e^{L h}` instead, and the proof avoids Dini
derivatives: split the step into `N` substeps, apply `distLR_flow_step` on each (local
`O(τ (τ + ε))` capture from nearest points plus stability of the flow), and let `N → ∞`, which
removes the `O(h²)` term of `distLR_flow_le`.  No singular value enters. -/
theorem distLR_flow_le_exp (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) :
    distLR r (A t₁) ≤ 2 * h * ε * Real.exp (L * h) := by
  have hB0 := hB.nonneg
  have hN : ∀ N : ℕ, 0 < N → distLR r (A t₁) ≤
      2 * h * ε * Real.exp (L * h) + 8 * L * B * h ^ 2 * Real.exp (L * h) / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hτ : 0 ≤ h / N := by positivity
    have hNτ : (N : ℝ) * (h / N) = h := by field_simp
    have hA' : ODESolution F A t₀ (t₀ + N * (h / N)) := by rw [hNτ, ← ht₁]; exact hA
    have hg := distLR_flow_le_grid hF hL hB hc hε0 hε hτ hA' hrank N le_rfl
    rw [hNτ, ← ht₁] at hg
    have e : (N : ℝ) * (2 * (h / N * (4 * L * B * (h / N) + ε))) =
        2 * h * ε + 8 * L * B * h ^ 2 / N := by
      field_simp; ring
    rw [e] at hg
    calc distLR r (A t₁) ≤ (2 * h * ε + 8 * L * B * h ^ 2 / N) * Real.exp (L * h) := hg
      _ = _ := by ring
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨N, hN'⟩ := exists_nat_gt (8 * L * B * h ^ 2 * Real.exp (L * h) / η)
  have hq : 0 ≤ 8 * L * B * h ^ 2 * Real.exp (L * h) / η := by positivity
  have hNr : (0 : ℝ) < N := lt_of_le_of_lt hq hN'
  have hlt : 8 * L * B * h ^ 2 * Real.exp (L * h) / N ≤ η := by
    rw [div_le_iff₀ hNr]
    rw [div_lt_iff₀ hη] at hN'
    linarith [mul_comm η (N : ℝ)]
  linarith [hN N (by exact_mod_cast hNr)]

/-- **Robust rank-`r` truncation with the `h ε_r` term of the papers** (OP-RA-07;
arXiv 2402.08607, Remark 4; arXiv 2608.27749, Remark 2, robust form).  For every approximation
`Ŷ` of `A(t₁)` and every `κ`-quasi-best rank-`r` approximation `T` of `Ŷ`,

    ‖T - A(t₁)‖ ≤ 2 κ h ε_r e^{L h} + (1 + κ) ‖Ŷ - A(t₁)‖,

the bound `h ε_r + 2 ‖Ŷ - A(t₁)‖` of the papers (`κ = 1`) with the constant `2 e^{L h}` in front of
`h ε_r`, and **without** assuming that a rank-`r` DLRA solution exists over the step.  Combined
with a local error `‖Ŷ - A(t₁)‖ = O(h (h² + ε_r))` (midpoint BUG, arXiv 2402.08607 Thm. 1) this
gives the `O(h (h² + ε_r))` truncated bound of Remark 4. -/
theorem norm_trunc_flow_le_exp (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) {κ : ℝ} (hκ : 0 ≤ κ)
    {Yh T : Matrix m n ℝ} (hT : ‖T - Yh‖ ≤ κ * distLR r Yh) :
    ‖T - A t₁‖ ≤ κ * (2 * h * ε * Real.exp (L * h)) + (1 + κ) * ‖Yh - A t₁‖ := by
  have h1 := norm_trunc_sub_le (A₁ := A t₁) hκ hT
  have h2 := mul_le_mul_of_nonneg_left
    (distLR_flow_le_exp hF hL hB hc hε0 hε ht₁ hh hA hrank) hκ
  linarith

end Sharp

/-! ### Fixed-rank truncation of the augmented BUG integrator: robust global error -/

section FixedRank

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Best rank-`r` truncation along the exact flow** (OP-RA-07, non-vacuous form): for every
approximation `Ŷ` of `A(t₁)` there is a best rank-`r` approximation `T` of `Ŷ` (exists by
`exists_best_approx`), and it satisfies `‖T - A(t₁)‖ ≤ 2 h ε e^{L h} + 2 ‖Ŷ - A(t₁)‖`. -/
theorem exists_bestTrunc_flow_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (Yh : Matrix m n ℝ) :
    ∃ T : Matrix m n ℝ, T.rank ≤ r ∧ ‖T - Yh‖ = distLR r Yh ∧
      ‖T - A t₁‖ ≤ 2 * h * ε * Real.exp (L * h) + 2 * ‖Yh - A t₁‖ := by
  obtain ⟨T, hT, hTY⟩ := exists_best_approx r Yh
  refine ⟨T, hT, by rw [norm_sub_rev]; exact hTY, ?_⟩
  have := norm_trunc_flow_le_exp hF hL hB hc hε0 hε ht₁ hh hA hrank zero_le_one
    (T := T) (Yh := Yh) (by rw [norm_sub_rev, hTY, one_mul])
  linarith

/-- The truncation defect of one fixed-rank truncated augmented BUG step:
`κ (2 h ε e^{L h} + h (c₁ ε + c₂ h))`. -/
noncomputable def fixedRankDefect (κ L B ε h H : ℝ) : ℝ :=
  κ * (2 * h * ε * Real.exp (L * h) + h * (bugC₁ L H * ε + bugC₂ L B H * h))

/-- **Robust global error of the fixed-rank truncated augmented BUG integrator** (new; the
fixed-rank variant "augment, Galerkin, truncate back to rank `r`" of the rank-adaptive BUG
integrator of arXiv 2104.05247, cf. arXiv 2402.08607, Remark 4).  Let `F` be `L`-Lipschitz,
bounded by `B`, continuous in time, with the factored normal-component bound `ε` at rank `r`.
Each step `j < N` is a rank-adaptive step (`IsRankAdaptiveStep`, any tolerance `θ`) from
`Yⱼ = Uⱼ Sⱼ Vⱼᵀ` (rank `r`) whose result `Yⱼ₊₁` is a `κ`-quasi-best rank-`r` approximation of
the augmented result `Ŷⱼ₊₁ = Ûⱼ Ŝⱼ(tⱼ₊₁) V̂ⱼᵀ`.  Then for `j ≤ N`, `j h ≤ T`, `0 ≤ h ≤ H`,

    ‖Yⱼ - A(tⱼ)‖ ≤ e^{L T} δ + T e^{L T} c₁ ε + T e^{L T} c₂ h + e^{L T} j ϑ⋆,

with `ϑ⋆ = fixedRankDefect κ L B ε h H = κ (2 h ε e^{L h} + h (c₁ ε + c₂ h)) = O(h (h + ε))`, hence
`‖Yⱼ - A(tⱼ)‖ = O(δ + ε + h)` (`fixedRank_global_error_le'`): the rank stays `r`, there is no
tolerance term, and neither a rank-`r` DLRA solution nor a singular-value gap is assumed. -/
theorem fixedRank_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (hε₀ : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H)
    {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h)) {ka kb : ℕ → ℕ}
    {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {Ua : (j : ℕ) → Matrix m (Fin (ka j)) ℝ}
    {Va : (j : ℕ) → Matrix n (Fin (kb j)) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {Sa : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ} {θ κ : ℝ} (hκ : 0 ≤ κ)
    (hstep : ∀ j < N, MatrixBUG.IsRankAdaptiveStep F θ (t₀ + j * h) (t₀ + (j + 1) * h) (U j)
      (Sm j) (V j) (Ua j) (Va j) (K j) (Lf j) (Sa j) (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ))
    (htrunc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ
        - Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ‖
      ≤ κ * distLR r (Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * j * fixedRankDefect κ L B ε h H := by
  have hstep' : ∀ j < N, MatrixBUG.IsRankAdaptiveStep F (fixedRankDefect κ L B ε h H)
      (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (Ua j) (Va j) (K j) (Lf j) (Sa j)
      (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ) := by
    intro j hj
    have hs := hstep j hj
    have hs0 : MatrixBUG.IsRankAdaptiveStep F 0 (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j)
        (V j) (Ua j) (Va j) (K j) (Lf j) (Sa j) (Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ) :=
      { hs with trunc := by simp }
    have ht : t₀ + (j + 1) * h = t₀ + j * h + h := by ring
    have hloc := hs0.local_error_le hε hF hL hB ht hh hhH (hΦ j hj) (hΦ₀ j hj)
    rw [add_zero] at hloc
    have hrank : (Φ j (t₀ + j * h)).rank ≤ r := by
      rw [hΦ₀ j hj]; exact rank_mul_mul_transpose_le _ _ _
    have hdist := distLR_flow_le_exp hF hL hB hc hε₀ hε ht hh (hΦ j hj) hrank
    have h3 := distLR_le_add (r := r) (Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ)
      (Φ j (t₀ + (j + 1) * h))
    refine { hs with trunc := (htrunc j hj).trans ?_ }
    unfold fixedRankDefect
    exact mul_le_mul_of_nonneg_left (by linarith) hκ
  exact MatrixBUG.rankAdaptive_global_error_le (r := fun _ => r) hF hL hB hε₀ hh hhH hA
    (fun _ _ => hε) hstep' hΦ hΦ₀ hδ

/-- **Fixed-rank truncated augmented BUG, `O(δ + ε + h)` form**: under the hypotheses of
`fixedRank_global_error_le`, for `j ≤ N`, `j h ≤ T`,

    ‖Yⱼ - A(tⱼ)‖ ≤ e^{L T} δ + T e^{L T} ((1 + κ) c₁ + 2 κ e^{L H}) ε + T e^{L T} (1 + κ) c₂ h. -/
theorem fixedRank_global_error_le' (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (hε₀ : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H)
    {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h)) {ka kb : ℕ → ℕ}
    {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {Ua : (j : ℕ) → Matrix m (Fin (ka j)) ℝ}
    {Va : (j : ℕ) → Matrix n (Fin (kb j)) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {Sa : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ} {θ κ : ℝ} (hκ : 0 ≤ κ)
    (hstep : ∀ j < N, MatrixBUG.IsRankAdaptiveStep F θ (t₀ + j * h) (t₀ + (j + 1) * h) (U j)
      (Sm j) (V j) (Ua j) (Va j) (K j) (Lf j) (Sa j) (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ))
    (htrunc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ
        - Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ‖
      ≤ κ * distLR r (Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * ((1 + κ) * bugC₁ L H + 2 * κ * Real.exp (L * H)) * ε
        + T * Real.exp (L * T) * ((1 + κ) * bugC₂ L B H) * h := by
  intro j hj hjT
  have hmain := fixedRank_global_error_le hF hL hB hc hε₀ hε hh hhH hA hκ hstep htrunc hΦ hΦ₀ hδ
    j hj hjT
  have hB0 := hB.nonneg
  have hT0 : 0 ≤ T := le_trans (by positivity) hjT
  have hexpH : Real.exp (L * h) ≤ Real.exp (L * H) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have hc₁ := bugC₁_nonneg hL (hh.trans hhH)
  have hc₂ := bugC₂_nonneg hL hB0 (hh.trans hhH)
  have heT : 0 ≤ Real.exp (L * T) := (Real.exp_pos _).le
  -- `j ϑ⋆ ≤ T κ (2 ε e^{L H} + c₁ ε + c₂ h)`
  have hdef : (j : ℝ) * fixedRankDefect κ L B ε h H ≤
      T * (κ * (2 * ε * Real.exp (L * H) + bugC₁ L H * ε + bugC₂ L B H * h)) := by
    unfold fixedRankDefect
    have hX : 0 ≤ κ * (2 * ε * Real.exp (L * H) + bugC₁ L H * ε + bugC₂ L B H * h) := by
      positivity
    have h1 : 2 * h * ε * Real.exp (L * h) ≤ 2 * h * ε * Real.exp (L * H) :=
      mul_le_mul_of_nonneg_left hexpH (by positivity)
    calc (j : ℝ) * (κ * (2 * h * ε * Real.exp (L * h) + h * (bugC₁ L H * ε + bugC₂ L B H * h)))
        ≤ (j : ℝ) * (κ * (2 * h * ε * Real.exp (L * H) + h * (bugC₁ L H * ε
            + bugC₂ L B H * h))) := by gcongr
      _ = ((j : ℝ) * h) * (κ * (2 * ε * Real.exp (L * H) + bugC₁ L H * ε
            + bugC₂ L B H * h)) := by ring
      _ ≤ T * (κ * (2 * ε * Real.exp (L * H) + bugC₁ L H * ε + bugC₂ L B H * h)) :=
          mul_le_mul_of_nonneg_right hjT hX
  have h2 := mul_le_mul_of_nonneg_left hdef heT
  calc ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖
      ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * bugC₁ L H * ε
        + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * (j * fixedRankDefect κ L B ε h H) := by
        simpa [mul_assoc] using hmain
    _ ≤ _ := by nlinarith

end FixedRank

/-! ### Satisfiability and sharpness of the distance bounds -/

section Examples

open MatrixBUG

/-- **Two-sided bound in the counterexample setting** (non-vacuity and sharpness of
`distLR_flow_le_exp`).  For `F ≡ [[0, 1], [1, 0]]` (`L = 0`, `B = ε = ‖F‖`, the factored
normal-component bound of a constant field) and `Y₀ = diag(δ, 0)`, `0 ≤ δ ≤ h`, the exact
solution satisfies `h / 3 ≤ dist(A(h), M_{≤ 1}) ≤ 2 h ‖F‖`: the robust bound is attained up to a
constant factor, so the order `h ε` cannot be improved. -/
example {δ h : ℝ} (hδ : 0 ≤ δ) (hδh : δ ≤ h) :
    h / 3 ≤ distLR 1 (cxY₀ δ + (h - 0) • swapMat) ∧
    distLR 1 (cxY₀ δ + (h - 0) • swapMat) ≤ 2 * h * ‖swapMat‖ * Real.exp (0 * h) := by
  refine ⟨le_distLR_cx hδ hδh, ?_⟩
  have hA : ODESolution (fun _ _ => swapMat) (fun t => cxY₀ δ + (t - 0) • swapMat) 0 h :=
    odeSolution_affine (cxY₀ δ) swapMat 0 h
  have hFL : IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) 0 :=
    fun _ _ _ => by simp
  have hFB : IsBoundedField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) ‖swapMat‖ :=
    fun _ _ => le_rfl
  have hrank : (cxY₀ δ + (0 - 0 : ℝ) • swapMat).rank ≤ 1 := by
    rw [sub_self, zero_smul, add_zero]
    exact rank_mul_mul_transpose_le _ _ _
  have hε : FactoredNormalBound (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) 1
      ‖swapMat‖ := factoredNormalBound_const swapMat 1
  have key := distLR_flow_le_exp hFL le_rfl hFB (fun _ => continuous_const) (norm_nonneg _) hε
    (zero_add h).symm (hδ.trans hδh) hA hrank
  exact key

/-- `diag(2, 1) ↦ diag(2, 0)` (the truncation of `isRankAdaptiveStep_example`) is a best
rank-one approximation. -/
theorem exSa_bestTrunc :
    ‖unitCol * ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * unitColᵀ
        - (1 : Matrix (Fin 2) (Fin 2) ℝ) * exSa 1 * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖
      ≤ 1 * distLR 1
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * exSa 1 * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) := by
  have hd : (1 : Matrix (Fin 2) (Fin 2) ℝ) * exSa 1 * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
      Matrix.diagonal ![2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [exSa, Matrix.mul_apply, Matrix.one_apply]
  have h1 : (1 : ℝ) ≤ distLR 1 (Matrix.diagonal ![(2 : ℝ), 1]) :=
    le_distLR_diagonal zero_le_one (fun i => by fin_cases i <;> norm_num) (by simp)
  have h2 := isRankAdaptiveStep_example.trunc
  rw [hd, one_mul]
  rw [hd] at h2
  -- after rewriting
  linarith [show ‖unitCol * ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * unitColᵀ
      - Matrix.diagonal ![(2 : ℝ), 1]‖ ≤ 1 from by
        simpa [exSa] using h2]

/-- The ranks/coefficients of the one-step fixed-rank example: `S₀ = 1`, `S₁ = 2`. -/
noncomputable def exSm (j : ℕ) : Matrix (Fin 1) (Fin 1) ℝ :=
  if j = 0 then 1 else (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)

/-- **Satisfiability of `fixedRank_global_error_le`** with a genuine truncation: one step
(`N = 1`, `h = T = 1`) of `isRankAdaptiveStep_example` (`F ≡ I`, `Y₀ = e₁ e₁ᵀ`, augmented result
`diag(2, 1)`, truncated to the best rank-one approximation `diag(2, 0)`, `κ = 1`). -/
example : ‖unitCol * exSm 1 * unitColᵀ - exA (0 + ((1 : ℕ) : ℝ) * 1)‖ ≤
    Real.exp (0 * 1) * 0
      + 1 * Real.exp (0 * 1) * bugC₁ 0 1 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      + 1 * Real.exp (0 * 1) * bugC₂ 0 ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 * 1
      + Real.exp (0 * 1) * ((1 : ℕ) : ℝ) * fixedRankDefect 1 0 ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
        ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 1 := by
  have e0 : (0 : ℝ) + ((0 : ℕ) : ℝ) * 1 = 0 := by norm_num
  have e1 : (0 : ℝ) + (((0 : ℕ) : ℝ) + 1) * 1 = 1 := by norm_num
  have hA : ODESolution (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) exA 0 1 :=
    odeSolution_of_const (fun _ _ => rfl) _ 0 1
  have hA' : ODESolution (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) exA 0
      (0 + ((1 : ℕ) : ℝ) * 1) := by
    rw [show (0 : ℝ) + ((1 : ℕ) : ℝ) * 1 = 1 by norm_num]; exact hA
  refine fixedRank_global_error_le (F := fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) (L := 0)
    (A := exA) (t₀ := 0) (h := 1) (H := 1) (N := 1) (δ := 0) (T := 1) (r := 1)
    (ka := fun _ => 2) (kb := fun _ => 2) (U := fun _ => unitCol) (Sm := exSm)
    (V := fun _ => unitCol) (Ua := fun _ => 1) (Va := fun _ => 1) (K := fun _ => exK)
    (Lf := fun _ => exK) (Sa := fun _ => exSa) (Φ := fun _ => exA) (θ := 1) (κ := 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (fun _ => continuous_const)
    (norm_nonneg _) (factoredNormalBound_const _ 1) zero_le_one le_rfl
    hA' zero_le_one ?_ ?_ ?_ ?_ (by simp [exA, exSm]) 1 le_rfl (by norm_num)
  · intro j hj
    obtain rfl : j = 0 := by omega
    rw [e0, e1]
    exact isRankAdaptiveStep_example
  · intro j hj
    obtain rfl : j = 0 := by omega
    rw [e1]
    exact exSa_bestTrunc
  · intro j hj
    obtain rfl : j = 0 := by omega
    rw [e0, e1]
    exact hA
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp [exA, exSm]

end Examples

end LeanDLRA
