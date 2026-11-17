import LeanDLRA.Matrix.LowRankDistance

/-!
# Best rank-`≤ r` approximation without the singular value decomposition

Let `M_{≤ r} = {Y ∈ ℝ^{m × n} : rank Y ≤ r}`.  This file proves, without constructing a
singular value decomposition and without Eckart–Young, the following classical facts.

1. **Closedness and existence.**  The rank is lower semicontinuous on matrices over any complete
   nontrivially normed field, so `{A : rank A ≤ r}` is closed (`Matrix.isClosed_setOf_rank_le`,
   `Matrix.isOpen_setOf_lt_rank`, `Matrix.lowerSemicontinuous_rank`).  For real matrices and
   the Frobenius norm (`open scoped LeanDLRA.Frobenius`) the closedness of `M_{≤ r}`
   (`LeanDLRA.isClosed_lowRankSet`, proved there via compactness of the Stiefel set) and the
   existence of a best approximation `X⋆ ∈ M_{≤ r}` with `‖X - X⋆‖ = dist(X, M_{≤ r})`
   (`LeanDLRA.exists_best_approx`) are in `LeanDLRA.Matrix.LowRankDistance`, together with
   `LeanDLRA.distLR_pos_iff` (`dist(X, M_{≤ r}) > 0 ↔ rank X > r`).
2. **Gap-free quasi-optimality** (OP-RA-21, easy part).  Every best approximation `T` of `X`
   satisfies `‖T - Y‖ ≤ dist(Y, M_{≤ r}) + 2 ‖X - Y‖` for all `Y`, and `‖T - Y‖ ≤ 2 ‖X - Y‖`
   when `rank Y ≤ r` (`norm_sub_le_infDist_add_two_mul`, `norm_sub_le_two_mul_of_rank_le`).
   No gap `σ_r > σ_{r+1}` is needed.
3. **`ε`-rank sandwich** (OP-RA-03).  With `rank_ε X = min {k : dist(X, M_{≤ k}) ≤ ε}` written
   with `Nat.find`, `‖X - X'‖ ≤ e` implies `rank_{ε+e}(X') ≤ rank_ε(X)` (`find_add_le_find`;
   `epsRank_eq_find` identifies `Nat.find` with `LeanDLRA.epsRank`).  The `ε`-rank is the rank of
   a matrix within distance `ε` (`exists_rank_eq_epsRank`).
4. **Normal-component sandwich.**  For `U ∈ ℝ^{m × r}`, `V ∈ ℝ^{n × r}`,
   `dist(X, M_{≤ 2r}) ≤ ‖(1 - U Uᵀ) X (1 - V Vᵀ)‖` (`infDist_two_mul_le_norm_normal`; no
   orthonormality needed), and if `r ≤ card m`, `r ≤ card n` there are orthonormal frames `U`,
   `V`, capturing a best approximation `X⋆ = U (Uᵀ X⋆ V) Vᵀ`, with
   `‖(1 - U Uᵀ) X (1 - V Vᵀ)‖ ≤ dist(X, M_{≤ r})` (`exists_bestApprox_frames`).

## Proof strategy

* Closedness: `isOpen_setOfPred_nat_le_rank` (the set of continuous linear maps of rank `≥ k` is
  open) pulled back along the continuous linear map `A ↦ toLin' A`; the cardinal rank of
  `mulVecLin A` is `rank A` (`Matrix.rank_mulVecLin`).  The scoped Frobenius topology is
  definitionally the product topology (`LeanDLRA.Frobenius.frobeniusTopologicalSpace_eq`).
* Existence (in `LeanDLRA.Matrix.LowRankDistance`): `IsClosed.exists_infDist_eq_dist` in the
  proper space `ℝ^{m × n}`.
* Quasi-optimality and the `ε`-rank sandwich: triangle inequality and the `1`-Lipschitz property
  of `dist(·, M_{≤ r})` (`LeanDLRA.norm_bestTrunc_sub_le`, `LeanDLRA.epsRank_add_le`).
* Normal component, lower bound: `X - (1 - U Uᵀ) X (1 - V Vᵀ) = U (Uᵀ X) + (X V - U Uᵀ X V) Vᵀ`
  has rank `≤ 2r`.  Upper bound: if `U Uᵀ X⋆ = X⋆` then
  `(1 - U Uᵀ) X (1 - V Vᵀ) = (1 - U Uᵀ) (X - X⋆) (1 - V Vᵀ)` and the normal projector is a
  contraction (`LeanDLRA.MatrixBUG.norm_normal_le`); the frames come from
  `LeanDLRA.exists_orthonormal_capture`.

## Connection to dynamical low-rank approximation

* `exists_bestTrunc`: a best rank-`r` truncation `T` of an augmented BUG result `Ŷ` exists, and
  `‖T - A₁‖ ≤ dist(A₁, M_{≤ r}) + 2 ‖Ŷ - A₁‖` (the truncation inequality of
  [HauckKuschSchotthofer2026], Remark 2, used for the fixed-rank truncated augmented BUG integrator;
  the hypothesis `κ = 1` of `LeanDLRA.norm_trunc_sub_le` is satisfiable without an SVD).
* `exists_rankAdaptive_trunc`: for a tolerance `ϑ ≥ 0` there is a truncation `Y₁` with
  `‖Y₁ - Ŷ‖ ≤ ϑ` (the hypothesis `IsRankAdaptiveBUGStep.trunc` of the rank-adaptive BUG
  integrator, Ceruti–Kusch–Lubich, [CerutiKuschLubich2022]) whose rank `rank_ϑ Ŷ` is minimal among
  all matrices meeting the tolerance.
* `infDist_two_mul_le_norm_normal_apply`, `exists_norm_normal_apply_le_infDist`,
  `norm_normal_le_norm_sub_factored`: the modelling error `ε` of the robust DLRA error bounds,
  i.e. a bound for the normal component `‖(1 - U Uᵀ) F(Y) (1 - V Vᵀ)‖` at `Y = U S Vᵀ`, can never
  be smaller than the best rank-`2r` approximation error of `F(Y)`, and with optimal frames it is
  at most the best rank-`r` error.  By Eckart–Young (`LeanDLRA.EckartYoung.infDist_setOf_rank_le`)
  these are the singular-value tails `(∑_{i ≥ 2r} σ_i²)^{1/2}` and `(∑_{i ≥ r} σ_i²)^{1/2}` of
  `F(Y)`.  This makes the heuristic "`ε` is small when `F` is nearly of low rank" (OP-RA-08)
  precise in both directions.  It does *not* show that `ε` is small along an actual DLRA
  trajectory: the frames there are those of the numerical solution, not the optimal ones.

## References

* C. Eckart, G. Young, *The approximation of one matrix by another of lower rank*,
  Psychometrika 1 (1936), 211–218.
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., §2.4 and §5.4.
* O. Koch, C. Lubich, *Dynamical low-rank approximation*, SIAM J. Matrix Anal. Appl. 29 (2007),
  434–454.
* G. Ceruti, J. Kusch, C. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, BIT 62 (2022), [CerutiKuschLubich2022].
* G. Ceruti, J. Kusch, C. Lubich, *A parallel rank-adaptive integrator for dynamical low-rank
  approximation*, [CerutiKuschLubich2024].

## Implementation notes

The topological results are stated over any complete nontrivially normed field `𝕜` with the
product topology on `Matrix m n 𝕜`.  All metric results are for real matrices and the scoped
Frobenius norm of `LeanDLRA.Frobenius`; there `Metric.infDist X {Y | Y.rank ≤ r}` is
definitionally `LeanDLRA.distLR r X`, and `LeanDLRA.epsRank` is the `ε`-rank of
`LeanDLRA.Matrix.LowRankDistance` (shown to agree with the `Nat.find` definition in
`epsRank_eq_find`).
-/

open Set Metric Module

/-! ### Lower semicontinuity of the rank -/

namespace Matrix

variable {m n 𝕜 : Type*} [Finite m] [Fintype n] [NontriviallyNormedField 𝕜]

omit [Finite m] in
/-- The (cardinal) rank of the linear map `x ↦ A x` is the rank of the matrix `A`. -/
theorem rank_mulVecLin (A : Matrix m n 𝕜) : (A.mulVecLin).rank = A.rank := by
  rw [LinearMap.rank, Matrix.rank, finrank_eq_rank]

variable [CompleteSpace 𝕜]

/-- The set of matrices of rank `> r` is open. -/
theorem isOpen_setOf_lt_rank (r : ℕ) : IsOpen {A : Matrix m n 𝕜 | r < A.rank} := by
  classical
  have := Fintype.ofFinite m
  let Φ : Matrix m n 𝕜 →ₗ[𝕜] (n → 𝕜) →L[𝕜] (m → 𝕜) :=
    (LinearMap.toContinuousLinearMap : ((n → 𝕜) →ₗ[𝕜] (m → 𝕜)) ≃ₗ[𝕜] _).toLinearMap ∘ₗ
      (Matrix.toLin' : Matrix m n 𝕜 ≃ₗ[𝕜] _).toLinearMap
  have h := (isOpen_setOfPred_nat_le_rank (𝕜 := 𝕜) (E := n → 𝕜) (F := m → 𝕜) (r + 1)).preimage
    Φ.continuous_of_finiteDimensional
  convert h using 1
  ext A
  change r < A.rank ↔ ((r + 1 : ℕ) : Cardinal) ≤ (A.mulVecLin).rank
  rw [rank_mulVecLin, Nat.cast_le]
  omega

/-- **The set of matrices of rank at most `r` is closed.** -/
theorem isClosed_setOf_rank_le (r : ℕ) : IsClosed {A : Matrix m n 𝕜 | A.rank ≤ r} := by
  simpa only [compl_ofPred, not_lt] using
    (isOpen_setOf_lt_rank (m := m) (n := n) (𝕜 := 𝕜) r).isClosed_compl

/-- **The rank is lower semicontinuous**: a small perturbation never decreases the rank. -/
theorem lowerSemicontinuous_rank : LowerSemicontinuous (Matrix.rank : Matrix m n 𝕜 → ℕ) :=
  fun _ r hr => (isOpen_setOf_lt_rank r).mem_nhds hr

end Matrix

namespace LeanDLRA

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] {r k : ℕ} {ε : ℝ} {X Y T : Matrix m n ℝ}

/-! ### Gap-free quasi-optimality of best approximations -/

section QuasiOptimality

/-- **Gap-free quasi-optimality** (OP-RA-21).  If `T` is a best rank-`≤ r` approximation of `X`
(it suffices that `‖X - T‖ ≤ dist(X, M_{≤ r})`), then for every `Y`
`‖T - Y‖ ≤ dist(Y, M_{≤ r}) + 2 ‖X - Y‖`. -/
theorem norm_sub_le_infDist_add_two_mul
    (hT : ‖X - T‖ ≤ infDist X {Z : Matrix m n ℝ | Z.rank ≤ r}) (Y : Matrix m n ℝ) :
    ‖T - Y‖ ≤ infDist Y {Z : Matrix m n ℝ | Z.rank ≤ r} + 2 * ‖X - Y‖ :=
  norm_bestTrunc_sub_le (r := r) (by rw [norm_sub_rev]; exact hT)

/-- **Quasi-optimality on `M_{≤ r}`**: a best rank-`≤ r` approximation `T` of `X` satisfies
`‖T - Y‖ ≤ 2 ‖X - Y‖` for every `Y` of rank at most `r`. -/
theorem norm_sub_le_two_mul_of_rank_le
    (hT : ‖X - T‖ ≤ infDist X {Z : Matrix m n ℝ | Z.rank ≤ r}) (hY : Y.rank ≤ r) :
    ‖T - Y‖ ≤ 2 * ‖X - Y‖ := by
  have h := norm_sub_le_infDist_add_two_mul hT Y
  rwa [infDist_zero_of_mem (s := {Z : Matrix m n ℝ | Z.rank ≤ r}) hY, zero_add] at h

end QuasiOptimality

/-! ### The `ε`-rank -/

section EpsRank

/-- The `ε`-rank agrees with the `Nat.find` definition
`rank_ε X = min {k : dist(X, M_{≤ k}) ≤ ε}` (for `ε ≥ 0` the defining set is nonempty). -/
theorem epsRank_eq_find (hε : 0 ≤ ε) [DecidablePred fun k => distLR k X ≤ ε] :
    epsRank ε X = Nat.find (epsRank_set_nonempty (X := X) hε) :=
  le_antisymm (epsRank_le_of_distLR_le (Nat.find_spec (epsRank_set_nonempty hε)))
    (Nat.find_min' _ (distLR_epsRank_le hε))

/-- **The `ε`-rank is attained**: for `ε ≥ 0` there is a matrix `Y` with `‖X - Y‖ ≤ ε` and
`rank Y = rank_ε X`. -/
theorem exists_rank_eq_epsRank (hε : 0 ≤ ε) (X : Matrix m n ℝ) :
    ∃ Y : Matrix m n ℝ, ‖X - Y‖ ≤ ε ∧ Y.rank = epsRank ε X := by
  obtain ⟨Y, hY, hle⟩ := exists_epsRank_approx (X := X) hε
  exact ⟨Y, hle, le_antisymm hY (epsRank_le_of_norm_sub_le le_rfl hle)⟩

/-- **`ε`-rank sandwich** (OP-RA-03), stated with `Nat.find`: if `‖X - X'‖ ≤ e` and `ε ≥ 0`, then
`rank_{ε+e}(X') ≤ rank_ε(X)`, where `rank_δ Z = min {k : dist(Z, M_{≤ k}) ≤ δ}`. -/
theorem find_add_le_find {X' : Matrix m n ℝ} {e : ℝ} (hε : 0 ≤ ε) (hXX' : ‖X - X'‖ ≤ e)
    [DecidablePred fun k => distLR k X ≤ ε] [DecidablePred fun k => distLR k X' ≤ ε + e] :
    Nat.find (epsRank_set_nonempty (X := X') (hε.trans (le_add_of_nonneg_right
        ((norm_nonneg _).trans hXX')))) ≤
      Nat.find (epsRank_set_nonempty (X := X) hε) := by
  rw [← epsRank_eq_find hε, ← epsRank_eq_find (hε.trans (le_add_of_nonneg_right
    ((norm_nonneg _).trans hXX')))]
  exact epsRank_add_le hε hXX'

end EpsRank

/-! ### The normal-component sandwich -/

section Normal

variable [DecidableEq m] [DecidableEq n]

/-- `X` minus its normal component `(1 - U Uᵀ) X (1 - V Vᵀ)` has rank at most `card k + card l`,
so the normal component bounds `dist(X, M_{≤ card k + card l})` (no orthonormality needed). -/
theorem infDist_le_norm_normal {k l : Type*} [Fintype k] [Fintype l] (X : Matrix m n ℝ)
    (U : Matrix m k ℝ) (V : Matrix n l ℝ) :
    infDist X {Z : Matrix m n ℝ | Z.rank ≤ Fintype.card k + Fintype.card l} ≤
      ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ := by
  have hZ : (U * (Uᵀ * X) + (X * V - U * (Uᵀ * X * V)) * Vᵀ).rank ≤
      Fintype.card k + Fintype.card l := by
    rw [← Matrix.fromCols_mul_fromRows]
    calc _ ≤ (Matrix.fromCols U (X * V - U * (Uᵀ * X * V))).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (k ⊕ l) := Matrix.rank_le_card_width _
      _ = _ := Fintype.card_sum
  have h : (1 - U * Uᵀ) * X * (1 - V * Vᵀ) =
      X - (U * (Uᵀ * X) + (X * V - U * (Uᵀ * X * V)) * Vᵀ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [h, ← dist_eq_norm]
  exact infDist_le_dist_of_mem hZ

/-- **Normal-component sandwich, lower half**: for all `U ∈ ℝ^{m × r}`, `V ∈ ℝ^{n × r}`,
`dist(X, M_{≤ 2r}) ≤ ‖(1 - U Uᵀ) X (1 - V Vᵀ)‖`. -/
theorem infDist_two_mul_le_norm_normal (X : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ)
    (V : Matrix n (Fin r) ℝ) :
    infDist X {Z : Matrix m n ℝ | Z.rank ≤ 2 * r} ≤ ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ := by
  simpa [two_mul] using infDist_le_norm_normal X U V

/-- If `U` has orthonormal columns capturing `Y` (`U Uᵀ Y = Y`) and `V` has orthonormal columns,
then the normal component of `X` is at most `‖X - Y‖`. -/
theorem norm_normal_le_norm_sub {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k]
    [DecidableEq l] {U : Matrix m k ℝ} {V : Matrix n l ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hY : U * Uᵀ * Y = Y) (X : Matrix m n ℝ) :
    ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ ≤ ‖X - Y‖ := by
  have h0 : (1 - U * Uᵀ) * Y = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hY, sub_self]
  calc ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ = ‖(1 - U * Uᵀ) * (X - Y) * (1 - V * Vᵀ)‖ := by
        rw [Matrix.mul_sub (1 - U * Uᵀ) X Y, h0, sub_zero]
    _ ≤ ‖X - Y‖ := MatrixBUG.norm_normal_le hU hV _

/-- **Normal-component sandwich, upper half**: if `r ≤ card m` and `r ≤ card n`, there are a
best rank-`≤ r` approximation `X⋆` of `X` and frames `U`, `V` with `r` orthonormal columns and
`X⋆ = U (Uᵀ X⋆ V) Vᵀ` such that `‖(1 - U Uᵀ) X (1 - V Vᵀ)‖ ≤ dist(X, M_{≤ r})`. -/
theorem exists_bestApprox_frames (X : Matrix m n ℝ) (hm : r ≤ Fintype.card m)
    (hn : r ≤ Fintype.card n) :
    ∃ Xs : Matrix m n ℝ, ∃ U : Matrix m (Fin r) ℝ, ∃ V : Matrix n (Fin r) ℝ,
      Xs.rank ≤ r ∧ ‖X - Xs‖ = infDist X {Z : Matrix m n ℝ | Z.rank ≤ r} ∧
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ U * (Uᵀ * Xs * V) * Vᵀ = Xs ∧
      ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ ≤ infDist X {Z : Matrix m n ℝ | Z.rank ≤ r} := by
  obtain ⟨Xs, hXs, hXXs⟩ := exists_best_approx r X
  obtain ⟨U, hU, hUc⟩ := exists_orthonormal_capture Xs hXs hm
  obtain ⟨V, hV, hVc⟩ :=
    exists_orthonormal_capture Xsᵀ (by rwa [Matrix.rank_transpose]) hn
  have hVc' : Xs * (V * Vᵀ) = Xs := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hVc
  refine ⟨Xs, U, V, hXs, hXXs, hU, hV, ?_, (norm_normal_le_norm_sub hU hV hUc X).trans hXXs.le⟩
  calc U * (Uᵀ * Xs * V) * Vᵀ = U * Uᵀ * Xs * (V * Vᵀ) := by simp only [Matrix.mul_assoc]
    _ = Xs := by rw [hUc, hVc']

/-- **Normal-component sandwich**, existence form: some frames `U`, `V` with `r` orthonormal
columns satisfy `‖(1 - U Uᵀ) X (1 - V Vᵀ)‖ ≤ dist(X, M_{≤ r})`. -/
theorem exists_norm_normal_le_infDist (X : Matrix m n ℝ) (hm : r ≤ Fintype.card m)
    (hn : r ≤ Fintype.card n) :
    ∃ U : Matrix m (Fin r) ℝ, ∃ V : Matrix n (Fin r) ℝ, Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧
      ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ ≤ infDist X {Z : Matrix m n ℝ | Z.rank ≤ r} := by
  obtain ⟨-, U, V, -, -, hU, hV, -, h⟩ := exists_bestApprox_frames X hm hn
  exact ⟨U, V, hU, hV, h⟩

end Normal

/-! ### Connection to dynamical low-rank approximation -/

section DLRA

/-- **Best truncation of an augmented step** ([HauckKuschSchotthofer2026, Remark 2]; OP-RA-07): for
every `Ŷ` there is a best rank-`≤ r` approximation `T` (no SVD needed), and every such `T` satisfies
`‖T - A₁‖ ≤ dist(A₁, M_{≤ r}) + 2 ‖Ŷ - A₁‖` for the exact value `A₁`. So the quasi-best hypothesis
(`κ = 1`) of `LeanDLRA.norm_trunc_sub_le` is always satisfiable. -/
theorem exists_bestTrunc (Yh : Matrix m n ℝ) (r : ℕ) :
    ∃ T : Matrix m n ℝ, T.rank ≤ r ∧ ‖T - Yh‖ = distLR r Yh ∧
      ∀ A₁ : Matrix m n ℝ, ‖T - A₁‖ ≤ distLR r A₁ + 2 * ‖Yh - A₁‖ := by
  obtain ⟨T, hT, hYT⟩ := exists_best_approx r Yh
  have hTY : ‖T - Yh‖ = distLR r Yh := by rw [norm_sub_rev]; exact hYT
  exact ⟨T, hT, hTY, fun _ => norm_bestTrunc_sub_le hTY.le⟩

/-- **Rank-adaptive truncation with minimal rank** (Ceruti–Kusch–Lubich, [CerutiKuschLubich2022],
step 3 of the rank-adaptive BUG integrator): for a tolerance `ϑ ≥ 0` there is `Y₁` with
`‖Y₁ - Ŷ‖ ≤ ϑ` (the hypothesis `IsRankAdaptiveBUGStep.trunc`) and `rank Y₁ = rank_ϑ Ŷ`, which is the
smallest rank of any matrix meeting the tolerance. -/
theorem exists_rankAdaptive_trunc {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (Yh : Matrix m n ℝ) :
    ∃ Y₁ : Matrix m n ℝ, ‖Y₁ - Yh‖ ≤ ϑ ∧ Y₁.rank = epsRank ϑ Yh ∧
      ∀ Z : Matrix m n ℝ, ‖Z - Yh‖ ≤ ϑ → Y₁.rank ≤ Z.rank := by
  obtain ⟨Y₁, hY₁, hrank⟩ := exists_rank_eq_epsRank hϑ Yh
  refine ⟨Y₁, by rwa [norm_sub_rev], hrank, fun Z hZ => ?_⟩
  rw [hrank]
  exact epsRank_le_of_norm_sub_le le_rfl (by rwa [norm_sub_rev])

/-- **Lower bound for the modelling error `ε`.**  In the projector form used by the integrators,
the normal component `(1 - P) (1 - Q) Z` with `P = leftProj U`, `Q = rightProj V`
(`U`, `V` with `r` columns) satisfies `dist(Z, M_{≤ 2r}) ≤ ‖(1 - P)(1 - Q) Z‖`.  Hence any `ε`
with `‖(1 - P) (1 - Q) F(Y)‖ ≤ ε` is at least the best rank-`2r` error of `F(Y)`. -/
theorem infDist_two_mul_le_norm_normal_apply (Z : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ)
    (V : Matrix n (Fin r) ℝ) :
    distLR (2 * r) Z ≤ ‖(1 - leftProj U) ((1 - rightProj V) Z)‖ := by
  classical
  rw [one_sub_leftProj_one_sub_rightProj_apply]
  exact infDist_two_mul_le_norm_normal Z U V

/-- **Upper bound for the modelling error `ε` with optimal frames**: if `r ≤ card m` and
`r ≤ card n`, some orthonormal frames give `‖(1 - P) (1 - Q) Z‖ ≤ dist(Z, M_{≤ r})`.  Together
with `infDist_two_mul_le_norm_normal_apply`:
`dist(Z, M_{≤ 2r}) ≤ min_{U,V} ‖(1 - P)(1 - Q) Z‖ ≤ dist(Z, M_{≤ r})`. -/
theorem exists_norm_normal_apply_le_infDist (Z : Matrix m n ℝ) (hm : r ≤ Fintype.card m)
    (hn : r ≤ Fintype.card n) :
    ∃ U : Matrix m (Fin r) ℝ, ∃ V : Matrix n (Fin r) ℝ, Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧
      ‖(1 - leftProj U) ((1 - rightProj V) Z)‖ ≤ distLR r Z := by
  classical
  obtain ⟨U, V, hU, hV, h⟩ := exists_norm_normal_le_infDist Z hm hn
  exact ⟨U, V, hU, hV, by rw [one_sub_leftProj_one_sub_rightProj_apply]; exact h⟩

variable [DecidableEq m] [DecidableEq n]

/-- **The normal component at a factored point.**  At `Y = U S Vᵀ` with orthonormal `U`, `V`, the
normal component of any `Z` (e.g. `Z = F(Y)`) is at most the distance from `Z` to any matrix
`U S' Vᵀ` with the same frames. -/
theorem norm_normal_le_norm_sub_factored {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k]
    [DecidableEq l] {U : Matrix m k ℝ} {V : Matrix n l ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix k l ℝ) (Z : Matrix m n ℝ) :
    ‖(1 - U * Uᵀ) * Z * (1 - V * Vᵀ)‖ ≤ ‖Z - U * S * Vᵀ‖ := by
  refine norm_normal_le_norm_sub hU hV ?_ Z
  rw [show U * Uᵀ * (U * S * Vᵀ) = U * (Uᵀ * U) * S * Vᵀ by simp only [Matrix.mul_assoc], hU,
    Matrix.mul_one]

end DLRA

end LeanDLRA
