import LeanDLRA.Tensor.TT.NormalSecondOrder
import LeanDLRA.Tensor.TT.Operations

/-!
# The normal component of a nearby tensor train, with a constant independent of the order

Let `Y` be a tensor train with `d` modes, left-orthogonal cores `A` and right-orthogonal cores
`B` (`tt B = tt A = Y`), with the tangent projector `P(Y) = ttTangentProj A B`, and let `X` be a
tensor train with the same bond dimensions `|β k|` and `e = ‖X - Y‖`. Let `ρ` be a lower bound of
the singular values `σ_{|β k|}` of the unfoldings `Y⟨k⟩`, `0 < k < d`, or of the unfoldings
`X⟨k⟩`. This file shows, for `e < ρ`,

  `ρ (ρ - 2 e) ‖X - P(Y) X‖² ≤ e⁴ / 2`,   i.e.   `‖X - P(Y) X‖ ≤ e² / √(2 ρ (ρ - 2 e))`,

so the normal component of `X` at `Y` is of second order in `e` with a constant that does not
depend on the number of modes. The bounds of [BachmayrEisenmannUschmajew2025, Prop. 4.11] and of
Budzinskiy–Zamarashkin (arXiv 2110.03975, Lemma 3.1) have the factors `√(d - 1)` and `d - 1`
(for all `e`).

## Main results

* `LeanDLRA.Tensor.unfold_actOn_compl`: acting on the modes outside `p` multiplies the
  `p`-unfolding from the right.
* `LeanDLRA.Tensor.exists_unfold_actOn_eq_mul_of_imp`,
  `LeanDLRA.Tensor.rank_unfold_actOn_le_of_imp`: acting on a subset of the modes in `p`
  multiplies the `p`-unfolding from the left, and does not raise its rank.
* `LeanDLRA.Tensor.mul_norm_sub_actOn_sub_actOn_compl_le`: for a tensor `T` whose `p`-unfolding
  has rank at most `q` and `q`-th singular value at least `ρ`,
  `ρ ‖(1 - S) (1 - N) T‖ ≤ ‖(1 - S) T‖ ‖(1 - N) T‖` for `S` acting on the modes in `p` and `N`
  on the other modes.
* `LeanDLRA.Tensor.sub_mul_norm_sq_sub_ttTangentProj_apply_le`: the bound for a tensor `Z` in
  terms of the unfoldings of the tensors `P_{≤k} Z`.
* `LeanDLRA.Tensor.mul_norm_sq_sub_ttTangentProj_tt_le`,
  `LeanDLRA.Tensor.norm_sub_ttTangentProj_tt_le`: the bound above with `ρ` at `Y`.
* `LeanDLRA.Tensor.mul_norm_sq_sub_ttTangentProj_tt_le_of_le_singularValues_tt`,
  `LeanDLRA.Tensor.norm_sub_ttTangentProj_tt_le_of_le_singularValues_tt`: the same with `ρ` at
  `X`.

## Implementation notes

The hypothesis of `sub_mul_norm_sq_sub_ttTangentSum_apply_le` at the interface `k + 1` is
`mul_norm_sub_actOn_sub_actOn_compl_le` for the tensor `T = P_{≤k} X` and the set of the first
`k + 1` modes: `P_{≤k+1}` acts on these modes and `P_{>k+1}` on the others. The unfolding of `T`
is the unfolding of `X` multiplied from the left, so its rank is at most `|β (k + 1)|`, and by
Weyl's inequality its singular value is at least `ρ - ‖T - Y‖ ≥ ρ - e` (`P_{≤k} Y = Y`), and also
at least `ρ - ‖T - X‖ ≥ ρ - e` if `ρ` is a bound at `X` (`X - T = (1 - P_{≤k}) (X - Y)`).

## References

* [LubichOseledetsVandereycken2015]
* [BachmayrEisenmannUschmajew2025, Prop. 4.11]
* S. Budzinskiy, N. Zamarashkin, arXiv 2110.03975, Lemma 3.1
-/

open Matrix Finset
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Tensor

/-! ### Unfoldings and maps acting on some of the modes -/

section Unfold

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- Acting on the modes outside `p` is right multiplication of the `p`-unfolding by the
transposed matrix. -/
theorem unfold_actOn_compl (p : κ → Prop) [DecidablePred p]
    (N : Matrix (∀ k : {k // ¬ p k}, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ) (X : Tensor ι) :
    unfold p (actOn (fun k => ¬ p k) N X) = unfold p X * Nᵀ := by
  ext a b
  simp only [unfold_apply, actOn_apply, Matrix.mul_apply, Matrix.transpose_apply,
    restrict_not_merge]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : override (fun k => ¬ p k) (merge p a b) z = merge p a z := by
    funext k
    by_cases h : p k <;> simp [override, merge, h]
  rw [hz, mul_comm]

/-- **Acting on a subset of the row modes.** If every mode in `q` is in `p`, then a matrix
acting on the modes in `q` multiplies the `p`-unfolding from the left by a matrix that does not
depend on the tensor. -/
theorem exists_unfold_actOn_eq_mul_of_imp {p q : κ → Prop} [DecidablePred p] [DecidablePred q]
    (hqp : ∀ k, q k → p k) (M : Matrix (∀ k : Subtype q, ι k) (∀ k : Subtype q, ι k) ℝ) :
    ∃ M' : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ,
      ∀ X : Tensor ι, unfold p (actOn q M X) = M' * unfold p X := by
  classical
  obtain ⟨ovr, hovr⟩ : ∃ ovr : (∀ k : Subtype p, ι k) → (∀ k : Subtype q, ι k) →
      ∀ k : Subtype p, ι k, ∀ a z k, ovr a z k = if h : q k.1 then z ⟨k.1, h⟩ else a k :=
    ⟨_, fun _ _ _ => rfl⟩
  refine ⟨Matrix.of fun a a' => ∑ z, M (restrictLE hqp a) z * if a' = ovr a z then 1 else 0,
    fun X => ?_⟩
  ext a b
  have hr : Subtype.restrict q (merge p a b) = restrictLE hqp a := by
    funext k
    simp [merge, restrictLE, Subtype.restrict, hqp k.1 k.2]
  have ho : ∀ z, override q (merge p a b) z = merge p (ovr a z) b := fun z => by
    funext k
    by_cases hp : p k
    · by_cases hq : q k <;> simp [override, merge, hovr, hp, hq]
    · have hq : ¬ q k := fun h => hp (hqp k h)
      simp [override, merge, hp, hq]
  simp only [unfold_apply, actOn_apply, Matrix.mul_apply, Matrix.of_apply, hr, ho,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single (ovr a z) (fun a' _ ha' => by simp [ha'])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

/-- Acting on a subset of the row modes does not raise the rank of the unfolding. -/
theorem rank_unfold_actOn_le_of_imp {p q : κ → Prop} [DecidablePred p] [DecidablePred q]
    (hqp : ∀ k, q k → p k) (M : Matrix (∀ k : Subtype q, ι k) (∀ k : Subtype q, ι k) ℝ)
    (X : Tensor ι) : (unfold p (actOn q M X)).rank ≤ (unfold p X).rank := by
  obtain ⟨M', h⟩ := exists_unfold_actOn_eq_mul_of_imp (p := p) hqp M
  rw [h]
  exact Matrix.rank_mul_le_right _ _

variable [∀ k, DecidableEq (ι k)]

/-- **The normal component at an interface of a tensor of unfolding rank at most `q`.** Let the
unfolding `Mat_p(T)` have rank at most `q` and `0 < ρ ≤ σ_{q-1}(Mat_p(T))`. For every matrix `S`
acting on the modes in `p` and every `N` acting on the other modes:
`ρ ‖(1 - S) (1 - N) T‖ ≤ ‖(1 - S) T‖ ‖(1 - N) T‖`. -/
theorem mul_norm_sub_actOn_sub_actOn_compl_le (p : κ → Prop) [DecidablePred p]
    (S : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ)
    (N : Matrix (∀ k : {k // ¬ p k}, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ) {q : ℕ} {T : Tensor ι}
    (hT : (unfold p T).rank ≤ q) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin (unfold p T)).singularValues (q - 1)) :
    ρ * ‖(T - actOn (fun k => ¬ p k) N T) - actOn p S (T - actOn (fun k => ¬ p k) N T)‖ ≤
      ‖T - actOn p S T‖ * ‖T - actOn (fun k => ¬ p k) N T‖ := by
  have e1 : unfold p (T - actOn (fun k => ¬ p k) N T) = unfold p T * (1 - Nᵀ) := by
    rw [unfold_sub, unfold_actOn_compl, Matrix.mul_sub, Matrix.mul_one]
  have e2 : unfold p (T - actOn p S T) = (1 - S) * unfold p T := by
    rw [unfold_sub, unfold_actOn, Matrix.sub_mul, Matrix.one_mul]
  have e3 : unfold p ((T - actOn (fun k => ¬ p k) N T) -
      actOn p S (T - actOn (fun k => ¬ p k) N T)) = (1 - S) * unfold p T * (1 - Nᵀ) := by
    rw [unfold_sub, unfold_actOn, e1, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  have h := norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul hT hρ hσ (1 - S) (1 - Nᵀ)
  rw [← e3, ← e1, ← e2, norm_unfold, norm_unfold, norm_unfold] at h
  calc ρ * ‖(T - actOn (fun k => ¬ p k) N T) - actOn p S (T - actOn (fun k => ¬ p k) N T)‖
      ≤ ρ * (ρ⁻¹ * ‖T - actOn p S T‖ * ‖T - actOn (fun k => ¬ p k) N T‖) :=
        mul_le_mul_of_nonneg_left h hρ.le
    _ = ‖T - actOn p S T‖ * ‖T - actOn (fun k => ¬ p k) N T‖ := by
        field_simp

end Unfold

/-! ### Tensor trains -/

section Train

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
  {β : ℕ → Type*} [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]

/-- **The normal component of a tensor at a tensor train, from the unfoldings of its prefix
projections.** Let `Y = tt A = tt B` with left-orthogonal cores `A` and right-orthogonal cores
`B`, `d ≥ 1` modes, and let `Z` be a tensor such that for every interface `0 < k + 1 < d` the
unfolding of `P_{≤k} Z` with respect to the first `k + 1` modes has rank at most `|β (k + 1)|`
and its singular value `σ_{|β (k + 1)|}` is at least `σ > 0`. Then
`(σ² - ‖Z - Y‖²) ‖Z - P(Y) Z‖² ≤ ‖Z - Y‖⁴ / 2`. -/
theorem sub_mul_norm_sq_sub_ttTangentProj_apply_le [Unique (β 0)] [Unique (β d)]
    {A B : TTCores ι β} (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i)
    (hAB : tt B = tt A) {Z : Tensor ι} {σ : ℝ} (hσ0 : 0 < σ)
    (hrk : ∀ k, k + 1 < d → (unfold (fun i : Fin d => i.val < k + 1)
      (ttLeftProj A k Z)).rank ≤ Fintype.card (β (k + 1)))
    (hσ : ∀ k, k + 1 < d → σ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k + 1)
      (ttLeftProj A k Z))).singularValues (Fintype.card (β (k + 1)) - 1)) :
    (σ ^ 2 - ‖Z - tt A‖ ^ 2) * ‖Z - ttTangentProj A B Z‖ ^ 2 ≤ ‖Z - tt A‖ ^ 4 / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hQl : ∀ k, k ≤ n + 1 → IsOrthProj (ttLeftProj A k) := fun k hk =>
    isOrthProj_ttLeftProj hk fun i _ => hA i
  have hQr : ∀ k, k ≤ n + 1 → IsOrthProj (ttRightProj B k) := fun k hk =>
    isOrthProj_ttRightProj hk fun i _ => hB i
  have hsum : ttTangentProj A B = ttTangentSum (fun k => ttLeftProj A (min k (n + 1)))
      (fun k => ttRightProj B (min k (n + 1))) (n + 1) := by
    rw [ttTangentProj, ttTangentSum, ttTangentSum]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left (Nat.succ_le_of_lt hk)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      rw [Nat.min_eq_left (show k + 1 ≤ n + 1 by omega)]
  have hlr : ∀ k, ttLeftProj A (min k (n + 1)) * ttLeftProj A (min (k + 1) (n + 1)) =
      ttLeftProj A (min (k + 1) (n + 1)) := fun k => by
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · rw [Nat.min_eq_left h.le, Nat.min_eq_left (Nat.succ_le_of_lt h)]
      exact ttLeftProj_mul_succ fun i _ => hA i
    · rw [Nat.min_eq_right h, Nat.min_eq_right (show n + 1 ≤ k + 1 by omega)]
      ext1 W
      exact (hQl _ le_rfl).idem W
  -- the interface `k + 1`
  have hm : ∀ k, k < n → σ * ‖ttLeftProj A k (Z - ttRightProj B (k + 1) Z) -
      ttLeftProj A (k + 1) (Z - ttRightProj B (k + 1) Z)‖ ≤
      ‖ttLeftProj A k Z - ttLeftProj A (k + 1) Z‖ *
        ‖ttLeftProj A k (Z - ttRightProj B (k + 1) Z)‖ := fun k hk => by
    have hc : ∀ W, ttLeftProj A k (ttRightProj B (k + 1) W) =
        ttRightProj B (k + 1) (ttLeftProj A k W) := fun W =>
      congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T W)
        (ttLeftProj_comm_ttRightProj A B (Nat.le_succ k))
    have hlrA : ∀ W, ttLeftProj A k (ttLeftProj A (k + 1) W) = ttLeftProj A (k + 1) W :=
      fun W => congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T W)
        (ttLeftProj_mul_succ fun i _ => hA i)
    have hlkA : ∀ W, ttLeftProj A (k + 1) (ttLeftProj A k W) = ttLeftProj A (k + 1) W :=
      fun W => by
        refine ext_inner_right ℝ fun w => ?_
        rw [(hQl (k + 1) (by omega)).symm, (hQl k (by omega)).symm, hlrA,
          ← (hQl (k + 1) (by omega)).symm]
    have hrk' := hrk k (by omega)
    have hσ' := hσ k (by omega)
    obtain ⟨T, hT⟩ : ∃ T, T = ttLeftProj A k Z := ⟨_, rfl⟩
    rw [← hT] at hrk' hσ'
    have ea : ttLeftProj A k (Z - ttRightProj B (k + 1) Z) = T - ttRightProj B (k + 1) T := by
      rw [map_sub, hc, hT]
    have eb : ttLeftProj A (k + 1) (Z - ttRightProj B (k + 1) Z) =
        ttLeftProj A (k + 1) (T - ttRightProj B (k + 1) T) := by
      rw [← ea, hlkA]
    have ec : ttLeftProj A (k + 1) Z = ttLeftProj A (k + 1) T := by rw [hT, hlkA]
    rw [ea, eb, ec, ← hT, ttLeftProj, ttRightProj]
    exact mul_norm_sub_actOn_sub_actOn_compl_le (fun i : Fin (n + 1) => i.val < k + 1) _ _
      hrk' hσ0 hσ'
  have h := sub_mul_norm_sq_sub_ttTangentSum_apply_le
    (Ql := fun k => ttLeftProj A (min k (n + 1))) (Qr := fun k => ttRightProj B (min k (n + 1)))
    (n := n) (y := tt A) (z := Z) (σ := σ)
    (fun k => hQl _ (min_le_right _ _)) (fun k => hQr _ (min_le_right _ _))
    (by simpa using ttLeftProj_zero A) (by simpa using ttRightProj_self B)
    (fun j k hjk => ttLeftProj_comm_ttRightProj A B (min_le_min_right _ hjk)) hlr
    (fun k => ttLeftProj_tt (min_le_right _ _) fun i _ => hA i)
    (fun k => by
      rw [← hAB]
      exact ttRightProj_tt (min_le_right _ _) fun i _ => hB i)
    hσ0.le (fun k hk => by
      simp only [Nat.min_eq_left (show k ≤ n + 1 by omega),
        Nat.min_eq_left (show k + 1 ≤ n + 1 by omega)]
      exact hm k hk)
  rwa [← hsum] at h

omit [∀ i, DecidableEq (ι i)] [∀ k, DecidableEq (β k)] in
/-- The unfolding of a prefix projection of a tensor train has rank at most the bond
dimension. -/
theorem rank_unfold_ttLeftProj_tt_le (A G : TTCores ι β) {k : ℕ} (hk : k + 1 ≤ d) :
    (unfold (fun i : Fin d => i.val < k + 1) (ttLeftProj A k (tt G))).rank ≤
      Fintype.card (β (k + 1)) :=
  (rank_unfold_actOn_le_of_imp (fun (i : Fin d) (hi : i.val < k) => Nat.lt_succ_of_lt hi) _
    _).trans (rank_unfold_tt_le G (k + 1) hk)

/-- **The normal component of a nearby tensor train, with a constant independent of the number
of modes.** Let `Y = tt A = tt B` with left-orthogonal cores `A` and right-orthogonal cores `B`,
`d ≥ 1` modes, let `ρ` be a lower bound of the singular values `σ_{|β k|}` of the unfoldings
`Y⟨k⟩`, `0 < k < d`, and let `X = tt G` be a tensor train with the same bond dimensions and
`e = ‖X - Y‖ < ρ`. Then `ρ (ρ - 2 e) ‖X - P(Y) X‖² ≤ e⁴ / 2`. -/
theorem mul_norm_sq_sub_ttTangentProj_tt_le [Unique (β 0)] [Unique (β d)]
    {A B G : TTCores ι β} (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i)
    (hAB : tt B = tt A) {ρ : ℝ}
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt A))).singularValues (Fintype.card (β k) - 1))
    (he : ‖tt G - tt A‖ < ρ) :
    ρ * (ρ - 2 * ‖tt G - tt A‖) * ‖tt G - ttTangentProj A B (tt G)‖ ^ 2 ≤
      ‖tt G - tt A‖ ^ 4 / 2 := by
  have hpos : 0 < ρ - ‖tt G - tt A‖ := sub_pos.2 he
  have h := sub_mul_norm_sq_sub_ttTangentProj_apply_le hd hA hB hAB (Z := tt G) hpos
    (fun k hk => rank_unfold_ttLeftProj_tt_le A G hk.le) (fun k hk => ?_)
  · have e : (ρ - ‖tt G - tt A‖) ^ 2 - ‖tt G - tt A‖ ^ 2 =
        ρ * (ρ - 2 * ‖tt G - tt A‖) := by ring
    rwa [e] at h
  · have hy : ttLeftProj A k (tt A) = tt A := ttLeftProj_tt (by omega) fun i _ => hA i
    have hn : ‖unfold (fun i : Fin d => i.val < k + 1) (ttLeftProj A k (tt G)) -
        unfold (fun i : Fin d => i.val < k + 1) (tt A)‖ ≤ ‖tt G - tt A‖ := by
      have e2 : ttLeftProj A k (tt G) - tt A = ttLeftProj A k (tt G - tt A) := by
        rw [map_sub, hy]
      rw [← unfold_sub, norm_unfold, e2]
      exact (isOrthProj_ttLeftProj (by omega) fun i _ => hA i).norm_le _
    have hw := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius
      (unfold (fun i : Fin d => i.val < k + 1) (ttLeftProj A k (tt G)))
      (unfold (fun i : Fin d => i.val < k + 1) (tt A)) (Fintype.card (β (k + 1)) - 1))).1
    linarith [hσ (k + 1) (Nat.succ_pos k) hk]

/-- **The normal component of a nearby tensor train, with the singular values of the tensor
that is projected.** As `mul_norm_sq_sub_ttTangentProj_tt_le`, with `ρ` a lower bound of the
singular values `σ_{|β k|}` of the unfoldings `X⟨k⟩`, `0 < k < d`, of the tensor train `X = tt G`
instead of those of `Y`. -/
theorem mul_norm_sq_sub_ttTangentProj_tt_le_of_le_singularValues_tt [Unique (β 0)]
    [Unique (β d)] {A B G : TTCores ι β} (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i)
    (hB : ∀ i, IsRightOrth B i) (hAB : tt B = tt A) {ρ : ℝ}
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt G))).singularValues (Fintype.card (β k) - 1))
    (he : ‖tt G - tt A‖ < ρ) :
    ρ * (ρ - 2 * ‖tt G - tt A‖) * ‖tt G - ttTangentProj A B (tt G)‖ ^ 2 ≤
      ‖tt G - tt A‖ ^ 4 / 2 := by
  have hpos : 0 < ρ - ‖tt G - tt A‖ := sub_pos.2 he
  have h := sub_mul_norm_sq_sub_ttTangentProj_apply_le hd hA hB hAB (Z := tt G) hpos
    (fun k hk => rank_unfold_ttLeftProj_tt_le A G hk.le) (fun k hk => ?_)
  · have e : (ρ - ‖tt G - tt A‖) ^ 2 - ‖tt G - tt A‖ ^ 2 =
        ρ * (ρ - 2 * ‖tt G - tt A‖) := by ring
    rwa [e] at h
  · have hP := isOrthProj_ttLeftProj (A := A) (k := k) (by omega) fun i _ => hA i
    have hy : ttLeftProj A k (tt A) = tt A := ttLeftProj_tt (by omega) fun i _ => hA i
    have hn : ‖unfold (fun i : Fin d => i.val < k + 1) (ttLeftProj A k (tt G)) -
        unfold (fun i : Fin d => i.val < k + 1) (tt G)‖ ≤ ‖tt G - tt A‖ := by
      rw [← unfold_sub, norm_unfold, norm_sub_rev]
      have e : tt G - ttLeftProj A k (tt G) =
          (tt G - tt A) - ttLeftProj A k (tt G - tt A) := by
        rw [map_sub, hy]
        abel
      have h2 := hP.norm_sub_apply_sq (tt G - tt A) 0
      simp only [map_zero, sub_zero] at h2
      rw [e]
      exact (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖ttLeftProj A k (tt G - tt A)‖])
        (norm_nonneg _)).2
    have hw := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius
      (unfold (fun i : Fin d => i.val < k + 1) (ttLeftProj A k (tt G)))
      (unfold (fun i : Fin d => i.val < k + 1) (tt G)) (Fintype.card (β (k + 1)) - 1))).1
    linarith [hσ (k + 1) (Nat.succ_pos k) hk]

/-- From `ρ (ρ - 2 e) n² ≤ e⁴ / 2` and `2 e < ρ` to `n ≤ e² / √(2 ρ (ρ - 2 e))`. -/
theorem le_sq_div_sqrt_of_mul_sq_le {ρ e n : ℝ} (he0 : 0 ≤ e) (he : 2 * e < ρ)
    (h : ρ * (ρ - 2 * e) * n ^ 2 ≤ e ^ 4 / 2) : n ≤ e ^ 2 / √(2 * ρ * (ρ - 2 * e)) := by
  have hD : 0 < 2 * ρ * (ρ - 2 * e) := mul_pos (by linarith) (by linarith)
  have hsq : n ^ 2 ≤ (e ^ 2 / √(2 * ρ * (ρ - 2 * e))) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hD.le, le_div_iff₀ hD]
    nlinarith
  exact (abs_le_of_sq_le_sq' hsq (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))).2

/-- **The normal component of a nearby tensor train, explicit form.** Under the hypotheses of
`mul_norm_sq_sub_ttTangentProj_tt_le`, if `2 ‖X - Y‖ < ρ` then
`‖X - P(Y) X‖ ≤ ‖X - Y‖² / √(2 ρ (ρ - 2 ‖X - Y‖))`. -/
theorem norm_sub_ttTangentProj_tt_le [Unique (β 0)] [Unique (β d)] {A B G : TTCores ι β}
    (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i) (hAB : tt B = tt A)
    {ρ : ℝ}
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt A))).singularValues (Fintype.card (β k) - 1))
    (he : 2 * ‖tt G - tt A‖ < ρ) :
    ‖tt G - ttTangentProj A B (tt G)‖ ≤
      ‖tt G - tt A‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tt G - tt A‖)) :=
  le_sq_div_sqrt_of_mul_sq_le (norm_nonneg _) he
    (mul_norm_sq_sub_ttTangentProj_tt_le hd hA hB hAB hσ
      (by linarith [norm_nonneg (tt G - tt A)]))

/-- **The normal component of a nearby tensor train, explicit form with the singular values of
the tensor that is projected.** Under the hypotheses of
`mul_norm_sq_sub_ttTangentProj_tt_le_of_le_singularValues_tt`, if `2 ‖X - Y‖ < ρ` then
`‖X - P(Y) X‖ ≤ ‖X - Y‖² / √(2 ρ (ρ - 2 ‖X - Y‖))`. -/
theorem norm_sub_ttTangentProj_tt_le_of_le_singularValues_tt [Unique (β 0)] [Unique (β d)]
    {A B G : TTCores ι β} (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i)
    (hAB : tt B = tt A) {ρ : ℝ}
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt G))).singularValues (Fintype.card (β k) - 1))
    (he : 2 * ‖tt G - tt A‖ < ρ) :
    ‖tt G - ttTangentProj A B (tt G)‖ ≤
      ‖tt G - tt A‖ ^ 2 / √(2 * ρ * (ρ - 2 * ‖tt G - tt A‖)) :=
  le_sq_div_sqrt_of_mul_sq_le (norm_nonneg _) he
    (mul_norm_sq_sub_ttTangentProj_tt_le_of_le_singularValues_tt hd hA hB hAB hσ
      (by linarith [norm_nonneg (tt G - tt A)]))

end Train

/-! ### Examples: elementary tensor trains with three modes -/

namespace TTNormalSecondOrderTrainExamples

/-- The cores of the elementary tensor train `v ⊗ v ⊗ v` on three modes of size two (all bond
dimensions one). -/
def elemCores (v : Fin 2 → ℝ) : TTCores (fun _ : Fin 3 => Fin 2) (fun _ => Fin 1) :=
  fun _ _ x _ => v x

/-- The cores of `e₁ ⊗ e₁ ⊗ e₁`. -/
def baseCores : TTCores (fun _ : Fin 3 => Fin 2) (fun _ => Fin 1) := elemCores ![1, 0]

/-- The cores of `v ⊗ v ⊗ v` with the unit vector `v = (40/41, 9/41)`. -/
noncomputable def nearCores : TTCores (fun _ : Fin 3 => Fin 2) (fun _ => Fin 1) :=
  elemCores ![40 / 41, 9 / 41]

/-- The cores of an elementary tensor train of a unit vector are left-orthogonal. -/
theorem isLeftOrth_elemCores {v : Fin 2 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 = 1) (i : Fin 3) :
    IsLeftOrth (elemCores v) i := by
  intro b b'
  obtain rfl := Subsingleton.elim b b'
  change ∑ _a : Fin 1, ∑ x : Fin 2, v x * v x = (1 : Matrix (Fin 1) (Fin 1) ℝ) b b
  rw [Fin.sum_univ_one, Fin.sum_univ_two, Matrix.one_apply_eq, ← hv]
  ring

/-- The cores of an elementary tensor train of a unit vector are right-orthogonal. -/
theorem isRightOrth_elemCores {v : Fin 2 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 = 1) (i : Fin 3) :
    IsRightOrth (elemCores v) i := by
  intro a a'
  obtain rfl := Subsingleton.elim a a'
  change ∑ x : Fin 2, ∑ _b : Fin 1, v x * v x = (1 : Matrix (Fin 1) (Fin 1) ℝ) a a
  rw [Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one, Matrix.one_apply_eq, ← hv]
  ring

/-- The inner product of two elementary tensor trains is the cube of the inner product of the
vectors. -/
theorem inner_tt_elemCores (v w : Fin 2 → ℝ) :
    ⟪tt (elemCores v), tt (elemCores w)⟫ = (v 0 * w 0 + v 1 * w 1) ^ 3 := by
  rw [inner_eq_sum]
  have h := Fintype.prod_sum (fun (_ : Fin 3) (a : Fin 2) => v a * w a)
  rw [Fin.sum_univ_two, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tt_rankOne, tt_rankOne, ← Finset.prod_mul_distrib]
  rfl

/-- The squared distance of two elementary tensor trains. -/
theorem norm_sq_tt_elemCores_sub (v w : Fin 2 → ℝ) :
    ‖tt (elemCores v) - tt (elemCores w)‖ ^ 2 =
      (v 0 * v 0 + v 1 * v 1) ^ 3 - 2 * (v 0 * w 0 + v 1 * w 1) ^ 3 +
        (w 0 * w 0 + w 1 * w 1) ^ 3 := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_tt_elemCores, inner_tt_elemCores, inner_tt_elemCores]

/-- A column with `wᵀ w = 1` has the Frobenius norm one. -/
theorem norm_eq_one_of_transpose_mul_self {m : Type*} [Fintype m] {w : Matrix m (Fin 1) ℝ}
    (h : wᵀ * w = 1) : ‖w‖ = 1 := by
  have h1 : ∑ i, w i 0 * w i 0 = 1 := by
    have h0 := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply] using h0
  have h2 : ‖w‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum, ← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [Fin.sum_univ_one, sq]
  exact (sq_eq_sq₀ (norm_nonneg w) zero_le_one).1 (h2.trans (one_pow 2).symm)

/-- The singular value of every unfolding of an elementary tensor train of a unit vector is at
least one. -/
theorem one_le_singularValues_unfold_tt_elemCores {v : Fin 2 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 = 1)
    {k : ℕ} (hk : k ≤ 3) :
    1 ≤ (toEuclideanLin (unfold (fun i : Fin 3 => i.val < k)
      (tt (elemCores v)))).singularValues (Fintype.card (Fin 1) - 1) := by
  have hL := ttLeft_transpose_mul_self (A := elemCores v) k hk fun i _ =>
    isLeftOrth_elemCores hv i
  have hR := ttRight_transpose_mul_self (B := elemCores v) k hk fun i _ =>
    isRightOrth_elemCores hv i
  have h := Curvature.frob_mul_le (unfold (fun i : Fin 3 => i.val < k) (tt (elemCores v)))
    (ttRight (elemCores v) k)
  rw [unfold_tt _ k hk, Matrix.mul_assoc, hR, Matrix.mul_one,
    norm_eq_one_of_transpose_mul_self hL, norm_eq_one_of_transpose_mul_self hR, mul_one] at h
  rwa [show Fintype.card (Fin 1) - 1 = 0 by simp,
    ← EckartYoung.specNorm_eq_singularValues_zero, unfold_tt _ k hk]

/-- `e₁` is a unit vector. -/
theorem base_unit : (![1, 0] : Fin 2 → ℝ) 0 ^ 2 + (![1, 0] : Fin 2 → ℝ) 1 ^ 2 = 1 := by
  norm_num

/-- `(40/41, 9/41)` is a unit vector. -/
theorem near_unit :
    (![40 / 41, 9 / 41] : Fin 2 → ℝ) 0 ^ 2 + (![40 / 41, 9 / 41] : Fin 2 → ℝ) 1 ^ 2 = 1 := by
  norm_num

/-- The cores of `e₁ ⊗ e₁ ⊗ e₁` are left-orthogonal. -/
theorem isLeftOrth_baseCores (i : Fin 3) : IsLeftOrth baseCores i :=
  isLeftOrth_elemCores base_unit i

/-- The cores of `e₁ ⊗ e₁ ⊗ e₁` are right-orthogonal. -/
theorem isRightOrth_baseCores (i : Fin 3) : IsRightOrth baseCores i :=
  isRightOrth_elemCores base_unit i

/-- The cores of `v ⊗ v ⊗ v`, `v = (40/41, 9/41)`, are left-orthogonal. -/
theorem isLeftOrth_nearCores (i : Fin 3) : IsLeftOrth nearCores i :=
  isLeftOrth_elemCores near_unit i

/-- The cores of `v ⊗ v ⊗ v`, `v = (40/41, 9/41)`, are right-orthogonal. -/
theorem isRightOrth_nearCores (i : Fin 3) : IsRightOrth nearCores i :=
  isRightOrth_elemCores near_unit i

/-- The singular values of the unfoldings of `e₁ ⊗ e₁ ⊗ e₁` are at least one. -/
theorem one_le_singularValues_unfold_tt_baseCores (k : ℕ) (_ : 0 < k) (hk : k < 3) :
    1 ≤ (toEuclideanLin (unfold (fun i : Fin 3 => i.val < k)
      (tt baseCores))).singularValues (Fintype.card (Fin 1) - 1) :=
  one_le_singularValues_unfold_tt_elemCores base_unit hk.le

/-- The singular values of the unfoldings of `v ⊗ v ⊗ v`, `v = (40/41, 9/41)`, are at least
one. -/
theorem one_le_singularValues_unfold_tt_nearCores (k : ℕ) (_ : 0 < k) (hk : k < 3) :
    1 ≤ (toEuclideanLin (unfold (fun i : Fin 3 => i.val < k)
      (tt nearCores))).singularValues (Fintype.card (Fin 1) - 1) :=
  one_le_singularValues_unfold_tt_elemCores near_unit hk.le

/-- The squared distance of the two tensor trains of the examples. -/
theorem norm_sq_tt_nearCores_sub_tt_baseCores :
    ‖tt nearCores - tt baseCores‖ ^ 2 = 9842 / 68921 := by
  rw [nearCores, baseCores, norm_sq_tt_elemCores_sub]
  norm_num

/-- The distance of the two tensor trains of the examples is positive and less than `2/5`. -/
theorem norm_tt_nearCores_sub_tt_baseCores_pos_lt :
    0 < ‖tt nearCores - tt baseCores‖ ∧ ‖tt nearCores - tt baseCores‖ < 2 / 5 := by
  have h := norm_sq_tt_nearCores_sub_tt_baseCores
  have h0 := norm_nonneg (tt nearCores - tt baseCores)
  constructor
  · rcases h0.eq_or_lt with h1 | h1
    · rw [← h1] at h
      norm_num at h
    · exact h1
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h]; norm_num)

/-- The two tensor trains of the examples are different. -/
theorem tt_nearCores_ne_tt_baseCores : tt nearCores ≠ tt baseCores := fun h => by
  have hd := norm_tt_nearCores_sub_tt_baseCores_pos_lt.1
  rw [h, sub_self, norm_zero] at hd
  exact lt_irrefl _ hd

/-- Non-vacuity of `mul_norm_sq_sub_ttTangentProj_tt_le` and `norm_sub_ttTangentProj_tt_le` with
three modes of dimension two: `Y = e₁ ⊗ e₁ ⊗ e₁`, `X = v ⊗ v ⊗ v` with `v = (40/41, 9/41)`, and
`ρ = 1`. All hypotheses hold, `X ≠ Y`, and `2 ‖X - Y‖ < ρ`. (The normal component of `X` at `Y`
has the entries `v₁ v₂²` and `v₂³`; that it does not vanish is not part of the statement.) -/
example : tt nearCores ≠ tt baseCores ∧
    ‖tt nearCores - ttTangentProj baseCores baseCores (tt nearCores)‖ ≤
      ‖tt nearCores - tt baseCores‖ ^ 2 /
        √(2 * 1 * (1 - 2 * ‖tt nearCores - tt baseCores‖)) := by
  have hd := norm_tt_nearCores_sub_tt_baseCores_pos_lt
  refine ⟨fun h => ?_, norm_sub_ttTangentProj_tt_le (A := baseCores) (by norm_num)
    isLeftOrth_baseCores isRightOrth_baseCores rfl one_le_singularValues_unfold_tt_baseCores
    (by linarith [hd.2])⟩
  rw [h, sub_self, norm_zero] at hd
  exact lt_irrefl _ hd.1

/-- Non-vacuity of `mul_norm_sq_sub_ttTangentProj_tt_le_of_le_singularValues_tt` and
`sub_mul_norm_sq_sub_ttTangentProj_apply_le` for the same tensor trains, with the singular
values of `X = v ⊗ v ⊗ v`. -/
example : (1 : ℝ) * (1 - 2 * ‖tt nearCores - tt baseCores‖) *
    ‖tt nearCores - ttTangentProj baseCores baseCores (tt nearCores)‖ ^ 2 ≤
      ‖tt nearCores - tt baseCores‖ ^ 4 / 2 :=
  mul_norm_sq_sub_ttTangentProj_tt_le_of_le_singularValues_tt (A := baseCores)
    (G := nearCores) (by norm_num) isLeftOrth_baseCores isRightOrth_baseCores rfl
    one_le_singularValues_unfold_tt_nearCores
    (by linarith [norm_tt_nearCores_sub_tt_baseCores_pos_lt.2])

/-- Non-vacuity of `mul_norm_sub_actOn_sub_actOn_compl_le`, `unfold_actOn_compl` and
`exists_unfold_actOn_eq_mul_of_imp`: the tensor `e₁ ⊗ e₁ ⊗ e₁`, the first mode, the zero
matrices and `ρ = 1`. -/
example : (1 : ℝ) * ‖(tt baseCores - actOn (fun i : Fin 3 => ¬ i.val < 1) 0 (tt baseCores)) -
      actOn (fun i : Fin 3 => i.val < 1) 0
        (tt baseCores - actOn (fun i : Fin 3 => ¬ i.val < 1) 0 (tt baseCores))‖ ≤
    ‖tt baseCores - actOn (fun i : Fin 3 => i.val < 1) 0 (tt baseCores)‖ *
      ‖tt baseCores - actOn (fun i : Fin 3 => ¬ i.val < 1) 0 (tt baseCores)‖ :=
  mul_norm_sub_actOn_sub_actOn_compl_le (fun i : Fin 3 => i.val < 1) 0 0
    (rank_unfold_tt_le baseCores 1 (by norm_num)) one_pos
    (one_le_singularValues_unfold_tt_baseCores 1 one_pos (by norm_num))

end TTNormalSecondOrderTrainExamples

end LeanDLRA.Tensor
