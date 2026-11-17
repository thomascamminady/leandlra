import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2401.03748: Federated recommendation via low-rank training (CoLR)

Ngoc-Hieu et al., *Towards Efficient Communication and Secure Federated Recommendation System via
Low-rank Training* (WWW 2024, arXiv v2).  This module proves that one local gradient step of
federated matrix factorization changes the item matrix by a rank-one term plus regularization and
that the data part of `τ` steps has rank at most `τ` (Sec. 4.1), that aggregation with a shared
frozen basis is linear, has rank at most `r` and only adds (Sec. 4.3), and the error analysis of
random low-rank updates (Appendix D): a corrected Proposition D.1 with counterexamples to the
printed form, both parts of Lemma D.2 for genuine Gaussian matrices (`gaussianReal`, spectral
norm, explicit constant `26`), and Theorem D.3 as an exact identity.

## Main results

* Sec. 4.1: `hasGradientAt_localLoss`, `hasGradientAt_localLoss_sq`, `itemStep_eq_gradient_step`,
  `itemStep_sub`, `rank_itemStep_data_le_one`, `itemIter_eq`, `rank_dataPart_le`,
  `localTraining_lowRank`.
* Sec. 4.2, 4.3: `hasGradientAt_frozenBasis`, `colr_first_step`, `colr_aggregate`,
  `rank_colr_aggregate_le`, `colr_aggregate_mem_range_leftProj`, `colr_secure_aggregate`,
  `exists_rank_sum_gt`.
* Appendix D: `propD1`, `propD1_counterexample`, `propD1_biasTerm_counterexample`,
  `lemmaD2_unbiased`, `lemmaD2_opNorm`, `theoremD3_eq`, `theoremD3`, `sharedSketch_mse`,
  `exists_gaussianSketch_family`.

## Differences from the paper

* **Proposition D.1 is false as printed.**  Hypothesis (1) reads `E‖B‖² ≤ L_B`, but the last step of
  the proof uses `E‖B Bᵀ‖² ≤ L_B²`, that is `E‖B‖⁴ ≤ (E‖B‖²)²`, which is Jensen's inequality in the
  wrong direction.  `propD1_counterexample` is a two-point scalar law with `E‖B‖² = 1`,
  `E[B Bᵀ] = 1` and error `3 > 2`.  `propD1` proves the statement under the hypothesis the proof
  really uses, `E‖B‖⁴ ≤ L²`.
* **The constant `C_p` is undefined in the paper.**  Eq. (11) bounds a single cross term and loses
  the `|S| (|S| - 1)` terms of the double sum and the `α`s, so the printed `(1/|S|) C_p² δ_B` fails
  for every `C_p` independent of `|S|` (`propD1_biasTerm_counterexample`).  Here `C_p` is
  `crossConst`, the double sum `∑_{u ≠ v} |α_u α_v| ‖p_u‖₂ ‖p_v‖₂`, which in general grows like
  `|S|²`.
* **Theorem D.3 does not follow from Proposition D.1 and Lemma D.2**, as the paper claims.  The
  corrected D.1 needs `L² ≥ E‖B‖⁴ ≥ (E‖B‖²)² ≥ (d/r)²` (the last step because `‖B e₁‖₂² ≤ ‖B‖²` with
  mean `d/r`), which only gives `O((d/r)²)`.  `theoremD3_eq` instead computes the fourth moments
  directly (Isserlis' formula) and obtains the exact value, with the paper's order `d/r`.
* The printed `max_u α_u ‖p_u‖²` (in D.1 and D.3) has `α_u` where the proofs have `α_u²`; we state
  `α_u²`.  Lemma D.2 prints `N(0, 1/k)` for `N(0, 1/r)`.  The `O` in D.2 (1) is made explicit, with
  constant `26`, and `r ≤ d` is enough; the paper gives no proof of this part.  Pairwise
  independence of the `B_u` suffices, and in D.1 they need not be identically distributed.
* Appendix D assumes independent `B_u`, whereas CoLR (Sec. 4.3) shares one `B`.  `sharedSketch_mse`
  is the shared case, which is not in the paper: there is no factor `1/|S|`.
* Eq. (4) prints the rank-one term as `(m ∗ (r - r̂)) pᵀ`, which does not match `r̂ = Qᵀ p` with
  `q_i` the columns of `Q`; we use `p (m ∗ (r - r̂))ᵀ`.  The user-embedding update (3) is not
  needed: `itemIter_eq` holds for arbitrary `p_t`.
* "Needs only additions" (Sec. 4.3) is modelled by an additive map `dec : C →+ _` from ciphertexts,
  so `colr_secure_aggregate` is a statement about the algebra of aggregation, not about security.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2401_03748

section LocalTraining

open scoped LeanDLRA.Frobenius

variable {d ι k U : Type*}

/-- The predicted ratings `r̂ = Qᵀ p` of a user with embedding `p ∈ ℝ^d`; the item embeddings
`q_i` are the columns of `Q`, so `r̂_i = q_iᵀ p` (arXiv 2401.03748, Sec. 4.1). -/
def predicted [Fintype d] (Q : Matrix d ι ℝ) (p : d → ℝ) : ι → ℝ := Qᵀ *ᵥ p

/-- The local objective `L_u(p, Q) = ∑_{i ∈ O} ℓ_i((Qᵀ p)_i) + λ/2 ‖p‖² + λ/2 ‖Q‖_F²` of
arXiv 2401.03748, Sec. 4.1, where `O` is the set of items observed by user `u` and
`l i = ℓ(r_{ui}, ·)` is the per-item loss. -/
noncomputable def localLoss [Fintype d] [Fintype ι] (O : Finset ι) (l : ι → ℝ → ℝ) (lam : ℝ)
    (p : d → ℝ)
    (Q : Matrix d ι ℝ) : ℝ :=
  ∑ i ∈ O, l i (predicted Q p i) + lam / 2 * ∑ j, p j ^ 2 + lam / 2 * ‖Q‖ ^ 2

/-- The squared per-item loss `ℓ(r_i, x) = (r_i - x)² / 2`, for which the gradient steps of
arXiv 2401.03748, Sec. 4.1, take the form (3)-(5) with `r - r̂`. -/
noncomputable def sqLoss (r : ι → ℝ) : ι → ℝ → ℝ := fun i x => (r i - x) ^ 2 / 2

/-- The masked residual `m ∗ (r - r̂)` of arXiv 2401.03748, Sec. 4.1, where `m` is the indicator
of the observed items `O`. -/
noncomputable def residual [Fintype d] [DecidableEq ι] (O : Finset ι) (r : ι → ℝ)
    (Q : Matrix d ι ℝ) (p : d → ℝ) : ι → ℝ :=
  fun i => (if i ∈ O then 1 else 0) * (r i - predicted Q p i)

/-- One local update of the item matrix, arXiv 2401.03748, eq. (4), in the orientation that matches
`r̂ = Qᵀ p`: `Q⁺ = Q - η (λ Q - p (m ∗ (r - r̂))ᵀ)`.  See `itemStep_eq_gradient_step`. -/
noncomputable def itemStep [Fintype d] [DecidableEq ι] (η lam : ℝ) (O : Finset ι) (r : ι → ℝ)
    (p : d → ℝ)
    (Q : Matrix d ι ℝ) : Matrix d ι ℝ :=
  Q - η • (lam • Q - Matrix.vecMulVec p (residual O r Q p))

/-- The data part of `τ` local steps: `η ∑_{s<τ} (1 - ηλ)^{τ-1-s} p_s e_sᵀ`, the sum of the
rank-one terms discounted by the regularization. -/
noncomputable def dataPart (η lam : ℝ) (e : ℕ → ι → ℝ) (p : ℕ → d → ℝ) (τ : ℕ) : Matrix d ι ℝ :=
  ∑ s ∈ Finset.range τ, (η * (1 - η * lam) ^ (τ - 1 - s)) • Matrix.vecMulVec (p s) (e s)

/-- `(Qᵀ p)_i` is the Frobenius inner product of `Q` with `p e_iᵀ`. -/
private theorem predicted_eq_inner [Fintype d] [Fintype ι] [DecidableEq ι] (Q : Matrix d ι ℝ)
    (p : d → ℝ) (i : ι) :
    predicted Q p i = ⟪Matrix.vecMulVec p (Pi.single i 1), Q⟫ := by
  simp only [predicted, Matrix.mulVec, dotProduct, LeanDLRA.Frobenius.inner_def,
    Matrix.vecMulVec_apply, Matrix.transpose_apply, Pi.single_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

/-- **arXiv 2401.03748, Sec. 4.1** (gradient of the local loss in the item matrix): for any
differentiable per-item loss, `∇_Q L_u = λ Q + p gᵀ` in the Frobenius inner product, with
`g_i = ℓ_i'(r̂_i)` on observed items and `0` otherwise.  This derives the rank-one structure of the
paper's update instead of assuming it, for a general `ℓ` (the paper states the squared case). -/
theorem hasGradientAt_localLoss [Fintype d] [Fintype ι] [DecidableEq ι] (O : Finset ι)
    (l l' : ι → ℝ → ℝ) (lam : ℝ) (p : d → ℝ)
    (Q : Matrix d ι ℝ)
    (hl : ∀ i ∈ O, HasDerivAt (l i) (l' i (predicted Q p i)) (predicted Q p i)) :
    HasGradientAt (localLoss O l lam p)
      (lam • Q + Matrix.vecMulVec p (fun i => if i ∈ O then l' i (predicted Q p i) else 0)) Q := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : ∀ i ∈ O, HasFDerivAt (fun Q : Matrix d ι ℝ => l i (predicted Q p i))
      (l' i (predicted Q p i) • innerSL ℝ (Matrix.vecMulVec p (Pi.single i 1))) Q := by
    intro i hi
    have hL : HasFDerivAt (fun Q : Matrix d ι ℝ => predicted Q p i)
        (innerSL ℝ (Matrix.vecMulVec p (Pi.single i 1))) Q := by
      have := (innerSL ℝ (Matrix.vecMulVec p (Pi.single i (1 : ℝ)))).hasFDerivAt (x := Q)
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun X => ?_)
      simpa using predicted_eq_inner X p i
    exact (hl i hi).comp_hasFDerivAt Q hL
  have h2 : HasFDerivAt (fun Q : Matrix d ι ℝ => lam / 2 * ‖Q‖ ^ 2)
      (lam • innerSL ℝ Q) Q := by
    have := ((hasFDerivAt_id Q).norm_sq).const_mul (lam / 2)
    refine this.congr_fderiv ?_
    ext X
    simp only [smul_apply, ContinuousLinearMap.comp_id, smul_eq_mul, id,
      nsmul_eq_mul, Nat.cast_ofNat, innerSL_apply_apply]
    ring
  have h3 := ((HasFDerivAt.fun_sum h1).add_const (lam / 2 * ∑ j, p j ^ 2)).add h2
  refine h3.congr_fderiv ?_
  ext X
  simp only [add_apply, sum_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, inner_add_left, real_inner_smul_left]
  rw [add_comm]
  congr 1
  have key : ∀ Y : ι → ℝ, ⟪Matrix.vecMulVec p Y, X⟫ =
      ∑ i, Y i * ⟪Matrix.vecMulVec p (Pi.single i 1), X⟫ := by
    intro Y
    simp only [LeanDLRA.Frobenius.inner_def, Matrix.vecMulVec_apply, Finset.mul_sum,
      Pi.single_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    symm
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro b _ hb; simp [hb]
    · simp
    · simp; ring
  rw [key, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ O)]
  have : ∑ x ∈ Finset.univ with x ∉ O, (if x ∈ O then l' x (predicted Q p x) else 0) *
      ⟪Matrix.vecMulVec p (Pi.single x 1), X⟫ = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    simp [(Finset.mem_filter.mp hx).2]
  rw [this, add_zero]
  have hf : (Finset.univ.filter (· ∈ O)) = O := by ext; simp
  rw [hf]
  exact Finset.sum_congr rfl fun i hi => by simp [hi]

/-- **arXiv 2401.03748, Sec. 4.1** (squared loss): `∇_Q L_u = λ Q - p (m ∗ (r - r̂))ᵀ`, the gradient
inside eq. (4).  The paper prints the rank-one term transposed, `(m ∗ (r - r̂)) pᵀ`, which does not
match `r̂ = Qᵀ p` with `q_i` the columns of `Q`; the statement here is the consistent one. -/
theorem hasGradientAt_localLoss_sq [Fintype d] [Fintype ι] [DecidableEq ι] (O : Finset ι)
    (r : ι → ℝ) (lam : ℝ) (p : d → ℝ)
    (Q : Matrix d ι ℝ) :
    HasGradientAt (localLoss O (sqLoss r) lam p)
      (lam • Q - Matrix.vecMulVec p (residual O r Q p)) Q := by
  have h := hasGradientAt_localLoss O (sqLoss r) (fun i x => -(r i - x)) lam p Q (fun i _ => by
    have := (((hasDerivAt_id (predicted Q p i)).const_sub (r i)).pow 2).div_const 2
    refine (this.congr_deriv ?_)
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, id]
    ring)
  have e : (fun i => if i ∈ O then -(r i - predicted Q p i) else 0) = -(residual O r Q p) := by
    ext i; by_cases hi : i ∈ O <;> simp [residual, hi]
  simp only [e] at h
  have e2 : Matrix.vecMulVec p (-residual O r Q p) = - Matrix.vecMulVec p (residual O r Q p) := by
    ext a b; simp [Matrix.vecMulVec_apply]
  rw [e2, ← sub_eq_add_neg] at h
  exact h

/-- **arXiv 2401.03748, eq. (5)**: the local update of the item matrix is a rank-one term plus
regularization, `ΔQ = η (p (m ∗ (r - r̂))ᵀ - λ Q)`.  Same orientation remark as
`hasGradientAt_localLoss_sq`. -/
theorem itemStep_sub [Fintype d] [DecidableEq ι] (η lam : ℝ) (O : Finset ι) (r : ι → ℝ)
    (p : d → ℝ) (Q : Matrix d ι ℝ) :
    itemStep η lam O r p Q - Q = η • (Matrix.vecMulVec p (residual O r Q p) - lam • Q) := by
  simp only [itemStep, sub_sub_cancel_left, ← smul_neg, neg_sub]

/-- **arXiv 2401.03748, eq. (4)**: `itemStep` is exactly one gradient descent step on the local
loss `L_u` in the item matrix `Q`, with squared per-item loss. -/
theorem itemStep_eq_gradient_step [Fintype d] [Fintype ι] [DecidableEq ι] (η lam : ℝ)
    (O : Finset ι) (r : ι → ℝ) (p : d → ℝ)
    (Q : Matrix d ι ℝ) :
    itemStep η lam O r p Q = Q - η • gradient (localLoss O (sqLoss r) lam p) Q := by
  rw [(hasGradientAt_localLoss_sq O r lam p Q).gradient, itemStep]

/-- **arXiv 2401.03748, Sec. 4.1**: the data part `η p eᵀ` of one local step has rank at most
one. -/
theorem rank_itemStep_data_le_one [Fintype ι] (η : ℝ) (e : ι → ℝ) (p : d → ℝ) :
    (η • Matrix.vecMulVec p e).rank ≤ 1 := by
  classical
  have : η • Matrix.vecMulVec p e = Matrix.vecMulVec (η • p) e := by
    ext a b; simp [Matrix.vecMulVec_apply, mul_assoc]
  rw [this]
  exact Matrix.rank_vecMulVec_le _ _

/-- **arXiv 2401.03748, Sec. 4.1** (`τ` local steps): along local training, whatever the user
embeddings `p_t` do (so in particular for eq. (3)),
`Q_τ = (1 - ηλ)^τ Q_0 + η ∑_{s<τ} (1 - ηλ)^{τ-1-s} p_s e_sᵀ` with `e_s = m ∗ (r - r̂_s)`. -/
theorem itemIter_eq [Fintype d] [DecidableEq ι] (η lam : ℝ) (O : Finset ι) (r : ι → ℝ)
    (p : ℕ → d → ℝ)
    (Q : ℕ → Matrix d ι ℝ) (hQ : ∀ t, Q (t + 1) = itemStep η lam O r (p t) (Q t)) (τ : ℕ) :
    Q τ = (1 - η * lam) ^ τ • Q 0 +
      dataPart η lam (fun t => residual O r (Q t) (p t)) p τ := by
  induction τ with
  | zero => simp [dataPart]
  | succ n ih =>
    have hs : Q (n + 1) = (1 - η * lam) • Q n +
        η • Matrix.vecMulVec (p n) (residual O r (Q n) (p n)) := by
      rw [hQ n, itemStep, smul_sub, smul_smul, sub_smul, one_smul]
      abel
    have h1 : (1 - η * lam) • dataPart η lam (fun t => residual O r (Q t) (p t)) p n =
        ∑ s ∈ Finset.range n, (η * (1 - η * lam) ^ (n + 1 - 1 - s)) •
          Matrix.vecMulVec (p s) (residual O r (Q s) (p s)) := by
      rw [dataPart, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [smul_smul]
      congr 1
      have : n + 1 - 1 - s = (n - 1 - s) + 1 := by have := Finset.mem_range.mp hs; omega
      rw [this, pow_succ]
      ring
    rw [hs]
    nth_rw 1 [ih]
    rw [smul_add, smul_smul, ← pow_succ', h1, dataPart, Finset.sum_range_succ]
    simp [add_assoc]

/-- **arXiv 2401.03748, Sec. 4.1**: the data part of `τ` local steps has rank at most `τ`, for
arbitrary vectors `e_s, p_s`.  Together with `itemIter_eq` this is the low-rank bias of the update,
and `Fin τ` is the width of an explicit factorization `U V`. -/
theorem rank_dataPart_le [Fintype ι] (η lam : ℝ) (e : ℕ → ι → ℝ) (p : ℕ → d → ℝ) (τ : ℕ) :
    (dataPart η lam e p τ).rank ≤ τ := by
  classical
  let U : Matrix d (Fin τ) ℝ :=
    Matrix.of fun j s => (η * (1 - η * lam) ^ (τ - 1 - (s : ℕ))) * p s j
  let V : Matrix (Fin τ) ι ℝ := Matrix.of fun s i => e s i
  have h : dataPart η lam e p τ = U * V := by
    ext j i
    simp only [dataPart, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Matrix.mul_apply, U, V, Matrix.of_apply]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h]
  exact (Matrix.rank_mul_le_left U V).trans (U.rank_le_card_width.trans (by simp))

/-- **arXiv 2401.03748, Sec. 4.1**, summary: after `τ` local steps on the item matrix,
`Q_τ` is the discounted initial matrix plus a data part of rank at most `τ`. -/
theorem localTraining_lowRank [Fintype d] [Fintype ι] [DecidableEq ι] (η lam : ℝ) (O : Finset ι)
    (r : ι → ℝ) (p : ℕ → d → ℝ) (Q : ℕ → Matrix d ι ℝ)
    (hQ : ∀ t, Q (t + 1) = itemStep η lam O r (p t) (Q t)) (τ : ℕ) :
    ∃ D : Matrix d ι ℝ, Q τ = (1 - η * lam) ^ τ • Q 0 + D ∧ D.rank ≤ τ :=
  ⟨_, itemIter_eq η lam O r p Q hQ τ, rank_dataPart_le η lam _ p τ⟩

/-- **arXiv 2401.03748, Sec. 4.2** (frozen basis): if `B` is frozen and `Q + B A` is trained in
`A`, the gradient is the projected one, `∇_A f(Q + B A) = Bᵀ ∇f(Q + B A)`, in the Frobenius inner
products.  This is the chain rule behind Algorithm 1. -/
theorem hasGradientAt_frozenBasis [Fintype d] [Fintype ι] [Fintype k] {f : Matrix d ι ℝ → ℝ}
    {G Q : Matrix d ι ℝ}
    (B : Matrix d k ℝ) (A : Matrix k ι ℝ) (hf : HasGradientAt f G (Q + B * A)) :
    HasGradientAt (fun A => f (Q + B * A)) (Bᵀ * G) A := by
  have h := hf.hasFDerivAt
  have hL : HasFDerivAt (fun A : Matrix k ι ℝ => Q + B * A)
      (LeanDLRA.Frobenius.leftMulCLM B) A :=
    ((LeanDLRA.Frobenius.leftMulCLM (n := ι) B).hasFDerivAt (x := A)).const_add Q
  have h2 := h.comp A hL
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h2.congr_fderiv ?_
  ext X
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
    LeanDLRA.Frobenius.leftMulCLM_apply]
  rw [LeanDLRA.Frobenius.inner_mul_left, Matrix.transpose_transpose]

/-- The restricted update `a = α Bᵀ p` of one item (arXiv 2401.03748, Appendix D): the coefficient
vector whose image `B a = α B Bᵀ p` is "the projection of the update of item `i` on the subspace
spanned by the columns of `B`".  See `colr_first_step`. -/
noncomputable def sketchUpdate [Fintype d] (α : ℝ) (B : Matrix d k ℝ) (p : d → ℝ) : k → ℝ := α •
    (Bᵀ *ᵥ p)

/-- **arXiv 2401.03748, Appendix D, first paragraph**: with frozen `B`, `A = 0` initially and no
regularization (`λ = 0`), the `i`-th column of `A` after one gradient step on the CoLR local loss
`A ↦ L_u(p, Q + B A)` is `sketchUpdate (η (m ∗ (r - r̂))_i) B p`.  So the `a_u` of Prop. D.1 is the
real local update, with `α_u` the scaled residual (the paper takes `η = 1` and suppresses `λ`). -/
theorem colr_first_step [Fintype d] [Fintype ι] [Fintype k] [DecidableEq ι] (η : ℝ)
    (O : Finset ι) (r : ι → ℝ) (p : d → ℝ) (Q : Matrix d ι ℝ)
    (B : Matrix d k ℝ) (i : ι) :
    (fun j => ((0 : Matrix k ι ℝ) - η • gradient
        (fun A => localLoss O (sqLoss r) 0 p (Q + B * A)) (0 : Matrix k ι ℝ)) j i) =
      sketchUpdate (η * residual O r Q p i) B p := by
  have h := hasGradientAt_frozenBasis (Q := Q) B (0 : Matrix k ι ℝ)
    (hasGradientAt_localLoss_sq O r 0 p (Q + B * 0))
  simp only [Matrix.mul_zero, add_zero] at h
  rw [h.gradient]
  ext j
  simp only [zero_smul, zero_sub, Matrix.mul_neg, smul_neg, neg_neg,
    Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vecMulVec_apply,
    smul_eq_mul, sketchUpdate, Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

variable {C : Type*} [AddCommMonoid C]

/-- **arXiv 2401.03748, Sec. 4.3**: with a shared frozen `B`, the aggregated update is
`∑_u w_u B A_u = B (∑_u w_u A_u)`, so the server only combines the `A_u`. -/
theorem colr_aggregate [Fintype k] (S : Finset U) (w : U → ℝ) (B : Matrix d k ℝ)
    (A : U → Matrix k ι ℝ) :
    ∑ u ∈ S, w u • (B * A u) = B * ∑ u ∈ S, w u • A u := by
  simp [Matrix.mul_sum, Matrix.mul_smul]

/-- **arXiv 2401.03748, Sec. 4.3**: the aggregate of updates with a shared `B ∈ ℝ^{d × r}` has rank
at most `r`, however many users take part. -/
theorem rank_colr_aggregate_le [Fintype k] [Fintype ι] (S : Finset U) (w : U → ℝ)
    (B : Matrix d k ℝ) (A : U → Matrix k ι ℝ) :
    (∑ u ∈ S, w u • (B * A u)).rank ≤ Fintype.card k := by
  classical
  rw [colr_aggregate]
  exact (Matrix.rank_mul_le_left _ _).trans B.rank_le_card_width

/-- **arXiv 2401.03748, Sec. 4.3**, in the library's vocabulary: for orthonormal `B`, the aggregate
stays in the range of the orthogonal projector `X ↦ B Bᵀ X`, the fixed subspace of the round. -/
theorem colr_aggregate_mem_range_leftProj [Fintype d] [Fintype k] [Fintype ι] [DecidableEq k]
    (S : Finset U) (w : U → ℝ)
    (B : Matrix d k ℝ) (hB : Bᵀ * B = 1) (A : U → Matrix k ι ℝ) :
    LeanDLRA.leftProj B (∑ u ∈ S, w u • (B * A u)) = ∑ u ∈ S, w u • (B * A u) := by
  rw [colr_aggregate, LeanDLRA.leftProj_apply, Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ, hB,
    Matrix.one_mul]

/-- **arXiv 2401.03748, Sec. 4.3** (compatibility with additive homomorphic encryption): if the
ciphertexts `c u` of a scheme decrypt additively (`dec : C →+ _`) to the weighted `w_u A_u`, then
the server only has to add ciphertexts, and each client recovers the aggregated update from the
decrypted sum and the public `B`.  No multiplication of two encrypted factors occurs.  This
formalizes the algebra only; it says nothing about the security of a scheme. -/
theorem colr_secure_aggregate [Fintype k] (S : Finset U) (w : U → ℝ) (B : Matrix d k ℝ)
    (A : U → Matrix k ι ℝ) (dec : C →+ Matrix k ι ℝ) (c : U → C)
    (hc : ∀ u ∈ S, dec (c u) = w u • A u) :
    B * dec (∑ u ∈ S, c u) = ∑ u ∈ S, w u • (B * A u) := by
  rw [map_sum, colr_aggregate, Finset.sum_congr rfl hc]

/-- **arXiv 2401.03748, Sec. 4.3, challenge (2)**: without a shared `B` the sum of low-rank updates
can have a larger rank: two rank-one updates can add up to rank two.  This is the contrast with
`rank_colr_aggregate_le`. -/
theorem exists_rank_sum_gt :
    ∃ (B : Fin 2 → Matrix (Fin 2) (Fin 1) ℝ) (A : Fin 2 → Matrix (Fin 1) (Fin 2) ℝ),
      (∀ u, (B u * A u).rank ≤ 1) ∧ (∑ u, B u * A u).rank = 2 := by
  refine ⟨![!![1; 0], !![0; 1]], ![!![1, 0], !![0, 1]], fun u => ?_, ?_⟩
  · exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  · have : (∑ u, (![!![1; 0], !![0; 1]] : Fin 2 → Matrix (Fin 2) (Fin 1) ℝ) u *
        (![!![1, 0], !![0, 1]] : Fin 2 → Matrix (Fin 1) (Fin 2) ℝ) u) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]
    rw [this, Matrix.rank_one]
    simp

end LocalTraining

section Net

open MeasureTheory Metric Module
open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Volumetric packing bound, same proof as `Besicovitch.card_le_of_separated`. -/
private theorem card_le_of_quarter_separated (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (h : ∀ c ∈ s, ∀ e ∈ s, c ≠ e → 1 / 4 ≤ ‖c - e‖) : s.card ≤ 9 ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1 / 8
  let ρ : ℝ := 9 / 8
  have ρpos : 0 < ρ := by norm_num [ρ]
  have δpos : 0 < δ := by norm_num [δ]
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have D : Set.Pairwise (s : Set E) (Function.onFun Disjoint fun c => ball (c : E) δ) := by
    rintro c hc e he hce
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := h c hc e he hce
    norm_num [δ]
    linarith
  have A_subset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    have := hs x hx
    rw [dist_zero_right]
    norm_num [δ, ρ]
    linarith
  have I : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ δpos]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono A_subset
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) ≤ (9 : ℝ) ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg δpos.le _)] at this
    have h9 : ρ ^ finrank ℝ E = 9 ^ finrank ℝ E * δ ^ finrank ℝ E := by
      rw [← mul_pow]
      norm_num [δ, ρ]
    rw [h9] at this
    exact le_of_mul_le_mul_right this (pow_pos δpos _)
  exact_mod_cast K

/-- Tool for **arXiv 2401.03748, Lemma D.2 (1)**, not stated in the paper: a `1/4`-net of the unit
sphere of a finite-dimensional normed space with at most `9 ^ dim` points, from Mathlib's maximal
separated sets and a volumetric packing bound. -/
theorem exists_quarter_net :
    ∃ N : Finset E, (∀ w ∈ N, ‖w‖ = 1) ∧ N.card ≤ 9 ^ finrank ℝ E ∧
      ∀ v, ‖v‖ = 1 → ∃ w ∈ N, ‖v - w‖ ≤ 1 / 4 := by
  classical
  let A : Set E := sphere 0 1
  let ε : ℝ≥0 := 1 / 4
  have hε : (ε : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp [ε]
  have hsep : ∀ s : Finset E, (s : Set E) ⊆ A → IsSeparated (ε : ℝ≥0∞) (s : Set E) →
      s.card ≤ 9 ^ finrank ℝ E := by
    intro s hsA hs
    refine card_le_of_quarter_separated s (fun c hc => ?_) (fun c hc e he hce => ?_)
    · have : c ∈ A := hsA hc
      exact (mem_sphere_zero_iff_norm.mp this).le
    · have h1 : (ε : ℝ≥0∞) < edist c e := hs hc he hce
      rw [edist_dist, hε, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)] at h1
      rw [← dist_eq_norm]
      exact h1.le
  have hle : packingNumber ε A ≤ ((9 ^ finrank ℝ E : ℕ) : ℕ∞) := by
    refine iSup_le fun C => iSup_le fun hCA => iSup_le fun hC => ?_
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨t, htC, htc⟩ := Set.exists_subset_encard_eq (s := C)
      (k := ((9 ^ finrank ℝ E + 1 : ℕ) : ℕ∞)) (by
        push_cast
        exact Order.add_one_le_of_lt (by exact_mod_cast hlt))
    have htf : t.Finite := Set.finite_of_encard_eq_coe htc
    have hC' : IsSeparated (ε : ℝ≥0∞) t := Set.Pairwise.mono htC hC
    have h1 := hsep htf.toFinset (by simpa using htC.trans hCA) (by simpa using hC')
    have h2 : htf.toFinset.card = 9 ^ finrank ℝ E + 1 := by
      have := htf.encard_eq_coe_toFinset_card
      rw [htc] at this
      exact_mod_cast this.symm
    omega
  have hpack : packingNumber ε A ≠ ⊤ := (lt_of_le_of_lt hle (ENat.natCast_lt_top _)).ne
  set M := maximalSeparatedSet ε A with hM
  have hMf : M.Finite := by
    apply Set.finite_of_encard_le_coe (k := 9 ^ finrank ℝ E)
    rw [hM, encard_maximalSeparatedSet hpack]
    exact hle
  have hcov := isCover_maximalSeparatedSet hpack
  refine ⟨hMf.toFinset, fun w hw => ?_, ?_, fun v hv => ?_⟩
  · have : w ∈ M := by simpa using hw
    exact mem_sphere_zero_iff_norm.mp (maximalSeparatedSet_subset this)
  · exact hsep _ (by simpa using maximalSeparatedSet_subset)
      (by simpa using isSeparated_maximalSeparatedSet)
  · obtain ⟨w, hw, hvw⟩ := hcov (x := v) (mem_sphere_zero_iff_norm.mpr hv)
    refine ⟨w, by simpa using hw, ?_⟩
    have h1 : edist v w ≤ (ε : ℝ≥0∞) := hvw
    rw [edist_dist, hε, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h1
    rwa [dist_eq_norm] at h1

end Net

section Absorb

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Tool for **arXiv 2401.03748, Lemma D.2 (1)**, not stated in the paper: absorption on a
`1/4`-net.  If `‖T w‖²` is within `M` of `c` on a `1/4`-net of the unit sphere, then
`‖T‖² ≤ c + 2 M`.  Working
with `T† T - c` rather than `T` means the net loses a factor on the fluctuation `M` only, so the
leading constant `c` is untouched; this gives the leading constant `1` in Lemma D.2 (1). -/
theorem opNorm_sq_le_of_net (T : E →L[ℝ] F) (N : Finset E) (hN1 : ∀ w ∈ N, ‖w‖ = 1)
    (hN : ∀ v, ‖v‖ = 1 → ∃ w ∈ N, ‖v - w‖ ≤ 1 / 4) (c M : ℝ) (hc : 0 ≤ c) (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ N, |‖T w‖ ^ 2 - c| ≤ M) : ‖T‖ ^ 2 ≤ c + 2 * M := by
  let A : E →L[ℝ] E :=
    _root_.ContinuousLinearMap.adjoint T ∘L T - c • ContinuousLinearMap.id ℝ E
  have hA : ∀ x y, ⟪A x, y⟫ = ⟪T x, T y⟫ - c * ⟪x, y⟫ := by
    intro x y
    simp only [A, sub_apply, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
      _root_.ContinuousLinearMap.adjoint_inner_left]
  have hsymm : ∀ x y, ⟪A x, y⟫ = ⟪A y, x⟫ := by
    intro x y
    rw [hA, hA, real_inner_comm (T x), real_inner_comm x]
  set K := M + ‖A‖ / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have step1 : ∀ v, ‖v‖ = 1 → |⟪A v, v⟫| ≤ K := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hN v hv
    have hw1 := hN1 w hw
    have e : ⟪A v, v⟫ = ⟪A w, w⟫ + ⟪A (v - w), v + w⟫ := by
      simp only [map_sub, inner_sub_left, inner_add_right]
      rw [hsymm w v]
      ring
    have e1 : ⟪A w, w⟫ = ‖T w‖ ^ 2 - c := by
      rw [hA, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hw1]
      ring
    have e2 : |⟪A (v - w), v + w⟫| ≤ ‖A‖ / 2 := by
      calc |⟪A (v - w), v + w⟫| ≤ ‖A (v - w)‖ * ‖v + w‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖v - w‖) * ‖v + w‖ := by gcongr; exact A.le_opNorm _
        _ ≤ (‖A‖ * (1 / 4)) * 2 := by
            have : ‖v + w‖ ≤ 2 := by
              calc ‖v + w‖ ≤ ‖v‖ + ‖w‖ := norm_add_le _ _
                _ = 2 := by rw [hv, hw1]; norm_num
            gcongr
        _ = ‖A‖ / 2 := by ring
    rw [e]
    calc |⟪A w, w⟫ + ⟪A (v - w), v + w⟫| ≤ |⟪A w, w⟫| + |⟪A (v - w), v + w⟫| := abs_add_le _ _
      _ ≤ M + ‖A‖ / 2 := add_le_add (by rw [e1]; exact hM w hw) e2
  have step2 : ∀ x, |⟪A x, x⟫| ≤ K * ‖x‖ ^ 2 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hu : ‖(‖x‖⁻¹ • x)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx']
    have h := step1 _ hu
    have e : ⟪A x, x⟫ = ‖x‖ ^ 2 * ⟪A (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫ := by
      simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial]
      field_simp
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖), mul_comm K]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
  have step3 : ∀ x y, 4 * |⟪A x, y⟫| ≤ 2 * K * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    intro x y
    have e : 4 * ⟪A x, y⟫ = ⟪A (x + y), x + y⟫ - ⟪A (x - y), x - y⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
      rw [hsymm y x]
      ring
    have p := parallelogram_law_with_norm ℝ x y
    calc 4 * |⟪A x, y⟫| = |4 * ⟪A x, y⟫| := by rw [abs_mul]; norm_num
      _ ≤ |⟪A (x + y), x + y⟫| + |⟪A (x - y), x - y⟫| := by rw [e]; exact abs_sub _ _
      _ ≤ K * ‖x + y‖ ^ 2 + K * ‖x - y‖ ^ 2 := add_le_add (step2 _) (step2 _)
      _ = 2 * K * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by nlinarith
  have step4 : ‖A‖ ≤ K := by
    refine A.opNorm_le_bound hK0 fun x => ?_
    by_cases hAx : A x = 0
    · rw [hAx, norm_zero]; positivity
    by_cases hx : x = 0
    · simp [hx]
    have hAx' : ‖A x‖ ≠ 0 := norm_ne_zero_iff.mpr hAx
    have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y : E := (‖x‖ / ‖A x‖) • A x
    have hy : ‖y‖ = ‖x‖ := by
      simp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    have hinner : ⟪A x, y⟫ = ‖x‖ * ‖A x‖ := by
      simp only [y]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have h := step3 x y
    rw [hinner, hy, abs_of_nonneg (by positivity)] at h
    have : ‖x‖ * (4 * ‖A x‖) ≤ ‖x‖ * (4 * (K * ‖x‖)) := by nlinarith
    have := le_of_mul_le_mul_left this hx'
    linarith
  have hA2 : ‖A‖ ≤ 2 * M := by
    have : ‖A‖ ≤ M + ‖A‖ / 2 := step4
    linarith
  have hsplit : _root_.ContinuousLinearMap.adjoint T ∘L T =
      A + c • ContinuousLinearMap.id ℝ E := by
    simp [A]
  have hnorm : ‖T‖ ^ 2 = ‖_root_.ContinuousLinearMap.adjoint T ∘L T‖ := by
    rw [_root_.ContinuousLinearMap.norm_adjoint_comp_self, sq]
  rw [hnorm, hsplit]
  calc ‖A + c • ContinuousLinearMap.id ℝ E‖ ≤ ‖A‖ + ‖c • ContinuousLinearMap.id ℝ E‖ :=
        norm_add_le _ _
    _ ≤ 2 * M + c := by
        refine add_le_add hA2 ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
        calc c * ‖ContinuousLinearMap.id ℝ E‖ ≤ c * 1 := by
              gcongr
              exact ContinuousLinearMap.norm_id_le
          _ = c := mul_one c
    _ = c + 2 * M := add_comm _ _

end Absorb

section Sketch

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable {Ω U d k : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The Euclidean norm `‖v‖₂` of a vector. -/
noncomputable def vnorm [Fintype d] (v : d → ℝ) : ℝ := √(v ⬝ᵥ v)

/-- The normalized vector `p̄ = p / ‖p‖₂` of arXiv 2401.03748, Appendix D (`0` for `p = 0`). -/
noncomputable def unitVec [Fintype d] (p : d → ℝ) : d → ℝ := (vnorm p)⁻¹ • p

/-- The average full-space update `Δ̄ = (1/|S|) ∑_{u ∈ S} α_u p_u` of one item, Appendix D of
arXiv 2401.03748; in `Δ_u = α_u p_u`, `α_u = r_{ui} - r̂_{ui}` is the residual of user `u`. -/
noncomputable def meanUpdate [Fintype d] (S : Finset U) (α : U → ℝ) (p : U → d → ℝ) : d → ℝ :=
  (S.card : ℝ)⁻¹ • ∑ u ∈ S, α u • p u

/-- The error vector `Δ̄ - (1/|S|) ∑_{u ∈ S} B_u a_u` of eq. (7) of arXiv 2401.03748, with
`a_u = α_u B_uᵀ p_u` as in the first line of the proof of Prop. D.1. -/
noncomputable def itemError [Fintype d] [Fintype k] (S : Finset U) (α : U → ℝ) (p : U → d → ℝ)
    (B : U → Matrix d k ℝ) : d → ℝ :=
  meanUpdate S α p - (S.card : ℝ)⁻¹ • ∑ u ∈ S, B u *ᵥ sketchUpdate (α u) (B u) (p u)

/-- The entrywise expectation `E[B Bᵀ]`. -/
noncomputable def secondMoment [Fintype k] (P : Measure Ω) (B : Ω → Matrix d k ℝ) :
    Matrix d d ℝ :=
  Matrix.of fun i j => ∫ ω, (B ω * (B ω)ᵀ) i j ∂P

/-- The sketching defect `(B Bᵀ - I) p`. -/
noncomputable def defect [Fintype d] [Fintype k] [DecidableEq d] (B : Matrix d k ℝ) (p : d → ℝ) :
    d → ℝ := (B * Bᵀ - 1) *ᵥ p

/-- The constant `C_p` of Prop. D.1, which the paper leaves undefined: the double sum
`∑_{u ≠ v} |α_u α_v| ‖p_u‖₂ ‖p_v‖₂`.  By `propD1_biasTerm_counterexample` it cannot be taken
independent of `|S|`. -/
noncomputable def crossConst [Fintype d] [DecidableEq U] (S : Finset U) (α : U → ℝ)
    (p : U → d → ℝ) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ S.erase u, |α u * α v| * vnorm (p u) * vnorm (p v)

/-- `v ⬝ᵥ v ≥ 0`. -/
private theorem dot_self_nonneg [Fintype d] (v : d → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simpa [dotProduct, sq] using Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (v i)

/-- `‖v‖₂² = v ⬝ᵥ v`. -/
private theorem vnorm_sq [Fintype d] (v : d → ℝ) : vnorm v ^ 2 = v ⬝ᵥ v :=
  Real.sq_sqrt (dot_self_nonneg v)

/-- `‖v‖₂ ≥ 0`. -/
private theorem vnorm_nonneg [Fintype d] (v : d → ℝ) : 0 ≤ vnorm v := Real.sqrt_nonneg _

/-- Cauchy-Schwarz for `vnorm`. -/
private theorem abs_dot_le [Fintype d] (v w : d → ℝ) : |v ⬝ᵥ w| ≤ vnorm v * vnorm w := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 v : EuclideanSpace ℝ d) (WithLp.toLp 2 w)
  have e1 : ∀ x : d → ℝ, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ d)‖ = vnorm x := by
    intro x
    rw [EuclideanSpace.norm_eq, vnorm]
    simp [dotProduct, sq]
  have e2 : ⟪(WithLp.toLp 2 v : EuclideanSpace ℝ d), WithLp.toLp 2 w⟫ = v ⬝ᵥ w := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rwa [e1, e1, e2] at h

/-- `vnorm` agrees with the norm of `EuclideanSpace`. -/
private theorem norm_toLp_sq {l : Type*} [Fintype l] (x : l → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ l)‖ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

/-- The spectral norm bounds `‖A x‖₂² ≤ ‖A‖² ‖x‖₂²`. -/
private theorem dot_mulVec_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (x : n → ℝ) : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ ‖A‖ ^ 2 * (x ⬝ᵥ x) := by
  have h : ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ m)‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ :=
    Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [mul_pow, norm_toLp_sq, norm_toLp_sq] at h2

/-- `‖B Bᵀ‖ = ‖B‖²` for the spectral norm. -/
private theorem norm_mul_transpose [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    (B : Matrix d k ℝ) : ‖B * Bᵀ‖ = ‖B‖ ^ 2 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Bᵀ
  have h2 := Matrix.l2_opNorm_conjTranspose B
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h h2
  rw [h, h2, sq]

/-- The error vector of eq. (7) is `-(1/|S|) ∑_u α_u (B_u B_uᵀ - I) p_u`, the first line of the
proof of Prop. D.1 (up to a sign that the paper drops). -/
private theorem itemError_eq [Fintype d] [Fintype k] [DecidableEq d] (S : Finset U) (α : U → ℝ)
    (p : U → d → ℝ) (B : U → Matrix d k ℝ) :
    itemError S α p B = (-(S.card : ℝ)⁻¹) • ∑ u ∈ S, α u • defect (B u) (p u) := by
  have h : ∀ u ∈ S, B u *ᵥ sketchUpdate (α u) (B u) (p u) =
      α u • p u + α u • defect (B u) (p u) := by
    intro u _
    simp only [sketchUpdate, defect, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, smul_sub]
    abel
  rw [itemError, meanUpdate, Finset.sum_congr rfl h, Finset.sum_add_distrib, smul_add, neg_smul]
  abel

/-- Bilinear expansion of a squared norm. -/
private theorem dot_sum_sum [Fintype d] (S : Finset U) (a : U → ℝ) (x : U → d → ℝ) (c : ℝ) :
    (c • ∑ u ∈ S, a u • x u) ⬝ᵥ (c • ∑ u ∈ S, a u • x u) =
      c ^ 2 * ∑ u ∈ S, ∑ v ∈ S, a u * a v * (x u ⬝ᵥ x v) := by
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, sum_dotProduct, dotProduct_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [dotProduct_comm (x v) (x u)]
  ring

/-- The bias/variance decomposition of Prop. D.1: for pairwise independent `X_u` with coordinates
in `L²`, the cross terms of `E‖c ∑_u a_u X_u‖²` factor into products of means. -/
private theorem integral_dot_sum [IsProbabilityMeasure P] [Fintype d] [DecidableEq U]
    (S : Finset U) (a : U → ℝ)
    (X : U → Ω → d → ℝ) (hX : ∀ u ∈ S, ∀ i, MemLp (fun ω => X u ω i) 2 P)
    (hind : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∀ i,
      IndepFun (fun ω => X u ω i) (fun ω => X v ω i) P) :
    (∀ c : ℝ, Integrable (fun ω => (c • ∑ u ∈ S, a u • X u ω) ⬝ᵥ (c • ∑ u ∈ S, a u • X u ω)) P) ∧
    ∀ c : ℝ, ∫ ω, (c • ∑ u ∈ S, a u • X u ω) ⬝ᵥ (c • ∑ u ∈ S, a u • X u ω) ∂P =
      c ^ 2 * (∑ u ∈ S, ∑ v ∈ S.erase u,
        a u * a v * ((fun i => ∫ ω, X u ω i ∂P) ⬝ᵥ (fun i => ∫ ω, X v ω i ∂P)) +
        ∑ u ∈ S, a u ^ 2 * ∫ ω, X u ω ⬝ᵥ X u ω ∂P) := by
  have hint : ∀ u ∈ S, ∀ v ∈ S, Integrable (fun ω => X u ω ⬝ᵥ X v ω) P := by
    intro u hu v hv
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hX u hu i).integrable_mul (hX v hv i)
  have hexp : ∀ (c : ℝ) ω, (c • ∑ u ∈ S, a u • X u ω) ⬝ᵥ (c • ∑ u ∈ S, a u • X u ω) =
      c ^ 2 * ∑ u ∈ S, ∑ v ∈ S, a u * a v * (X u ω ⬝ᵥ X v ω) := fun c ω => dot_sum_sum S a _ c
  refine ⟨fun c => ?_, fun c => ?_⟩
  · simp only [hexp]
    exact (integrable_finsetSum _ fun u hu => integrable_finsetSum _ fun v hv =>
      (hint u hu v hv).const_mul _).const_mul _
  simp only [hexp]
  rw [integral_const_mul, integral_finsetSum _ fun u hu => integrable_finsetSum _ fun v hv =>
    (hint u hu v hv).const_mul _]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [integral_finsetSum _ fun v hv => (hint u hu v hv).const_mul _,
    ← Finset.add_sum_erase S _ hu, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun v hv => ?_
    have hvS := Finset.mem_of_mem_erase hv
    have hne : u ≠ v := (Finset.ne_of_mem_erase hv).symm
    rw [integral_const_mul]
    congr 1
    simp only [dotProduct]
    rw [integral_finsetSum _ (f := fun i ω => X u ω i * X v ω i)
      fun i _ => (hX u hu i).integrable_mul (hX v hvS i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (hind u hu v hvS hne i).integral_fun_mul_eq_mul_integral
      (hX u hu i).aestronglyMeasurable (hX v hvS i).aestronglyMeasurable
  · rw [integral_const_mul]
    ring_nf

/-- The coordinates of the defect are polynomial, hence measurable, in `M`. -/
private theorem measurable_defect [Fintype d] [Fintype k] [DecidableEq d] (p : d → ℝ) (i : d) :
    Measurable (fun M : Matrix d k ℝ => defect M p i) := by
  simp only [defect, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun j _ => Measurable.mul ?_ measurable_const
  refine Measurable.sub_const ?_ _
  exact Finset.measurable_sum _ fun l _ => Matrix.measurable_apply.mul Matrix.measurable_apply

/-- The spectral norm is measurable. -/
private theorem measurable_opNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Measurable (fun M : Matrix m n ℝ => ‖M‖) := continuous_norm.measurable

/-- The pointwise estimate of the paper's last display:
`‖(B Bᵀ - I) p‖₂² ≤ (‖B‖⁴ + 1) ‖p‖₂²`. -/
private theorem defect_dot_le [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    (B : Matrix d k ℝ) (p : d → ℝ) :
    defect B p ⬝ᵥ defect B p ≤ (‖B‖ ^ 4 + 1) * (p ⬝ᵥ p) := by
  have h1 : defect B p = (B * Bᵀ) *ᵥ p - p := by simp [defect, Matrix.sub_mulVec]
  have h2 : p ⬝ᵥ ((B * Bᵀ) *ᵥ p) = (Bᵀ *ᵥ p) ⬝ᵥ (Bᵀ *ᵥ p) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have h3 := dot_mulVec_le (B * Bᵀ) p
  rw [norm_mul_transpose] at h3
  have h4 := dot_self_nonneg (Bᵀ *ᵥ p)
  rw [h1, sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm ((B * Bᵀ) *ᵥ p) p, h2]
  have h5 : (‖B‖ ^ 2) ^ 2 = ‖B‖ ^ 4 := by ring
  rw [h5] at h3
  nlinarith

/-- A fourth moment of `‖B‖` puts the coordinates of the defect in `L²`. -/
private theorem memLp_defect [IsProbabilityMeasure P] [Fintype d] [Fintype k] [DecidableEq d]
    [DecidableEq k] {B : Ω → Matrix d k ℝ} (hm : Measurable B)
    (h4 : Integrable (fun ω => ‖B ω‖ ^ 4) P) (p : d → ℝ) (i : d) :
    MemLp (fun ω => defect (B ω) p i) 2 P := by
  have hme : Measurable (fun ω => defect (B ω) p i) := (measurable_defect p i).comp hm
  rw [memLp_two_iff_integrable_sq hme.aestronglyMeasurable]
  refine Integrable.mono' (g := fun ω => (‖B ω‖ ^ 4 + 1) * (p ⬝ᵥ p))
    ((h4.add (integrable_const 1)).mul_const _) (hme.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  refine le_trans ?_ (defect_dot_le (B ω) p)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [dotProduct, ← sq]
  exact Finset.single_le_sum (f := fun j => defect (B ω) p j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- A fourth moment of `‖B‖` makes the entries of `B Bᵀ` integrable. -/
private theorem integrable_mul_transpose [IsProbabilityMeasure P] [Fintype d] [Fintype k]
    [DecidableEq k] {B : Ω → Matrix d k ℝ} (hm : Measurable B)
    (h4 : Integrable (fun ω => ‖B ω‖ ^ 4) P) (i j : d) :
    Integrable (fun ω => (B ω * (B ω)ᵀ) i j) P := by
  classical
  have h := (memLp_defect hm h4 (Pi.single j 1) i).integrable (by norm_num)
  have e : ∀ ω, (B ω * (B ω)ᵀ) i j = defect (B ω) (Pi.single j 1) i + (1 : Matrix d d ℝ) i j := by
    intro ω
    simp [defect]
  simp only [e]
  exact h.add (integrable_const _)

/-- The mean of the defect is `(E[B Bᵀ] - I) p`. -/
private theorem integral_defect [IsProbabilityMeasure P] [Fintype d] [Fintype k] [DecidableEq d]
    {B : Ω → Matrix d k ℝ} (hB : ∀ i j, Integrable (fun ω => (B ω * (B ω)ᵀ) i j) P)
    (p : d → ℝ) : (fun i => ∫ ω, defect (B ω) p i ∂P) = (secondMoment P B - 1) *ᵥ p := by
  ext i
  simp only [defect, Matrix.mulVec, dotProduct, Matrix.sub_apply, secondMoment, Matrix.of_apply]
  rw [integral_finsetSum _ (f := fun j ω => ((B ω * (B ω)ᵀ) i j - (1 : Matrix d d ℝ) i j) * p j)
    fun j _ => ((hB i j).sub (integrable_const _)).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_sub (hB i j) (integrable_const _)]
  simp

/-- Homogeneity of `vnorm`. -/
private theorem vnorm_smul [Fintype d] (c : ℝ) (v : d → ℝ) : vnorm (c • v) = |c| * vnorm v := by
  simp only [vnorm, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- From the bias of `p̄` to the bias of `p`. -/
private theorem vnorm_mulVec_defect_le [Fintype d] (M : Matrix d d ℝ) [DecidableEq d] (p : d → ℝ)
    {δ : ℝ} (h : vnorm (M *ᵥ unitVec p - unitVec p) ≤ √δ) :
    vnorm ((M - 1) *ᵥ p) ≤ vnorm p * √δ := by
  by_cases hp : vnorm p = 0
  · have : p ⬝ᵥ p = 0 := by rw [← vnorm_sq, hp]; simp
    have hp0 : p = 0 := dotProduct_self_eq_zero.mp this
    simp [hp0, vnorm]
  · have e : (M - 1) *ᵥ p = vnorm p • (M *ᵥ unitVec p - unitVec p) := by
      have e2 : p = vnorm p • unitVec p := by simp [unitVec, smul_smul, hp]
      nth_rw 1 [e2]
      simp [Matrix.sub_mulVec, Matrix.mulVec_smul, smul_sub]
    rw [e, vnorm_smul, abs_of_nonneg (vnorm_nonneg p)]
    exact mul_le_mul_of_nonneg_left h (vnorm_nonneg p)

/-- **arXiv 2401.03748, Proposition D.1, corrected.**  Let the `B_u` be pairwise independent random
`d × r` matrices, `‖B_u‖` the spectral norm, with `E‖B_u‖⁴ ≤ L²` and bias
`‖E[B_u B_uᵀ] p̄_u - p̄_u‖₂ ≤ √δ`.  Then the error of eq. (7) is finite and
`ε_i ≤ (1/|S|²) C_p δ + (1/|S|) max_u α_u² ‖p_u‖₂² (L² + 1)`.

Differences from the paper: its hypothesis (1) reads `E‖B‖² ≤ L_B`, under which the claim is false
(`propD1_counterexample`), while its proof uses `E‖B Bᵀ‖² = E‖B‖⁴ ≤ L_B²`, the hypothesis here.
`C_p` is undefined in the paper and is `crossConst` here; it cannot be independent of `|S|`
(`propD1_biasTerm_counterexample`).  The paper prints `α_u` where its proof has `α_u²`.  Pairwise
independence suffices, and the `B_u` need not be identically distributed.  In the paper's use,
`a_u = α_u B_uᵀ p_u` is one local gradient step, see `colr_first_step`. -/
theorem propD1 [IsProbabilityMeasure P] [Fintype d] [Fintype k] [DecidableEq k]
    [DecidableEq U] (S : Finset U) (hS : S.Nonempty) (α : U → ℝ) (p : U → d → ℝ)
    (B : U → Ω → Matrix d k ℝ) (L δ : ℝ) (hδ : 0 ≤ δ)
    (hmeas : ∀ u ∈ S, Measurable (B u))
    (hindep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → IndepFun (B u) (B v) P)
    (hint : ∀ u ∈ S, Integrable (fun ω => ‖B u ω‖ ^ 4) P)
    (hL : ∀ u ∈ S, ∫ ω, ‖B u ω‖ ^ 4 ∂P ≤ L ^ 2)
    (hbias : ∀ u ∈ S, vnorm (secondMoment P (B u) *ᵥ unitVec (p u) - unitVec (p u)) ≤ √δ) :
    Integrable (fun ω => vnorm (itemError S α p fun u => B u ω) ^ 2) P ∧
    ∫ ω, vnorm (itemError S α p fun u => B u ω) ^ 2 ∂P ≤
      (S.card : ℝ)⁻¹ ^ 2 * crossConst S α p * δ +
        (S.card : ℝ)⁻¹ * S.sup' hS (fun u => α u ^ 2 * vnorm (p u) ^ 2) * (L ^ 2 + 1) := by
  classical
  have hform : ∀ ω, vnorm (itemError S α p fun u => B u ω) ^ 2 =
      ((-(S.card : ℝ)⁻¹) • ∑ u ∈ S, α u • defect (B u ω) (p u)) ⬝ᵥ
        ((-(S.card : ℝ)⁻¹) • ∑ u ∈ S, α u • defect (B u ω) (p u)) := fun ω => by
    rw [vnorm_sq, itemError_eq]
  obtain ⟨hI, hE⟩ := integral_dot_sum (P := P) S α (fun u ω => defect (B u ω) (p u))
    (fun u hu i => memLp_defect (hmeas u hu) (hint u hu) (p u) i)
    (fun u hu v hv huv i => (hindep u hu v hv huv).comp (measurable_defect (p u) i)
      (measurable_defect (p v) i))
  simp only [hform]
  refine ⟨hI _, ?_⟩
  rw [hE]
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hm : ∀ u ∈ S, (fun i => ∫ ω, defect (B u ω) (p u) i ∂P) =
      (secondMoment P (B u) - 1) *ᵥ p u := fun u hu =>
    integral_defect (integrable_mul_transpose (hmeas u hu) (hint u hu)) (p u)
  have hb : ∀ u ∈ S, vnorm ((secondMoment P (B u) - 1) *ᵥ p u) ≤ vnorm (p u) * √δ := fun u hu =>
    vnorm_mulVec_defect_le _ _ (hbias u hu)
  have hcross : ∑ u ∈ S, ∑ v ∈ S.erase u, α u * α v *
      ((fun i => ∫ ω, defect (B u ω) (p u) i ∂P) ⬝ᵥ (fun i => ∫ ω, defect (B v ω) (p v) i ∂P)) ≤
      crossConst S α p * δ := by
    rw [crossConst, Finset.sum_mul]
    refine Finset.sum_le_sum fun u hu => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun v hv => ?_
    have hvS := Finset.mem_of_mem_erase hv
    rw [hm u hu, hm v hvS]
    set x := (secondMoment P (B u) - 1) *ᵥ p u
    set y := (secondMoment P (B v) - 1) *ᵥ p v
    have h1 : |x ⬝ᵥ y| ≤ vnorm (p u) * vnorm (p v) * δ := by
      calc |x ⬝ᵥ y| ≤ vnorm x * vnorm y := abs_dot_le x y
        _ ≤ (vnorm (p u) * √δ) * (vnorm (p v) * √δ) :=
            mul_le_mul (hb u hu) (hb v hvS) (vnorm_nonneg _)
              (mul_nonneg (vnorm_nonneg _) (Real.sqrt_nonneg _))
        _ = vnorm (p u) * vnorm (p v) * (√δ * √δ) := by ring
        _ = vnorm (p u) * vnorm (p v) * δ := by rw [Real.mul_self_sqrt hδ]
    calc α u * α v * (x ⬝ᵥ y) ≤ |α u * α v * (x ⬝ᵥ y)| := le_abs_self _
      _ = |α u * α v| * |x ⬝ᵥ y| := abs_mul _ _
      _ ≤ |α u * α v| * (vnorm (p u) * vnorm (p v) * δ) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |α u * α v| * vnorm (p u) * vnorm (p v) * δ := by ring
  set M := S.sup' hS (fun u => α u ^ 2 * vnorm (p u) ^ 2)
  have hdiag : ∑ u ∈ S, α u ^ 2 * ∫ ω, defect (B u ω) (p u) ⬝ᵥ defect (B u ω) (p u) ∂P ≤
      (S.card : ℝ) * (M * (L ^ 2 + 1)) := by
    have : ∀ u ∈ S, α u ^ 2 * ∫ ω, defect (B u ω) (p u) ⬝ᵥ defect (B u ω) (p u) ∂P ≤
        M * (L ^ 2 + 1) := by
      intro u hu
      have h1 : ∫ ω, defect (B u ω) (p u) ⬝ᵥ defect (B u ω) (p u) ∂P ≤
          (L ^ 2 + 1) * vnorm (p u) ^ 2 := by
        have hint2 : Integrable (fun ω => (‖B u ω‖ ^ 4 + 1) * (p u ⬝ᵥ p u)) P :=
          ((hint u hu).add (integrable_const 1)).mul_const _
        have hmono : ∫ ω, defect (B u ω) (p u) ⬝ᵥ defect (B u ω) (p u) ∂P ≤
            ∫ ω, (‖B u ω‖ ^ 4 + 1) * (p u ⬝ᵥ p u) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => dot_self_nonneg _) hint2
            (ae_of_all _ fun ω => defect_dot_le (B u ω) (p u))
        refine hmono.trans ?_
        rw [integral_mul_const, integral_add (hint u hu) (integrable_const 1), vnorm_sq]
        simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
        exact mul_le_mul_of_nonneg_right (by linarith [hL u hu]) (dot_self_nonneg _)
      have h2 : α u ^ 2 * vnorm (p u) ^ 2 ≤ M :=
        Finset.le_sup' (fun u => α u ^ 2 * vnorm (p u) ^ 2) hu
      have hL0 : 0 ≤ L ^ 2 + 1 := by positivity
      calc α u ^ 2 * ∫ ω, defect (B u ω) (p u) ⬝ᵥ defect (B u ω) (p u) ∂P
          ≤ α u ^ 2 * ((L ^ 2 + 1) * vnorm (p u) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (α u ^ 2 * vnorm (p u) ^ 2) * (L ^ 2 + 1) := by ring
        _ ≤ M * (L ^ 2 + 1) := mul_le_mul_of_nonneg_right h2 hL0
    calc _ ≤ ∑ _u ∈ S, M * (L ^ 2 + 1) := Finset.sum_le_sum this
      _ = _ := by simp
  have hc2 : (-(S.card : ℝ)⁻¹) ^ 2 = (S.card : ℝ)⁻¹ ^ 2 := by ring
  rw [hc2]
  calc (S.card : ℝ)⁻¹ ^ 2 * (_ + _)
      ≤ (S.card : ℝ)⁻¹ ^ 2 * (crossConst S α p * δ + (S.card : ℝ) * (M * (L ^ 2 + 1))) :=
        mul_le_mul_of_nonneg_left (add_le_add hcross hdiag) (by positivity)
    _ = _ := by field_simp

/-- The scalar sketch of `propD1_counterexample`: `B = 2` on one of four equally likely points and
`B = 0` on the other three. -/
noncomputable def twoPointSketch (ω : Fin 4) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.diagonal fun _ => if ω = 0 then 2 else 0

/-- The uniform measure on four points is a probability measure. -/
private theorem isProbabilityMeasure_unifFour :
    IsProbabilityMeasure ((4⁻¹ : ℝ≥0∞) • Measure.count : Measure (Fin 4)) := by
  constructor
  simp only [_root_.smul_apply, smul_eq_mul, Measure.count_univ]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Expectation under the uniform measure on four points. -/
private theorem integral_unifFour (f : Fin 4 → ℝ) :
    ∫ ω, f ω ∂((4⁻¹ : ℝ≥0∞) • Measure.count : Measure (Fin 4)) =
      (f 0 + f 1 + f 2 + f 3) / 4 := by
  rw [integral_smul_measure, integral_count, Fin.sum_univ_four]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- Spectral norm of `twoPointSketch`. -/
private theorem norm_twoPointSketch (ω : Fin 4) : ‖twoPointSketch ω‖ = if ω = 0 then 2 else 0 := by
  rw [twoPointSketch, Matrix.l2_opNorm_diagonal, pi_norm_const]
  split_ifs <;> simp

/-- **arXiv 2401.03748, Proposition D.1 is false as printed.**  Take one user, `d = r = 1`, `α = 1`,
`p = 1` and `B = 2` with probability `1/4`, `B = 0` otherwise.  Hypothesis (1), `E‖B‖² ≤ L_B`, holds
with `L_B = 1` and hypothesis (2) with `δ_B = 0`, since `E[B Bᵀ] = 1`.  But the error of eq. (7) is
`3`, above the claimed `C_p² · 0 + 1 · (1² + 1) = 2` for every value of `C_p`.  With `α = p = 1` it
makes no difference whether the bound is read with `α_u` or `α_u²`.  The corrected hypothesis of
`propD1` holds here with `L = 2`, in agreement with `3 ≤ 5`. -/
theorem propD1_counterexample :
    ∃ (P : Measure (Fin 4)) (_ : IsProbabilityMeasure P)
      (B : Unit → Fin 4 → Matrix (Fin 1) (Fin 1) ℝ) (α : Unit → ℝ) (p : Unit → Fin 1 → ℝ)
      (hS : ({()} : Finset Unit).Nonempty),
      (∀ u, Measurable (B u)) ∧
      (∀ u, ∫ ω, ‖B u ω‖ ^ 2 ∂P ≤ 1) ∧
      (∀ u, vnorm (secondMoment P (B u) *ᵥ unitVec (p u) - unitVec (p u)) ≤ √0) ∧
      (∀ u, ∫ ω, ‖B u ω‖ ^ 4 ∂P ≤ 2 ^ 2) ∧
      ∀ C : ℝ, (({()} : Finset Unit).card : ℝ)⁻¹ * C ^ 2 * 0 +
          (({()} : Finset Unit).card : ℝ)⁻¹ *
            ({()} : Finset Unit).sup' hS (fun u => α u ^ 2 * vnorm (p u) ^ 2) * (1 ^ 2 + 1) <
        ∫ ω, vnorm (itemError {()} α p fun u => B u ω) ^ 2 ∂P := by
  have hP := isProbabilityMeasure_unifFour
  have hv1 : vnorm (fun _ : Fin 1 => (1 : ℝ)) = 1 := by simp [vnorm, dotProduct]
  have hsm : secondMoment ((4⁻¹ : ℝ≥0∞) • Measure.count) twoPointSketch = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [secondMoment, Matrix.of_apply]
    rw [integral_unifFour]
    simp [twoPointSketch, Matrix.mul_apply]
    norm_num
  refine ⟨(4⁻¹ : ℝ≥0∞) • Measure.count, hP, fun _ => twoPointSketch, fun _ => 1,
    fun _ _ => 1, by simp, fun _ => measurable_of_finite _, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun C => ?_⟩
  · rw [integral_unifFour]
    simp [norm_twoPointSketch]
    norm_num
  · simp [hsm]
    simp [vnorm, dotProduct]
  · rw [integral_unifFour]
    simp [norm_twoPointSketch]
    norm_num
  · have he : ∀ ω, vnorm (itemError {()} (fun _ => (1 : ℝ)) (fun _ _ => 1)
        fun _ => twoPointSketch ω) ^ 2 = ((if ω = 0 then (4 : ℝ) else 0) - 1) ^ 2 := by
      intro ω
      rw [vnorm_sq, itemError_eq]
      by_cases h : ω = 0
      · simp [defect, dotProduct, Matrix.mulVec, twoPointSketch, h, sq]
        norm_num
      · simp [defect, dotProduct, Matrix.mulVec, twoPointSketch, h, sq]
    simp only [he]
    rw [integral_unifFour]
    simp [hv1]
    norm_num

/-- **arXiv 2401.03748, Proposition D.1: the bias term cannot scale like `1/|S|`.**  Eq. (11) of the
paper bounds one cross term and loses the `|S| (|S| - 1)` terms of the double sum, so its `(1/|S|)
C_p² δ_B` fails for every `C_p` independent of `|S|`: for every `C` there is a number `n` of users
such that, with `α_u = 1`, `p_u = 1` and the deterministic `B_u = √2`, all hypotheses hold with `δ =
1` and `L_B = 2` (even the corrected `E‖B‖⁴ ≤ L_B²`), and the error `1` exceeds `(1/n) C² δ + (1/n)
max_u α_u² ‖p_u‖₂² (L_B² + 1)`.  A fortiori the form `(1/|S|²) C_p δ_B` fails for every constant
`C_p`, which is why `propD1` has `crossConst`. -/
theorem propD1_biasTerm_counterexample (C : ℝ) :
    ∃ (n : ℕ) (hS : (Finset.range n).Nonempty)
      (B : ℕ → Unit → Matrix (Fin 1) (Fin 1) ℝ) (α : ℕ → ℝ) (p : ℕ → Fin 1 → ℝ),
      (∀ u, Measurable (B u)) ∧
      (∀ u v, IndepFun (B u) (B v) (Measure.dirac ())) ∧
      (∀ u, ∫ ω, ‖B u ω‖ ^ 2 ∂(Measure.dirac ()) ≤ 2) ∧
      (∀ u, ∫ ω, ‖B u ω‖ ^ 4 ∂(Measure.dirac ()) ≤ 2 ^ 2) ∧
      (∀ u, vnorm (secondMoment (Measure.dirac ()) (B u) *ᵥ unitVec (p u) - unitVec (p u)) ≤ √1) ∧
      (∀ u, |α u| * vnorm (p u) = 1) ∧
      ((n : ℝ)⁻¹ * C ^ 2 * 1 + (n : ℝ)⁻¹ *
          (Finset.range n).sup' hS (fun u => α u ^ 2 * vnorm (p u) ^ 2) * (2 ^ 2 + 1) <
        ∫ ω, vnorm (itemError (Finset.range n) α p fun u => B u ω) ^ 2 ∂(Measure.dirac ())) := by
  let b : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ => √2
  have hb : ‖b‖ = √2 := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_const, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hb2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb4 : (√2 : ℝ) ^ 4 = 2 ^ 2 := by
    calc (√2 : ℝ) ^ 4 = ((√2 : ℝ) ^ 2) ^ 2 := by ring
      _ = 2 ^ 2 := by rw [hb2]
  have hbb : ∀ i j : Fin 1, (b * bᵀ) i j = 2 := by
    intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [b, h2]
  have hv1 : vnorm (fun _ : Fin 1 => (1 : ℝ)) = 1 := by simp [vnorm, dotProduct]
  have hunit : unitVec (fun _ : Fin 1 => (1 : ℝ)) = fun _ => 1 := by simp [unitVec, hv1]
  have hdef : defect b (fun _ => 1) = fun _ => 1 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [defect, Matrix.mulVec, dotProduct, Matrix.sub_apply, hbb]
    norm_num
  have hcpos : (0 : ℝ) ≤ C ^ 2 + 5 := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (C ^ 2 + 5)
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := by linarith
    exact_mod_cast this
  refine ⟨m, ⟨0, Finset.mem_range.mpr hm0⟩, fun _ _ => b, fun _ => 1, fun _ _ => 1,
    fun _ => measurable_const, fun _ _ => indepFun_const_left _ _, fun _ => ?_, fun _ => ?_,
    fun _ => ?_, fun _ => ?_, ?_⟩
  · simp [hb, hb2]
  · simp [hb, hb4]
  · have hsm : secondMoment (Measure.dirac ()) (fun _ : Unit => b) *ᵥ (fun _ : Fin 1 => (1 : ℝ)) -
        (fun _ => 1) = fun _ => 1 := by
      ext i
      simp [secondMoment, Matrix.mulVec, dotProduct, hbb]
      norm_num
    rw [hunit, hsm, hv1]
    simp
  · simp [hv1]
  · have he : vnorm (itemError (Finset.range m) (fun _ => (1 : ℝ)) (fun _ _ => 1)
        fun _ => b) ^ 2 = 1 := by
      rw [vnorm_sq, itemError_eq]
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
      simp [hdef, dotProduct, hm']
    have hsup : (Finset.range m).sup' ⟨0, Finset.mem_range.mpr hm0⟩
        (fun _ => (1 : ℝ) ^ 2 * vnorm (fun _ : Fin 1 => (1 : ℝ)) ^ 2) = 1 := by
      simp only [hv1, one_pow, one_mul]
      exact le_antisymm (Finset.sup'_le _ _ fun _ _ => le_rfl)
        (Finset.le_sup' (fun _ => (1 : ℝ)) (Finset.mem_range.mpr hm0))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, he, hsup]
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
    field_simp
    norm_num
    linarith

/-- `B` is a random `m × n` matrix with i.i.d. `N(0, s)` entries, `s` being the variance: each entry
has law `gaussianReal 0 s` and the family of all entries is independent.  With `s = 1/r` this is the
distribution of Lemma D.2 and Theorem D.3 of arXiv 2401.03748.  Instances exist by
`exists_gaussianSketch_family`. -/
structure IsGaussianSketch {m n : Type*} (P : Measure Ω) (B : Ω → Matrix m n ℝ) (s : ℝ≥0) :
    Prop where
  measurable : Measurable B
  hasLaw : ∀ i j, HasLaw (fun ω => B ω i j) (gaussianReal 0 s) P
  indep : iIndepFun (fun (a : m × n) ω => B ω a.1 a.2) P

/-- The moments `E X = 0`, `E X² = s`, `E X³ = 0`, `E X⁴ = 3 s²` of `X ~ N(0, s)`, as iterated
derivatives of the moment generating function at `0`. -/
private theorem gaussian_moments (s : ℝ≥0) :
    ∫ x, x ^ 1 ∂gaussianReal 0 s = (0 : ℝ) ∧ ∫ x, x ^ 2 ∂gaussianReal 0 s = (s : ℝ) ∧
      ∫ x, x ^ 3 ∂gaussianReal 0 s = (0 : ℝ) ∧
      ∫ x, x ^ 4 ∂gaussianReal 0 s = 3 * (s : ℝ) ^ 2 := by
  set v : ℝ := (s : ℝ)
  let g : ℝ → ℝ := fun t => Real.exp ((s : ℝ) * t ^ 2 / 2)
  have hg : ∀ t, HasDerivAt g (g t * (v * t)) t := by
    intro t
    have : HasDerivAt (fun t : ℝ => (s : ℝ) * t ^ 2 / 2) (v * t) t := by
      have := ((hasDerivAt_id t).pow 2).const_mul (s : ℝ) |>.div_const 2
      refine this.congr_deriv ?_
      simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, v]
      ring
    exact this.exp
  have hd : ∀ (q q' : ℝ → ℝ) (t : ℝ), HasDerivAt q (q' t) t →
      HasDerivAt (fun t => q t * g t) ((q' t + q t * (v * t)) * g t) t := by
    intro q q' t hq
    refine (hq.mul (hg t)).congr_deriv ?_
    ring
  have hmgf : mgf (fun x => x) (gaussianReal 0 s) = g := by
    rw [mgf_fun_id_gaussianReal]
    ext t
    simp [g]
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x => x) (gaussianReal 0 s)) := by
    simp
  have hM : ∀ k, ∫ x, x ^ k ∂gaussianReal 0 s = iteratedDeriv k g 0 := by
    intro k
    rw [← hmgf, iteratedDeriv_mgf_zero h0]
    rfl
  have hg0 : g 0 = 1 := by simp [g]
  have I1 : iteratedDeriv 1 g = fun t => (v * t) * g t := by
    rw [iteratedDeriv_one]
    ext t
    rw [(hg t).deriv]
    ring
  have I2 : iteratedDeriv 2 g = fun t => (v + v ^ 2 * t ^ 2) * g t := by
    rw [iteratedDeriv_succ, I1]
    ext t
    have := hd (fun t => v * t) (fun _ => v) t
      ((hasDerivAt_id t).const_mul v |>.congr_deriv (by simp))
    rw [this.deriv]
    ring
  have I3 : iteratedDeriv 3 g = fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * g t := by
    rw [iteratedDeriv_succ, I2]
    ext t
    have h1 : HasDerivAt (fun t : ℝ => v + v ^ 2 * t ^ 2) (2 * v ^ 2 * t) t := by
      have := (((hasDerivAt_id t).pow 2).const_mul (v ^ 2)).const_add v
      refine this.congr_deriv ?_
      simp
      ring
    rw [(hd _ (fun t => 2 * v ^ 2 * t) t h1).deriv]
    ring
  have I4 : iteratedDeriv 4 g = fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * g t := by
    rw [iteratedDeriv_succ, I3]
    ext t
    have h1 : HasDerivAt (fun t : ℝ => 3 * v ^ 2 * t + v ^ 3 * t ^ 3)
        (3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t := by
      have := ((hasDerivAt_id t).const_mul (3 * v ^ 2)).add
        (((hasDerivAt_id t).pow 3).const_mul (v ^ 3))
      refine this.congr_deriv ?_
      simp
      ring
    rw [(hd _ (fun t => 3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t h1).deriv]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hM, I1]; simp
  · rw [hM, I2]; simp [hg0]
  · rw [hM, I3]; simp
  · rw [hM, I4]; simp [hg0]

/-- `x⁴` is integrable under `N(0, s)`. -/
private theorem gaussian_integrable_pow_four (s : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 s) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := s) ((4 : ℕ) : ℝ≥0∞)
    (by simp)).integrable_norm_pow (by norm_num)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [id, Real.norm_eq_abs]
  exact Even.pow_abs (by decide) x

/-- Moments only depend on the law. -/
private theorem integral_pow_law {Y : Ω → ℝ} {s : ℝ≥0} (hY : HasLaw Y (gaussianReal 0 s) P)
    (k : ℕ) : ∫ ω, Y ω ^ k ∂P = ∫ x, x ^ k ∂gaussianReal 0 s :=
  hY.integral_comp (f := fun x : ℝ => x ^ k) (measurable_id.pow_const k).aestronglyMeasurable

section Family

variable {ι : Type*} {X : ι → Ω → ℝ} {s : ℝ≥0}

/-- Independent variables with the same Gaussian law: moments of monomials factor. -/
private theorem integral_prod_pow [Fintype ι] (hX : ∀ i, HasLaw (X i) (gaussianReal 0 s) P)
    (hI : iIndepFun X P) (n : ι → ℕ) :
    ∫ ω, ∏ i, X i ω ^ n i ∂P = ∏ i, ∫ x, x ^ n i ∂gaussianReal 0 s := by
  have h := hI.integral_fun_prod_comp (f := fun i x => x ^ n i) (fun i => (hX i).aemeasurable)
    (fun i => (measurable_id.pow_const _).aestronglyMeasurable)
  rw [h]
  exact Finset.prod_congr rfl fun i _ => integral_pow_law (hX i) (n i)

/-- How often `i` occurs among `a, b, c, e`. -/
private def cnt4 [DecidableEq ι] (a b c e i : ι) : ℕ :=
  (if i = a then 1 else 0) + (if i = b then 1 else 0) + (if i = c then 1 else 0) +
    (if i = e then 1 else 0)

/-- A monomial of degree four written as a product over the index set. -/
private theorem prod_cnt4 [Fintype ι] [DecidableEq ι] (x : ι → ℝ) (a b c e : ι) :
    ∏ i, x i ^ cnt4 a b c e i = x a * x b * x c * x e := by
  simp only [cnt4, pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq', Finset.mem_univ, ite_true]

/-- Isserlis' formula for independent `N(0, s)` variables:
`E[X_a X_b X_c X_e] = s² (δ_ab δ_ce + δ_ac δ_be + δ_ae δ_bc)`. -/
private theorem moment_four [Finite ι] [DecidableEq ι]
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 s) P) (hI : iIndepFun X P) (a b c e : ι) :
    ∫ ω, X a ω * X b ω * X c ω * X e ω ∂P = (s : ℝ) ^ 2 *
      ((if a = b then 1 else 0) * (if c = e then 1 else 0) +
       (if a = c then 1 else 0) * (if b = e then 1 else 0) +
       (if a = e then 1 else 0) * (if b = c then 1 else 0)) := by
  have := Fintype.ofFinite ι
  obtain ⟨M1, M2, M3, M4⟩ := gaussian_moments s
  have M0 : ∫ x, x ^ 0 ∂gaussianReal 0 s = (1 : ℝ) := by simp
  have key : ∫ ω, X a ω * X b ω * X c ω * X e ω ∂P =
      ∏ i, ∫ x, x ^ cnt4 a b c e i ∂gaussianReal 0 s := by
    rw [← integral_prod_pow hX hI]
    simp only [prod_cnt4]
  rw [key]
  by_cases hab : a = b
  · subst hab
    by_cases hce : c = e
    · subst hce
      by_cases hac : a = c
      · subst hac
        rw [Finset.prod_eq_single a]
        · simp [cnt4, M4]; ring
        · intro i _ hi
          simp [cnt4, hi]
        · simp
      · rw [Finset.prod_eq_mul a c hac]
        · have h1 : cnt4 a a c c a = 2 := by simp [cnt4, hac]
          have h2 : cnt4 a a c c c = 2 := by simp [cnt4, Ne.symm hac]
          rw [h1, h2, M2]
          simp [hac, sq]
        · rintro i _ ⟨h1, h2⟩
          simp [cnt4, h1, h2]
        · simp
        · simp
    · by_cases hac : a = c
      · subst hac
        rw [Finset.prod_eq_zero (Finset.mem_univ e)]
        · simp [hce]
        · have : cnt4 a a a e e = 1 := by simp [cnt4, Ne.symm hce]
          rw [this, M1]
      · rw [Finset.prod_eq_zero (Finset.mem_univ c)]
        · simp [hce, hac]
        · have : cnt4 a a c e c = 1 := by simp [cnt4, Ne.symm hac, hce]
          rw [this, M1]
  · by_cases hac : a = c
    · subst hac
      by_cases hbe : b = e
      · subst hbe
        rw [Finset.prod_eq_mul a b hab]
        · have h1 : cnt4 a b a b a = 2 := by simp [cnt4, hab]
          have h2 : cnt4 a b a b b = 2 := by simp [cnt4, Ne.symm hab]
          rw [h1, h2, M2]
          simp [hab, sq]
        · rintro i _ ⟨h1, h2⟩
          simp [cnt4, h1, h2]
        · simp
        · simp
      · rw [Finset.prod_eq_zero (Finset.mem_univ b)]
        · simp [hab, hbe, Ne.symm hab]
        · have : cnt4 a b a e b = 1 := by simp [cnt4, Ne.symm hab, hbe]
          rw [this, M1]
    · by_cases hae : a = e
      · subst hae
        by_cases hbc : b = c
        · subst hbc
          rw [Finset.prod_eq_mul a b hab]
          · have h1 : cnt4 a b b a a = 2 := by simp [cnt4, hab]
            have h2 : cnt4 a b b a b = 2 := by simp [cnt4, Ne.symm hab]
            rw [h1, h2, M2]
            simp [hab, sq]
          · rintro i _ ⟨h1, h2⟩
            simp [cnt4, h1, h2]
          · simp
          · simp
        · rw [Finset.prod_eq_zero (Finset.mem_univ b)]
          · simp [hab, hbc, hac, Ne.symm hab]
          · have : cnt4 a b c a b = 1 := by simp [cnt4, Ne.symm hab, hbc]
            rw [this, M1]
      · rw [Finset.prod_eq_zero (Finset.mem_univ a)]
        · simp [hab, hac, hae]
        · have : cnt4 a b c e a = 1 := by simp [cnt4, hab, hac, hae]
          rw [this, M1]

/-- Second moments of independent `N(0, s)` variables: `E[X_a X_b] = s δ_ab`. -/
private theorem moment_two [DecidableEq ι] (hX : ∀ i, HasLaw (X i) (gaussianReal 0 s) P)
    (hI : iIndepFun X P) (a b : ι) : ∫ ω, X a ω * X b ω ∂P = if a = b then (s : ℝ) else 0 := by
  obtain ⟨M1, M2, -, -⟩ := gaussian_moments s
  by_cases hab : a = b
  · subst hab
    simp only [← sq, integral_pow_law (hX a) 2, M2, ite_true]
  · have h := (hI.indepFun hab).integral_fun_mul_eq_mul_integral
      (hX a).aemeasurable.aestronglyMeasurable (hX b).aemeasurable.aestronglyMeasurable
    have h0 : ∀ i, ∫ ω, X i ω ∂P = 0 := by
      intro i
      have := integral_pow_law (hX i) 1
      simp only [pow_one] at this M1
      exact this.trans M1
    simp [h, h0, hab]

/-- `X⁴` is integrable. -/
private theorem integrable_pow_four (hX : ∀ i, HasLaw (X i) (gaussianReal 0 s) P) (a : ι) :
    Integrable (fun ω => X a ω ^ 4) P :=
  (hX a).integrable_comp (gaussian_integrable_pow_four s)

/-- A monomial of degree four is bounded by a sum of fourth powers. -/
private theorem abs_mul_four_le (a b c e : ℝ) :
    |a * b * c * e| ≤ a ^ 4 + b ^ 4 + c ^ 4 + e ^ 4 := by
  have h1 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩
  have h2 : |c * e| ≤ (c ^ 2 + e ^ 2) / 2 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (c + e)], by nlinarith [sq_nonneg (c - e)]⟩
  have h3 : |a * b * c * e| = |a * b| * |c * e| := by rw [mul_assoc (a * b), abs_mul]
  rw [h3]
  have h4 : |a * b| * |c * e| ≤ (a ^ 2 + b ^ 2) / 2 * ((c ^ 2 + e ^ 2) / 2) :=
    mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - e ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (b ^ 2 - e ^ 2), sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (c ^ 2),
    sq_nonneg (e ^ 2)]

/-- Monomials of degree four are integrable. -/
private theorem integrable_four (hX : ∀ i, HasLaw (X i) (gaussianReal 0 s) P) (a b c e : ι) :
    Integrable (fun ω => X a ω * X b ω * X c ω * X e ω) P := by
  refine Integrable.mono' (g := fun ω => X a ω ^ 4 + X b ω ^ 4 + X c ω ^ 4 + X e ω ^ 4)
    (((integrable_pow_four hX a).add (integrable_pow_four hX b)).add
      (integrable_pow_four hX c) |>.add (integrable_pow_four hX e)) ?_
    (ae_of_all _ fun ω => abs_mul_four_le _ _ _ _)
  have m : ∀ i, AEStronglyMeasurable (X i) P := fun i => (hX i).aemeasurable.aestronglyMeasurable
  exact (((m a).mul (m b)).mul (m c)).mul (m e)

/-- Products of two entries are in `L²`. -/
private theorem memLp_pair (hX : ∀ i, HasLaw (X i) (gaussianReal 0 s) P) (a b : ι) :
    MemLp (fun ω => X a ω * X b ω) 2 P := by
  have m : ∀ i, AEStronglyMeasurable (X i) P := fun i => (hX i).aemeasurable.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq (f := fun ω => X a ω * X b ω) ((m a).mul (m b))).2 ?_
  refine (integrable_four hX a b a b).congr (ae_of_all _ fun ω => ?_)
  simp only
  ring

end Family

section Moments

variable {m n : Type*} {B : Ω → Matrix m n ℝ} {s : ℝ≥0}

/-- `IsGaussianSketch.hasLaw` indexed by pairs. -/
private theorem IsGaussianSketch.hasLaw' (hB : IsGaussianSketch P B s) (a : m × n) :
    HasLaw (fun ω => B ω a.1 a.2) (gaussianReal 0 s) P := hB.hasLaw a.1 a.2

/-- Isserlis' formula for the entries that occur in `(B Bᵀ v)_i²`. -/
private theorem IsGaussianSketch.quad_moment [Finite m] [Finite n] [DecidableEq m] [DecidableEq n]
    (hB : IsGaussianSketch P B s) (i j j' : m) (k k' : n) :
    ∫ ω, B ω i k * B ω j k * B ω i k' * B ω j' k' ∂P = (s : ℝ) ^ 2 *
      ((if i = j then 1 else 0) * (if i = j' then 1 else 0) +
       (if k = k' then 1 else 0) * (if j = j' then 1 else 0) +
       (if i = j' then 1 else 0) * (if j = i then 1 else 0) * (if k = k' then 1 else 0)) := by
  have h := moment_four (X := fun (a : m × n) ω => B ω a.1 a.2) hB.hasLaw' hB.indep
    (i, k) (j, k) (i, k') (j', k')
  simp only at h
  rw [h]
  by_cases hk : k = k'
  · subst hk; simp
  · simp [hk]

/-- The index sum of the three Isserlis pairings, `r² v_i² + r ‖v‖² + r v_i²`. -/
private theorem isserlis_sum [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (v : m → ℝ)
    (i : m) :
    ∑ t : m × n, ∑ t' : m × n, v t.1 * v t'.1 *
      ((if i = t.1 then 1 else 0) * (if i = t'.1 then 1 else 0) +
       (if t.2 = t'.2 then 1 else 0) * (if t.1 = t'.1 then 1 else 0) +
       (if i = t'.1 then 1 else 0) * (if t.1 = i then 1 else 0) * (if t.2 = t'.2 then 1 else 0)) =
      (Fintype.card n : ℝ) ^ 2 * v i ^ 2 + (Fintype.card n : ℝ) * (v ⬝ᵥ v) +
        (Fintype.card n : ℝ) * v i ^ 2 := by
  simp only [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp [mul_ite, sq]
      ring
    · simp [mul_ite, dotProduct, Finset.mul_sum]
  · simp [mul_ite, sq]

/-- `(M Mᵀ v)_i` as a sum over pairs `(j, k)`. -/
private theorem mulVec_eq_sum [Fintype m] [Fintype n] (M : Matrix m n ℝ) (v : m → ℝ) (i : m) :
    ((M * Mᵀ) *ᵥ v) i = ∑ t : m × n, v t.1 * (M i t.2 * M t.1 t.2) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- Products of two entries of a Gaussian sketch are in `L²`. -/
private theorem IsGaussianSketch.memLp_pair (hB : IsGaussianSketch P B s) (a b : m × n) :
    MemLp (fun ω => B ω a.1 a.2 * B ω b.1 b.2) 2 P :=
  _root_.LeanDLRA.Literature.P2401_03748.memLp_pair
    (X := fun (a : m × n) ω => B ω a.1 a.2) hB.hasLaw' a b

/-- `E (B Bᵀ v)_i = r s v_i`. -/
private theorem IsGaussianSketch.integral_mulVec [Fintype m] [Fintype n]
    (hB : IsGaussianSketch P B s) (v : m → ℝ) (i : m) :
    ∫ ω, ((B ω * (B ω)ᵀ) *ᵥ v) i ∂P = (Fintype.card n : ℝ) * s * v i := by
  classical
  have := hB.indep.isProbabilityMeasure
  simp only [mulVec_eq_sum]
  rw [integral_finsetSum _ fun t _ =>
    ((hB.memLp_pair (i, t.2) t).integrable (by norm_num)).const_mul _]
  have h : ∀ t : m × n, ∫ ω, v t.1 * (B ω i t.2 * B ω t.1 t.2) ∂P =
      v t.1 * (if (i, t.2) = t then (s : ℝ) else 0) := by
    intro t
    rw [integral_const_mul]
    congr 1
    exact moment_two (X := fun (a : m × n) ω => B ω a.1 a.2) hB.hasLaw' hB.indep (i, t.2) t
  simp only [h, Fintype.sum_prod_type]
  simp [mul_ite]
  ring

/-- `E (B Bᵀ v)_i² = s² (r² v_i² + r ‖v‖² + r v_i²)`. -/
private theorem IsGaussianSketch.integral_mulVec_sq [Fintype m] [Fintype n]
    (hB : IsGaussianSketch P B s) (v : m → ℝ) (i : m) :
    ∫ ω, ((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2 ∂P = (s : ℝ) ^ 2 *
      ((Fintype.card n : ℝ) ^ 2 * v i ^ 2 + (Fintype.card n : ℝ) * (v ⬝ᵥ v) +
        (Fintype.card n : ℝ) * v i ^ 2) := by
  classical
  have hI : ∀ t t' : m × n, Integrable
      (fun ω => v t.1 * v t'.1 * (B ω i t.2 * B ω t.1 t.2 * B ω i t'.2 * B ω t'.1 t'.2)) P :=
    fun t t' => (integrable_four (X := fun (a : m × n) ω => B ω a.1 a.2) hB.hasLaw'
      (i, t.2) t (i, t'.2) t').const_mul _
  have hexp : ∀ ω, ((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2 = ∑ t : m × n, ∑ t' : m × n,
      v t.1 * v t'.1 * (B ω i t.2 * B ω t.1 t.2 * B ω i t'.2 * B ω t'.1 t'.2) := by
    intro ω
    rw [mulVec_eq_sum, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => by ring
  simp only [hexp]
  rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ => hI t t']
  have h : ∀ t : m × n, ∫ ω, ∑ t' : m × n,
      v t.1 * v t'.1 * (B ω i t.2 * B ω t.1 t.2 * B ω i t'.2 * B ω t'.1 t'.2) ∂P =
      ∑ t' : m × n, v t.1 * v t'.1 * ((s : ℝ) ^ 2 *
        ((if i = t.1 then 1 else 0) * (if i = t'.1 then 1 else 0) +
         (if t.2 = t'.2 then 1 else 0) * (if t.1 = t'.1 then 1 else 0) +
         (if i = t'.1 then 1 else 0) * (if t.1 = i then 1 else 0) *
           (if t.2 = t'.2 then 1 else 0))) := by
    intro t
    rw [integral_finsetSum _ fun t' _ => hI t t']
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [integral_const_mul, hB.quad_moment]
  simp only [h]
  rw [← isserlis_sum v i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t' _ => by ring

/-- The coordinates of the defect of a Gaussian sketch are in `L²`. -/
private theorem IsGaussianSketch.memLp_defect [Fintype m] [Fintype n] [DecidableEq m]
    (hB : IsGaussianSketch P B s) (v : m → ℝ) (i : m) :
    MemLp (fun ω => defect (B ω) v i) 2 P := by
  have := hB.indep.isProbabilityMeasure
  have e : (fun ω => defect (B ω) v i) =
      fun ω => (∑ t : m × n, v t.1 * (B ω i t.2 * B ω t.1 t.2)) - v i := by
    ext ω
    simp only [defect, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, mulVec_eq_sum]
  rw [e]
  have h1 : MemLp (fun ω => ∑ t : m × n, v t.1 * (B ω i t.2 * B ω t.1 t.2)) 2 P :=
    memLp_finsetSum (f := fun (t : m × n) ω => v t.1 * (B ω i t.2 * B ω t.1 t.2)) _
      fun t _ => (hB.memLp_pair (i, t.2) t).const_mul _
  exact h1.sub (memLp_const _)

/-- The exact mean square defect of a Gaussian sketch with entry variance `s`:
`E‖(B Bᵀ - I) v‖₂² = (s² (r² + d r + r) - 2 r s + 1) ‖v‖₂²`. -/
private theorem IsGaussianSketch.integral_defect_dot [Fintype m] [Fintype n] [DecidableEq m]
    (hB : IsGaussianSketch P B s) (v : m → ℝ) :
    ∫ ω, defect (B ω) v ⬝ᵥ defect (B ω) v ∂P =
      ((s : ℝ) ^ 2 * ((Fintype.card n : ℝ) ^ 2 + Fintype.card m * Fintype.card n +
        Fintype.card n) - 2 * Fintype.card n * s + 1) * (v ⬝ᵥ v) := by
  have := hB.indep.isProbabilityMeasure
  have hY : ∀ i, Integrable (fun ω => ((B ω * (B ω)ᵀ) *ᵥ v) i) P := by
    intro i
    simp only [mulVec_eq_sum]
    exact integrable_finsetSum _ fun t _ =>
      ((hB.memLp_pair (i, t.2) t).integrable (by norm_num)).const_mul _
  have hY2 : ∀ i, Integrable (fun ω => ((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2) P := by
    intro i
    have h := (hB.memLp_defect v i).integrable_sq
    have e : (fun ω => ((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2) = fun ω => defect (B ω) v i ^ 2 +
        2 * v i * ((B ω * (B ω)ᵀ) *ᵥ v) i - v i ^ 2 := by
      ext ω
      simp only [defect, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      ring
    rw [e]
    exact (h.add ((hY i).const_mul _)).sub (integrable_const _)
  have hI1 : ∀ i, Integrable (fun ω => ((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2 -
      2 * v i * ((B ω * (B ω)ᵀ) *ᵥ v) i) P := fun i => (hY2 i).sub ((hY i).const_mul _)
  have hI2 : ∀ i, Integrable (fun ω => ((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2 -
      2 * v i * ((B ω * (B ω)ᵀ) *ᵥ v) i + v i ^ 2) P :=
    fun i => (hI1 i).add (integrable_const _)
  have hexp : ∀ ω, defect (B ω) v ⬝ᵥ defect (B ω) v = ∑ i, (((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2 -
      2 * v i * ((B ω * (B ω)ᵀ) *ᵥ v) i + v i ^ 2) := by
    intro ω
    simp only [dotProduct, defect, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ i, ∫ ω, (((B ω * (B ω)ᵀ) *ᵥ v) i ^ 2 -
      2 * v i * ((B ω * (B ω)ᵀ) *ᵥ v) i + v i ^ 2) ∂P =
      (s : ℝ) ^ 2 * ((Fintype.card n : ℝ) ^ 2 * v i ^ 2 + (Fintype.card n : ℝ) * (v ⬝ᵥ v) +
        (Fintype.card n : ℝ) * v i ^ 2) - 2 * v i * ((Fintype.card n : ℝ) * s * v i) + v i ^ 2 := by
    intro i
    rw [integral_add (hI1 i) (integrable_const _),
      integral_sub (hY2 i) ((hY i).const_mul _), integral_const_mul, hB.integral_mulVec_sq,
      hB.integral_mulVec]
    simp
  simp only [hexp]
  rw [integral_finsetSum _ fun i _ => hI2 i]
  simp only [hterm]
  have hsum : ∑ i, v i ^ 2 = v ⬝ᵥ v := by simp [dotProduct, sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ i, 2 * v i * ((Fintype.card n : ℝ) * s * v i) =
      2 * (Fintype.card n : ℝ) * s * (v ⬝ᵥ v) := by
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  ring

end Moments

section Theorems

/-- `E[B Bᵀ] = r s I`. -/
private theorem IsGaussianSketch.secondMoment_eq {m n : Type*} [Finite m] [Fintype n]
    [DecidableEq m] {B : Ω → Matrix m n ℝ} {s : ℝ≥0} (hB : IsGaussianSketch P B s) :
    secondMoment P B = ((Fintype.card n : ℝ) * s) • (1 : Matrix m m ℝ) := by
  have := Fintype.ofFinite m
  ext i j
  have h := hB.integral_mulVec (Pi.single j 1) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at h
  simp only [secondMoment, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h, Matrix.one_apply, Pi.single_apply]

/-- **arXiv 2401.03748, Lemma D.2 (2)** (unbiasedness).  If `B ∈ ℝ^{d × r}` has i.i.d. `N(0, 1/r)`
entries then `E[B Bᵀ] = I`, hence `‖E[B Bᵀ] v - v‖₂ = 0` for every `v`.  The paper prints
`N(0, 1/k)`, a typo for `1/r` (its proof and Thm D.3 use `1/r`), and assumes `r < d` and a unit
vector `v`, neither of which is needed.  The proof is a direct second moment computation instead of
the paper's rotation to `e₁`. -/
theorem lemmaD2_unbiased {d r : ℕ} (hr : 0 < r) {B : Ω → Matrix (Fin d) (Fin r) ℝ}
    (hB : IsGaussianSketch P B (r : ℝ≥0)⁻¹) :
    secondMoment P B = 1 ∧ ∀ v : Fin d → ℝ, vnorm (secondMoment P B *ᵥ v - v) = 0 := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h : secondMoment P B = 1 := by
    rw [hB.secondMoment_eq]
    simp [hr']
  refine ⟨h, fun v => ?_⟩
  simp [h, vnorm]

/-- The coefficient of the mean square defect for `s = 1/r` is `(d + 1)/r`. -/
private theorem defect_coeff {r : ℕ} (hr : 0 < r) (d : ℕ) :
    (((r : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) ^ 2 * ((r : ℝ) ^ 2 + d * r + r) -
      2 * r * (((r : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) + 1 = ((d : ℝ) + 1) / r := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [NNReal.coe_inv, NNReal.coe_natCast]
  field_simp
  ring

/-- For `s = 1/r`: `E‖(B Bᵀ - I) v‖₂² = (d + 1)/r ‖v‖₂²`. -/
private theorem IsGaussianSketch.integral_defect_dot' {d r : ℕ} (hr : 0 < r)
    {B : Ω → Matrix (Fin d) (Fin r) ℝ} (hB : IsGaussianSketch P B (r : ℝ≥0)⁻¹) (v : Fin d → ℝ) :
    ∫ ω, defect (B ω) v ⬝ᵥ defect (B ω) v ∂P = ((d : ℝ) + 1) / r * (v ⬝ᵥ v) := by
  rw [hB.integral_defect_dot, ← defect_coeff hr d]
  simp [Fintype.card_fin]

/-- **arXiv 2401.03748, Theorem D.3, exact form.**  Let the `B_u ∈ ℝ^{d × r}` be pairwise
independent with i.i.d. `N(0, 1/r)` entries.  Then the error of eq. (7) is finite and equals `ε_i =
(1/|S|²) ∑_u α_u² ‖p_u‖₂² (d + 1)/r`.  This is stronger than the `O(d/r)` of the paper.  The paper
derives its bound from Prop. D.1 and Lemma D.2, which does not work: see the module docstring. The
proof computes the fourth moments directly by Isserlis' formula. -/
theorem theoremD3_eq [IsProbabilityMeasure P] {d r : ℕ} (hr : 0 < r)
    (S : Finset U) (α : U → ℝ) (p : U → Fin d → ℝ) (B : U → Ω → Matrix (Fin d) (Fin r) ℝ)
    (hB : ∀ u ∈ S, IsGaussianSketch P (B u) (r : ℝ≥0)⁻¹)
    (hindep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → IndepFun (B u) (B v) P) :
    Integrable (fun ω => vnorm (itemError S α p fun u => B u ω) ^ 2) P ∧
    ∫ ω, vnorm (itemError S α p fun u => B u ω) ^ 2 ∂P =
      (S.card : ℝ)⁻¹ ^ 2 * (∑ u ∈ S, α u ^ 2 * vnorm (p u) ^ 2) * (((d : ℝ) + 1) / r) := by
  classical
  have hform : ∀ ω, vnorm (itemError S α p fun u => B u ω) ^ 2 =
      ((-(S.card : ℝ)⁻¹) • ∑ u ∈ S, α u • defect (B u ω) (p u)) ⬝ᵥ
        ((-(S.card : ℝ)⁻¹) • ∑ u ∈ S, α u • defect (B u ω) (p u)) := fun ω => by
    rw [vnorm_sq, itemError_eq]
  obtain ⟨hI, hE⟩ := integral_dot_sum (P := P) S α (fun u ω => defect (B u ω) (p u))
    (fun u hu i => (hB u hu).memLp_defect (p u) i)
    (fun u hu v hv huv i => (hindep u hu v hv huv).comp (measurable_defect (p u) i)
      (measurable_defect (p v) i))
  simp only [hform]
  refine ⟨hI _, ?_⟩
  rw [hE]
  have hm : ∀ u ∈ S, (fun i => ∫ ω, defect (B u ω) (p u) i ∂P) = 0 := by
    intro u hu
    ext i
    have hent : ∀ i j, Integrable (fun ω => (B u ω * (B u ω)ᵀ) i j) P := by
      intro i j
      have h := ((hB u hu).memLp_defect (Pi.single j 1) i).integrable (by norm_num)
      have e : ∀ ω, (B u ω * (B u ω)ᵀ) i j =
          defect (B u ω) (Pi.single j 1) i + (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
        intro ω
        simp [defect]
      simp only [e]
      exact h.add (integrable_const _)
    have h2 := congrFun (integral_defect (P := P) hent (p u)) i
    rw [h2, (lemmaD2_unbiased hr (hB u hu)).1]
    simp
  have hcross : ∑ u ∈ S, ∑ v ∈ S.erase u, α u * α v *
      ((fun i => ∫ ω, defect (B u ω) (p u) i ∂P) ⬝ᵥ (fun i => ∫ ω, defect (B v ω) (p v) i ∂P)) =
      0 := by
    refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v _ => ?_
    rw [hm u hu]
    simp
  have hdiag : ∑ u ∈ S, α u ^ 2 * ∫ ω, defect (B u ω) (p u) ⬝ᵥ defect (B u ω) (p u) ∂P =
      (∑ u ∈ S, α u ^ 2 * vnorm (p u) ^ 2) * (((d : ℝ) + 1) / r) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [(hB u hu).integral_defect_dot' hr, vnorm_sq]
    ring
  rw [hcross, hdiag, zero_add]
  ring

/-- **arXiv 2401.03748, Theorem D.3.**  Let `r < d` and let the `B_u ∈ ℝ^{d × r}` be pairwise
independent with i.i.d. `N(0, 1/r)` entries.  Then
`ε_i ≤ (1/|S|) max_u α_u² ‖p_u‖₂² · 2 d/r`, the paper's `(1/|S|) max_u α_u ‖p_u‖₂² O(d/r)` with the
explicit constant `2`, and with `α_u²` where the paper prints `α_u` (its proof has `α_u²`).
Integrability is part of `theoremD3_eq`. -/
theorem theoremD3 [IsProbabilityMeasure P] {d r : ℕ} (hr : 0 < r) (hrd : r < d)
    (S : Finset U) (hS : S.Nonempty) (α : U → ℝ) (p : U → Fin d → ℝ)
    (B : U → Ω → Matrix (Fin d) (Fin r) ℝ)
    (hB : ∀ u ∈ S, IsGaussianSketch P (B u) (r : ℝ≥0)⁻¹)
    (hindep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → IndepFun (B u) (B v) P) :
    ∫ ω, vnorm (itemError S α p fun u => B u ω) ^ 2 ∂P ≤
      (S.card : ℝ)⁻¹ * S.sup' hS (fun u => α u ^ 2 * vnorm (p u) ^ 2) * (2 * (d / r)) := by
  rw [(theoremD3_eq hr S α p B hB hindep).2]
  set M := S.sup' hS (fun u => α u ^ 2 * vnorm (p u) ^ 2)
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hsum : ∑ u ∈ S, α u ^ 2 * vnorm (p u) ^ 2 ≤ S.card * M := by
    calc _ ≤ ∑ _u ∈ S, M := Finset.sum_le_sum fun u hu =>
          Finset.le_sup' (fun u => α u ^ 2 * vnorm (p u) ^ 2) hu
      _ = _ := by simp
  have hd1 : ((d : ℝ) + 1) / r ≤ 2 * (d / r) := by
    have h1 : (1 : ℝ) ≤ d := by
      have : 1 ≤ d := by omega
      exact_mod_cast this
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hr'.le
  have hM : 0 ≤ M := by
    obtain ⟨u, hu⟩ := hS
    exact le_trans (by positivity) (Finset.le_sup' (fun u => α u ^ 2 * vnorm (p u) ^ 2) hu)
  calc (S.card : ℝ)⁻¹ ^ 2 * (∑ u ∈ S, α u ^ 2 * vnorm (p u) ^ 2) * (((d : ℝ) + 1) / r)
      ≤ (S.card : ℝ)⁻¹ ^ 2 * (S.card * M) * (2 * (d / r)) := by
        have h0 : 0 ≤ ∑ u ∈ S, α u ^ 2 * vnorm (p u) ^ 2 :=
          Finset.sum_nonneg fun u _ => by positivity
        gcongr
    _ = (S.card : ℝ)⁻¹ * M * (2 * (d / r)) := by
        field_simp

/-- Companion of **arXiv 2401.03748, Theorem D.3** for the algorithm the paper proposes.  CoLR
(Sec. 4.3, Algorithm 1) shares one `B`, while Appendix D assumes independent `B_u`.  For a shared
Gaussian `B` the error of eq. (7) is exactly `ε_i = (d + 1)/r ‖Δ̄‖₂²`: there is no factor `1/|S|`,
only the mean update in place of the individual ones.  This statement is not in the paper. -/
theorem sharedSketch_mse {d r : ℕ} (hr : 0 < r) (S : Finset U) (α : U → ℝ)
    (p : U → Fin d → ℝ) {B : Ω → Matrix (Fin d) (Fin r) ℝ}
    (hB : IsGaussianSketch P B (r : ℝ≥0)⁻¹) :
    ∫ ω, vnorm (itemError S α p fun _ => B ω) ^ 2 ∂P =
      ((d : ℝ) + 1) / r * vnorm (meanUpdate S α p) ^ 2 := by
  have hform : ∀ ω, vnorm (itemError S α p fun _ => B ω) ^ 2 =
      defect (B ω) (meanUpdate S α p) ⬝ᵥ defect (B ω) (meanUpdate S α p) := by
    intro ω
    have h : itemError S α p (fun _ => B ω) = -defect (B ω) (meanUpdate S α p) := by
      rw [itemError_eq]
      simp only [defect, meanUpdate, Matrix.mulVec_smul, Matrix.mulVec_sum, neg_smul]
    rw [vnorm_sq, h]
    simp
  simp only [hform]
  rw [hB.integral_defect_dot' hr, vnorm_sq]

/-- Non-vacuity for **arXiv 2401.03748, Appendix D**: on the product space where all entries of all
users are independent `N(0, s)`, every `B_u` is a Gaussian sketch and `B_u`, `B_v` are independent
for `u ≠ v`.  So the hypotheses of `lemmaD2_unbiased`, `lemmaD2_opNorm`, `theoremD3_eq`, `theoremD3`
and `sharedSketch_mse` can hold. -/
theorem exists_gaussianSketch_family (U m n : Type*) [Finite U] [Finite m] [Finite n] (s : ℝ≥0) :
    ∃ (P : Measure (U × m × n → ℝ)) (B : U → (U × m × n → ℝ) → Matrix m n ℝ),
      IsProbabilityMeasure P ∧ (∀ u, IsGaussianSketch P (B u) s) ∧
        ∀ u v, u ≠ v → IndepFun (B u) (B v) P := by
  classical
  have := Fintype.ofFinite U
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  let P : Measure (U × m × n → ℝ) := Measure.pi fun _ => gaussianReal 0 s
  have hI : iIndepFun (fun (t : U × m × n) (ω : U × m × n → ℝ) => ω t) P :=
    iIndepFun_pi (X := fun _ x => x) fun _ => aemeasurable_id
  have hL : ∀ t : U × m × n, HasLaw (fun ω : U × m × n → ℝ => ω t) (gaussianReal 0 s) P := by
    intro t
    exact ⟨(measurable_pi_apply t).aemeasurable, (measurePreserving_eval _ t).map_eq⟩
  let B : U → (U × m × n → ℝ) → Matrix m n ℝ := fun u ω => Matrix.of fun i j => ω (u, i, j)
  have hmB : ∀ u, Measurable (B u) := fun u =>
    Measurable.of_eval_matrix _ fun i j => measurable_pi_apply (u, i, j)
  refine ⟨P, B, inferInstance, fun u => ⟨hmB u, fun i j => hL (u, i, j), ?_⟩, fun u v huv => ?_⟩
  · exact hI.precomp (g := fun a : m × n => (u, a.1, a.2)) fun a b h => by
      simpa [Prod.ext_iff] using h
  · let S : Finset (U × m × n) := Finset.univ.filter (·.1 = u)
    let T : Finset (U × m × n) := Finset.univ.filter (·.1 = v)
    have hST : Disjoint S T := by
      refine Finset.disjoint_left.mpr fun t ht ht' => huv ?_
      have h1 := (Finset.mem_filter.mp ht).2
      have h2 := (Finset.mem_filter.mp ht').2
      exact h1.symm.trans h2
    have h := hI.indepFun_finset S T hST fun t => measurable_pi_apply t
    let φ : (S → ℝ) → Matrix m n ℝ := fun g => Matrix.of fun i j =>
      g ⟨(u, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    let ψ : (T → ℝ) → Matrix m n ℝ := fun g => Matrix.of fun i j =>
      g ⟨(v, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hφ : Measurable φ := Measurable.of_eval_matrix _ fun i j => measurable_pi_apply _
    have hψ : Measurable ψ := Measurable.of_eval_matrix _ fun i j => measurable_pi_apply _
    exact h.comp hφ hψ

end Theorems

/-- `E exp(θ X²/s) = (1 - 2θ)^{-1/2}` for `X ~ N(0, s)` and `2θ < 1`. -/
private theorem gaussian_exp_sq (s : ℝ≥0) (hs : s ≠ 0) (θ : ℝ) (hθ : 2 * θ < 1) :
    Integrable (fun x : ℝ => Real.exp (θ * (x ^ 2 / s))) (gaussianReal 0 s) ∧
    ∫ x, Real.exp (θ * (x ^ 2 / s)) ∂gaussianReal 0 s = (√(1 - 2 * θ))⁻¹ := by
  have hv : (0 : ℝ) < s := by positivity
  set v : ℝ := (s : ℝ) with hvdef
  set b : ℝ := (1 - 2 * θ) / (2 * v) with hbdef
  have hb : 0 < b := div_pos (by linarith) (by positivity)
  have hfun : ∀ x, gaussianPDFReal 0 s x * Real.exp (θ * (x ^ 2 / v)) =
      (√(2 * Real.pi * v))⁻¹ * Real.exp (-b * x ^ 2) := by
    intro x
    rw [gaussianPDFReal, mul_assoc, ← Real.exp_add]
    congr 2
    rw [hbdef, ← hvdef]
    field_simp
    ring
  have hI : Integrable (fun x => (√(2 * Real.pi * v))⁻¹ * Real.exp (-b * x ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  constructor
  · rw [gaussianReal_of_var_ne_zero _ hs,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    refine hI.congr (ae_of_all _ fun x => ?_)
    simp only [toReal_gaussianPDF, smul_eq_mul]
    rw [← hfun]
  · rw [integral_gaussianReal_eq_integral_smul hs]
    simp only [smul_eq_mul, hfun]
    rw [integral_const_mul, integral_gaussian]
    have h1 : Real.pi / b = 2 * Real.pi * v / (1 - 2 * θ) := by
      rw [hbdef]; field_simp
    have h2 : (0 : ℝ) < 2 * Real.pi * v := by positivity
    rw [h1, Real.sqrt_div h2.le]
    have h3 : √(2 * Real.pi * v) ≠ 0 := (Real.sqrt_pos.mpr h2).ne'
    field_simp

/-- `(1 - 2θ)^{-1/2} e^{-θ} ≤ e^{4θ²}` for `|θ| ≤ 1/4`: the subexponential bound of `χ²₁ - 1`. -/
private theorem inv_sqrt_mul_exp_le (θ : ℝ) (h : |θ| ≤ 1 / 4) :
    (√(1 - 2 * θ))⁻¹ * Real.exp (-θ) ≤ Real.exp (4 * θ ^ 2) := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hpos : 0 < 1 - 2 * θ := by linarith
  have hsq : 0 < √(1 - 2 * θ) := Real.sqrt_pos.mpr hpos
  have key : (1 - 2 * θ)⁻¹ ≤ Real.exp (2 * θ + 8 * θ ^ 2) := by
    set u := 2 * θ with hu
    have hA : u / (1 - u) ≤ u + 2 * u ^ 2 := by
      rw [div_le_iff₀ hpos]
      have : 0 ≤ u ^ 2 * (1 - 2 * u) := mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith
    have h3 : (1 - u)⁻¹ = u / (1 - u) + 1 := by field_simp; ring
    rw [h3]
    calc u / (1 - u) + 1 ≤ Real.exp (u / (1 - u)) := Real.add_one_le_exp _
      _ ≤ Real.exp (u + 8 * θ ^ 2) := by
          apply Real.exp_le_exp.mpr
          have : u ^ 2 = 4 * θ ^ 2 := by rw [hu]; ring
          linarith
  have hx : (√(1 - 2 * θ))⁻¹ ≤ Real.exp (θ + 4 * θ ^ 2) := by
    have e1 : ((√(1 - 2 * θ))⁻¹) ^ 2 = (1 - 2 * θ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hpos.le]
    have e2 : Real.exp (2 * θ + 8 * θ ^ 2) = Real.exp (θ + 4 * θ ^ 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e2, ← e1] at key
    exact (pow_le_pow_iff_left₀ (by positivity) (Real.exp_pos _).le (by norm_num)).mp key
  calc (√(1 - 2 * θ))⁻¹ * Real.exp (-θ) ≤ Real.exp (θ + 4 * θ ^ 2) * Real.exp (-θ) := by
        gcongr
    _ = Real.exp (4 * θ ^ 2) := by rw [← Real.exp_add]; congr 1; ring

/-- The moment generating function of a centered `χ²`-type sum, for `|θ| ≤ 1/4`. -/
private theorem exp_moment_sum {ι : Type*} [Fintype ι] {Z : ι → Ω → ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 s) P) (hI : iIndepFun Z P) (θ : ℝ)
    (hθ : |θ| ≤ 1 / 4) :
    Integrable (fun ω => Real.exp (θ * ∑ i, (Z i ω ^ 2 / s - 1))) P ∧
    ∫ ω, Real.exp (θ * ∑ i, (Z i ω ^ 2 / s - 1)) ∂P ≤
      Real.exp (4 * θ ^ 2 * Fintype.card ι) := by
  have h2θ : 2 * θ < 1 := by linarith [(abs_le.mp hθ).2]
  obtain ⟨hint, hval⟩ := gaussian_exp_sq s hs θ h2θ
  let f : ℝ → ℝ := fun x => Real.exp (θ * (x ^ 2 / s - 1))
  have hf : ∀ x, f x = Real.exp (θ * (x ^ 2 / s)) * Real.exp (-θ) := by
    intro x
    simp only [f]
    rw [← Real.exp_add]
    congr 1
    ring
  have hfm : Measurable f := by
    simp only [f]
    fun_prop
  have hfint : Integrable f (gaussianReal 0 s) := by
    refine (hint.mul_const (Real.exp (-θ))).congr (ae_of_all _ fun x => ?_)
    exact (hf x).symm
  have hfval : ∫ x, f x ∂gaussianReal 0 s ≤ Real.exp (4 * θ ^ 2) := by
    simp only [hf]
    rw [integral_mul_const, hval]
    exact inv_sqrt_mul_exp_le θ hθ
  have hexp : ∀ ω, Real.exp (θ * ∑ i, (Z i ω ^ 2 / s - 1)) = ∏ i, f (Z i ω) := by
    intro ω
    rw [Finset.mul_sum, Real.exp_sum]
  have hlaw : HasLaw (fun ω i => Z i ω) (Measure.pi fun _ : ι => gaussianReal 0 s) P := by
    refine ⟨aemeasurable_pi_iff.mpr fun i => (hZ i).aemeasurable, ?_⟩
    rw [hI.map_fun_eq_pi_map fun i => (hZ i).aemeasurable]
    congr 1
    ext1 i
    exact (hZ i).map_eq
  have hprod : Integrable (fun x : ι → ℝ => ∏ i, f (x i))
      (Measure.pi fun _ : ι => gaussianReal 0 s) :=
    Integrable.fintype_prod (f := fun _ => f) fun _ => hfint
  simp only [hexp]
  refine ⟨hlaw.integrable_comp hprod, ?_⟩
  have h := hI.integral_fun_prod_comp (f := fun _ x => f x) (fun i => (hZ i).aemeasurable)
    (fun i => hfm.aestronglyMeasurable)
  rw [h]
  have h' : ∀ i, ∫ ω, f (Z i ω) ∂P = ∫ x, f x ∂gaussianReal 0 s := fun i =>
    (hZ i).integral_comp hfm.aestronglyMeasurable
  simp only [h', Finset.prod_const, Finset.card_univ]
  have hpos : 0 ≤ ∫ x, f x ∂gaussianReal 0 s :=
    integral_nonneg fun x => (Real.exp_pos _).le
  calc (∫ x, f x ∂gaussianReal 0 s) ^ Fintype.card ι
      ≤ Real.exp (4 * θ ^ 2) ^ Fintype.card ι := pow_le_pow_left₀ hpos hfval _
    _ = Real.exp (4 * θ ^ 2 * Fintype.card ι) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

section Rows

variable {m n : Type*} {B : Ω → Matrix m n ℝ} {s : ℝ≥0}

/-- For a unit vector `w`, the entries of `B w` are independent `N(0, s)`.  Independence comes from
joint Gaussianity and zero covariances. -/
private theorem IsGaussianSketch.row [Finite m] [Fintype n] (hB : IsGaussianSketch P B s)
    (w : n → ℝ) (hw : w ⬝ᵥ w = 1) :
    (∀ i, HasLaw (fun ω => (B ω *ᵥ w) i) (gaussianReal 0 s) P) ∧
      iIndepFun (fun i ω => (B ω *ᵥ w) i) P := by
  classical
  have := Fintype.ofFinite m
  have hprob := hB.indep.isProbabilityMeasure
  let X : m × n → Ω → ℝ := fun a ω => B ω a.1 a.2
  have hXl : ∀ a, HasLaw (X a) (gaussianReal 0 s) P := hB.hasLaw'
  have hG : HasGaussianLaw (fun ω a => X a ω) P :=
    hB.indep.hasGaussianLaw fun a => (hXl a).hasGaussianLaw
  let L : (m × n → ℝ) →L[ℝ] (m → ℝ) :=
    ContinuousLinearMap.pi fun i => ∑ k, w k • ContinuousLinearMap.proj (i, k)
  have hZ : HasGaussianLaw (fun ω i => (B ω *ᵥ w) i) P := by
    have h := hG.map_fun L
    have e : (fun ω => L fun a => X a ω) = fun ω i => (B ω *ᵥ w) i := by
      ext ω i
      simp [L, X, Matrix.mulVec, dotProduct, mul_comm]
    rwa [e] at h
  have hZ2 : ∀ i, MemLp (fun ω => (B ω *ᵥ w) i) 2 P := fun i => (hZ.eval i).memLp_two
  have hentry : ∀ a b : m × n, Integrable (fun ω => X a ω * X b ω) P := fun a b =>
    ((hXl a).memLp (memLp_id_gaussianReal' 2 (by simp))).integrable_mul
      ((hXl b).memLp (memLp_id_gaussianReal' 2 (by simp)))
  have hsum : ∀ i ω, (B ω *ᵥ w) i = ∑ k, X (i, k) ω * w k := fun i ω => rfl
  have hmean : ∀ i, ∫ ω, (B ω *ᵥ w) i ∂P = 0 := by
    intro i
    simp only [hsum]
    rw [integral_finsetSum _ fun k _ =>
      (((hXl (i, k)).memLp (memLp_id_gaussianReal' 2 (by simp))).integrable
        (by norm_num)).mul_const _]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_mul_const]
    have := (hXl (i, k)).integral_comp (f := fun x : ℝ => x) aestronglyMeasurable_id
    simp only [Function.comp_def] at this
    rw [this]
    simp
  have hsecond : ∀ i j, ∫ ω, (B ω *ᵥ w) i * (B ω *ᵥ w) j ∂P = if i = j then (s : ℝ) else 0 := by
    intro i j
    have hexp : ∀ ω, (B ω *ᵥ w) i * (B ω *ᵥ w) j =
        ∑ k, ∑ l, w k * w l * (X (i, k) ω * X (j, l) ω) := by
      intro ω
      rw [hsum, hsum, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp only [hexp]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hentry _ _).const_mul _]
    have hval : ∀ k, ∫ ω, ∑ l, w k * w l * (X (i, k) ω * X (j, l) ω) ∂P =
        ∑ l, w k * w l * (if (i, k) = (j, l) then (s : ℝ) else 0) := by
      intro k
      rw [integral_finsetSum _ fun l _ => (hentry _ _).const_mul _]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_const_mul, moment_two hXl hB.indep]
    simp only [hval]
    by_cases hij : i = j
    · subst hij
      have : w ⬝ᵥ w = ∑ k, w k ^ 2 := by simp [dotProduct, sq]
      simp only [Prod.mk.injEq, true_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]
      rw [← Finset.sum_mul]
      simp only [← sq]
      rw [← this, hw, one_mul]
    · simp [hij]
  have hcov : ∀ i j, cov[fun ω => (B ω *ᵥ w) i, fun ω => (B ω *ᵥ w) j; P] =
      if i = j then (s : ℝ) else 0 := by
    intro i j
    rw [covariance_eq_sub (hZ2 i) (hZ2 j), hmean, hmean, zero_mul, sub_zero]
    exact hsecond i j
  constructor
  · intro i
    refine ⟨(hZ.eval i).aemeasurable, ?_⟩
    have h := (hZ.eval i).map_eq_gaussianReal
    have hvar : Var[fun ω => (B ω *ᵥ w) i; P] = s := by
      rw [← covariance_self (hZ2 i).aemeasurable, hcov]
      simp
    rw [h, hvar, hmean]
    simp
  · exact hZ.iIndepFun_of_covariance_eq_zero fun i j hij => by rw [hcov]; simp [hij]

end Rows

/-- The net count is absorbed: `2 · 9^r ≤ e^{3 r}` for `r ≥ 1`. -/
private theorem two_mul_nine_pow_le (r : ℕ) (hr : 0 < r) :
    2 * (9 : ℝ) ^ r ≤ Real.exp (3 * r) := by
  have h18 : (18 : ℝ) ≤ Real.exp 3 := by
    have h := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    calc (18 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have h2 : (2 : ℝ) ≤ 2 ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  calc 2 * (9 : ℝ) ^ r ≤ 2 ^ r * 9 ^ r := by gcongr
    _ = 18 ^ r := by rw [← mul_pow]; norm_num
    _ ≤ Real.exp 3 ^ r := pow_le_pow_left₀ (by norm_num) h18 r
    _ = Real.exp (3 * r) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **arXiv 2401.03748, Lemma D.2 (1)** (operator norm).  Let `1 ≤ r ≤ d` and let `B ∈ ℝ^{d × r}`
have i.i.d. `N(0, 1/r)` entries, `‖B‖` being the spectral norm.  Then `‖B‖²` is integrable and
`E‖B‖² ≤ (d/r) (1 + 26 √(r/d))`, the paper's `(d/r) (1 + O(√(r/d)))` with an explicit constant.  The
paper prints `N(0, 1/k)` for `N(0, 1/r)`, assumes `r < d` and gives no proof of this part.

The proof takes a `1/4`-net `N` of the unit sphere of `ℝ^r` with `|N| ≤ 9^r`, controls `Bᵀ B -
(d/r) I` on `N` by the `χ²_d` moment generating function of `r ‖B w‖₂²` with `θ = √(r/d)/4`, and
absorbs the net loss in `opNorm_sq_le_of_net`, so that the leading constant stays `1`. -/
theorem lemmaD2_opNorm {d r : ℕ} (hr : 0 < r) (hrd : r ≤ d) {B : Ω → Matrix (Fin d) (Fin r) ℝ}
    (hB : IsGaussianSketch P B (r : ℝ≥0)⁻¹) :
    Integrable (fun ω => ‖B ω‖ ^ 2) P ∧
      ∫ ω, ‖B ω‖ ^ 2 ∂P ≤ ((d : ℝ) / r) * (1 + 26 * √((r : ℝ) / d)) := by
  have hprob := hB.indep.isProbabilityMeasure
  set s : ℝ≥0 := (r : ℝ≥0)⁻¹ with hs
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hsval : (s : ℝ) = (r : ℝ)⁻¹ := by simp [hs]
  have hspos : (0 : ℝ) < s := by rw [hsval]; positivity
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hspos
    simp at hspos
  set ρ := √((r : ℝ) / d) with hρ
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hρsq : ρ ^ 2 = (r : ℝ) / d := Real.sq_sqrt (by positivity)
  have hρle : ρ ≤ 1 := by
    rw [hρ, Real.sqrt_le_one, div_le_one hd']
    exact_mod_cast hrd
  have hdρ : (d : ℝ) * ρ ^ 2 = r := by
    rw [hρsq]
    field_simp
  set θ := ρ / 4 with hθ
  have hθpos : 0 < θ := by positivity
  have hθabs : |θ| ≤ 1 / 4 := by
    rw [abs_of_pos hθpos, hθ]
    linarith
  have hθabs' : |-θ| ≤ 1 / 4 := by rwa [abs_neg]
  have h4 : 4 * θ ^ 2 * d = (r : ℝ) / 4 := by
    rw [hθ, ← hdρ]
    ring
  set c : ℝ := 13 * r / 4 with hc
  have hc1 : 1 ≤ c := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    rw [hc]
    linarith
  obtain ⟨N, hN1, hNcard, hNcov⟩ := exists_quarter_net (E := EuclideanSpace ℝ (Fin r))
  rw [finrank_euclideanSpace_fin] at hNcard
  let y : EuclideanSpace ℝ (Fin r) → Ω → ℝ :=
    fun w ω => ∑ i, ((B ω *ᵥ w.ofLp) i ^ 2 / s - 1)
  have hmom : ∀ w ∈ N, ∀ t : ℝ, |t| ≤ 1 / 4 → Integrable (fun ω => Real.exp (t * y w ω)) P ∧
      ∫ ω, Real.exp (t * y w ω) ∂P ≤ Real.exp (4 * t ^ 2 * d) := by
    intro w hw t ht
    have hww : w.ofLp ⬝ᵥ w.ofLp = 1 := by
      have := norm_toLp_sq w.ofLp
      rw [WithLp.toLp_ofLp, hN1 w hw] at this
      simpa using this.symm
    obtain ⟨hlaw, hind⟩ := hB.row w.ofLp hww
    simpa [y] using exp_moment_sum hs0 hlaw hind t ht
  let Q : EuclideanSpace ℝ (Fin r) → Ω → ℝ :=
    fun w ω => Real.exp (θ * y w ω) + Real.exp ((-θ) * y w ω)
  have hQint : ∀ w ∈ N, Integrable (Q w) P := fun w hw =>
    (hmom w hw θ hθabs).1.add (hmom w hw (-θ) hθabs').1
  have hQval : ∀ w ∈ N, ∫ ω, Q w ω ∂P ≤ 2 * Real.exp ((r : ℝ) / 4) := by
    intro w hw
    have h1 := (hmom w hw θ hθabs).2
    have h2 := (hmom w hw (-θ) hθabs').2
    rw [neg_sq] at h2
    rw [h4] at h1 h2
    simp only [Q]
    rw [integral_add (hmom w hw θ hθabs).1 (hmom w hw (-θ) hθabs').1]
    linarith
  have hQpos : ∀ w ω, 0 ≤ Q w ω := fun w ω => by positivity
  let Z : Ω → ℝ := fun ω => Real.exp (-c) * ∑ w ∈ N, Q w ω
  have hZint : Integrable Z P := (integrable_finsetSum _ hQint).const_mul _
  have hZnonneg : ∀ ω, 0 ≤ Z ω := fun ω =>
    mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun w _ => hQpos w ω)
  have hZval : ∫ ω, Z ω ∂P ≤ 1 := by
    simp only [Z]
    rw [integral_const_mul, integral_finsetSum _ hQint]
    have hsum : ∑ w ∈ N, ∫ ω, Q w ω ∂P ≤ N.card * (2 * Real.exp ((r : ℝ) / 4)) := by
      calc _ ≤ ∑ _w ∈ N, 2 * Real.exp ((r : ℝ) / 4) := Finset.sum_le_sum hQval
        _ = _ := by simp
    have hcard : (N.card : ℝ) ≤ 9 ^ r := by exact_mod_cast hNcard
    have hexp := two_mul_nine_pow_le r hr
    calc Real.exp (-c) * ∑ w ∈ N, ∫ ω, Q w ω ∂P
        ≤ Real.exp (-c) * (N.card * (2 * Real.exp ((r : ℝ) / 4))) := by gcongr
      _ ≤ Real.exp (-c) * ((9 ^ r : ℝ) * (2 * Real.exp ((r : ℝ) / 4))) := by gcongr
      _ = Real.exp (-c) * (2 * 9 ^ r * Real.exp ((r : ℝ) / 4)) := by ring
      _ ≤ Real.exp (-c) * (Real.exp (3 * r) * Real.exp ((r : ℝ) / 4)) := by gcongr
      _ = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]
          have : -c + (3 * r + (r : ℝ) / 4) = 0 := by rw [hc]; ring
          rw [this, Real.exp_zero]
  let Mo : Ω → ℝ := fun ω => (Z ω + c - 1) / θ
  have hMo0 : ∀ ω, 0 ≤ Mo ω := fun ω => div_nonneg (by linarith [hZnonneg ω]) hθpos.le
  have hbound : ∀ w ∈ N, ∀ ω, |y w ω| ≤ Mo ω := by
    intro w hw ω
    simp only [Mo]
    rw [le_div_iff₀ hθpos]
    have h1 : |y w ω| * θ - c + 1 ≤ Real.exp (|y w ω| * θ - c) := Real.add_one_le_exp _
    have h2 : Real.exp (|y w ω| * θ - c) ≤ Z ω := by
      have e : Real.exp (|y w ω| * θ - c) = Real.exp (-c) * Real.exp (|y w ω| * θ) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      simp only [Z]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      refine le_trans ?_ (Finset.single_le_sum (f := fun w => Q w ω)
        (fun w _ => hQpos w ω) hw)
      simp only [Q]
      rcases abs_cases (y w ω) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h, mul_comm]
        linarith [Real.exp_pos ((-θ) * y w ω)]
      · rw [h]
        have : -y w ω * θ = -θ * y w ω := by ring
        rw [this]
        linarith [Real.exp_pos (θ * y w ω)]
    linarith
  have hpoint : ∀ ω, ‖B ω‖ ^ 2 ≤ s * d + 2 * (s * Mo ω) := by
    intro ω
    let T : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (B ω))
    have hT : ‖B ω‖ = ‖T‖ := rfl
    rw [hT]
    refine opNorm_sq_le_of_net T N hN1 hNcov _ _ (by positivity)
      (mul_nonneg hspos.le (hMo0 ω)) fun w hw => ?_
    have hTw : ‖T w‖ ^ 2 = (B ω *ᵥ w.ofLp) ⬝ᵥ (B ω *ᵥ w.ofLp) := norm_toLp_sq _
    have hy : ‖T w‖ ^ 2 - s * d = s * y w ω := by
      rw [hTw]
      simp only [y, dotProduct, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.sum_div]
      simp only [← sq]
      field_simp
    rw [hy, abs_mul, abs_of_pos hspos]
    exact mul_le_mul_of_nonneg_left (hbound w hw ω) hspos.le
  have hgint : Integrable (fun ω => (s : ℝ) * d + 2 * (s * Mo ω)) P := by
    simp only [Mo]
    exact (integrable_const _).add (((((hZint.add (integrable_const _)).sub
      (integrable_const _)).div_const _).const_mul _).const_mul _)
  have hmeas : AEStronglyMeasurable (fun ω => ‖B ω‖ ^ 2) P :=
    ((measurable_opNorm.comp hB.measurable).pow_const 2).aestronglyMeasurable
  have hle : ∫ ω, ‖B ω‖ ^ 2 ∂P ≤ ∫ ω, (s : ℝ) * d + 2 * (s * Mo ω) ∂P :=
    integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) hgint (ae_of_all _ hpoint)
  refine ⟨hgint.mono' hmeas (ae_of_all _ fun ω => ?_), hle.trans ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  · have e : ∫ ω, (s : ℝ) * d + 2 * (s * Mo ω) ∂P =
        s * d + 2 * s * ((∫ ω, Z ω ∂P) + c - 1) / θ := by
      have e1 : ∀ ω, (s : ℝ) * d + 2 * (s * Mo ω) =
          ((s : ℝ) * d + 2 * s * (c - 1) / θ) + (2 * s / θ) * Z ω := by
        intro ω
        simp only [Mo]
        field_simp
        ring
      simp only [e1]
      rw [integral_add (integrable_const _) (hZint.const_mul _), integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      field_simp
      ring
    rw [e]
    have h2 : (s : ℝ) * d + 2 * s * ((∫ ω, Z ω ∂P) + c - 1) / θ ≤ s * d + 2 * s * c / θ := by
      gcongr
      linarith
    refine h2.trans (le_of_eq ?_)
    have e3 : (d : ℝ) / r * (26 * ρ) = 26 / ρ := by
      rw [← hdρ]
      field_simp
    rw [mul_add, mul_one, e3, hsval, hc, hθ]
    field_simp
    ring

end Sketch

end LeanDLRA.Literature.P2401_03748
