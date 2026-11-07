import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Literature.RankAdaptive.P2007_13153a
import LeanDLRA.Literature.Foundations.P2008_07427a
import LeanDLRA.Literature.Randomized.P2308_16547b

/-!
# Results of arXiv 2308.16547: Adaptive symplectic hyper-reduction

Matrix-level results of Pagliantini–Vismara, arXiv 2308.16547 (Frobenius norm throughout; the
a posteriori bound, Proposition 3, is in `P2308_16547b`, whose `Mmat` and `projT` are reused).
`lemma_1`/`lemma_1_isLeast` (Lemma 1): `O(α, β) = ‖M₁ + α βᵀ M₂‖²` takes the same values on the
rank-`r` pairs as on those with `αᵀ α` diagonal.  `proposition_1` (Proposition 1, via the
library's Eckart–Young theorem, the compact SVD `C* = U* Σ* V*ᵀ` given as data): the minimum of
`‖Sᵀ R* + α βᵀ C*‖²` over rank-`r` pairs, `r ≤ rank(Sᵀ R* V*)`, is
`‖Sᵀ R*‖² - ∑_{i < r} σ_i(Sᵀ R* V*)²`, attained with `α βᵀ = -(Sᵀ R* V*)_r Σ*⁻¹ U*ᵀ`;
`proposition_1_full` is eq. (14) (`α βᵀ = -Sᵀ R* (C*)†`).  `proposition_2` (Proposition 2):
`‖U^upd C - D‖² = ‖U C - D‖² - δ` with `δ` of (18), so the EIM residual decreases iff `δ > 0`
(for any matrix in place of `(C*)†`).  `eq_17`/`eq_17_lt_iff` (eq. (17)): with all parameters
sampled the residual drops by exactly `‖Sᵀ R V‖²`; the strict decrease claimed in (17) is false
in general (`eq_17_strict_fails`, a counterexample with nonzero residual).  `rank_condition`
(Sec. 5): `rank M(Z*) = 2n` forces `p*_A ≥ n`, sharp by `rank_condition_sharp`.
`symplectic_dlra` (Sec. 2, eqs. (4)–(6)): a solution `(A, Z)` of (6) on `[t₀, T]` with `A(t₀)`
ortho-symplectic keeps `A(t)` ortho-symplectic (`isOrthosymplectic_of_eq_6a`, by Grönwall on the
defects `J A - A J` and `Aᵀ A - I`, with no assumption on `A` along the flow), `W = A Z`
satisfies `Ẇ = Π_{T_W} X_H(W)` with `Π` the projection (5), and the (total) Hamiltonian is
conserved; `hasFDerivAt_reduced_hamiltonian` shows (6b) is the Hamiltonian flow of
`H_r(Z) = H(A Z)`.  Not formalized: per-parameter conservation of each `H_{η_k}`, uniqueness of
the minimizer in Proposition 1, and the algorithms and complexity counts.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2308_16547


section Lemma1

variable {q₁ q₂ g : Type*} [Fintype q₁] [Fintype q₂] [Fintype g]

/-- The cost `O(α, β) = ‖M₁ + α βᵀ M₂‖_F²` of Lemma 1 (Frobenius norm). -/
noncomputable def costO {ρ : Type*} [Fintype ρ] (M₁ : Matrix q₁ g ℝ) (M₂ : Matrix q₂ g ℝ)
    (α : Matrix q₁ ρ ℝ) (β : Matrix q₂ ρ ℝ) : ℝ :=
  ‖M₁ + α * βᵀ * M₂‖ ^ 2

/-- `𝒱_r`: pairs `(α, β) ∈ ℝ^{q₁ × r} × ℝ^{q₂ × r}` with `rank α = rank β = r`. -/
def pairsV (q₁ q₂ : Type*) [Fintype q₁] [Fintype q₂] (r : ℕ) :
    Set (Matrix q₁ (Fin r) ℝ × Matrix q₂ (Fin r) ℝ) :=
  {ab | ab.1.rank = r ∧ ab.2.rank = r}

/-- `𝒱̄_r`: pairs of `𝒱_r` with `αᵀ α` diagonal. -/
def pairsVbar (q₁ q₂ : Type*) [Fintype q₁] [Fintype q₂] (r : ℕ) :
    Set (Matrix q₁ (Fin r) ℝ × Matrix q₂ (Fin r) ℝ) :=
  {ab | ab.1.rank = r ∧ ab.2.rank = r ∧ (ab.1ᵀ * ab.1).IsDiag}

omit [Fintype q₂] in
/-- Every pair `(α, β)` can be replaced by `(Q, Z) = (α V, β V)`, `V` an orthogonal eigenbasis of
`αᵀ α`, with the same ranks, `Qᵀ Q` diagonal and `Q Zᵀ = α βᵀ`. -/
lemma exists_orthogonal_reparam {ρ : Type*} [Fintype ρ]
    (α : Matrix q₁ ρ ℝ) (β : Matrix q₂ ρ ℝ) :
    ∃ Q : Matrix q₁ ρ ℝ, ∃ Z : Matrix q₂ ρ ℝ, Q.rank = α.rank ∧ Z.rank = β.rank ∧
      (Qᵀ * Q).IsDiag ∧ Q * Zᵀ = α * βᵀ := by
  classical
  have hH : (αᵀ * α).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul]
  set V : Matrix ρ ρ ℝ := (hH.eigenvectorUnitary : Matrix ρ ρ ℝ) with hV
  have hVV : Vᵀ * V = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hVV' : V * Vᵀ = 1 := mul_eq_one_comm.1 hVV
  have hdet : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hVV
  refine ⟨α * V, β * V, Matrix.rank_mul_eq_left_of_isUnit_det V α hdet,
    Matrix.rank_mul_eq_left_of_isUnit_det V β hdet, ?_, ?_⟩
  · have h := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    have : (α * V)ᵀ * (α * V) = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      rw [← h]
      simp [Matrix.transpose_mul, Matrix.mul_assoc, hV, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [this]; exact Matrix.isDiag_diagonal _
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV', Matrix.one_mul]

/-- **Lemma 1** (arXiv 2308.16547).  For `M₁ ∈ ℝ^{q₁ × g}`, `M₂ ∈ ℝ^{q₂ × g}`, the set of values of
`O(α, β) = ‖M₁ + α βᵀ M₂‖_F²` over `𝒱_r = {rank α = rank β = r}` equals the set of values over
`𝒱̄_r = {(α, β) ∈ 𝒱_r : αᵀ α diagonal}`; in particular the two minima coincide
(`lemma_1_isLeast`).  Differences: this equality of value sets is stronger than the paper's equality
of minima and needs no existence of a minimizer; the condition `1 ≤ r ≤ q₂` is not needed; the
proof uses an orthogonal eigenbasis of `αᵀ α` instead of the paper's unnormalised QR
factorisation. -/
theorem lemma_1 (M₁ : Matrix q₁ g ℝ) (M₂ : Matrix q₂ g ℝ) (r : ℕ) :
    (fun ab => costO M₁ M₂ ab.1 ab.2) '' pairsV q₁ q₂ r =
      (fun ab => costO M₁ M₂ ab.1 ab.2) '' pairsVbar q₁ q₂ r := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨α, β⟩, ⟨hα, hβ⟩, rfl⟩
    obtain ⟨Q, Z, hQ, hZ, hD, hQZ⟩ := exists_orthogonal_reparam α β
    exact ⟨(Q, Z), ⟨hQ.trans hα, hZ.trans hβ, hD⟩, by simp [costO, hQZ]⟩
  · exact image_mono fun ab h => ⟨h.1, h.2.1⟩

/-- **Lemma 1** (arXiv 2308.16547), in the paper's form: `o` is the minimum of `O` over `𝒱_r` iff it
is the minimum of `O` over `𝒱̄_r`. -/
theorem lemma_1_isLeast (M₁ : Matrix q₁ g ℝ) (M₂ : Matrix q₂ g ℝ) (r : ℕ) (o : ℝ) :
    IsLeast ((fun ab => costO M₁ M₂ ab.1 ab.2) '' pairsV q₁ q₂ r) o ↔
      IsLeast ((fun ab => costO M₁ M₂ ab.1 ab.2) '' pairsVbar q₁ q₂ r) o := by
  rw [lemma_1]

end Lemma1

section Proposition1

open LeanDLRA.EckartYoung Matrix

variable {σ κ μ ρ : Type*} [Fintype σ] [Fintype κ] [Fintype μ] [Fintype ρ] [DecidableEq ρ]

/-- Pythagoras for the orthogonal projector `V Vᵀ` (`Vᵀ V = I`):
`‖Y‖² = ‖Y V‖² + ‖Y - Y V Vᵀ‖²`. -/
lemma sq_norm_eq_add_of_orthonormal {V : Matrix κ ρ ℝ} (hV : Vᵀ * V = 1) (Y : Matrix σ κ ℝ) :
    ‖Y‖ ^ 2 = ‖Y * V‖ ^ 2 + ‖Y - Y * V * Vᵀ‖ ^ 2 := by
  have h0 : ⟪Y * V * Vᵀ, Y - Y * V * Vᵀ⟫ = 0 := by
    rw [Frobenius.inner_mul_right, Matrix.transpose_transpose, Matrix.sub_mul,
      Matrix.mul_assoc (Y * V), hV, Matrix.mul_one, sub_self, inner_zero_right]
  have := norm_add_sq_real (Y * V * Vᵀ) (Y - Y * V * Vᵀ)
  rw [add_sub_cancel, h0, Frobenius.norm_mul_transpose_of_orthonormal hV] at this
  linarith

/-- With `C* = U* Σ* (V*)ᵀ` (`(V*)ᵀ V* = I`):
`‖X + B C*‖² = ‖X‖² - ‖X V*‖² + ‖X V* + B U* Σ*‖²`. -/
lemma cost_eq (X : Matrix σ κ ℝ) (Us : Matrix μ ρ ℝ) (sv : ρ → ℝ) {Vs : Matrix κ ρ ℝ}
    (hV : Vsᵀ * Vs = 1) (B : Matrix σ μ ℝ) :
    ‖X + B * (Us * diagonal sv * Vsᵀ)‖ ^ 2 =
      ‖X‖ ^ 2 - ‖X * Vs‖ ^ 2 + ‖X * Vs + B * Us * diagonal sv‖ ^ 2 := by
  set W := X + B * (Us * diagonal sv * Vsᵀ) with hWdef
  have h1 : W * Vs = X * Vs + B * Us * diagonal sv := by
    simp only [hWdef, Matrix.add_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
  have h2 : W - W * Vs * Vsᵀ = X - X * Vs * Vsᵀ := by
    rw [h1]; simp only [hWdef, Matrix.add_mul, Matrix.mul_assoc]; abel
  have hW := sq_norm_eq_add_of_orthonormal hV W
  have hX := sq_norm_eq_add_of_orthonormal hV X
  rw [h2, h1] at hW
  linarith

/-- `σ_k(Y) > 0` for `k < rank Y` (singular values zero-indexed). -/
lemma singularValues_pos_of_lt_rank (Y : Matrix σ ρ ℝ) {k : ℕ} (hk : k < Y.rank) :
    0 < (toEuclideanLin Y).singularValues k := by
  rcases ((toEuclideanLin Y).singularValues_nonneg k).lt_or_eq with h | h
  · exact h
  exfalso
  have hsum : ∑ i ∈ Ico k (Fintype.card ρ), (toEuclideanLin Y).singularValues i ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have := sq_singularValues_antitone (toEuclideanLin Y) (Finset.mem_Ico.1 hi).1
    rw [← h] at this
    nlinarith [sq_nonneg ((toEuclideanLin Y).singularValues i)]
  have h0 := sq_norm_sub_truncation Y k
  rw [hsum] at h0
  have hY : Y = truncation Y k :=
    sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))
  have := rank_truncation_le Y k
  rw [← hY] at this
  omega

/-- The `r`-truncated SVD of `Y` has rank `≥ r` when `r ≤ rank Y`. -/
lemma le_rank_truncation (Y : Matrix σ ρ ℝ) {r : ℕ} (hr : r ≤ Y.rank) :
    r ≤ (truncation Y r).rank := by
  by_contra h
  rw [not_le] at h
  have hr1 : 1 ≤ r := by omega
  have hn : r ≤ Fintype.card ρ := hr.trans (rank_le_card_width Y)
  have hlow := sum_sq_singularValues_le_sq_norm_sub Y (truncation Y r) (r := r - 1) (by omega)
  rw [sq_norm_sub_truncation, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Nat.sub_add_cancel hr1] at hlow
  have hpos := singularValues_pos_of_lt_rank Y (k := r - 1) (by omega)
  nlinarith [sq_pos_of_pos hpos]

omit [Fintype σ] [Fintype κ] [Fintype μ] [Fintype ρ] [DecidableEq ρ] in
/-- `rank (-A) = rank A`. -/
lemma rank_neg' {m n : Type*} [Finite m] [Fintype n] (A : Matrix m n ℝ) :
    (-A).rank = A.rank := by
  classical
  have := Fintype.ofFinite m
  have h : -A = (-1 : Matrix m m ℝ) * A := by rw [Matrix.neg_mul, Matrix.one_mul]
  rw [h]
  exact rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_left_inverse
    (B := (-1 : Matrix m m ℝ)) (by rw [Matrix.neg_mul, Matrix.one_mul, neg_neg]))

/-- `Fin r ≃ {i : Fin N // i < r}` for `r ≤ N`. -/
def finLtEquiv {N r : ℕ} (h : r ≤ N) : Fin r ≃ {i : Fin N // (i : ℕ) < r} where
  toFun k := ⟨⟨k, lt_of_lt_of_le k.2 h⟩, k.2⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The update `-(Sᵀ R* V*)_r (Σ*)⁻¹ (U*)ᵀ` of Proposition 1, with `X = Sᵀ R*`,
`(·)_r = truncation · r` the `r`-truncated SVD and `Σ* = diagonal sv`. -/
noncomputable def optUpdate (X : Matrix σ κ ℝ) (Us : Matrix μ ρ ℝ) (sv : ρ → ℝ)
    (Vs : Matrix κ ρ ℝ) (r : ℕ) : Matrix σ μ ℝ :=
  -(truncation (X * Vs) r * diagonal sv⁻¹ * Usᵀ)

/-- Lower bound of Proposition 1, for every pair `(α, β)` (no rank condition needed):
`O(α, β) ≥ ‖X‖² - ∑_{i < r} σ_i(X V*)²`. -/
lemma cost_lower (X : Matrix σ κ ℝ) {Cs : Matrix μ κ ℝ} {Us : Matrix μ ρ ℝ} {sv : ρ → ℝ}
    {Vs : Matrix κ ρ ℝ} (hV : Vsᵀ * Vs = 1) (hC : Cs = Us * diagonal sv * Vsᵀ) {r : ℕ}
    (hn : r ≤ Fintype.card ρ) (α : Matrix σ (Fin r) ℝ) (β : Matrix μ (Fin r) ℝ) :
    ‖X‖ ^ 2 - ∑ i ∈ range r, (toEuclideanLin (X * Vs)).singularValues i ^ 2 ≤
      costO X Cs α β := by
  have hB : (-(α * βᵀ * Us * diagonal sv)).rank ≤ r := by
    rw [rank_neg']
    calc _ ≤ (α * βᵀ * Us).rank := rank_mul_le_left _ _
      _ ≤ (α * βᵀ).rank := rank_mul_le_left _ _
      _ ≤ α.rank := rank_mul_le_left _ _
      _ ≤ r := by simpa using rank_le_card_width α
  have hEY := sum_sq_singularValues_le_sq_norm_sub (X * Vs) _ hB
  rw [sub_neg_eq_add] at hEY
  have hsum := sq_norm_eq_sum_sq_singularValues (X * Vs)
  rw [← Finset.sum_range_add_sum_Ico _ hn] at hsum
  have hc : costO X Cs α β =
      ‖X‖ ^ 2 - ‖X * Vs‖ ^ 2 + ‖X * Vs + α * βᵀ * Us * diagonal sv‖ ^ 2 := by
    rw [costO, hC, cost_eq X Us sv hV]
  linarith

/-- **Proposition 1** (arXiv 2308.16547).  Let `S ∈ ℝ^{d × m_s}`, `R* ∈ ℝ^{d × 2np*}`, and let
`C* = U* Σ* (V*)ᵀ ∈ ℝ^{m × 2np*}` be a compact SVD (`(U*)ᵀ U* = I`, `(V*)ᵀ V* = I`,
`Σ* = diagonal sv`, `sv > 0`).  For every `r ≤ rank(Sᵀ R* V*)` the minimum of
`O(α, β) = ‖Sᵀ R* + α βᵀ C*‖_F²` over pairs `(α, β) ∈ ℝ^{m_s × r} × ℝ^{m × r}` of rank `r` is
`‖Sᵀ R*‖_F² - ∑_{i < r} σ_i(Sᵀ R* V*)²` (zero-indexed singular values, i.e. the paper's
`∑_{i=1}^r`), and it is attained by a pair of rank `r` with
`α βᵀ = -(Sᵀ R* V*)_r (Σ*)⁻¹ (U*)ᵀ` (`optUpdate`, `(·)_r` the truncated SVD `truncation`).
Differences: the compact SVD of `C*` is given as data (Mathlib has no SVD; the library's
Eckart–Young theorem does the work), which also encodes `rank C* ≤ m`; `r = 0` is allowed; we
prove that the given update is *a* minimizer, not that it is the only one. -/
theorem proposition_1 {ι : Type*} [Fintype ι] (S : Matrix ι σ ℝ) (Rs : Matrix ι κ ℝ)
    (Cs : Matrix μ κ ℝ) (Us : Matrix μ ρ ℝ) (sv : ρ → ℝ) (Vs : Matrix κ ρ ℝ)
    (hU : Usᵀ * Us = 1) (hV : Vsᵀ * Vs = 1) (hsv : ∀ i, 0 < sv i)
    (hC : Cs = Us * diagonal sv * Vsᵀ) {r : ℕ} (hr : r ≤ (Sᵀ * Rs * Vs).rank) :
    IsLeast ((fun ab => costO (Sᵀ * Rs) Cs ab.1 ab.2) '' pairsV σ μ r)
      (‖Sᵀ * Rs‖ ^ 2 - ∑ i ∈ range r, (toEuclideanLin (Sᵀ * Rs * Vs)).singularValues i ^ 2) ∧
    ∃ ab ∈ pairsV σ μ r, ab.1 * ab.2ᵀ = optUpdate (Sᵀ * Rs) Us sv Vs r ∧
      costO (Sᵀ * Rs) Cs ab.1 ab.2 =
        ‖Sᵀ * Rs‖ ^ 2 - ∑ i ∈ range r, (toEuclideanLin (Sᵀ * Rs * Vs)).singularValues i ^ 2 := by
  classical
  set X := Sᵀ * Rs with hX
  set Y := X * Vs with hY
  have hn : r ≤ Fintype.card ρ := hr.trans (rank_le_card_width Y)
  set Vr := topRightSingularVectors Y r with hVr
  let e := finLtEquiv (N := Module.finrank ℝ (EuclideanSpace ℝ ρ)) (r := r)
    (by rw [finrank_euclideanSpace]; exact hn)
  let α₀ : Matrix σ (Fin r) ℝ := (Y * Vr).submatrix id e
  let β₀ : Matrix μ (Fin r) ℝ := (-(Us * diagonal sv⁻¹ * Vr)).submatrix id e
  have hprod : α₀ * β₀ᵀ = optUpdate X Us sv Vs r := by
    simp only [α₀, β₀, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, optUpdate, truncation, Matrix.transpose_mul,
      Matrix.diagonal_transpose, Matrix.transpose_neg, Matrix.mul_neg, Matrix.mul_assoc, ← hVr,
      ← hY]
  have hDD : diagonal sv⁻¹ * diagonal sv = (1 : Matrix ρ ρ ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hsv i).ne'
  have hT : optUpdate X Us sv Vs r * Us * diagonal sv = -truncation Y r := by
    simp only [optUpdate, Matrix.neg_mul, Matrix.mul_assoc, hU, hDD, Matrix.mul_one, ← hY]
  have hval : costO X Cs α₀ β₀ =
      ‖X‖ ^ 2 - ∑ i ∈ range r, (toEuclideanLin Y).singularValues i ^ 2 := by
    rw [costO, hprod, hC, cost_eq X Us sv hV, hT, ← sub_eq_add_neg, sq_norm_sub_truncation,
      sq_norm_eq_sum_sq_singularValues Y, ← Finset.sum_range_add_sum_Ico _ hn]
    ring
  have htr := le_rank_truncation Y (hY ▸ hr)
  have hα : α₀.rank = r := by
    refine le_antisymm (by simpa using rank_le_card_width α₀) ?_
    have : α₀.rank = (Y * Vr).rank := rank_submatrix _ (Equiv.refl _) e
    rw [this]
    exact htr.trans (rank_mul_le_left _ _)
  have hβ : β₀.rank = r := by
    refine le_antisymm (by simpa using rank_le_card_width β₀) ?_
    have : β₀.rank = (Us * diagonal sv⁻¹ * Vr).rank := by
      rw [show β₀.rank = (-(Us * diagonal sv⁻¹ * Vr)).rank from
        rank_submatrix _ (Equiv.refl _) e, rank_neg']
    rw [this]
    have hVrT : Vrᵀ = (Us * diagonal sv⁻¹ * Vr)ᵀ * Us * diagonal sv := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc, hU, hDD,
        Matrix.mul_one]
    calc r ≤ (truncation Y r).rank := htr
      _ = (Y * Vr * ((Us * diagonal sv⁻¹ * Vr)ᵀ * Us * diagonal sv)).rank := by
          rw [← hVrT]; rfl
      _ ≤ ((Us * diagonal sv⁻¹ * Vr)ᵀ * Us * diagonal sv).rank := rank_mul_le_right _ _
      _ ≤ ((Us * diagonal sv⁻¹ * Vr)ᵀ * Us).rank := rank_mul_le_left _ _
      _ ≤ (Us * diagonal sv⁻¹ * Vr)ᵀ.rank := rank_mul_le_left _ _
      _ = _ := rank_transpose _
  refine ⟨⟨⟨(α₀, β₀), ⟨hα, hβ⟩, hval⟩, ?_⟩, ⟨(α₀, β₀), ⟨hα, hβ⟩, hprod, hval⟩⟩
  rintro _ ⟨⟨α, β⟩, _, rfl⟩
  exact cost_lower X hV hC hn α β

/-- The pseudo-inverse `(C*)† = V* (Σ*)⁻¹ (U*)ᵀ` built from a compact SVD `C* = U* Σ* (V*)ᵀ`
(as in line 13 of Algorithm 1 of arXiv 2308.16547). -/
noncomputable def svdPinv (Us : Matrix μ ρ ℝ) (sv : ρ → ℝ) (Vs : Matrix κ ρ ℝ) :
    Matrix κ μ ℝ :=
  Vs * diagonal sv⁻¹ * Usᵀ

/-- The singular values of `Y` vanish from index `rank Y` on. -/
lemma sum_Ico_rank_eq_zero (Y : Matrix σ ρ ℝ) :
    ∑ i ∈ Ico Y.rank (Fintype.card ρ), (toEuclideanLin Y).singularValues i ^ 2 = 0 := by
  have h1 := sum_sq_singularValues_le_sq_norm_sub Y Y (r := Y.rank) le_rfl
  rw [sub_self, norm_zero] at h1
  exact le_antisymm (by simpa using h1) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Truncating the SVD at the rank changes nothing. -/
lemma truncation_rank (Y : Matrix σ ρ ℝ) : truncation Y Y.rank = Y := by
  have h := sq_norm_sub_truncation Y Y.rank
  rw [sum_Ico_rank_eq_zero] at h
  exact (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h))).symm

/-- **Proposition 1, last claim / eq. (14)** (arXiv 2308.16547).  For `r = rank(Sᵀ R* V*)` the
minimizing update is `α βᵀ = -Sᵀ R* (C*)†`, with `(C*)† = V* (Σ*)⁻¹ (U*)ᵀ` (`svdPinv`), and the
minimum is `‖Sᵀ R*‖_F² - ‖Sᵀ R* V*‖_F²`.  Same conventions and differences as
`proposition_1`. -/
theorem proposition_1_full {ι : Type*} [Fintype ι] (S : Matrix ι σ ℝ) (Rs : Matrix ι κ ℝ)
    (Cs : Matrix μ κ ℝ) (Us : Matrix μ ρ ℝ) (sv : ρ → ℝ) (Vs : Matrix κ ρ ℝ)
    (hU : Usᵀ * Us = 1) (hV : Vsᵀ * Vs = 1) (hsv : ∀ i, 0 < sv i)
    (hC : Cs = Us * diagonal sv * Vsᵀ) :
    IsLeast ((fun ab => costO (Sᵀ * Rs) Cs ab.1 ab.2) '' pairsV σ μ (Sᵀ * Rs * Vs).rank)
      (‖Sᵀ * Rs‖ ^ 2 - ‖Sᵀ * Rs * Vs‖ ^ 2) ∧
    ∃ ab ∈ pairsV σ μ (Sᵀ * Rs * Vs).rank, ab.1 * ab.2ᵀ = -(Sᵀ * Rs * svdPinv Us sv Vs) ∧
      costO (Sᵀ * Rs) Cs ab.1 ab.2 = ‖Sᵀ * Rs‖ ^ 2 - ‖Sᵀ * Rs * Vs‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := proposition_1 S Rs Cs Us sv Vs hU hV hsv hC le_rfl
  have hsum : ∑ i ∈ range (Sᵀ * Rs * Vs).rank,
      (toEuclideanLin (Sᵀ * Rs * Vs)).singularValues i ^ 2 = ‖Sᵀ * Rs * Vs‖ ^ 2 := by
    rw [sq_norm_eq_sum_sq_singularValues, ← Finset.sum_range_add_sum_Ico _
      (rank_le_card_width (Sᵀ * Rs * Vs)), sum_Ico_rank_eq_zero, add_zero]
  rw [hsum] at h1 h2
  refine ⟨h1, ?_⟩
  obtain ⟨ab, hab, hp, hc⟩ := h2
  refine ⟨ab, hab, ?_, hc⟩
  rw [hp, optUpdate, truncation_rank, svdPinv]
  simp only [Matrix.mul_assoc]

/-- Non-vacuity of `proposition_1` (arXiv 2308.16547): `S = R* = C* = 1 ∈ ℝ^{1 × 1}`, `r = 1`. -/
example := proposition_1 (ι := Fin 1) (σ := Fin 1) (κ := Fin 1) (μ := Fin 1) (ρ := Fin 1)
  1 1 1 1 1 1 (by simp) (by simp) (fun _ => one_pos) (by simp) (r := 1) (by simp [Matrix.rank_one])

end Proposition1

section Proposition2

open Matrix

variable {ι μ κ κ' ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [Fintype κ] [Fintype κ']
  [Fintype ρ] [DecidableEq ρ]

/-- The sampling matrix `S = [e_{i₁} | … | e_{i_{m_s}}] ∈ ℝ^{d × m_s}` of the indices `i` with
`p i` (eq. (13)); `selMat (¬ p ·)` is the complementary matrix `S̆`. -/
def selMat (p : ι → Prop) [DecidablePred p] : Matrix ι {i // p i} ℝ :=
  Matrix.of fun i j => if i = j.1 then 1 else 0

omit [Fintype ι] in
/-- `Sᵀ X` is the submatrix of the sampled rows. -/
lemma selMat_transpose_mul [Fintype ι] (p : ι → Prop) [DecidablePred p] {n : Type*}
    (X : Matrix ι n ℝ) : (selMat p)ᵀ * X = X.submatrix Subtype.val id := by
  ext j k
  simp [selMat, Matrix.mul_apply]

/-- `‖X‖_F² = ‖Sᵀ X‖_F² + ‖S̆ᵀ X‖_F²`. -/
lemma sq_norm_split (p : ι → Prop) [DecidablePred p] {n : Type*} [Fintype n]
    (X : Matrix ι n ℝ) :
    ‖X‖ ^ 2 = ‖(selMat p)ᵀ * X‖ ^ 2 + ‖(selMat (fun i => ¬ p i))ᵀ * X‖ ^ 2 := by
  rw [selMat_transpose_mul, selMat_transpose_mul, Frobenius.norm_sq_eq_sum,
    Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
  simp only [Matrix.submatrix_apply, id]
  exact (Fintype.sum_subtype_add_sum_subtype p _).symm

/-- The EIM coefficients `C = (Pᵀ U)⁻¹ Pᵀ D`, eq. (12). -/
noncomputable def eimCoeff [DecidableEq μ] (P U : Matrix ι μ ℝ) (D : Matrix ι κ ℝ) :
    Matrix μ κ ℝ :=
  (Pᵀ * U)⁻¹ * Pᵀ * D

/-- The residual identity behind Proposition 2, for an arbitrary row correction `K`: if
`Sᵀ U^upd = Sᵀ U - Sᵀ K` and `S̆ᵀ U^upd = S̆ᵀ U`, then
`‖U^upd C - D‖² = ‖U C - D‖² - (‖Sᵀ (U C - D)‖² - ‖Sᵀ (U C - D - K C)‖²)`. -/
theorem sq_norm_update (p : ι → Prop) [DecidablePred p] (U Uupd K : Matrix ι μ ℝ)
    (C : Matrix μ κ ℝ) (D : Matrix ι κ ℝ)
    (h₁ : (selMat p)ᵀ * Uupd = (selMat p)ᵀ * U - (selMat p)ᵀ * K)
    (h₂ : (selMat (fun i => ¬ p i))ᵀ * Uupd = (selMat (fun i => ¬ p i))ᵀ * U) :
    ‖Uupd * C - D‖ ^ 2 = ‖U * C - D‖ ^ 2 -
      (‖(selMat p)ᵀ * (U * C - D)‖ ^ 2 - ‖(selMat p)ᵀ * (U * C - D - K * C)‖ ^ 2) := by
  have e₁ : (selMat p)ᵀ * (Uupd * C - D) = (selMat p)ᵀ * (U * C - D - K * C) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h₁]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have e₂ : (selMat (fun i => ¬ p i))ᵀ * (Uupd * C - D) =
      (selMat (fun i => ¬ p i))ᵀ * (U * C - D) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h₂, Matrix.mul_sub, ← Matrix.mul_assoc]
  have hA := sq_norm_split p (Uupd * C - D)
  have hB := sq_norm_split p (U * C - D)
  rw [e₁, e₂] at hA
  linarith

/-- **Proposition 2** (arXiv 2308.16547).  Let `C = (Pᵀ U)⁻¹ Pᵀ D` (`eimCoeff`), `R = U C - D`,
let the sample parameters be given by a column map `f` (so `R* = R f` is the residual of the
sampled columns), let `S` select the rows `i` with `p i` and `S̆` the others, and let `U^upd`
satisfy `Sᵀ U^upd = Sᵀ U - Sᵀ R* (C*)†`, `S̆ᵀ U^upd = S̆ᵀ U`.  Then
`‖U^upd C - D‖_F² = ‖U C - D‖_F² - δ` with `δ = ‖Sᵀ R‖_F² - ‖Sᵀ (R - R* (C*)† C)‖_F²` (18), so
`‖U^upd C - D‖_F < ‖U C - D‖_F` iff `δ > 0`.  Differences: `(C*)†` may be any matrix `Cdag`
(the identity does not use that it is the pseudo-inverse of `C* = C f`), and neither the
invertibility of `Pᵀ U` nor the structure of `D` (11) is needed. -/
theorem proposition_2 [DecidableEq μ] (p : ι → Prop) [DecidablePred p] (U P : Matrix ι μ ℝ)
    (D : Matrix ι κ ℝ) (f : κ' → κ) (Cdag : Matrix κ' μ ℝ) (Uupd : Matrix ι μ ℝ)
    (h₁ : (selMat p)ᵀ * Uupd = (selMat p)ᵀ * U -
      (selMat p)ᵀ * ((U * eimCoeff P U D - D).submatrix id f * Cdag))
    (h₂ : (selMat (fun i => ¬ p i))ᵀ * Uupd = (selMat (fun i => ¬ p i))ᵀ * U) :
    ‖Uupd * eimCoeff P U D - D‖ ^ 2 = ‖U * eimCoeff P U D - D‖ ^ 2 -
        (‖(selMat p)ᵀ * (U * eimCoeff P U D - D)‖ ^ 2 -
          ‖(selMat p)ᵀ * (U * eimCoeff P U D - D -
            (U * eimCoeff P U D - D).submatrix id f * Cdag * eimCoeff P U D)‖ ^ 2) ∧
    (‖Uupd * eimCoeff P U D - D‖ < ‖U * eimCoeff P U D - D‖ ↔
      0 < ‖(selMat p)ᵀ * (U * eimCoeff P U D - D)‖ ^ 2 -
          ‖(selMat p)ᵀ * (U * eimCoeff P U D - D -
            (U * eimCoeff P U D - D).submatrix id f * Cdag * eimCoeff P U D)‖ ^ 2) := by
  have h := sq_norm_update p U Uupd _ (eimCoeff P U D) D h₁ h₂
  refine ⟨h, ?_⟩
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, h]
  constructor <;> intro <;> linarith

/-- **Eq. (17)** (arXiv 2308.16547).  With all parameters sampled (`R* = R`, `C* = C`) and a
compact SVD `C = U Σ Vᵀ` (`(C)† = V Σ⁻¹ Uᵀ`, `svdPinv`), the update of Proposition 1 gives
`‖U^upd C - D‖_F² = ‖U C - D‖_F² - ‖Sᵀ R V‖_F²`; equivalently `δ = ‖Sᵀ R V‖_F²` in (18) (the
paper writes `‖Sᵀ R V‖_F`, missing the square).  The final strict inequality of (17)
`… < ‖U C - D‖_F²` is false in general, see `eq_17_strict_fails`; it holds iff `Sᵀ R V ≠ 0`. -/
theorem eq_17 [DecidableEq μ] (p : ι → Prop) [DecidablePred p] (U P : Matrix ι μ ℝ)
    (D : Matrix ι κ ℝ) (Us : Matrix μ ρ ℝ) (sv : ρ → ℝ) (Vs : Matrix κ ρ ℝ)
    (hU : Usᵀ * Us = 1) (hV : Vsᵀ * Vs = 1) (hsv : ∀ i, 0 < sv i)
    (hC : eimCoeff P U D = Us * diagonal sv * Vsᵀ) (Uupd : Matrix ι μ ℝ)
    (h₁ : (selMat p)ᵀ * Uupd = (selMat p)ᵀ * U -
      (selMat p)ᵀ * ((U * eimCoeff P U D - D) * svdPinv Us sv Vs))
    (h₂ : (selMat (fun i => ¬ p i))ᵀ * Uupd = (selMat (fun i => ¬ p i))ᵀ * U) :
    ‖Uupd * eimCoeff P U D - D‖ ^ 2 =
      ‖U * eimCoeff P U D - D‖ ^ 2 - ‖(selMat p)ᵀ * (U * eimCoeff P U D - D) * Vs‖ ^ 2 := by
  have h := sq_norm_update p U Uupd _ (eimCoeff P U D) D h₁ h₂
  set R := U * eimCoeff P U D - D
  have hDD : diagonal sv⁻¹ * diagonal sv = (1 : Matrix ρ ρ ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hsv i).ne'
  have hPC : svdPinv Us sv Vs * (Us * diagonal sv * Vsᵀ) = Vs * Vsᵀ := by
    calc svdPinv Us sv Vs * (Us * diagonal sv * Vsᵀ)
        = Vs * (diagonal sv⁻¹ * (Usᵀ * Us) * diagonal sv) * Vsᵀ := by
          simp only [svdPinv, Matrix.mul_assoc]
      _ = Vs * Vsᵀ := by rw [hU, Matrix.mul_one, hDD, Matrix.mul_one]
  have hKC : R * svdPinv Us sv Vs * eimCoeff P U D = R * Vs * Vsᵀ := by
    rw [Matrix.mul_assoc R, hC, hPC, Matrix.mul_assoc]
  have e : (selMat p)ᵀ * (R - R * Vs * Vsᵀ) =
      (selMat p)ᵀ * R - (selMat p)ᵀ * R * Vs * Vsᵀ := by
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
  have hpy := sq_norm_eq_add_of_orthonormal hV ((selMat p)ᵀ * R)
  rw [hKC, e] at h
  linarith

/-- **Eq. (17)** (arXiv 2308.16547), corrected strict form: the residual decreases strictly iff
`Sᵀ R V ≠ 0`. -/
theorem eq_17_lt_iff [DecidableEq μ] (p : ι → Prop) [DecidablePred p] (U P : Matrix ι μ ℝ)
    (D : Matrix ι κ ℝ) (Us : Matrix μ ρ ℝ) (sv : ρ → ℝ) (Vs : Matrix κ ρ ℝ)
    (hU : Usᵀ * Us = 1) (hV : Vsᵀ * Vs = 1) (hsv : ∀ i, 0 < sv i)
    (hC : eimCoeff P U D = Us * diagonal sv * Vsᵀ) (Uupd : Matrix ι μ ℝ)
    (h₁ : (selMat p)ᵀ * Uupd = (selMat p)ᵀ * U -
      (selMat p)ᵀ * ((U * eimCoeff P U D - D) * svdPinv Us sv Vs))
    (h₂ : (selMat (fun i => ¬ p i))ᵀ * Uupd = (selMat (fun i => ¬ p i))ᵀ * U) :
    ‖Uupd * eimCoeff P U D - D‖ < ‖U * eimCoeff P U D - D‖ ↔
      (selMat p)ᵀ * (U * eimCoeff P U D - D) * Vs ≠ 0 := by
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    eq_17 p U P D Us sv Vs hU hV hsv hC Uupd h₁ h₂, sub_lt_self_iff, ← norm_pos_iff]
  constructor
  · intro h
    exact lt_of_le_of_ne (norm_nonneg _) fun h0 => by rw [← h0] at h; simp at h
  · intro h; positivity

/-- **Eq. (17), strict inequality: false as stated** (arXiv 2308.16547).  With `d = 2`, `m = 1`,
`U = P = e₁`, `D = e₂` one has `C = 0` (compact SVD with `r_C = 0`), `R = -e₂ ≠ 0`, all rows and
parameters sampled, and the update leaves `U` unchanged, so the EIM residual does not decrease. -/
theorem eq_17_strict_fails :
    ∃ (U Uupd D : Matrix (Fin 2) (Fin 1) ℝ) (Us : Matrix (Fin 1) (Fin 0) ℝ) (sv : Fin 0 → ℝ)
      (Vs : Matrix (Fin 1) (Fin 0) ℝ),
      Usᵀ * Us = 1 ∧ Vsᵀ * Vs = 1 ∧ (∀ i, 0 < sv i) ∧
      eimCoeff U U D = Us * diagonal sv * Vsᵀ ∧
      (selMat (fun _ : Fin 2 => True))ᵀ * Uupd = (selMat (fun _ : Fin 2 => True))ᵀ * U -
        (selMat (fun _ : Fin 2 => True))ᵀ * ((U * eimCoeff U U D - D) * svdPinv Us sv Vs) ∧
      (selMat (fun _ : Fin 2 => ¬ True))ᵀ * Uupd = (selMat (fun _ : Fin 2 => ¬ True))ᵀ * U ∧
      U * eimCoeff U U D - D ≠ 0 ∧ ‖Uupd * eimCoeff U U D - D‖ = ‖U * eimCoeff U U D - D‖ := by
  set U : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![1], ![0]]
  set D : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![0], ![1]]
  have hUD : Uᵀ * D = 0 := by
    ext i j; simp [U, D, Matrix.mul_apply, Fin.sum_univ_two]
  have hC : eimCoeff U U D = 0 := by
    rw [eimCoeff, Matrix.mul_assoc, hUD, Matrix.mul_zero]
  refine ⟨U, U, D, 0, 0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _, fun i => i.elim0,
    ?_, ?_, rfl, ?_, rfl⟩
  · rw [hC]; simp
  · have : svdPinv (0 : Matrix (Fin 1) (Fin 0) ℝ) (0 : Fin 0 → ℝ)
        (0 : Matrix (Fin 1) (Fin 0) ℝ) = 0 := by
      ext i j; simp [svdPinv, Matrix.mul_apply]
    rw [this, Matrix.mul_zero, Matrix.mul_zero, sub_zero]
  · rw [hC, Matrix.mul_zero, zero_sub, neg_ne_zero]
    intro h
    have := congrFun (congrFun h 1) 0
    simp [D] at this

end Proposition2

section RankCondition

variable {l p : Type*} [Fintype l] [DecidableEq l] [Fintype p]

/-- **Section 5, rank condition** (arXiv 2308.16547).  If `Z* ∈ ℝ^{2n × p*_A}` satisfies
`rank(Z* Z*ᵀ + J_{2n}ᵀ Z* Z*ᵀ J_{2n}) = 2n` (`P2007_13153.Zτ`, `M(Z*)` is `P2007_13153.Smat`),
then `p*_A ≥ n`: `rank M(Z*) ≤ rank(Z* Z*ᵀ) + rank(Jᵀ Z* Z*ᵀ J) ≤ 2 p*_A`. -/
theorem rank_condition (Z : Matrix (l ⊕ l) p ℝ) (h : P2007_13153.Zτ Z) :
    Fintype.card l ≤ Fintype.card p := by
  have h1 : (Z * Zᵀ).rank ≤ Fintype.card p :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width Z)
  have h2 : ((P2007_13153.sJ l)ᵀ * (Z * Zᵀ) * P2007_13153.sJ l).rank ≤ Fintype.card p :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans h1
  have h3 := EckartYoung.rank_add_le (Z * Zᵀ) ((P2007_13153.sJ l)ᵀ * (Z * Zᵀ) * P2007_13153.sJ l)
  unfold P2007_13153.Zτ P2007_13153.Smat at h
  rw [Fintype.card_sum] at h
  omega

/-- The bound of `rank_condition` (arXiv 2308.16547, Sec. 5) is sharp: `Z* = [I_n; 0]` has
`p*_A = n` and `M(Z*) = I_{2n}`. -/
theorem rank_condition_sharp : P2007_13153.Zτ (Matrix.fromRows (1 : Matrix l l ℝ) 0) := by
  have h : P2007_13153.Smat (Matrix.fromRows (1 : Matrix l l ℝ) 0) = 1 := by
    ext (i | i) (j | j) <;>
      simp [P2007_13153.Smat, P2007_13153.sJ, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.one_apply, eq_comm]
  unfold P2007_13153.Zτ
  rw [h, Matrix.rank_one]

end RankCondition


section SymplecticDLRA

open P2008_07427

variable {ι κ p : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype p]

/-- The factor `F = (J_{2N} ∇H(AZ) Zᵀ + ∇H(AZ) Zᵀ J_{2n}) M(Z)⁻¹` of eq. (6a). -/
noncomputable def coefF (g : Matrix (ι ⊕ ι) p ℝ → Matrix (ι ⊕ ι) p ℝ)
    (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix (κ ⊕ κ) p ℝ) : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ :=
  (symplJ ι * g (A * Z) * Zᵀ + g (A * Z) * Zᵀ * symplJ κ) * (Mmat Z)⁻¹

/-- The right-hand side `(I - A Aᵀ)(J_{2N} ∇H(AZ) Zᵀ + ∇H(AZ) Zᵀ J_{2n}) M(Z)⁻¹` of eq. (6a). -/
noncomputable def velA (g : Matrix (ι ⊕ ι) p ℝ → Matrix (ι ⊕ ι) p ℝ)
    (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix (κ ⊕ κ) p ℝ) : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ :=
  (1 - A * Aᵀ) * coefF g A Z

/-- `F J_{2n} = J_{2N} F` for the factor `F` of (6a). -/
lemma coefF_comm (g : Matrix (ι ⊕ ι) p ℝ → Matrix (ι ⊕ ι) p ℝ) (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ)
    {Z : Matrix (κ ⊕ κ) p ℝ} (hM : IsUnit (Mmat Z).det) :
    coefF g A Z * symplJ κ = symplJ ι * coefF g A Z := by
  have hS : IsUnit (P2008_07427.Smat Zᵀ).det := by rwa [← Mmat_eq]
  have hinv := Sinv_comm hS
  rw [← Mmat_eq] at hinv
  set B := g (A * Z) * Zᵀ
  have hB : (symplJ ι * B + B * symplJ κ) * symplJ κ =
      symplJ ι * (symplJ ι * B + B * symplJ κ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, symplJ_mul_self, Matrix.mul_neg,
      Matrix.mul_one, ← Matrix.mul_assoc (symplJ ι) (symplJ ι), Matrix.neg_mul, Matrix.one_mul]
    abel
  unfold coefF
  rw [show symplJ ι * g (A * Z) * Zᵀ = symplJ ι * B by rw [Matrix.mul_assoc]]
  rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]

/-- The defect `J_{2N} A - A J_{2n}` (zero iff `A` intertwines the symplectic units). -/
def defX (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ :=
  symplJ ι * A - A * symplJ κ

/-- Along (6a) the defect `X = J A - A J` solves the linear equation `Ẋ = -(X Aᵀ + A Xᵀ) F`. -/
lemma deriv_defX (A F : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (hF : F * symplJ κ = symplJ ι * F) :
    symplJ ι * ((1 - A * Aᵀ) * F) - (1 - A * Aᵀ) * F * symplJ κ =
      -((defX A * Aᵀ + A * (defX A)ᵀ) * F) := by
  rw [Matrix.mul_assoc (1 - A * Aᵀ), hF]
  simp only [defX, Matrix.transpose_sub, Matrix.transpose_mul, symplJ_transpose, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_neg]
  abel

/-- Along (6a) the defect `G = Aᵀ A - I` solves the linear equation `Ġ = -(Fᵀ A G + G Aᵀ F)`. -/
lemma deriv_defG (A F : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) :
    ((1 - A * Aᵀ) * F)ᵀ * A + Aᵀ * ((1 - A * Aᵀ) * F) =
      -(Fᵀ * A * (Aᵀ * A - 1) + (Aᵀ * A - 1) * (Aᵀ * F)) := by
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Matrix.one_mul,
    Matrix.mul_one]
  abel

section Cont

variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n] {s : Set ℝ}

/-- Products of continuous matrix-valued curves are continuous. -/
lemma continuousOn_matMul {f : ℝ → Matrix m l ℝ} {g : ℝ → Matrix l n ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun t => f t * g t) s := by
  have := (Frobenius.mulCLM (m := m) (l := l) (n := n)).continuous₂.comp_continuousOn
    (hf.prodMk hg)
  exact this

/-- Transposes of continuous matrix-valued curves are continuous. -/
lemma continuousOn_matTranspose {f : ℝ → Matrix m n ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (fun t => (f t)ᵀ) s := by
  exact (Frobenius.transposeCLM (m := m) (n := n)).continuous.comp_continuousOn hf

/-- Inverses of continuous curves of invertible matrices are continuous. -/
lemma continuousOn_matInv [DecidableEq n] {f : ℝ → Matrix n n ℝ} (hf : ContinuousOn f s)
    (hdet : ∀ t ∈ s, IsUnit (f t).det) : ContinuousOn (fun t => (f t)⁻¹) s := by
  intro t ht
  have h1 : ContinuousAt Inv.inv (f t) := continuousAt_matrix_inv _
    (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hdet t ht).ne_zero)
  exact h1.comp_continuousWithinAt (hf t ht)

end Cont

/-- **Section 2, after (6)** (arXiv 2308.16547): the solution `A(t)` of (6a) stays in `U_n`.  If `A`
solves `Ȧ = (I - A Aᵀ)(J_{2N} ∇H(AZ) Zᵀ + ∇H(AZ) Zᵀ J_{2n}) M(Z)⁻¹` on `[t₀, T]` (derivatives
within the interval) for a continuous `Z` with `M(Z(t))` invertible, `∇H` continuous, and
`A(t₀)` is orthosymplectic, then `A(t)` is orthosymplectic for all `t ∈ [t₀, T]`.  Nothing is
assumed about `A` along the flow: the defects `J A - A J` and `Aᵀ A - I` solve linear equations
(`deriv_defX`, `deriv_defG`) and vanish by Grönwall's lemma. -/
theorem isOrthosymplectic_of_eq_6a {g : Matrix (ι ⊕ ι) p ℝ → Matrix (ι ⊕ ι) p ℝ}
    (hg : Continuous g) {A A' : ℝ → Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} {Z : ℝ → Matrix (κ ⊕ κ) p ℝ}
    {t₀ T : ℝ} (hA : ∀ t ∈ Icc t₀ T, HasDerivWithinAt A (A' t) (Icc t₀ T) t)
    (hZ : ContinuousOn Z (Icc t₀ T)) (hA' : ∀ t ∈ Icc t₀ T, A' t = velA g (A t) (Z t))
    (hM : ∀ t ∈ Icc t₀ T, IsUnit (Mmat (Z t)).det) (h₀ : IsOrthosymplectic (A t₀)) :
    ∀ t ∈ Icc t₀ T, IsOrthosymplectic (A t) := by
  have hAc : ContinuousOn A (Icc t₀ T) := fun t ht => (hA t ht).continuousWithinAt
  have hFc : ContinuousOn (fun t => coefF g (A t) (Z t)) (Icc t₀ T) := by
    have hG : ContinuousOn (fun t => g (A t * Z t)) (Icc t₀ T) :=
      hg.comp_continuousOn (continuousOn_matMul hAc hZ)
    have hZt := continuousOn_matTranspose hZ
    have hMc : ContinuousOn (fun t => Mmat (Z t)) (Icc t₀ T) :=
      (continuousOn_matMul hZ hZt).add (continuousOn_matMul (continuousOn_matMul
        continuousOn_const (continuousOn_matMul hZ hZt)) continuousOn_const)
    exact continuousOn_matMul ((continuousOn_matMul (continuousOn_matMul continuousOn_const hG)
      hZt).add (continuousOn_matMul (continuousOn_matMul hG hZt) continuousOn_const))
      (continuousOn_matInv hMc hM)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hAc.norm.mul hFc.norm)
  have hb : ∀ t ∈ Icc t₀ T, ‖A t‖ * ‖coefF g (A t) (Z t)‖ ≤ C := fun t ht =>
    (le_abs_self _).trans (by simpa using hC t ht)
  have hAr : ∀ x ∈ Ico t₀ T, HasDerivWithinAt A (A' x) (Ici x) x := fun x hx =>
    (hA x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  -- the defect `J A - A J` vanishes
  have hX : ∀ t ∈ Icc t₀ T, defX (A t) = 0 := by
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := fun t => defX (A t))
      (f' := fun t => symplJ ι * A' t - A' t * symplJ κ) (K := 2 * C)
      ((continuousOn_matMul continuousOn_const hAc).sub
        (continuousOn_matMul hAc continuousOn_const)) (fun x hx => ?_) ?_ (fun x hx => ?_)
    · exact (Frobenius.hasDerivWithinAt_const_mul _ (hAr x hx)).sub
        (Frobenius.hasDerivWithinAt_mul_const _ (hAr x hx))
    · simp [defX, h₀.comm]
    · have hx' := Ico_subset_Icc_self hx
      rw [hA' x hx', velA, deriv_defX _ _ (coefF_comm g _ (hM x hx')), norm_neg]
      set X := defX (A x)
      set F := coefF g (A x) (Z x)
      have h1 := norm_add_le (X * (A x)ᵀ) (A x * Xᵀ)
      have h2 := Frobenius.norm_mul_le X (A x)ᵀ
      have h3 := Frobenius.norm_mul_le (A x) Xᵀ
      rw [Frobenius.norm_transpose] at h2 h3
      have h4 := Frobenius.norm_mul_le (X * (A x)ᵀ + A x * Xᵀ) F
      have h5 := hb x hx'
      calc ‖(X * (A x)ᵀ + A x * Xᵀ) * F‖ ≤ (2 * ‖X‖ * ‖A x‖) * ‖F‖ :=
            h4.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
        _ = 2 * (‖A x‖ * ‖F‖) * ‖X‖ := by ring
        _ ≤ 2 * C * ‖X‖ := by gcongr
  -- the defect `Aᵀ A - I` vanishes
  have hG : ∀ t ∈ Icc t₀ T, (A t)ᵀ * A t - 1 = 0 := by
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := fun t => (A t)ᵀ * A t - 1)
      (f' := fun t => (A' t)ᵀ * A t + (A t)ᵀ * A' t) (K := 2 * C)
      ((continuousOn_matMul (continuousOn_matTranspose hAc) hAc).sub continuousOn_const)
      (fun x hx => ?_) ?_ (fun x hx => ?_)
    · exact (Frobenius.hasDerivWithinAt_mul (Frobenius.hasDerivWithinAt_transpose (hAr x hx))
        (hAr x hx)).sub_const 1
    · simp [h₀.1]
    · have hx' := Ico_subset_Icc_self hx
      rw [hA' x hx', velA, deriv_defG, norm_neg]
      set G := (A x)ᵀ * A x - 1
      set F := coefF g (A x) (Z x)
      have h2' := Frobenius.norm_mul_le Fᵀ (A x)
      have h3' := Frobenius.norm_mul_le (A x)ᵀ F
      rw [Frobenius.norm_transpose] at h2' h3'
      have h5 := hb x hx'
      have hG0 := norm_nonneg G
      calc ‖Fᵀ * A x * G + G * ((A x)ᵀ * F)‖ ≤ ‖Fᵀ * A x * G‖ + ‖G * ((A x)ᵀ * F)‖ :=
            norm_add_le _ _
        _ ≤ ‖Fᵀ * A x‖ * ‖G‖ + ‖G‖ * ‖(A x)ᵀ * F‖ :=
            add_le_add (Frobenius.norm_mul_le _ _) (Frobenius.norm_mul_le _ _)
        _ ≤ (‖F‖ * ‖A x‖) * ‖G‖ + ‖G‖ * (‖A x‖ * ‖F‖) :=
            add_le_add (mul_le_mul_of_nonneg_right h2' hG0) (mul_le_mul_of_nonneg_left h3' hG0)
        _ = 2 * (‖A x‖ * ‖F‖) * ‖G‖ := by ring
        _ ≤ 2 * C * ‖G‖ := by gcongr
  intro t ht
  have hc : symplJ ι * A t = A t * symplJ κ := sub_eq_zero.1 (hX t ht)
  have h1 : (A t)ᵀ * A t = 1 := sub_eq_zero.1 (hG t ht)
  refine ⟨h1, ?_⟩
  rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- For orthosymplectic `A`, the projection `Π(J_{2N} G)` of (5) at `W = A Z` (in the form
`tangentPi` of arXiv 2008.07427) is `Ȧ Z + A Ż` with `Ȧ`, `Ż` the right-hand sides of (6). -/
lemma tangentPi_eq_rhs {A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} (hA : IsOrthosymplectic A)
    (Z : Matrix (κ ⊕ κ) p ℝ) (G : Matrix (ι ⊕ ι) p ℝ) :
    tangentPi A Zᵀ (symplJ ι * G) =
      (1 - A * Aᵀ) * ((symplJ ι * G * Zᵀ + G * Zᵀ * symplJ κ) * (Mmat Z)⁻¹) * Z +
        A * (symplJ κ * (Aᵀ * G)) := by
  have ht : Aᵀ * symplJ ι = symplJ κ * Aᵀ := by
    have := congrArg Matrix.transpose hA.comm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, symplJ_transpose, symplJ_transpose] at this
    simpa using this
  have hF : Fmat Zᵀ (symplJ ι * G) = symplJ ι * G * Zᵀ + G * Zᵀ * symplJ κ := by
    rw [Fmat, symplJ_transpose, ← Matrix.mul_assoc (symplJ ι) (symplJ ι), symplJ_mul_self]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  unfold tangentPi
  rw [hF, ← Mmat_eq, Matrix.transpose_transpose]
  congr 1
  · simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, ht, Matrix.mul_assoc]

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Section 2, eq. (6b)** (arXiv 2308.16547): the reduced Hamiltonian `H_r(Z) = H(A Z)` has
Frobenius gradient `Aᵀ ∇H(A Z)`, so (6b), `Ż = J_{2n} Aᵀ ∇H(A Z)`, is the Hamiltonian flow
`Ż = J_{2n} ∇H_r(Z)` (for each fixed `A`). -/
theorem hasFDerivAt_reduced_hamiltonian {H : Matrix (ι ⊕ ι) p ℝ → ℝ}
    {g : Matrix (ι ⊕ ι) p ℝ → Matrix (ι ⊕ ι) p ℝ} (hH : ∀ x, HasFDerivAt H (innerSL ℝ (g x)) x)
    (A : Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ) (Z : Matrix (κ ⊕ κ) p ℝ) :
    HasFDerivAt (fun Y => H (A * Y)) (innerSL ℝ (Aᵀ * g (A * Z))) Z := by
  have h := (hH (A * Z)).comp Z (Frobenius.leftMulCLM (n := p) A).hasFDerivAt
  refine h.congr_fderiv ?_
  ext V
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Frobenius.leftMulCLM_apply]
  exact Frobenius.inner_mul_left' _ _ _

/-- **Section 2, eqs. (4)–(6)** (arXiv 2308.16547).  Let `H : ℝ^{2N × p} → ℝ` have continuous
Frobenius gradient `∇H = g`, and let `(A, Z)` solve (6a)–(6b) on `[t₀, T]` (derivatives within
the interval) with `M(Z(t))` invertible and `A(t₀) ∈ U_n`.  Then for every `t ∈ [t₀, T]`:
`A(t)` is orthosymplectic; `W = A Z` satisfies `Ẇ = Π_{T_W M_n} X_H(W)` (4) with `Π` the
projection (5) (`projT`, an orthogonal projector for the symplectic form by arXiv 2008.07427,
`isOrthProj_tangentPi`); and `H(W(t)) = H(W(t₀))`.  Differences: the paper's vector-valued
Hamiltonian `(H_{η_k}(W_k))_k` enters through the total `∑_k H_{η_k}(W_k)`, whose gradient is
`∇H(W)`; conservation of each `H_{η_k}` separately is not claimed.  The invertibility of
`M(Z(t))` (the rank condition defining `M_n`) is assumed along the solution. -/
theorem symplectic_dlra {H : Matrix (ι ⊕ ι) p ℝ → ℝ}
    {g : Matrix (ι ⊕ ι) p ℝ → Matrix (ι ⊕ ι) p ℝ} (hH : ∀ x, HasFDerivAt H (innerSL ℝ (g x)) x)
    (hg : Continuous g) {A A' : ℝ → Matrix (ι ⊕ ι) (κ ⊕ κ) ℝ} {Z Z' : ℝ → Matrix (κ ⊕ κ) p ℝ}
    {t₀ T : ℝ} (hA : ∀ t ∈ Icc t₀ T, HasDerivWithinAt A (A' t) (Icc t₀ T) t)
    (hZ : ∀ t ∈ Icc t₀ T, HasDerivWithinAt Z (Z' t) (Icc t₀ T) t)
    (hA' : ∀ t ∈ Icc t₀ T, A' t = velA g (A t) (Z t))
    (hZ' : ∀ t ∈ Icc t₀ T, Z' t = symplJ κ * ((A t)ᵀ * g (A t * Z t)))
    (hM : ∀ t ∈ Icc t₀ T, IsUnit (Mmat (Z t)).det) (h₀ : IsOrthosymplectic (A t₀)) :
    ∀ t ∈ Icc t₀ T, IsOrthosymplectic (A t) ∧
      HasDerivWithinAt (fun s => A s * Z s)
        (projT (A t) (Z t) (symplJ ι * g (A t * Z t))) (Icc t₀ T) t ∧
      H (A t * Z t) = H (A t₀ * Z t₀) := by
  have hZc : ContinuousOn Z (Icc t₀ T) := fun t ht => (hZ t ht).continuousWithinAt
  have hO := isOrthosymplectic_of_eq_6a hg hA hZc hA' hM h₀
  have hW : ∀ t ∈ Icc t₀ T, HasDerivWithinAt (fun s => A s * Z s)
      (tangentPi (A t) (Z t)ᵀ (symplJ ι * g (A t * Z t))) (Icc t₀ T) t := by
    intro t ht
    have h := Frobenius.hasDerivWithinAt_mul (hA t ht) (hZ t ht)
    rwa [hA' t ht, hZ' t ht, velA, coefF, ← tangentPi_eq_rhs (hO t ht)] at h
  intro t ht
  refine ⟨hO t ht, by rw [projT_eq]; exact hW t ht, ?_⟩
  have hT : t₀ ≤ T := ht.1.trans ht.2
  have ht₀ : t₀ ∈ Icc t₀ T := ⟨le_rfl, hT⟩
  set c : ℝ → ℝ := fun s => (Set.projIcc t₀ T hT s : ℝ) with hc
  have hcs : ∀ s ∈ Icc t₀ T, c s = s := fun s hs => by
    simp [hc, Set.projIcc_of_mem hT hs]
  exact hamiltonian_conserved_matrix (U := fun s => A (c s)) (Z := fun s => (Z (c s))ᵀ) hH
    (fun s => hO _ (Set.projIcc t₀ T hT s).2)
    (fun s => by rw [← Mmat_eq]; exact hM _ (Set.projIcc t₀ T hT s).2)
    (convex_Icc t₀ T) hW (fun s hs => by simp only [hcs s hs]) ht₀ ht

/-- `M(I) = 2 I` is invertible. -/
lemma isUnit_det_Mmat_one :
    IsUnit (Mmat (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)).det := by
  refine Matrix.isUnit_det_of_left_inverse (B := (1 / 2 : ℝ) • 1) ?_
  rw [Mmat, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, symplJ_transpose_mul,
    Matrix.smul_mul, Matrix.one_mul, ← two_smul ℝ (1 : Matrix _ _ ℝ), smul_smul]
  norm_num

/-- Non-vacuity of `symplectic_dlra` (arXiv 2308.16547, Sec. 2): with `N = n = 1`, `p = 2`,
`H = 0`, the constant curves `A = I`, `Z = I` satisfy all hypotheses. -/
example := symplectic_dlra (ι := Fin 1) (κ := Fin 1) (p := Fin 1 ⊕ Fin 1) (H := fun _ => 0)
  (g := fun _ => 0) (A := fun _ => 1) (A' := fun _ => 0) (Z := fun _ => 1) (Z' := fun _ => 0)
  (t₀ := 0) (T := 1) (fun x => by simpa using hasFDerivAt_const (0 : ℝ) x) continuous_const
  (fun t _ => hasDerivWithinAt_const t _ _) (fun t _ => hasDerivWithinAt_const t _ _)
  (fun t _ => by simp [velA]) (fun t _ => by simp) (fun t _ => isUnit_det_Mmat_one)
  ⟨by simp, by simp⟩

end SymplecticDLRA

end LeanDLRA.Literature.P2308_16547
