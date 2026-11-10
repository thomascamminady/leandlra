import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# Ky Fan's maximum principle and the optimality of POD bases

Let `T` be a symmetric operator on an `n`-dimensional inner product space with eigenvalues
`λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ₋₁` (Mathlib's `LinearMap.IsSymmetric.eigenvalues`, sorted decreasingly and
indexed from `0`).  **Ky Fan's maximum principle** (Ky Fan 1949) states that for every
orthonormal family `w₀, …, w_{k-1}`

  `∑ⱼ re ⟪T wⱼ, wⱼ⟫ ≤ λ₀ + ⋯ + λ_{k-1}`,

with equality for the top `k` eigenvectors.  For a real matrix `A ∈ ℝ^{m × n}` and
`T = Aᵀ A` this is the optimality of the *proper orthogonal decomposition* (POD): among all
`W ∈ ℝ^{n × r}` with `Wᵀ W = 1`, the captured energy `‖A W‖_F²` is at most
`∑_{i < r} λᵢ(Aᵀ A)`, and the projection error `‖A (1 - W Wᵀ)‖_F²` is at least
`∑_{i ≥ r} λᵢ(Aᵀ A)`; both bounds are attained by the dominant eigenvectors (the POD basis).

## Main results

* `LeanDLRA.KyFan.sum_mul_le_sum_of_threshold`, `LeanDLRA.KyFan.sum_mul_le_sum_lt`: the
  *bathtub lemma*: if `λ` is antitone, `0 ≤ dᵢ ≤ 1` and `∑ᵢ dᵢ = k`, then
  `∑ᵢ λᵢ dᵢ ≤ ∑_{i < k} λᵢ` (the first version only needs a threshold separating a set `s`
  of indices from its complement).
* `LeanDLRA.KyFan.sum_re_inner_le` (**Ky Fan's maximum principle**) over any `RCLike` field,
  `sum_re_inner_eq_of_apply_eq` and `sum_re_inner_eigenvectorBasis` (equality for eigenvectors),
  and `isGreatest_sum_re_inner` (the maximum over orthonormal `k`-frames).
* Matrix and POD form for real matrices (`open scoped LeanDLRA.Frobenius`):
  `sq_norm_mul_le` (`‖A W‖_F² ≤ ∑_{i < r} λᵢ(Aᵀ A)`), `sq_norm_mul_podBasis` (equality for the
  POD basis `podBasis A hr`), `sq_norm_eq_sum_eigenvalues₀` (`‖A‖_F² = tr (Aᵀ A)`),
  `sq_norm_mul_one_sub` (Pythagoras), `sum_tail_le_sq_norm_mul_one_sub` and
  `sq_norm_mul_one_sub_podBasis` (dominant subspace optimality), and the packaged
  `isGreatest_sq_norm_mul`, `isLeast_sq_norm_mul_one_sub`.

## Connection to dynamical low-rank approximation

* `sum_tail_le_sq_norm_sub_rightProj`, `sum_tail_le_sq_norm_sub_leftProj`,
  `norm_sub_rightProj_podBasis_le`: for the projectors `rightProj V : X ↦ X V Vᵀ` and
  `leftProj U : X ↦ U Uᵀ X` of `LeanDLRA.Matrix.Projectors` (the K- and L-steps of the
  projector-splitting and BUG integrators), no rank-`r` basis captures more than the POD basis.
* `sum_tail_le_sq_norm_sub_of_rank_le`: the Frobenius lower bound of Eckart–Young–Mirsky in
  eigenvalue form, `‖A - Y‖_F² ≥ ∑_{i ≥ r} λᵢ(Aᵀ A)` for `rank Y ≤ r`, derived here from Ky Fan
  (a singular-value treatment is in `LeanDLRA.Classical.EckartYoung`).
* `sum_tail_two_mul_le_sq_norm_normal`: for *any* `U, V` with `r` columns, the normal component
  `(1 - U Uᵀ) X (1 - V Vᵀ)` of `X` (`LeanDLRA.normal_leftProj_rightProj_apply`) satisfies
  `‖(1 - U Uᵀ) X (1 - V Vᵀ)‖_F² ≥ ∑_{i ≥ 2r} λᵢ(Xᵀ X)`.  This is an intrinsic lower bound for the
  modelling error `ε` in the robust error bounds of Kieri–Lubich–Walach and Ceruti–Lubich.
* `exists_rank_le_norm_sub_le_iff`: the truncation criterion of the rank-adaptive BUG integrator
  (Ceruti–Kusch–Lubich, arXiv 2104.05247, §3): a matrix within `ϑ` of rank `≤ r` exists iff the
  eigenvalue tail satisfies `∑_{i ≥ r} λᵢ(Xᵀ X) ≤ ϑ²`; the witness is the POD truncation
  `X W Wᵀ`.

## Implementation notes

* The eigenvalues of `Aᵀ A` are Mathlib's `Matrix.IsHermitian.eigenvalues₀`, indexed by
  `Fin (Fintype.card n)` and sorted decreasingly.  Partial sums are written as sums over the
  finsets `{i | ↑i < r}` (top `r`) and `{i | r ≤ ↑i}` (tail), so no hypothesis `r ≤ card n` is
  needed in the inequalities.
* The bathtub lemma is proved with a threshold `c` separating the top indices from the others:
  `∑ λᵢ dᵢ - ∑_{i ∈ s} λᵢ = ∑ (λᵢ - c)(dᵢ - 𝟙_s(i)) + c (∑ dᵢ - #s)`, a sum of nonpositive terms.
* Ky Fan's principle follows from the bathtub lemma with the weights
  `dᵢ = ∑ⱼ ‖⟪eᵢ, wⱼ⟫‖²`, where `e` is the eigenvector basis: `dᵢ ≤ 1` is Bessel's inequality and
  `∑ᵢ dᵢ = k` is Parseval's identity.
* The matrix statements are only for real matrices, the setting of `LeanDLRA.Frobenius`.

`podBasis` and the symmetry lemmas for `Aᵀ A` are in
`LeanDLRA/LinearAlgebra/Factorization/Defs.lean`.

## References

* Ky Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations I*,
  Proc. Nat. Acad. Sci. USA 35 (1949), 652–655.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Chapter III.
* E. H. Lieb, M. Loss, *Analysis*, 2nd ed., AMS, 2001, §1.14 (bathtub principle).
* K. Kunisch, S. Volkwein, *Galerkin proper orthogonal decomposition methods for parabolic
  problems*, Numer. Math. 90 (2001), 117–148.
* O. Koch, Ch. Lubich, *Dynamical low-rank approximation*, SIAM J. Matrix Anal. Appl. 29 (2007).
* E. Kieri, Ch. Lubich, H. Walach, *Discretized dynamical low-rank approximation in the presence
  of small singular values*, SIAM J. Numer. Anal. 54 (2016).
* G. Ceruti, J. Kusch, Ch. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, BIT 62 (2022), arXiv 2104.05247.
-/

open Finset
open scoped InnerProductSpace ComplexConjugate

namespace LeanDLRA.KyFan

/-! ### The bathtub lemma -/

/-- **Bathtub lemma**, threshold form.  If `λᵢ ≥ c` on `s` and `λᵢ ≤ c` off `s`, and the
weights satisfy `0 ≤ dᵢ ≤ 1` with total mass `∑ dᵢ = #s`, then `∑ λᵢ dᵢ ≤ ∑_{i ∈ s} λᵢ`. -/
theorem sum_mul_le_sum_of_threshold {ι : Type*} [Fintype ι] (s : Finset ι) (lam d : ι → ℝ)
    (c : ℝ) (hs : ∀ i ∈ s, c ≤ lam i) (hsc : ∀ i ∉ s, lam i ≤ c) (h0 : ∀ i, 0 ≤ d i)
    (h1 : ∀ i, d i ≤ 1) (hd : ∑ i, d i = #s) : ∑ i, lam i * d i ≤ ∑ i ∈ s, lam i := by
  classical
  set e : ι → ℝ := fun i => if i ∈ s then 1 else 0 with he
  have hse : ∑ i ∈ s, lam i = ∑ i, lam i * e i := by
    simp [he, mul_ite, Finset.sum_ite_mem]
  have hce : ∑ i, e i = #s := by simp [he]
  have key : ∑ i, lam i * d i - ∑ i, lam i * e i =
      ∑ i, (lam i - c) * (d i - e i) + c * (∑ i, d i - ∑ i, e i) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ i, (lam i - c) * (d i - e i) ≤ 0 := by
    intro i
    by_cases hi : i ∈ s
    · simp only [he, hi, ite_true]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hs i hi]) (by linarith [h1 i])
    · simp only [he, hi, ite_false, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hsc i hi]) (h0 i)
  rw [hse]
  have := Finset.sum_nonpos fun i (_ : i ∈ univ) => hterm i
  rw [hd, hce, sub_self, mul_zero, add_zero] at key
  linarith

/-- **Bathtub lemma.**  Let `λ : Fin n → ℝ` be antitone and `0 ≤ dᵢ ≤ 1` with `∑ dᵢ = k`.
Then `∑ᵢ λᵢ dᵢ ≤ ∑_{i < k} λᵢ`.  (The hypothesis forces `k ≤ n`.) -/
theorem sum_mul_le_sum_lt {n : ℕ} {lam : Fin n → ℝ} (hlam : Antitone lam) {d : Fin n → ℝ}
    (h0 : ∀ i, 0 ≤ d i) (h1 : ∀ i, d i ≤ 1) {k : ℕ} (hd : ∑ i, d i = k) :
    ∑ i, lam i * d i ≤ ∑ i ∈ {i : Fin n | ↑i < k}, lam i := by
  have hkn : k ≤ n := by
    have : ∑ i, d i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    exact_mod_cast hd ▸ this
  have hcard : (#{i : Fin n | ↑i < k} : ℝ) = k := by
    rw [Fin.card_filter_val_lt, min_eq_right hkn]
  by_cases hk : k < n
  · refine sum_mul_le_sum_of_threshold _ lam d (lam ⟨k, hk⟩) (fun i hi => ?_) (fun i hi => ?_)
      h0 h1 (hd.trans hcard.symm)
    · simp only [mem_filter, mem_univ, true_and] at hi
      exact hlam (Fin.mk_le_of_le_val hi.le)
    · simp only [mem_filter, mem_univ, true_and, not_lt] at hi
      exact hlam (Fin.le_iff_val_le_val.mpr hi)
  · refine sum_mul_le_sum_of_threshold _ lam d (-∑ j, |lam j|) (fun i _ => ?_) (fun i hi => ?_)
      h0 h1 (hd.trans hcard.symm)
    · have := Finset.single_le_sum (fun j _ => abs_nonneg (lam j)) (mem_univ i)
      linarith [neg_abs_le (lam i)]
    · simp only [mem_filter, mem_univ, true_and] at hi
      exact absurd (i.2.trans_le (not_lt.mp hk)) hi

/-- Summing over the first `k` elements of `Fin n` via `Fin.castLE` is summing over
`{i | ↑i < k}`. -/
theorem sum_castLE_eq_sum_filter {M : Type*} [AddCommMonoid M] {n k : ℕ} (hk : k ≤ n)
    (f : Fin n → M) : ∑ j : Fin k, f (Fin.castLE hk j) = ∑ i ∈ {i : Fin n | ↑i < k}, f i := by
  rw [show ∑ j : Fin k, f (Fin.castLE hk j) = ∑ i ∈ univ.map (Fin.castLEEmb hk), f i by
    rw [Finset.sum_map]; rfl]
  congr 1
  ext i
  simp only [mem_map, mem_univ, true_and, Fin.castLEEmb_apply, mem_filter]
  exact ⟨fun ⟨j, hj⟩ => hj ▸ j.2, fun hi => ⟨⟨i, hi⟩, rfl⟩⟩

/-! ### Ky Fan's maximum principle -/

section KyFan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} {n : ℕ}

/-- Expansion of the quadratic form of a symmetric operator in its eigenvector basis:
`re ⟪T v, v⟫ = ∑ᵢ λᵢ ‖⟪eᵢ, v⟫‖²`. -/
theorem re_inner_apply_self_eq_sum (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) :
    RCLike.re ⟪T v, v⟫_𝕜 =
      ∑ i, hT.eigenvalues hn i * ‖⟪hT.eigenvectorBasis hn i, v⟫_𝕜‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [← b.sum_inner_mul_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT v (b i), hT.apply_eigenvectorBasis, inner_smul_right, mul_assoc, ← inner_conj_symm v,
    RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- **Ky Fan's maximum principle.**  For a symmetric operator `T` and an orthonormal family
`w : ι → E`, `∑ⱼ re ⟪T wⱼ, wⱼ⟫ ≤ ∑_{i < card ι} λᵢ(T)`. -/
theorem sum_re_inner_le (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {ι : Type*}
    [Fintype ι] {w : ι → E} (hw : Orthonormal 𝕜 w) :
    ∑ j, RCLike.re ⟪T (w j), w j⟫_𝕜 ≤
      ∑ i ∈ {i : Fin n | ↑i < Fintype.card ι}, hT.eigenvalues hn i := by
  set b := hT.eigenvectorBasis hn
  simp_rw [re_inner_apply_self_eq_sum hT hn]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  refine sum_mul_le_sum_lt (hT.eigenvalues_antitone hn)
    (fun i => Finset.sum_nonneg fun j _ => by positivity) (fun i => ?_) ?_
  · calc ∑ j, ‖⟪b i, w j⟫_𝕜‖ ^ 2 = ∑ j, ‖⟪w j, b i⟫_𝕜‖ ^ 2 := by
          simp_rw [norm_inner_symm]
      _ ≤ ‖b i‖ ^ 2 := Orthonormal.sum_inner_products_le (b i) hw
      _ = 1 := by rw [b.norm_eq_one, one_pow]
  · rw [Finset.sum_comm]
    simp_rw [OrthonormalBasis.sum_sq_norm_inner_right, hw.norm_eq_one, one_pow, Finset.sum_const,
      card_univ, nsmul_eq_mul, mul_one]

/-- Equality in Ky Fan's principle: if `w` consists of unit eigenvectors for the top `k`
eigenvalues, then `∑ⱼ re ⟪T wⱼ, wⱼ⟫ = ∑_{i < k} λᵢ(T)`. -/
theorem sum_re_inner_eq_of_apply_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {k : ℕ}
    (hk : k ≤ n) {w : Fin k → E} (hw : ∀ j, ‖w j‖ = 1)
    (hTw : ∀ j, T (w j) = (hT.eigenvalues hn (Fin.castLE hk j) : 𝕜) • w j) :
    ∑ j, RCLike.re ⟪T (w j), w j⟫_𝕜 = ∑ i ∈ {i : Fin n | ↑i < k}, hT.eigenvalues hn i := by
  rw [← sum_castLE_eq_sum_filter hk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hTw, inner_smul_left, inner_self_eq_norm_sq_to_K, hw, RCLike.conj_ofReal]
  simp

/-- Equality in Ky Fan's principle for the first `k` vectors of Mathlib's sorted eigenvector
basis. -/
theorem sum_re_inner_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {k : ℕ} (hk : k ≤ n) :
    ∑ j : Fin k, RCLike.re ⟪T (hT.eigenvectorBasis hn (Fin.castLE hk j)),
        hT.eigenvectorBasis hn (Fin.castLE hk j)⟫_𝕜 =
      ∑ i ∈ {i : Fin n | ↑i < k}, hT.eigenvalues hn i :=
  sum_re_inner_eq_of_apply_eq hT hn hk (fun _ => (hT.eigenvectorBasis hn).norm_eq_one _)
    fun _ => hT.apply_eigenvectorBasis hn _

/-- **Ky Fan's maximum principle**, extremal form: the maximum of `∑ⱼ re ⟪T wⱼ, wⱼ⟫` over
orthonormal `k`-frames is the sum of the `k` largest eigenvalues. -/
theorem isGreatest_sum_re_inner (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {k : ℕ}
    (hk : k ≤ n) :
    IsGreatest {s | ∃ w : Fin k → E, Orthonormal 𝕜 w ∧ s = ∑ j, RCLike.re ⟪T (w j), w j⟫_𝕜}
      (∑ i ∈ {i : Fin n | ↑i < k}, hT.eigenvalues hn i) := by
  refine ⟨⟨_, (hT.eigenvectorBasis hn).orthonormal.comp _ (Fin.castLE_injective hk),
    (sum_re_inner_eigenvectorBasis hT hn hk).symm⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  simpa using sum_re_inner_le hT hn hw

end KyFan

/-! ### Matrix form: POD optimality -/

section Matrix

open scoped Matrix LeanDLRA.Frobenius

variable {m n ι : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/- `isHermitian_transpose_mul_self`, `isSymmetric_toEuclideanLin_transpose_mul_self` and
`podBasis` are in `LeanDLRA/LinearAlgebra/Factorization/Defs.lean`. -/

/-- `eigenvalues₀` of `Aᵀ A` are the sorted eigenvalues of the symmetric operator `Aᵀ A`. -/
theorem eigenvalues₀_eq (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) :
    hA.eigenvalues₀ = (isSymmetric_toEuclideanLin_transpose_mul_self A).eigenvalues
      finrank_euclideanSpace := rfl

omit [DecidableEq ι] in
/-- The squared Frobenius norm of `A W` is the sum of the quadratic forms of `Aᵀ A` at the
columns of `W`: `‖A W‖_F² = ∑ⱼ ⟪Aᵀ A wⱼ, wⱼ⟫`. -/
theorem sq_norm_mul_eq_sum_inner (A : Matrix m n ℝ) (W : Matrix n ι ℝ) :
    ‖A * W‖ ^ 2 = ∑ j, ⟪Matrix.toEuclideanLin (Aᵀ * A) (WithLp.toLp 2 (W.col j)),
      WithLp.toLp 2 (W.col j)⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, ← Matrix.mul_assoc,
    Frobenius.inner_def, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.toLpLin_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    mul_comm]

omit [DecidableEq n] [Fintype ι] in
/-- A matrix with `Wᵀ W = 1` has orthonormal columns. -/
theorem orthonormal_toLp_col {W : Matrix n ι ℝ} (hW : Wᵀ * W = 1) :
    Orthonormal ℝ fun j => WithLp.toLp 2 (W.col j) :=
  orthonormal_iff_ite.mpr fun j l => by rw [inner_toLp_col_col, hW, Matrix.one_apply]

/-- **Ky Fan, matrix form.**  If `Wᵀ W = 1`, then `‖A W‖_F² ≤ ∑_{i < card ι} λᵢ(Aᵀ A)`:
no orthonormal frame captures more energy of `A` than the dominant eigenvectors of `Aᵀ A`. -/
theorem sq_norm_mul_le (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) {W : Matrix n ι ℝ}
    (hW : Wᵀ * W = 1) :
    ‖A * W‖ ^ 2 ≤ ∑ i ∈ {i : Fin (Fintype.card n) | ↑i < Fintype.card ι}, hA.eigenvalues₀ i := by
  rw [sq_norm_mul_eq_sum_inner, eigenvalues₀_eq]
  simpa using sum_re_inner_le (isSymmetric_toEuclideanLin_transpose_mul_self A)
    finrank_euclideanSpace (orthonormal_toLp_col hW)

/-- Equality in the matrix Ky Fan inequality: if `Wᵀ W = 1` and `Aᵀ A W = W Λ` with `Λ` the
diagonal of the top `r` eigenvalues, then `‖A W‖_F² = ∑_{i < r} λᵢ(Aᵀ A)`. -/
theorem sq_norm_mul_eq_of_mul_eq_mul_diagonal (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian)
    {r : ℕ} (hr : r ≤ Fintype.card n) {W : Matrix n (Fin r) ℝ} (hW : Wᵀ * W = 1)
    (hAW : Aᵀ * A * W = W * Matrix.diagonal fun j => hA.eigenvalues₀ (Fin.castLE hr j)) :
    ‖A * W‖ ^ 2 = ∑ i ∈ {i : Fin (Fintype.card n) | ↑i < r}, hA.eigenvalues₀ i := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, ← Matrix.mul_assoc, hAW,
    Frobenius.inner_mul_left', hW, Frobenius.inner_def, ← sum_castLE_eq_sum_filter hr]
  simp [Matrix.one_apply, Matrix.diagonal_apply]

/-- The POD basis has orthonormal columns. -/
theorem transpose_podBasis_mul_podBasis (A : Matrix m n ℝ) {r : ℕ} (hr : r ≤ Fintype.card n) :
    (podBasis A hr)ᵀ * podBasis A hr = 1 :=
  transpose_ofCols_mul_ofCols <|
    (OrthonormalBasis.orthonormal _).comp _ (Fin.castLE_injective hr)

/-- The POD basis consists of eigenvectors: `Aᵀ A W = W diag(λ₀, …, λ_{r-1})`. -/
theorem transpose_mul_self_mul_podBasis (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) {r : ℕ}
    (hr : r ≤ Fintype.card n) :
    Aᵀ * A * podBasis A hr =
      podBasis A hr * Matrix.diagonal fun j => hA.eigenvalues₀ (Fin.castLE hr j) := by
  ext i j
  have := congrArg (fun v : EuclideanSpace ℝ n => v i)
    ((isSymmetric_toEuclideanLin_transpose_mul_self A).apply_eigenvectorBasis
      finrank_euclideanSpace (Fin.castLE hr j))
  simp only [Matrix.toLpLin_apply, PiLp.smul_apply, smul_eq_mul, RCLike.ofReal_real_eq_id,
    id_eq] at this
  rw [Matrix.mul_diagonal, eigenvalues₀_eq, mul_comm]
  convert this using 1
  · simp [podBasis, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · rfl

/-- The POD basis captures the energy `‖A W‖_F² = ∑_{i < r} λᵢ(Aᵀ A)`. -/
theorem sq_norm_mul_podBasis (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) {r : ℕ}
    (hr : r ≤ Fintype.card n) :
    ‖A * podBasis A hr‖ ^ 2 = ∑ i ∈ {i : Fin (Fintype.card n) | ↑i < r}, hA.eigenvalues₀ i :=
  sq_norm_mul_eq_of_mul_eq_mul_diagonal A hA hr (transpose_podBasis_mul_podBasis A hr)
    (transpose_mul_self_mul_podBasis A hA hr)

/-- `‖A‖_F² = tr (Aᵀ A) = ∑ᵢ λᵢ(Aᵀ A)`. -/
theorem sq_norm_eq_sum_eigenvalues₀ (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) :
    ‖A‖ ^ 2 = ∑ i, hA.eigenvalues₀ i := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hA.trace_eq_sum_eigenvalues]
  simp only [Matrix.IsHermitian.eigenvalues, RCLike.ofReal_real_eq_id, id_eq]
  exact Equiv.sum_comp _ _

/-- Pythagoras for the right projector `W Wᵀ`: if `Wᵀ W = 1`, then
`‖A (1 - W Wᵀ)‖_F² = ‖A‖_F² - ‖A W‖_F²`. -/
theorem sq_norm_mul_one_sub (A : Matrix m n ℝ) {W : Matrix n ι ℝ} (hW : Wᵀ * W = 1) :
    ‖A * (1 - W * Wᵀ)‖ ^ 2 = ‖A‖ ^ 2 - ‖A * W‖ ^ 2 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, norm_sub_sq_real,
    Frobenius.inner_mul_right', Matrix.transpose_transpose, real_inner_self_eq_norm_sq,
    Frobenius.norm_mul_transpose_of_orthonormal hW]
  ring

/-- **Dominant subspace optimality.**  If `Wᵀ W = 1`, the projection error satisfies
`‖A (1 - W Wᵀ)‖_F² ≥ ∑_{i ≥ card ι} λᵢ(Aᵀ A)`. -/
theorem sum_tail_le_sq_norm_mul_one_sub (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian)
    {W : Matrix n ι ℝ} (hW : Wᵀ * W = 1) :
    ∑ i ∈ {i : Fin (Fintype.card n) | Fintype.card ι ≤ ↑i}, hA.eigenvalues₀ i ≤
      ‖A * (1 - W * Wᵀ)‖ ^ 2 := by
  rw [sq_norm_mul_one_sub A hW, sq_norm_eq_sum_eigenvalues₀ A hA,
    ← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin _ => ↑i < Fintype.card ι)]
  simp only [not_lt]
  linarith [sq_norm_mul_le A hA hW]

/-- The POD basis attains the dominant subspace bound:
`‖A (1 - W Wᵀ)‖_F² = ∑_{i ≥ r} λᵢ(Aᵀ A)`. -/
theorem sq_norm_mul_one_sub_podBasis (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) {r : ℕ}
    (hr : r ≤ Fintype.card n) :
    ‖A * (1 - podBasis A hr * (podBasis A hr)ᵀ)‖ ^ 2 =
      ∑ i ∈ {i : Fin (Fintype.card n) | r ≤ ↑i}, hA.eigenvalues₀ i := by
  rw [sq_norm_mul_one_sub A (transpose_podBasis_mul_podBasis A hr), sq_norm_mul_podBasis A hA hr,
    sq_norm_eq_sum_eigenvalues₀ A hA,
    ← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin _ => ↑i < r)]
  simp only [not_lt]
  ring

/-- **POD optimality**, maximal captured energy: the largest value of `‖A W‖_F²` over
`W ∈ ℝ^{n × r}` with `Wᵀ W = 1` is `∑_{i < r} λᵢ(Aᵀ A)`. -/
theorem isGreatest_sq_norm_mul (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) {r : ℕ}
    (hr : r ≤ Fintype.card n) :
    IsGreatest {s | ∃ W : Matrix n (Fin r) ℝ, Wᵀ * W = 1 ∧ s = ‖A * W‖ ^ 2}
      (∑ i ∈ {i : Fin (Fintype.card n) | ↑i < r}, hA.eigenvalues₀ i) := by
  refine ⟨⟨podBasis A hr, transpose_podBasis_mul_podBasis A hr,
    (sq_norm_mul_podBasis A hA hr).symm⟩, ?_⟩
  rintro _ ⟨W, hW, rfl⟩
  simpa using sq_norm_mul_le A hA hW

/-- **POD optimality**, minimal projection error: the smallest value of
`‖A (1 - W Wᵀ)‖_F²` over `W ∈ ℝ^{n × r}` with `Wᵀ W = 1` is `∑_{i ≥ r} λᵢ(Aᵀ A)`. -/
theorem isLeast_sq_norm_mul_one_sub (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian) {r : ℕ}
    (hr : r ≤ Fintype.card n) :
    IsLeast {s | ∃ W : Matrix n (Fin r) ℝ, Wᵀ * W = 1 ∧ s = ‖A * (1 - W * Wᵀ)‖ ^ 2}
      (∑ i ∈ {i : Fin (Fintype.card n) | r ≤ ↑i}, hA.eigenvalues₀ i) := by
  refine ⟨⟨podBasis A hr, transpose_podBasis_mul_podBasis A hr,
    (sq_norm_mul_one_sub_podBasis A hA hr).symm⟩, ?_⟩
  rintro _ ⟨W, hW, rfl⟩
  simpa using sum_tail_le_sq_norm_mul_one_sub A hA hW

end Matrix

/-! ### Connection to dynamical low-rank approximation -/

section DLRA

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The error of the right projector: `X - X V Vᵀ = X (1 - V Vᵀ)`. -/
theorem sub_rightProj_apply {ι : Type*} [Fintype ι] (X : Matrix m n ℝ) (V : Matrix n ι ℝ) :
    X - rightProj V X = X * (1 - V * Vᵀ) := by
  rw [rightProj_apply, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]

/-- Lower bound for the error of every right projector of rank `r` (the L-step bases of the
DLRA integrators): `‖X - X V Vᵀ‖_F² ≥ ∑_{i ≥ r} λᵢ(Xᵀ X)`. -/
theorem sum_tail_le_sq_norm_sub_rightProj (X : Matrix m n ℝ) (hX : (Xᵀ * X).IsHermitian) {r : ℕ}
    {V : Matrix n (Fin r) ℝ} (hV : Vᵀ * V = 1) :
    ∑ i ∈ {i : Fin (Fintype.card n) | r ≤ ↑i}, hX.eigenvalues₀ i ≤ ‖X - rightProj V X‖ ^ 2 := by
  rw [sub_rightProj_apply]
  simpa using sum_tail_le_sq_norm_mul_one_sub X hX hV

/-- The right projector onto the POD basis attains the lower bound. -/
theorem sq_norm_sub_rightProj_podBasis (X : Matrix m n ℝ) (hX : (Xᵀ * X).IsHermitian) {r : ℕ}
    (hr : r ≤ Fintype.card n) :
    ‖X - rightProj (podBasis X hr) X‖ ^ 2 =
      ∑ i ∈ {i : Fin (Fintype.card n) | r ≤ ↑i}, hX.eigenvalues₀ i := by
  rw [sub_rightProj_apply]
  exact sq_norm_mul_one_sub_podBasis X hX hr

/-- **Quasi-optimality with constant `1`**: the POD basis is a best right basis of rank `r`. -/
theorem norm_sub_rightProj_podBasis_le (X : Matrix m n ℝ) {r : ℕ} (hr : r ≤ Fintype.card n)
    {V : Matrix n (Fin r) ℝ} (hV : Vᵀ * V = 1) :
    ‖X - rightProj (podBasis X hr) X‖ ≤ ‖X - rightProj V X‖ := by
  have hX := isHermitian_transpose_mul_self X
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [sq_norm_sub_rightProj_podBasis X hX hr]
  exact sum_tail_le_sq_norm_sub_rightProj X hX hV

/-- **Eckart–Young–Mirsky lower bound** (Frobenius norm, eigenvalue form), from Ky Fan:
every `Y` with `rank Y ≤ r` satisfies `‖A - Y‖_F² ≥ ∑_{i ≥ r} λᵢ(Aᵀ A)`. -/
theorem sum_tail_le_sq_norm_sub_of_rank_le (A : Matrix m n ℝ) (hA : (Aᵀ * A).IsHermitian)
    {r : ℕ} {Y : Matrix m n ℝ} (hY : Y.rank ≤ r) :
    ∑ i ∈ {i : Fin (Fintype.card n) | r ≤ ↑i}, hA.eigenvalues₀ i ≤ ‖A - Y‖ ^ 2 := by
  by_cases hr : r ≤ Fintype.card n
  · obtain ⟨V, hV, hcap⟩ := exists_orthonormal_capture Yᵀ (by rwa [Matrix.rank_transpose]) hr
    have hYV : Y * (V * Vᵀ) = Y := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hcap
    have hsplit : (A - Y) * (1 - V * Vᵀ) = A * (1 - V * Vᵀ) := by
      rw [Matrix.sub_mul, Matrix.mul_sub Y, Matrix.mul_one, hYV, sub_self, sub_zero]
    calc _ ≤ ‖A * (1 - V * Vᵀ)‖ ^ 2 := by simpa using sum_tail_le_sq_norm_mul_one_sub A hA hV
      _ = ‖(A - Y) * (1 - V * Vᵀ)‖ ^ 2 := by rw [hsplit]
      _ ≤ ‖A - Y‖ ^ 2 := by
        rw [sq_norm_mul_one_sub _ hV]
        linarith [sq_nonneg ‖(A - Y) * V‖]
  · rw [Finset.sum_eq_zero fun i hi => ?_]
    · positivity
    · simp only [mem_filter, mem_univ, true_and] at hi
      exact (hr (hi.trans i.2.le)).elim

/-- **Lower bound for the normal component.**  For arbitrary `U ∈ ℝ^{m × r}` and
`V ∈ ℝ^{n × r}`, the normal component `(1 - U Uᵀ) X (1 - V Vᵀ)` satisfies
`‖(1 - U Uᵀ) X (1 - V Vᵀ)‖_F² ≥ ∑_{i ≥ 2r} λᵢ(Xᵀ X)`, since `X` minus it has rank `≤ 2r`.  Hence
the tolerance `ε` of the robust DLRA error bounds can never be below this tail. -/
theorem sum_tail_two_mul_le_sq_norm_normal (X : Matrix m n ℝ) (hX : (Xᵀ * X).IsHermitian)
    {r : ℕ} (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) :
    ∑ i ∈ {i : Fin (Fintype.card n) | 2 * r ≤ ↑i}, hX.eigenvalues₀ i ≤
      ‖normal (leftProj U) (rightProj V) X‖ ^ 2 := by
  classical
  rw [normal_leftProj_rightProj_apply]
  have h : (1 - U * Uᵀ) * X * (1 - V * Vᵀ) =
      X - (U * (Uᵀ * X) + (X * V - U * (Uᵀ * X * V)) * Vᵀ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [h]
  exact sum_tail_le_sq_norm_sub_of_rank_le X hX (rank_mul_add_mul_transpose_le _ _ _ _)

omit [DecidableEq n] in
/-- Lower bound for the error of every left projector of rank `r` (the K-step bases of the
DLRA integrators): `‖X - U Uᵀ X‖_F² ≥ ∑_{i ≥ r} λᵢ(X Xᵀ)`. -/
theorem sum_tail_le_sq_norm_sub_leftProj [DecidableEq m] (X : Matrix m n ℝ)
    (hX : (X * Xᵀ).IsHermitian) {r : ℕ} {U : Matrix m (Fin r) ℝ} (hU : Uᵀ * U = 1) :
    ∑ i ∈ {i : Fin (Fintype.card m) | r ≤ ↑i}, hX.eigenvalues₀ i ≤ ‖X - leftProj U X‖ ^ 2 := by
  have h : X - leftProj U X = (Xᵀ - rightProj U Xᵀ)ᵀ := by
    simp [leftProj_apply, rightProj_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h, Frobenius.norm_transpose]
  exact sum_tail_le_sq_norm_sub_rightProj Xᵀ hX hU

omit [DecidableEq n] in
/-- A right projection onto `r` columns has rank at most `r`. -/
theorem rank_rightProj_le {r : ℕ} (V : Matrix n (Fin r) ℝ) (X : Matrix m n ℝ) :
    (rightProj V X).rank ≤ r :=
  (Matrix.rank_mul_le_right _ _).trans (by simpa using Vᵀ.rank_le_card_height)

/-- **Rank truncation criterion** (rank-adaptive BUG, Ceruti–Kusch–Lubich, arXiv 2104.05247):
there is a matrix of rank `≤ r` within `ϑ` of `X` iff `∑_{i ≥ r} λᵢ(Xᵀ X) ≤ ϑ²`; the POD
truncation `X W Wᵀ` is such a matrix. -/
theorem exists_rank_le_norm_sub_le_iff (X : Matrix m n ℝ) (hX : (Xᵀ * X).IsHermitian) {r : ℕ}
    {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    (∃ Y : Matrix m n ℝ, Y.rank ≤ r ∧ ‖X - Y‖ ≤ ϑ) ↔
      ∑ i ∈ {i : Fin (Fintype.card n) | r ≤ ↑i}, hX.eigenvalues₀ i ≤ ϑ ^ 2 := by
  constructor
  · rintro ⟨Y, hY, hXY⟩
    exact (sum_tail_le_sq_norm_sub_of_rank_le X hX hY).trans
      (pow_le_pow_left₀ (norm_nonneg _) hXY 2)
  · intro h
    by_cases hr : r ≤ Fintype.card n
    · refine ⟨rightProj (podBasis X hr) X, rank_rightProj_le _ _, ?_⟩
      refine (sq_le_sq₀ (norm_nonneg _) hϑ).mp ?_
      rwa [sq_norm_sub_rightProj_podBasis X hX hr]
    · exact ⟨X, X.rank_le_card_width.trans (not_le.mp hr).le, by simpa using hϑ⟩

end DLRA

end LeanDLRA.KyFan
