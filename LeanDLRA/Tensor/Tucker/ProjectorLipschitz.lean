import LeanDLRA.Tensor.Tucker.TangentNormal
import LeanDLRA.FixedRank.TangentSpace.ProjectorLipschitz

/-!
# A Lipschitz bound of the tangent projector of the Tucker manifold

Let `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` be Tucker tensors with `d` modes and the same multilinear
rank, with tangent projectors `P(X)`, `P(Y)` (`tuckerTangentProj` with the core projector `1`,
[BachmayrEisenmannUschmajew2025, Prop. 4.2]), and let `0 < ρ` be a lower bound of the smallest
nonzero singular values of the `d` matricizations of `X`. This file shows

  `‖P(Y) B - P(X) B‖ ≤ √d ρ⁻¹ ‖Y - X‖ ‖B‖`

for all tensors `B`, in Frobenius norms, without a smallness condition on `‖Y - X‖` and with the
lower bound `ρ` at `X` only, together with the two bounds it is made of: `‖Z - P(Y) Z‖ ≤
√d ρ⁻¹ ‖Y - X‖ ‖Z‖` for `Z` tangent at `X`, and `‖P(X) N‖ ≤ √d ρ⁻¹ ‖Y - X‖ ‖N‖` for `N` normal
at `Y`.

For `d` modes the bound of [BachmayrEisenmannUschmajew2025, Prop. 4.7] (also global, in the
operator norm, for constrained core manifolds) has the constant `2 (√2 + 1) d` for the Tucker
manifold. The constant `√d` is not claimed to be optimal: for matrices (`d = 2`) the optimal
constant is `1` (`norm_tangentProjAt_sub_le_inv_mul`), and `√2` is obtained here.

## Main results

* `LeanDLRA.norm_sub_tangentProjAt_apply_le_of_tangentProjAt_eq_self`,
  `LeanDLRA.norm_sub_tangentProjAt_apply_le_of_tangentProjAt_eq_self_symm`: for matrices `X`, `Y`
  of rank `r`, the normal component at `Y` of a tangent vector at `X`, and the normal component
  at `X` of a tangent vector at `Y`, are at most `ρ⁻¹ ‖Y - X‖` times the vector (`ρ` at `X`).
* `LeanDLRA.rangeProj_eq_mul_transpose_of_rank_eq`: `U Uᵀ` is the column-space projector of `A`
  if it fixes `A` and `A` has as many independent columns as `U` has columns.
* `LeanDLRA.Tensor.unfold_ne_modeAct`: a mode-`k` action multiplies the unfolding with respect
  to the other modes from the right.
* `LeanDLRA.Tensor.unfold_ne_one_sub_modeProj_coRange`: in the unfolding with respect to the
  modes `≠ k`, the map `(1 - P_{Uₖ}) (1 - Q_k)` is the normal projector of the manifold of
  matrices of fixed rank at the unfolding of `X`.
* `LeanDLRA.Tensor.norm_sub_tuckerTangentProj_apply_le_of_eq_self`,
  `LeanDLRA.Tensor.norm_tuckerTangentProj_apply_le_of_eq_zero`,
  `LeanDLRA.Tensor.norm_tuckerTangentProj_sub_le`: the three bounds with the constant `√d`.

## Implementation notes

The matricization used is `unfold (· ≠ k)` (rows: the modes `≠ k`, columns: mode `k`), the
transpose of the mode-`k` matricization, because the co-range projectors `actOn (· ≠ k) (W Wᵀ)`
of `tuckerTangentProj` act on its rows. The tangent space of the Tucker manifold at `X` is the
intersection of the tangent spaces of the `d` manifolds of matrices of fixed rank at the
matricizations, and the normal component of a vector is bounded by its `d` normal components
with respect to these (`norm_sq_sub_modeTangentProj_apply_le`). The matrix bound with the
constant `1` in each mode gives the factor `√d`.

## References

* [BachmayrEisenmannUschmajew2025, Props. 4.2 and 4.7]
-/

open Matrix
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### Matrices: normal components of tangent vectors -/

section MatrixTangentNormal

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The normal component at `Y` of a tangent vector at `X`, two matrices of rank `r`.** For
`X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and `P(X) Z = Z`:
`‖Z - P(Y) Z‖ ≤ ρ⁻¹ ‖Y - X‖ ‖Z‖`. -/
theorem norm_sub_tangentProjAt_apply_le_of_tangentProjAt_eq_self {r : ℕ} {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {Z : Matrix m n ℝ}
    (hZ : tangentProjAt X Z = Z) : ‖Z - tangentProjAt Y Z‖ ≤ ρ⁻¹ * ‖Y - X‖ * ‖Z‖ := by
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  rw [tangentProjAt_eq_tangentProj hU hV hS]
  have h := norm_one_sub_tangentProj_apply_le_of_tangentProjAt_eq_self hX hρ hσ hU hV S hZ
  rwa [sub_apply, one_apply_eq_self] at h

/-- **The normal component at `X` of a tangent vector at `Y`, two matrices of rank `r`.** For
`X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)` and `P(Y) Z = Z`:
`‖Z - P(X) Z‖ ≤ ρ⁻¹ ‖Y - X‖ ‖Z‖`. The lower bound `ρ` is needed at `X` only. -/
theorem norm_sub_tangentProjAt_apply_le_of_tangentProjAt_eq_self_symm {r : ℕ}
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) {Z : Matrix m n ℝ}
    (hZ : tangentProjAt Y Z = Z) : ‖Z - tangentProjAt X Z‖ ≤ ρ⁻¹ * ‖Y - X‖ * ‖Z‖ := by
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  refine (isOrthProj_tangentProjAt X).norm_sub_apply_le_of_norm_apply_le
    (isOrthProj_tangentProjAt _) (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _))
    (fun N hN => ?_) hZ
  rw [tangentProjAt_eq_tangentProj hU hV hS]
  exact norm_tangentProj_apply_le_of_tangentProjAt_eq_zero hX hρ hσ hU hV S hN

omit [DecidableEq n] in
/-- **The column-space projector from a basis and the rank.** If `U Uᵀ` fixes the columns of `A`
and the rank of `A` is the number of columns of `U`, then `U Uᵀ` is the column-space projector
of `A`: the columns of `U` then lie in the column space of `A`. -/
theorem rangeProj_eq_mul_transpose_of_rank_eq {k : Type*} [Fintype k]
    {A : Matrix m n ℝ} {U : Matrix m k ℝ} (hfix : U * Uᵀ * A = A)
    (hr : A.rank = Fintype.card k) : A.rangeProj = U * Uᵀ := by
  classical
  have hG : (Uᵀ * A).rank = Fintype.card k := by
    refine le_antisymm (rank_le_card_height _) ?_
    calc Fintype.card k = (U * (Uᵀ * A)).rank := by rw [← Matrix.mul_assoc, hfix, hr]
      _ ≤ (Uᵀ * A).rank := rank_mul_le_right _ _
  have hsurj : Function.Surjective (Uᵀ * A).mulVecLin := by
    rw [← LinearMap.range_eq_top]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Module.finrank_pi]
    exact hG
  choose v hv using fun i : k => hsurj (Pi.single i 1)
  have hN : Uᵀ * A * Matrix.of (fun a i => v i a) = 1 := by
    ext i j
    have h1 : (Uᵀ * A * Matrix.of (fun a i => v i a)) i j = (Uᵀ * A).mulVecLin (v j) i := rfl
    rw [h1, hv j, Matrix.one_apply, Pi.single_apply]
  refine Matrix.rangeProj_eq_of_capture (C := Matrix.of fun a i => v i a) hfix ?_
  calc U = U * (Uᵀ * A * Matrix.of (fun a i => v i a)) := by rw [hN, Matrix.mul_one]
    _ = U * Uᵀ * A * Matrix.of (fun a i => v i a) := by simp only [Matrix.mul_assoc]
    _ = A * Matrix.of (fun a i => v i a) := by rw [hfix]

end MatrixTangentNormal

namespace Tensor

/-! ### The unfolding with respect to the other modes -/

section UnfoldMode

variable {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)]

/-- **A mode-`k` action in the unfolding with respect to the other modes**: `X ×ₖ A` is
multiplication of `Mat_{≠k}(X)` (rows: the modes `≠ k`, columns: mode `k`) by `Aᵀ` from the
right. -/
theorem unfold_ne_modeAct (k : Fin d) (A : Matrix (ι k) (ι k) ℝ) (Z : Tensor ι) :
    unfold (· ≠ k) (modeAct k A Z) =
      unfold (· ≠ k) Z * Aᵀ.submatrix (compEquiv k) (compEquiv k) := by
  ext a b
  rw [unfold_apply, modeAct_apply, Matrix.mul_apply]
  have hk : merge (· ≠ k) a b k = compEquiv k b := by simp [merge, compEquiv]
  refine (Fintype.sum_equiv (compEquiv k) _ _ fun b' => ?_).symm
  rw [unfold_apply, Matrix.submatrix_apply, Matrix.transpose_apply, hk, ← merge_compEquiv_symm,
    restrict_merge, Equiv.symm_apply_apply, mul_comm]

variable {r : Fin d → Type*} [∀ k, Fintype (r k)] [∀ k, DecidableEq (r k)]
  {U : ∀ k, Matrix (ι k) (r k) ℝ} {C : Tensor r}

/-- **The row-space projector of the unfolding of a Tucker tensor.** If `X = C ×ⱼ Uⱼ` with
orthonormal `Uₖ` and the unfolding `Mat_{≠k}(X)` has rank equal to the number of columns of `Uₖ`,
then `Uₖ Uₖᵀ` is the projector onto the row space of `Mat_{≠k}(X)`. -/
theorem rangeProj_transpose_unfold_ne_tucker {k : Fin d} (hU : (U k)ᵀ * U k = 1)
    (hr : (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (r k)) :
    (unfold (· ≠ k) (tucker C U))ᵀ.rangeProj =
      (U k * (U k)ᵀ).submatrix (compEquiv k) (compEquiv k) := by
  have hsub : (U k * (U k)ᵀ).submatrix (compEquiv k) (compEquiv k) =
      (U k).submatrix (compEquiv k) id * ((U k).submatrix (compEquiv k) id)ᵀ := by
    ext a b
    simp [Matrix.mul_apply]
  have hAR : unfold (· ≠ k) (tucker C U) *
      (U k * (U k)ᵀ).submatrix (compEquiv k) (compEquiv k) = unfold (· ≠ k) (tucker C U) := by
    have h := unfold_ne_modeAct k (U k * (U k)ᵀ) (tucker C U)
    rw [Matrix.transpose_mul, Matrix.transpose_transpose] at h
    rw [← h]
    exact congrArg _ (modeProj_tucker k hU C)
  rw [hsub] at hAR ⊢
  refine rangeProj_eq_mul_transpose_of_rank_eq ?_ (by rw [Matrix.rank_transpose]; exact hr)
  have h := congrArg Matrix.transpose hAR
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h

/-- **The mode-`k` normal projector in the unfolding.** Let `X = C ×ⱼ Uⱼ` with orthonormal `Uₖ`,
let the columns of `W` lie in the column space of `Mat_{≠k}(X)` with `W Wᵀ` fixing it, and let
`Mat_{≠k}(X)` have rank equal to the number of columns of `Uₖ`. Then, in the unfolding with
respect to the modes `≠ k`, the map `(1 - P_{Uₖ}) (1 - Q_k)` with `Q_k = actOn (· ≠ k) (W Wᵀ)`
is `1 - P` for the tangent projector `P` of the manifold of matrices of fixed rank at
`Mat_{≠k}(X)`. -/
theorem unfold_ne_one_sub_modeProj_coRange {k : Fin d} {s : Type*} [Fintype s]
    {W : Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) s ℝ} (hU : (U k)ᵀ * U k = 1)
    (hWX : actOn (· ≠ k) (W * Wᵀ) (tucker C U) = tucker C U)
    (hWB : ∃ B : Matrix _ s ℝ, W = unfold (· ≠ k) (tucker C U) * B)
    (hr : (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (r k)) (Z : Tensor ι) :
    unfold (· ≠ k) ((1 - modeProj k (U k)) (Z - actOn (· ≠ k) (W * Wᵀ) Z)) =
      unfold (· ≠ k) Z - tangentProjAt (unfold (· ≠ k) (tucker C U)) (unfold (· ≠ k) Z) := by
  obtain ⟨B, hB⟩ := hWB
  have hQ : (unfold (· ≠ k) (tucker C U)).rangeProj = W * Wᵀ :=
    Matrix.rangeProj_eq_of_capture (by rw [← unfold_actOn, hWX]) hB
  rw [tangentProjAt_apply, hQ, rangeProj_transpose_unfold_ne_tucker hU hr, sub_apply,
    one_apply_eq_self, unfold_sub, modeProj, unfold_ne_modeAct, unfold_sub, unfold_actOn,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.sub_mul]
  abel

omit [∀ k, DecidableEq (r k)] in
/-- The co-range map `actOn (· ≠ k) (W Wᵀ)` is an orthogonal projector if the columns of `W`
lie in the column space of `Mat_{≠k}(X)` and `W Wᵀ` fixes `X`. -/
theorem isOrthProj_coRangeProj_of_capture {k : Fin d} {s : Type*} [Fintype s]
    {W : Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) s ℝ} {X : Tensor ι}
    (hWX : actOn (· ≠ k) (W * Wᵀ) X = X)
    (hWB : ∃ B : Matrix _ s ℝ, W = unfold (· ≠ k) X * B) :
    IsOrthProj (actOn (· ≠ k) (W * Wᵀ)) := by
  obtain ⟨B, hB⟩ := hWB
  have hQ : (unfold (· ≠ k) X).rangeProj = W * Wᵀ :=
    Matrix.rangeProj_eq_of_capture (by rw [← unfold_actOn, hWX]) hB
  rw [← hQ]
  exact isOrthProj_actOn _ (Matrix.rangeProj_mul_rangeProj _) (Matrix.transpose_rangeProj _)

/-- The co-range projector of mode `i` maps into the range of the mode projector of every
other mode `j`: `P_{Uⱼ} Q_i = Q_i` for `j ≠ i`. -/
theorem modeProj_coRangeProj_of_ne {i j : Fin d} (hji : j ≠ i) (hU : (U j)ᵀ * U j = 1)
    {s : Type*} [Fintype s] {W : Matrix (∀ l : {l : Fin d // l ≠ i}, ι l) s ℝ}
    (hWB : ∃ B : Matrix _ s ℝ, W = unfold (· ≠ i) (tucker C U) * B) (x : Tensor ι) :
    modeProj j (U j) (actOn (· ≠ i) (W * Wᵀ) x) = actOn (· ≠ i) (W * Wᵀ) x := by
  obtain ⟨B, hB⟩ := hWB
  have e := (congrArg (· * Wᵀ) hB).trans (Matrix.mul_assoc _ B Wᵀ)
  have h := (congrArg (fun M => actOn (· ≠ i) M x) e).trans
    (actOn_unfold_mul i (tucker C U) x _)
  exact (congrArg (modeProj j (U j)) h).trans
    (((modeAct_comm hji (U j * (U j)ᵀ) _ (tucker C U)).trans
      (congrArg _ (modeProj_tucker j hU C))).trans h.symm)

end UnfoldMode

/-! ### The Lipschitz bound -/

section ProjectorLipschitz

variable {d : ℕ} {ι r : Fin d → Type*} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]
  [∀ k, Fintype (r k)] [∀ k, DecidableEq (r k)] {U U' : ∀ k, Matrix (ι k) (r k) ℝ}
  {C C' : Tensor r} {s s' : Fin d → Type*} [∀ k, Fintype (s k)] [∀ k, Fintype (s' k)]
  {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ}
  {W' : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s' k) ℝ}

omit [∀ k, DecidableEq (ι k)] in
/-- The mode projectors and the co-range projectors of a Tucker tensor satisfy the hypotheses
of `modeTangentProj_isOrthProj`. -/
private theorem tuckerFrame (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) :
    (∀ k, IsOrthProj (modeProj k (U k))) ∧
      (∀ k, IsOrthProj (actOn (· ≠ k) (W k * (W k)ᵀ) : Tensor ι →L[ℝ] Tensor ι)) ∧
      (∀ i j (x : Tensor ι), modeProj i (U i) (modeProj j (U j) x) =
        modeProj j (U j) (modeProj i (U i) x)) ∧
      (∀ i (x : Tensor ι), actOn (· ≠ i) (W i * (W i)ᵀ) (modeProj i (U i) x) =
        modeProj i (U i) (actOn (· ≠ i) (W i * (W i)ᵀ) x)) ∧
      ∀ i j, j ≠ i → ∀ x : Tensor ι,
        modeProj j (U j) (actOn (· ≠ i) (W i * (W i)ᵀ) x) = actOn (· ≠ i) (W i * (W i)ᵀ) x :=
  ⟨fun k => isOrthProj_modeProj k (hU k),
    fun k => isOrthProj_coRangeProj_of_capture (hWX k) (hWB k), modeProj_comm_family U,
    fun i x => (modeProj_comm_coRangeProj i (U i) (W i) x).symm,
    fun i j hji x => modeProj_coRangeProj_of_ne hji (hU j) (hWB i) x⟩

/-- The bounds of the modes: a vector that is tangent in mode `k` at one of the two Tucker
tensors has a mode-`k` normal component at the other one of norm at most `ρ⁻¹ ‖Y - X‖` times its
norm. -/
private theorem norm_modeNormal_le (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (hr : ∀ k, (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (r k))
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B)
    (hr' : ∀ k, (unfold (· ≠ k) (tucker C' U')).rank = Fintype.card (r k)) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hσ : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C U))).singularValues
      (Fintype.card (r k) - 1)) :
    (∀ k (z : Tensor ι), (1 - modeProj k (U k)) (z - actOn (· ≠ k) (W k * (W k)ᵀ) z) = 0 →
        ‖(1 - modeProj k (U' k)) (z - actOn (· ≠ k) (W' k * (W' k)ᵀ) z)‖ ≤
          ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖z‖) ∧
      ∀ k (z : Tensor ι), (1 - modeProj k (U' k)) (z - actOn (· ≠ k) (W' k * (W' k)ᵀ) z) = 0 →
        ‖(1 - modeProj k (U k)) (z - actOn (· ≠ k) (W k * (W k)ᵀ) z)‖ ≤
          ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖z‖ := by
  have hD : ∀ k, ‖tucker C' U' - tucker C U‖ =
      ‖unfold (· ≠ k) (tucker C' U') - unfold (· ≠ k) (tucker C U)‖ := fun k => by
    rw [← unfold_sub, norm_unfold]
  refine ⟨fun k z hz => ?_, fun k z hz => ?_⟩
  · have e := unfold_ne_one_sub_modeProj_coRange (hU k) (hWX k) (hWB k) (hr k) z
    rw [hz, unfold_zero] at e
    have hZ : tangentProjAt (unfold (· ≠ k) (tucker C U)) (unfold (· ≠ k) z) =
        unfold (· ≠ k) z := (sub_eq_zero.1 e.symm).symm
    rw [← norm_unfold (· ≠ k) ((1 - modeProj k (U' k)) _),
      unfold_ne_one_sub_modeProj_coRange (hU' k) (hWX' k) (hWB' k) (hr' k), hD k,
      ← norm_unfold (· ≠ k) z]
    exact norm_sub_tangentProjAt_apply_le_of_tangentProjAt_eq_self (hr k) (hr' k) hρ (hσ k) hZ
  · have e := unfold_ne_one_sub_modeProj_coRange (hU' k) (hWX' k) (hWB' k) (hr' k) z
    rw [hz, unfold_zero] at e
    have hZ : tangentProjAt (unfold (· ≠ k) (tucker C' U')) (unfold (· ≠ k) z) =
        unfold (· ≠ k) z := (sub_eq_zero.1 e.symm).symm
    rw [← norm_unfold (· ≠ k) ((1 - modeProj k (U k)) _),
      unfold_ne_one_sub_modeProj_coRange (hU k) (hWX k) (hWB k) (hr k), hD k,
      ← norm_unfold (· ≠ k) z]
    exact norm_sub_tangentProjAt_apply_le_of_tangentProjAt_eq_self_symm (hr k) (hr' k) hρ
      (hσ k) hZ

/-- **The normal component at `Y` of a tangent vector at `X`, Tucker tensors.** Let
`X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` with orthonormal `Uₖ`, `U'ₖ` and co-range bases `W`, `W'` as
in `tuckerTangentProj_eq_starProjection`, let the unfoldings `Mat_{≠k}` of `X` and of `Y` have
rank `|r k|` (the number of columns of `Uₖ`), and let `0 < ρ` be a lower bound of the smallest
nonzero singular value of every unfolding of `X`. If `Z` is tangent at `X`, `P(X) Z = Z`, then
`‖Z - P(Y) Z‖ ≤ √d ρ⁻¹ ‖Y - X‖ ‖Z‖`. -/
theorem norm_sub_tuckerTangentProj_apply_le_of_eq_self (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (hr : ∀ k, (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (r k))
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B)
    (hr' : ∀ k, (unfold (· ≠ k) (tucker C' U')).rank = Fintype.card (r k)) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hσ : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C U))).singularValues
      (Fintype.card (r k) - 1)) {Z : Tensor ι} (hZ : tuckerTangentProj U 1 W Z = Z) :
    ‖Z - tuckerTangentProj U' 1 W' Z‖ ≤ √d * ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖Z‖ := by
  obtain ⟨h, -⟩ := norm_modeNormal_le hU hWX hWB hr hU' hWX' hWB' hr' hρ hσ
  obtain ⟨a1, a2, a3, a4, a5⟩ := tuckerFrame hU hWX hWB
  obtain ⟨b1, -, b3, -, b5⟩ := tuckerFrame hU' hWX' hWB'
  rw [tuckerTangentProj_one_eq] at hZ ⊢
  rw [mul_assoc (√(d : ℝ))]
  exact norm_sub_modeTangentProj_apply_le_of_eq_self a1 a2 a3 a4 a5 b1 b3 b5 h hZ

/-- **The tangent projector at `X` on a vector normal at `Y`, Tucker tensors.** Under the
hypotheses of `norm_sub_tuckerTangentProj_apply_le_of_eq_self`, if `N` is normal at `Y`,
`P(Y) N = 0`, then `‖P(X) N‖ ≤ √d ρ⁻¹ ‖Y - X‖ ‖N‖`. -/
theorem norm_tuckerTangentProj_apply_le_of_eq_zero (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (hr : ∀ k, (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (r k))
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B)
    (hr' : ∀ k, (unfold (· ≠ k) (tucker C' U')).rank = Fintype.card (r k)) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hσ : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C U))).singularValues
      (Fintype.card (r k) - 1)) {N : Tensor ι} (hN : tuckerTangentProj U' 1 W' N = 0) :
    ‖tuckerTangentProj U 1 W N‖ ≤ √d * ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖N‖ := by
  obtain ⟨h, -⟩ := norm_modeNormal_le hU hWX hWB hr hU' hWX' hWB' hr' hρ hσ
  obtain ⟨a1, a2, a3, a4, a5⟩ := tuckerFrame hU hWX hWB
  obtain ⟨b1, b2, b3, b4, b5⟩ := tuckerFrame hU' hWX' hWB'
  rw [tuckerTangentProj_one_eq] at hN ⊢
  rw [mul_assoc (√(d : ℝ))]
  exact norm_modeTangentProj_apply_le_of_eq_zero a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
    (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)) h hN

/-- **Lipschitz bound of the tangent projector of the Tucker manifold with the constant `√d`.**
Let `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` be Tucker tensors with `d` modes, with orthonormal `Uₖ`,
`U'ₖ` and co-range bases `W`, `W'` as in `tuckerTangentProj_eq_starProjection`, let the
unfoldings `Mat_{≠k}` of `X` and of `Y` have rank `|r k|` (the same multilinear rank), and let
`0 < ρ` be a lower bound of the smallest nonzero singular value of every unfolding of `X`. Then
for every tensor `B`: `‖P(Y) B - P(X) B‖ ≤ √d ρ⁻¹ ‖Y - X‖ ‖B‖`. No smallness of `‖Y - X‖` is
needed, and the lower bound `ρ` is needed at `X` only. -/
theorem norm_tuckerTangentProj_sub_le (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (hr : ∀ k, (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (r k))
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B)
    (hr' : ∀ k, (unfold (· ≠ k) (tucker C' U')).rank = Fintype.card (r k)) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hσ : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C U))).singularValues
      (Fintype.card (r k) - 1)) (B : Tensor ι) :
    ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ ≤
      √d * ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖B‖ := by
  obtain ⟨h, h'⟩ := norm_modeNormal_le hU hWX hWB hr hU' hWX' hWB' hr' hρ hσ
  obtain ⟨a1, a2, a3, a4, a5⟩ := tuckerFrame hU hWX hWB
  obtain ⟨b1, b2, b3, b4, b5⟩ := tuckerFrame hU' hWX' hWB'
  rw [tuckerTangentProj_one_eq, tuckerTangentProj_one_eq, mul_assoc (√(d : ℝ))]
  exact norm_modeTangentProj_sub_le a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
    (mul_nonneg (inv_nonneg.2 hρ.le) (norm_nonneg _)) h h' B

end ProjectorLipschitz

/-! ### Example -/

namespace TuckerProjectorLipschitzExamples

/-- The Tucker tensor with one mode of dimension one, the core entry `c` and the basis `1`. -/
private theorem tucker_const (c : ℝ) :
    tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => c)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) = WithLp.toLp 2 fun _ => c :=
  tucker_one _

/-- The co-range basis with the entry one fixes the constant tensor. -/
private theorem actOn_const (k : Fin 1) (c : ℝ) :
    actOn (ι := fun _ : Fin 1 => Fin 1) (· ≠ k)
      ((Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ) *
        (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ)ᵀ)
      (WithLp.toLp 2 fun _ => c) = WithLp.toLp 2 fun _ => c := by
  ext x
  simp [actOn_apply, Matrix.mul_apply]

/-- The co-range basis with the entry one lies in the column space of the unfolding of the
constant tensor `c ≠ 0`. -/
private theorem coRange_const (k : Fin 1) {c : ℝ} (hc : c ≠ 0) :
    ∃ B : Matrix ({j : Fin 1 // ¬ j ≠ k} → Fin 1) (Fin 1) ℝ,
      (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ) =
        unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k) (WithLp.toLp 2 fun _ => c) * B := by
  refine ⟨Matrix.of fun _ _ => c⁻¹, ?_⟩
  ext z i
  rw [Matrix.mul_apply]
  simp [hc]

/-- The unfolding of the constant tensor `c ≠ 0` has rank one. -/
private theorem rank_unfold_const (k : Fin 1) {c : ℝ} (hc : c ≠ 0) :
    (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k) (WithLp.toLp 2 fun _ => c)).rank =
      Fintype.card (Fin 1) := by
  obtain ⟨B, hB⟩ := coRange_const k hc
  have hW : (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ)ᵀ *
      (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ) = 1 := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j]
  refine le_antisymm ((rank_le_card_width _).trans (by simp)) ?_
  calc Fintype.card (Fin 1) = (1 : Matrix (Fin 1) (Fin 1) ℝ).rank := rank_one.symm
    _ ≤ (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k) (WithLp.toLp 2 fun _ => c) * B).rank := by
        rw [← hW]
        nth_rw 2 [hB]
        exact rank_mul_le_right _ _
    _ ≤ _ := rank_mul_le_left _ _

/-- The two Tucker tensors of the example below are different. -/
example :
    tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => (2 : ℝ))
        (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) ≠
      tucker (WithLp.toLp 2 fun _ => (1 : ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  rw [tucker_const, tucker_const]
  intro h
  have h1 := congrArg (fun T : Tensor fun _ : Fin 1 => Fin 1 => T fun _ => 0) h
  norm_num at h1

/-- Non-vacuity of `norm_tuckerTangentProj_sub_le` with `X ≠ Y`: one mode of dimension one,
`X` the tensor with the entry `1`, `Y` the tensor with the entry `2`, the basis `1` and the
co-range basis with the entry one for both, and `ρ` the singular value of the unfolding of `X`.
All hypotheses hold. (With one mode the tangent space is the whole space, so here both
projectors are the identity.) -/
example : ∃ ρ : ℝ, 0 < ρ ∧ ∀ B : Tensor fun _ : Fin 1 => Fin 1,
    ‖tuckerTangentProj (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
          (fun k => (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ)) B -
        tuckerTangentProj (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
          (fun k => (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ)) B‖ ≤
      √((1 : ℕ) : ℝ) * ρ⁻¹ *
        ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => (2 : ℝ))
            (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
          tucker (WithLp.toLp 2 fun _ => (1 : ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))‖ *
        ‖B‖ := by
  have hrk : ∀ (c : ℝ), c ≠ 0 → ∀ k : Fin 1,
      (unfold (· ≠ k) (tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => c)
        (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)))).rank = Fintype.card (Fin 1) := fun c hc k => by
    rw [tucker_const]
    exact rank_unfold_const k hc
  refine ⟨_, SVD.singularValues_pred_rank_pos (hrk 1 one_ne_zero 0) (by simp), fun B => ?_⟩
  exact norm_tuckerTangentProj_sub_le (fun _ => by simp)
    (fun k => by rw [tucker_const]; exact actOn_const k 1)
    (fun k => by rw [tucker_const]; exact coRange_const k one_ne_zero) (hrk 1 one_ne_zero)
    (fun _ => by simp) (fun k => by rw [tucker_const]; exact actOn_const k 2)
    (fun k => by rw [tucker_const]; exact coRange_const k two_ne_zero) (hrk 2 two_ne_zero)
    (SVD.singularValues_pred_rank_pos (hrk 1 one_ne_zero 0) (by simp))
    (fun k => by obtain rfl : k = 0 := Subsingleton.elim _ _; exact le_rfl) B

end TuckerProjectorLipschitzExamples

end Tensor

end LeanDLRA
