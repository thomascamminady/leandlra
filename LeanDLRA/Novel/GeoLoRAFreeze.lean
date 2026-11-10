import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Novel.BlindSpot
import LeanDLRA.Novel.BlindSpotII
import LeanDLRA.Training.Descent

/-!
# The GeoLoRA freeze: why the zero doubly-normal block stops rank growth

Numerical experiments, kept outside this library, found that the GeoLoRA assembly (doubly-normal
block set to zero) freezes at low rank in real training, with the normal gradient `N` large
and the tangent gradient `P G` not small, while the Galerkin assembly (DLRT, augmented BUG)
does not.  This module derives the mechanism from the steps themselves, for actual matrices.
It builds on Theorem A of `LeanDLRA.Novel.BlindSpot`, which is the case `a =
b = 0`.

## Setting

`W₀ = U S Vᵀ` with `U`, `V` orthonormal, `r = card k`, `G = ∇ℒ(W₀)`, and `A = S − λ Uᵀ G V`,
`a = (1 − U Uᵀ) G V`, `b = Uᵀ G (1 − V Vᵀ)`, `N = (1 − U Uᵀ) G (1 − V Vᵀ)`. Both assemblies
are members of one family, `asm`:

`U A Vᵀ − λ a Vᵀ − λ U b + X`, with `X` doubly normal,

* GeoLoRA: `X = 0` (`geoPre_eq_asm`; `geoLoRAStep_eq_geoPre` identifies `geoPre` with the
  library's `geoLoRAStep`);
* Galerkin: `X = −λ Û Ûᵀ N V̂ V̂ᵀ` (`augStep_eq_asm`, derived from exact augmentation);
* `geolora_probe`: `X = −λ θ u vᵀ` (`geoProbePre_eq_asm`, `geoProbePre_eq_geoLoRADir`).

The Schur complement of `A` is `Z = X − λ² a A⁻¹ b` (`schur`).  Everything follows from one
two-sided estimate of the tail `τ_r = (∑_{i>r} σ_i²)^{1/2}`, valid for the whole family:

`min(1, σ_min(A) / ‖Z‖₂) ‖Z‖ / κ ≤ τ_r ≤ ‖Z‖`, `κ = (1 + |λ| ‖a A⁻¹‖) (1 + |λ| ‖A⁻¹ b‖)`.

The upper bound is the splitting `asm_eq_add_schur`.  The lower bound combines the block
diagonalisation `leftElim_mul_asm_mul_rightElim` with `norm_le_norm_sub_of_specNorm_le`, which
is `BlindSpotII.quadLoss_le_of_specNorm_le` for a general core, and a contraction that removes
the size condition (`mul_norm_le_norm_sub`).

## Main results

**Target (1), GeoLoRA.**
* `norm_geoPre_sub_core`, `rank_trunc_geoPre_le_of_tangent`: the first-order statement as
  asked.  The part outside the old bases has size `|λ| (‖a‖² + ‖b‖²)^{1/2} ≤ |λ| ‖P G‖`, and
  `ϑ ≥ |λ| ‖P G‖ / √2` gives rank at most `r` for every `N`, with no condition on `S`.
* `rank_trunc_geoPre_eq`: the sharp threshold, second order.  If `λ² ‖a A⁻¹ b‖ ≤ ϑ <
  σ_min(A)`, the truncated step has rank exactly `r`, for every `N`.
  `rank_trunc_geoPre_eq_of_tangent` states it in terms of `‖P G‖` and `σ_min(S)` alone.
* `lt_rank_trunc_geoPre`: the converse, no freeze below `λ² ‖a A⁻¹ b‖ / κ`.
* `tendsto_svTail_geoPre_div_sq`: the exact law `τ_r(Ŵ_λ) / λ² → ‖a S⁻¹ b‖` as `λ → 0`.
* `rank_svdTrunc_geoPre_le_one_iff`, `svTail_geoPre_rank_one`: at rank one the threshold is
  exact for every `λ` and every `s ≠ 0`: rank at most one iff `ϑ ≥ 2 α β / (D₊ + D₋)`, where
  `α = |λ| ‖a‖`, `β = |λ| ‖b‖`, `D± = (s² + (α ± β)²)^{1/2}`, `s = A`.

**Dependence on `σ_min`.**
* `LowerBd.norm_mul_inv_mul_le`: `‖a A⁻¹ b‖ ≤ ‖a‖ ‖b‖ / σ_min(A)`, attained when `a`, `b`
  couple through the smallest singular direction (`norm_mul_diagonal_inv_mul_eq`).  In general
  each direction counts with weight `1 / σᵢ` (`mul_diagonal_inv_mul_eq_sum`).
* `LowerBd.sub_smul`: `σ_min(A) ≥ σ_min(S) − |λ| ‖Uᵀ G V‖`.
* `svTail_geoPre_le_interp_left`, `svTail_geoPre_le_interp_right`: for all `r`, `τ_r ≤ λ² ‖a‖
  ‖b‖ / (s² + λ² ‖a‖²)^{1/2}`, and the same with `‖b‖`.  So the threshold grows like `1 /
  σ_min` as `σ_min` falls, then saturates at first order `|λ| min(‖a‖, ‖b‖)` once `σ_min` is
  below `|λ| max(‖a‖, ‖b‖)`.  `geoThreshold_bounds` is the exact version at rank one.

**Target (2), Galerkin.**  `transpose_mul_geoPre_mul`, `transpose_mul_augStep_mul`: the
doubly-normal coefficient block is `0` for GeoLoRA and `−λ` times the compression of `N` for
Galerkin. `lt_rank_trunc_augStep`, `lt_rank_trunc_augStep_explicit`: the rank grows once `κ ϑ
< min(|λ| ‖C‖ − λ² ‖a A⁻¹ b‖, σ_min(A))`, with `C = Û Ûᵀ N V̂ V̂ᵀ`.

**Target (3), the same point.**  `geoLoRA_frozen_galerkin_grows`, in `ℝ^{3×3}`, `r = 1`, `λ =
1/10`, `ϑ = 1/1000`, for every `ν ≥ 1`: `ϑ` is below the first-order size `|λ| ‖a‖`; GeoLoRA
stays at rank one for every `N`, Galerkin has rank at least two, `geolora_probe` has rank
exactly two.

**Target (4), one probe.**  One probe leaves `A`, `a`, `b` unchanged: the cross blocks vanish
(`vecMul_probe_mul`, `mul_mulVec_probe`).  It adds the single term `−λ θ u vᵀ` to `Z`,
orthogonal to the rest (`norm_sq_schur_probe`), where `θ = ‖(1 − V̂ V̂ᵀ) Gᵀ u‖ = ‖N̄ᵀ u‖` and
`N̄ = (1 − Û Ûᵀ) G (1 − V̂ V̂ᵀ)` (`probe_value`, `residual_eq_normalBlock`), and `‖N̄ ω‖ / ‖ω‖
≤ θ` for `ω ⊥ V̂` (`le_probe_value`).  So exactly one singular value moves from second to
first order: `rank_trunc_geoProbePre_le` (rank at most `r + 1` above the old threshold),
`lt_rank_trunc_geoProbePre` (rank above `r` if `κ ϑ < min(|λ θ|, σ_min(A))`),
`rank_trunc_geoProbePre_eq` (exactly `r + 1` between them).

## What differs from the targets

* The threshold of target (1) is not of order `λ ‖P G‖`.  That bound is true, but sharp only
  for `σ_min ≲ |λ| max(‖a‖, ‖b‖)`.  The sharp threshold is second order, and its coefficient
  is `‖a A⁻¹ b‖`, with `A = S − λ Uᵀ G V`, not `‖a‖ ‖b‖ / σ`, which is an upper bound.
* Target (2) needs a subtraction.  The block contains `−λ C` and also the GeoLoRA term `−λ² a
  A⁻¹ b`, and they can cancel: `augStep_cancellation` has `‖C‖ = 1` and rank at most one at
  every tolerance.
* The freeze is a statement about one step.  `rank_iterate_geoStep` iterates it under the
  hypothesis that the threshold holds at each iterate.  That it does in training is not proved
  here.

## Gaps

* For `r > 1` the lower bound carries `κ`, so it is exact only as `λ → 0`, and it is weak when
  `σ_min ≲ |λ| max(‖a‖, ‖b‖)`.  Only at `r = 1` is the threshold exact for all `σ` (for `s ≠
  0`).
* `le_probe_value` needs `ω ⊥ V̂`.  For the code's `ω` only `θ = ‖N̄ᵀ u‖` is proved, and `θ`
  can vanish, in which case the code drops the pair.  No expectation over `ω` is taken.
* Exact arithmetic throughout.  The comparison with the training runs is a mechanism: whether
  `ϑ` lies between the thresholds along actual training runs is not part of this module.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.GeoLoRAFreeze

open LeanDLRA FactorizedDynamics BlindSpot BlindSpotII EckartYoung Curvature
open LeanDLRA.WeylSingular (tailNorm)

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-! ### Cancellation in right-associated products -/

lemma vecMulVec_zero_left' {p q : Type*} (v : q → ℝ) :
    Matrix.vecMulVec (0 : p → ℝ) v = 0 := by
  ext i j
  simp [Matrix.vecMulVec_apply]

lemma norm_vecMulVec_sq {p q : Type*} [Fintype p] [Fintype q] (c : p → ℝ) (d : q → ℝ) :
    ‖Matrix.vecMulVec c d‖ ^ 2 = (c ⬝ᵥ c) * (d ⬝ᵥ d) := by
  rw [← real_inner_self_eq_norm_sq, inner_vecMulVec_vecMulVec]

lemma mul_mul_of_mul_eq_one {p q l : Type*} [Fintype q] [Fintype p] [DecidableEq p]
    {B : Matrix p q ℝ} {C : Matrix q p ℝ} (h : B * C = 1) (Y : Matrix p l ℝ) : B * (C * Y) = Y
  := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

lemma mul_mul_of_mul_eq_zero {p q s l : Type*} [Fintype q] [Fintype s]
    {B : Matrix p q ℝ} {C : Matrix q s ℝ} (h : B * C = 0) (Y : Matrix s l ℝ) : B * (C * Y) = 0
  := by
  rw [← Matrix.mul_assoc, h, Matrix.zero_mul]

/-! ### One family of assembled matrices -/

/-- The assembled matrix in block form with respect to `(U, U^⊥)` and `(V, V^⊥)`:
`U A Vᵀ + a Vᵀ + U b + X`, with `Uᵀ a = 0`, `b V = 0` and `X` doubly normal. -/
def asm (U : Matrix m k ℝ) (V : Matrix n k ℝ) (A : Matrix k k ℝ) (a : Matrix m k ℝ)
    (b : Matrix k n ℝ) (X : Matrix m n ℝ) : Matrix m n ℝ :=
  U * A * Vᵀ + a * Vᵀ + U * b + X

/-- The Schur complement `Z = X − a A⁻¹ b` of the block `A` in the assembled matrix. -/
noncomputable def schur (A : Matrix k k ℝ) (a : Matrix m k ℝ) (b : Matrix k n ℝ)
    (X : Matrix m n ℝ) : Matrix m n ℝ :=
  X - a * A⁻¹ * b

/-- **Schur splitting**: the assembled matrix is a matrix of rank at most `r` plus the Schur
complement.  No orthogonality is needed. -/
theorem asm_eq_add_schur (U : Matrix m k ℝ) (V : Matrix n k ℝ) {A : Matrix k k ℝ}
    (hA : IsUnit A.det) (a : Matrix m k ℝ) (b : Matrix k n ℝ) (X : Matrix m n ℝ) :
    asm U V A a b X = (U * A + a) * A⁻¹ * (A * Vᵀ + b) + schur A a b X := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have e : (U * A + a) * A⁻¹ = U + a * A⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have e2 : a * A⁻¹ * (A * Vᵀ) = a * Vᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹, h2, Matrix.one_mul]
  rw [e, schur, asm, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e2, Matrix.mul_assoc U A]
  abel

lemma rank_asm_core_le (U : Matrix m k ℝ) (A : Matrix k k ℝ) (a : Matrix m k ℝ)
    (Vt : Matrix k n ℝ) : ((U * A + a) * A⁻¹ * Vt).rank ≤ Fintype.card k :=
  (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans
    (Matrix.rank_le_card_width _))

/-- The left multiplier `1 − a A⁻¹ Uᵀ` removing `a`. -/
noncomputable def leftElim (U : Matrix m k ℝ) (A : Matrix k k ℝ) (a : Matrix m k ℝ) :
    Matrix m m ℝ :=
  1 - a * A⁻¹ * Uᵀ

/-- The right multiplier `1 − V A⁻¹ b` removing `b`. -/
noncomputable def rightElim (V : Matrix n k ℝ) (A : Matrix k k ℝ) (b : Matrix k n ℝ) :
    Matrix n n ℝ :=
  1 - V * A⁻¹ * b

/-- **Block diagonalisation**: `L M R = U A Vᵀ + Z`, for unit triangular `L`, `R`. -/
theorem leftElim_mul_asm_mul_rightElim {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} (hA : IsUnit A.det) {a : Matrix m k ℝ}
    {b : Matrix k n ℝ} {X : Matrix m n ℝ} (ha : Uᵀ * a = 0) (hb : b * V = 0)
    (hXl : Uᵀ * X = 0) (hXr : X * V = 0) :
    leftElim U A a * asm U V A a b X * rightElim V A b = U * A * Vᵀ + schur A a b X := by
  have hi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hj : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  simp only [leftElim, rightElim, asm, schur, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    mul_mul_of_mul_eq_one hU, mul_mul_of_mul_eq_one hV, mul_mul_of_mul_eq_one hi,
    mul_mul_of_mul_eq_one hj, mul_mul_of_mul_eq_zero ha, mul_mul_of_mul_eq_zero hb,
    mul_mul_of_mul_eq_zero hXr, hXl, Matrix.mul_zero, Matrix.zero_mul]
  abel

/-- The left elimination is bounded by `1 + ‖a A⁻¹‖`. -/
lemma norm_leftElim_mul_le {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (A : Matrix k k ℝ)
    (a : Matrix m k ℝ) (Y : Matrix m n ℝ) :
    ‖leftElim U A a * Y‖ ≤ (1 + ‖a * A⁻¹‖) * ‖Y‖ := by
  have e : leftElim U A a * Y = Y - (a * A⁻¹) * (Uᵀ * Y) := by
    rw [leftElim, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  have h1 : ‖(a * A⁻¹) * (Uᵀ * Y)‖ ≤ ‖a * A⁻¹‖ * ‖Y‖ :=
    (Frobenius.norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_transpose_mul_le hU Y) (norm_nonneg _))
  rw [e]
  calc ‖Y - (a * A⁻¹) * (Uᵀ * Y)‖ ≤ ‖Y‖ + ‖(a * A⁻¹) * (Uᵀ * Y)‖ := norm_sub_le _ _
    _ ≤ (1 + ‖a * A⁻¹‖) * ‖Y‖ := by nlinarith

/-- The right elimination is bounded by `1 + ‖A⁻¹ b‖`. -/
lemma norm_mul_rightElim_le {V : Matrix n k ℝ} (hV : Vᵀ * V = 1) (A : Matrix k k ℝ)
    (b : Matrix k n ℝ) (Y : Matrix m n ℝ) :
    ‖Y * rightElim V A b‖ ≤ (1 + ‖A⁻¹ * b‖) * ‖Y‖ := by
  have e : Y * rightElim V A b = Y - (Y * V) * (A⁻¹ * b) := by
    rw [rightElim, Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have h1 : ‖(Y * V) * (A⁻¹ * b)‖ ≤ ‖Y‖ * ‖A⁻¹ * b‖ :=
    (Frobenius.norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le_of_orthonormal hV Y) (norm_nonneg _))
  rw [e]
  calc ‖Y - (Y * V) * (A⁻¹ * b)‖ ≤ ‖Y‖ + ‖(Y * V) * (A⁻¹ * b)‖ := norm_sub_le _ _
    _ ≤ (1 + ‖A⁻¹ * b‖) * ‖Y‖ := by nlinarith

/-! ### Distance to rank at most `r` -/

/-- `σ_min(A) ≥ s`, in the sum-of-squares form used in `LeanDLRA.Novel.BlindSpot`. -/
def LowerBd (A : Matrix k k ℝ) (s : ℝ) : Prop :=
  ∀ x : k → ℝ, s ^ 2 * ∑ j, x j ^ 2 ≤ ∑ i, (A *ᵥ x) i ^ 2

/-- A positive lower bound makes `A` invertible. -/
lemma LowerBd.isUnit_det {A : Matrix k k ℝ} {s : ℝ} (h : LowerBd A s) (hs : 0 < s) :
    IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 := h v
  rw [hAv] at h1
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at h1
  have h2 : ∑ j, v j ^ 2 ≤ 0 := by
    by_contra hc
    rw [not_le] at hc
    have : 0 < s ^ 2 * ∑ j, v j ^ 2 := by positivity
    linarith
  have h3 : ∑ j, v j ^ 2 = 0 := le_antisymm h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h3
  exact hv (funext fun j => by simpa using h3 j (Finset.mem_univ j))

/-- The thin singular values of `A` are bounded below by any lower bound of `A`. -/
lemma LowerBd.le_thinσ {A : Matrix k k ℝ} {s : ℝ} (h : LowerBd A s) (hs : 0 < s)
    (i : Fin A.rank) : s ≤ thinσ A i := by
  set x : k → ℝ := fun j => thinV A j i with hx
  have hsum : ∀ W : Matrix k (Fin A.rank) ℝ, Wᵀ * W = 1 → ∑ j, W j i ^ 2 = 1 := fun W hW => by
    have := congrFun (congrFun hW i) i
    simpa [Matrix.mul_apply, sq] using this
  have hAV : A * thinV A = thinU A * Matrix.diagonal (thinσ A) := by
    calc A * thinV A
        = thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ * thinV A := by rw [← thin_eq]
      _ = thinU A * Matrix.diagonal (thinσ A) := by
        rw [Matrix.mul_assoc, thinV_orthonormal, Matrix.mul_one]
  have hAx : ∀ j, (A *ᵥ x) j = thinU A j i * thinσ A i := fun j => by
    have := congrFun (congrFun hAV j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, hx] using this
  have h1 := h x
  have h2 : ∑ j, (A *ᵥ x) j ^ 2 = thinσ A i ^ 2 := by
    simp only [hAx, mul_pow]
    rw [← Finset.sum_mul, hsum _ (thinU_orthonormal A), one_mul]
  rw [h2, hsum _ (thinV_orthonormal A), mul_one] at h1
  exact (pow_le_pow_iff_left₀ hs.le (thinσ_pos A i).le two_ne_zero).1 h1

/-- **Eckart–Young for a doubly normal perturbation.**  If `‖Z‖₂ ≤ σ_min(A)`, then `U A Vᵀ` is a
best approximation of `U A Vᵀ + Z` of rank at most `r`, for a general invertible core `A`. 
This is
`BlindSpotII.quadLoss_le_of_specNorm_le` after a thin SVD of `A`. -/
theorem norm_le_norm_sub_of_specNorm_le {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} {s : ℝ} (hs : 0 < s) (hA : LowerBd A s)
    {Z : Matrix m n ℝ} (hZl : Uᵀ * Z = 0) (hZr : Z * V = 0) (hZ : specNorm Z ≤ s)
    {Y : Matrix m n ℝ} (hY : Y.rank ≤ Fintype.card k) :
    ‖Z‖ ≤ ‖U * A * Vᵀ + Z - Y‖ := by
  have hrank : A.rank = Fintype.card k := by
    have := Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (hA.isUnit_det hs))
    exact this
  set U' : Matrix m (Fin A.rank) ℝ := U * thinU A with hU'def
  set V' : Matrix n (Fin A.rank) ℝ := V * thinV A with hV'def
  have hU' : U'ᵀ * U' = 1 := by
    rw [hU'def, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul,
      thinU_orthonormal]
  have hV' : V'ᵀ * V' = 1 := by
    rw [hV'def, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul,
      thinV_orthonormal]
  have e : U' * Matrix.diagonal (thinσ A) * V'ᵀ = U * A * Vᵀ := by
    calc U' * Matrix.diagonal (thinσ A) * V'ᵀ
        = U * (thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ) * Vᵀ := by
          simp only [hU'def, hV'def, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = U * A * Vᵀ := by rw [← thin_eq]
  have hl : U'ᵀ * Z = 0 := by
    rw [hU'def, Matrix.transpose_mul, Matrix.mul_assoc, hZl, Matrix.mul_zero]
  have hr : Z * V' = 0 := by
    rw [hV'def, ← Matrix.mul_assoc, hZr, Matrix.zero_mul]
  have hσ : ∀ i, specNorm Z ≤ |thinσ A i| := fun i =>
    hZ.trans ((hA.le_thinσ hs i).trans (le_abs_self _))
  have h := quadLoss_le_of_specNorm_le hU' hV' hl hr hσ (Y := Y)
    (by simpa [hrank] using hY)
  rw [e] at h
  simp only [quadLoss] at h
  have e1 : U * A * Vᵀ - (U * A * Vᵀ + Z) = -Z := by abel
  rw [e1, norm_neg, norm_sub_rev Y] at h
  have h2 : ‖Z‖ ^ 2 ≤ ‖U * A * Vᵀ + Z - Y‖ ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- Multiplying the part outside `U` by `0 ≤ t ≤ 1` is a contraction. -/
lemma norm_contract_le {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (X : Matrix m n ℝ) : ‖(U * Uᵀ + t • (1 - U * Uᵀ)) * X‖ ≤ ‖X‖ := by
  set p : Matrix m n ℝ := U * Uᵀ * X with hp
  set q : Matrix m n ℝ := X - p with hq
  have e : (U * Uᵀ + t • (1 - U * Uᵀ)) * X = p + t • q := by
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul]
  have hX : X = p + q := by rw [hq]; abel
  have hin : ⟪p, q⟫ = 0 := by
    have h1 : Uᵀ * q = 0 := by
      rw [hq, hp, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul,
        sub_self]
    rw [hp, Matrix.mul_assoc, Frobenius.inner_mul_left, h1]
    simp
  have h1 : ‖X‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    conv_lhs => rw [hX]
    rw [norm_add_sq_real, hin]
    ring
  have h2 : ‖p + t • q‖ ^ 2 = ‖p‖ ^ 2 + t ^ 2 * ‖q‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hin, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [e]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [h1, h2]
  have : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg ‖q‖]

/-- **Scaled form**, with no size condition on `Z`: if `0 ≤ t ≤ 1` and `t ‖Z‖₂ ≤ σ_min(A)`, then
every matrix of rank at most `r` is at distance at least `t ‖Z‖` from `U A Vᵀ + Z`. -/
theorem mul_norm_le_norm_sub {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} {s : ℝ} (hs : 0 < s) (hA : LowerBd A s)
    {Z : Matrix m n ℝ} (hZl : Uᵀ * Z = 0) (hZr : Z * V = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htZ : t * specNorm Z ≤ s) {Y : Matrix m n ℝ} (hY : Y.rank ≤ Fintype.card k) :
    t * ‖Z‖ ≤ ‖U * A * Vᵀ + Z - Y‖ := by
  set B : Matrix m m ℝ := U * Uᵀ + t • (1 - U * Uᵀ) with hB
  have e0 : U * Uᵀ * (U * (A * Vᵀ)) = U * (A * Vᵀ) := by
    rw [Matrix.mul_assoc, mul_mul_of_mul_eq_one hU]
  have e1 : B * (U * A * Vᵀ) = U * A * Vᵀ := by
    rw [hB, Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc U A,
      e0, sub_self, smul_zero, add_zero]
  have e2 : B * Z = t • Z := by
    have h0 : U * Uᵀ * Z = 0 := by rw [Matrix.mul_assoc, hZl, Matrix.mul_zero]
    rw [hB, Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, h0, sub_zero,
      zero_add]
  have e3 : B * (U * A * Vᵀ + Z - Y) = U * A * Vᵀ + t • Z - B * Y := by
    rw [Matrix.mul_sub, Matrix.mul_add, e1, e2]
  have hl : Uᵀ * (t • Z) = 0 := by rw [Matrix.mul_smul, hZl, smul_zero]
  have hr : (t • Z) * V = 0 := by rw [Matrix.smul_mul, hZr, smul_zero]
  have hspec : specNorm (t • Z) ≤ s := by
    have : specNorm (t • Z) = t * specNorm Z := by
      simp only [specNorm_eq_l2]
      open scoped Matrix.Norms.L2Operator in
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [this]
    exact htZ
  have hrk : (B * Y).rank ≤ Fintype.card k := (Matrix.rank_mul_le_right _ _).trans hY
  have h := norm_le_norm_sub_of_specNorm_le hU hV hs hA hl hr hspec hrk
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ← e3] at h
  exact h.trans (norm_contract_le hU ht0 ht1 _)

/-- `Uᵀ * Z = 0` for the Schur complement. -/
lemma transpose_mul_schur {U : Matrix m k ℝ} {A : Matrix k k ℝ} {a : Matrix m k ℝ}
    {b : Matrix k n ℝ} {X : Matrix m n ℝ} (ha : Uᵀ * a = 0) (hXl : Uᵀ * X = 0) :
    Uᵀ * schur A a b X = 0 := by
  rw [schur, Matrix.mul_sub, hXl, Matrix.mul_assoc, ← Matrix.mul_assoc, ha]
  simp

/-- `Z * V = 0` for the Schur complement. -/
lemma schur_mul {V : Matrix n k ℝ} {A : Matrix k k ℝ} {a : Matrix m k ℝ}
    {b : Matrix k n ℝ} {X : Matrix m n ℝ} (hb : b * V = 0) (hXr : X * V = 0) :
    schur A a b X * V = 0 := by
  rw [schur, Matrix.sub_mul, hXr, Matrix.mul_assoc, hb]
  simp

/-- The factor `κ = (1 + ‖a A⁻¹‖) (1 + ‖A⁻¹ b‖) ≥ 1` lost in the lower bound. -/
noncomputable def kappa (A : Matrix k k ℝ) (a : Matrix m k ℝ) (b : Matrix k n ℝ) : ℝ :=
  (1 + ‖a * A⁻¹‖) * (1 + ‖A⁻¹ * b‖)

lemma one_le_kappa (A : Matrix k k ℝ) (a : Matrix m k ℝ) (b : Matrix k n ℝ) :
    1 ≤ kappa A a b := by
  have h1 := norm_nonneg (a * A⁻¹)
  have h2 := norm_nonneg (A⁻¹ * b)
  rw [kappa]
  nlinarith [mul_nonneg h1 h2]

/-- **Lower bound for the assembled matrix.**  With `Z` the Schur complement, every matrix of
rank
at most `r` is at distance at least `t ‖Z‖ / κ` from the assembled matrix, for `0 ≤ t ≤ 1` and
`t ‖Z‖₂ ≤ σ_min(A)`. -/
theorem mul_norm_schur_le {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} {s : ℝ} (hs : 0 < s) (hA : LowerBd A s)
    {a : Matrix m k ℝ} {b : Matrix k n ℝ} {X : Matrix m n ℝ} (ha : Uᵀ * a = 0) (hb : b * V = 0)
    (hXl : Uᵀ * X = 0) (hXr : X * V = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htZ : t * specNorm (schur A a b X) ≤ s) {Y : Matrix m n ℝ}
    (hY : Y.rank ≤ Fintype.card k) :
    t * ‖schur A a b X‖ ≤ kappa A a b * ‖asm U V A a b X - Y‖ := by
  have hdet := hA.isUnit_det hs
  set L := leftElim U A a with hL
  set R := rightElim V A b with hR
  set M := asm U V A a b X with hM
  have e : L * (M - Y) * R = U * A * Vᵀ + schur A a b X - L * Y * R := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hL, hR, hM,
      leftElim_mul_asm_mul_rightElim hU hV hdet ha hb hXl hXr]
  have hrk : (L * Y * R).rank ≤ Fintype.card k :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hY)
  have h1 := mul_norm_le_norm_sub hU hV hs hA (transpose_mul_schur ha hXl) (schur_mul hb hXr)
    ht0 ht1 htZ hrk
  rw [← e] at h1
  refine h1.trans ?_
  have h2 : ‖L * (M - Y) * R‖ ≤ (1 + ‖A⁻¹ * b‖) * ‖L * (M - Y)‖ := norm_mul_rightElim_le hV A b _
  have h3 : ‖L * (M - Y)‖ ≤ (1 + ‖a * A⁻¹‖) * ‖M - Y‖ := norm_leftElim_mul_le hU A a _
  have h4 : 0 ≤ 1 + ‖A⁻¹ * b‖ := by positivity
  calc ‖L * (M - Y) * R‖ ≤ (1 + ‖A⁻¹ * b‖) * ((1 + ‖a * A⁻¹‖) * ‖M - Y‖) :=
        h2.trans (mul_le_mul_of_nonneg_left h3 h4)
    _ = kappa A a b * ‖M - Y‖ := by rw [kappa]; ring

/-! ### The tail of the assembled matrix and the truncated step -/

/-- **Upper bound for the tail**: `(∑_{i > r} σ_i²)^{1/2} ≤ ‖Z‖`. -/
theorem svTail_asm_le (U : Matrix m k ℝ) (V : Matrix n k ℝ) {A : Matrix k k ℝ}
    (hA : IsUnit A.det) (a : Matrix m k ℝ) (b : Matrix k n ℝ) (X : Matrix m n ℝ) :
    tailNorm (asm U V A a b X) (Fintype.card k) ≤ ‖schur A a b X‖ := by
  have h := svTail_le_norm_sub (asm U V A a b X) _ (rank_asm_core_le U A a (A * Vᵀ + b))
  have e : asm U V A a b X - (U * A + a) * A⁻¹ * (A * Vᵀ + b) = schur A a b X := by
    rw [asm_eq_add_schur U V hA a b X, add_sub_cancel_left]
  rwa [e] at h

/-- **Lower bound for the tail**: `t ‖Z‖ ≤ κ (∑_{i > r} σ_i²)^{1/2}`. -/
theorem mul_norm_schur_le_svTail {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} {s : ℝ} (hs : 0 < s) (hA : LowerBd A s)
    {a : Matrix m k ℝ} {b : Matrix k n ℝ} {X : Matrix m n ℝ} (ha : Uᵀ * a = 0) (hb : b * V = 0)
    (hXl : Uᵀ * X = 0) (hXr : X * V = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htZ : t * specNorm (schur A a b X) ≤ s) :
    t * ‖schur A a b X‖ ≤ kappa A a b * tailNorm (asm U V A a b X) (Fintype.card k) := by
  have h := mul_norm_schur_le hU hV hs hA ha hb hXl hXr ht0 ht1 htZ
    (rank_truncation_le (asm U V A a b X) (Fintype.card k))
  rwa [norm_sub_rev (asm U V A a b X), norm_sub_truncation_eq] at h

/-- **Truncation stays at rank `r`** once `ϑ ≥ ‖Z‖`. -/
theorem rank_trunc_le_of_norm_schur_le {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) (U : Matrix m k ℝ) (V : Matrix n k ℝ) {A : Matrix k k ℝ}
    (hA : IsUnit A.det) (a : Matrix m k ℝ) (b : Matrix k n ℝ) (X : Matrix m n ℝ)
    (h : ‖schur A a b X‖ ≤ ϑ) : (T (asm U V A a b X)).rank ≤ Fintype.card k := by
  refine (hT.rank_le _ ((U * A + a) * A⁻¹ * (A * Vᵀ + b)) ?_).trans (rank_asm_core_le U A a _)
  rw [asm_eq_add_schur U V hA a b X, sub_add_cancel_left, norm_neg]
  exact h

/-- **Truncation grows the rank** once `κ ϑ < t ‖Z‖`. -/
theorem lt_rank_trunc_of_lt {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} {s : ℝ} (hs : 0 < s) (hA : LowerBd A s)
    {a : Matrix m k ℝ} {b : Matrix k n ℝ} {X : Matrix m n ℝ} (ha : Uᵀ * a = 0) (hb : b * V = 0)
    (hXl : Uᵀ * X = 0) (hXr : X * V = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htZ : t * specNorm (schur A a b X) ≤ s) (h : kappa A a b * ϑ < t * ‖schur A a b X‖) :
    Fintype.card k < (T (asm U V A a b X)).rank := by
  by_contra hc
  rw [not_lt] at hc
  have h1 := mul_norm_schur_le hU hV hs hA ha hb hXl hXr ht0 ht1 htZ hc
  have h2 : ‖asm U V A a b X - T (asm U V A a b X)‖ ≤ ϑ := by
    rw [norm_sub_rev]
    exact hT.norm_sub_le _
  have h3 : kappa A a b * ‖asm U V A a b X - T (asm U V A a b X)‖ ≤ kappa A a b * ϑ :=
    mul_le_mul_of_nonneg_left h2 (zero_le_one.trans (one_le_kappa A a b))
  linarith

/-- The block `A` is seen by every matrix near the assembled one: truncation at `ϑ < σ_min(A)`
does
not lose rank. -/
theorem card_le_rank_trunc {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} {s : ℝ} (hA : LowerBd A s) {a : Matrix m k ℝ}
    {b : Matrix k n ℝ} {X : Matrix m n ℝ} (ha : Uᵀ * a = 0) (hb : b * V = 0) (hXl : Uᵀ * X = 0)
    (hϑ : ϑ < s) : Fintype.card k ≤ (T (asm U V A a b X)).rank := by
  set M := asm U V A a b X with hM
  have h0 : 0 ≤ ϑ := (norm_nonneg _).trans (hT.norm_sub_le M)
  have hs : 0 ≤ s := h0.trans hϑ.le
  set Y := T M with hY
  set Y' : Matrix m n ℝ := U * (Uᵀ * Y * V) * Vᵀ with hY'
  have hrk : Y'.rank ≤ Y.rank :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)))
  have hcore : Uᵀ * M * V = A := by
    simp only [hM, asm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hb, hV,
      mul_mul_of_mul_eq_one hU, mul_mul_of_mul_eq_zero ha, mul_mul_of_mul_eq_zero hXl,
      Matrix.mul_one, add_zero]
  have hdiff : Y' - U * A * Vᵀ = U * (Uᵀ * (Y - M) * V) * Vᵀ := by
    rw [hY', Matrix.mul_sub, Matrix.sub_mul, hcore, Matrix.mul_sub, Matrix.sub_mul]
  have hnorm : ‖Y' - U * A * Vᵀ‖ ≤ ‖Y - M‖ := by
    rw [hdiff, Matrix.mul_assoc U, Frobenius.norm_mul_of_orthonormal hU,
      Frobenius.norm_mul_transpose_of_orthonormal hV]
    exact (norm_mul_le_of_orthonormal hV _).trans (norm_transpose_mul_le hU _)
  have hlt : ‖Y' - U * A * Vᵀ‖ < s := hnorm.trans_lt ((hT.norm_sub_le M).trans_lt hϑ)
  exact (card_le_rank_of_norm_sub_lt hU hV hs hA hlt).trans hrk

/-- Spectral form of the lower bound on `A`: `‖A⁻¹‖₂ ≤ 1 / s`. -/
lemma LowerBd.specNorm_inv_le {A : Matrix k k ℝ} {s : ℝ} (h : LowerBd A s) (hs : 0 < s) :
    specNorm A⁻¹ ≤ s⁻¹ := by
  have hdet := h.isUnit_det hs
  by_contra hc
  rw [not_le] at hc
  obtain ⟨y, hy⟩ := exists_mulVec_of_lt_specNorm (inv_nonneg.2 hs.le) hc
  set x := A⁻¹ *ᵥ y with hx
  have hAx : A *ᵥ x = y := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have h1 := h x
  rw [hAx] at h1
  have e1 : ∀ z : k → ℝ, z ⬝ᵥ z = ∑ j, z j ^ 2 := fun z => by simp [dotProduct, sq]
  rw [e1, e1] at hy
  have h2 : (s⁻¹) ^ 2 * (s ^ 2 * ∑ j, x j ^ 2) ≤ (s⁻¹) ^ 2 * ∑ i, y i ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne', one_pow, one_mul] at h2
  linarith

/-- `‖a A⁻¹ b‖ ≤ ‖a‖ ‖b‖ / s`. -/
lemma LowerBd.norm_mul_inv_mul_le {A : Matrix k k ℝ} {s : ℝ} (h : LowerBd A s) (hs : 0 < s)
    (a : Matrix m k ℝ) (b : Matrix k n ℝ) : ‖a * A⁻¹ * b‖ ≤ ‖a‖ * ‖b‖ / s := by
  have h1 := h.specNorm_inv_le hs
  calc ‖a * A⁻¹ * b‖ = ‖a * (A⁻¹ * b)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖a‖ * ‖A⁻¹ * b‖ := Frobenius.norm_mul_le _ _
    _ ≤ ‖a‖ * (specNorm A⁻¹ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (frob_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖a‖ * (s⁻¹ * ‖b‖) := by gcongr
    _ = ‖a‖ * ‖b‖ / s := by rw [div_eq_mul_inv]; ring

/-- `‖a A⁻¹‖ ≤ ‖a‖ / s`. -/
lemma LowerBd.norm_mul_inv_le {A : Matrix k k ℝ} {s : ℝ} (h : LowerBd A s) (hs : 0 < s)
    (a : Matrix m k ℝ) : ‖a * A⁻¹‖ ≤ ‖a‖ / s := by
  calc ‖a * A⁻¹‖ ≤ ‖a‖ * specNorm A⁻¹ := frob_mul_le' _ _
    _ ≤ ‖a‖ * s⁻¹ := mul_le_mul_of_nonneg_left (h.specNorm_inv_le hs) (norm_nonneg _)
    _ = ‖a‖ / s := by rw [div_eq_mul_inv]

/-- `‖A⁻¹ b‖ ≤ ‖b‖ / s`. -/
lemma LowerBd.norm_inv_mul_le {A : Matrix k k ℝ} {s : ℝ} (h : LowerBd A s) (hs : 0 < s)
    (b : Matrix k n ℝ) : ‖A⁻¹ * b‖ ≤ ‖b‖ / s := by
  calc ‖A⁻¹ * b‖ ≤ specNorm A⁻¹ * ‖b‖ := frob_mul_le _ _
    _ ≤ s⁻¹ * ‖b‖ := mul_le_mul_of_nonneg_right (h.specNorm_inv_le hs) (norm_nonneg _)
    _ = ‖b‖ / s := by rw [div_eq_mul_inv]; ring

/-- `κ ≤ (1 + ‖a‖ / s) (1 + ‖b‖ / s)`. -/
lemma LowerBd.kappa_le {A : Matrix k k ℝ} {s : ℝ} (h : LowerBd A s) (hs : 0 < s)
    (a : Matrix m k ℝ) (b : Matrix k n ℝ) :
    kappa A a b ≤ (1 + ‖a‖ / s) * (1 + ‖b‖ / s) := by
  have h1 := h.norm_mul_inv_le hs a
  have h2 := h.norm_inv_mul_le hs b
  rw [kappa]
  gcongr

/-- **Weyl for the core**: `σ_min(S − λ B) ≥ σ_min(S) − |λ| ‖B‖`. -/
lemma LowerBd.sub_smul {S : Matrix k k ℝ} {s : ℝ} (h : LowerBd S s)
    (lr : ℝ) (B : Matrix k k ℝ) (hc : |lr| * ‖B‖ ≤ s) :
    LowerBd (S - lr • B) (s - |lr| * ‖B‖) := by
  intro x
  set nx : ℝ := √(∑ j, x j ^ 2) with hnx
  have hsum : ∀ z : k → ℝ, ‖(WithLp.toLp 2 z : EuclideanSpace ℝ k)‖ = √(∑ j, z j ^ 2) := fun z => by
    rw [EuclideanSpace.norm_eq]
    simp
  have hnx0 : nx ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h1 : s * nx ≤ √(∑ i, (S *ᵥ x) i ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, hnx0]
    exact h x
  have h2 : √(∑ i, (B *ᵥ x) i ^ 2) ≤ ‖B‖ * nx := by
    rw [hnx]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact sum_sq_mulVec_le B x
  have e : (S - lr • B) *ᵥ x = S *ᵥ x - lr • (B *ᵥ x) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec]
  have h3 : √(∑ i, (S *ᵥ x) i ^ 2) ≤
      √(∑ i, ((S - lr • B) *ᵥ x) i ^ 2) + |lr| * √(∑ i, (B *ᵥ x) i ^ 2) := by
    have h4 := norm_add_le (WithLp.toLp 2 ((S - lr • B) *ᵥ x) : EuclideanSpace ℝ k)
      (WithLp.toLp 2 (lr • (B *ᵥ x)))
    have hy : (S - lr • B) *ᵥ x + lr • (B *ᵥ x) = S *ᵥ x := by rw [e, sub_add_cancel]
    rw [← WithLp.toLp_add, hy, hsum, hsum, hsum] at h4
    have h5 : √(∑ i, (lr • (B *ᵥ x)) i ^ 2) = |lr| * √(∑ i, (B *ᵥ x) i ^ 2) := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rwa [h5] at h4
  have h6 : (s - |lr| * ‖B‖) * nx ≤ √(∑ i, ((S - lr • B) *ᵥ x) i ^ 2) := by
    have h7 : |lr| * √(∑ i, (B *ᵥ x) i ^ 2) ≤ |lr| * (‖B‖ * nx) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    nlinarith
  have h8 : 0 ≤ (s - |lr| * ‖B‖) * nx := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have h9 := pow_le_pow_left₀ h8 h6 2
  rwa [mul_pow, hnx0, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h9

/-! ### The blocks of the actual steps -/

section Steps

/-- The core of both assemblies, `A = S − λ Uᵀ G V`. -/
def coreBlock (U : Matrix m k ℝ) (V : Matrix n k ℝ) (S : Matrix k k ℝ) (G : Matrix m n ℝ)
    (lr : ℝ) : Matrix k k ℝ :=
  S - lr • (Uᵀ * G * V)

/-- The new left block `(1 − U Uᵀ) G V` of the `K`-step. -/
def leftBlock (U : Matrix m k ℝ) (V : Matrix n k ℝ) (G : Matrix m n ℝ) : Matrix m k ℝ :=
  (1 - U * Uᵀ) * G * V

/-- The new right block `Uᵀ G (1 − V Vᵀ)` of the `L`-step. -/
def rightBlock (U : Matrix m k ℝ) (V : Matrix n k ℝ) (G : Matrix m n ℝ) : Matrix k n ℝ :=
  Uᵀ * G * (1 - V * Vᵀ)

/-- The GeoLoRA iterate before truncation, `Ŵ = W₀ − λ P(W₀) G`.  By
`geoLoRAStep_eq_geoPre` this is the library's `geoLoRAStep`. -/
noncomputable def geoPre (U : Matrix m k ℝ) (V : Matrix n k ℝ) (S : Matrix k k ℝ) (G : Matrix m
n ℝ)
    (lr : ℝ) : Matrix m n ℝ :=
  U * S * Vᵀ - lr • tangentProj U V G

variable {U : Matrix m k ℝ} {V : Matrix n k ℝ}

lemma transpose_mul_one_sub (hU : Uᵀ * U = 1) : Uᵀ * (1 - U * Uᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self]

lemma one_sub_mul_self (hV : Vᵀ * V = 1) : (1 - V * Vᵀ) * V = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]

lemma transpose_mul_leftBlock (hU : Uᵀ * U = 1) (G : Matrix m n ℝ) :
    Uᵀ * leftBlock U V G = 0 := by
  rw [leftBlock, Matrix.mul_assoc (1 - U * Uᵀ), ← Matrix.mul_assoc Uᵀ, transpose_mul_one_sub hU,
    Matrix.zero_mul]

lemma rightBlock_mul (hV : Vᵀ * V = 1) (G : Matrix m n ℝ) :
    rightBlock U V G * V = 0 := by
  rw [rightBlock, Matrix.mul_assoc, one_sub_mul_self hV, Matrix.mul_zero]

/-- `P(W₀) G` in blocks. -/
lemma tangentProj_eq_blocks (U : Matrix m k ℝ) (V : Matrix n k ℝ) (G : Matrix m n ℝ) :
    tangentProj U V G =
      U * (Uᵀ * G * V) * Vᵀ + leftBlock U V G * Vᵀ + U * rightBlock U V G := by
  simp only [tangentProj_apply, leftBlock, rightBlock, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- `G` in blocks. -/
lemma eq_blocks (U : Matrix m k ℝ) (V : Matrix n k ℝ) (G : Matrix m n ℝ) :
    G = U * (Uᵀ * G * V) * Vᵀ + leftBlock U V G * Vᵀ + U * rightBlock U V G +
      normalBlock U V G := by
  simp only [normalBlock, leftBlock, rightBlock, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- `Ŵ` is the assembled matrix with zero doubly-normal block. -/
theorem geoPre_eq_asm (U : Matrix m k ℝ) (V : Matrix n k ℝ) (S : Matrix k k ℝ) (G : Matrix m n ℝ)
    (lr : ℝ) :
    geoPre U V S G lr = asm U V (coreBlock U V S G lr) ((-lr) • leftBlock U V G)
      ((-lr) • rightBlock U V G) 0 := by
  rw [geoPre, tangentProj_eq_blocks, asm, coreBlock, smul_add, smul_add, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, add_zero]
  simp only [neg_smul]
  abel

/-- The doubly-normal block of `G` does not enter the GeoLoRA iterate. -/
theorem geoPre_add_normal (U : Matrix m k ℝ) (V : Matrix n k ℝ) (S : Matrix k k ℝ)
    (G : Matrix m n ℝ) (lr : ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {N : Matrix m n ℝ}
    (hNl : Uᵀ * N = 0) (hNr : N * V = 0) :
    geoPre U V S (G + N) lr = geoPre U V S G lr := by
  have h0 : tangentProj U V N = 0 := (tangentProj_eq_zero_iff hU hV N).2 ⟨hNl, hNr⟩
  rw [geoPre, geoPre, map_add, h0, add_zero]

/-- The Schur complement of the GeoLoRA assembly: `Z = −λ² a A⁻¹ b`. -/
theorem schur_geo (A : Matrix k k ℝ) (a : Matrix m k ℝ) (b : Matrix k n ℝ) (lr : ℝ) :
    schur A ((-lr) • a) ((-lr) • b) 0 = -(lr ^ 2 • (a * A⁻¹ * b)) := by
  rw [schur, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, zero_sub]
  congr 2
  ring

/-- `‖Z‖ = λ² ‖a A⁻¹ b‖` for the GeoLoRA assembly. -/
theorem norm_schur_geo (A : Matrix k k ℝ) (a : Matrix m k ℝ) (b : Matrix k n ℝ) (lr : ℝ) :
    ‖schur A ((-lr) • a) ((-lr) • b) 0‖ = lr ^ 2 * ‖a * A⁻¹ * b‖ := by
  rw [schur_geo, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg lr)]

end Steps

/-- **The GeoLoRA step of the library is `Ŵ`.**  With `P̃ = Û Ûᵀ − U Uᵀ`, `Q̃ = V̂ V̂ᵀ − V Vᵀ`
as in
`BlindSpot.geoLoRAStep_eq_self_of_tangentProj_eq_zero`, the assembly `P₀ Q₀ + P̃ Q₀ + P₀ Q̃` with
the doubly-normal block set to zero gives `W₀ − λ P(W₀) G`. -/
theorem geoLoRAStep_eq_geoPre {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂] [DecidableEq k₁]
    [DecidableEq k₂] {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (S : Matrix k k ℝ) (g : Matrix m n ℝ → Matrix m n ℝ) {Uh : Matrix m k₁ ℝ}
    {Vh : Matrix n k₂ ℝ}
    (hUh : IsExactAugmentation Uh U (g (U * S * Vᵀ) * V))
    (hVh : IsExactAugmentation Vh V ((g (U * S * Vᵀ))ᵀ * U)) (lr : ℝ) :
    geoLoRAStep (leftProj U) (rightProj V) (leftProj Uh - leftProj U)
        (rightProj Vh - rightProj V) g lr (U * S * Vᵀ) =
      geoPre U V S (g (U * S * Vᵀ)) lr := by
  set G := g (U * S * Vᵀ) with hG
  have h1 : Uh * Uhᵀ * (G * V) = G * V := hUh.captures_aug
  have h2 : Uᵀ * G * (Vh * Vhᵀ) = Uᵀ * G := by
    have := congrArg Matrix.transpose hVh.captures_aug
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  have e : geoLoRADir (leftProj U) (rightProj V) (leftProj Uh - leftProj U)
      (rightProj Vh - rightProj V) G = tangentProj U V G := by
    rw [geoLoRADir, tangentProj_apply]
    simp only [sub_apply, leftProj_apply, rightProj_apply']
    have e1 : Uh * Uhᵀ * (G * (V * Vᵀ)) = G * (V * Vᵀ) := by
      rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc (Uh * Uhᵀ), h1]
    have e2 : U * Uᵀ * (G * (Vh * Vhᵀ)) = U * Uᵀ * G := by
      rw [Matrix.mul_assoc U, ← Matrix.mul_assoc Uᵀ, h2, ← Matrix.mul_assoc]
    rw [e1, Matrix.mul_sub, e2]
    simp only [Matrix.mul_assoc]
    abel
  rw [geoLoRAStep, ← hG, e, geoPre]

/-- `⟪a Vᵀ, U b⟫ = 0` when `Uᵀ a = 0`. -/
lemma inner_left_mul_right {U : Matrix m k ℝ} {V : Matrix n k ℝ} {a : Matrix m k ℝ}
    (ha : Uᵀ * a = 0) (b : Matrix k n ℝ) : ⟪a * Vᵀ, U * b⟫ = 0 := by
  rw [Frobenius.inner_mul_left', ← Matrix.mul_assoc, ha, Matrix.zero_mul]
  simp

/-! ### Target (1): GeoLoRA -/

section Geo

variable {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ} {U : Matrix m k ℝ} {V : Matrix n k ℝ}
  {S : Matrix k k ℝ} {G : Matrix m n ℝ} {lr : ℝ}

/-- The part of the GeoLoRA iterate outside the old bases has size `|λ| (‖a‖² + ‖b‖²)^{1/2}`. -/
theorem norm_geoPre_sub_core (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ‖geoPre U V S G lr - U * coreBlock U V S G lr * Vᵀ‖ ^ 2 =
      lr ^ 2 * (‖leftBlock U V G‖ ^ 2 + ‖rightBlock U V G‖ ^ 2) := by
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  have e : geoPre U V S G lr - U * coreBlock U V S G lr * Vᵀ =
      (-lr) • (a * Vᵀ) + (-lr) • (U * b) := by
    rw [geoPre_eq_asm, asm, add_zero, Matrix.smul_mul, Matrix.mul_smul]
    abel
  rw [e, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
    inner_left_mul_right (transpose_mul_leftBlock hU G), norm_smul, norm_smul,
    Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The exact Pythagoras for the tangent gradient in blocks. -/
theorem norm_sq_tangentProj_eq (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (G : Matrix m n ℝ) :
    ‖tangentProj U V G‖ ^ 2 =
      ‖Uᵀ * G * V‖ ^ 2 + ‖leftBlock U V G‖ ^ 2 + ‖rightBlock U V G‖ ^ 2 := by
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  have hUa : Uᵀ * a = 0 := transpose_mul_leftBlock hU G
  have hbV : b * V = 0 := rightBlock_mul hV G
  set B := Uᵀ * G * V with hB
  have h12 : ⟪U * B * Vᵀ, a * Vᵀ⟫ = 0 := by
    rw [Matrix.mul_assoc U, Frobenius.inner_mul_left, mul_mul_of_mul_eq_zero hUa]
    simp
  have h13 : ⟪U * B * Vᵀ, U * b⟫ = 0 := by
    rw [Matrix.mul_assoc U, Frobenius.inner_mul_left, mul_mul_of_mul_eq_one hU,
      Frobenius.inner_mul_right, Matrix.transpose_transpose, hbV]
    simp
  have h23 : ⟪a * Vᵀ, U * b⟫ = 0 := inner_left_mul_right hUa b
  have n1 : ‖U * B * Vᵀ‖ = ‖B‖ := by
    rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hU,
      Frobenius.norm_mul_transpose_of_orthonormal hV]
  rw [tangentProj_eq_blocks, norm_add_sq_real, norm_add_sq_real, inner_add_left, h13, h23, h12,
    n1, Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
  ring

/-- **Tail, upper bound**: `(∑_{i>r} σ_i(Ŵ)²)^{1/2} ≤ λ² ‖a A⁻¹ b‖`. -/
theorem svTail_geoPre_le (hA : IsUnit (coreBlock U V S G lr).det) :
    tailNorm (geoPre U V S G lr) (Fintype.card k) ≤
      lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖ := by
  rw [geoPre_eq_asm, ← norm_schur_geo]
  exact svTail_asm_le U V hA _ _ _

/-- **First-order bound, no condition on the core**: `T_ϑ Ŵ` has rank at most `r` as soon as
`ϑ ≥ |λ| ‖b‖`.  This is the bound `size(new part) ≤ |λ| ‖P G‖`.  It is sharp only when the core
is
small; see `svTail_geoPre_le_interp_left` for the crossover. -/
theorem rank_trunc_geoPre_le_of_right (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (h : |lr| * ‖rightBlock U V G‖ ≤ ϑ) : (T (geoPre U V S G lr)).rank ≤ Fintype.card k := by
  set a' := (-lr) • leftBlock U V G with ha'
  set b' := (-lr) • rightBlock U V G with hb'
  set A := coreBlock U V S G lr with hA
  have e : geoPre U V S G lr = (U * A + a') * Vᵀ + U * b' := by
    rw [geoPre_eq_asm, asm, add_zero, Matrix.add_mul]
  refine (hT.rank_le _ ((U * A + a') * Vᵀ) ?_).trans
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _))
  rw [e, sub_add_cancel_left, norm_neg, Frobenius.norm_mul_of_orthonormal hU, hb', norm_smul,
    Real.norm_eq_abs, abs_neg]
  exact h

/-- First-order bound with the left block. -/
theorem rank_trunc_geoPre_le_of_left (hT : IsToleranceTruncation T ϑ) (hV : Vᵀ * V = 1)
    (h : |lr| * ‖leftBlock U V G‖ ≤ ϑ) : (T (geoPre U V S G lr)).rank ≤ Fintype.card k := by
  set a' := (-lr) • leftBlock U V G with ha'
  set b' := (-lr) • rightBlock U V G with hb'
  set A := coreBlock U V S G lr with hA
  have e : geoPre U V S G lr = U * (A * Vᵀ + b') + a' * Vᵀ := by
    rw [geoPre_eq_asm, asm, add_zero, Matrix.mul_add, Matrix.mul_assoc]
    abel
  refine (hT.rank_le _ (U * (A * Vᵀ + b')) ?_).trans
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _))
  rw [e, sub_add_cancel_left, norm_neg, Frobenius.norm_mul_transpose_of_orthonormal hV, ha',
    norm_smul, Real.norm_eq_abs, abs_neg]
  exact h

/-- **Target (1) as stated, first order.**  If `ϑ ≥ |λ| ‖P(W₀) G‖ / √2`, the truncated GeoLoRA
step
has rank at most `r`, for every doubly-normal `N` added to `G`, and with no condition on `S`. 
True,
but not sharp once `σ_min` exceeds `|λ| ‖P G‖`: the sharp threshold is second order, see
`rank_trunc_geoPre_eq`. -/
theorem rank_trunc_geoPre_le_of_tangent (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (h : |lr| * ‖tangentProj U V G‖ / √2 ≤ ϑ) {N : Matrix m n ℝ}
    (hNl : Uᵀ * N = 0) (hNr : N * V = 0) :
    (T (geoPre U V S (G + N) lr)).rank ≤ Fintype.card k := by
  rw [geoPre_add_normal U V S G lr hU hV hNl hNr]
  have h1 := norm_sq_tangentProj_eq hU hV G
  have hsq : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ ‖tangentProj U V G‖ ^ 2 / 2 →
      |lr| * x ≤ ϑ := fun x hx hx2 => by
    refine le_trans ?_ h
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 ?_
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    exact hx2
  rcases le_total ‖leftBlock U V G‖ ‖rightBlock U V G‖ with hle | hle
  · refine rank_trunc_geoPre_le_of_left hT hV (hsq _ (norm_nonneg _) ?_)
    nlinarith [sq_nonneg ‖Uᵀ * G * V‖, norm_nonneg (leftBlock U V G),
      norm_nonneg (rightBlock U V G)]
  · refine rank_trunc_geoPre_le_of_right hT hU (hsq _ (norm_nonneg _) ?_)
    nlinarith [sq_nonneg ‖Uᵀ * G * V‖, norm_nonneg (leftBlock U V G),
      norm_nonneg (rightBlock U V G)]

/-- **Two competitors for the crossover.**  For every real `t`, the rank-`r` matrix
`(U A + a) (Vᵀ + t A⁻¹ b)` gives `τ² ≤ (1 − t)² ‖b‖² + t² ‖a A⁻¹ b‖²`. -/
theorem svTail_asm_sq_le_right {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    {A : Matrix k k ℝ} (hA : IsUnit A.det) {a : Matrix m k ℝ} (ha : Uᵀ * a = 0)
    (b : Matrix k n ℝ) (t : ℝ) :
    tailNorm (asm U V A a b 0) (Fintype.card k) ^ 2 ≤
      (1 - t) ^ 2 * ‖b‖ ^ 2 + t ^ 2 * ‖a * A⁻¹ * b‖ ^ 2 := by
  set Y : Matrix m n ℝ := (U * A + a) * (Vᵀ + t • (A⁻¹ * b)) with hY
  have hj : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hrk : Y.rank ≤ Fintype.card k :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  have e : asm U V A a b 0 - Y = (1 - t) • (U * b) - t • (a * A⁻¹ * b) := by
    simp only [hY, asm, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc,
      mul_mul_of_mul_eq_one hj, sub_smul, one_smul, add_zero, smul_add]
    abel
  have hin : ⟪U * b, a * A⁻¹ * b⟫ = 0 := by
    rw [Frobenius.inner_mul_left, Matrix.mul_assoc a, mul_mul_of_mul_eq_zero ha]
    simp
  have h1 := svTail_le_norm_sub (asm U V A a b 0) Y hrk
  rw [e] at h1
  have h2 := pow_le_pow_left₀ (svTail_nonneg _ _) h1 2
  refine h2.trans (le_of_eq ?_)
  rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, hin, norm_smul, norm_smul,
    Frobenius.norm_mul_of_orthonormal hU]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The mirror competitor `(U + t a A⁻¹) (A Vᵀ + b)`. -/
theorem svTail_asm_sq_le_left {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hV : Vᵀ * V = 1)
    {A : Matrix k k ℝ} (hA : IsUnit A.det) (a : Matrix m k ℝ) {b : Matrix k n ℝ} (hb : b * V = 0)
    (t : ℝ) :
    tailNorm (asm U V A a b 0) (Fintype.card k) ^ 2 ≤
      (1 - t) ^ 2 * ‖a‖ ^ 2 + t ^ 2 * ‖a * A⁻¹ * b‖ ^ 2 := by
  set Y : Matrix m n ℝ := (U + t • (a * A⁻¹)) * (A * Vᵀ + b) with hY
  have hi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hrk : Y.rank ≤ Fintype.card k :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  have e : asm U V A a b 0 - Y = (1 - t) • (a * Vᵀ) - t • (a * A⁻¹ * b) := by
    simp only [hY, asm, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_assoc,
      mul_mul_of_mul_eq_one hi, sub_smul, one_smul, add_zero]
    abel
  have hin : ⟪a * Vᵀ, a * A⁻¹ * b⟫ = 0 := by
    rw [Frobenius.inner_mul_right, Matrix.transpose_transpose,
      show a * A⁻¹ * b * V = a * A⁻¹ * (b * V) by simp only [Matrix.mul_assoc], hb]
    simp
  have h1 := svTail_le_norm_sub (asm U V A a b 0) Y hrk
  rw [e] at h1
  have h2 := pow_le_pow_left₀ (svTail_nonneg _ _) h1 2
  refine h2.trans (le_of_eq ?_)
  rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, hin, norm_smul, norm_smul,
    Frobenius.norm_mul_transpose_of_orthonormal hV]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The optimisation behind the crossover. -/
lemma crossover_bound {τ p q₀ s c : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) (hp : 0 ≤ p) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ t → τ ^ 2 ≤ (1 - t) ^ 2 * p ^ 2 + t ^ 2 * (c * p / s) ^ 2)
    (hq : q₀ = c * p) :
    τ ≤ q₀ / √(s ^ 2 + c ^ 2) := by
  set D := s ^ 2 + c ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have h1 := h (s ^ 2 / D) (by positivity)
  have e : (1 - s ^ 2 / D) ^ 2 * p ^ 2 + (s ^ 2 / D) ^ 2 * (c * p / s) ^ 2 =
      c ^ 2 * p ^ 2 / D := by
    have hc2 : c ^ 2 = D - s ^ 2 := by rw [hD]; ring
    field_simp
    rw [hc2]
    ring
  rw [e] at h1
  rw [hq]
  refine (le_div_iff₀ (Real.sqrt_pos.2 hD0)).2 ?_
  refine (pow_le_pow_iff_left₀ (mul_nonneg hτ (Real.sqrt_nonneg _)) (by positivity)
    two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hD0.le]
  calc τ ^ 2 * D ≤ c ^ 2 * p ^ 2 / D * D := mul_le_mul_of_nonneg_right h1 hD0.le
    _ = (c * p) ^ 2 := by field_simp

/-- **The dependence on `σ_min`: the crossover.**  For `σ_min(A) ≥ s > 0`,
`τ_r(Ŵ) ≤ λ² ‖a‖ ‖b‖ / (s² + λ² ‖a‖²)^{1/2}`.  For `s ≫ |λ| ‖a‖` this is the second-order
`λ² ‖a‖ ‖b‖ / s`, for `s ≪ |λ| ‖a‖` it saturates at the first-order `|λ| ‖b‖`. -/
theorem svTail_geoPre_le_interp_left (hU : Uᵀ * U = 1) {s : ℝ} (hs : 0 < s)
    (hA : LowerBd (coreBlock U V S G lr) s) :
    tailNorm (geoPre U V S G lr) (Fintype.card k) ≤
      lr ^ 2 * ‖leftBlock U V G‖ * ‖rightBlock U V G‖ /
        √(s ^ 2 + (|lr| * ‖leftBlock U V G‖) ^ 2) := by
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  set A := coreBlock U V S G lr with hAdef
  have hdet := hA.isUnit_det hs
  have hUa : Uᵀ * ((-lr) • a) = 0 := by
    rw [Matrix.mul_smul, ha, transpose_mul_leftBlock hU, smul_zero]
  have key : ∀ t : ℝ, 0 ≤ t → tailNorm (geoPre U V S G lr) (Fintype.card k) ^ 2 ≤
      (1 - t) ^ 2 * (|lr| * ‖b‖) ^ 2 + t ^ 2 * ((|lr| * ‖a‖) * (|lr| * ‖b‖) / s) ^ 2 := by
    intro t ht
    have h1 := svTail_asm_sq_le_right (V := V) hU hdet hUa ((-lr) • b) t
    rw [← geoPre_eq_asm] at h1
    refine h1.trans ?_
    have e1 : ‖(-lr) • b‖ = |lr| * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg]
    have e2 : ‖(-lr) • a‖ = |lr| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg]
    have h2 := hA.norm_mul_inv_mul_le hs ((-lr) • a) ((-lr) • b)
    rw [e1, e2] at h2
    rw [e1]
    gcongr
  have h := crossover_bound (svTail_nonneg _ _) hs (by positivity) (by positivity) key
    (q₀ := lr ^ 2 * ‖a‖ * ‖b‖) (by
      have : lr ^ 2 = |lr| * |lr| := by rw [← sq, sq_abs]
      rw [this]
      ring)
  exact h

/-- Mirror of `svTail_geoPre_le_interp_left`, saturating at `|λ| ‖a‖`. -/
theorem svTail_geoPre_le_interp_right (hV : Vᵀ * V = 1) {s : ℝ} (hs : 0 < s)
    (hA : LowerBd (coreBlock U V S G lr) s) :
    tailNorm (geoPre U V S G lr) (Fintype.card k) ≤
      lr ^ 2 * ‖leftBlock U V G‖ * ‖rightBlock U V G‖ /
        √(s ^ 2 + (|lr| * ‖rightBlock U V G‖) ^ 2) := by
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  set A := coreBlock U V S G lr with hAdef
  have hdet := hA.isUnit_det hs
  have hbV : ((-lr) • b) * V = 0 := by
    rw [Matrix.smul_mul, hb, rightBlock_mul hV, smul_zero]
  have key : ∀ t : ℝ, 0 ≤ t → tailNorm (geoPre U V S G lr) (Fintype.card k) ^ 2 ≤
      (1 - t) ^ 2 * (|lr| * ‖a‖) ^ 2 + t ^ 2 * ((|lr| * ‖b‖) * (|lr| * ‖a‖) / s) ^ 2 := by
    intro t ht
    have h1 := svTail_asm_sq_le_left (U := U) hV hdet ((-lr) • a) hbV t
    rw [← geoPre_eq_asm] at h1
    refine h1.trans ?_
    have e1 : ‖(-lr) • b‖ = |lr| * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg]
    have e2 : ‖(-lr) • a‖ = |lr| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg]
    have h2 := hA.norm_mul_inv_mul_le hs ((-lr) • a) ((-lr) • b)
    rw [e1, e2, mul_comm (|lr| * ‖a‖)] at h2
    rw [e2]
    gcongr
  have h := crossover_bound (svTail_nonneg _ _) hs (by positivity) (by positivity) key
    (q₀ := lr ^ 2 * ‖a‖ * ‖b‖) (by
      have : lr ^ 2 = |lr| * |lr| := by rw [← sq, sq_abs]
      rw [this]
      ring)
  exact h

/-- **Target (1), the sharp threshold: freeze.**  If
`λ² ‖a A⁻¹ b‖ ≤ ϑ < σ_min(A)`, with `A = S − λ Uᵀ G V`, `a = (1 − U Uᵀ) G V`,
`b = Uᵀ G (1 − V Vᵀ)`, then the truncated GeoLoRA step has rank exactly `r`, for every
doubly-normal
`N` added to the gradient.  The threshold is second order in `λ` and depends on `G` through
`P(W₀) G` only.  The converse is `lt_rank_trunc_geoPre`, the exact coefficient
`tendsto_svTail_geoPre_div_sq`.  Compare the first-order `rank_trunc_geoPre_le_of_tangent`; for
the blind spot of `BlindSpot.lean`, `a = b = 0`, the threshold is `0`. -/
theorem rank_trunc_geoPre_eq (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {s : ℝ} (hs : 0 < s) (hA : LowerBd (coreBlock U V S G lr) s)
    (h1 : lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖ ≤ ϑ)
    (h2 : ϑ < s) {N : Matrix m n ℝ} (hNl : Uᵀ * N = 0) (hNr : N * V = 0) :
    (T (geoPre U V S (G + N) lr)).rank = Fintype.card k := by
  rw [geoPre_add_normal U V S G lr hU hV hNl hNr, geoPre_eq_asm]
  refine le_antisymm (rank_trunc_le_of_norm_schur_le hT U V (hA.isUnit_det hs) _ _ _ ?_)
    (card_le_rank_trunc hT hU hV hA ?_ ?_ (Matrix.mul_zero _) h2)
  · rwa [norm_schur_geo]
  · rw [Matrix.mul_smul, transpose_mul_leftBlock hU, smul_zero]
  · rw [Matrix.smul_mul, rightBlock_mul hV, smul_zero]

/-- **Target (1), sharpness of the threshold.**  If `κ ϑ < λ² ‖a A⁻¹ b‖ ≤ σ_min(A)`, the
truncated
GeoLoRA step has rank larger than `r`.  So below `λ² ‖a A⁻¹ b‖ / κ` there is no freeze, and the
threshold of `rank_trunc_geoPre_eq` is exact up to `κ = (1 + |λ| ‖a A⁻¹‖) (1 + |λ| ‖A⁻¹ b‖)`,
which
tends to `1` with `λ`. -/
theorem lt_rank_trunc_geoPre (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {s : ℝ} (hs : 0 < s) (hA : LowerBd (coreBlock U V S G lr) s)
    (h1 : lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖ ≤ s)
    (h2 : kappa (coreBlock U V S G lr) ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G) * ϑ <
      lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖) :
    Fintype.card k < (T (geoPre U V S G lr)).rank := by
  rw [geoPre_eq_asm]
  refine lt_rank_trunc_of_lt hT hU hV hs hA ?_ ?_ (Matrix.mul_zero _) (Matrix.zero_mul _)
    zero_le_one le_rfl ?_ ?_
  · rw [Matrix.mul_smul, transpose_mul_leftBlock hU, smul_zero]
  · rw [Matrix.smul_mul, rightBlock_mul hV, smul_zero]
  · rw [one_mul]
    refine (specNorm_le_frob _).trans ?_
    rwa [norm_schur_geo]
  · rwa [one_mul, norm_schur_geo]

/-- **Target (1) in terms of `‖P G‖` and `σ_min(S)` only.**  Put `c = s − |λ| ‖P(W₀) G‖ > 0`,
with
`σ_min(S) ≥ s`.  If `λ² ‖P(W₀) G‖² / (2 c) ≤ ϑ < c`, the truncated GeoLoRA step has rank exactly
`r`, for every doubly-normal `N`. -/
theorem rank_trunc_geoPre_eq_of_tangent (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {s : ℝ} (hS : LowerBd S s)
    (hc : 0 < s - |lr| * ‖tangentProj U V G‖)
    (h1 : lr ^ 2 * ‖tangentProj U V G‖ ^ 2 / (2 * (s - |lr| * ‖tangentProj U V G‖)) ≤ ϑ)
    (h2 : ϑ < s - |lr| * ‖tangentProj U V G‖) {N : Matrix m n ℝ} (hNl : Uᵀ * N = 0)
    (hNr : N * V = 0) :
    (T (geoPre U V S (G + N) lr)).rank = Fintype.card k := by
  set c := s - |lr| * ‖tangentProj U V G‖ with hcdef
  have hsq := norm_sq_tangentProj_eq hU hV G
  have hB : ‖Uᵀ * G * V‖ ≤ ‖tangentProj U V G‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by
      nlinarith [sq_nonneg ‖leftBlock U V G‖, sq_nonneg ‖rightBlock U V G‖])
  have hle : |lr| * ‖Uᵀ * G * V‖ ≤ |lr| * ‖tangentProj U V G‖ :=
    mul_le_mul_of_nonneg_left hB (abs_nonneg _)
  have hA1 := hS.sub_smul lr (Uᵀ * G * V) (by linarith)
  have hA : LowerBd (coreBlock U V S G lr) c := fun x => by
    have hx : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine le_trans ?_ (hA1 x)
    refine mul_le_mul_of_nonneg_right ?_ hx
    exact pow_le_pow_left₀ hc.le (by linarith) 2
  refine rank_trunc_geoPre_eq hT hU hV hc hA (le_trans ?_ h1) h2 hNl hNr
  have h3 := hA.norm_mul_inv_mul_le hc (leftBlock U V G) (rightBlock U V G)
  have h4 : ‖leftBlock U V G‖ * ‖rightBlock U V G‖ ≤ ‖tangentProj U V G‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖leftBlock U V G‖ - ‖rightBlock U V G‖), sq_nonneg ‖Uᵀ * G * V‖]
  have h5 : ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖ ≤
      ‖tangentProj U V G‖ ^ 2 / 2 / c :=
    h3.trans (div_le_div_of_nonneg_right h4 hc.le)
  calc lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖
      ≤ lr ^ 2 * (‖tangentProj U V G‖ ^ 2 / 2 / c) :=
        mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
    _ = lr ^ 2 * ‖tangentProj U V G‖ ^ 2 / (2 * c) := by
        field_simp

/-- A lower bound for `S` from invertibility alone, with the explicit constant
`1 / (‖S⁻¹‖ + 1)`. -/
lemma lowerBd_of_isUnit {S : Matrix k k ℝ} (hS : IsUnit S.det) :
    LowerBd S (‖S⁻¹‖ + 1)⁻¹ := fun x => by
  have h1 := sum_sq_mulVec_le S⁻¹ (S *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hS, Matrix.one_mulVec] at h1
  have hc : 0 < ‖S⁻¹‖ + 1 := by positivity
  have h2 : ‖S⁻¹‖ ^ 2 ≤ (‖S⁻¹‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hy : 0 ≤ ∑ i, (S *ᵥ x) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : ∑ j, x j ^ 2 ≤ (‖S⁻¹‖ + 1) ^ 2 * ∑ i, (S *ᵥ x) i ^ 2 :=
    h1.trans (mul_le_mul_of_nonneg_right h2 hy)
  rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
  exact h3

/-- **Target (1), the exact second-order law.**  For invertible `S`,
`(∑_{i>r} σ_i(Ŵ_λ)²)^{1/2} / λ² → ‖a S⁻¹ b‖` as `λ → 0`.  So new singular values of the GeoLoRA
assembly are second order, with exact coefficient `‖a S⁻¹ b‖`, not the `‖a‖ ‖b‖ / σ_min` of the
upper bound, which is attained only when `a` and `b` couple through the smallest singular
direction of `S` (`norm_mul_diagonal_inv_mul_eq`).  This makes the heuristic `λ² ‖a‖ ‖b‖ / σ`
exact. -/
theorem tendsto_svTail_geoPre_div_sq (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) (G : Matrix m n ℝ) :
    Tendsto (fun lr : ℝ => tailNorm (geoPre U V S G lr) (Fintype.card k) / lr ^ 2) (𝓝[≠] 0)
      (𝓝 ‖leftBlock U V G * S⁻¹ * rightBlock U V G‖) := by
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  set B := Uᵀ * G * V with hB
  set s₀ : ℝ := (‖S⁻¹‖ + 1)⁻¹ with hs₀
  have hs₀pos : 0 < s₀ := by positivity
  have hS₀ : LowerBd S s₀ := lowerBd_of_isUnit hS
  have hcore0 : coreBlock U V S G 0 = S := by simp [coreBlock]
  have hcore : Continuous fun lr : ℝ => coreBlock U V S G lr :=
    continuous_const.sub (continuous_id.smul continuous_const)
  -- continuity of the inverse at `0`
  have hinv : ContinuousAt (fun lr : ℝ => (coreBlock U V S G lr)⁻¹) 0 := by
    have hdet0 : ContinuousAt Ring.inverse (S.det) :=
      (NormedRing.inverse_continuousAt hS.unit)
    have h1 : ContinuousAt Inv.inv (coreBlock U V S G 0) := by
      rw [hcore0]
      exact continuousAt_matrix_inv S hdet0
    exact h1.comp hcore.continuousAt
  -- the two bounds as functions
  set φ : ℝ → ℝ := fun lr => ‖a * (coreBlock U V S G lr)⁻¹ * b‖ with hφ
  have hleft : ContinuousAt (fun lr : ℝ => a * (coreBlock U V S G lr)⁻¹) 0 :=
    ContinuousAt.comp (f := fun lr : ℝ => (coreBlock U V S G lr)⁻¹)
      (Frobenius.leftMulCLM (n := k) a).continuous.continuousAt hinv
  have hright : ContinuousAt (fun lr : ℝ => (coreBlock U V S G lr)⁻¹ * b) 0 :=
    ContinuousAt.comp (f := fun lr : ℝ => (coreBlock U V S G lr)⁻¹)
      (Frobenius.rightMulCLM (m := k) b).continuous.continuousAt hinv
  have hφc : ContinuousAt φ 0 :=
    (ContinuousAt.comp (f := fun lr : ℝ => a * (coreBlock U V S G lr)⁻¹)
      (Frobenius.rightMulCLM (m := m) b).continuous.continuousAt hleft).norm
  have hφ0 : φ 0 = ‖a * S⁻¹ * b‖ := by simp only [hφ, hcore0]
  set κ : ℝ → ℝ := fun lr => kappa (coreBlock U V S G lr) ((-lr) • a) ((-lr) • b) with hκ
  have hκc : ContinuousAt κ 0 := by
    have e : κ = fun lr => (1 + |lr| * ‖a * (coreBlock U V S G lr)⁻¹‖) *
        (1 + |lr| * ‖(coreBlock U V S G lr)⁻¹ * b‖) := by
      funext lr
      simp only [hκ, kappa, Matrix.smul_mul, Matrix.mul_smul, norm_smul, Real.norm_eq_abs, abs_neg]
    rw [e]
    exact (continuousAt_const.add (continuous_abs.continuousAt.mul hleft.norm)).mul
      (continuousAt_const.add (continuous_abs.continuousAt.mul hright.norm))
  have hκ0 : κ 0 = 1 := by simp [hκ, kappa]
  have hlow : Tendsto (fun lr => φ lr / κ lr) (𝓝 0) (𝓝 ‖a * S⁻¹ * b‖) := by
    have h := (hφc.div hκc (by rw [hκ0]; exact one_ne_zero)).tendsto
    have e : (φ / κ) 0 = ‖a * S⁻¹ * b‖ := by rw [Pi.div_apply, hφ0, hκ0, div_one]
    rw [e] at h
    exact h
  have hup : Tendsto φ (𝓝 0) (𝓝 ‖a * S⁻¹ * b‖) := by
    have := hφc.tendsto
    rwa [hφ0] at this
  -- eventual conditions
  have hsm : ContinuousAt (fun lr : ℝ => lr ^ 2 * φ lr) 0 := (continuousAt_id.pow 2).mul hφc
  have ev1 : ∀ᶠ lr in 𝓝 (0 : ℝ), lr ^ 2 * φ lr < s₀ / 2 := by
    have h0 : (fun lr : ℝ => lr ^ 2 * φ lr) 0 < s₀ / 2 := by simpa using hs₀pos
    exact hsm.eventually (gt_mem_nhds h0)
  have hw : ContinuousAt (fun lr : ℝ => |lr| * ‖B‖) 0 :=
    (continuous_abs.continuousAt).mul continuousAt_const
  have ev2 : ∀ᶠ lr in 𝓝 (0 : ℝ), |lr| * ‖B‖ < s₀ / 2 := by
    have h0 : (fun lr : ℝ => |lr| * ‖B‖) 0 < s₀ / 2 := by simpa using hs₀pos
    exact hw.eventually (gt_mem_nhds h0)
  have hAev : ∀ᶠ lr in 𝓝 (0 : ℝ), LowerBd (coreBlock U V S G lr) (s₀ / 2) := by
    filter_upwards [ev2] with lr hlr x
    have h1 := hS₀.sub_smul lr B (by linarith) x
    have hx : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hx) h1
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hmem : (∀ᶠ lr in 𝓝[≠] (0 : ℝ), lr ≠ 0) := eventually_mem_nhdsWithin
  have ev1' := nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ) ev1
  have hAev' := nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ) hAev
  have hupper : ∀ᶠ lr in 𝓝[≠] (0 : ℝ),
      tailNorm (geoPre U V S G lr) (Fintype.card k) / lr ^ 2 ≤ φ lr := by
    filter_upwards [hAev', hmem] with lr hA hlr
    have h1 := svTail_geoPre_le (U := U) (V := V) (S := S) (G := G) (lr := lr)
      (hA.isUnit_det (by positivity))
    have h2 : 0 < lr ^ 2 := by positivity
    rw [div_le_iff₀ h2]
    linarith [h1, mul_comm (φ lr) (lr ^ 2)]
  have hlower : ∀ᶠ lr in 𝓝[≠] (0 : ℝ),
      φ lr / κ lr ≤ tailNorm (geoPre U V S G lr) (Fintype.card k) / lr ^ 2 := by
    filter_upwards [hAev', hmem, ev1'] with lr hA hlr hsmall
    have h2 : 0 < lr ^ 2 := by positivity
    have hk : 0 < κ lr := lt_of_lt_of_le one_pos (one_le_kappa _ _ _)
    have h1 := mul_norm_schur_le_svTail hU hV (s := s₀ / 2) (by positivity) hA
      (a := (-lr) • a) (b := (-lr) • b) (X := 0)
      (by rw [Matrix.mul_smul, ha, transpose_mul_leftBlock hU, smul_zero])
      (by rw [Matrix.smul_mul, hb, rightBlock_mul hV, smul_zero])
      (Matrix.mul_zero _) (Matrix.zero_mul _) (t := 1) zero_le_one le_rfl
      (by
        rw [one_mul]
        refine (specNorm_le_frob _).trans ?_
        rw [norm_schur_geo]
        exact hsmall.le)
    rw [one_mul, norm_schur_geo, ← geoPre_eq_asm] at h1
    rw [div_le_div_iff₀ hk h2]
    linarith [h1, mul_comm (φ lr) (lr ^ 2)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.mono_left nhdsWithin_le_nhds)
    (hup.mono_left nhdsWithin_le_nhds) hlower hupper

/-- **The exact dependence on the singular values.**  If the core is `diag(σ)`, then
`a diag(σ)⁻¹ b = ∑ᵢ σᵢ⁻¹ aᵢ bᵢᵀ`, each singular direction of the core contributing with weight
`1 / σᵢ`.  So `‖a‖ ‖b‖ / σ_min` is attained precisely when the mass of `a` and `b` sits in the
smallest direction. -/
theorem mul_diagonal_inv_mul_eq_sum (σ : k → ℝ) (hσ : ∀ i, σ i ≠ 0) (a : Matrix m k ℝ)
    (b : Matrix k n ℝ) :
    a * (Matrix.diagonal σ)⁻¹ * b =
      ∑ i, (σ i)⁻¹ • Matrix.vecMulVec (fun l => a l i) (fun j => b i j) := by
  have hdet : IsUnit (Matrix.diagonal σ).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hσ i
  have hinv : (Matrix.diagonal σ)⁻¹ = Matrix.diagonal fun i => (σ i)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hσ i)
  ext l j
  rw [hinv, Matrix.sum_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **When `1 / σ` is attained.**  If `a` and `b` couple through the single direction `i` of
the core
`diag(σ)`, then `‖a diag(σ)⁻¹ b‖ = ‖a‖ ‖b‖ / |σᵢ|`.  With `i` the smallest direction this is
the upper
bound `LowerBd.norm_mul_inv_mul_le`, so that bound is sharp, and with another `i` the
coefficient is
`1 / σᵢ`, not `1 / σ_min`. -/
theorem norm_mul_diagonal_inv_mul_eq (σ : k → ℝ) (hσ : ∀ i, σ i ≠ 0) (i : k) (x : m → ℝ)
    (y : n → ℝ) :
    ‖Matrix.vecMulVec x (Pi.single i 1) * (Matrix.diagonal σ)⁻¹ *
        Matrix.vecMulVec (Pi.single i 1) y‖ =
      ‖Matrix.vecMulVec x (Pi.single i (1 : ℝ))‖ * ‖Matrix.vecMulVec (Pi.single i (1 : ℝ)) y‖ /
        |σ i| := by
  have hsum := mul_diagonal_inv_mul_eq_sum σ hσ (Matrix.vecMulVec x (Pi.single i 1))
    (Matrix.vecMulVec (Pi.single i 1) y)
  have e : Matrix.vecMulVec x (Pi.single i 1) * (Matrix.diagonal σ)⁻¹ *
      Matrix.vecMulVec (Pi.single i 1) y = (σ i)⁻¹ • Matrix.vecMulVec x y := by
    rw [hsum, Finset.sum_eq_single i]
    · congr 1
      ext l j
      simp [Matrix.vecMulVec_apply]
    · intro j _ hj
      have : (fun l => Matrix.vecMulVec x (Pi.single i (1 : ℝ)) l j) = 0 := by
        funext l
        simp [Matrix.vecMulVec_apply, hj]
      rw [this, vecMulVec_zero_left', smul_zero]
    · simp
  have hsi : 0 < |σ i| := abs_pos.2 (hσ i)
  have hee : (Pi.single i (1 : ℝ) : k → ℝ) ⬝ᵥ Pi.single i 1 = 1 := by simp
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv, div_eq_mul_inv, mul_comm]
  congr 1
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [mul_pow, norm_vecMulVec_sq, norm_vecMulVec_sq, norm_vecMulVec_sq, hee]
  ring

end Geo

/-- **Truncation grows the rank**, without a size condition: `κ ϑ < min(‖Z‖, s)` suffices. -/
theorem lt_rank_trunc_of_lt_min {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {A : Matrix k k ℝ} {s : ℝ} (hs : 0 < s) (hA : LowerBd A s)
    {a : Matrix m k ℝ} {b : Matrix k n ℝ} {X : Matrix m n ℝ} (ha : Uᵀ * a = 0) (hb : b * V = 0)
    (hXl : Uᵀ * X = 0) (hXr : X * V = 0)
    (h : kappa A a b * ϑ < min ‖schur A a b X‖ s) :
    Fintype.card k < (T (asm U V A a b X)).rank := by
  set z := ‖schur A a b X‖ with hz
  have hsp : specNorm (schur A a b X) ≤ z := specNorm_le_frob _
  rcases le_total z s with hle | hle
  · rw [min_eq_left hle] at h
    refine lt_rank_trunc_of_lt hT hU hV hs hA ha hb hXl hXr zero_le_one le_rfl ?_ ?_
    · rw [one_mul]
      exact hsp.trans hle
    · rwa [one_mul]
  · rw [min_eq_right hle] at h
    have hz0 : 0 < z := hs.trans_le hle
    refine lt_rank_trunc_of_lt hT hU hV hs hA ha hb hXl hXr (t := s / z) (by positivity)
      ((div_le_one hz0).2 hle) ?_ ?_
    · calc s / z * specNorm (schur A a b X) ≤ s / z * z :=
            mul_le_mul_of_nonneg_left hsp (by positivity)
        _ = s := by field_simp
    · rwa [div_mul_cancel₀ s hz0.ne']

/-! ### Target (2): the Galerkin assembly -/

section Galerkin

variable {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂] [DecidableEq k₁] [DecidableEq k₂]

/-- The compression `Û Ûᵀ N V̂ V̂ᵀ` of `N` to the augmented bases.  For orthonormal `Û`, `V̂` its
norm is `‖Ûᵀ N V̂‖` (`norm_compress`). -/
def compress (Uh : Matrix m k₁ ℝ) (Vh : Matrix n k₂ ℝ) (N : Matrix m n ℝ) : Matrix m n ℝ :=
  Uh * Uhᵀ * N * (Vh * Vhᵀ)

/-- The compression has the norm of the coefficient block `Ûᵀ N V̂`. -/
theorem norm_compress {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} (hUh : Uhᵀ * Uh = 1)
    (hVh : Vhᵀ * Vh = 1) (N : Matrix m n ℝ) : ‖compress Uh Vh N‖ = ‖Uhᵀ * N * Vh‖ := by
  have e : compress Uh Vh N = Uh * ((Uhᵀ * N * Vh) * Vhᵀ) := by
    simp only [compress, Matrix.mul_assoc]
  rw [e, Frobenius.norm_mul_of_orthonormal hUh, Frobenius.norm_mul_transpose_of_orthonormal hVh]

variable {U : Matrix m k ℝ} {V : Matrix n k ℝ} {G : Matrix m n ℝ} {Uh : Matrix m k₁ ℝ}
  {Vh : Matrix n k₂ ℝ}

lemma transpose_mul_proj (hUh : IsExactAugmentation Uh U (G * V)) :
    Uᵀ * (Uh * Uhᵀ) = Uᵀ := by
  have := congrArg Matrix.transpose hUh.captures_basis
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this

lemma transpose_mul_proj_right (hVh : IsExactAugmentation Vh V (Gᵀ * U)) :
    Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
  have := congrArg Matrix.transpose hVh.captures_basis
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this

lemma proj_mul_leftBlock (hUh : IsExactAugmentation Uh U (G * V)) :
    Uh * Uhᵀ * leftBlock U V G = leftBlock U V G := by
  have e : leftBlock U V G = G * V - U * (Uᵀ * G * V) := by
    simp only [leftBlock, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [e, Matrix.mul_sub, hUh.captures_aug, ← Matrix.mul_assoc, hUh.captures_basis]

lemma rightBlock_mul_proj (hVh : IsExactAugmentation Vh V (Gᵀ * U)) :
    rightBlock U V G * (Vh * Vhᵀ) = rightBlock U V G := by
  have h2 : Uᵀ * G * (Vh * Vhᵀ) = Uᵀ * G := by
    have := congrArg Matrix.transpose hVh.captures_aug
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  have e : rightBlock U V G = Uᵀ * G - (Uᵀ * G * V) * Vᵀ := by
    simp only [rightBlock, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, Matrix.sub_mul, h2, Matrix.mul_assoc (Uᵀ * G * V), transpose_mul_proj_right hVh]

/-- The compression of a doubly-normal matrix is doubly normal. -/
lemma transpose_mul_compress (hUh : IsExactAugmentation Uh U (G * V)) {N : Matrix m n ℝ}
    (hN : Uᵀ * N = 0) : Uᵀ * compress Uh Vh N = 0 := by
  rw [compress, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, transpose_mul_proj hUh,
    ← Matrix.mul_assoc, hN, Matrix.zero_mul]

lemma compress_mul (hVh : IsExactAugmentation Vh V (Gᵀ * U)) {N : Matrix m n ℝ}
    (hN : N * V = 0) : compress Uh Vh N * V = 0 := by
  rw [compress, Matrix.mul_assoc, Matrix.mul_assoc, hVh.captures_basis, hN, Matrix.mul_zero]

lemma transpose_mul_normalBlock (hU : Uᵀ * U = 1) (G : Matrix m n ℝ) :
    Uᵀ * normalBlock U V G = 0 := by
  rw [normalBlock, Matrix.mul_assoc (1 - U * Uᵀ), ← Matrix.mul_assoc Uᵀ, transpose_mul_one_sub hU,
    Matrix.zero_mul]

lemma normalBlock_mul (hV : Vᵀ * V = 1) (G : Matrix m n ℝ) :
    normalBlock U V G * V = 0 := by
  rw [normalBlock, Matrix.mul_assoc, one_sub_mul_self hV, Matrix.mul_zero]

/-- **The Galerkin assembly differs from GeoLoRA by the compressed doubly-normal block.**  From
the
actual step `Û Ûᵀ (W₀ − λ G) V̂ V̂ᵀ` of augmented BUG and DLRT, with `Û`, `V̂` exact
augmentations:
`Ŵ_G = U A Vᵀ − λ a Vᵀ − λ U b − λ Û Ûᵀ N V̂ V̂ᵀ`.  The core and the blocks `a`, `b` are those of
GeoLoRA. -/
theorem augStep_eq_asm (hUh : IsExactAugmentation Uh U (G * V))
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) (S : Matrix k k ℝ) (lr : ℝ) :
    augStep Uh Vh (U * S * Vᵀ) G lr =
      asm U V (coreBlock U V S G lr) ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G)
        ((-lr) • compress Uh Vh (normalBlock U V G)) := by
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  set N := normalBlock U V G with hN
  set B := Uᵀ * G * V with hB
  have hPU : Uh * Uhᵀ * U = U := hUh.captures_basis
  have hPV : Vᵀ * (Vh * Vhᵀ) = Vᵀ := transpose_mul_proj_right hVh
  have hPa : Uh * Uhᵀ * a = a := proj_mul_leftBlock hUh
  have hPb : b * (Vh * Vhᵀ) = b := rightBlock_mul_proj hVh
  have e1 : Uh * Uhᵀ * (U * S * Vᵀ) * (Vh * Vhᵀ) = U * S * Vᵀ := by
    rw [show Uh * Uhᵀ * (U * S * Vᵀ) * (Vh * Vhᵀ) =
      (Uh * Uhᵀ * U) * S * (Vᵀ * (Vh * Vhᵀ)) by simp only [Matrix.mul_assoc], hPU, hPV]
  have e2 : Uh * Uhᵀ * (U * B * Vᵀ) * (Vh * Vhᵀ) = U * B * Vᵀ := by
    rw [show Uh * Uhᵀ * (U * B * Vᵀ) * (Vh * Vhᵀ) =
      (Uh * Uhᵀ * U) * B * (Vᵀ * (Vh * Vhᵀ)) by simp only [Matrix.mul_assoc], hPU, hPV]
  have e3 : Uh * Uhᵀ * (a * Vᵀ) * (Vh * Vhᵀ) = a * Vᵀ := by
    rw [show Uh * Uhᵀ * (a * Vᵀ) * (Vh * Vhᵀ) =
      (Uh * Uhᵀ * a) * (Vᵀ * (Vh * Vhᵀ)) by simp only [Matrix.mul_assoc], hPa, hPV]
  have e4 : Uh * Uhᵀ * (U * b) * (Vh * Vhᵀ) = U * b := by
    rw [show Uh * Uhᵀ * (U * b) * (Vh * Vhᵀ) =
      (Uh * Uhᵀ * U) * (b * (Vh * Vhᵀ)) by simp only [Matrix.mul_assoc], hPU, hPb]
  have eG : Uh * Uhᵀ * G * (Vh * Vhᵀ) = U * B * Vᵀ + a * Vᵀ + U * b + compress Uh Vh N := by
    have h := eq_blocks U V G
    calc Uh * Uhᵀ * G * (Vh * Vhᵀ)
        = Uh * Uhᵀ * (U * B * Vᵀ + a * Vᵀ + U * b + N) * (Vh * Vhᵀ) := by rw [← h]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
          Matrix.add_mul, e2, e3, e4, compress]
  have e5 : Uh * Uhᵀ * (U * S * Vᵀ - lr • G) * (Vh * Vhᵀ) =
      U * S * Vᵀ - lr • (U * B * Vᵀ + a * Vᵀ + U * b + compress Uh Vh N) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.mul_smul, Matrix.smul_mul, eG]
  rw [augStep, e5, asm, coreBlock, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul]
  simp only [neg_smul, smul_add]
  abel

/-- The Schur complement of the Galerkin assembly: `Z = −λ C − λ² a A⁻¹ b`, with `C` the
compression
of `N`.  The first term is first order in `λ`, the second is the GeoLoRA term. -/
theorem schur_aug (A : Matrix k k ℝ) (a : Matrix m k ℝ) (b : Matrix k n ℝ) (C : Matrix m n ℝ)
    (lr : ℝ) :
    schur A ((-lr) • a) ((-lr) • b) ((-lr) • C) = (-lr) • C - lr ^ 2 • (a * A⁻¹ * b) := by
  rw [schur, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 2
  ring

/-- `‖Z‖ ≥ |λ| ‖C‖ − λ² ‖a A⁻¹ b‖`. -/
theorem le_norm_schur_aug (A : Matrix k k ℝ) (a : Matrix m k ℝ) (b : Matrix k n ℝ)
    (C : Matrix m n ℝ) (lr : ℝ) :
    |lr| * ‖C‖ - lr ^ 2 * ‖a * A⁻¹ * b‖ ≤ ‖schur A ((-lr) • a) ((-lr) • b) ((-lr) • C)‖ := by
  rw [schur_aug]
  have h := norm_sub_norm_le ((-lr) • C) (lr ^ 2 • (a * A⁻¹ * b))
  rwa [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (sq_nonneg lr)] at h

variable {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ} {S : Matrix k k ℝ} {lr : ℝ}

/-- **Target (2): the Galerkin step grows the rank.**  With `C = Û Ûᵀ N V̂ V̂ᵀ` and `A`, `a`,
`b` as
in GeoLoRA: if `κ ϑ < min(|λ| ‖C‖ − λ² ‖a A⁻¹ b‖, σ_min(A))`, the truncated Galerkin step has
rank
larger than `r`.  This corrects the plain reading of target (2): the block also contains the
GeoLoRA term, and the two can cancel (`augStep_cancellation`), so the subtraction cannot be
dropped.  Together with `rank_trunc_geoPre_eq` this is the difference between the assemblies:
first
order in `λ` against second order. -/
theorem lt_rank_trunc_augStep (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hUh : IsExactAugmentation Uh U (G * V))
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) {s : ℝ} (hs : 0 < s)
    (hA : LowerBd (coreBlock U V S G lr) s)
    (h : kappa (coreBlock U V S G lr) ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G) * ϑ <
      min (|lr| * ‖compress Uh Vh (normalBlock U V G)‖ -
        lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖) s) :
    Fintype.card k < (T (augStep Uh Vh (U * S * Vᵀ) G lr)).rank := by
  rw [augStep_eq_asm hUh hVh]
  refine lt_rank_trunc_of_lt_min hT hU hV hs hA ?_ ?_ ?_ ?_ (h.trans_le ?_)
  · rw [Matrix.mul_smul, transpose_mul_leftBlock hU, smul_zero]
  · rw [Matrix.smul_mul, rightBlock_mul hV, smul_zero]
  · rw [Matrix.mul_smul, transpose_mul_compress hUh (transpose_mul_normalBlock hU G), smul_zero]
  · rw [Matrix.smul_mul, compress_mul hVh (normalBlock_mul hV G), smul_zero]
  · exact min_le_min_right _ (le_norm_schur_aug _ _ _ _ _)

/-- **Target (2) in explicit form.**  If `σ_min(A) ≥ s > 0` and
`(1 + |λ| ‖a‖ / s) (1 + |λ| ‖b‖ / s) ϑ < min(|λ| ‖C‖ − λ² ‖a‖ ‖b‖ / s, s)`, the truncated
Galerkin
step has rank larger than `r`. -/
theorem lt_rank_trunc_augStep_explicit (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hUh : IsExactAugmentation Uh U (G * V))
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) {s : ℝ} (hs : 0 < s)
    (hA : LowerBd (coreBlock U V S G lr) s)
    (h : (1 + |lr| * ‖leftBlock U V G‖ / s) * (1 + |lr| * ‖rightBlock U V G‖ / s) * ϑ <
      min (|lr| * ‖compress Uh Vh (normalBlock U V G)‖ -
        lr ^ 2 * (‖leftBlock U V G‖ * ‖rightBlock U V G‖ / s)) s) :
    Fintype.card k < (T (augStep Uh Vh (U * S * Vᵀ) G lr)).rank := by
  have h0 : 0 ≤ ϑ := (norm_nonneg _).trans (hT.norm_sub_le 0)
  have hk := hA.kappa_le hs ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G)
  simp only [norm_smul, Real.norm_eq_abs, abs_neg] at hk
  have h3 := hA.norm_mul_inv_mul_le hs (leftBlock U V G) (rightBlock U V G)
  refine lt_rank_trunc_augStep hT hU hV hUh hVh hs hA (lt_of_le_of_lt ?_ (h.trans_le ?_))
  · exact mul_le_mul_of_nonneg_right hk h0
  · refine min_le_min_right _ ?_
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg lr)
    linarith

/-- The block outside the bases: for `Ũ ⊥ U` and `Ṽ ⊥ V`, only `X` is seen. -/
theorem transpose_mul_asm_mul {k₃ k₄ : Type*} [Fintype k₃] [Fintype k₄] {Ut : Matrix m k₃ ℝ}
    {Vt : Matrix n k₄ ℝ} (hUt : Uᵀ * Ut = 0) (hVt : Vᵀ * Vt = 0) (A : Matrix k k ℝ)
    (a : Matrix m k ℝ) (b : Matrix k n ℝ) (X : Matrix m n ℝ) :
    Utᵀ * asm U V A a b X * Vt = Utᵀ * X * Vt := by
  have hUt' : Utᵀ * U = 0 := by
    have := congrArg Matrix.transpose hUt
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using this
  simp only [asm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hVt,
    mul_mul_of_mul_eq_zero hUt', Matrix.mul_zero, Matrix.zero_mul, zero_add]

/-- **The block in question.**  For `Ũ ⊥ U`, `Ṽ ⊥ V`, the doubly-normal coefficient block of the
GeoLoRA step is zero. -/
theorem transpose_mul_geoPre_mul {k₃ k₄ : Type*} [Fintype k₃] [Fintype k₄] {Ut : Matrix m k₃ ℝ}
    {Vt : Matrix n k₄ ℝ} (hUt : Uᵀ * Ut = 0) (hVt : Vᵀ * Vt = 0) (S : Matrix k k ℝ)
    (G : Matrix m n ℝ) (lr : ℝ) : Utᵀ * geoPre U V S G lr * Vt = 0 := by
  rw [geoPre_eq_asm, transpose_mul_asm_mul hUt hVt]
  simp

/-- **The block in question.**  For `Ũ ⊥ U`, `Ṽ ⊥ V` inside the augmented bases, the
doubly-normal
coefficient block of the Galerkin step is `−λ` times the compression of `N`. -/
theorem transpose_mul_augStep_mul {k₃ k₄ : Type*} [Fintype k₃] [Fintype k₄] {Ut : Matrix m k₃ ℝ}
    {Vt : Matrix n k₄ ℝ} (hUt : Uᵀ * Ut = 0) (hVt : Vᵀ * Vt = 0)
    (hUh : IsExactAugmentation Uh U (G * V)) (hVh : IsExactAugmentation Vh V (Gᵀ * U))
    (hUt' : Uh * Uhᵀ * Ut = Ut) (hVt' : Vh * Vhᵀ * Vt = Vt) (S : Matrix k k ℝ) (lr : ℝ) :
    Utᵀ * augStep Uh Vh (U * S * Vᵀ) G lr * Vt = (-lr) • (Utᵀ * normalBlock U V G * Vt) := by
  have h1 : Utᵀ * (Uh * Uhᵀ) = Utᵀ := by
    have := congrArg Matrix.transpose hUt'
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  rw [augStep_eq_asm hUh hVh, transpose_mul_asm_mul hUt hVt, Matrix.mul_smul, Matrix.smul_mul,
    compress]
  congr 1
  rw [show Utᵀ * (Uh * Uhᵀ * normalBlock U V G * (Vh * Vhᵀ)) * Vt =
    (Utᵀ * (Uh * Uhᵀ)) * normalBlock U V G * ((Vh * Vhᵀ) * Vt) by
      simp only [Matrix.mul_assoc], h1, hVt']

end Galerkin

/-! ### Target (4): one probe -/

section Probe

variable {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂] [DecidableEq k₁] [DecidableEq k₂]

/-- Normalisation of a vector. -/
noncomputable def unitize {ι : Type*} [Fintype ι] (x : ι → ℝ) : ι → ℝ := (√(x ⬝ᵥ x))⁻¹ • x

lemma dotProduct_self_pos {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have h : 0 < x i * x i := mul_self_pos.2 hi
  exact lt_of_lt_of_le h (Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))

lemma unitize_dotProduct_self {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : x ≠ 0) :
    unitize x ⬝ᵥ unitize x = 1 := by
  have h0 := dotProduct_self_pos hx
  rw [unitize, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
    inv_pow, Real.sq_sqrt h0.le, inv_mul_cancel₀ h0.ne']

/-- The left probe of `geolora_probe`: the normalised part of `G ω` outside `Û`. -/
noncomputable def probeLeft (Uh : Matrix m k₁ ℝ) (G : Matrix m n ℝ) (ω : n → ℝ) : m → ℝ :=
  unitize ((1 - Uh * Uhᵀ) *ᵥ (G *ᵥ ω))

/-- The right probe of `geolora_probe`: the normalised part of `Gᵀ u` outside `V̂`. -/
noncomputable def probeRight (Vh : Matrix n k₂ ℝ) (G : Matrix m n ℝ) (u : m → ℝ) : n → ℝ :=
  unitize ((1 - Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ u))

/-- The GeoLoRA assembly with one probe pair: the GeoLoRA assembly with the
coefficient of the probe pair kept, `Ŵ_p = Ŵ − λ (uᵀ G v) u vᵀ`.  The cross blocks `uᵀ G V` and
`Uᵀ G v` of the code vanish by `vecMul_probe_mul`, `mul_mulVec_probe`, and
`geoProbePre_eq_geoLoRADir` gives the projector form. -/
noncomputable def geoProbePre (U : Matrix m k ℝ) (V : Matrix n k ℝ) (S : Matrix k k ℝ)
    (G : Matrix m n ℝ) (lr : ℝ) (u : m → ℝ) (v : n → ℝ) : Matrix m n ℝ :=
  geoPre U V S G lr - (lr * (u ⬝ᵥ (G *ᵥ v))) • Matrix.vecMulVec u v

/-- A probe pair: unit vectors outside the augmented bases. -/
structure IsProbePair (Uh : Matrix m k₁ ℝ) (Vh : Matrix n k₂ ℝ) (u : m → ℝ) (v : n → ℝ) :
    Prop where
  left_orth : Uhᵀ *ᵥ u = 0
  right_orth : Vhᵀ *ᵥ v = 0
  left_unit : u ⬝ᵥ u = 1
  right_unit : v ⬝ᵥ v = 1

lemma transpose_mulVec_residual {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] {W : Matrix p q ℝ} (hW : Wᵀ * W = 1) (y : p → ℝ) :
    Wᵀ *ᵥ ((1 - W * Wᵀ) *ᵥ y) = 0 := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hW, Matrix.one_mul,
    sub_self, Matrix.zero_mulVec]

/-- **The vectors of `geolora_probe` form a probe pair**, unless a residual vanishes (then the
code
drops the pair). -/
theorem isProbePair_probe {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} (hUh : Uhᵀ * Uh = 1)
    (hVh : Vhᵀ * Vh = 1) (G : Matrix m n ℝ) (ω : n → ℝ)
    (hx : (1 - Uh * Uhᵀ) *ᵥ (G *ᵥ ω) ≠ 0)
    (hy : (1 - Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ probeLeft Uh G ω) ≠ 0) :
    IsProbePair Uh Vh (probeLeft Uh G ω) (probeRight Vh G (probeLeft Uh G ω)) where
  left_orth := by
    rw [probeLeft, unitize, Matrix.mulVec_smul, transpose_mulVec_residual hUh, smul_zero]
  right_orth := by
    rw [probeRight, unitize, Matrix.mulVec_smul, transpose_mulVec_residual hVh, smul_zero]
  left_unit := unitize_dotProduct_self hx
  right_unit := unitize_dotProduct_self hy

/-- **The kept coefficient is the residual norm**: `uᵀ G v = ‖(1 − V̂ V̂ᵀ) Gᵀ u‖`. -/
theorem probe_value {Vh : Matrix n k₂ ℝ} (hVh : Vhᵀ * Vh = 1) (G : Matrix m n ℝ) (u : m → ℝ)
    (hy : (1 - Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ u) ≠ 0) :
    u ⬝ᵥ (G *ᵥ probeRight Vh G u) =
      √(((1 - Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ u)) ⬝ᵥ ((1 - Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ u))) := by
  set z := Gᵀ *ᵥ u with hz
  set y := (1 - Vh * Vhᵀ) *ᵥ z with hyd
  have h0 := dotProduct_self_pos hy
  have hzy : z ⬝ᵥ y = y ⬝ᵥ y := by
    have e1 : z = y + Vh *ᵥ (Vhᵀ *ᵥ z) := by
      have e0 : y = z - (Vh * Vhᵀ) *ᵥ z := by rw [hyd, Matrix.sub_mulVec, Matrix.one_mulVec]
      have e00 : Vh *ᵥ (Vhᵀ *ᵥ z) = (Vh * Vhᵀ) *ᵥ z := Matrix.mulVec_mulVec _ _ _
      rw [e0, e00]
      abel
    have e2 : (Vh *ᵥ (Vhᵀ *ᵥ z)) ⬝ᵥ y = 0 := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        transpose_mulVec_residual hVh]
      simp
    calc z ⬝ᵥ y = (y + Vh *ᵥ (Vhᵀ *ᵥ z)) ⬝ᵥ y := by rw [← e1]
      _ = y ⬝ᵥ y := by rw [add_dotProduct, e2, add_zero]
  have e : u ⬝ᵥ (G *ᵥ probeRight Vh G u) = z ⬝ᵥ probeRight Vh G u := by
    rw [Matrix.dotProduct_mulVec, hz, Matrix.mulVec_transpose]
  rw [e, probeRight, unitize, dotProduct_smul, hzy, smul_eq_mul]
  have hs : √(y ⬝ᵥ y) ^ 2 = y ⬝ᵥ y := Real.sq_sqrt h0.le
  have hsp : 0 < √(y ⬝ᵥ y) := Real.sqrt_pos.2 h0
  calc (√(y ⬝ᵥ y))⁻¹ * (y ⬝ᵥ y) = (√(y ⬝ᵥ y))⁻¹ * √(y ⬝ᵥ y) ^ 2 := by rw [hs]
    _ = √(y ⬝ᵥ y) := by field_simp

/-- For `u ⊥ Û`, the residual is `N̄ᵀ u`, with `N̄ = (1 − Û Ûᵀ) G (1 − V̂ V̂ᵀ)` the part of `G`
outside both augmented bases. -/
theorem residual_eq_normalBlock {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} (G : Matrix m n ℝ)
    {u : m → ℝ} (hu : Uhᵀ *ᵥ u = 0) :
    (1 - Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ u) = (normalBlock Uh Vh G)ᵀ *ᵥ u := by
  have e : (1 - Uh * Uhᵀ) *ᵥ u = u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero,
      sub_zero]
  have e2 : (normalBlock Uh Vh G)ᵀ = (1 - Vh * Vhᵀ) * Gᵀ * (1 - Uh * Uhᵀ) := by
    simp [normalBlock, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_assoc]
  rw [e2, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_mulVec]

/-- **What the probe sees.**  If `ω ⊥ V̂` and `N̄ ω ≠ 0`, the kept coefficient satisfies
`‖N̄ ω‖ / ‖ω‖ ≤ θ`, with `N̄ = (1 − Û Ûᵀ) G (1 − V̂ V̂ᵀ)`, the part of the gradient outside both
augmented bases.  For `ω` with a component in `V̂` this argument does not apply: `u` then also
contains `(1 − Û Ûᵀ) G V̂ V̂ᵀ ω`, and only the identity `θ = ‖N̄ᵀ u‖` remains. -/
theorem le_probe_value {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} (hUh : Uhᵀ * Uh = 1)
    (hVh : Vhᵀ * Vh = 1) (G : Matrix m n ℝ) {ω : n → ℝ} (hω : Vhᵀ *ᵥ ω = 0)
    (hx : (1 - Uh * Uhᵀ) *ᵥ (G *ᵥ ω) ≠ 0)
    (hy : (1 - Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ probeLeft Uh G ω) ≠ 0) :
    (normalBlock Uh Vh G *ᵥ ω) ⬝ᵥ (normalBlock Uh Vh G *ᵥ ω) ≤
      (probeLeft Uh G ω ⬝ᵥ (G *ᵥ probeRight Vh G (probeLeft Uh G ω))) ^ 2 * (ω ⬝ᵥ ω) := by
  set Nb := normalBlock Uh Vh G with hNb
  set u := probeLeft Uh G ω with hu
  have hp := isProbePair_probe hUh hVh G ω hx hy
  have hxN : (1 - Uh * Uhᵀ) *ᵥ (G *ᵥ ω) = Nb *ᵥ ω := by
    have e : (1 - Vh * Vhᵀ) *ᵥ ω = ω := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hω, Matrix.mulVec_zero,
        sub_zero]
    rw [hNb, normalBlock, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_mulVec]
  set x := Nb *ᵥ ω with hxdef
  have hval := probe_value hVh G u hy
  rw [residual_eq_normalBlock G hp.left_orth] at hval hy
  set y := Nbᵀ *ᵥ u with hyd
  have hxpos := dotProduct_self_pos (hxN ▸ hx)
  have hsq : (u ⬝ᵥ (G *ᵥ probeRight Vh G u)) ^ 2 = y ⬝ᵥ y := by
    rw [hval, Real.sq_sqrt (dotProduct_self_pos hy).le]
  have huform : u = (√(x ⬝ᵥ x))⁻¹ • x := by rw [hu, probeLeft, unitize, hxN]
  -- `‖x‖² = xᵀ N̄ ω = ‖x‖ yᵀ ω`, so `‖x‖ = yᵀ ω`
  have hdot : y ⬝ᵥ ω = √(x ⬝ᵥ x) := by
    have e : y ⬝ᵥ ω = u ⬝ᵥ x := by
      rw [hxdef, Matrix.dotProduct_mulVec, hyd, Matrix.mulVec_transpose]
    rw [e, huform, smul_dotProduct, smul_eq_mul]
    have hs : √(x ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hxpos.le
    have hsp : 0 < √(x ⬝ᵥ x) := Real.sqrt_pos.2 hxpos
    calc (√(x ⬝ᵥ x))⁻¹ * (x ⬝ᵥ x) = (√(x ⬝ᵥ x))⁻¹ * √(x ⬝ᵥ x) ^ 2 := by rw [hs]
      _ = √(x ⬝ᵥ x) := by field_simp
  have hcs : (y ⬝ᵥ ω) ^ 2 ≤ (y ⬝ᵥ y) * (ω ⬝ᵥ ω) := sq_dotProduct_le y ω
  rw [hsq]
  rw [hdot, Real.sq_sqrt hxpos.le] at hcs
  exact hcs

end Probe

section ProbeAssembly

variable {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂] [DecidableEq k₁] [DecidableEq k₂]
variable {U : Matrix m k ℝ} {V : Matrix n k ℝ} {G : Matrix m n ℝ} {Uh : Matrix m k₁ ℝ}
  {Vh : Matrix n k₂ ℝ} {u : m → ℝ} {v : n → ℝ}

lemma vecMulVec_zero_right (u : m → ℝ) : Matrix.vecMulVec u (0 : n → ℝ) = 0 := by
  ext i j
  simp [Matrix.vecMulVec_apply]

lemma vecMulVec_zero_left (v : n → ℝ) : Matrix.vecMulVec (0 : m → ℝ) v = 0 := by
  ext i j
  simp [Matrix.vecMulVec_apply]

lemma IsProbePair.transpose_mulVec_left (hp : IsProbePair Uh Vh u v)
    (hUh : IsExactAugmentation Uh U (G * V)) : Uᵀ *ᵥ u = 0 := by
  have h := transpose_mul_proj hUh
  calc Uᵀ *ᵥ u = (Uᵀ * (Uh * Uhᵀ)) *ᵥ u := by rw [h]
    _ = (Uᵀ * Uh) *ᵥ (Uhᵀ *ᵥ u) := by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = 0 := by rw [hp.left_orth, Matrix.mulVec_zero]

lemma IsProbePair.transpose_mulVec_right (hp : IsProbePair Uh Vh u v)
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) : Vᵀ *ᵥ v = 0 := by
  have h := transpose_mul_proj_right hVh
  calc Vᵀ *ᵥ v = (Vᵀ * (Vh * Vhᵀ)) *ᵥ v := by rw [h]
    _ = (Vᵀ * Vh) *ᵥ (Vhᵀ *ᵥ v) := by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = 0 := by rw [hp.right_orth, Matrix.mulVec_zero]

/-- **The cross block `uᵀ G V` vanishes**: the left probe is orthogonal to the `K`-step. -/
theorem vecMul_probe_mul (hp : IsProbePair Uh Vh u v) (hUh : IsExactAugmentation Uh U (G * V)) :
    Matrix.vecMul u (G * V) = 0 := by
  have h : G * V = Uh * (Uhᵀ * (G * V)) := by
    rw [← Matrix.mul_assoc]
    exact hUh.captures_aug.symm
  have h1 : Matrix.vecMul u Uh = 0 := by
    rw [← Matrix.mulVec_transpose, hp.left_orth]
  rw [h, ← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]

/-- **The cross block `Uᵀ G v` vanishes**: the right probe is orthogonal to the `L`-step. -/
theorem mul_mulVec_probe (hp : IsProbePair Uh Vh u v) (hVh : IsExactAugmentation Vh V (Gᵀ * U)) :
    (Uᵀ * G) *ᵥ v = 0 := by
  have h : Uᵀ * G = (Uᵀ * G * Vh) * Vhᵀ := by
    have := congrArg Matrix.transpose hVh.captures_aug
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this.symm
  rw [h, ← Matrix.mulVec_mulVec, hp.right_orth, Matrix.mulVec_zero]

/-- `b v = 0` for the right block. -/
lemma rightBlock_mulVec_probe (hp : IsProbePair Uh Vh u v)
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) : rightBlock U V G *ᵥ v = 0 := by
  have h0 := hp.transpose_mulVec_right hVh
  have e : (1 - V * Vᵀ) *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero,
      sub_zero]
  rw [rightBlock, ← Matrix.mulVec_mulVec, e]
  exact mul_mulVec_probe hp hVh

/-- **Projector form of `geolora_probe`.**  With `P̃₊ = Û Ûᵀ − U Uᵀ + u uᵀ` and
`Q̃₊ = V̂ V̂ᵀ − V Vᵀ + v vᵀ`, the code's assembly is the library's GeoLoRA direction for the
enlarged new bases plus the kept corner:
`Ŵ_p = W₀ − λ (P₀ Q₀ + P̃₊ Q₀ + P₀ Q̃₊) G − λ (u uᵀ) G (v vᵀ)`. -/
theorem geoProbePre_eq_geoLoRADir (hp : IsProbePair Uh Vh u v)
    (hUh : IsExactAugmentation Uh U (G * V)) (hVh : IsExactAugmentation Vh V (Gᵀ * U))
    (S : Matrix k k ℝ) (lr : ℝ) :
    geoProbePre U V S G lr u v =
      U * S * Vᵀ - lr • (geoLoRADir (leftProj U) (rightProj V)
          (leftProj Uh - leftProj U + Frobenius.leftMulCLM (Matrix.vecMulVec u u))
          (rightProj Vh - rightProj V + Frobenius.rightMulCLM (Matrix.vecMulVec v v)) G +
        Matrix.vecMulVec u u * G * Matrix.vecMulVec v v) := by
  have h1 : Uh * Uhᵀ * (G * V) = G * V := hUh.captures_aug
  have h2 : Uᵀ * G * (Vh * Vhᵀ) = Uᵀ * G := by
    have := congrArg Matrix.transpose hVh.captures_aug
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  have h3 : Matrix.vecMulVec u u * (G * (V * Vᵀ)) = 0 := by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, Matrix.vecMulVec_mul, vecMul_probe_mul hp hUh,
      vecMulVec_zero_right, Matrix.zero_mul]
  have h4 : U * Uᵀ * (G * Matrix.vecMulVec v v) = 0 := by
    rw [Matrix.mul_assoc U, ← Matrix.mul_assoc Uᵀ, Matrix.mul_vecMulVec, mul_mulVec_probe hp hVh,
      vecMulVec_zero_left, Matrix.mul_zero]
  have e0 : Matrix.vecMulVec u u * G * Matrix.vecMulVec v v =
      (u ⬝ᵥ (G *ᵥ v)) • Matrix.vecMulVec u v := by
    rw [Matrix.mul_assoc, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
    ring
  have e : geoLoRADir (leftProj U) (rightProj V)
      (leftProj Uh - leftProj U + Frobenius.leftMulCLM (Matrix.vecMulVec u u))
      (rightProj Vh - rightProj V + Frobenius.rightMulCLM (Matrix.vecMulVec v v)) G =
        tangentProj U V G := by
    rw [geoLoRADir, tangentProj_apply]
    simp only [add_apply, sub_apply, leftProj_apply, rightProj_apply',
      Frobenius.leftMulCLM_apply, Frobenius.rightMulCLM_apply]
    have e1 : Uh * Uhᵀ * (G * (V * Vᵀ)) = G * (V * Vᵀ) := by
      rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc (Uh * Uhᵀ), h1]
    have e2 : U * Uᵀ * (G * (Vh * Vhᵀ)) = U * Uᵀ * G := by
      rw [Matrix.mul_assoc U, ← Matrix.mul_assoc Uᵀ, h2, ← Matrix.mul_assoc]
    rw [h3, Matrix.mul_add, Matrix.mul_sub, e1, e2, h4]
    simp only [Matrix.mul_assoc]
    abel
  rw [e, e0, geoProbePre, geoPre, smul_add, smul_smul]
  abel

/-- The kept corner is doubly normal. -/
lemma IsProbePair.transpose_mul_vecMulVec (hp : IsProbePair Uh Vh u v)
    (hUh : IsExactAugmentation Uh U (G * V)) : Uᵀ * Matrix.vecMulVec u v = 0 := by
  rw [Matrix.mul_vecMulVec, hp.transpose_mulVec_left hUh, vecMulVec_zero_left]

lemma IsProbePair.vecMulVec_mul (hp : IsProbePair Uh Vh u v)
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) : Matrix.vecMulVec u v * V = 0 := by
  rw [Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, hp.transpose_mulVec_right hVh,
    vecMulVec_zero_right]

/-- `Ŵ_p` is the assembled matrix with the corner `X = −λ θ u vᵀ`, and the same `A`, `a`, `b` as
GeoLoRA: one probe changes the doubly-normal block and nothing else. -/
theorem geoProbePre_eq_asm (S : Matrix k k ℝ) (lr : ℝ) (U : Matrix m k ℝ) (V : Matrix n k ℝ)
    (G : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ) :
    geoProbePre U V S G lr u v =
      asm U V (coreBlock U V S G lr) ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G)
        ((-lr) • ((u ⬝ᵥ (G *ᵥ v)) • Matrix.vecMulVec u v)) := by
  have e : (-lr) • ((u ⬝ᵥ (G *ᵥ v)) • Matrix.vecMulVec u v) =
      -((lr * (u ⬝ᵥ (G *ᵥ v))) • Matrix.vecMulVec u v) := by
    rw [smul_smul, neg_mul, neg_smul]
  rw [geoProbePre, geoPre_eq_asm, asm, asm, add_zero, e, sub_eq_add_neg]

/-- **Pythagoras for the Schur complement with a probe**:
`‖Z_p‖² = λ² θ² + λ⁴ ‖a A⁻¹ b‖²`, because `u ⊥ a` and `v ⊥ b`. -/
theorem norm_sq_schur_probe (hp : IsProbePair Uh Vh u v)
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) (A : Matrix k k ℝ) (lr : ℝ) :
    ‖schur A ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G)
        ((-lr) • ((u ⬝ᵥ (G *ᵥ v)) • Matrix.vecMulVec u v))‖ ^ 2 =
      lr ^ 2 * (u ⬝ᵥ (G *ᵥ v)) ^ 2 +
        lr ^ 2 * lr ^ 2 * ‖leftBlock U V G * A⁻¹ * rightBlock U V G‖ ^ 2 := by
  set θ := u ⬝ᵥ (G *ᵥ v) with hθ
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  have hin : ⟪Matrix.vecMulVec u v, a * A⁻¹ * b⟫ = 0 := by
    rw [inner_vecMulVec_left, ← Matrix.mulVec_mulVec, hb, rightBlock_mulVec_probe hp hVh]
    simp
  have hn : ‖Matrix.vecMulVec u v‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_vecMulVec_vecMulVec, hp.left_unit, hp.right_unit,
      one_mul]
  rw [schur_aug, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, hin, norm_smul, norm_smul, norm_smul]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs, hn]
  ring

variable {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ} {S : Matrix k k ℝ} {lr : ℝ}

/-- **At most one new direction.**  If `ϑ ≥ λ² ‖a A⁻¹ b‖`, the threshold of GeoLoRA, one probe
raises the rank by at most one: the singular values it does not touch stay second order. -/
theorem rank_trunc_geoProbePre_le (hT : IsToleranceTruncation T ϑ)
    (hdet : IsUnit (coreBlock U V S G lr).det)
    (h : lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖ ≤ ϑ) :
    (T (geoProbePre U V S G lr u v)).rank ≤ Fintype.card k + 1 := by
  set A := coreBlock U V S G lr with hA
  set a := (-lr) • leftBlock U V G with ha
  set b := (-lr) • rightBlock U V G with hb
  set X := (-lr) • ((u ⬝ᵥ (G *ᵥ v)) • Matrix.vecMulVec u v) with hX
  set Y : Matrix m n ℝ := (U * A + a) * A⁻¹ * (A * Vᵀ + b) + X with hY
  have eM : geoProbePre U V S G lr u v = asm U V A a b X := geoProbePre_eq_asm S lr U V G u v
  have e : geoProbePre U V S G lr u v - Y = schur A a b 0 := by
    rw [eM, asm_eq_add_schur U V hdet, hY]
    simp only [schur]
    abel
  have hrkX : X.rank ≤ 1 := by
    have e1 : X = Matrix.vecMulVec ((-lr * (u ⬝ᵥ (G *ᵥ v))) • u) v := by
      ext i j
      simp [hX, Matrix.vecMulVec_apply, mul_assoc]
    rw [e1]
    exact Matrix.rank_vecMulVec_le _ _
  refine (hT.rank_le _ Y ?_).trans
    ((EckartYoung.rank_add_le _ _).trans (add_le_add (rank_asm_core_le U A a _) hrkX))
  rw [norm_sub_rev, e, hA, ha, hb, norm_schur_geo]
  exact h

/-- **The probe adds a first-order singular value.**  If `κ ϑ < min(|λ θ|, σ_min(A))`, the
truncated `geolora_probe` step has rank larger than `r`.  So the threshold of one direction rises
from second order `λ² ‖a A⁻¹ b‖` to first order `|λ| θ`, and `κ` is the same as for GeoLoRA. -/
theorem lt_rank_trunc_geoProbePre (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hp : IsProbePair Uh Vh u v) (hUh : IsExactAugmentation Uh U (G * V))
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) {s : ℝ} (hs : 0 < s)
    (hA : LowerBd (coreBlock U V S G lr) s)
    (h : kappa (coreBlock U V S G lr) ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G) * ϑ <
      min (|lr| * |u ⬝ᵥ (G *ᵥ v)|) s) :
    Fintype.card k < (T (geoProbePre U V S G lr u v)).rank := by
  rw [geoProbePre_eq_asm]
  refine lt_rank_trunc_of_lt_min hT hU hV hs hA ?_ ?_ ?_ ?_ (h.trans_le ?_)
  · rw [Matrix.mul_smul, transpose_mul_leftBlock hU, smul_zero]
  · rw [Matrix.smul_mul, rightBlock_mul hV, smul_zero]
  · rw [Matrix.mul_smul, Matrix.mul_smul, hp.transpose_mul_vecMulVec hUh, smul_zero, smul_zero]
  · rw [Matrix.smul_mul, Matrix.smul_mul, hp.vecMulVec_mul hVh, smul_zero, smul_zero]
  · refine min_le_min_right _ ?_
    have h1 := norm_sq_schur_probe hp hVh (coreBlock U V S G lr) lr
    refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |>.2
    rw [h1, mul_pow, sq_abs, sq_abs]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg lr) (sq_nonneg lr)) (sq_nonneg
      ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖)]

/-- **Target (4): what one probe changes.**  Between the two thresholds, `λ² ‖a A⁻¹ b‖ ≤ ϑ` and
`κ ϑ < min(|λ θ|, σ_min(A))`, the truncated `geolora_probe` step has rank exactly `r + 1`,
whereas
GeoLoRA stays at `r` (`rank_trunc_geoPre_eq`).  This is growth of one rank per step; the core and
the blocks `a`, `b` are unchanged. -/
theorem rank_trunc_geoProbePre_eq (hT : IsToleranceTruncation T ϑ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hp : IsProbePair Uh Vh u v) (hUh : IsExactAugmentation Uh U (G * V))
    (hVh : IsExactAugmentation Vh V (Gᵀ * U)) {s : ℝ} (hs : 0 < s)
    (hA : LowerBd (coreBlock U V S G lr) s)
    (h1 : lr ^ 2 * ‖leftBlock U V G * (coreBlock U V S G lr)⁻¹ * rightBlock U V G‖ ≤ ϑ)
    (h2 : kappa (coreBlock U V S G lr) ((-lr) • leftBlock U V G) ((-lr) • rightBlock U V G) * ϑ <
      min (|lr| * |u ⬝ᵥ (G *ᵥ v)|) s) :
    (T (geoProbePre U V S G lr u v)).rank = Fintype.card k + 1 :=
  le_antisymm (rank_trunc_geoProbePre_le hT (hA.isUnit_det hs) h1)
    (lt_rank_trunc_geoProbePre hT hU hV hp hUh hVh hs hA h2)

end ProbeAssembly

/-! ### The exact threshold at rank one -/

section RankOne

/-- The two radii of `[[s, β], [α, t]]`, in terms of which its singular values are `(D₊ ± D₋) /
2`
(in either order): `D₊² = (s − t)² + (α + β)²`. -/
noncomputable def radP (s β α t : ℝ) : ℝ := √((s - t) ^ 2 + (α + β) ^ 2)

/-- The second radius: `D₋² = (s + t)² + (α − β)²`. -/
noncomputable def radM (s β α t : ℝ) : ℝ := √((s + t) ^ 2 + (α - β) ^ 2)

lemma radP_sq (s β α t : ℝ) : radP s β α t ^ 2 = (s - t) ^ 2 + (α + β) ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma radM_sq (s β α t : ℝ) : radM s β α t ^ 2 = (s + t) ^ 2 + (α - β) ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- A `2 × 2` matrix of determinant zero has rank at most one. -/
lemma rank_le_one_of_det_eq_zero {Y : Matrix (Fin 2) (Fin 2) ℝ} (h : Y.det = 0) : Y.rank ≤ 1 := by
  obtain ⟨v, hv, hYv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 := LinearMap.finrank_range_add_finrank_ker Y.mulVecLin
  have h2 : 0 < Module.finrank ℝ (LinearMap.ker Y.mulVecLin) := by
    refine Module.finrank_pos_iff.2 ?_
    exact ⟨⟨⟨v, by simpa [LinearMap.mem_ker] using hYv⟩, 0, fun h0 => hv (congrArg Subtype.val
  h0)⟩⟩
  have h3 : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  rw [h3] at h1
  have h4 : Y.rank = Module.finrank ℝ (LinearMap.range Y.mulVecLin) := rfl
  omega

/-- A `2 × 2` matrix of rank at most one has determinant zero. -/
lemma det_eq_zero_of_rank_le_one {Y : Matrix (Fin 2) (Fin 2) ℝ} (h : Y.rank ≤ 1) : Y.det = 0 := by
  by_contra hc
  have hu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).2 (isUnit_iff_ne_zero.2 hc)
  have := Matrix.rank_of_isUnit Y hu
  simp at this
  omega

/-- The elementary inequality: `|√(a² + b²) − √(c² + d²)| ≤ √((a − c)² + (b − d)²)`. -/
lemma abs_sqrt_sub_sqrt_le (a b c d : ℝ) :
    |√(a ^ 2 + b ^ 2) - √(c ^ 2 + d ^ 2)| ≤ √((a - c) ^ 2 + (b - d) ^ 2) := by
  have e : ∀ x y : ℝ, ‖(⟨x, y⟩ : ℂ)‖ = √(x ^ 2 + y ^ 2) := fun x y => by
    rw [Complex.norm_def, Complex.normSq_mk]
    congr 1
    ring
  have h := abs_norm_sub_norm_le (⟨a, b⟩ : ℂ) ⟨c, d⟩
  have e2 : (⟨a, b⟩ : ℂ) - ⟨c, d⟩ = ⟨a - c, b - d⟩ := by
    apply Complex.ext <;> simp
  rwa [e, e, e2, e] at h

/-- **Lower bound for `2 × 2` matrices.**  Every `Y` of determinant zero has
`|D₊ − D₋| ≤ 2 ‖[[s, β], [α, t]] − Y‖`.  Proof: `det` is the difference of the squares of the
conformal and anticonformal parts, so `Y` has equal parts, and the triangle inequality holds in
each. -/
theorem abs_rad_sub_le (s β α t : ℝ) {Y : Matrix (Fin 2) (Fin 2) ℝ} (hY : Y.det = 0) :
    |radP s β α t - radM s β α t| ≤ 2 * ‖!![s, β; α, t] - Y‖ := by
  set y₁ := Y 0 0 with h1
  set y₂ := Y 0 1 with h2
  set y₃ := Y 1 0 with h3
  set y₄ := Y 1 1 with h4
  rw [Matrix.det_fin_two] at hY
  have hr : √((y₁ - y₄) ^ 2 + (y₂ + y₃) ^ 2) = √((y₁ + y₄) ^ 2 + (y₂ - y₃) ^ 2) := by
    congr 1
    nlinarith [hY]
  have ha := abs_sqrt_sub_sqrt_le (s - t) (α + β) (y₁ - y₄) (y₂ + y₃)
  have hb := abs_sqrt_sub_sqrt_le (s + t) (α - β) (y₁ + y₄) (y₃ - y₂)
  have hr' : √((y₁ + y₄) ^ 2 + (y₃ - y₂) ^ 2) = √((y₁ + y₄) ^ 2 + (y₂ - y₃) ^ 2) := by
    congr 1
    ring
  rw [hr'] at hb
  rw [hr] at ha
  set P := √((s - t - (y₁ - y₄)) ^ 2 + (α + β - (y₂ + y₃)) ^ 2) with hP
  set Q := √((s + t - (y₁ + y₄)) ^ 2 + (α - β - (y₃ - y₂)) ^ 2) with hQ
  have hP2 : P ^ 2 = (s - t - (y₁ - y₄)) ^ 2 + (α + β - (y₂ + y₃)) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hQ2 : Q ^ 2 = (s + t - (y₁ + y₄)) ^ 2 + (α - β - (y₃ - y₂)) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hE : ‖!![s, β; α, t] - Y‖ ^ 2 = (P ^ 2 + Q ^ 2) / 2 := by
    rw [Frobenius.norm_sq_eq_sum, hP2, hQ2]
    simp [Fin.sum_univ_two, ← h1, ← h2, ← h3, ← h4]
    ring
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have htri : |radP s β α t - radM s β α t| ≤ P + Q := by
    have e : radP s β α t - radM s β α t =
        (radP s β α t - √((y₁ + y₄) ^ 2 + (y₂ - y₃) ^ 2)) -
          (radM s β α t - √((y₁ + y₄) ^ 2 + (y₂ - y₃) ^ 2)) := by ring
    rw [e]
    exact (abs_sub _ _).trans (add_le_add ha hb)
  refine htri.trans ?_
  have hN := norm_nonneg (!![s, β; α, t] - Y)
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, hE]
  nlinarith [sq_nonneg (P - Q)]

/-- **The best rank-one approximation of a `2 × 2` matrix.**  For positive radii there is a
matrix
of rank at most one at distance exactly `|D₊ − D₋| / 2` from `[[s, β], [α, t]]`. -/
theorem exists_rank_le_one_norm_sub (s β α t : ℝ) (hP : 0 < radP s β α t)
    (hM : 0 < radM s β α t) :
    ∃ Y : Matrix (Fin 2) (Fin 2) ℝ, Y.rank ≤ 1 ∧
      2 * ‖!![s, β; α, t] - Y‖ = |radP s β α t - radM s β α t| := by
  set Dp := radP s β α t with hDp
  set Dm := radM s β α t with hDm
  have hPsq : Dp ^ 2 = (s - t) ^ 2 + (α + β) ^ 2 := radP_sq s β α t
  have hMsq : Dm ^ 2 = (s + t) ^ 2 + (α - β) ^ 2 := radM_sq s β α t
  set ρ := (Dp + Dm) / 2 with hρ
  set c₁ := ρ / Dm with hc₁
  set c₂ := ρ / Dp with hc₂
  have h1 : c₁ * Dm = ρ := div_mul_cancel₀ ρ hM.ne'
  have h2 : c₂ * Dp = ρ := div_mul_cancel₀ ρ hP.ne'
  set Y : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(c₁ * (s + t) + c₂ * (s - t)) / 2, (c₁ * (β - α) + c₂ * (α + β)) / 2;
       (c₂ * (α + β) - c₁ * (β - α)) / 2, (c₁ * (s + t) - c₂ * (s - t)) / 2] with hY
  have hdet : Y.det = 0 := by
    rw [hY, Matrix.det_fin_two_of]
    have e1 : c₁ ^ 2 * ((s + t) ^ 2 + (α - β) ^ 2) = ρ ^ 2 := by
      rw [← hMsq, ← mul_pow, h1]
    have e2 : c₂ ^ 2 * ((s - t) ^ 2 + (α + β) ^ 2) = ρ ^ 2 := by
      rw [← hPsq, ← mul_pow, h2]
    linear_combination (e1 - e2) / 4
  refine ⟨Y, rank_le_one_of_det_eq_zero hdet, ?_⟩
  have hnorm : ‖!![s, β; α, t] - Y‖ ^ 2 = (Dp - Dm) ^ 2 / 4 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two, hY, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e1 : (1 - c₁) ^ 2 * Dm ^ 2 = (Dm - ρ) ^ 2 := by
      rw [← mul_pow, sub_mul, one_mul, h1]
    have e2 : (1 - c₂) ^ 2 * Dp ^ 2 = (Dp - ρ) ^ 2 := by
      rw [← mul_pow, sub_mul, one_mul, h2]
    rw [hMsq] at e1
    rw [hPsq] at e2
    have e3 : (Dm - ρ) ^ 2 + (Dp - ρ) ^ 2 = (Dp - Dm) ^ 2 / 2 := by
      rw [hρ]
      ring
    linear_combination (e1 + e2) / 2 + e3 / 2
  have h3 : (2 * ‖!![s, β; α, t] - Y‖) ^ 2 = |Dp - Dm| ^ 2 := by
    rw [mul_pow, hnorm, sq_abs]
    ring
  exact (sq_eq_sq₀ (by positivity) (abs_nonneg _)).1 h3

variable {l l' : Type*} [Fintype l] [Fintype l'] [DecidableEq l] [DecidableEq l']

/-- **Exact tail of a two-dimensional block**: for orthonormal frames `P`, `Q` with two columns,
`(∑_{i ≥ 2} σ_i²)^{1/2} = |D₊ − D₋| / 2` for `P [[s, β], [α, t]] Qᵀ`. -/
theorem svTail_frame_eq {P : Matrix m (Fin 2) ℝ} {Q : Matrix n (Fin 2) ℝ} (hP : Pᵀ * P = 1)
    (hQ : Qᵀ * Q = 1) (s β α t : ℝ) (hDp : 0 < radP s β α t) (hDm : 0 < radM s β α t) :
    tailNorm (P * !![s, β; α, t] * Qᵀ) 1 = |radP s β α t - radM s β α t| / 2 := by
  set M := !![s, β; α, t] with hM
  set X := P * M * Qᵀ with hX
  refine le_antisymm ?_ ?_
  · obtain ⟨Y, hY, hYn⟩ := exists_rank_le_one_norm_sub s β α t hDp hDm
    have hrk : (P * Y * Qᵀ).rank ≤ 1 :=
      (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hY)
    have h1 := svTail_le_norm_sub X _ hrk
    have e : X - P * Y * Qᵀ = P * ((M - Y) * Qᵀ) := by
      rw [hX, Matrix.sub_mul, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
    rw [e, Frobenius.norm_mul_of_orthonormal hP,
      Frobenius.norm_mul_transpose_of_orthonormal hQ] at h1
    linarith
  · set Y := truncation X 1 with hY
    have hrk : Y.rank ≤ 1 := rank_truncation_le X 1
    set Z := Pᵀ * Y * Q with hZ
    have hZrk : Z.rank ≤ 1 :=
      (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hrk)
    have h1 := abs_rad_sub_le s β α t (det_eq_zero_of_rank_le_one hZrk)
    have e : Pᵀ * X * Q = M := by
      rw [hX]
      calc Pᵀ * (P * M * Qᵀ) * Q = (Pᵀ * P) * M * (Qᵀ * Q) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [hP, hQ, Matrix.one_mul, Matrix.mul_one]
    have e2 : M - Z = Pᵀ * (X - Y) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, e]
    have h2 : ‖M - Z‖ ≤ ‖X - Y‖ := by
      rw [e2]
      exact (norm_mul_le_of_orthonormal hQ _).trans (norm_transpose_mul_le hP _)
    have h3 : ‖X - Y‖ = tailNorm X 1 := by
      rw [norm_sub_rev, hY, norm_sub_truncation_eq]
    rw [h3] at h2
    linarith

/-- The exact threshold at rank one: `2 α β / (D₊ + D₋)`, `D± = (s² + (α ± β)²)^{1/2}`. -/
noncomputable def geoThreshold (s α β : ℝ) : ℝ :=
  2 * α * β / (√(s ^ 2 + (α + β) ^ 2) + √(s ^ 2 + (α - β) ^ 2))

/-- **The dependence on `σ`, exactly.**  For `α, β ≥ 0`, `s ≠ 0`, with `D₊ = (s² + (α +
β)²)^{1/2}`:
`α β / D₊ ≤ 2 α β / (D₊ + D₋) ≤ α β / |s|`, and it is also at most `min(α, β)`.  So the threshold
is `α β / |s|` for `|s| ≫ α + β` and saturates at `min(α, β)` as `s → 0`. -/
theorem geoThreshold_bounds {s α β : ℝ} (hs : s ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    α * β / √(s ^ 2 + (α + β) ^ 2) ≤ geoThreshold s α β ∧ geoThreshold s α β ≤ α * β / |s| ∧
      geoThreshold s α β ≤ min α β := by
  set Dp := √(s ^ 2 + (α + β) ^ 2) with hDp
  set Dm := √(s ^ 2 + (α - β) ^ 2) with hDm
  have hs2 : 0 < s ^ 2 := by positivity
  have hsabs : 0 < |s| := abs_pos.2 hs
  have hPsq : Dp ^ 2 = s ^ 2 + (α + β) ^ 2 := Real.sq_sqrt (by positivity)
  have hMsq : Dm ^ 2 = s ^ 2 + (α - β) ^ 2 := Real.sq_sqrt (by positivity)
  have hP : 0 < Dp := Real.sqrt_pos.2 (by positivity)
  have hM : 0 < Dm := Real.sqrt_pos.2 (by positivity)
  have hab : 0 ≤ α * β := mul_nonneg hα hβ
  have hle : Dm ≤ Dp := by
    refine (pow_le_pow_iff_left₀ hM.le hP.le two_ne_zero).1 ?_
    rw [hPsq, hMsq]
    nlinarith
  have hs1 : |s| ≤ Dm := by
    rw [hDm]
    refine Real.abs_le_sqrt ?_
    nlinarith [sq_nonneg (α - β)]
  have hsum : 0 < Dp + Dm := by positivity
  rw [geoThreshold]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hP hsum]
    nlinarith
  · rw [div_le_div_iff₀ hsum hsabs]
    nlinarith
  · have hP1 : α + β ≤ Dp := by
      rw [hDp]
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have hM1 : |α - β| ≤ Dm := by
      rw [hDm]
      refine Real.abs_le_sqrt ?_
      nlinarith
    rw [div_le_iff₀ hsum]
    rcases le_total α β with h | h
    · rw [min_eq_left h]
      have h2 : β - α ≤ Dm := by
        have := le_abs_self (β - α)
        rw [abs_sub_comm] at this
        linarith
      nlinarith
    · rw [min_eq_right h]
      have h2 : α - β ≤ Dm := (le_abs_self (α - β)).trans hM1
      nlinarith

/-- At `s = 0` the threshold is exactly the first-order value `min(α, β)`. -/
theorem geoThreshold_zero {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    geoThreshold 0 α β = min α β := by
  have e1 : √((0 : ℝ) ^ 2 + (α + β) ^ 2) = α + β := by
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq (add_nonneg hα hβ)]
  have e2 : √((0 : ℝ) ^ 2 + (α - β) ^ 2) = |α - β| := by
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs]
  rw [geoThreshold, e1, e2]
  rcases le_total α β with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]
    rcases hβ.eq_or_lt with h0 | h0
    · have hα0 : α = 0 := le_antisymm (by linarith) hα
      simp [hα0, ← h0]
    · have : α + β + -(α - β) = 2 * β := by ring
      rw [this]
      field_simp
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]
    rcases hα.eq_or_lt with h0 | h0
    · have hβ0 : β = 0 := le_antisymm (by linarith) hβ
      simp [hβ0, ← h0]
    · have : α + β + (α - β) = 2 * α := by ring
      rw [this]
      field_simp

end RankOne

section RankOneStep

variable [Unique k] {U : Matrix m k ℝ} {V : Matrix n k ℝ}

/-- **The exact tail at rank one.**  At a rank-one point, with `s = S − λ uᵀ G v`, `α = |λ| ‖a‖`,
`β = |λ| ‖b‖`: `τ₁(Ŵ) = 2 α β / (D₊ + D₋)`, `D± = (s² + (α ± β)²)^{1/2}`.  This holds for every
`σ`
and every `λ`, and contains the second-order law and the first-order saturation of
`geoThreshold_bounds`. -/
theorem svTail_geoPre_rank_one (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k ℝ)
    (G : Matrix m n ℝ) (lr : ℝ) (hs : coreBlock U V S G lr default default ≠ 0) :
    tailNorm (geoPre U V S G lr) 1 =
      geoThreshold (coreBlock U V S G lr default default)
        (|lr| * ‖leftBlock U V G‖) (|lr| * ‖rightBlock U V G‖) := by
  set e : k := default with he
  set A := coreBlock U V S G lr with hA
  set a := leftBlock U V G with ha
  set b := rightBlock U V G with hb
  have hkk : ∀ x : k, x = e := fun x => Unique.eq_default x
  have hdet : IsUnit A.det := by
    rw [Matrix.det_unique, isUnit_iff_ne_zero]
    exact hs
  have hcard : Fintype.card k = 1 := Fintype.card_unique
  have hUa : Uᵀ * a = 0 := transpose_mul_leftBlock hU G
  have hbV : b * V = 0 := rightBlock_mul hV G
  by_cases hab : ‖a‖ = 0 ∨ ‖b‖ = 0
  · have h0 : schur A ((-lr) • a) ((-lr) • b) 0 = 0 := by
      have h1 : a = 0 ∨ b = 0 := hab.imp norm_eq_zero.1 norm_eq_zero.1
      rw [schur_geo]
      rcases h1 with h1 | h1 <;> simp [h1]
    have h1 := svTail_asm_le U V hdet ((-lr) • a) ((-lr) • b) 0
    rw [h0, norm_zero, ← geoPre_eq_asm, hcard] at h1
    have h2 := le_antisymm h1 (svTail_nonneg _ _)
    rw [h2, geoThreshold]
    rcases hab with h3 | h3 <;> simp [h3]
  · have hna : ‖a‖ ≠ 0 := fun h => hab (Or.inl h)
    have hnb : ‖b‖ ≠ 0 := fun h => hab (Or.inr h)
    have hasum : ∑ i, a i e * a i e = ‖a‖ ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp only [Fintype.sum_unique, sq]
      rfl
    have hbsum : ∑ j, b e j * b e j = ‖b‖ ^ 2 := by
      rw [Frobenius.norm_sq_eq_sum]
      simp only [Fintype.sum_unique, sq]
      rfl
    have hUU : ∑ i, U i e * U i e = 1 := by
      have := congrFun (congrFun hU e) e
      simpa [Matrix.mul_apply] using this
    have hVV : ∑ i, V i e * V i e = 1 := by
      have := congrFun (congrFun hV e) e
      simpa [Matrix.mul_apply] using this
    have hUa0 : ∑ i, U i e * a i e = 0 := by
      have := congrFun (congrFun hUa e) e
      simpa [Matrix.mul_apply] using this
    have hbV0 : ∑ j, V j e * b e j = 0 := by
      have := congrFun (congrFun hbV e) e
      simpa [Matrix.mul_apply, mul_comm] using this
    set na := ‖a‖ with hnadef
    set nb := ‖b‖ with hnbdef
    have hasum' : ∑ i, (a i e / na) ^ 2 = 1 := by
      have h : ∀ i, (a i e / na) ^ 2 = a i e * a i e / na ^ 2 := fun i => by rw [div_pow, sq]
      simp only [h]
      rw [← Finset.sum_div, hasum]
      exact div_self (pow_ne_zero 2 hna)
    have hbsum' : ∑ j, (b e j / nb) ^ 2 = 1 := by
      have h : ∀ j, (b e j / nb) ^ 2 = b e j * b e j / nb ^ 2 := fun j => by rw [div_pow, sq]
      simp only [h]
      rw [← Finset.sum_div, hbsum]
      exact div_self (pow_ne_zero 2 hnb)
    set P : Matrix m (Fin 2) ℝ := Matrix.of fun i => ![U i e, a i e / na] with hP
    set Q : Matrix n (Fin 2) ℝ := Matrix.of fun j => ![V j e, b e j / nb] with hQ
    have hPP : Pᵀ * P = 1 := by
      ext p q
      fin_cases p <;> fin_cases q
      · simpa [Matrix.mul_apply, hP] using hUU
      · simp only [Matrix.mul_apply, hP]
        simp [mul_div_assoc', ← Finset.sum_div, hUa0]
      · simp only [Matrix.mul_apply, hP]
        simp [div_mul_eq_mul_div, ← Finset.sum_div, mul_comm (a _ e), hUa0]
      · simp only [Matrix.mul_apply, hP]
        simpa [sq] using hasum'
    have hQQ : Qᵀ * Q = 1 := by
      ext p q
      fin_cases p <;> fin_cases q
      · simpa [Matrix.mul_apply, hQ] using hVV
      · simp only [Matrix.mul_apply, hQ]
        simp [mul_div_assoc', ← Finset.sum_div, hbV0]
      · simp only [Matrix.mul_apply, hQ]
        simp [div_mul_eq_mul_div, ← Finset.sum_div, mul_comm (b e _), hbV0]
      · simp only [Matrix.mul_apply, hQ]
        simpa [sq] using hbsum'
    set s0 := A e e with hs0
    set α := |lr| * na with hα
    set β := |lr| * nb with hβ
    have hlr : α * β = lr ^ 2 * (na * nb) := by
      rw [hα, hβ, show lr ^ 2 = |lr| * |lr| by rw [← sq, sq_abs]]
      ring
    have hX : geoPre U V S G lr = P * !![s0, -lr * nb; -lr * na, 0] * Qᵀ := by
      rw [geoPre_eq_asm, asm, add_zero]
      ext i j
      have h1 : (U * A * Vᵀ) i j = U i e * s0 * V j e := by
        simp [Matrix.mul_apply, hs0]
        rfl
      have h2 : (((-lr) • a) * Vᵀ) i j = -lr * a i e * V j e := by
        simp [Matrix.mul_apply]
        rfl
      have h3 : (U * ((-lr) • b)) i j = U i e * (-lr * b e j) := by
        simp [Matrix.mul_apply]
        rfl
      rw [Matrix.add_apply, Matrix.add_apply, h1, h2, h3]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hP, hQ, Matrix.of_apply,
        Matrix.transpose_apply]
      simp
      field_simp
    have hD1 : radP s0 (-lr * nb) (-lr * na) 0 = √(s0 ^ 2 + (α + β) ^ 2) := by
      rw [radP]
      congr 1
      have : (α + β) ^ 2 = lr ^ 2 * (na + nb) ^ 2 := by
        rw [hα, hβ, show lr ^ 2 = |lr| ^ 2 from (sq_abs lr).symm]
        ring
      rw [this]
      ring
    have hD2 : radM s0 (-lr * nb) (-lr * na) 0 = √(s0 ^ 2 + (α - β) ^ 2) := by
      rw [radM]
      congr 1
      have : (α - β) ^ 2 = lr ^ 2 * (na - nb) ^ 2 := by
        rw [hα, hβ, show lr ^ 2 = |lr| ^ 2 from (sq_abs lr).symm]
        ring
      rw [this]
      ring
    have hs2 : 0 < s0 ^ 2 := by positivity
    have hPpos : 0 < √(s0 ^ 2 + (α + β) ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hMpos : 0 < √(s0 ^ 2 + (α - β) ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [hX, svTail_frame_eq hPP hQQ s0 _ _ 0 (by rwa [hD1]) (by rwa [hD2]), hD1, hD2, geoThreshold]
    set Dp := √(s0 ^ 2 + (α + β) ^ 2) with hDp
    set Dm := √(s0 ^ 2 + (α - β) ^ 2) with hDm
    have hPsq : Dp ^ 2 = s0 ^ 2 + (α + β) ^ 2 := Real.sq_sqrt (by positivity)
    have hMsq : Dm ^ 2 = s0 ^ 2 + (α - β) ^ 2 := Real.sq_sqrt (by positivity)
    have hab0 : 0 ≤ α * β := by rw [hlr]; positivity
    have hle : Dm ≤ Dp := by
      refine (pow_le_pow_iff_left₀ hMpos.le hPpos.le two_ne_zero).1 ?_
      rw [hPsq, hMsq]
      nlinarith
    rw [abs_of_nonneg (sub_nonneg.2 hle), div_eq_div_iff (by norm_num) (by positivity)]
    nlinarith

/-- **Target (1) at rank one: the exact freeze criterion.**  At a rank-one point the truncated
SVD
of the GeoLoRA iterate has rank at most one if and only if `ϑ ≥ 2 α β / (D₊ + D₋)`, for every
doubly-normal `N` in the gradient. -/
theorem rank_svdTrunc_geoPre_le_one_iff (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k ℝ)
    (G : Matrix m n ℝ) (lr : ℝ) (hs : coreBlock U V S G lr default default ≠ 0) {ϑ : ℝ}
    (hϑ : 0 ≤ ϑ) :
    (svdTrunc ϑ (geoPre U V S G lr)).rank ≤ 1 ↔
      geoThreshold (coreBlock U V S G lr default default)
        (|lr| * ‖leftBlock U V G‖) (|lr| * ‖rightBlock U V G‖) ≤ ϑ := by
  rw [rank_svdTrunc hϑ, ← svTail_geoPre_rank_one hU hV S G lr hs]
  constructor
  · intro h
    exact (svTail_antitone _ h).trans (tolRank_mem hϑ _)
  · exact tolRank_le_of_svTail_le

end RankOneStep

/-! ### The concrete algorithms -/

section Concrete

/-- One step of the concrete GeoLoRA method in the thin SVD `W = U diag(σ) Vᵀ`, with the
doubly-normal block set to zero: `T(W − λ P(W) ∇ℒ(W))`. -/
noncomputable def geoStep (T : Matrix m n ℝ → Matrix m n ℝ) (g : Matrix m n ℝ → Matrix m n ℝ)
    (lr : ℝ) (W : Matrix m n ℝ) : Matrix m n ℝ :=
  T (geoPre (thinU W) (thinV W) (Matrix.diagonal (thinσ W)) (g W) lr)

/-- In the thin SVD, `geoPre` is the tangent gradient step at `W`. -/
theorem geoPre_thin (G W : Matrix m n ℝ) (lr : ℝ) :
    geoPre (thinU W) (thinV W) (Matrix.diagonal (thinσ W)) G lr =
      W - lr • tangentProj (thinU W) (thinV W) G := by
  rw [geoPre, ← thin_eq]

/-- The freeze condition at `W`: a lower bound `s` of the core with
`λ² ‖a A⁻¹ b‖ ≤ ϑ < s`, in the thin SVD of `W`. -/
def FreezesAt (g : Matrix m n ℝ → Matrix m n ℝ) (lr ϑ : ℝ) (W : Matrix m n ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ LowerBd (coreBlock (thinU W) (thinV W) (Matrix.diagonal (thinσ W)) (g W) lr)
  s ∧
    lr ^ 2 * ‖leftBlock (thinU W) (thinV W) (g W) *
        (coreBlock (thinU W) (thinV W) (Matrix.diagonal (thinσ W)) (g W) lr)⁻¹ *
        rightBlock (thinU W) (thinV W) (g W)‖ ≤ ϑ ∧ ϑ < s

/-- **The freeze for the concrete GeoLoRA method**, one step: the rank does not change. -/
theorem rank_geoStep_eq {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) {g : Matrix m n ℝ → Matrix m n ℝ} {lr : ℝ} {W : Matrix m n ℝ}
    (h : FreezesAt g lr ϑ W) : (geoStep T g lr W).rank = W.rank := by
  obtain ⟨s, hs, hA, h1, h2⟩ := h
  have := rank_trunc_geoPre_eq hT (thinU_orthonormal W) (thinV_orthonormal W) hs hA h1 h2
    (N := 0) (Matrix.mul_zero _) (Matrix.zero_mul _)
  rw [add_zero, Fintype.card_fin] at this
  exact this

/-- **The freeze along an iteration.**  If the condition holds at each of the first `K` iterates,
the rank of the `K`-th iterate equals the initial rank.  This is conditional on the iterates: the
experiment shows the condition can persist, this statement does not derive that it does. -/
theorem rank_iterate_geoStep {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) {g : Matrix m n ℝ → Matrix m n ℝ} {lr : ℝ}
    (W : Matrix m n ℝ) (K : ℕ)
    (h : ∀ t < K, FreezesAt g lr ϑ ((geoStep T g lr)^[t] W)) :
    ((geoStep T g lr)^[K] W).rank = W.rank := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply', rank_geoStep_eq hT (h K (Nat.lt_succ_self K)),
      ih fun t ht => h t (ht.trans (Nat.lt_succ_self K))]

/-- **The growth for the concrete Galerkin method**: under the bound of `lt_rank_trunc_augStep`,
in the thin SVD of `W`, one step of `bugStep` raises the rank. -/
theorem lt_rank_bugStep {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) {g : Matrix m n ℝ → Matrix m n ℝ} {lr : ℝ} {W : Matrix m n ℝ}
    {s : ℝ} (hs : 0 < s)
    (hA : LowerBd (coreBlock (thinU W) (thinV W) (Matrix.diagonal (thinσ W)) (g W) lr) s)
    (h : kappa (coreBlock (thinU W) (thinV W) (Matrix.diagonal (thinσ W)) (g W) lr)
          ((-lr) • leftBlock (thinU W) (thinV W) (g W))
          ((-lr) • rightBlock (thinU W) (thinV W) (g W)) * ϑ <
      min (|lr| * ‖compress (orth (Matrix.fromCols (thinU W) (g W * thinV W)))
            (orth (Matrix.fromCols (thinV W) ((g W)ᵀ * thinU W)))
            (normalBlock (thinU W) (thinV W) (g W))‖ -
        lr ^ 2 * ‖leftBlock (thinU W) (thinV W) (g W) *
          (coreBlock (thinU W) (thinV W) (Matrix.diagonal (thinσ W)) (g W) lr)⁻¹ *
          rightBlock (thinU W) (thinV W) (g W)‖) s) :
    W.rank < (bugStep T g lr W).rank := by
  have hh := lt_rank_trunc_augStep hT (thinU_orthonormal W) (thinV_orthonormal W)
    (isExactAugmentation_orth _ _) (isExactAugmentation_orth _ _) hs hA h
  rw [← thin_eq, Fintype.card_fin] at hh
  exact hh

end Concrete

/-! ### Target (3): the same point, three outcomes -/

section Example

set_option linter.unusedSimpArgs false

/-- The left basis `e₀` of the example; also the right basis. -/
def exU : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- The augmented basis `[e₀, e₁]` of the example, on both sides. -/
def exUh : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- The gradient of the examples: the tangent part is `ε (e₀ e₁ᵀ + e₁ e₀ᵀ)`, the doubly-normal
part
is `ν e₁ e₁ᵀ + μ e₂ e₂ᵀ`.  It is `∇ L(W₀)` for `L(W) = ½ ‖W − C‖²` with `C = W₀ − G`. -/
def exG (ε ν μ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, ε, 0; ε, ν, 0; 0, 0, μ]

/-- The third coordinate vector, which is also the probe `ω` of the example. -/
def exE : Fin 3 → ℝ := ![0, 0, 1]

macro "ex_simp" : tactic =>
  `(tactic| simp [exUh, exU, exG, exE, leftBlock, rightBlock, normalBlock, compress, coreBlock,
    Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.transpose_apply, Matrix.one_apply, Matrix.sub_apply])

lemma exU_orth : exUᵀ * exU = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  ex_simp

lemma exUh_orth : exUhᵀ * exUh = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> ex_simp

lemma ex_aug (ε ν μ : ℝ) (hε : ε ≠ 0) :
    IsExactAugmentation exUh exU (exG ε ν μ * exU) where
  orthonormal := exUh_orth
  captures_basis := by
    ext i j
    fin_cases i <;> fin_cases j <;> ex_simp
  captures_aug := by
    ext i j
    fin_cases i <;> fin_cases j <;> ex_simp
  spanned := by
    refine ⟨!![1, 0], !![0, ε⁻¹], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> ex_simp
    all_goals exact (mul_inv_cancel₀ hε).symm

lemma ex_aug' (ε ν μ : ℝ) (hε : ε ≠ 0) :
    IsExactAugmentation exUh exU ((exG ε ν μ)ᵀ * exU) where
  orthonormal := exUh_orth
  captures_basis := (ex_aug ε ν μ hε).captures_basis
  captures_aug := by
    ext i j
    fin_cases i <;> fin_cases j <;> ex_simp
  spanned := by
    refine ⟨!![1, 0], !![0, ε⁻¹], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> ex_simp
    all_goals exact (mul_inv_cancel₀ hε).symm

lemma ex_core (ε ν μ lr : ℝ) : coreBlock exU exU 1 (exG ε ν μ) lr = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  ex_simp

lemma ex_left (ε ν μ : ℝ) : leftBlock exU exU (exG ε ν μ) = !![0; ε; 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> ex_simp

lemma ex_right (ε ν μ : ℝ) : rightBlock exU exU (exG ε ν μ) = !![0, ε, 0] := by
  ext i j
  fin_cases i
  fin_cases j <;> ex_simp

lemma ex_compress (ε ν μ : ℝ) :
    compress exUh exUh (normalBlock exU exU (exG ε ν μ)) = !![0, 0, 0; 0, ν, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> ex_simp

lemma ex_norm_left (ε ν μ : ℝ) : ‖leftBlock exU exU (exG ε ν μ)‖ = |ε| := by
  rw [ex_left]
  refine (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 ?_
  rw [Frobenius.norm_sq_eq_sum, sq_abs]
  simp [Fin.sum_univ_succ]

lemma ex_norm_right (ε ν μ : ℝ) : ‖rightBlock exU exU (exG ε ν μ)‖ = |ε| := by
  rw [ex_right]
  refine (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 ?_
  rw [Frobenius.norm_sq_eq_sum, sq_abs]
  simp [Fin.sum_univ_succ]

lemma ex_norm_compress (ν : ℝ) :
    ‖(!![0, 0, 0; 0, ν, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)‖ = |ν| := by
  refine (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 ?_
  rw [Frobenius.norm_sq_eq_sum, sq_abs]
  simp [Fin.sum_univ_succ]

lemma ex_lower : LowerBd (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 := fun x => by simp

lemma ex_resL (ε ν : ℝ) : (1 - exUh * exUhᵀ) *ᵥ (exG ε ν ν *ᵥ exE) = ν • exE := by
  ext i
  fin_cases i <;> ex_simp

lemma ex_resR (ε ν : ℝ) : (1 - exUh * exUhᵀ) *ᵥ ((exG ε ν ν)ᵀ *ᵥ exE) = ν • exE := by
  ext i
  fin_cases i <;> ex_simp

/-- The left probe of the example, for `ν > 0`. -/
lemma ex_probeLeft {ε ν : ℝ} (hν : 0 < ν) : probeLeft exUh (exG ε ν ν) exE = exE := by
  have e := ex_resL ε ν
  have h0 : ν • exE ⬝ᵥ ν • exE = ν ^ 2 := by
    simp [exE, dotProduct, Fin.sum_univ_succ, sq]
  rw [probeLeft, unitize, e, h0, Real.sqrt_sq hν.le, smul_smul, inv_mul_cancel₀ hν.ne', one_smul]

/-- The right probe of the example, for `ν > 0`. -/
lemma ex_probeRight {ε ν : ℝ} (hν : 0 < ν) : probeRight exUh (exG ε ν ν) exE = exE := by
  have e := ex_resR ε ν
  have h0 : ν • exE ⬝ᵥ ν • exE = ν ^ 2 := by
    simp [exE, dotProduct, Fin.sum_univ_succ, sq]
  rw [probeRight, unitize, e, h0, Real.sqrt_sq hν.le, smul_smul, inv_mul_cancel₀ hν.ne', one_smul]

/-- The kept coefficient of the example. -/
lemma ex_theta (ε ν : ℝ) : exE ⬝ᵥ (exG ε ν ν *ᵥ exE) = ν := by
  ex_simp

lemma ex_probePair {ε ν : ℝ} (hν : 0 < ν) : IsProbePair exUh exUh exE exE := by
  have hne : ν • exE ≠ 0 := by
    intro h
    have h2 : ν = 0 := by simpa [exE] using congrFun h 2
    exact hν.ne' h2
  have hx : (1 - exUh * exUhᵀ) *ᵥ (exG ε ν ν *ᵥ exE) ≠ 0 := by
    rwa [ex_resL]
  have hy : (1 - exUh * exUhᵀ) *ᵥ ((exG ε ν ν)ᵀ *ᵥ probeLeft exUh (exG ε ν ν) exE) ≠ 0 := by
    rwa [ex_probeLeft hν, ex_resR]
  have h := isProbePair_probe exUh_orth exUh_orth (exG ε ν ν) exE hx hy
  rwa [ex_probeLeft hν, ex_probeRight hν] at h

/-- **Target (3): the same point, three outcomes.**  At `W₀ = e₀ e₀ᵀ` in `ℝ^{3×3}`, `r = 1`, take
`G = exG (1/10) ν ν`, so `P(W₀) G` has size about `0.14` and `‖N‖ = √2 ν` is as large as one
likes,
`λ = 1/10` and `ϑ = 1/1000`.  For every tolerance truncation `T` with tolerance `ϑ` and every
`ν ≥ 1`:

1. the tolerance lies below the first-order size, `ϑ < |λ| ‖a‖` and `ϑ < |λ| ‖b‖`, so only the
   second-order threshold explains what follows;
2. GeoLoRA stays at rank `1`, for every doubly-normal `N` added to `G`;
3. the Galerkin step of augmented BUG and DLRT has rank at least `2`;
4. `geolora_probe`, with the actual probe `ω = e₂`, has rank exactly `2`. -/
theorem geoLoRA_frozen_galerkin_grows {T : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IsToleranceTruncation T (1 / 1000)) {ν : ℝ} (hν : 1 ≤ ν) :
    (1 / 1000 : ℝ) < |(1 / 10 : ℝ)| * ‖leftBlock exU exU (exG (1 / 10) ν ν)‖ ∧
    (1 / 1000 : ℝ) < |(1 / 10 : ℝ)| * ‖rightBlock exU exU (exG (1 / 10) ν ν)‖ ∧
    (∀ N : Matrix (Fin 3) (Fin 3) ℝ, exUᵀ * N = 0 → N * exU = 0 →
      (T (geoPre exU exU 1 (exG (1 / 10) ν ν + N) (1 / 10))).rank = 1) ∧
    2 ≤ (T (augStep exUh exUh (exU * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exUᵀ)
      (exG (1 / 10) ν ν) (1 / 10))).rank ∧
    (T (geoProbePre exU exU 1 (exG (1 / 10) ν ν) (1 / 10)
      (probeLeft exUh (exG (1 / 10) ν ν) exE)
      (probeRight exUh (exG (1 / 10) ν ν) (probeLeft exUh (exG (1 / 10) ν ν) exE)))).rank = 2 := by
  have hν0 : 0 < ν := by linarith
  set G := exG (1 / 10) ν ν with hG
  have hε : (1 / 10 : ℝ) ≠ 0 := by norm_num
  have habs : |(1 / 10 : ℝ)| = 1 / 10 := abs_of_pos (by norm_num)
  have hnL : ‖leftBlock exU exU G‖ = 1 / 10 := by rw [hG, ex_norm_left, habs]
  have hnR : ‖rightBlock exU exU G‖ = 1 / 10 := by rw [hG, ex_norm_right, habs]
  have hA : LowerBd (coreBlock exU exU 1 G (1 / 10)) 1 := by
    rw [hG, ex_core]
    exact ex_lower
  have hcore : ‖leftBlock exU exU G * (coreBlock exU exU 1 G (1 / 10))⁻¹ * rightBlock exU exU G‖ ≤
      1 / 100 := by
    refine (hA.norm_mul_inv_mul_le one_pos _ _).trans ?_
    rw [hnL, hnR]
    norm_num
  have hth : (1 / 10 : ℝ) ^ 2 *
      ‖leftBlock exU exU G * (coreBlock exU exU 1 G (1 / 10))⁻¹ * rightBlock exU exU G‖ ≤
      1 / 1000 := by
    nlinarith [norm_nonneg
      (leftBlock exU exU G * (coreBlock exU exU 1 G (1 / 10))⁻¹ * rightBlock exU exU G)]
  have hκ : kappa (coreBlock exU exU 1 G (1 / 10)) ((-(1 / 10 : ℝ)) • leftBlock exU exU G)
      ((-(1 / 10 : ℝ)) • rightBlock exU exU G) * (1 / 1000) ≤ 1 / 500 := by
    have h1 := hA.kappa_le one_pos ((-(1 / 10 : ℝ)) • leftBlock exU exU G)
      ((-(1 / 10 : ℝ)) • rightBlock exU exU G)
    have e1 : ‖(-(1 / 10 : ℝ)) • leftBlock exU exU G‖ = 1 / 100 := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, habs, hnL]
      norm_num
    have e2 : ‖(-(1 / 10 : ℝ)) • rightBlock exU exU G‖ = 1 / 100 := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, habs, hnR]
      norm_num
    rw [e1, e2] at h1
    refine (mul_le_mul_of_nonneg_right h1 (by norm_num)).trans ?_
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [habs, hnL]
    norm_num
  · rw [habs, hnR]
    norm_num
  · intro N hNl hNr
    exact rank_trunc_geoPre_eq hT exU_orth exU_orth one_pos hA hth (by norm_num) hNl hNr
  · have hC : ‖compress exUh exUh (normalBlock exU exU G)‖ = ν := by
      rw [hG, ex_compress, ex_norm_compress, abs_of_pos hν0]
    have h := lt_rank_trunc_augStep hT exU_orth exU_orth (ex_aug _ _ _ hε) (ex_aug' _ _ _ hε)
      one_pos hA (lt_of_le_of_lt hκ ?_)
    · rw [Fintype.card_fin] at h
      exact h
    · rw [hC, habs]
      refine lt_min ?_ (by norm_num)
      nlinarith
  · rw [ex_probeLeft hν0, ex_probeRight hν0]
    have hp := ex_probePair (ε := 1 / 10) hν0
    have h := rank_trunc_geoProbePre_eq hT exU_orth exU_orth hp (ex_aug _ _ _ hε)
      (ex_aug' _ _ _ hε) one_pos hA hth (lt_of_le_of_lt hκ ?_)
    · rw [Fintype.card_fin] at h
      exact h
    · rw [ex_theta, habs, abs_of_pos hν0]
      refine lt_min ?_ (by norm_num)
      nlinarith

/-- The statement `geoLoRA_frozen_galerkin_grows` for the concrete truncated SVD, so it is not
vacuous. -/
theorem geoLoRA_frozen_galerkin_grows_svdTrunc {ν : ℝ} (hν : 1 ≤ ν) :
    (svdTrunc (1 / 1000) (geoPre exU exU 1 (exG (1 / 10) ν ν) (1 / 10))).rank = 1 ∧
    2 ≤ (svdTrunc (1 / 1000) (augStep exUh exUh (exU * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exUᵀ)
      (exG (1 / 10) ν ν) (1 / 10))).rank := by
  obtain ⟨-, -, h1, h2, -⟩ := geoLoRA_frozen_galerkin_grows
    (isToleranceTruncation_svdTrunc (m := Fin 3) (n := Fin 3) (ϑ := 1 / 1000) (by norm_num)) hν
  have h3 := h1 0 (Matrix.mul_zero _) (Matrix.zero_mul _)
  rw [add_zero] at h3
  exact ⟨h3, h2⟩

/-- **The subtraction in target (2) cannot be dropped.**  For `L(W) = ½ ‖W − C‖²` with `C` of
rank
one and `λ = 1`, the first-order and the second-order term of the Galerkin block cancel exactly:
here `‖Û Ûᵀ N V̂ V̂ᵀ‖ = 1`, while the truncated Galerkin step has rank at most `1`, at every
tolerance. -/
theorem augStep_cancellation {T : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ} {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) :
    ‖compress exUh exUh (normalBlock exU exU (exG (-1) (-1) 0))‖ = 1 ∧
    (T (augStep exUh exUh (exU * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exUᵀ)
      (exG (-1) (-1) 0) 1)).rank ≤ 1 := by
  have hε : (-1 : ℝ) ≠ 0 := by norm_num
  constructor
  · rw [ex_compress, ex_norm_compress]
    simp
  · have h0 : 0 ≤ ϑ := (norm_nonneg _).trans (hT.norm_sub_le 0)
    have hdet : IsUnit (coreBlock exU exU 1 (exG (-1) (-1) 0) 1).det := by
      rw [ex_core]
      simp
    rw [augStep_eq_asm (ex_aug _ _ _ hε) (ex_aug' _ _ _ hε)]
    refine (rank_trunc_le_of_norm_schur_le hT exU exU hdet _ _ _ ?_).trans (by simp)
    rw [schur_aug, ex_core, ex_left, ex_right, ex_compress]
    have e : (-(1 : ℝ)) • (!![0, 0, 0; 0, -1, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) -
        (1 : ℝ) ^ 2 • ((!![0; -1; 0] : Matrix (Fin 3) (Fin 1) ℝ) *
          (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * (!![0, -1, 0] : Matrix (Fin 1) (Fin 3) ℝ)) = 0 := by
      rw [inv_one, Matrix.mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    rw [e, norm_zero]
    exact h0

end Example

end LeanDLRA.Novel.GeoLoRAFreeze
