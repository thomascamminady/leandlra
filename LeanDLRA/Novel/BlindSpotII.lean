import Mathlib
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Novel.BlindSpot
import LeanDLRA.Training.Descent
import LeanDLRA.Training.FactorizedDynamics
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# The blind spot and the probe, for the concrete algorithm

`LeanDLRA.Novel.BlindSpot` proves the blind spot and the
probe bound for abstract tolerance truncations and finitely supported probes.  This module proves
them for the algorithm as it is run, with no abstract hypothesis left on the bases or on the
truncation.

## The algorithm

For `W` of rank `r` with thin SVD `W = U diag(σ) Vᵀ` (`thinU`, `thinV`, `thinσ`), `G = ∇ℒ(W)` and a
truncation `T`, usually `svdTrunc ϑ` (the library's `EckartYoung.truncation` at the tolerance rank):

* `bugStep`: `Û = orth[U, G V]`, `V̂ = orth[V, Gᵀ U]`, `W⁺ = T(Û Ûᵀ (W − λ G) V̂ V̂ᵀ)`;
* `probeStep`: `Û = orth[U, G V, G ω]`, `V̂ = orth[V, Gᵀ Û]`, the same `W⁺`;
* `parPre`: the parallel (GeoLoRA) ordering `Û = orth[U, G V, G ωᵣ]`, `V̂ = orth[V, Gᵀ U, Gᵀ ωₗ]`.

`orth K` is an orthonormal basis of the column space with exactly `rank K` columns.

## Main results

* **Truncated SVD.**  `isToleranceTruncation_svdTrunc` discharges `IsToleranceTruncation`,
  `svdTrunc_eq_self_iff` is the exact criterion `T_ϑ W = W ⇔ ϑ < σ_{r-1}(W)`, `rank_svdTrunc` and
  `tolRank_eq_epsRank` identify the tolerance rank.
* **Theorem A.**  `bugStep_svdTrunc_eq_self`, `bugStep_iterate_eq_self`: at a point with
  `P(W) ∇ℒ(W) = 0` the concrete method stays for ever, for every `λ` and `0 ≤ ϑ < σ_{r-1}(W)`.
  `bugStep_iterate_quadratic` is the quadratic instance.
* **The saddle claim.**  `lt_specNorm_iff_exists` is `‖N‖₂ > s ⇔ ∃ unit u v, uᵀ N v > s`;
  `blindSpot_dichotomy` and `isLocalMinOn_quadLoss_iff` give the exact threshold: `A` is a global
  minimiser of the rank-`r` problem if `‖N‖₂ ≤ σ_{r-1}(A)`, and a saddle (smaller and larger values
  in every neighbourhood) if `‖N‖₂ > σ_{r-1}(A)`.  `exists_blindSpot_saddle` shows non-vacuity.
* **Probes.**  `IsIsotropicLaw` replaces the finite law: `integral_stdGaussian_mulVec_sq` and
  `integral_pi_gaussian_mulVec_sq` (Gaussian), `integral_sphere_mulVec_sq` (sphere),
  `isIsotropicLaw_ofProbe` (finite laws), all giving `E[‖N ω‖² / ‖ω‖²] = ‖N‖²_F / n`.
* **Theorem B.**  `probe_capture_ge`, `lintegral_probeProj_ge`; for the Gaussian probe the sharper
  `probe_capture_ge_rayleigh`, `div_rank_le_integral_ratio`, `lintegral_probeProj_gaussian_ge`:
  `E ‖Π̂ G‖² ≥ ‖P(W) G‖² + ‖N‖²_F / rank N ≥ ‖G‖²_F / min(m, n)`.
* **Convergence.**  `exists_lintegral_gaussian_grad_sq_le` is the main statement:
  `min_{k<K} E ‖∇ℒ(W_k)‖² ≤ min(m, n) [(ℒ(W₀) − ℒ_inf) / (K c) + B_K ϑ / c]` for `β`-smooth `ℒ`
  bounded below, with `B_K` derived.  `exists_iterE_grad_sq_le_svdTrunc` and
  `exists_pathExp_grad_sq_le_svdTrunc` state it for `EckartYoung.truncation`;
  `tendsto_lintegral_gaussian_grad_sq` is the gradient-coupled limit.
* **Escape.**  `probeStep_ne_self`, `loss_probeStep_le_of_blindSpot`,
  `rank_lt_probeStep_of_blindSpot`, `ae_ratio_pos_stdGaussian`: at a blind spot with `∇ℒ ≠ 0` the
  Gaussian probe moves, decreases the loss and grows the rank, almost surely, below a random
  tolerance threshold.
* **Rank.**  `rank_probePre_le`, `rank_probeStep_svdTrunc_le`, `rank_parPre_le`: `≤ 2 r + 1`.
* **Parallel ordering.**  `norm_sq_galerkin_ge_of_two_probes`, `lintegral_twoProbeRatio_ge`,
  `lintegral_parProj_ge`, `exists_lintegral_pi_grad_sq_le_parIter`, with constant
  `1 / (m n min(m, n))`.

## Remarks on the constants

* The Gaussian constant is `rank N` in place of `n`, so the convergence bound
  has `min(m, n)` in place of `n`.  This uses rotation invariance and fails for coordinate probes
  (`N = e₁e₁ᵀ` has `E[‖Nᵀ N ω‖² / ‖N ω‖²] = 1/n` against `‖N‖²_F / rank N = 1`).
* The gradient bound `B` is derived from smoothness and the lower bound
  (`gradPot_step_le`) in the fixed-tolerance theorem, at the price of a factor growing with `K`:
  `B_K = (2 β (ℒ(W₀) − ℒ_inf))^{1/2} + K β ϑ`, so `ϑ = O(1/K)` gives the rate `O(min(m, n) / K)`.
  The gradient-coupled theorems keep `B` as a hypothesis, since `B` enters the tolerance.
* "Rank `≤ 2r + 1`" is true of the matrix `Ŵ`, but the K-then-L basis `V̂ = orth[V, Gᵀ Û]` can have
  `3 r + 1` columns and costs `2 r + 1` products with `Gᵀ`, so "one extra matrix-vector product"
  holds only for `G`.  `div_le_twoProbeRatio` and `par_capture_ge_correlated` give the variant
  `V̂ = orth[V, Gᵀ U, Gᵀ N ω]` with `2 r + 1` columns on both sides, one extra product with each of
  `G`, `Gᵀ`, and the same constant.
* The saddle statement has the exact threshold `‖N‖₂ = σ_{r-1}(A)`, and "saddle" is proved
  (the point is not a local maximiser either), not only "not a local minimiser".
* The convergence statements are for `∃ k < K`, in expectation over the probes.

## Gaps

* `EckartYoung.truncation` goes through a `Classical.choice` eigenbasis, so it is not known to be a
  Borel function at tied singular values, and for a continuous probe law the iterates of
  `svdTrunc ϑ` are not known to be measurable.  Therefore:
  - for discrete probe laws every statement holds for `svdTrunc ϑ` as a genuine expectation
    (`exists_lintegral_pi_grad_sq_le_svdTrunc_finite`, `exists_pathExp_grad_sq_le_svdTrunc`);
  - for the Gaussian and the sphere, `svdTrunc ϑ` is covered only in the sense of the iterated lower
    integral `iterE`, which does not control the upper integral;
  - the genuine Gaussian theorems take a Borel tolerance truncation, and one exists
    (`exists_measurable_toleranceFamily`, a truncated SVD with a Borel choice at ties).  That it
    agrees with `svdTrunc ϑ` away from ties is not proved here.
* The rank constant needs `N ω ≠ 0` almost surely, proved for the Gaussian only; for the sphere only
  `n` is stated.
* The parallel constant `1 / (m n min(m, n))` is not sharp.  Numerics suggest `1 / min(m, n)²` for
  Gaussian probes and `1 / (m n)` for all isotropic laws (attained by coordinate probes aligned with
  the SVD).  The second is open, and the first needs off-diagonal cancellation not done here.
* Exact arithmetic throughout (`orth` drops zero directions).
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius ENNReal

namespace LeanDLRA.Novel.BlindSpotII

open LeanDLRA FactorizedDynamics BlindSpot EckartYoung
open LeanDLRA.WeylSingular (tailNorm)
open Matrix (rangeProj)

section Truncation

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! The singular-value tail `τ_r(X) = (∑_{i ≥ r} σ_i(X)²)^{1/2}`, the Frobenius error of the
rank-`r` truncated SVD, is the core `WeylSingular.tailNorm`, and the **tolerance rank** (the
smallest `r` whose tail is at most `ϑ`; arXiv 2104.05247 eq. (6), arXiv 2410.18720 Alg. 1) is the
core `epsRank` (`WeylSingular.epsRank_eq_sInf_tailNorm`). The local `svTail` and `tolRank` of an
earlier version of this file were these definitions (unification, follow-up of batch C3). -/

/-- The **truncated SVD at the tolerance rank**: the library's `EckartYoung.truncation` at
`epsRank ϑ X`.  This is the concrete map `T_ϑ` of rank-adaptive BUG, DLRT and GeoLoRA. -/
noncomputable def svdTrunc (ϑ : ℝ) (X : Matrix m n ℝ) : Matrix m n ℝ :=
  truncation X (epsRank ϑ X)

lemma svTail_nonneg (X : Matrix m n ℝ) (r : ℕ) : 0 ≤ tailNorm X r := Real.sqrt_nonneg _

lemma svTail_sq (X : Matrix m n ℝ) (r : ℕ) :
    tailNorm X r ^ 2 =
      ∑ i ∈ Ico r (Fintype.card n), (Matrix.toEuclideanLin X).singularValues i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma norm_sub_truncation_eq (X : Matrix m n ℝ) (r : ℕ) :
    ‖truncation X r - X‖ = tailNorm X r := by
  rw [norm_sub_rev, norm_sub_truncation, WeylSingular.tailNorm]

lemma svTail_le_norm_sub (X Y : Matrix m n ℝ) {r : ℕ} (hY : Y.rank ≤ r) :
    tailNorm X r ≤ ‖X - Y‖ :=
  sqrt_sum_sq_singularValues_le_norm_sub X Y hY

lemma svTail_eq_zero_of_rank_le {X : Matrix m n ℝ} {r : ℕ} (h : X.rank ≤ r) : tailNorm X r = 0 :=
  le_antisymm (by simpa using svTail_le_norm_sub X X h) (svTail_nonneg X r)

lemma svTail_antitone (X : Matrix m n ℝ) {r s : ℕ} (h : r ≤ s) : tailNorm X s ≤ tailNorm X r := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _)
  exact Finset.Ico_subset_Ico_left h

/-- The set defining the tolerance rank is nonempty for `ϑ ≥ 0`. -/
lemma tolRank_mem {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (X : Matrix m n ℝ) : tailNorm X (epsRank ϑ X) ≤ ϑ := by
  have hne : {r | tailNorm X r ≤ ϑ}.Nonempty :=
    ⟨Fintype.card n, show tailNorm X _ ≤ ϑ by simpa [WeylSingular.tailNorm] using hϑ⟩
  rw [WeylSingular.epsRank_eq_sInf_tailNorm]
  exact Nat.sInf_mem hne

lemma lt_svTail_of_lt_tolRank {ϑ : ℝ} {X : Matrix m n ℝ} {s : ℕ} (h : s < epsRank ϑ X) :
    ϑ < tailNorm X s := by
  rw [WeylSingular.epsRank_eq_sInf_tailNorm] at h
  exact not_le.mp (Nat.notMem_of_lt_sInf h)

lemma tolRank_le_of_svTail_le {ϑ : ℝ} {X : Matrix m n ℝ} {r : ℕ} (h : tailNorm X r ≤ ϑ) :
    epsRank ϑ X ≤ r := by
  rw [WeylSingular.epsRank_eq_sInf_tailNorm]
  exact Nat.sInf_le h

omit [DecidableEq n] in
lemma tolRank_le_rank_of_norm_sub_le {ϑ : ℝ} {X Y : Matrix m n ℝ} (h : ‖Y - X‖ ≤ ϑ) :
    epsRank ϑ X ≤ Y.rank := by
  classical
  exact tolRank_le_of_svTail_le ((svTail_le_norm_sub X Y le_rfl).trans (by rwa [norm_sub_rev]))

/-- The truncated SVD is within the tolerance. -/
theorem norm_svdTrunc_sub_le {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (X : Matrix m n ℝ) :
    ‖svdTrunc ϑ X - X‖ ≤ ϑ := by
  rw [svdTrunc, norm_sub_truncation_eq]
  exact tolRank_mem hϑ X

/-- The truncated SVD has exactly the tolerance rank. -/
theorem rank_svdTrunc {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (X : Matrix m n ℝ) :
    (svdTrunc ϑ X).rank = epsRank ϑ X :=
  le_antisymm (rank_truncation_le X _) (tolRank_le_rank_of_norm_sub_le (norm_svdTrunc_sub_le hϑ X))

/-- **The library's truncated SVD is a tolerance truncation.**  This discharges
the abstract `IsToleranceTruncation` of the blind-spot module for `EckartYoung.truncation` at the
tolerance rank, so that its results hold for the map actually used; the three properties are
Eckart–Young–Mirsky in the form `norm_sub_truncation_le`, `rank_le_of_tolerance`. -/
theorem isToleranceTruncation_svdTrunc {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    IsToleranceTruncation (svdTrunc (m := m) (n := n) ϑ) ϑ where
  norm_sub_le X := norm_svdTrunc_sub_le hϑ X
  rank_le X Y hY := by
    rw [rank_svdTrunc hϑ]
    exact tolRank_le_rank_of_norm_sub_le hY
  norm_sub_le_of_rank_le X Y hY := by
    rw [rank_svdTrunc hϑ] at hY
    rw [norm_sub_rev, svdTrunc, norm_sub_rev Y]
    exact norm_sub_truncation_le X hY

lemma sq_singularValues_le_svTail_sq (X : Matrix m n ℝ) {i : ℕ} (hi : i < Fintype.card n) :
    (Matrix.toEuclideanLin X).singularValues i ≤ tailNorm X i := by
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => (Matrix.toEuclideanLin X).singularValues j ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_Ico.2 ⟨le_rfl, hi⟩)

/-- `σ_{r-1}` is the tail before the last nonzero singular value. -/
lemma svTail_pred_rank {X : Matrix m n ℝ} {r : ℕ} (hr : X.rank = r + 1) :
    tailNorm X r = (Matrix.toEuclideanLin X).singularValues r := by
  have hlt : r < Fintype.card n := by
    have := Matrix.rank_le_card_width X
    omega
  have h0 : tailNorm X (r + 1) ^ 2 = 0 := by
    rw [svTail_eq_zero_of_rank_le hr.le]; simp
  have h1 := svTail_sq X r
  rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ← svTail_sq, h0, add_zero] at h1
  exact (sq_eq_sq₀ (svTail_nonneg X r)
    ((Matrix.toEuclideanLin X).singularValues_nonneg r)).1 h1

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- A matrix of rank zero vanishes. -/
lemma eq_zero_of_rank_eq_zero {X : Matrix m n ℝ} (h : X.rank = 0) : X = 0 := by
  have h1 := norm_sub_truncation_eq X 0
  rw [truncation_zero, zero_sub, norm_neg, svTail_eq_zero_of_rank_le h.le] at h1
  exact norm_eq_zero.1 h1

/-- **Exact criterion for the truncated SVD to keep a matrix**: `T_ϑ W = W` iff `ϑ` lies below all
nonzero singular values of `W`.  This is what makes the condition `ϑ < σ_{r-1}(W)` of Theorem A
necessary as well as sufficient.  Compare `BlindSpot.IsToleranceTruncation.eq_self`. -/
theorem svdTrunc_eq_self_iff {ϑ : ℝ} (hϑ : 0 ≤ ϑ) {W : Matrix m n ℝ} :
    svdTrunc ϑ W = W ↔ ∀ i < W.rank, ϑ < (Matrix.toEuclideanLin W).singularValues i := by
  constructor
  · intro h i hi
    obtain ⟨r, hr⟩ : ∃ r, W.rank = r + 1 := ⟨W.rank - 1, by omega⟩
    have hrk : r < epsRank ϑ W := by
      have := rank_svdTrunc hϑ W
      rw [h] at this
      omega
    have h1 := lt_svTail_of_lt_tolRank hrk
    rw [svTail_pred_rank hr] at h1
    exact h1.trans_le ((Matrix.toEuclideanLin W).singularValues_antitone (by omega))
  · intro h
    have h1 : epsRank ϑ W = W.rank := by
      refine le_antisymm (tolRank_le_of_svTail_le ?_) ?_
      · rw [svTail_eq_zero_of_rank_le le_rfl]; exact hϑ
      · rw [WeylSingular.epsRank_eq_sInf_tailNorm]
        refine le_csInf ⟨W.rank, ?_⟩ fun r hr => ?_
        · change tailNorm W W.rank ≤ ϑ
          rw [svTail_eq_zero_of_rank_le le_rfl]; exact hϑ
        · by_contra hlt
          rw [not_le] at hlt
          have h2 := sq_singularValues_le_svTail_sq W
            (hlt.trans_le (Matrix.rank_le_card_width W))
          exact absurd (hr : tailNorm W r ≤ ϑ) (not_le.2 ((h r hlt).trans_le h2))
    have h2 : ‖svdTrunc ϑ W - W‖ = 0 := by
      rw [svdTrunc, norm_sub_truncation_eq, h1, svTail_eq_zero_of_rank_le le_rfl]
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)

end Truncation

section Concrete

section Thin

variable {m j : Type*} [Fintype m] [Fintype j] [DecidableEq j]

/-! ### The concrete thin SVD and orthonormalisation -/

/-- The left factor `U` of a chosen thin SVD `A = U diag(σ) Vᵀ` with `rank A` columns. -/
noncomputable def thinU (A : Matrix m j ℝ) : Matrix m (Fin A.rank) ℝ :=
  (SVD.exists_svd A rfl).choose

/-- The right factor `V` of the chosen thin SVD. -/
noncomputable def thinV (A : Matrix m j ℝ) : Matrix j (Fin A.rank) ℝ :=
  (SVD.exists_svd A rfl).choose_spec.choose

/-- The positive singular values of the chosen thin SVD. -/
noncomputable def thinσ (A : Matrix m j ℝ) : Fin A.rank → ℝ :=
  (SVD.exists_svd A rfl).choose_spec.choose_spec.choose

theorem thinU_orthonormal (A : Matrix m j ℝ) : (thinU A)ᵀ * thinU A = 1 :=
  (SVD.exists_svd A rfl).choose_spec.choose_spec.choose_spec.1

theorem thinV_orthonormal (A : Matrix m j ℝ) : (thinV A)ᵀ * thinV A = 1 :=
  (SVD.exists_svd A rfl).choose_spec.choose_spec.choose_spec.2.1

theorem thinσ_pos (A : Matrix m j ℝ) (i : Fin A.rank) : 0 < thinσ A i :=
  (SVD.exists_svd A rfl).choose_spec.choose_spec.choose_spec.2.2.2.1 i

theorem thinσ_eq (A : Matrix m j ℝ) (i : Fin A.rank) :
    thinσ A i = (Matrix.toEuclideanLin A).singularValues i :=
  (SVD.exists_svd A rfl).choose_spec.choose_spec.choose_spec.2.2.2.2.1 i

theorem thin_eq (A : Matrix m j ℝ) : A = thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ :=
  (SVD.exists_svd A rfl).choose_spec.choose_spec.choose_spec.2.2.2.2.2

lemma mul_thinV (A : Matrix m j ℝ) :
    A * thinV A * Matrix.diagonal (fun i => (thinσ A i)⁻¹) = thinU A := by
  have hd : Matrix.diagonal (thinσ A) * Matrix.diagonal (fun i => (thinσ A i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (thinσ_pos A i).ne'
  calc A * thinV A * Matrix.diagonal (fun i => (thinσ A i)⁻¹)
      = thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ * thinV A *
        Matrix.diagonal (fun i => (thinσ A i)⁻¹) := by rw [← thin_eq]
    _ = thinU A * (Matrix.diagonal (thinσ A) * ((thinV A)ᵀ * thinV A) *
          Matrix.diagonal (fun i => (thinσ A i)⁻¹)) := by simp only [Matrix.mul_assoc]
    _ = thinU A := by rw [thinV_orthonormal, Matrix.mul_one, hd, Matrix.mul_one]

lemma transpose_mul_thinU (A : Matrix m j ℝ) :
    Aᵀ * thinU A * Matrix.diagonal (fun i => (thinσ A i)⁻¹) = thinV A := by
  have hd : Matrix.diagonal (thinσ A) * Matrix.diagonal (fun i => (thinσ A i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (thinσ_pos A i).ne'
  have h : Aᵀ = thinV A * Matrix.diagonal (thinσ A) * (thinU A)ᵀ := by
    calc Aᵀ = (thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ)ᵀ := by rw [← thin_eq]
      _ = thinV A * Matrix.diagonal (thinσ A) * (thinU A)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
          Matrix.mul_assoc]
  rw [h]
  calc thinV A * Matrix.diagonal (thinσ A) * (thinU A)ᵀ * thinU A *
        Matrix.diagonal (fun i => (thinσ A i)⁻¹)
      = thinV A * (Matrix.diagonal (thinσ A) * ((thinU A)ᵀ * thinU A) *
          Matrix.diagonal (fun i => (thinσ A i)⁻¹)) := by simp only [Matrix.mul_assoc]
    _ = thinV A := by rw [thinU_orthonormal, Matrix.mul_one, hd, Matrix.mul_one]

/-- `U Uᵀ A = A` for the thin SVD. -/
theorem thinU_capture (A : Matrix m j ℝ) : thinU A * (thinU A)ᵀ * A = A := by
  calc thinU A * (thinU A)ᵀ * A
      = thinU A * (thinU A)ᵀ * (thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ) := by
        rw [← thin_eq]
    _ = thinU A * ((thinU A)ᵀ * thinU A) * Matrix.diagonal (thinσ A) * (thinV A)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [thinU_orthonormal, Matrix.mul_one, ← thin_eq]

/-- `A V Vᵀ = A` for the thin SVD. -/
theorem thinV_capture (A : Matrix m j ℝ) : A * (thinV A * (thinV A)ᵀ) = A := by
  calc A * (thinV A * (thinV A)ᵀ)
      = thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ * (thinV A * (thinV A)ᵀ) := by
        rw [← thin_eq]
    _ = thinU A * Matrix.diagonal (thinσ A) * ((thinV A)ᵀ * thinV A) * (thinV A)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [thinV_orthonormal, Matrix.mul_one, ← thin_eq]

/-- `orth K`: an orthonormal basis of the column space of `K`, with exactly `rank K` columns.  This
is `orth` with zero directions dropped, the semantics of rank-adaptive QR. -/
noncomputable abbrev orth (K : Matrix m j ℝ) : Matrix m (Fin K.rank) ℝ := thinU K

theorem exists_orth_eq (K : Matrix m j ℝ) : ∃ B : Matrix j (Fin K.rank) ℝ, orth K = K * B :=
  ⟨thinV K * Matrix.diagonal (fun i => (thinσ K i)⁻¹), by
    rw [← Matrix.mul_assoc, mul_thinV]⟩

lemma capture_fromCols {k k' : Type*} {P : Matrix m m ℝ} {A : Matrix m k ℝ} {B : Matrix m k' ℝ}
    (h : P * Matrix.fromCols A B = Matrix.fromCols A B) : P * A = A ∧ P * B = B := by
  rw [Matrix.mul_fromCols] at h
  exact ⟨Matrix.fromCols_inj h |>.1, Matrix.fromCols_inj h |>.2⟩

/-- `orth[U₀, K]` is an exact augmentation of `U₀` by `K`. -/
theorem isExactAugmentation_orth {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k]
    [DecidableEq k'] (U₀ : Matrix m k ℝ) (K : Matrix m k' ℝ) :
    IsExactAugmentation (orth (Matrix.fromCols U₀ K)) U₀ K := by
  have hc := capture_fromCols (thinU_capture (Matrix.fromCols U₀ K))
  refine ⟨thinU_orthonormal _, hc.1, hc.2, ?_⟩
  obtain ⟨B, hB⟩ := exists_orth_eq (Matrix.fromCols U₀ K)
  refine ⟨Matrix.toRows₁ B, Matrix.toRows₂ B, ?_⟩
  rw [hB, ← Matrix.fromCols_mul_fromRows, Matrix.fromRows_toRows]

end Thin

/-! ### The concrete steps -/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- One step of the concrete rank-adaptive method without probe, in the thin SVD `W = U S Vᵀ`:
`Û = orth[U, G V]`, `V̂ = orth[V, Gᵀ U]`, `T(Û Ûᵀ (W − λ G) V̂ V̂ᵀ)`, with `G = g W`. -/
noncomputable def bugStep (T : Matrix m n ℝ → Matrix m n ℝ) (g : Matrix m n ℝ → Matrix m n ℝ)
    (lr : ℝ) (W : Matrix m n ℝ) : Matrix m n ℝ :=
  T (augStep (orth (Matrix.fromCols (thinU W) (g W * thinV W)))
    (orth (Matrix.fromCols (thinV W) ((g W)ᵀ * thinU W))) W (g W) lr)

/-- The Riemannian stationarity condition is basis free: `P(W) G = 0 ⇔ Gᵀ W = 0 ∧ G Wᵀ = 0`. -/
theorem tangentProj_thin_eq_zero_iff (W G : Matrix m n ℝ) :
    tangentProj (thinU W) (thinV W) G = 0 ↔ Gᵀ * W = 0 ∧ G * Wᵀ = 0 := by
  rw [tangentProj_eq_zero_iff (thinU_orthonormal W) (thinV_orthonormal W)]
  constructor
  · rintro ⟨hl, hr⟩
    have hl' : Gᵀ * thinU W = 0 := by
      have := congrArg Matrix.transpose hl
      simpa [Matrix.transpose_mul] using this
    constructor
    · rw [← thinU_capture W, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hl']
      simp
    · have : W = W * (thinV W * (thinV W)ᵀ) := (thinV_capture W).symm
      rw [this, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, hr]
      simp
  · rintro ⟨hl, hr⟩
    constructor
    · have h1 : Gᵀ * thinU W = 0 := by
        rw [← mul_thinV W, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hl]
        simp
      have := congrArg Matrix.transpose h1
      simpa [Matrix.transpose_mul] using this
    · rw [← transpose_mul_thinU W, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hr]
      simp

/-- **Theorem A for the concrete method.**  If `P(W) ∇ℒ(W) = 0`, then one step of
the augmented method, with `orth` and the truncated SVD and for every `λ` and every `0 ≤ ϑ` below
the nonzero singular values of `W`, returns `W`.  This is the blind spot of rank-adaptive training
(DLRT, GeoLoRA) with no abstract hypothesis left; the abstract version is
`BlindSpot.truncated_augStep_eq_self_of_tangentProj_eq_zero`. -/
theorem bugStep_svdTrunc_eq_self {g : Matrix m n ℝ → Matrix m n ℝ} {W : Matrix m n ℝ}
    (hG : tangentProj (thinU W) (thinV W) (g W) = 0) {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ)
    (hϑ : ∀ i < W.rank, ϑ < (Matrix.toEuclideanLin W).singularValues i) (lr : ℝ) :
    bugStep (svdTrunc ϑ) g lr W = W := by
  have h := augStep_eq_self_of_tangentProj_eq_zero (thinU_orthonormal W) (thinV_orthonormal W)
    (Matrix.diagonal (thinσ W)) hG (isExactAugmentation_orth _ _) (isExactAugmentation_orth _ _) lr
  rw [← thin_eq] at h
  rw [bugStep, h.2.2]
  exact (svdTrunc_eq_self_iff hϑ0).2 hϑ

/-- **Theorem A, iterated**: the concrete method stays at the blind spot for ever, and the rank
never grows. -/
theorem bugStep_iterate_eq_self {g : Matrix m n ℝ → Matrix m n ℝ} {W : Matrix m n ℝ}
    (hG : tangentProj (thinU W) (thinV W) (g W) = 0) {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ)
    (hϑ : ∀ i < W.rank, ϑ < (Matrix.toEuclideanLin W).singularValues i) (lr : ℝ) (t : ℕ) :
    (bugStep (svdTrunc ϑ) g lr)^[t] W = W :=
  Function.iterate_fixed (bugStep_svdTrunc_eq_self hG hϑ0 hϑ lr) t

/-- The left probed basis `Û = orth[U, G V, G ω]`. -/
noncomputable abbrev probeK (G W : Matrix m n ℝ) (ω : n → ℝ) :
    Matrix m ((Fin W.rank ⊕ Fin W.rank) ⊕ Unit) ℝ :=
  Matrix.fromCols (Matrix.fromCols (thinU W) (G * thinV W)) (Matrix.replicateCol Unit (G *ᵥ ω))

/-- `Û = orth[U, G V, G ω]`. -/
noncomputable abbrev probeU (G W : Matrix m n ℝ) (ω : n → ℝ) :
    Matrix m (Fin (probeK G W ω).rank) ℝ := orth (probeK G W ω)

/-- `V̂ = orth[V, Gᵀ Û]`, the sequential K-then-L ordering. -/
noncomputable abbrev probeV (G W : Matrix m n ℝ) (ω : n → ℝ) :
    Matrix n (Fin (Matrix.fromCols (thinV W) (Gᵀ * probeU G W ω)).rank) ℝ :=
  orth (Matrix.fromCols (thinV W) (Gᵀ * probeU G W ω))

/-- The probed step before truncation, `Ŵ = Û Ûᵀ (W − λ G) V̂ V̂ᵀ`. -/
noncomputable def probePre (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ω : n → ℝ)
    (W : Matrix m n ℝ) : Matrix m n ℝ :=
  augStep (probeU (g W) W ω) (probeV (g W) W ω) W (g W) lr

/-- One concrete probed step `T(Ŵ)`. -/
noncomputable def probeStep (T : Matrix m n ℝ → Matrix m n ℝ) (g : Matrix m n ℝ → Matrix m n ℝ)
    (lr : ℝ) (ω : n → ℝ) (W : Matrix m n ℝ) : Matrix m n ℝ :=
  T (probePre g lr ω W)

lemma mulVec_of_mul_replicateCol {P : Matrix m m ℝ} {y : m → ℝ}
    (h : P * Matrix.replicateCol Unit y = Matrix.replicateCol Unit y) : P *ᵥ y = y := by
  funext i
  have := congrFun (congrFun h i) ()
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem probeU_capture (G W : Matrix m n ℝ) (ω : n → ℝ) :
    probeU G W ω * (probeU G W ω)ᵀ * thinU W = thinU W ∧
      probeU G W ω * (probeU G W ω)ᵀ * (G * thinV W) = G * thinV W ∧
      (probeU G W ω * (probeU G W ω)ᵀ) *ᵥ (G *ᵥ ω) = G *ᵥ ω := by
  have h := capture_fromCols (thinU_capture (probeK G W ω))
  have h' := capture_fromCols h.1
  exact ⟨h'.1, h'.2, mulVec_of_mul_replicateCol h.2⟩

theorem probeV_capture (G W : Matrix m n ℝ) (ω : n → ℝ) :
    probeV G W ω * (probeV G W ω)ᵀ * thinV W = thinV W ∧
      probeV G W ω * (probeV G W ω)ᵀ * (Gᵀ * probeU G W ω) = Gᵀ * probeU G W ω :=
  capture_fromCols (thinU_capture (Matrix.fromCols (thinV W) (Gᵀ * probeU G W ω)))

/-- **The rank bound**: the left basis of the probed step has at most `2 r + 1`
columns. -/
theorem rank_probeK_le (G W : Matrix m n ℝ) (ω : n → ℝ) :
    (probeK G W ω).rank ≤ 2 * W.rank + 1 := by
  refine (Matrix.rank_le_card_width _).trans (le_of_eq ?_)
  simp [Fintype.card_sum]
  ring

/-- `Ŵ` has rank at most `2 r + 1` before truncation.  The right basis may have `3 r + 1` columns;
the rank of `Ŵ` is limited by the left one. -/
theorem rank_probePre_le (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ω : n → ℝ)
    (W : Matrix m n ℝ) : (probePre g lr ω W).rank ≤ 2 * W.rank + 1 := by
  refine le_trans ?_ (rank_probeK_le (g W) W ω)
  have e : probePre g lr ω W = probeU (g W) W ω * ((probeU (g W) W ω)ᵀ * (W - lr • g W) *
      (probeV (g W) W ω * (probeV (g W) W ω)ᵀ)) := by
    simp only [probePre, augStep, Matrix.mul_assoc]
  rw [e]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (le_of_eq ?_))
  simp

end Concrete


/-! ### The saddle claim in the spectral norm -/

section Saddle

open Curvature

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
lemma dotProduct_self_nonneg (x : m → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

omit [Fintype m] [DecidableEq n] in
lemma norm_sq_toLp (x : n → ℝ) : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

omit [Fintype m] in
lemma toEuclideanLin_toLp (N : Matrix m n ℝ) (x : n → ℝ) :
    Matrix.toEuclideanLin N (WithLp.toLp 2 x) = WithLp.toLp 2 (N *ᵥ x) := by
  rw [Matrix.toLpLin_apply]

omit [Fintype m] [Fintype n] [DecidableEq n] in
lemma lt_inv_sqrt {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (h : s ^ 2 * a < b) :
    s < (√a)⁻¹ * ((√b)⁻¹ * b) := by
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hsb : 0 < √b := Real.sqrt_pos.2 hb
  have h1 : s * √a < √b := by
    have : (s * √a) ^ 2 < √b ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]; exact h
    exact lt_of_pow_lt_pow_left₀ 2 hsb.le this
  have h2 : (√b)⁻¹ * b = √b := by
    calc (√b)⁻¹ * b = (√b)⁻¹ * (√b * √b) := by rw [Real.mul_self_sqrt hb.le]
      _ = √b := inv_mul_cancel_left₀ hsb.ne' _
  rw [h2, inv_mul_eq_div, lt_div_iff₀ hsa]
  exact h1

/-- `‖N x‖² ≤ ‖N‖₂² ‖x‖²` in dot-product notation. -/
theorem dotProduct_mulVec_le_specNorm (N : Matrix m n ℝ) (x : n → ℝ) :
    (N *ᵥ x) ⬝ᵥ (N *ᵥ x) ≤ specNorm N ^ 2 * (x ⬝ᵥ x) := by
  have h := norm_toEuclideanLin_le N (WithLp.toLp 2 x)
  rw [toEuclideanLin_toLp] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [mul_pow, norm_sq_toLp, norm_sq_toLp] at h2

/-- If `s < ‖N‖₂` then `N` stretches some vector by more than `s`. -/
theorem exists_mulVec_of_lt_specNorm {s : ℝ} (hs : 0 ≤ s) {N : Matrix m n ℝ}
    (h : s < specNorm N) : ∃ x : n → ℝ, s ^ 2 * (x ⬝ᵥ x) < (N *ᵥ x) ⬝ᵥ (N *ᵥ x) := by
  by_contra hcon
  push Not at hcon
  refine absurd (specNorm_le_of hs fun x => ?_) (not_le.2 h)
  have h1 := hcon x.ofLp
  have h2 : ‖Matrix.toEuclideanLin N x‖ ^ 2 ≤ (s * ‖x‖) ^ 2 := by
    have e : x = WithLp.toLp 2 x.ofLp := rfl
    rw [e, toEuclideanLin_toLp, norm_sq_toLp, mul_pow, norm_sq_toLp]
    exact h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hs (norm_nonneg _)) two_ne_zero).mp h2

/-- **The spectral norm as the top bilinear value** (item 3 of the plan): for `s ≥ 0`,
`s < ‖N‖₂ ⇔ ∃ unit u v, uᵀ N v > s`. -/
theorem lt_specNorm_iff_exists {s : ℝ} (hs : 0 ≤ s) (N : Matrix m n ℝ) :
    s < specNorm N ↔
      ∃ (u : m → ℝ) (v : n → ℝ), u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ s < u ⬝ᵥ (N *ᵥ v) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_mulVec_of_lt_specNorm hs h
    set a := x ⬝ᵥ x with ha
    set b := (N *ᵥ x) ⬝ᵥ (N *ᵥ x) with hb
    have ha0 : 0 ≤ a := dotProduct_self_nonneg x
    have hb0 : 0 < b := lt_of_le_of_lt (mul_nonneg (sq_nonneg s) ha0) hx
    have ha1 : 0 < a := by
      rcases ha0.eq_or_lt with h0 | h0
      · exfalso
        have hx0 : x = 0 := dotProduct_self_eq_zero.1 h0.symm
        rw [hb, hx0, Matrix.mulVec_zero, dotProduct_zero] at hb0
        exact lt_irrefl _ hb0
      · exact h0
    refine ⟨(√b)⁻¹ • (N *ᵥ x), (√a)⁻¹ • x, ?_, ?_, ?_⟩
    · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← hb]
      rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt hb0.le, inv_mul_cancel₀ hb0.ne']
    · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← ha]
      rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt ha1.le, inv_mul_cancel₀ ha1.ne']
    · rw [Matrix.mulVec_smul]
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← hb]
      exact lt_inv_sqrt ha1 hb0 hx
  · rintro ⟨u, v, hu, hv, huv⟩
    refine huv.trans_le ?_
    have h1 : (u ⬝ᵥ (N *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ u) * ((N *ᵥ v) ⬝ᵥ (N *ᵥ v)) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (N *ᵥ v)
      simpa [dotProduct, sq] using this
    have h2 := dotProduct_mulVec_le_specNorm N v
    rw [hu, one_mul] at h1
    rw [hv, mul_one] at h2
    exact abs_le_of_sq_le_sq' (h1.trans h2) (specNorm_nonneg N) |>.2

omit [Fintype n] [DecidableEq n] [Fintype k] in
lemma mulVec_transpose_of_mul_eq_zero {j : Type*} [Fintype j] {U₀ : Matrix m k ℝ}
    {N : Matrix m j ℝ} (h : U₀ᵀ * N = 0) (y : j → ℝ) : U₀ᵀ *ᵥ (N *ᵥ y) = 0 := by
  rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

set_option linter.unusedFintypeInType false in
/-- A pair of unit vectors orthogonal to the factors with `uᵀ N v > s`, from `s < ‖N‖₂`, for `N`
doubly normal: the normal block attains its spectral norm on the orthogonal complements. -/
theorem exists_unit_pair_of_lt_specNorm [DecidableEq k] {U₀ : Matrix m k ℝ} {V₀ : Matrix n k ℝ}
    (hV₀ : V₀ᵀ * V₀ = 1) {N : Matrix m n ℝ} (hNl : U₀ᵀ * N = 0) (hNr : N * V₀ = 0) {s : ℝ}
    (hs : 0 ≤ s) (h : s < specNorm N) :
    ∃ (u : m → ℝ) (v : n → ℝ), u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ U₀ᵀ *ᵥ u = 0 ∧ V₀ᵀ *ᵥ v = 0 ∧
      s < u ⬝ᵥ (N *ᵥ v) := by
  obtain ⟨x, hx⟩ := exists_mulVec_of_lt_specNorm hs h
  set z := V₀ᵀ *ᵥ x with hz
  set y := x - V₀ *ᵥ z with hy
  have hVy : V₀ᵀ *ᵥ y = 0 := by
    rw [hy, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hV₀, Matrix.one_mulVec, sub_self]
  have hNy : N *ᵥ y = N *ᵥ x := by
    rw [hy, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hNr, Matrix.zero_mulVec, sub_zero]
  have hxy : y ⬝ᵥ y ≤ x ⬝ᵥ x := by
    have e1 : x = y + V₀ *ᵥ z := by rw [hy]; abel
    have e2 : y ⬝ᵥ (V₀ *ᵥ z) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hVy, zero_dotProduct]
    have e3 : (V₀ *ᵥ z) ⬝ᵥ (V₀ *ᵥ z) = z ⬝ᵥ z := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hV₀,
        Matrix.one_mulVec]
    have e4 : x ⬝ᵥ x = y ⬝ᵥ y + z ⬝ᵥ z := by
      conv_lhs => rw [e1]
      simp only [add_dotProduct, dotProduct_add, e2, dotProduct_comm (V₀ *ᵥ z) y, e3]
      ring
    linarith [dotProduct_self_nonneg z]
  have hlt : s ^ 2 * (y ⬝ᵥ y) < (N *ᵥ y) ⬝ᵥ (N *ᵥ y) := by
    rw [hNy]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxy (sq_nonneg s)) hx
  set a := y ⬝ᵥ y with ha
  set b := (N *ᵥ y) ⬝ᵥ (N *ᵥ y) with hb
  have ha0 : 0 ≤ a := dotProduct_self_nonneg y
  have hb0 : 0 < b := lt_of_le_of_lt (mul_nonneg (sq_nonneg s) ha0) hlt
  have ha1 : 0 < a := by
    rcases ha0.eq_or_lt with h0 | h0
    · exfalso
      have hx0 : y = 0 := dotProduct_self_eq_zero.1 h0.symm
      rw [hb, hx0, Matrix.mulVec_zero, dotProduct_zero] at hb0
      exact lt_irrefl _ hb0
    · exact h0
  refine ⟨(√b)⁻¹ • (N *ᵥ y), (√a)⁻¹ • y, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← hb]
    rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt hb0.le, inv_mul_cancel₀ hb0.ne']
  · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← ha]
    rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt ha1.le, inv_mul_cancel₀ ha1.ne']
  · rw [Matrix.mulVec_smul, mulVec_transpose_of_mul_eq_zero hNl, smul_zero]
  · rw [Matrix.mulVec_smul, hVy, smul_zero]
  · rw [Matrix.mulVec_smul]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← hb]
    exact lt_inv_sqrt ha1 hb0 hlt

/-- **Not a local minimiser, spectral form**: if `σ_{i₀} < ‖N‖₂` for `A = U₀ diag(σ) V₀ᵀ`
with `N` doubly normal to `A`, every neighbourhood of `A` contains a rank-`card k` matrix of
strictly smaller quadratic loss. -/
theorem exists_rank_eq_norm_sub_lt_quadLoss_lt_of_specNorm [DecidableEq k]
    {U₀ : Matrix m k ℝ} {V₀ : Matrix n k ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {σ : k → ℝ}
    (hσ : ∀ i, σ i ≠ 0) {N : Matrix m n ℝ} (hNl : U₀ᵀ * N = 0) (hNr : N * V₀ = 0) {i₀ : k}
    (hσ0 : 0 < σ i₀) (hν : σ i₀ < specNorm N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : Matrix m n ℝ, W.rank = Fintype.card k ∧ ‖W - U₀ * Matrix.diagonal σ * V₀ᵀ‖ < δ ∧
      quadLoss (U₀ * Matrix.diagonal σ * V₀ᵀ + N) W <
        quadLoss (U₀ * Matrix.diagonal σ * V₀ᵀ + N) (U₀ * Matrix.diagonal σ * V₀ᵀ) := by
  obtain ⟨u, v, hu, hv, huU, hvV, huv⟩ :=
    exists_unit_pair_of_lt_specNorm hV₀ hNl hNr hσ0.le hν
  exact exists_rank_eq_norm_sub_lt_quadLoss_lt hU₀ hV₀ hσ hNl hNr hu hv huU hvV hσ0 huv hδ

omit [DecidableEq n] in
/-- Radial scaling increases the loss: `A` is never a local maximiser on the rank-`r` matrices. -/
theorem exists_rank_eq_norm_sub_lt_quadLoss_gt [DecidableEq k] {U₀ : Matrix m k ℝ}
    {V₀ : Matrix n k ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {σ : k → ℝ}
    (hσ : ∀ i, σ i ≠ 0) (hne : U₀ * Matrix.diagonal σ * V₀ᵀ ≠ 0) {N : Matrix m n ℝ}
    (hNl : U₀ᵀ * N = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : Matrix m n ℝ, W.rank = Fintype.card k ∧ ‖W - U₀ * Matrix.diagonal σ * V₀ᵀ‖ < δ ∧
      quadLoss (U₀ * Matrix.diagonal σ * V₀ᵀ + N) (U₀ * Matrix.diagonal σ * V₀ᵀ) <
        quadLoss (U₀ * Matrix.diagonal σ * V₀ᵀ + N) W := by
  set A := U₀ * Matrix.diagonal σ * V₀ᵀ with hA
  have hnA : 0 < ‖A‖ := norm_pos_iff.2 hne
  set t : ℝ := δ / (2 * ‖A‖) with ht
  have ht0 : 0 < t := by positivity
  have hW : (1 + t) • A = U₀ * Matrix.diagonal (fun i => (1 + t) * σ i) * V₀ᵀ := by
    have : Matrix.diagonal (fun i => (1 + t) * σ i) = (1 + t) • Matrix.diagonal σ := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, hA]
  have hAN : ⟪A, N⟫ = 0 := by
    rw [hA, Matrix.mul_assoc, Frobenius.inner_mul_left, hNl]
    simp
  refine ⟨(1 + t) • A, ?_, ?_, ?_⟩
  · rw [hW]
    refine rank_mul_mul_transpose_eq_card hU₀ hV₀ ?_
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    exact fun i => isUnit_iff_ne_zero.2 (mul_ne_zero (by positivity) (hσ i))
  · have e : (1 + t) • A - A = t • A := by rw [add_smul, one_smul]; abel
    rw [e, norm_smul, Real.norm_of_nonneg ht0.le, ht]
    have : δ / (2 * ‖A‖) * ‖A‖ = δ / 2 := by field_simp
    rw [this]
    linarith
  · have e1 : A - (A + N) = -N := by abel
    have e2 : (1 + t) • A - (A + N) = t • A - N := by rw [add_smul, one_smul]; abel
    have h1 : quadLoss (A + N) A = ‖N‖ ^ 2 / 2 := by
      rw [quadLoss, e1, norm_neg]
    have h2 : quadLoss (A + N) ((1 + t) • A) = (t ^ 2 * ‖A‖ ^ 2 + ‖N‖ ^ 2) / 2 := by
      rw [quadLoss, e2, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_smul_left, hAN]
      ring
    rw [h1, h2]
    have : 0 < t ^ 2 * ‖A‖ ^ 2 := by positivity
    linarith

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Bessel for an orthonormal frame in dot-product form. -/
lemma sum_sq_transpose_mul_le [DecidableEq k] {j : Type*} [Fintype j] [DecidableEq j]
    {V₀ : Matrix n k ℝ} (hV₀ : V₀ᵀ * V₀ = 1) {Vy : Matrix n j ℝ} (hVy : Vyᵀ * Vy = 1) (i : k) :
    ∑ l, (V₀ᵀ * Vy) i l ^ 2 ≤ 1 := by
  set b : n → ℝ := V₀ *ᵥ Pi.single i 1 with hb
  have hbb : b ⬝ᵥ b = 1 := by
    rw [hb, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hV₀,
      Matrix.one_mulVec]
    simp
  have he : ∀ l, (V₀ᵀ * Vy) i l = (Vyᵀ *ᵥ b) l := fun l => by
    simp only [hb, Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have h1 := dotProduct_mulVec_le_specNorm Vyᵀ b
  have h2 : specNorm Vyᵀ ≤ 1 := by
    rw [specNorm_transpose]
    exact specNorm_le_one_of_orthonormal hVy
  have h3 : specNorm Vyᵀ ^ 2 ≤ 1 := by
    have := specNorm_nonneg Vyᵀ
    nlinarith
  calc ∑ l, (V₀ᵀ * Vy) i l ^ 2 = (Vyᵀ *ᵥ b) ⬝ᵥ (Vyᵀ *ᵥ b) := by
        simp only [he, dotProduct, sq]
    _ ≤ specNorm Vyᵀ ^ 2 * (b ⬝ᵥ b) := h1
    _ ≤ 1 := by rw [hbb, mul_one]; exact h3

/-- **Sharpness of the saddle claim.**  If `‖N‖₂ ≤ |σ_i|` for all `i`, then `A = U₀ diag(σ) V₀ᵀ` is
a global minimiser of the quadratic loss over all matrices of rank at most `card k`.  Together with
`exists_rank_eq_norm_sub_lt_quadLoss_lt_of_specNorm` this makes `‖N‖₂ = σ_min(A)` the exact
threshold.  Proof: for `Π` the projector onto the row space of `Y`, `‖C - Y‖² ≥ ‖C‖² − ‖C Π‖²`, and
`‖C Π‖² ≤ ∑ σ_i² c_i + ‖N‖₂² ∑ (1 − c_i) ≤ ∑ σ_i²` with the Bessel weights
`c_i = ‖Πᵀ V₀ e_i‖² ∈ [0, 1]`. -/
theorem quadLoss_le_of_specNorm_le [DecidableEq k] {U₀ : Matrix m k ℝ} {V₀ : Matrix n k ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {σ : k → ℝ} {N : Matrix m n ℝ}
    (hNl : U₀ᵀ * N = 0) (hNr : N * V₀ = 0) (hs : ∀ i, specNorm N ≤ |σ i|) {Y : Matrix m n ℝ}
    (hY : Y.rank ≤ Fintype.card k) :
    quadLoss (U₀ * Matrix.diagonal σ * V₀ᵀ + N) (U₀ * Matrix.diagonal σ * V₀ᵀ) ≤
      quadLoss (U₀ * Matrix.diagonal σ * V₀ᵀ + N) Y := by
  set A := U₀ * Matrix.diagonal σ * V₀ᵀ with hA
  set C := A + N with hC
  set Vy := thinV Y with hVydef
  have hVy : Vyᵀ * Vy = 1 := thinV_orthonormal Y
  set R : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := rightProj Vy with hRdef
  have hR : IsOrthProj R := isOrthProj_rightProj hVy
  have hRY : R Y = Y := by
    rw [hRdef, rightProj_apply']
    exact thinV_capture Y
  have hRC : ‖R C‖ = ‖C * Vy‖ := by
    rw [hRdef, rightProj_apply', ← Matrix.mul_assoc,
      Frobenius.norm_mul_transpose_of_orthonormal hVy]
  -- Step 1
  have h1 : ‖C‖ ^ 2 - ‖C * Vy‖ ^ 2 ≤ ‖Y - C‖ ^ 2 := by
    have e1 := hR.norm_sq_add C
    have e2 := hR.norm_sq_add (C - Y)
    have e3 : (C - Y) - R (C - Y) = C - R C := by
      rw [map_sub, hRY]; abel
    rw [e3] at e2
    rw [hRC] at e1
    rw [norm_sub_rev Y C]
    nlinarith [sq_nonneg ‖R (C - Y)‖]
  -- Step 2
  set Z := V₀ᵀ * Vy with hZ
  set c : k → ℝ := fun i => ∑ l, Z i l ^ 2 with hc
  have hc1 : ∀ i, c i ≤ 1 := fun i => sum_sq_transpose_mul_le hV₀ hVy i
  have hAtN : Aᵀ * N = 0 := by
    rw [hA, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc, Matrix.mul_assoc, hNl]
    simp
  have hin : ⟪A * Vy, N * Vy⟫ = 0 := by
    rw [Frobenius.inner_mul_left, ← Matrix.mul_assoc, hAtN]
    simp
  have hsplit : ‖C * Vy‖ ^ 2 = ‖A * Vy‖ ^ 2 + ‖N * Vy‖ ^ 2 := by
    rw [hC, Matrix.add_mul, norm_add_sq_real, hin]
    ring
  have hAVy : ‖A * Vy‖ ^ 2 = ∑ i, σ i ^ 2 * c i := by
    have e : A * Vy = U₀ * (Matrix.diagonal σ * Z) := by
      simp only [hA, hZ, Matrix.mul_assoc]
    rw [e, Frobenius.norm_mul_of_orthonormal hU₀, Frobenius.norm_sq_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diagonal_mul, mul_pow, hc, Finset.mul_sum]
  have hZsum : ‖Z‖ ^ 2 = ∑ i, c i := by
    rw [Frobenius.norm_sq_eq_sum]
  have hVynorm : ‖Vy‖ ^ 2 = Y.rank := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hVy, Matrix.trace_one,
      Fintype.card_fin]
  set E := Vy - V₀ * Z with hE
  have hNE : N * Vy = N * E := by
    rw [hE, Matrix.mul_sub, ← Matrix.mul_assoc, hNr]
    simp
  have hEnorm : ‖E‖ ^ 2 = Y.rank - ∑ i, c i := by
    have hL := (isOrthProj_leftProj hV₀ (n := Fin Y.rank)).norm_sq_add Vy
    have e : (leftProj V₀ : Matrix n (Fin Y.rank) ℝ →L[ℝ] _) Vy = V₀ * Z := by
      rw [leftProj_apply, Matrix.mul_assoc]
    rw [e, Frobenius.norm_mul_of_orthonormal hV₀, hZsum, hVynorm] at hL
    linarith
  have hNnorm : ‖N * Vy‖ ^ 2 ≤ specNorm N ^ 2 * (Y.rank - ∑ i, c i) := by
    rw [hNE, ← hEnorm, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (frob_mul_le N E) 2
  have hAnorm : ‖A‖ ^ 2 = ∑ i, σ i ^ 2 := by
    have e : A = U₀ * (Matrix.diagonal σ * V₀ᵀ) := by rw [hA, Matrix.mul_assoc]
    rw [e, Frobenius.norm_mul_of_orthonormal hU₀,
      Frobenius.norm_mul_transpose_of_orthonormal hV₀, Frobenius.norm_sq_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  have hstep : specNorm N ^ 2 * (Y.rank - ∑ i, c i) ≤ ∑ i, σ i ^ 2 * (1 - c i) := by
    have hcard : (Y.rank : ℝ) ≤ ∑ _i : k, (1 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact_mod_cast hY
    calc specNorm N ^ 2 * (Y.rank - ∑ i, c i)
        ≤ specNorm N ^ 2 * (∑ _i : k, (1 : ℝ) - ∑ i, c i) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = ∑ i, specNorm N ^ 2 * (1 - c i) := by
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ i, σ i ^ 2 * (1 - c i) := Finset.sum_le_sum fun i _ => by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith [hc1 i])
          have := pow_le_pow_left₀ (specNorm_nonneg N) (hs i) 2
          rwa [sq_abs] at this
  have h2 : ‖C * Vy‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [hsplit, hAVy, hAnorm]
    have : ∑ i, σ i ^ 2 = ∑ i, σ i ^ 2 * c i + ∑ i, σ i ^ 2 * (1 - c i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  -- conclusion
  have hAN : ⟪A, N⟫ = 0 := by
    rw [hA, Matrix.mul_assoc, Frobenius.inner_mul_left, hNl]
    simp
  have hCnorm : ‖C‖ ^ 2 = ‖A‖ ^ 2 + ‖N‖ ^ 2 := by
    rw [hC, norm_add_sq_real, hAN]
    ring
  have e1 : A - C = -N := by rw [hC]; abel
  simp only [quadLoss, e1, norm_neg]
  linarith

/-- **The blind-spot point: exact threshold (item 3; Theorem A).**  Let `A` have
rank `r > 0` and let `N` be doubly normal to `A`, `Aᵀ N = 0`, `N Aᵀ = 0`; write `C = A + N`.  Then
for the rank-`r` problem `min ½ ‖W − C‖²`:
(1) if `‖N‖₂ ≤ σ_{r-1}(A)`, `A` is a global minimiser over rank `≤ r`;
(2) if `σ_{r-1}(A) < ‖N‖₂`, every neighbourhood of `A` contains rank-`r` matrices of strictly
smaller and of strictly larger loss, while `P(A) ∇L(A) = 0`: `A` is a saddle.
So `‖N‖₂ > σ_min(A)` is exactly the saddle case, here derived from the spectral norm
alone (Helmke–Shayman).  The exact fixed-point property holds on both sides of the threshold. -/
theorem blindSpot_dichotomy {A N : Matrix m n ℝ} (hA : 0 < A.rank) (hl : Aᵀ * N = 0)
    (hr : N * Aᵀ = 0) :
    tangentProj (thinU A) (thinV A) (A - (A + N)) = 0 ∧
    (specNorm N ≤ (Matrix.toEuclideanLin A).singularValues (A.rank - 1) →
      ∀ Y : Matrix m n ℝ, Y.rank ≤ A.rank → quadLoss (A + N) A ≤ quadLoss (A + N) Y) ∧
    ((Matrix.toEuclideanLin A).singularValues (A.rank - 1) < specNorm N → ∀ δ > 0,
      (∃ W : Matrix m n ℝ, W.rank = A.rank ∧ ‖W - A‖ < δ ∧
        quadLoss (A + N) W < quadLoss (A + N) A) ∧
      (∃ W : Matrix m n ℝ, W.rank = A.rank ∧ ‖W - A‖ < δ ∧
        quadLoss (A + N) A < quadLoss (A + N) W)) := by
  classical
  have hNtA : Nᵀ * A = 0 := by
    have := congrArg Matrix.transpose hl
    simpa [Matrix.transpose_mul] using this
  have hN0 := (tangentProj_thin_eq_zero_iff A N).2 ⟨hNtA, hr⟩
  obtain ⟨hNl, hNr⟩ :=
    (tangentProj_eq_zero_iff (thinU_orthonormal A) (thinV_orthonormal A) N).1 hN0
  have hAeq : thinU A * Matrix.diagonal (thinσ A) * (thinV A)ᵀ = A := (thin_eq A).symm
  have hsv : ∀ i : Fin A.rank, (Matrix.toEuclideanLin A).singularValues (A.rank - 1) ≤ thinσ A i :=
    fun i => by
      rw [thinσ_eq]
      exact (Matrix.toEuclideanLin A).singularValues_antitone (by omega)
  have hcard : Fintype.card (Fin A.rank) = A.rank := Fintype.card_fin _
  refine ⟨?_, ?_, ?_⟩
  · have e : A - (A + N) = -N := by abel
    rw [e, map_neg, hN0, neg_zero]
  · intro hs Y hY
    have := quadLoss_le_of_specNorm_le (thinU_orthonormal A) (thinV_orthonormal A) hNl hNr
      (σ := thinσ A) (fun i => (hs.trans (hsv i)).trans (le_abs_self _)) (Y := Y) (by rwa [hcard])
    rwa [hAeq] at this
  · intro hs δ hδ
    have hne : A ≠ 0 := fun h => by simp [h] at hA
    let i₀ : Fin A.rank := ⟨A.rank - 1, by omega⟩
    have h1 := exists_rank_eq_norm_sub_lt_quadLoss_lt_of_specNorm (thinU_orthonormal A)
      (thinV_orthonormal A) (σ := thinσ A) (fun i => (thinσ_pos A i).ne') hNl hNr
      (i₀ := i₀) (thinσ_pos A i₀) (by rwa [thinσ_eq]) hδ
    have h2 := exists_rank_eq_norm_sub_lt_quadLoss_gt (thinU_orthonormal A) (thinV_orthonormal A)
      (σ := thinσ A) (fun i => (thinσ_pos A i).ne') (by rwa [hAeq]) hNl hδ
    rw [hAeq, hcard] at h1 h2
    exact ⟨h1, h2⟩

/-- **The local-minimum characterisation**: `A` is a local minimiser of `½ ‖W − (A + N)‖²` on the
rank-`r` matrices if and only if `‖N‖₂ ≤ σ_{r-1}(A)`. -/
theorem isLocalMinOn_quadLoss_iff {A N : Matrix m n ℝ} (hA : 0 < A.rank) (hl : Aᵀ * N = 0)
    (hr : N * Aᵀ = 0) :
    IsLocalMinOn (quadLoss (A + N)) {W | W.rank = A.rank} A ↔
      specNorm N ≤ (Matrix.toEuclideanLin A).singularValues (A.rank - 1) := by
  obtain ⟨-, h1, h2⟩ := blindSpot_dichotomy hA hl hr
  constructor
  · intro hmin
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hmin
    obtain ⟨⟨W, hW, hd, hL⟩, -⟩ := h2 hlt δ hδ
    have hmem : W ∈ Metric.ball A δ ∩ {W | W.rank = A.rank} :=
      ⟨by rwa [Metric.mem_ball, dist_eq_norm], hW⟩
    exact absurd (hball hmem) (not_le.2 hL)
  · intro hs
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun Y hY => ?_
    exact h1 hs Y (le_of_eq hY)

end Saddle

/-! ### Isotropic probe laws: the Gaussian and the sphere -/

section Isotropic

variable {n : Type*} [Fintype n]

lemma sq_dotProduct_le (x y : n → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simpa [dotProduct, sq] using this

lemma ratio_nonneg (ω x : n → ℝ) : 0 ≤ (ω ⬝ᵥ x) ^ 2 / (ω ⬝ᵥ ω) :=
  div_nonneg (sq_nonneg _) (dotProduct_self_nonneg ω)

lemma ratio_le (ω x : n → ℝ) : (ω ⬝ᵥ x) ^ 2 / (ω ⬝ᵥ ω) ≤ x ⬝ᵥ x := by
  rcases (dotProduct_self_nonneg ω).eq_or_lt with h | h
  · rw [← h, div_zero]; exact dotProduct_self_nonneg x
  · rw [div_le_iff₀ h, mul_comm]; exact sq_dotProduct_le ω x

lemma measurable_dotProduct_const (x : n → ℝ) : Measurable fun ω : n → ℝ => ω ⬝ᵥ x :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _

lemma measurable_dotProduct_self : Measurable fun ω : n → ℝ => ω ⬝ᵥ ω :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul (measurable_pi_apply i)

lemma measurable_ratio (x : n → ℝ) : Measurable fun ω : n → ℝ => (ω ⬝ᵥ x) ^ 2 / (ω ⬝ᵥ ω) :=
  ((measurable_dotProduct_const x).pow_const 2).div measurable_dotProduct_self

lemma mulVec_dotProduct_eq_sum {m : Type*} [Fintype m] (N : Matrix m n ℝ) (w : n → ℝ) :
    (N *ᵥ w) ⬝ᵥ (N *ᵥ w) = ∑ i, (w ⬝ᵥ N i) ^ 2 := by
  simp only [dotProduct, sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (N *ᵥ w) i = ∑ j, w j * N i j := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [this]

/-- A **probe law**: a measurable random vector `ω` on a probability space, isotropic after
normalisation, `E[(ω̂ᵀ x)²] = ‖x‖² / n`, with `0 / 0 = 0` on `{ω = 0}`.  This replaces the finitely
supported `IsIsotropicProbe`; instances: the standard Gaussian (`isIsotropicLaw_stdGaussian`), the
uniform law on the sphere (`isIsotropicLaw_sphere`), every finitely supported isotropic probe
(`isIsotropicLaw_ofProbe`). -/
structure IsIsotropicLaw {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (ω : Ξ → n → ℝ) :
    Prop where
  measurable : Measurable ω
  isotropic : ∀ x : n → ℝ,
    ∫ ξ, (ω ξ ⬝ᵥ x) ^ 2 / (ω ξ ⬝ᵥ ω ξ) ∂μ = (x ⬝ᵥ x) / Fintype.card n

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} {ω : Ξ → n → ℝ}

theorem IsIsotropicLaw.integrable_ratio [IsProbabilityMeasure μ] (h : IsIsotropicLaw μ ω)
    (x : n → ℝ) : Integrable (fun ξ => (ω ξ ⬝ᵥ x) ^ 2 / (ω ξ ⬝ᵥ ω ξ)) μ := by
  refine Integrable.of_bound ((measurable_ratio x).comp h.measurable).aestronglyMeasurable
    (x ⬝ᵥ x) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (ratio_nonneg _ _)]
  exact ratio_le _ _

/-- `E[‖N ω‖² / ‖ω‖²] = ‖N‖²_F / n` for every isotropic probe law. -/
theorem IsIsotropicLaw.integral_mulVec_sq {m : Type*} [Fintype m] [IsProbabilityMeasure μ]
    (h : IsIsotropicLaw μ ω) (N : Matrix m n ℝ) :
    ∫ ξ, ((N *ᵥ ω ξ) ⬝ᵥ (N *ᵥ ω ξ)) / (ω ξ ⬝ᵥ ω ξ) ∂μ = ‖N‖ ^ 2 / Fintype.card n := by
  have e : ∀ ξ, ((N *ᵥ ω ξ) ⬝ᵥ (N *ᵥ ω ξ)) / (ω ξ ⬝ᵥ ω ξ) =
      ∑ i, (ω ξ ⬝ᵥ N i) ^ 2 / (ω ξ ⬝ᵥ ω ξ) := fun ξ => by
    rw [mulVec_dotProduct_eq_sum, Finset.sum_div]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => h.integrable_ratio (N i)]
  simp_rw [h.isotropic]
  rw [← Finset.sum_div, Frobenius.norm_sq_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (sq _).symm

theorem IsIsotropicLaw.integrable_mulVec_sq {m : Type*} [Fintype m] [IsProbabilityMeasure μ]
    (h : IsIsotropicLaw μ ω) (N : Matrix m n ℝ) :
    Integrable (fun ξ => ((N *ᵥ ω ξ) ⬝ᵥ (N *ᵥ ω ξ)) / (ω ξ ⬝ᵥ ω ξ)) μ := by
  have e : (fun ξ => ((N *ᵥ ω ξ) ⬝ᵥ (N *ᵥ ω ξ)) / (ω ξ ⬝ᵥ ω ξ)) =
      fun ξ => ∑ i, (ω ξ ⬝ᵥ N i) ^ 2 / (ω ξ ⬝ᵥ ω ξ) := by
    funext ξ
    rw [mulVec_dotProduct_eq_sum, Finset.sum_div]
  rw [e]
  exact integrable_finsetSum _ fun i _ => h.integrable_ratio (N i)

/-! #### Rotation invariance implies isotropy -/

/-- A law on `ℝⁿ` invariant under all linear isometries and without an atom at the origin. -/
structure IsRotationInvariant (ν : Measure (EuclideanSpace ℝ n)) : Prop where
  map_isometry : ∀ L : EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n, ν.map L = ν
  ae_ne_zero : ∀ᵐ x ∂ν, x ≠ 0

/-- The direction functional `Q(y) = E[⟪x, y⟫² / ‖x‖²]`. -/
noncomputable def dirQ (ν : Measure (EuclideanSpace ℝ n)) (y : EuclideanSpace ℝ n) : ℝ :=
  ∫ x, ⟪x, y⟫ ^ 2 / ‖x‖ ^ 2 ∂ν

lemma measurable_inner_ratio (y : EuclideanSpace ℝ n) :
    Measurable fun x : EuclideanSpace ℝ n => ⟪x, y⟫ ^ 2 / ‖x‖ ^ 2 := by
  have h1 : Measurable fun x : EuclideanSpace ℝ n => ⟪x, y⟫ :=
    (continuous_id.inner continuous_const).measurable
  exact (h1.pow_const 2).div (continuous_norm.measurable.pow_const 2)

lemma inner_ratio_le (x y : EuclideanSpace ℝ n) : ⟪x, y⟫ ^ 2 / ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : 0 < ‖x‖ ^ 2 := by positivity
    rw [div_le_iff₀ hx']
    have := abs_real_inner_le_norm x y
    have h2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [sq_abs] at h2
    nlinarith

lemma integrable_inner_ratio {ν : Measure (EuclideanSpace ℝ n)} [IsProbabilityMeasure ν]
    (y : EuclideanSpace ℝ n) : Integrable (fun x => ⟪x, y⟫ ^ 2 / ‖x‖ ^ 2) ν := by
  refine Integrable.of_bound (measurable_inner_ratio y).aestronglyMeasurable (‖y‖ ^ 2)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact inner_ratio_le x y

lemma dirQ_eq_of_norm_eq {ν : Measure (EuclideanSpace ℝ n)} (h : IsRotationInvariant ν)
    {y z : EuclideanSpace ℝ n} (hyz : ‖y‖ = ‖z‖) : dirQ ν y = dirQ ν z := by
  set L := (ℝ ∙ (y - z))ᗮ.reflection with hL
  have hLy : L y = z := Submodule.reflection_sub hyz
  have h1 := h.map_isometry L.symm
  have hm : Measurable L.symm := L.symm.continuous.measurable
  have h2 : dirQ ν y = ∫ x, ⟪L.symm x, y⟫ ^ 2 / ‖L.symm x‖ ^ 2 ∂ν := by
    unfold dirQ
    conv_lhs => rw [← h1]
    rw [integral_map hm.aemeasurable (measurable_inner_ratio y).aestronglyMeasurable]
  rw [h2, dirQ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [LinearIsometryEquiv.norm_map]
  rw [← hLy, LinearIsometryEquiv.inner_map_eq_flip]
  simp

lemma dirQ_smul (ν : Measure (EuclideanSpace ℝ n)) (c : ℝ) (y : EuclideanSpace ℝ n) :
    dirQ ν (c • y) = c ^ 2 * dirQ ν y := by
  unfold dirQ
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [real_inner_smul_right, mul_pow]
  ring

/-- **Rotation invariance gives the constant `1/n`**: `E[⟪x, y⟫² / ‖x‖²] = ‖y‖² / n`. -/
theorem IsRotationInvariant.dirQ_eq {ν : Measure (EuclideanSpace ℝ n)}
    [IsProbabilityMeasure ν] (h : IsRotationInvariant ν) (y : EuclideanSpace ℝ n) :
    dirQ ν y = ‖y‖ ^ 2 / Fintype.card n := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · have : y = 0 := Subsingleton.elim _ _
    simp [dirQ, this]
  set b := EuclideanSpace.basisFun n ℝ with hb
  have hsum : ∑ i, dirQ ν (b i) = 1 := by
    unfold dirQ
    rw [← integral_finsetSum _ fun i _ => integrable_inner_ratio (b i)]
    have : (fun x : EuclideanSpace ℝ n => ∑ i, ⟪x, b i⟫ ^ 2 / ‖x‖ ^ 2) =ᵐ[ν] fun _ => 1 := by
      filter_upwards [h.ae_ne_zero] with x hx
      rw [← Finset.sum_div]
      have e : ∑ i, ⟪x, b i⟫ ^ 2 = ‖x‖ ^ 2 := by
        have := b.sum_sq_norm_inner_left x
        simpa [real_inner_comm, sq_abs] using this
      rw [e]
      exact div_self (by positivity)
    rw [integral_congr_ae this]
    simp
  obtain ⟨i₀⟩ := hn
  have hall : ∀ i, dirQ ν (b i) = dirQ ν (b i₀) := fun i =>
    dirQ_eq_of_norm_eq h (by simp [b.norm_eq_one])
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by
    have : Nonempty n := ⟨i₀⟩
    exact_mod_cast Fintype.card_ne_zero
  have h0 : dirQ ν (b i₀) = 1 / Fintype.card n := by
    simp_rw [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    field_simp
    linarith
  have hy : dirQ ν y = dirQ ν (‖y‖ • b i₀) :=
    dirQ_eq_of_norm_eq h (by simp [norm_smul, b.norm_eq_one])
  rw [hy, dirQ_smul, h0]
  ring

lemma inner_toLp (x y : n → ℝ) :
    ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ n), WithLp.toLp 2 y⟫ = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

set_option linter.unusedFintypeInType false in
lemma measurable_ofLp' : Measurable fun x : EuclideanSpace ℝ n => x.ofLp :=
  (PiLp.continuous_ofLp 2 _).measurable

/-- A rotation invariant law, read in coordinates, is an isotropic probe law. -/
theorem IsRotationInvariant.isIsotropicLaw {ν : Measure (EuclideanSpace ℝ n)}
    [IsProbabilityMeasure ν] (h : IsRotationInvariant ν) :
    IsIsotropicLaw ν (fun x : EuclideanSpace ℝ n => x.ofLp) := by
  refine ⟨measurable_ofLp', fun x => ?_⟩
  have := h.dirQ_eq (WithLp.toLp 2 x)
  rw [norm_sq_toLp] at this
  rw [← this, dirQ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change (y.ofLp ⬝ᵥ x) ^ 2 / (y.ofLp ⬝ᵥ y.ofLp) = _
  rw [← inner_toLp, ← inner_toLp, real_inner_self_eq_norm_sq]

/-! #### The standard Gaussian -/

open ProbabilityTheory in
/-- Every nonzero linear functional of a standard Gaussian is nonzero almost surely. -/
theorem ae_inner_ne_zero_stdGaussian {a : EuclideanSpace ℝ n} (ha : a ≠ 0) :
    ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ n)), ⟪a, x⟫ ≠ 0 := by
  set L : StrongDual ℝ (EuclideanSpace ℝ n) := innerSL ℝ a with hL
  have hL' : L ≠ 0 := by
    intro h0
    have := congrArg (fun f => f a) h0
    simp [hL, ha] at this
  have hmap := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (EuclideanSpace ℝ n)) L
  have hvar : Var[L; stdGaussian (EuclideanSpace ℝ n)] = ‖L‖ ^ 2 := variance_dual_stdGaussian L
  have hne : (Var[L; stdGaussian (EuclideanSpace ℝ n)]).toNNReal ≠ 0 := by
    rw [hvar]
    intro h0
    have h1 : 0 < ‖L‖ ^ 2 := by have := norm_pos_iff.2 hL'; positivity
    rw [Real.toNNReal_eq_zero] at h0
    linarith
  have hatom : (stdGaussian (EuclideanSpace ℝ n)).map L {0} = 0 := by
    rw [hmap]
    have := nullSingletonClass_gaussianReal
      (μ := ∫ x, L x ∂stdGaussian (EuclideanSpace ℝ n)) hne
    exact measure_singleton 0
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton 0)] at hatom
  rw [ae_iff]
  have hset : {x : EuclideanSpace ℝ n | ¬ ⟪a, x⟫ ≠ 0} = L ⁻¹' {0} := by
    ext x
    simp [hL]
  rw [hset]
  exact hatom

open ProbabilityTheory in
/-- The standard Gaussian on `ℝⁿ` is rotation invariant. -/
theorem isRotationInvariant_stdGaussian [Nonempty n] :
    IsRotationInvariant (stdGaussian (EuclideanSpace ℝ n)) where
  map_isometry L := stdGaussian_map L
  ae_ne_zero := by
    classical
    obtain ⟨i⟩ := ‹Nonempty n›
    have ha : (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ n) ≠ 0 := by
      intro h
      have := congrArg (fun v : EuclideanSpace ℝ n => v.ofLp i) h
      simp at this
    filter_upwards [ae_inner_ne_zero_stdGaussian ha] with x hx h0
    exact hx (by simp [h0])

open ProbabilityTheory in
/-- **The Gaussian probe is isotropic.** -/
theorem isIsotropicLaw_stdGaussian [Nonempty n] :
    IsIsotropicLaw (stdGaussian (EuclideanSpace ℝ n))
      (fun x : EuclideanSpace ℝ n => x.ofLp) :=
  isRotationInvariant_stdGaussian.isIsotropicLaw

open ProbabilityTheory in
/-- **Item 2, Gaussian form.**  For standard Gaussian `ω ∈ ℝⁿ`,
`E[‖N ω‖² / ‖ω‖²] = ‖N‖²_F / n`.  This replaces the finite isotropic law of the blind-spot module by
the probe that is actually used; the proof is by rotation invariance of the Gaussian. -/
theorem integral_stdGaussian_mulVec_sq {m : Type*} [Fintype m] [Nonempty n] (N : Matrix m n ℝ) :
    ∫ x : EuclideanSpace ℝ n, ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) / (x.ofLp ⬝ᵥ x.ofLp)
        ∂(stdGaussian (EuclideanSpace ℝ n)) = ‖N‖ ^ 2 / Fintype.card n :=
  isIsotropicLaw_stdGaussian.integral_mulVec_sq N

open ProbabilityTheory in
/-- The same identity for `ω` with independent standard normal coordinates. -/
theorem integral_pi_gaussian_mulVec_sq {m : Type*} [Fintype m] [Nonempty n] (N : Matrix m n ℝ) :
    ∫ ω : n → ℝ, ((N *ᵥ ω) ⬝ᵥ (N *ᵥ ω)) / (ω ⬝ᵥ ω) ∂(Measure.pi fun _ : n => gaussianReal 0 1) =
      ‖N‖ ^ 2 / Fintype.card n := by
  rw [← integral_stdGaussian_mulVec_sq N, ← map_pi_eq_stdGaussian]
  have hm : Measurable fun ω : n → ℝ => (WithLp.toLp 2 ω : EuclideanSpace ℝ n) :=
    (PiLp.continuous_toLp 2 _).measurable
  rw [integral_map hm.aemeasurable]
  have h1 : Measurable fun x : EuclideanSpace ℝ n =>
      ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) / (x.ofLp ⬝ᵥ x.ofLp) := by
    have e : (fun x : EuclideanSpace ℝ n =>
        ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) / (x.ofLp ⬝ᵥ x.ofLp)) =
        fun x => ∑ i, (x.ofLp ⬝ᵥ N i) ^ 2 / (x.ofLp ⬝ᵥ x.ofLp) := by
      funext x
      rw [mulVec_dotProduct_eq_sum, Finset.sum_div]
    rw [e]
    exact Finset.measurable_sum _ fun i _ => (measurable_ratio (N i)).comp measurable_ofLp'
  exact h1.aestronglyMeasurable

open ProbabilityTheory in
/-- **The Gaussian probe sees `N` almost surely**: if `N ≠ 0`, then `N ω ≠ 0` with probability
one. -/
theorem ae_mulVec_ne_zero_stdGaussian {m : Type*} {N : Matrix m n ℝ} (hN : N ≠ 0) :
    ∀ᵐ x : EuclideanSpace ℝ n ∂(stdGaussian (EuclideanSpace ℝ n)), N *ᵥ x.ofLp ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN (Matrix.ext hcon)
  set a : EuclideanSpace ℝ n := WithLp.toLp 2 (N i) with ha
  have ha0 : a ≠ 0 := by
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ n => v.ofLp j) h
    exact hij (by simpa [ha] using this)
  filter_upwards [ae_inner_ne_zero_stdGaussian ha0] with x hx h0
  apply hx
  have h1 := congrFun h0 i
  have e : x = WithLp.toLp 2 x.ofLp := rfl
  rw [e, ha, inner_toLp]
  simpa [Matrix.mulVec] using h1

/-! #### The uniform law on the sphere -/

/-- The **uniform law on the unit sphere** of `ℝⁿ`: the normalised surface measure. -/
noncomputable def sphereLaw (n : Type*) [Fintype n] :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ n) 1) :=
  ((volume : Measure (EuclideanSpace ℝ n)).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ n)).toSphere

instance [Nonempty n] : IsProbabilityMeasure (sphereLaw n) := by
  refine ⟨?_⟩
  have h0 : (volume : Measure (EuclideanSpace ℝ n)).toSphere Set.univ ≠ 0 := by
    intro h
    exact Measure.toSphere_ne_zero (μ := (volume : Measure (EuclideanSpace ℝ n)))
      (Measure.measure_univ_eq_zero.1 h)
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)

open Pointwise in
lemma toSphere_preimage_isometry (L : EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n)
    {s : Set (EuclideanSpace ℝ n)} (hs : MeasurableSet s) :
    (volume : Measure (EuclideanSpace ℝ n)).toSphere (Subtype.val ⁻¹' (L ⁻¹' s)) =
      (volume : Measure (EuclideanSpace ℝ n)).toSphere (Subtype.val ⁻¹' s) := by
  have hL : Measurable L := L.continuous.measurable
  rw [Measure.toSphere_apply' _ (measurable_subtype_coe (hL hs)),
    Measure.toSphere_apply' _ (measurable_subtype_coe hs)]
  congr 1
  set A : Set (EuclideanSpace ℝ n) :=
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (Subtype.val ⁻¹' s :
      Set (Metric.sphere (0 : EuclideanSpace ℝ n) 1))) with hA
  have heq : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (Subtype.val ⁻¹' (L ⁻¹' s) :
      Set (Metric.sphere (0 : EuclideanSpace ℝ n) 1))) = L ⁻¹' A := by
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage, hA]
    constructor
    · rintro ⟨c, hc, y, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨c, hc, L u, ⟨⟨L u, ?_⟩, hu, rfl⟩, by simp⟩
      simp
    · rintro ⟨c, hc, y, ⟨u, hu, rfl⟩, hx⟩
      refine ⟨c, hc, L.symm u, ⟨⟨L.symm u, ?_⟩, by simpa using hu, rfl⟩, ?_⟩
      · simp
      · apply L.injective
        simpa using hx
  rw [heq]
  exact (L.measurePreserving.measure_preimage_equiv
    (f := L.toHomeomorph.toMeasurableEquiv) A)

/-- The uniform law on the sphere, as a law on `ℝⁿ`, is rotation invariant. -/
theorem isRotationInvariant_sphereLaw [Nonempty n] :
    IsRotationInvariant ((sphereLaw n).map Subtype.val) where
  map_isometry L := by
    have hL : Measurable L := L.continuous.measurable
    ext s hs
    rw [Measure.map_apply hL hs, Measure.map_apply measurable_subtype_coe (hL hs),
      Measure.map_apply measurable_subtype_coe hs]
    simp only [sphereLaw, Measure.smul_apply, smul_eq_mul, toSphere_preimage_isometry L hs]
  ae_ne_zero := by
    have hm : MeasurableSet {x : EuclideanSpace ℝ n | x ≠ 0} :=
      (measurableSet_singleton 0).compl
    rw [ae_map_iff measurable_subtype_coe.aemeasurable hm]
    refine Filter.Eventually.of_forall fun u h0 => ?_
    have := u.2
    simp [h0] at this

/-- **The uniform probe on the sphere is isotropic.** -/
theorem isIsotropicLaw_sphere [Nonempty n] :
    IsIsotropicLaw (sphereLaw n) (fun u => (u : EuclideanSpace ℝ n).ofLp) := by
  have h := isRotationInvariant_sphereLaw (n := n).isIsotropicLaw
  refine ⟨measurable_ofLp'.comp measurable_subtype_coe, fun x => ?_⟩
  rw [← h.isotropic x]
  exact (integral_map measurable_subtype_coe.aemeasurable
    (f := fun ξ : EuclideanSpace ℝ n => (ξ.ofLp ⬝ᵥ x) ^ 2 / (ξ.ofLp ⬝ᵥ ξ.ofLp))
    ((measurable_ratio x).comp measurable_ofLp').aestronglyMeasurable).symm

/-- **Item 2, sphere form.**  For `u` uniform on the unit sphere of `ℝⁿ`,
`E ‖N u‖² = ‖N‖²_F / n`. -/
theorem integral_sphere_mulVec_sq {m : Type*} [Fintype m] [Nonempty n] (N : Matrix m n ℝ) :
    ∫ u, (N *ᵥ (u : EuclideanSpace ℝ n).ofLp) ⬝ᵥ (N *ᵥ (u : EuclideanSpace ℝ n).ofLp)
        ∂sphereLaw n = ‖N‖ ^ 2 / Fintype.card n := by
  rw [← isIsotropicLaw_sphere.integral_mulVec_sq N]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hu : ((u : EuclideanSpace ℝ n).ofLp ⬝ᵥ (u : EuclideanSpace ℝ n).ofLp) = 1 := by
    rw [← inner_toLp, real_inner_self_eq_norm_sq]
    have := u.2
    simp only [mem_sphere_iff_norm, sub_zero] at this
    change ‖(u : EuclideanSpace ℝ n)‖ ^ 2 = 1
    rw [this, one_pow]
  simp only [hu, div_one]

/-! #### Finitely supported probes -/

/-- The law `∑ ξ, p ξ δ_ξ` of a finitely supported probe. -/
noncomputable def finiteLaw {Ξ : Type*} [Fintype Ξ] [MeasurableSpace Ξ] (p : Ξ → ℝ) : Measure Ξ :=
  ∑ ξ, ENNReal.ofReal (p ξ) • Measure.dirac ξ

theorem isProbabilityMeasure_finiteLaw {Ξ : Type*} [Fintype Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (hp1 : ∑ ξ, p ξ = 1) :
    IsProbabilityMeasure (finiteLaw p) := by
  refine ⟨?_⟩
  simp only [finiteLaw, Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ξ _ => hp ξ, hp1, ENNReal.ofReal_one]

theorem integral_finiteLaw {Ξ : Type*} [Fintype Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] {p : Ξ → ℝ} (hp : ∀ ξ, 0 ≤ p ξ) (f : Ξ → ℝ) :
    ∫ ξ, f ξ ∂finiteLaw p = ∑ ξ, p ξ * f ξ := by
  have hi : ∀ ξ ∈ (Finset.univ : Finset Ξ),
      Integrable f (ENNReal.ofReal (p ξ) • Measure.dirac ξ) := fun ξ _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [finiteLaw, integral_finsetSum_measure hi]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp ξ), smul_eq_mul]

/-- Every finitely supported isotropic probe of the blind-spot module is an isotropic law. -/
theorem isIsotropicLaw_ofProbe {Ξ : Type*} [Fintype Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] {p : Ξ → ℝ} {ω : Ξ → n → ℝ} (h : IsIsotropicProbe p ω) :
    IsIsotropicLaw (finiteLaw p) ω where
  measurable := measurable_of_finite ω
  isotropic x := by
    rw [integral_finiteLaw h.nonneg]
    exact h.isotropic x

end Isotropic

/-! ### The rotation-invariant constant: the rank of `N` instead of the dimension -/

section RankConstant

/-- The pointwise inequality behind the rearrangement: a larger weight attracts more of the mass
of `ω`, in the average over the swap of two coordinates. -/
lemma swap_pair_nonneg {p q a b T : ℝ} (hq : 0 ≤ q) (hpq : q ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hT : 0 ≤ T) :
    0 ≤ (p * a - q * b) / (p * a + q * b + T) + (p * b - q * a) / (p * b + q * a + T) := by
  have hp : 0 ≤ p := hq.trans hpq
  have hA : 0 ≤ p * a := mul_nonneg hp ha
  have hB : 0 ≤ q * b := mul_nonneg hq hb
  have hC : 0 ≤ p * b := mul_nonneg hp hb
  have hD : 0 ≤ q * a := mul_nonneg hq ha
  have hS : 0 ≤ p * a + q * b + T := by positivity
  have hS' : 0 ≤ p * b + q * a + T := by positivity
  rcases hS.eq_or_lt with h0 | h0
  · rw [← h0, div_zero, zero_add]
    refine div_nonneg ?_ hS'
    have h1 : p * a = 0 := by linarith
    have h2 : q * a ≤ p * a := mul_le_mul_of_nonneg_right hpq ha
    linarith
  rcases hS'.eq_or_lt with h1 | h1
  · rw [← h1, div_zero, add_zero]
    refine div_nonneg ?_ hS
    have h2 : p * b = 0 := by linarith
    have h3 : q * b ≤ p * b := mul_le_mul_of_nonneg_right hpq hb
    linarith
  rw [div_add_div _ _ h0.ne' h1.ne']
  refine div_nonneg ?_ (mul_pos h0 h1).le
  have e : (p * a - q * b) * (p * b + q * a + T) + (p * a + q * b + T) * (p * b - q * a) =
      2 * ((p - q) * (p + q) * (a * b)) + (p - q) * (a + b) * T := by ring
  rw [e]
  have h2 : 0 ≤ p - q := sub_nonneg.2 hpq
  positivity

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- `λ_i = σ_i(N)²`. -/
noncomputable def svSq (N : Matrix m n ℝ) (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n))) : ℝ :=
  (Matrix.toEuclideanLin N).singularValues i ^ 2

/-- The energy `∑_i λ_i ⟪e_i, x⟫²` of `x` under `N`. -/
noncomputable def svEnergy (N : Matrix m n ℝ) (x : EuclideanSpace ℝ n) : ℝ :=
  ∑ i, svSq N i * ⟪rightSingularVectors N i, x⟫ ^ 2

/-- The share `λ_i ⟪e_i, x⟫² / ∑_k λ_k ⟪e_k, x⟫²` of the `i`-th singular direction. -/
noncomputable def svShare (N : Matrix m n ℝ) (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)))
    (x : EuclideanSpace ℝ n) : ℝ :=
  svSq N i * ⟪rightSingularVectors N i, x⟫ ^ 2 / svEnergy N x

lemma svSq_nonneg (N : Matrix m n ℝ) (i) : 0 ≤ svSq N i := sq_nonneg _

lemma svEnergy_nonneg (N : Matrix m n ℝ) (x) : 0 ≤ svEnergy N x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (svSq_nonneg N i) (sq_nonneg _)

lemma svShare_nonneg (N : Matrix m n ℝ) (i) (x) : 0 ≤ svShare N i x :=
  div_nonneg (mul_nonneg (svSq_nonneg N i) (sq_nonneg _)) (svEnergy_nonneg N x)

lemma svShare_le_one (N : Matrix m n ℝ) (i) (x) : svShare N i x ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (svEnergy_nonneg N x)
  exact Finset.single_le_sum (f := fun k => svSq N k * ⟪rightSingularVectors N k, x⟫ ^ 2)
    (fun k _ => mul_nonneg (svSq_nonneg N k) (sq_nonneg _)) (Finset.mem_univ i)

lemma measurable_svEnergy (N : Matrix m n ℝ) : Measurable (svEnergy N) :=
  Finset.measurable_sum _ fun _ _ =>
    ((continuous_const.inner continuous_id).measurable.pow_const 2).const_mul _

lemma measurable_svShare (N : Matrix m n ℝ) (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n))) :
    Measurable (svShare N i) :=
  (((continuous_const.inner continuous_id).measurable.pow_const 2).const_mul _).div
    (measurable_svEnergy N)

lemma integrable_svShare {ν : Measure (EuclideanSpace ℝ n)} [IsProbabilityMeasure ν]
    (N : Matrix m n ℝ) (i) : Integrable (svShare N i) ν := by
  refine Integrable.of_bound (measurable_svShare N i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (svShare_nonneg N i x)]
  exact svShare_le_one N i x

/-- `‖N x‖² = ∑_i λ_i ⟪e_i, x⟫²` in coordinates. -/
lemma svEnergy_toLp (N : Matrix m n ℝ) (ω : n → ℝ) :
    svEnergy N (WithLp.toLp 2 ω) = (N *ᵥ ω) ⬝ᵥ (N *ᵥ ω) := by
  have h := sq_norm_toEuclideanLin_apply N (WithLp.toLp 2 ω)
  rw [toEuclideanLin_toLp, norm_sq_toLp] at h
  exact h.symm

set_option linter.unusedDecidableInType false in
/-- `‖Nᵀ N x‖² = ∑_i λ_i² ⟪e_i, x⟫²` in coordinates. -/
lemma sq_gram_toLp (N : Matrix m n ℝ) [DecidableEq m] (ω : n → ℝ) :
    (Nᵀ *ᵥ (N *ᵥ ω)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ ω)) =
      ∑ i, svSq N i ^ 2 *
        ⟪rightSingularVectors N i, (WithLp.toLp 2 ω : EuclideanSpace ℝ n)⟫ ^ 2 := by
  set x : EuclideanSpace ℝ n := WithLp.toLp 2 ω with hx
  set T := Matrix.toEuclideanLin N with hT
  set e := rightSingularVectors N with he
  set z : EuclideanSpace ℝ n := LinearMap.adjoint T (T x) with hz
  have hzω : z = WithLp.toLp 2 (Nᵀ *ᵥ (N *ᵥ ω)) := by
    have h1 := toEuclideanLin_transpose_mul_self N
    have h2 : z = Matrix.toEuclideanLin (Nᵀ * N) x := by
      rw [h1]
      rfl
    rw [h2, toEuclideanLin_toLp, Matrix.mulVec_mulVec]
  have hnorm : (Nᵀ *ᵥ (N *ᵥ ω)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ ω)) = ‖z‖ ^ 2 := by
    rw [hzω, norm_sq_toLp]
  rw [hnorm, ← e.sum_sq_norm_inner_left z]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : ⟪z, e i⟫ = T.singularValues i ^ 2 * ⟪e i, x⟫ := by
    rw [hz, LinearMap.adjoint_inner_left, ← LinearMap.adjoint_inner_right,
      adjoint_toEuclideanLin_rightSingularVectors, real_inner_smul_right, real_inner_comm]
  rw [Real.norm_eq_abs, sq_abs, h3, svSq, mul_pow]

/-- Away from `N ω = 0`, the Rayleigh quotient `‖Nᵀ N ω‖² / ‖N ω‖²` is the mean of the `λ_i` under
the shares. -/
lemma ratio_eq_sum_share (N : Matrix m n ℝ) (ω : n → ℝ) :
    (Nᵀ *ᵥ (N *ᵥ ω)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ ω)) / ((N *ᵥ ω) ⬝ᵥ (N *ᵥ ω)) =
      ∑ i, svSq N i * svShare N i (WithLp.toLp 2 ω) := by
  classical
  rw [sq_gram_toLp, ← svEnergy_toLp, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [svShare, sq (svSq N i), mul_assoc, mul_div_assoc]

/-- The swap of two singular directions. -/
noncomputable def svSwap (N : Matrix m n ℝ) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ n))) :
    EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n :=
  (rightSingularVectors N).equiv (rightSingularVectors N) (Equiv.swap i j)

lemma inner_svSwap (N : Matrix m n ℝ) (i j k) (x : EuclideanSpace ℝ n) :
    ⟪rightSingularVectors N k, svSwap N i j x⟫ =
      ⟪rightSingularVectors N (Equiv.swap i j k), x⟫ := by
  have h : (svSwap N i j).symm (rightSingularVectors N k) =
      rightSingularVectors N (Equiv.swap i j k) := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    simp [svSwap]
  rw [real_inner_comm, LinearIsometryEquiv.inner_map_eq_flip, h, real_inner_comm]

/-- `∑_k λ_k ⟪e_k, L x⟫²`, the energy after the swap, in terms of the unswapped data. -/
lemma svEnergy_decomp (N : Matrix m n ℝ) {i j} (hij : i ≠ j) (x : EuclideanSpace ℝ n) :
    ∃ T : ℝ, 0 ≤ T ∧
      svEnergy N x = svSq N i * ⟪rightSingularVectors N i, x⟫ ^ 2 +
        svSq N j * ⟪rightSingularVectors N j, x⟫ ^ 2 + T ∧
      svEnergy N (svSwap N i j x) = svSq N i * ⟪rightSingularVectors N j, x⟫ ^ 2 +
        svSq N j * ⟪rightSingularVectors N i, x⟫ ^ 2 + T := by
  set E := ((Finset.univ : Finset _).erase i).erase j with hE
  have hsplit : ∀ f : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) → ℝ,
      ∑ k, f k = f i + f j + ∑ k ∈ E, f k := fun f => by
    have h1 : j ∈ (Finset.univ : Finset _).erase i :=
      Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ i), ← Finset.add_sum_erase _ f h1, add_assoc]
  refine ⟨∑ k ∈ E, svSq N k * ⟪rightSingularVectors N k, x⟫ ^ 2,
    Finset.sum_nonneg fun k _ => mul_nonneg (svSq_nonneg N k) (sq_nonneg _), ?_, ?_⟩
  · rw [svEnergy, hsplit]
  · rw [svEnergy, hsplit]
    simp only [inner_svSwap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.1 hk).1
    have hki : k ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hk).2).1
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- **Rearrangement**: the expected shares are ordered like the `λ_i`.  This is where rotation
invariance is used; it fails for coordinate probes. -/
theorem integral_svShare_le {ν : Measure (EuclideanSpace ℝ n)} [IsProbabilityMeasure ν]
    (h : IsRotationInvariant ν) (N : Matrix m n ℝ) {i j} (hij : svSq N j ≤ svSq N i) :
    ∫ x, svShare N j x ∂ν ≤ ∫ x, svShare N i x ∂ν := by
  rcases eq_or_ne i j with rfl | hne
  · exact le_rfl
  set L := svSwap N i j with hL
  have hLm : Measurable L := L.continuous.measurable
  set D : EuclideanSpace ℝ n → ℝ := fun x => svShare N i x - svShare N j x with hD
  have hDm : Measurable D := (measurable_svShare N i).sub (measurable_svShare N j)
  have hDi : Integrable D ν := (integrable_svShare N i).sub (integrable_svShare N j)
  have hinv : ∫ x, D (L x) ∂ν = ∫ x, D x ∂ν := by
    conv_rhs => rw [← h.map_isometry L]
    rw [integral_map hLm.aemeasurable hDm.aestronglyMeasurable]
  have hDLi : Integrable (fun x => D (L x)) ν := by
    have hi : Integrable D (ν.map L) := by rwa [h.map_isometry L]
    exact (integrable_map_measure hDm.aestronglyMeasurable hLm.aemeasurable).1 hi
  have hpt : ∀ x, 0 ≤ D x + D (L x) := fun x => by
    obtain ⟨T, hT, h1, h2⟩ := svEnergy_decomp N hne x
    set a := ⟪rightSingularVectors N i, x⟫ ^ 2 with ha
    set b := ⟪rightSingularVectors N j, x⟫ ^ 2 with hb
    have e1 : D x = (svSq N i * a - svSq N j * b) / (svSq N i * a + svSq N j * b + T) := by
      simp only [hD, svShare, h1, sub_div]
      rfl
    have e2 : D (L x) = (svSq N i * b - svSq N j * a) / (svSq N i * b + svSq N j * a + T) := by
      simp only [hD, svShare, h2, sub_div, hL, inner_svSwap, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
      rfl
    rw [e1, e2]
    exact swap_pair_nonneg (svSq_nonneg N j) hij (sq_nonneg _) (sq_nonneg _) hT
  have h0 : 0 ≤ ∫ x, (D x + D (L x)) ∂ν := integral_nonneg hpt
  rw [integral_add hDi hDLi, hinv] at h0
  have h1 : 0 ≤ ∫ x, D x ∂ν := by linarith
  rw [hD, integral_sub (integrable_svShare N i) (integrable_svShare N j)] at h1
  linarith

set_option linter.unusedDecidableInType false in
/-- **The Rayleigh quotient for a rotation-invariant probe**: if `N ω ≠ 0` almost surely, then
`E[‖Nᵀ N ω‖² / ‖N ω‖²] ≥ ‖N‖²_F / rank N`.  Equality for flat `N`.  So the dimension `n` of the
isotropic bound is the rank of `N` for the Gaussian probe.  This is false for coordinate probes:
for `N = e₁e₁ᵀ` the left side is `1/n` and the right side `1`.  Proof: Chebyshev's sum inequality
with `integral_svShare_le`. -/
theorem div_rank_le_integral_ratio {ν : Measure (EuclideanSpace ℝ n)} [IsProbabilityMeasure ν]
    (h : IsRotationInvariant ν) (N : Matrix m n ℝ) (hne : ∀ᵐ x ∂ν, N *ᵥ x.ofLp ≠ 0) :
    ‖N‖ ^ 2 / N.rank ≤ ∫ x : EuclideanSpace ℝ n,
      (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) / ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) ∂ν := by
  classical
  set π : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) → ℝ := fun i => ∫ x, svShare N i x ∂ν with hπ
  -- the integral as a mean
  have hmean : ∫ x : EuclideanSpace ℝ n,
      (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) / ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) ∂ν =
      ∑ i, svSq N i * π i := by
    have e : ∀ x : EuclideanSpace ℝ n,
        (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) / ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) =
          ∑ i, svSq N i * svShare N i x := fun x => ratio_eq_sum_share N x.ofLp
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ => (integrable_svShare N i).const_mul _]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hsum : ∑ i, π i = 1 := by
    rw [hπ, ← integral_finsetSum _ fun i _ => integrable_svShare N i]
    have e : (fun x => ∑ i, svShare N i x) =ᵐ[ν] fun _ => 1 := by
      filter_upwards [hne] with x hx
      have hS : svEnergy N x ≠ 0 := by
        have : svEnergy N x = (N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp) := svEnergy_toLp N x.ofLp
        rw [this]
        exact fun h0 => hx (dotProduct_self_eq_zero.1 h0)
      simp only [svShare, ← Finset.sum_div]
      exact div_self hS
    rw [integral_congr_ae e]
    simp
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ n) = Fintype.card n := finrank_euclideanSpace
  have hlamsum : ∑ i, svSq N i = ‖N‖ ^ 2 := by
    rw [sq_norm_eq_sum_sq_singularValues, ← hfr]
    exact Fin.sum_univ_eq_sum_range (fun i => (Matrix.toEuclideanLin N).singularValues i ^ 2) _
  set I := (Finset.univ : Finset (Fin (Module.finrank ℝ (EuclideanSpace ℝ n)))).filter
    fun i => svSq N i ≠ 0 with hI
  have hoff : ∀ i, i ∉ I → π i = 0 := fun i hi => by
    have h0 : svSq N i = 0 := by simpa [hI] using hi
    simp [hπ, svShare, h0]
  have hmono : MonovaryOn π (svSq N) (I : Set _) := fun i _ j _ hlt =>
    integral_svShare_le h N hlt.le
  have hcheb := hmono.sum_mul_sum_le_card_mul_sum
  have e1 : ∑ i ∈ I, π i = 1 := by
    rw [← hsum]
    exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hoff i hi
  have e2 : ∑ i ∈ I, svSq N i = ‖N‖ ^ 2 := by
    rw [← hlamsum]
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    simpa [hI] using hi
  have e3 : ∑ i ∈ I, π i * svSq N i = ∑ i, svSq N i * π i := by
    have : ∑ i, svSq N i * π i = ∑ i ∈ I, svSq N i * π i :=
      (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by rw [hoff i hi, mul_zero]).symm
    rw [this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1, e2, one_mul, e3] at hcheb
  rw [hmean]
  have hcard : I.card ≤ N.rank := by
    have hsub : ∀ i ∈ I, (i : ℕ) < N.rank := fun i hi => by
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : (Matrix.toEuclideanLin N).singularValues i ≤ tailNorm N i := by
        exact sq_singularValues_le_svTail_sq N (lt_of_lt_of_eq i.2 hfr)
      have h2 : tailNorm N i = 0 := svTail_eq_zero_of_rank_le hcon
      have h3 := (Matrix.toEuclideanLin N).singularValues_nonneg i
      have h4 : (Matrix.toEuclideanLin N).singularValues i = 0 := le_antisymm (by linarith) h3
      exact (Finset.mem_filter.1 hi).2 (by simp [svSq, h4])
    calc I.card = (I.image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.range N.rank).card := Finset.card_le_card fun x hx => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          exact Finset.mem_range.2 (hsub i hi)
      _ = N.rank := Finset.card_range _
  rcases (Nat.zero_le N.rank).eq_or_lt with h0 | h0
  · rw [← h0]
    simp only [Nat.cast_zero, div_zero]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (svSq_nonneg N i) (integral_nonneg fun x => svShare_nonneg N i x)
  have hr : (0 : ℝ) < N.rank := by exact_mod_cast h0
  have hsumnn : 0 ≤ ∑ i, svSq N i * π i := Finset.sum_nonneg fun i _ =>
    mul_nonneg (svSq_nonneg N i) (integral_nonneg fun x => svShare_nonneg N i x)
  rw [div_le_iff₀ hr]
  calc ‖N‖ ^ 2 ≤ I.card * ∑ i, svSq N i * π i := by exact_mod_cast hcheb
    _ ≤ N.rank * ∑ i, svSq N i * π i :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hsumnn
    _ = (∑ i, svSq N i * π i) * N.rank := mul_comm _ _

end RankConstant

/-! ### Expectation over probe paths -/

section Paths

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- **Iterated expectation over probe paths.**  `iterE μ K f = ∫⁻ ξ₁, … ∫⁻ ξ_K, f(ξ₁, …, ξ_K)`, the
tower of Lebesgue integrals with the last probe innermost.  It is defined for every `f`, measurable
or not (`∫⁻` is the lower integral), and it is the expectation under the product law `μ^K` whenever
`f` is measurable (`iterE_eq_lintegral_pi`). -/
noncomputable def iterE (μ : Measure Ξ) : (K : ℕ) → ((Fin K → Ξ) → ℝ≥0∞) → ℝ≥0∞
  | 0, f => f fun i => i.elim0
  | K + 1, f => iterE μ K fun ω => ∫⁻ ξ, f (Fin.snoc ω ξ) ∂μ

variable {μ : Measure Ξ}

lemma iterE_succ {K : ℕ} (f : (Fin (K + 1) → Ξ) → ℝ≥0∞) :
    iterE μ (K + 1) f = iterE μ K fun ω => ∫⁻ ξ, f (Fin.snoc ω ξ) ∂μ := rfl

lemma iterE_mono {K : ℕ} {f g : (Fin K → Ξ) → ℝ≥0∞} (h : ∀ ω, f ω ≤ g ω) :
    iterE μ K f ≤ iterE μ K g := by
  induction K with
  | zero => exact h _
  | succ K ih => exact ih fun ω => lintegral_mono fun ξ => h _

lemma iterE_add_le {K : ℕ} (f g : (Fin K → Ξ) → ℝ≥0∞) :
    iterE μ K f + iterE μ K g ≤ iterE μ K fun ω => f ω + g ω := by
  induction K with
  | zero => exact le_rfl
  | succ K ih => exact (ih _ _).trans (iterE_mono fun ω => le_lintegral_add _ _)

lemma iterE_add_const [IsProbabilityMeasure μ] {K : ℕ} (f : (Fin K → Ξ) → ℝ≥0∞) (c : ℝ≥0∞) :
    iterE μ K (fun ω => f ω + c) = iterE μ K f + c := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have e : ∀ ω : Fin K → Ξ, ∫⁻ ξ, (f (Fin.snoc ω ξ) + c) ∂μ =
        ∫⁻ ξ, f (Fin.snoc ω ξ) ∂μ + c := fun ω => by
      rw [lintegral_add_right _ measurable_const]
      simp
    simp only [iterE, e]
    exact ih _

lemma iterE_const_mul {K : ℕ} (c : ℝ≥0∞) (hc : c ≠ ∞) (f : (Fin K → Ξ) → ℝ≥0∞) :
    iterE μ K (fun ω => c * f ω) = c * iterE μ K f := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [iterE, lintegral_const_mul' c _ hc]
    exact ih _

/-- For measurable `f`, the iterated integral is the expectation under the product law. -/
theorem iterE_eq_lintegral_pi [SigmaFinite μ] {K : ℕ} {f : (Fin K → Ξ) → ℝ≥0∞}
    (hf : Measurable f) : iterE μ K f = ∫⁻ ω, f ω ∂Measure.pi fun _ : Fin K => μ := by
  induction K with
  | zero =>
    rw [Measure.pi_of_empty, lintegral_dirac' _ hf]
    exact congrArg f (Subsingleton.elim _ _)
  | succ K ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => Ξ) (Fin.last K) with he
    have hsnoc : ∀ (ξ : Ξ) (ω : Fin K → Ξ), e.symm (ξ, ω) = Fin.snoc ω ξ := fun ξ ω => by
      simp [he, MeasurableEquiv.piFinSuccAbove]
    have hm : Measurable fun p : (Fin K → Ξ) × Ξ => f (Fin.snoc p.1 p.2) := by
      have : (fun p : (Fin K → Ξ) × Ξ => f (Fin.snoc p.1 p.2)) =
          fun p => f (e.symm (p.2, p.1)) := by
        funext p
        rw [hsnoc]
      rw [this]
      exact hf.comp (e.symm.measurable.comp measurable_swap)
    have hmi : Measurable fun ω : Fin K → Ξ => ∫⁻ ξ, f (Fin.snoc ω ξ) ∂μ :=
      hm.lintegral_prod_right'
    change iterE μ K (fun ω => ∫⁻ ξ, f (Fin.snoc ω ξ) ∂μ) = _
    rw [ih hmi]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (K + 1) => μ) (Fin.last K)
    have h1 : ∫⁻ ω, f ω ∂Measure.pi (fun _ : Fin (K + 1) => μ) =
        ∫⁻ z, f (e.symm z) ∂(μ.prod (Measure.pi fun _ : Fin K => μ)) := by
      have h2 := lintegral_map_equiv (μ := Measure.pi fun _ : Fin (K + 1) => μ)
        (fun z => f (e.symm z)) e
      simp only [MeasurableEquiv.symm_apply_apply] at h2
      rw [← h2, hmp.map_eq]
    rw [h1, lintegral_prod_symm (fun z => f (e.symm z)) (hf.comp e.symm.measurable).aemeasurable]
    simp only [hsnoc]

/-- **Telescoped descent for iterated expectations.**  No measurability is used. -/
theorem sum_iterE_add_le [IsProbabilityMeasure μ] {a e : (k : ℕ) → (Fin k → Ξ) → ℝ≥0∞}
    {b : (k : ℕ) → (Fin k → Ξ) → Ξ → ℝ≥0∞} {d : ℝ≥0∞} {K : ℕ}
    (hstep : ∀ k < K, ∀ ω ξ, a (k + 1) (Fin.snoc ω ξ) + b k ω ξ ≤ a k ω + d)
    (hcap : ∀ k ω, e k ω ≤ ∫⁻ ξ, b k ω ξ ∂μ) :
    ∑ k ∈ range K, iterE μ k (e k) + iterE μ K (a K) ≤ iterE μ 0 (a 0) + K * d := by
  induction K with
  | zero => simp
  | succ K ih =>
    have ih := ih fun k hk => hstep k (by omega)
    have h1 : iterE μ (K + 1) (a (K + 1)) + iterE μ K (e K) ≤ iterE μ K (a K) + d := by
      have hp : ∀ ω, ∫⁻ ξ, a (K + 1) (Fin.snoc ω ξ) ∂μ + e K ω ≤ a K ω + d := fun ω =>
        calc ∫⁻ ξ, a (K + 1) (Fin.snoc ω ξ) ∂μ + e K ω
            ≤ ∫⁻ ξ, a (K + 1) (Fin.snoc ω ξ) ∂μ + ∫⁻ ξ, b K ω ξ ∂μ := by
              gcongr
              exact hcap K ω
          _ ≤ ∫⁻ ξ, (a (K + 1) (Fin.snoc ω ξ) + b K ω ξ) ∂μ := le_lintegral_add _ _
          _ ≤ ∫⁻ _, (a K ω + d) ∂μ := lintegral_mono fun ξ => hstep K (by omega) ω ξ
          _ = a K ω + d := by simp
      rw [iterE_succ]
      calc iterE μ K (fun ω => ∫⁻ ξ, a (K + 1) (Fin.snoc ω ξ) ∂μ) + iterE μ K (e K)
          ≤ iterE μ K (fun ω => ∫⁻ ξ, a (K + 1) (Fin.snoc ω ξ) ∂μ + e K ω) := iterE_add_le _ _
        _ ≤ iterE μ K (fun ω => a K ω + d) := iterE_mono hp
        _ = iterE μ K (a K) + d := iterE_add_const _ _
    rw [Finset.sum_range_succ]
    calc ∑ k ∈ range K, iterE μ k (e k) + iterE μ K (e K) + iterE μ (K + 1) (a (K + 1))
        = ∑ k ∈ range K, iterE μ k (e k) + (iterE μ (K + 1) (a (K + 1)) + iterE μ K (e K)) := by
          ring
      _ ≤ ∑ k ∈ range K, iterE μ k (e k) + (iterE μ K (a K) + d) := by gcongr
      _ = (∑ k ∈ range K, iterE μ k (e k) + iterE μ K (a K)) + d := by ring
      _ ≤ (iterE μ 0 (a 0) + K * d) + d := by gcongr
      _ = iterE μ 0 (a 0) + ((K + 1 : ℕ) : ℝ≥0∞) * d := by push_cast; ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ℒ : E → ℝ} {g : E → E}
  {β : ℝ}

/-- One lower-integral capture rescaled by a positive constant. -/
lemma ofReal_mul_le_lintegral {c γ : ℝ} (hc : 0 ≤ c) {t : ℝ} {f : Ξ → ℝ}
    (h : ENNReal.ofReal (γ * t) ≤ ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂μ) :
    ENNReal.ofReal (c * γ * t) ≤ ∫⁻ ξ, ENNReal.ofReal (c * f ξ) ∂μ := by
  have e : ∀ ξ, ENNReal.ofReal (c * f ξ) = ENNReal.ofReal c * ENNReal.ofReal (f ξ) := fun ξ =>
    ENNReal.ofReal_mul hc
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc, ENNReal.ofReal_mul hc]
  gcongr

/-- **Abstract convergence with a general probability law (no measurability).**  Random projected
gradient descent with truncation, where the projector `P_{k,ω,ξ}` drawn with the fresh probe `ξ ∼ μ`
captures in expectation a fraction `γ` of the gradient energy, satisfies
`min_{k<K} E ‖∇ℒ(x_k)‖² ≤ [(ℒ(x₀) − ℒ_inf) / (K c) + B ϑ / c] / γ`, `c = λ (1 − βλ/2)`.  This is
`BlindSpot.exists_pathExp_grad_sq_le` with a general law `μ` in place of a finite one, the
expectation being the iterated integral `iterE`. -/
theorem exists_iterE_grad_sq_le [Nonempty Ξ] [IsProbabilityMeasure μ]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {x : (k : ℕ) → (Fin k → Ξ) → E} {P : (k : ℕ) → (Fin k → Ξ) → Ξ → E →L[ℝ] E}
    (hP : ∀ k ω ξ, IsOrthProj (P k ω ξ)) {h ϑ B ℒinf γ : ℝ} {K : ℕ}
    (htr : ∀ k ω ξ, ‖x (k + 1) (Fin.snoc ω ξ) - projGradStep (P k ω ξ) g h (x k ω)‖ ≤ ϑ)
    (hB : ∀ k < K, ∀ ω ξ, ∀ w ∈ segment ℝ (projGradStep (P k ω ξ) g h (x k ω))
      (x (k + 1) (Fin.snoc ω ξ)), ‖g w‖ ≤ B)
    (hinf : ∀ k ω, ℒinf ≤ ℒ (x k ω)) (hγ0 : 0 < γ)
    (hγ : ∀ k ω, ENNReal.ofReal (γ * ‖g (x k ω)‖ ^ 2) ≤
      ∫⁻ ξ, ENNReal.ofReal (‖P k ω ξ (g (x k ω))‖ ^ 2) ∂μ)
    (hh : 0 < h * (1 - β * h / 2)) (hK : 0 < K) :
    ∃ k < K, iterE μ k (fun ω => ENNReal.ofReal (‖g (x k ω)‖ ^ 2)) ≤
      ENNReal.ofReal (((ℒ (x 0 fun i => i.elim0) - ℒinf) / (K * (h * (1 - β * h / 2))) +
        B * ϑ / (h * (1 - β * h / 2))) / γ) := by
  set c := h * (1 - β * h / 2) with hc
  obtain ⟨ξ₀⟩ := ‹Nonempty Ξ›
  have hϑ0 : 0 ≤ ϑ := (norm_nonneg _).trans (htr 0 (fun i => i.elim0) ξ₀)
  have hB0 : 0 ≤ B :=
    (norm_nonneg _).trans (hB 0 hK (fun i => i.elim0) ξ₀ _ (left_mem_segment ℝ _ _))
  have hBϑ : 0 ≤ B * ϑ := mul_nonneg hB0 hϑ0
  set A := ℒ (x 0 fun i => i.elim0) - ℒinf with hA
  have hA0 : 0 ≤ A := sub_nonneg.2 (hinf 0 _)
  have hs := sum_iterE_add_le (μ := μ)
    (a := fun k ω => ENNReal.ofReal (ℒ (x k ω) - ℒinf))
    (e := fun k ω => ENNReal.ofReal (c * γ * ‖g (x k ω)‖ ^ 2))
    (b := fun k ω ξ => ENNReal.ofReal (c * ‖P k ω ξ (g (x k ω))‖ ^ 2))
    (d := ENNReal.ofReal (B * ϑ)) (K := K) (fun k hk ω ξ => by
      have h1 := loss_truncated_projGradStep_le hℒ hg (hP k ω ξ) h (x k ω) (htr k ω ξ)
        (hB k hk ω ξ)
      rw [← hc] at h1
      have h2 := hinf (k + 1) (Fin.snoc ω ξ)
      have h3 := hinf k ω
      rw [← ENNReal.ofReal_add (sub_nonneg.2 h2) (by positivity),
        ← ENNReal.ofReal_add (sub_nonneg.2 h3) hBϑ]
      exact ENNReal.ofReal_le_ofReal (by linarith))
    (fun k ω => ofReal_mul_le_lintegral hh.le (hγ k ω))
  have hcγ : 0 < c * γ := mul_pos hh hγ0
  have he : ∀ k, iterE μ k (fun ω => ENNReal.ofReal (c * γ * ‖g (x k ω)‖ ^ 2)) =
      ENNReal.ofReal (c * γ) * iterE μ k (fun ω => ENNReal.ofReal (‖g (x k ω)‖ ^ 2)) := fun k => by
    rw [← iterE_const_mul _ ENNReal.ofReal_ne_top]
    exact congrArg _ (funext fun ω => ENNReal.ofReal_mul hcγ.le)
  simp only [he] at hs
  set X := (A / (K * c) + B * ϑ / c) / γ with hX
  have hX0 : 0 ≤ X := by positivity
  by_contra hcon
  push Not at hcon
  have hlt : ∑ k ∈ range K, ENNReal.ofReal (c * γ) * ENNReal.ofReal X <
      ∑ k ∈ range K, ENNReal.ofReal (c * γ) *
        iterE μ k (fun ω => ENNReal.ofReal (‖g (x k ω)‖ ^ 2)) := by
    refine ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 hK⟩ fun k hk => ?_
    exact (ENNReal.mul_lt_mul_iff_right (by simpa using hcγ) ENNReal.ofReal_ne_top).2
      (hcon k (Finset.mem_range.1 hk))
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hval : ((K : ℝ) * (c * γ * X)) = A + K * (B * ϑ) := by
    rw [hX]
    field_simp
  have hsum : ∑ _k ∈ range K, ENNReal.ofReal (c * γ) * ENNReal.ofReal X =
      ENNReal.ofReal A + (K : ℝ≥0∞) * ENNReal.ofReal (B * ϑ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_mul hcγ.le,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg K), hval,
      ENNReal.ofReal_add hA0 (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg K)]
  have hle := (le_self_add).trans hs
  change _ ≤ ENNReal.ofReal A + _ at hle
  rw [← hsum] at hle
  exact absurd hle (not_le.2 hlt)

/-- **Abstract gradient-coupled tolerance (no measurability).**  With
`‖x_{k+1} − x̂_{k+1}‖ ≤ c₀ λ ‖P ∇ℒ(x_k)‖² / B`, `c₀ < 1 − βλ/2`, and a capture fraction `γ > 0`,
the iterated expectations of `‖∇ℒ(x_k)‖²` are summable and tend to `0`. -/
theorem tendsto_iterE_grad_sq [IsProbabilityMeasure μ]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {x : (k : ℕ) → (Fin k → Ξ) → E} {P : (k : ℕ) → (Fin k → Ξ) → Ξ → E →L[ℝ] E}
    (hP : ∀ k ω ξ, IsOrthProj (P k ω ξ)) {h B c₀ ℒinf γ : ℝ}
    (htr : ∀ k ω ξ, ‖x (k + 1) (Fin.snoc ω ξ) - projGradStep (P k ω ξ) g h (x k ω)‖ ≤
      c₀ * h * ‖P k ω ξ (g (x k ω))‖ ^ 2 / B)
    (hB : ∀ k ω ξ, ∀ w ∈ segment ℝ (projGradStep (P k ω ξ) g h (x k ω)) (x (k + 1) (Fin.snoc ω ξ)),
      ‖g w‖ ≤ B) (hB0 : 0 < B) (hh : 0 < h) (hc : c₀ < 1 - β * h / 2)
    (hinf : ∀ k ω, ℒinf ≤ ℒ (x k ω)) (hγ0 : 0 < γ)
    (hγ : ∀ k ω, ENNReal.ofReal (γ * ‖g (x k ω)‖ ^ 2) ≤
      ∫⁻ ξ, ENNReal.ofReal (‖P k ω ξ (g (x k ω))‖ ^ 2) ∂μ) :
    Tendsto (fun k => iterE μ k fun ω => ENNReal.ofReal (‖g (x k ω)‖ ^ 2)) atTop (𝓝 0) := by
  set c' := h * (1 - β * h / 2 - c₀) with hc'
  have hc'0 : 0 < c' := mul_pos hh (by linarith)
  have hs := fun K : ℕ => sum_iterE_add_le (μ := μ)
    (a := fun k ω => ENNReal.ofReal (ℒ (x k ω) - ℒinf))
    (e := fun k ω => ENNReal.ofReal (c' * γ * ‖g (x k ω)‖ ^ 2))
    (b := fun k ω ξ => ENNReal.ofReal (c' * ‖P k ω ξ (g (x k ω))‖ ^ 2))
    (d := 0) (K := K) (fun k _ ω ξ => by
      have h1 := loss_truncated_projGradStep_le hℒ hg (hP k ω ξ) h (x k ω) (htr k ω ξ) (hB k ω ξ)
      have h2 := hinf (k + 1) (Fin.snoc ω ξ)
      have h3 := hinf k ω
      rw [← ENNReal.ofReal_add (sub_nonneg.2 h2) (by positivity), add_zero]
      refine ENNReal.ofReal_le_ofReal ?_
      have h4 : B * (c₀ * h * ‖P k ω ξ (g (x k ω))‖ ^ 2 / B) =
          c₀ * h * ‖P k ω ξ (g (x k ω))‖ ^ 2 := by field_simp
      rw [h4] at h1
      rw [hc']
      nlinarith)
    (fun k ω => ofReal_mul_le_lintegral hc'0.le (hγ k ω))
  have hcγ : 0 < c' * γ := mul_pos hc'0 hγ0
  have he : ∀ k, iterE μ k (fun ω => ENNReal.ofReal (c' * γ * ‖g (x k ω)‖ ^ 2)) =
      ENNReal.ofReal (c' * γ) * iterE μ k (fun ω => ENNReal.ofReal (‖g (x k ω)‖ ^ 2)) := fun k => by
    rw [← iterE_const_mul _ ENNReal.ofReal_ne_top]
    exact congrArg _ (funext fun ω => ENNReal.ofReal_mul hcγ.le)
  simp only [he, mul_zero, add_zero] at hs
  set f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (c' * γ) *
    iterE μ k (fun ω => ENNReal.ofReal (‖g (x k ω)‖ ^ 2)) with hf
  have hA : iterE μ 0 (fun ω => ENNReal.ofReal (ℒ (x 0 ω) - ℒinf)) ≠ ∞ := ENNReal.ofReal_ne_top
  have htsum : ∑' k, f k ≠ ∞ := by
    refine ne_top_of_le_ne_top hA ?_
    rw [ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun K => (le_self_add).trans (hs K)
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top htsum
  have hne : ENNReal.ofReal (c' * γ) ≠ 0 := by simpa using hcγ
  have ht' := ENNReal.Tendsto.const_mul (a := (ENNReal.ofReal (c' * γ))⁻¹) ht
    (Or.inr (ENNReal.inv_ne_top.2 hne))
  simp only [mul_zero] at ht'
  refine ht'.congr fun k => ?_
  rw [hf, ← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]

/-- The iterate along a probe path of the stationary process `x_{k+1} = step(ξ_{k+1}, x_k)`. -/
def pathIter (step : Ξ → E → E) (x₀ : E) : (k : ℕ) → (Fin k → Ξ) → E
  | 0, _ => x₀
  | k + 1, ω => step (ω (Fin.last k)) (pathIter step x₀ k (Fin.init ω))

omit [MeasurableSpace Ξ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma pathIter_snoc (step : Ξ → E → E) (x₀ : E) (k : ℕ) (ω : Fin k → Ξ) (ξ : Ξ) :
    pathIter step x₀ (k + 1) (Fin.snoc ω ξ) = step ξ (pathIter step x₀ k ω) := by
  simp [pathIter]

end Paths

/-! ### Theorem B for the concrete probed step -/

section ProbeConcrete

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The Galerkin projector `Π̂ = Û Ûᵀ (·) V̂ V̂ᵀ` of the concrete probed step. -/
noncomputable def probeProj (G W : Matrix m n ℝ) (ω : n → ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  leftProj (probeU G W ω) * rightProj (probeV G W ω)

theorem isOrthProj_probeProj (G W : Matrix m n ℝ) (ω : n → ℝ) :
    IsOrthProj (probeProj G W ω) :=
  isOrthProj_leftProj_mul_rightProj (thinU_orthonormal _) (thinU_orthonormal _)

/-- The probed step is a projected gradient step with `Π̂`. -/
theorem probePre_eq_projGradStep (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ω : n → ℝ)
    (W : Matrix m n ℝ) : probePre g lr ω W = projGradStep (probeProj (g W) W ω) g lr W := by
  have h := augStep_eq_projGradStep (probeU_capture (g W) W ω).1 (probeV_capture (g W) W ω).1
    (Matrix.diagonal (thinσ W)) g lr
  rw [← thin_eq] at h
  exact h

theorem norm_probeProj_apply (G W : Matrix m n ℝ) (ω : n → ℝ) :
    ‖probeProj G W ω G‖ = ‖(probeU G W ω)ᵀ * G * probeV G W ω‖ := by
  classical
  exact norm_galerkin_apply (thinU_orthonormal _) (thinU_orthonormal _) G

/-- **Theorem B for the concrete step**: `‖Π̂ G‖² ≥ ‖P(W) G‖² + ‖N ω‖² / ‖ω‖²`.
One extra column `G ω` makes the augmentation see the doubly-normal block.  This is
`BlindSpot.norm_sq_galerkin_ge_of_probe` with all capture hypotheses discharged. -/
theorem probe_capture_ge [DecidableEq m] (G W : Matrix m n ℝ) (ω : n → ℝ) :
    ‖tangentProj (thinU W) (thinV W) G‖ ^ 2 +
        (normalBlock (thinU W) (thinV W) G *ᵥ ω) ⬝ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω) /
          (ω ⬝ᵥ ω) ≤ ‖probeProj G W ω G‖ ^ 2 := by
  rw [norm_probeProj_apply]
  obtain ⟨h1, h2, h3⟩ := probeU_capture G W ω
  obtain ⟨h4, h5⟩ := probeV_capture G W ω
  exact norm_sq_galerkin_ge_of_probe (thinU_orthonormal W) (thinV_orthonormal W)
    (thinU_orthonormal _) (thinU_orthonormal _) h1 h2 h3 h4 h5

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ] {ω : Ξ → n → ℝ}

/-- **Expected capture for an arbitrary selection (no measurability).**  If `C ξ` dominates the
probe bound pointwise, then `∫⁻ C ≥ ‖P G‖² + ‖N‖²_F / n ≥ ‖G‖²_F / n`.  In particular this holds for
`C ξ = ‖Û_ξᵀ G V̂_ξ‖²` for any selection of the bases, measurable or not. -/
theorem lintegral_capture_ge [DecidableEq m] [Nonempty n] (hiso : IsIsotropicLaw μ ω)
    {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (G : Matrix m n ℝ) {C : Ξ → ℝ}
    (hC : ∀ ξ, ‖tangentProj U V G‖ ^ 2 + (normalBlock U V G *ᵥ ω ξ) ⬝ᵥ
      (normalBlock U V G *ᵥ ω ξ) / (ω ξ ⬝ᵥ ω ξ) ≤ C ξ) :
    ENNReal.ofReal (‖tangentProj U V G‖ ^ 2 + ‖normalBlock U V G‖ ^ 2 / Fintype.card n) ≤
        ∫⁻ ξ, ENNReal.ofReal (C ξ) ∂μ ∧
      ENNReal.ofReal ((1 / Fintype.card n) * ‖G‖ ^ 2) ≤ ∫⁻ ξ, ENNReal.ofReal (C ξ) ∂μ := by
  set N := normalBlock U V G with hN
  set T := tangentProj U V G with hT
  set f : Ξ → ℝ := fun ξ => ‖T‖ ^ 2 + (N *ᵥ ω ξ) ⬝ᵥ (N *ᵥ ω ξ) / (ω ξ ⬝ᵥ ω ξ) with hf
  have hint : Integrable f μ := (integrable_const _).add (hiso.integrable_mulVec_sq N)
  have hint' : ∫ ξ, f ξ ∂μ = ‖T‖ ^ 2 + ‖N‖ ^ 2 / Fintype.card n := by
    rw [hf, integral_add (integrable_const _) (hiso.integrable_mulVec_sq N),
      hiso.integral_mulVec_sq N]
    simp
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => by
    refine add_nonneg (sq_nonneg _) (div_nonneg ?_ (dotProduct_self_nonneg _))
    exact dotProduct_self_nonneg _
  have h1 : ENNReal.ofReal (‖T‖ ^ 2 + ‖N‖ ^ 2 / Fintype.card n) ≤
      ∫⁻ ξ, ENNReal.ofReal (C ξ) ∂μ := by
    rw [← hint', ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)]
    exact lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hC ξ)
  refine ⟨h1, le_trans (ENNReal.ofReal_le_ofReal ?_) h1⟩
  have hcard : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hpyth : ‖T‖ ^ 2 + ‖N‖ ^ 2 = ‖G‖ ^ 2 := norm_sq_tangentProj_add_normal hU hV G
  rw [← hpyth, one_div, inv_mul_eq_div, add_div]
  have := div_le_self (sq_nonneg ‖T‖) hcard
  linarith

/-- **Theorem B for the Gaussian probe, or any isotropic law.**  The concrete
probed step `Û = orth[U, G V, G ω]`, `V̂ = orth[V, Gᵀ Û]` captures in expectation
`E ‖Π̂ G‖² ≥ ‖P(W) G‖² + ‖N‖²_F / n ≥ ‖G‖²_F / n`.  Expectation in the sense of the lower integral,
so that no measurability of the chosen bases is required; for measurable selections this is the
usual expectation. -/
theorem lintegral_probeProj_ge [DecidableEq m] [Nonempty n] (hiso : IsIsotropicLaw μ ω)
    (G W : Matrix m n ℝ) :
    ENNReal.ofReal (‖tangentProj (thinU W) (thinV W) G‖ ^ 2 +
        ‖normalBlock (thinU W) (thinV W) G‖ ^ 2 / Fintype.card n) ≤
        ∫⁻ ξ, ENNReal.ofReal (‖probeProj G W (ω ξ) G‖ ^ 2) ∂μ ∧
      ENNReal.ofReal ((1 / Fintype.card n) * ‖G‖ ^ 2) ≤
        ∫⁻ ξ, ENNReal.ofReal (‖probeProj G W (ω ξ) G‖ ^ 2) ∂μ :=
  lintegral_capture_ge hiso (thinU_orthonormal W) (thinV_orthonormal W) G fun ξ =>
    probe_capture_ge G W (ω ξ)

/-- The concrete probed iteration along a probe path. -/
noncomputable def probeIter (T : Matrix m n ℝ → Matrix m n ℝ) (g : Matrix m n ℝ → Matrix m n ℝ)
    (lr : ℝ) (ω : Ξ → n → ℝ) (W₀ : Matrix m n ℝ) : (k : ℕ) → (Fin k → Ξ) → Matrix m n ℝ :=
  pathIter (fun ξ W => probeStep T g lr (ω ξ) W) W₀

/-- The convergence of the concrete method for any capture fraction `γ`. -/
theorem exists_iterE_grad_sq_le_of_capture [Nonempty Ξ]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hcap : ∀ G W : Matrix m n ℝ, ENNReal.ofReal (γ * ‖G‖ ^ 2) ≤
      ∫⁻ ξ, ENNReal.ofReal (‖probeProj G W (ω ξ) G‖ ^ 2) ∂μ)
    {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) (W₀ : Matrix m n ℝ) {lr B ℒinf : ℝ} {K : ℕ}
    (hB : ∀ k < K, ∀ ω' ξ, ∀ w ∈ segment ℝ (probePre g lr (ω ξ) (probeIter T g lr ω W₀ k ω'))
      (T (probePre g lr (ω ξ) (probeIter T g lr ω W₀ k ω'))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) (hK : 0 < K) :
    ∃ k < K, iterE μ k (fun ω' => ENNReal.ofReal (‖g (probeIter T g lr ω W₀ k ω')‖ ^ 2)) ≤
      ENNReal.ofReal (((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        B * ϑ / (lr * (1 - β * lr / 2))) / γ) := by
  classical
  set x := probeIter T g lr ω W₀ with hx
  have hsucc : ∀ k (ω' : Fin k → Ξ) ξ, x (k + 1) (Fin.snoc ω' ξ) =
      T (projGradStep (probeProj (g (x k ω')) (x k ω') (ω ξ)) g lr (x k ω')) := fun k ω' ξ => by
    rw [← probePre_eq_projGradStep]
    exact pathIter_snoc _ _ _ _ _
  exact exists_iterE_grad_sq_le (μ := μ) (x := x) hℒ hg
    (P := fun k ω' ξ => probeProj (g (x k ω')) (x k ω') (ω ξ))
    (fun k ω' ξ => isOrthProj_probeProj _ _ _) (ϑ := ϑ) (B := B) (h := lr) (ℒinf := ℒinf)
    (fun k ω' ξ => by rw [hsucc]; exact hT _)
    (fun k hk ω' ξ w hw => by
      rw [hsucc, ← probePre_eq_projGradStep] at hw
      exact hB k hk ω' ξ w hw)
    (fun k ω' => hinf _) hγ0 (fun k ω' => hcap _ _) hh hK

/-- **Theorem B, convergence of the concrete method.**  For a `β`-smooth loss
bounded below, an isotropic probe law, any truncation with `‖T X − X‖ ≤ ϑ`, `T = svdTrunc ϑ` for
instance, and a gradient bound `B` on the truncation segments:
`min_{k<K} E ‖∇ℒ(W_k)‖² ≤ n [(ℒ(W₀) − ℒ_inf) / (K c) + B ϑ / c]`, `c = λ (1 − βλ/2) > 0`, where
`W_k` are the concrete iterates and `E` is the iterated expectation `iterE`.  All bases are
derived.  See `exists_lintegral_gaussian_grad_sq_le` for the Gaussian probe, with a better constant
and without `B`. -/
theorem exists_iterE_grad_sq_le_probeIter [Nonempty n] [Nonempty Ξ]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hiso : IsIsotropicLaw μ ω) {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) (W₀ : Matrix m n ℝ) {lr B ℒinf : ℝ} {K : ℕ}
    (hB : ∀ k < K, ∀ ω' ξ, ∀ w ∈ segment ℝ (probePre g lr (ω ξ) (probeIter T g lr ω W₀ k ω'))
      (T (probePre g lr (ω ξ) (probeIter T g lr ω W₀ k ω'))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) (hK : 0 < K) :
    ∃ k < K, iterE μ k (fun ω' => ENNReal.ofReal (‖g (probeIter T g lr ω W₀ k ω')‖ ^ 2)) ≤
      ENNReal.ofReal (Fintype.card n * ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        B * ϑ / (lr * (1 - β * lr / 2)))) := by
  classical
  have hγ0 : (0 : ℝ) < 1 / Fintype.card n := by
    have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    positivity
  obtain ⟨k, hk, hle⟩ := exists_iterE_grad_sq_le_of_capture hℒ hg hγ0
    (fun G W => (lintegral_probeProj_ge hiso G W).2) hT W₀ hB hinf hh hK
  refine ⟨k, hk, hle.trans (le_of_eq ?_)⟩
  rw [div_div_eq_mul_div, div_one, mul_comm]

/-- **The convergence bound for the library's truncated SVD** (item 1 of the plan): the statement
of `exists_iterE_grad_sq_le_probeIter` with `T = svdTrunc ϑ`, the truncation
`EckartYoung.truncation` at the tolerance rank, for any isotropic probe law, the Gaussian one in
particular.  The tolerance hypothesis of the blind-spot module is discharged. -/
theorem exists_iterE_grad_sq_le_svdTrunc [Nonempty n] [Nonempty Ξ]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hiso : IsIsotropicLaw μ ω) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (W₀ : Matrix m n ℝ) {lr B ℒinf : ℝ} {K : ℕ}
    (hB : ∀ k < K, ∀ ω' ξ, ∀ w ∈ segment ℝ
      (probePre g lr (ω ξ) (probeIter (svdTrunc ϑ) g lr ω W₀ k ω'))
      (svdTrunc ϑ (probePre g lr (ω ξ) (probeIter (svdTrunc ϑ) g lr ω W₀ k ω'))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) (hK : 0 < K) :
    ∃ k < K, iterE μ k
        (fun ω' => ENNReal.ofReal (‖g (probeIter (svdTrunc ϑ) g lr ω W₀ k ω')‖ ^ 2)) ≤
      ENNReal.ofReal (Fintype.card n * ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        B * ϑ / (lr * (1 - β * lr / 2)))) :=
  exists_iterE_grad_sq_le_probeIter hℒ hg hiso (norm_svdTrunc_sub_le hϑ) W₀ hB hinf hh hK

/-- The concrete step with the **gradient-coupled tolerance** `ϑ = c₀ λ ‖Π̂ ∇ℒ(W)‖² / B`, for a
family `T ϑ` of truncations. -/
noncomputable def coupledStep (T : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (g : Matrix m n ℝ → Matrix m n ℝ) (lr c₀ B : ℝ) (ω : n → ℝ) (W : Matrix m n ℝ) :
    Matrix m n ℝ :=
  T (c₀ * lr * ‖probeProj (g W) W ω (g W)‖ ^ 2 / B) (probePre g lr ω W)

/-- **Convergence to a stationary point of the full problem.**  With the
gradient-coupled tolerance, `0 ≤ c₀ < 1 − βλ/2` and a capture fraction `γ > 0`, the concrete
iterates satisfy `E ‖∇ℒ(W_k)‖² → 0`, in the sense of the iterated expectation.  Unlike the
blind-spot iteration, the limit is a stationary point of the full problem, not only of the
fixed-rank one. -/
theorem tendsto_iterE_grad_sq_coupled {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {γ : ℝ} (hγ0 : 0 < γ)
    (hcap : ∀ G W : Matrix m n ℝ, ENNReal.ofReal (γ * ‖G‖ ^ 2) ≤
      ∫⁻ ξ, ENNReal.ofReal (‖probeProj G W (ω ξ) G‖ ^ 2) ∂μ)
    {T : ℝ → Matrix m n ℝ → Matrix m n ℝ} (hT : ∀ ϑ, 0 ≤ ϑ → ∀ X, ‖T ϑ X - X‖ ≤ ϑ)
    (W₀ : Matrix m n ℝ) {lr B c₀ ℒinf : ℝ} (hB0 : 0 < B) (hlr : 0 < lr) (hc0 : 0 ≤ c₀)
    (hc : c₀ < 1 - β * lr / 2)
    (hB : ∀ k ω' ξ, ∀ w ∈ segment ℝ
      (probePre g lr (ω ξ) (pathIter (fun ξ W => coupledStep T g lr c₀ B (ω ξ) W) W₀ k ω'))
      (coupledStep T g lr c₀ B (ω ξ)
        (pathIter (fun ξ W => coupledStep T g lr c₀ B (ω ξ) W) W₀ k ω')), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) :
    Tendsto (fun k => iterE μ k fun ω' => ENNReal.ofReal
      (‖g (pathIter (fun ξ W => coupledStep T g lr c₀ B (ω ξ) W) W₀ k ω')‖ ^ 2)) atTop (𝓝 0) := by
  classical
  set x := pathIter (fun ξ W => coupledStep T g lr c₀ B (ω ξ) W) W₀ with hx
  have hsucc : ∀ k (ω' : Fin k → Ξ) ξ, x (k + 1) (Fin.snoc ω' ξ) =
      coupledStep T g lr c₀ B (ω ξ) (x k ω') := fun k ω' ξ => pathIter_snoc _ _ _ _ _
  refine tendsto_iterE_grad_sq (μ := μ) (x := x) hℒ hg
    (P := fun k ω' ξ => probeProj (g (x k ω')) (x k ω') (ω ξ))
    (fun k ω' ξ => isOrthProj_probeProj _ _ _) (c₀ := c₀) (B := B) (ℒinf := ℒinf)
    (fun k ω' ξ => ?_) (fun k ω' ξ w hw => ?_) hB0 hlr hc (fun k ω' => hinf _) hγ0
    (fun k ω' => hcap _ _)
  · rw [hsucc, ← probePre_eq_projGradStep]
    exact hT _ (by positivity) _
  · rw [← probePre_eq_projGradStep] at hw
    exact hB k ω' ξ w (by rwa [hsucc] at hw)

/-- The gradient-coupled statement for the library's truncated SVD and any isotropic probe law. -/
theorem tendsto_iterE_grad_sq_svdTrunc [Nonempty n] {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hiso : IsIsotropicLaw μ ω) (W₀ : Matrix m n ℝ)
    {lr B c₀ ℒinf : ℝ} (hB0 : 0 < B) (hlr : 0 < lr) (hc0 : 0 ≤ c₀) (hc : c₀ < 1 - β * lr / 2)
    (hB : ∀ k ω' ξ, ∀ w ∈ segment ℝ
      (probePre g lr (ω ξ) (pathIter (fun ξ W => coupledStep svdTrunc g lr c₀ B (ω ξ) W) W₀ k ω'))
      (coupledStep svdTrunc g lr c₀ B (ω ξ)
        (pathIter (fun ξ W => coupledStep svdTrunc g lr c₀ B (ω ξ) W) W₀ k ω')), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) :
    Tendsto (fun k => iterE μ k fun ω' => ENNReal.ofReal (‖g (pathIter
      (fun ξ W => coupledStep svdTrunc g lr c₀ B (ω ξ) W) W₀ k ω')‖ ^ 2)) atTop (𝓝 0) := by
  classical
  have hγ0 : (0 : ℝ) < 1 / Fintype.card n := by
    have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    positivity
  exact tendsto_iterE_grad_sq_coupled hℒ hg hγ0 (fun G W => (lintegral_probeProj_ge hiso G W).2)
    (fun ϑ hϑ X => norm_svdTrunc_sub_le hϑ X) W₀ hB0 hlr hc0 hc hB hinf

/-! #### Escape from the blind spot -/

/-- At a blind-spot point the normal block is the whole gradient. -/
theorem normalBlock_eq_of_tangentProj_eq_zero [DecidableEq m] {G W : Matrix m n ℝ}
    (hG : tangentProj (thinU W) (thinV W) G = 0) : normalBlock (thinU W) (thinV W) G = G := by
  obtain ⟨hl, hr⟩ :=
    (tangentProj_eq_zero_iff (thinU_orthonormal W) (thinV_orthonormal W) G).1 hG
  rw [normalBlock, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc (thinU W), hl, Matrix.mul_zero,
    sub_zero, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hr, Matrix.zero_mul, sub_zero]

/-- The probe bound at a blind-spot point: `‖Π̂ G‖² ≥ ‖G ω‖² / ‖ω‖²`. -/
theorem probeProj_sq_ge_of_blindSpot {G W : Matrix m n ℝ}
    (hG : tangentProj (thinU W) (thinV W) G = 0) (ω : n → ℝ) :
    (G *ᵥ ω) ⬝ᵥ (G *ᵥ ω) / (ω ⬝ᵥ ω) ≤ ‖probeProj G W ω G‖ ^ 2 := by
  classical
  have h := probe_capture_ge G W ω
  rw [hG, normalBlock_eq_of_tangentProj_eq_zero hG] at h
  simpa using h

/-- **The probed step leaves the blind spot.**  Let `P(W) ∇ℒ(W) = 0`, and let the tolerance satisfy
`ϑ² < λ² ‖G ω‖² / ‖ω‖²`, `G = ∇ℒ(W)`.  Then the probed step moves: `T(Ŵ) ≠ W`.  Contrast
`bugStep_svdTrunc_eq_self`: without the probe the same point is an exact fixed point. -/
theorem probeStep_ne_self {g : Matrix m n ℝ → Matrix m n ℝ} {W : Matrix m n ℝ}
    (hG : tangentProj (thinU W) (thinV W) (g W) = 0) {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) {lr : ℝ} {ω : n → ℝ}
    (hϑ : ϑ ^ 2 < lr ^ 2 * ((g W *ᵥ ω) ⬝ᵥ (g W *ᵥ ω) / (ω ⬝ᵥ ω))) :
    probeStep T g lr ω W ≠ W := by
  intro h
  have h1 := hT (probePre g lr ω W)
  have h2 : T (probePre g lr ω W) = W := h
  rw [h2, probePre_eq_projGradStep, projGradStep] at h1
  have e : W - (W - lr • probeProj (g W) W ω (g W)) = lr • probeProj (g W) W ω (g W) := by abel
  rw [e, norm_smul, Real.norm_eq_abs] at h1
  have h0 : 0 ≤ |lr| * ‖probeProj (g W) W ω (g W)‖ := by positivity
  have h3 := pow_le_pow_left₀ h0 h1 2
  rw [mul_pow, sq_abs] at h3
  have h4 := mul_le_mul_of_nonneg_left (probeProj_sq_ge_of_blindSpot hG ω) (sq_nonneg lr)
  linarith

/-- **The probed step strictly decreases a smooth loss at the blind spot**, by at least
`c ‖G ω‖² / ‖ω‖² − B ϑ`, `c = λ (1 − βλ/2)`. -/
theorem loss_probeStep_le_of_blindSpot {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ}
    {β : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {W : Matrix m n ℝ}
    (hG : tangentProj (thinU W) (thinV W) (g W) = 0) {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ B : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) {lr : ℝ} {ω : n → ℝ} (hc : 0 ≤ lr * (1 - β * lr / 2))
    (hB : ∀ w ∈ segment ℝ (probePre g lr ω W) (T (probePre g lr ω W)), ‖g w‖ ≤ B) :
    ℒ (probeStep T g lr ω W) ≤
      ℒ W - lr * (1 - β * lr / 2) * ((g W *ᵥ ω) ⬝ᵥ (g W *ᵥ ω) / (ω ⬝ᵥ ω)) + B * ϑ := by
  have hpre := probePre_eq_projGradStep g lr ω W
  have h1 := loss_truncated_projGradStep_le hℒ hg (isOrthProj_probeProj (g W) W ω) lr W
    (x₁ := T (probePre g lr ω W)) (ϑ := ϑ) (G := B)
    (by rw [← hpre]; exact hT _) (by rw [← hpre]; exact hB)
  have h2 := mul_le_mul_of_nonneg_left (probeProj_sq_ge_of_blindSpot hG ω) hc
  change ℒ (T (probePre g lr ω W)) ≤ _
  linarith

/-- **One probe grows the rank at the blind spot.**  Let `r = rank W > 0`, `P(W) G = 0`, the step
size small enough that `|λ| ‖G‖₂ ≤ σ_{r-1}(W)` and `ϑ² < λ² ‖G ω‖² / ‖ω‖²`.  Then every truncation
within `ϑ` of the augmented matrix has rank `> r`: the rank grows, whereas without the probe it
never does (`bugStep_iterate_eq_self`).  Proof: `Ŵ = W − λ Π̂ G` with `Π̂ G` doubly normal to `W`
and `‖λ Π̂ G‖₂ ≤ σ_{r-1}(W)`, so `W` is a best rank-`r` approximation of `Ŵ`
(`quadLoss_le_of_specNorm_le`) at distance `|λ| ‖Π̂ G‖`. -/
theorem rank_lt_probeStep_of_blindSpot {g : Matrix m n ℝ → Matrix m n ℝ} {W : Matrix m n ℝ}
    (hG : tangentProj (thinU W) (thinV W) (g W) = 0) (hW : 0 < W.rank)
    {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ} (hT : ∀ X, ‖T X - X‖ ≤ ϑ) {lr : ℝ} {ω : n → ℝ}
    (hlr : |lr| * Curvature.specNorm (g W) ≤
      (Matrix.toEuclideanLin W).singularValues (W.rank - 1))
    (hϑ : ϑ ^ 2 < lr ^ 2 * ((g W *ᵥ ω) ⬝ᵥ (g W *ᵥ ω) / (ω ⬝ᵥ ω))) :
    W.rank < (probeStep T g lr ω W).rank := by
  classical
  set G := g W with hGdef
  set Uh := probeU G W ω with hUh
  set Vh := probeV G W ω with hVh
  set D := Uh * Uhᵀ * G * (Vh * Vhᵀ) with hD
  set N := (-lr) • D with hN
  obtain ⟨hUU, -, -⟩ := probeU_capture G W ω
  obtain ⟨hVV, -⟩ := probeV_capture G W ω
  obtain ⟨hl, hr⟩ := (tangentProj_eq_zero_iff (thinU_orthonormal W) (thinV_orthonormal W) G).1 hG
  have hU' : (thinU W)ᵀ * (Uh * Uhᵀ) = (thinU W)ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hUU
  have hDl : (thinU W)ᵀ * D = 0 := by
    calc (thinU W)ᵀ * D = ((thinU W)ᵀ * (Uh * Uhᵀ)) * G * (Vh * Vhᵀ) := by
          simp only [hD, Matrix.mul_assoc]
      _ = 0 := by rw [hU', hl, Matrix.zero_mul]
  have hDr : D * thinV W = 0 := by
    rw [hD, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, hVV, hr, Matrix.mul_zero,
      Matrix.mul_zero]
  have hNl : (thinU W)ᵀ * N = 0 := by rw [hN, Matrix.mul_smul, hDl, smul_zero]
  have hNr : N * thinV W = 0 := by rw [hN, Matrix.smul_mul, hDr, smul_zero]
  have hspecU : Curvature.specNorm (Uh * Uhᵀ) ≤ 1 := by
    have h1 := Curvature.specNorm_mul_le Uh Uhᵀ
    have h2 := Curvature.specNorm_le_one_of_orthonormal (thinU_orthonormal (probeK G W ω))
    rw [Curvature.specNorm_transpose] at h1
    have h3 := Curvature.specNorm_nonneg Uh
    change Curvature.specNorm Uh ≤ 1 at h2
    nlinarith
  have hspecV : Curvature.specNorm (Vh * Vhᵀ) ≤ 1 := by
    have h1 := Curvature.specNorm_mul_le Vh Vhᵀ
    have h2 := Curvature.specNorm_le_one_of_orthonormal
      (thinU_orthonormal (Matrix.fromCols (thinV W) (Gᵀ * probeU G W ω)))
    rw [Curvature.specNorm_transpose] at h1
    have h3 := Curvature.specNorm_nonneg Vh
    change Curvature.specNorm Vh ≤ 1 at h2
    nlinarith
  have hspecD : Curvature.specNorm D ≤ Curvature.specNorm G := by
    have h1 := Curvature.specNorm_mul_le (Uh * Uhᵀ * G) (Vh * Vhᵀ)
    have h2 := Curvature.specNorm_mul_le (Uh * Uhᵀ) G
    have h0 := Curvature.specNorm_nonneg G
    have h4 := Curvature.specNorm_nonneg (Uh * Uhᵀ * G)
    calc Curvature.specNorm D ≤ Curvature.specNorm (Uh * Uhᵀ * G) * 1 :=
          h1.trans (mul_le_mul_of_nonneg_left hspecV h4)
      _ ≤ 1 * Curvature.specNorm G := by
          rw [mul_one]
          exact h2.trans (mul_le_mul_of_nonneg_right hspecU h0)
      _ = Curvature.specNorm G := one_mul _
  have hspecN : Curvature.specNorm N ≤ |lr| * Curvature.specNorm G := by
    have e : Curvature.specNorm N ≤ |lr| * Curvature.specNorm D := by
      refine Curvature.specNorm_le_of (mul_nonneg (abs_nonneg _) (Curvature.specNorm_nonneg _))
        fun x => ?_
      rw [hN, map_smul, LinearMap.smul_apply, norm_smul, norm_neg, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (Curvature.norm_toEuclideanLin_le D x) (abs_nonneg _)
    exact e.trans (mul_le_mul_of_nonneg_left hspecD (abs_nonneg _))
  have hs : ∀ i, Curvature.specNorm N ≤ |thinσ W i| := fun i => by
    rw [abs_of_pos (thinσ_pos W i), thinσ_eq]
    refine hspecN.trans (hlr.trans ?_)
    exact (Matrix.toEuclideanLin W).singularValues_antitone (by omega)
  have hpre : probePre g lr ω W = W + N := by
    rw [hN, neg_smul, ← sub_eq_add_neg]
    have := probePre_eq_projGradStep g lr ω W
    rw [this, projGradStep]
    congr 2
    change leftProj Uh (rightProj Vh G) = D
    rw [leftProj_apply, rightProj_apply']
    simp only [hD, Matrix.mul_assoc]
  by_contra hcon
  rw [not_lt] at hcon
  have hmin := quadLoss_le_of_specNorm_le (thinU_orthonormal W) (thinV_orthonormal W) hNl hNr hs
    (Y := probeStep T g lr ω W) (by rwa [Fintype.card_fin])
  rw [← thin_eq, ← hpre] at hmin
  have h1 : ‖N‖ ≤ ‖T (probePre g lr ω W) - probePre g lr ω W‖ := by
    have e1 : W - probePre g lr ω W = -N := by rw [hpre]; abel
    have hq : ‖N‖ ^ 2 / 2 ≤ ‖T (probePre g lr ω W) - probePre g lr ω W‖ ^ 2 / 2 := by
      simpa [quadLoss, e1, norm_neg, probeStep] using hmin
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)
  have h2 := h1.trans (hT _)
  have h3 : ‖D‖ = ‖probeProj G W ω G‖ := by
    congr 1
    change _ = leftProj Uh (rightProj Vh G)
    rw [leftProj_apply, rightProj_apply']
    simp only [hD, Matrix.mul_assoc]
  have hNn : ‖N‖ ^ 2 = lr ^ 2 * ‖probeProj G W ω G‖ ^ 2 := by
    rw [hN, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq, h3]
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h5 := mul_le_mul_of_nonneg_left (probeProj_sq_ge_of_blindSpot hG ω) (sq_nonneg lr)
  rw [hNn] at h4
  linarith

omit [DecidableEq n] in
/-- **The Gaussian probe sees the blind spot with probability one**: if `G ≠ 0`, then
`‖G ω‖² / ‖ω‖² > 0` almost surely.  With `probeStep_ne_self`, `loss_probeStep_le_of_blindSpot` and
`rank_lt_probeStep_of_blindSpot`: at a blind-spot point with nonzero gradient, the probed step
(at tolerance below the random threshold `|λ| ‖G ω‖ / ‖ω‖`) moves, decreases the loss and grows the
rank, almost surely. -/
theorem ae_ratio_pos_stdGaussian {G : Matrix m n ℝ} (hG : G ≠ 0) :
    ∀ᵐ x : EuclideanSpace ℝ n ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ n)),
      0 < (G *ᵥ x.ofLp) ⬝ᵥ (G *ᵥ x.ofLp) / (x.ofLp ⬝ᵥ x.ofLp) := by
  filter_upwards [ae_mulVec_ne_zero_stdGaussian hG] with x hx
  have h1 : 0 < (G *ᵥ x.ofLp) ⬝ᵥ (G *ᵥ x.ofLp) :=
    lt_of_le_of_ne (dotProduct_self_nonneg _) fun h => hx (dotProduct_self_eq_zero.1 h.symm)
  have hx0 : x.ofLp ≠ 0 := fun h => hx (by rw [h, Matrix.mulVec_zero])
  have h2 : 0 < x.ofLp ⬝ᵥ x.ofLp :=
    lt_of_le_of_ne (dotProduct_self_nonneg _) fun h => hx0 (dotProduct_self_eq_zero.1 h.symm)
  exact div_pos h1 h2

end ProbeConcrete

/-! ### The parallel ordering: one left and one right probe -/

section ParallelAux

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The capture lower bound of a pair of probes: with `u = N ωᵣ`, `v = Nᵀ ωₗ`,
`κ(ωᵣ, ωₗ) = (uᵀ N v)² / (‖u‖² ‖v‖²)`. -/
noncomputable def twoProbeRatio (N : Matrix m n ℝ) (ωr : n → ℝ) (ωl : m → ℝ) : ℝ :=
  ((N *ᵥ ωr) ⬝ᵥ (N *ᵥ (Nᵀ *ᵥ ωl))) ^ 2 /
    (((N *ᵥ ωr) ⬝ᵥ (N *ᵥ ωr)) * ((Nᵀ *ᵥ ωl) ⬝ᵥ (Nᵀ *ᵥ ωl)))

/-- The algebra of the chain: `‖N Nᵀ u‖² / ‖u‖² ≥ (‖u‖² / ‖ω‖²)²` for `u = N ω`. -/
theorem sq_ratio_le (N : Matrix m n ℝ) (ω : n → ℝ) :
    ((N *ᵥ ω) ⬝ᵥ (N *ᵥ ω) / (ω ⬝ᵥ ω)) ^ 2 * ((N *ᵥ ω) ⬝ᵥ (N *ᵥ ω)) ≤
      (N *ᵥ (Nᵀ *ᵥ (N *ᵥ ω))) ⬝ᵥ (N *ᵥ (Nᵀ *ᵥ (N *ᵥ ω))) := by
  set u := N *ᵥ ω with hu
  set z := Nᵀ *ᵥ u with hz
  set y := N *ᵥ z with hy
  set p := u ⬝ᵥ u with hp
  set q := z ⬝ᵥ z with hq
  set w := ω ⬝ᵥ ω with hw
  set Y := y ⬝ᵥ y with hY
  have hp0 : 0 ≤ p := dotProduct_self_nonneg _
  have hq0 : 0 ≤ q := dotProduct_self_nonneg _
  have hw0 : 0 ≤ w := dotProduct_self_nonneg _
  have hY0 : 0 ≤ Y := dotProduct_self_nonneg _
  have h1 : q ^ 2 ≤ p * Y := by
    have e : u ⬝ᵥ y = q := by
      rw [hy, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have := sq_dotProduct_le u y
    rwa [e] at this
  have h2 : p ^ 2 ≤ w * q := by
    have e : ω ⬝ᵥ z = p := by
      rw [hz, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
        dotProduct_comm]
    have := sq_dotProduct_le ω z
    rwa [e] at this
  rcases hw0.eq_or_lt with hw1 | hw1
  · rw [← hw1]
    simpa using hY0
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  -- `p³ ≤ Y w²`
  rcases hp0.eq_or_lt with hp1 | hp1
  · rw [← hp1]
    have : 0 ≤ Y * w ^ 2 := by positivity
    simpa using this
  have h3 : p ^ 4 ≤ w ^ 2 * q ^ 2 := by nlinarith [sq_nonneg (p ^ 2), mul_nonneg hw0 hq0]
  have h4 : p * p ^ 3 ≤ p * (Y * w ^ 2) := by
    calc p * p ^ 3 = p ^ 4 := by ring
      _ ≤ w ^ 2 * q ^ 2 := h3
      _ ≤ w ^ 2 * (p * Y) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = p * (Y * w ^ 2) := by ring
  have h5 := le_of_mul_le_mul_left h4 hp1
  calc p ^ 2 * p = p ^ 3 := by ring
    _ ≤ Y * w ^ 2 := h5

lemma measurable_dotProduct {l α : Type*} [Fintype l] [MeasurableSpace α] {a b : α → l → ℝ}
    (ha : Measurable a) (hb : Measurable b) : Measurable fun x => a x ⬝ᵥ b x :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_iff.1 ha i).mul (measurable_pi_iff.1 hb i)

omit [Fintype m] in
set_option linter.unusedFintypeInType false in
lemma measurable_mulVec_const (N : Matrix m n ℝ) : Measurable fun ω : n → ℝ => N *ᵥ ω :=
  measurable_pi_iff.2 fun _ => Finset.measurable_sum _ fun j _ =>
    (measurable_pi_apply j).const_mul _

lemma measurable_twoProbeRatio (N : Matrix m n ℝ) {α : Type*} [MeasurableSpace α]
    {a : α → n → ℝ} {b : α → m → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => twoProbeRatio N (a x) (b x) := by
  have hu : Measurable fun x => N *ᵥ a x := (measurable_mulVec_const N).comp ha
  have hv : Measurable fun x => Nᵀ *ᵥ b x := (measurable_mulVec_const Nᵀ).comp hb
  have hy : Measurable fun x => N *ᵥ (Nᵀ *ᵥ b x) := (measurable_mulVec_const N).comp hv
  exact ((measurable_dotProduct hu hy).pow_const 2).div
    ((measurable_dotProduct hu hu).mul (measurable_dotProduct hv hv))

end ParallelAux

section Parallel

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The transpose of a doubly-normal block is the doubly-normal block of the transpose. -/
theorem normalBlock_transpose [DecidableEq m] {k k' : Type*} [Fintype k] [Fintype k']
    (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (G : Matrix m n ℝ) :
    (normalBlock U V G)ᵀ = normalBlock V U Gᵀ := by
  simp only [normalBlock, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Any matrix fixing `U`, `G V` and `G ω` fixes the probe direction `N ω` of the normal block. -/
theorem mulVec_normalBlock_capture [DecidableEq m] {k k' : Type*} [Fintype k] [Fintype k']
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} {G : Matrix m n ℝ} {ω : n → ℝ} {P : Matrix m m ℝ}
    (hPU : P * U = U) (hPG : P * (G * V) = G * V) (hPω : P *ᵥ (G *ᵥ ω) = G *ᵥ ω) :
    P *ᵥ (normalBlock U V G *ᵥ ω) = normalBlock U V G *ᵥ ω := by
  set y := G *ᵥ ((1 - V * Vᵀ) *ᵥ ω) with hy
  have hw : y = G *ᵥ ω - (G * V) *ᵥ (Vᵀ *ᵥ ω) := by
    rw [hy, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  have hPy : P *ᵥ y = y := by
    rw [hw, Matrix.mulVec_sub, hPω, mulVec_mulVec_of_mul_eq hPG]
  have e : normalBlock U V G *ᵥ ω = y - U *ᵥ (Uᵀ *ᵥ y) := by
    rw [hy, normalBlock, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec (1 : Matrix m m ℝ) (U * Uᵀ), Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  rw [e, Matrix.mulVec_sub, hPy, mulVec_mulVec_of_mul_eq hPU]

/-- The Galerkin energy splits into the Riemannian gradient and the projected normal block. -/
theorem norm_sq_galerkin_eq_add [DecidableEq m] {k k' k₁ k₂ : Type*} [Fintype k] [Fintype k']
    [Fintype k₁] [Fintype k₂] [DecidableEq k] [DecidableEq k'] [DecidableEq k₁] [DecidableEq k₂]
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1)
    {G : Matrix m n ℝ} (hUU : Uh * Uhᵀ * U = U) (hUG : Uh * Uhᵀ * (G * V) = G * V)
    (hVV : Vh * Vhᵀ * V = V) (hVG : Vh * Vhᵀ * (Gᵀ * U) = Gᵀ * U) :
    ‖Uhᵀ * G * Vh‖ ^ 2 = ‖tangentProj U V G‖ ^ 2 +
      ‖Uh * Uhᵀ * normalBlock U V G * (Vh * Vhᵀ)‖ ^ 2 := by
  have heq := norm_sq_galerkin_eq_of_capture hUh hVh hU hV hUU hUG hVV hVG
  have hcap := galerkin_tangentProj_of_capture hUU hUG hVV hVG
  rw [leftProj_apply, rightProj_apply'] at hcap
  have hN' : normalBlock U V G = G - tangentProj U V G :=
    eq_sub_of_add_eq' (tangentProj_add_normal U V G)
  have hdiff : Uh * Uhᵀ * G * Vh * Vhᵀ - tangentProj U V G =
      Uh * Uhᵀ * normalBlock U V G * (Vh * Vhᵀ) := by
    rw [hN', Matrix.mul_sub, Matrix.sub_mul, show Uh * Uhᵀ * tangentProj U V G * (Vh * Vhᵀ) =
      tangentProj U V G by simpa only [Matrix.mul_assoc] using hcap]
    simp only [Matrix.mul_assoc]
  rwa [hdiff] at heq

/-- **Item 5: deterministic inequality for the parallel ordering.**  With
`Û ⊇ [U, G V, G ωᵣ]`, `V̂ ⊇ [V, Gᵀ U, Gᵀ ωₗ]` (both bases built from the old factors, as in the
GeoLoRA ordering), `‖Ûᵀ G V̂‖² ≥ ‖P(W) G‖² + κ(ωᵣ, ωₗ)`.  Unlike the sequential ordering the pair
`(u, v)` is not aligned: `u = N ωᵣ` and `v = Nᵀ ωₗ` are independent directions, which is why the
expected constant is weaker. -/
theorem norm_sq_galerkin_ge_of_two_probes [DecidableEq m] {k k' k₁ k₂ : Type*} [Fintype k]
    [Fintype k'] [Fintype k₁] [Fintype k₂] [DecidableEq k] [DecidableEq k'] [DecidableEq k₁]
    [DecidableEq k₂]
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1)
    {G : Matrix m n ℝ} {ωr : n → ℝ} {ωl : m → ℝ} (hUU : Uh * Uhᵀ * U = U)
    (hUG : Uh * Uhᵀ * (G * V) = G * V) (hUω : (Uh * Uhᵀ) *ᵥ (G *ᵥ ωr) = G *ᵥ ωr)
    (hVV : Vh * Vhᵀ * V = V) (hVG : Vh * Vhᵀ * (Gᵀ * U) = Gᵀ * U)
    (hVω : (Vh * Vhᵀ) *ᵥ (Gᵀ *ᵥ ωl) = Gᵀ *ᵥ ωl) :
    ‖tangentProj U V G‖ ^ 2 + twoProbeRatio (normalBlock U V G) ωr ωl ≤ ‖Uhᵀ * G * Vh‖ ^ 2 := by
  rw [norm_sq_galerkin_eq_add hU hV hUh hVh hUU hUG hVV hVG]
  set N := normalBlock U V G with hN
  have hu : (Uh * Uhᵀ) *ᵥ (N *ᵥ ωr) = N *ᵥ ωr := mulVec_normalBlock_capture hUU hUG hUω
  have hv : (Vh * Vhᵀ) *ᵥ (Nᵀ *ᵥ ωl) = Nᵀ *ᵥ ωl := by
    rw [hN, normalBlock_transpose]
    exact mulVec_normalBlock_capture hVV hVG hVω
  have hkey := sq_dotProduct_le_norm_sq_galerkin hUh hVh N hu hv
  have hC : twoProbeRatio N ωr ωl ≤ ‖Uh * Uhᵀ * N * (Vh * Vhᵀ)‖ ^ 2 := by
    refine div_le_of_le_mul₀ ?_ (sq_nonneg _) hkey
    exact mul_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _)
  linarith

/-- The pointwise lower bound behind the parallel constant: for fixed `ωᵣ`, with `u = N ωᵣ` and
`y = N Nᵀ u`, `κ(ωᵣ, ωₗ) ≥ (ωₗ ⬝ y)² / (ωₗ ⬝ ωₗ) / (‖u‖² ‖N‖₂²)`. -/
theorem twoProbeRatio_ge (N : Matrix m n ℝ) (ωr : n → ℝ) (ωl : m → ℝ) :
    ((ωl ⬝ᵥ (N *ᵥ (Nᵀ *ᵥ (N *ᵥ ωr)))) ^ 2 / (ωl ⬝ᵥ ωl)) /
      (((N *ᵥ ωr) ⬝ᵥ (N *ᵥ ωr)) * Curvature.specNorm N ^ 2) ≤ twoProbeRatio N ωr ωl := by
  classical
  set u := N *ᵥ ωr with hu
  set v := Nᵀ *ᵥ ωl with hv
  set y := N *ᵥ (Nᵀ *ᵥ u) with hy
  set s := Curvature.specNorm N with hs
  have hadj : ∀ (a : m → ℝ) (b : n → ℝ), a ⬝ᵥ (N *ᵥ b) = (Nᵀ *ᵥ a) ⬝ᵥ b := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hpair : ωl ⬝ᵥ y = u ⬝ᵥ (N *ᵥ v) := by
    rw [hy, hadj ωl, hadj u, dotProduct_comm]
  have hvv : v ⬝ᵥ v ≤ s ^ 2 * (ωl ⬝ᵥ ωl) := by
    have := dotProduct_mulVec_le_specNorm Nᵀ ωl
    rwa [Curvature.specNorm_transpose] at this
  rw [twoProbeRatio, ← hu, ← hv, hpair]
  set a := (u ⬝ᵥ (N *ᵥ v)) ^ 2 with ha
  set p := u ⬝ᵥ u with hp
  set w := ωl ⬝ᵥ ωl with hw
  set q := v ⬝ᵥ v with hq
  have ha0 : 0 ≤ a := sq_nonneg _
  have hp0 : 0 ≤ p := dotProduct_self_nonneg _
  have hw0 : 0 ≤ w := dotProduct_self_nonneg _
  have hq0 : 0 ≤ q := dotProduct_self_nonneg _
  rcases hq0.eq_or_lt with hq1 | hq1
  · -- `v = 0`
    have hv0 : v = 0 := dotProduct_self_eq_zero.1 hq1.symm
    have : a = 0 := by simp [ha, hv0]
    simp [this]
  rcases hp0.eq_or_lt with hp1 | hp1
  · have hu0 : u = 0 := dotProduct_self_eq_zero.1 hp1.symm
    have : a = 0 := by simp [ha, hu0]
    simp [this]
  have hsw : 0 < s ^ 2 * w := lt_of_lt_of_le hq1 hvv
  have hw1 : 0 < w := by
    rcases hw0.eq_or_lt with h | h
    · rw [← h, mul_zero] at hsw
      exact absurd hsw (lt_irrefl _)
    · exact h
  have hs1 : 0 < s ^ 2 := by
    by_contra hcon
    have : s ^ 2 = 0 := le_antisymm (not_lt.1 hcon) (sq_nonneg s)
    rw [this, zero_mul] at hsw
    exact absurd hsw (lt_irrefl _)
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : a * (p * q) ≤ a * (w * (p * s ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ ha0
    nlinarith
  exact this

variable {Ξr Ξl : Type*} [MeasurableSpace Ξr] [MeasurableSpace Ξl] {μr : Measure Ξr}
  {μl : Measure Ξl} [IsProbabilityMeasure μr] [IsProbabilityMeasure μl] {ωr : Ξr → n → ℝ}
  {ωl : Ξl → m → ℝ}

omit [DecidableEq n] in
/-- `(E r)² ≤ E r²` for the bounded variable `r = ‖N ω‖² / ‖ω‖²`. -/
theorem sq_integral_ratio_le (hiso : IsIsotropicLaw μr ωr) (N : Matrix m n ℝ) :
    (‖N‖ ^ 2 / Fintype.card n) ^ 2 ≤
      ∫ ξ, ((N *ᵥ ωr ξ) ⬝ᵥ (N *ᵥ ωr ξ) / (ωr ξ ⬝ᵥ ωr ξ)) ^ 2 ∂μr := by
  set r : Ξr → ℝ := fun ξ => (N *ᵥ ωr ξ) ⬝ᵥ (N *ᵥ ωr ξ) / (ωr ξ ⬝ᵥ ωr ξ) with hr
  set a := ‖N‖ ^ 2 / Fintype.card n with ha
  classical
  have hint : Integrable r μr := hiso.integrable_mulVec_sq N
  have hmean : ∫ ξ, r ξ ∂μr = a := hiso.integral_mulVec_sq N
  have hbound : ∀ ξ, r ξ ≤ Curvature.specNorm N ^ 2 := fun ξ => by
    refine div_le_of_le_mul₀ (dotProduct_self_nonneg _) (sq_nonneg _) ?_
    exact dotProduct_mulVec_le_specNorm N _
  have hr0 : ∀ ξ, 0 ≤ r ξ := fun ξ =>
    div_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _)
  have hint2 : Integrable (fun ξ => r ξ ^ 2) μr := by
    refine Integrable.of_bound (hint.aestronglyMeasurable.pow 2)
      ((Curvature.specNorm N ^ 2) ^ 2) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hr0 ξ) (hbound ξ) 2
  have h0 : 0 ≤ ∫ ξ, (r ξ - a) ^ 2 ∂μr := integral_nonneg fun _ => sq_nonneg _
  have e : ∫ ξ, (r ξ - a) ^ 2 ∂μr = ∫ ξ, r ξ ^ 2 ∂μr - a ^ 2 := by
    have e1 : (fun ξ => (r ξ - a) ^ 2) = fun ξ => (r ξ ^ 2 - 2 * a * r ξ) + a ^ 2 := by
      funext ξ; ring
    have h3 : Integrable (fun ξ => r ξ ^ 2 - 2 * a * r ξ) μr := hint2.sub (hint.const_mul _)
    rw [e1, integral_add h3 (integrable_const _), integral_sub hint2 (hint.const_mul _),
      integral_const_mul, hmean]
    simp
    ring
  linarith

/-- **Item 5: the expected capture of the parallel ordering, for every pair of independent
isotropic probes**: `E κ ≥ ‖N‖_F⁴ / (m n² ‖N‖₂²)`.  The chain: integrate `twoProbeRatio_ge` in `ωₗ`
by isotropy, use `sq_ratio_le`, then Jensen in `ωᵣ`.  For a flat square `N` this equals the true
value `‖N‖²_F / n²`. -/
theorem lintegral_twoProbeRatio_ge [Nonempty m] (hr : IsIsotropicLaw μr ωr)
    (hl : IsIsotropicLaw μl ωl) (N : Matrix m n ℝ) :
    ENNReal.ofReal ((‖N‖ ^ 2 / Fintype.card n) ^ 2 /
        (Fintype.card m * Curvature.specNorm N ^ 2)) ≤
      ∫⁻ ξ, ∫⁻ ξ', ENNReal.ofReal (twoProbeRatio N (ωr ξ) (ωl ξ')) ∂μl ∂μr := by
  set s := Curvature.specNorm N with hs
  set M : ℝ := (Fintype.card m : ℝ) with hM
  have hM0 : 0 < M := by rw [hM]; exact_mod_cast Fintype.card_pos
  set r : Ξr → ℝ := fun ξ => (N *ᵥ ωr ξ) ⬝ᵥ (N *ᵥ ωr ξ) / (ωr ξ ⬝ᵥ ωr ξ) with hrdef
  -- inner integral
  have hinner : ∀ ξ, ENNReal.ofReal (r ξ ^ 2 / (M * s ^ 2)) ≤
      ∫⁻ ξ', ENNReal.ofReal (twoProbeRatio N (ωr ξ) (ωl ξ')) ∂μl := fun ξ => by
    set u := N *ᵥ ωr ξ with hu
    set y := N *ᵥ (Nᵀ *ᵥ u) with hy
    set p := u ⬝ᵥ u with hp
    have hp0 : 0 ≤ p := dotProduct_self_nonneg _
    set c := (p * s ^ 2)⁻¹ with hc
    have hc0 : 0 ≤ c := inv_nonneg.2 (mul_nonneg hp0 (sq_nonneg s))
    have hint := (hl.integrable_ratio y).const_mul c
    have hval : ∫ ξ', c * ((ωl ξ' ⬝ᵥ y) ^ 2 / (ωl ξ' ⬝ᵥ ωl ξ')) ∂μl = c * ((y ⬝ᵥ y) / M) := by
      rw [integral_const_mul, hl.isotropic y]
    have hle : r ξ ^ 2 / (M * s ^ 2) ≤ c * ((y ⬝ᵥ y) / M) := by
      have h1 : r ξ ^ 2 * p ≤ y ⬝ᵥ y := sq_ratio_le N (ωr ξ)
      rcases hp0.eq_or_lt with hp1 | hp1
      · have hu0 : u = 0 := dotProduct_self_eq_zero.1 hp1.symm
        have hr0 : r ξ = 0 := by simp [hrdef, ← hu, hu0]
        simp [hr0, hc, ← hp1]
      rcases (sq_nonneg s).eq_or_lt with hs1 | hs1
      · rw [hc, ← hs1]
        simp
      rw [hc, div_le_iff₀ (by positivity)]
      have hs' : s ≠ 0 := fun h => by simp [h] at hs1
      have e : (p * s ^ 2)⁻¹ * ((y ⬝ᵥ y) / M) * (M * s ^ 2) = (y ⬝ᵥ y) / p := by
        field_simp
      rw [e, le_div_iff₀ hp1]
      exact h1
    calc ENNReal.ofReal (r ξ ^ 2 / (M * s ^ 2))
        ≤ ENNReal.ofReal (∫ ξ', c * ((ωl ξ' ⬝ᵥ y) ^ 2 / (ωl ξ' ⬝ᵥ ωl ξ')) ∂μl) := by
          rw [hval]
          exact ENNReal.ofReal_le_ofReal hle
      _ = ∫⁻ ξ', ENNReal.ofReal (c * ((ωl ξ' ⬝ᵥ y) ^ 2 / (ωl ξ' ⬝ᵥ ωl ξ'))) ∂μl :=
          ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ =>
            mul_nonneg hc0 (ratio_nonneg _ _))
      _ ≤ ∫⁻ ξ', ENNReal.ofReal (twoProbeRatio N (ωr ξ) (ωl ξ')) ∂μl := by
          refine lintegral_mono fun ξ' => ENNReal.ofReal_le_ofReal ?_
          have := twoProbeRatio_ge N (ωr ξ) (ωl ξ')
          rw [hc, inv_mul_eq_div]
          exact this
  -- outer integral
  have hr0 : ∀ ξ, 0 ≤ r ξ := fun ξ =>
    div_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _)
  have hrbd : ∀ ξ, r ξ ≤ s ^ 2 := fun ξ => by
    refine div_le_of_le_mul₀ (dotProduct_self_nonneg _) (sq_nonneg _) ?_
    exact dotProduct_mulVec_le_specNorm N _
  have hintr : Integrable r μr := hr.integrable_mulVec_sq N
  have hint2 : Integrable (fun ξ => r ξ ^ 2 / (M * s ^ 2)) μr := by
    refine Integrable.div_const ?_ _
    refine Integrable.of_bound (hintr.aestronglyMeasurable.pow 2) ((s ^ 2) ^ 2)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hr0 ξ) (hrbd ξ) 2
  calc ENNReal.ofReal ((‖N‖ ^ 2 / Fintype.card n) ^ 2 / (M * s ^ 2))
      ≤ ENNReal.ofReal (∫ ξ, r ξ ^ 2 / (M * s ^ 2) ∂μr) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div]
        exact div_le_div_of_nonneg_right (sq_integral_ratio_le hr N) (by positivity)
    _ = ∫⁻ ξ, ENNReal.ofReal (r ξ ^ 2 / (M * s ^ 2)) ∂μr :=
        ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall fun ξ => by
          positivity)
    _ ≤ ∫⁻ ξ, ∫⁻ ξ', ENNReal.ofReal (twoProbeRatio N (ωr ξ) (ωl ξ')) ∂μl ∂μr :=
        lintegral_mono hinner

end Parallel

section ParallelConcrete

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The columns of the parallel right basis, `[V, Gᵀ U, Gᵀ ωₗ]`. -/
noncomputable abbrev parK (G W : Matrix m n ℝ) (ωl : m → ℝ) :
    Matrix n ((Fin W.rank ⊕ Fin W.rank) ⊕ Unit) ℝ :=
  Matrix.fromCols (Matrix.fromCols (thinV W) (Gᵀ * thinU W)) (Matrix.replicateCol Unit (Gᵀ *ᵥ ωl))

/-- The parallel right basis `V̂ = orth[V, Gᵀ U, Gᵀ ωₗ]`. -/
noncomputable abbrev parV (G W : Matrix m n ℝ) (ωl : m → ℝ) :
    Matrix n (Fin (parK G W ωl).rank) ℝ := orth (parK G W ωl)

/-- The parallel (GeoLoRA ordering) step before truncation:
`Ŵ = Û Ûᵀ (W − λ G) V̂ V̂ᵀ`, `Û = orth[U, G V, G ωᵣ]`, `V̂ = orth[V, Gᵀ U, Gᵀ ωₗ]`. -/
noncomputable def parPre (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ωr : n → ℝ) (ωl : m → ℝ)
    (W : Matrix m n ℝ) : Matrix m n ℝ :=
  augStep (probeU (g W) W ωr) (parV (g W) W ωl) W (g W) lr

/-- The parallel Galerkin projector. -/
noncomputable def parProj (G W : Matrix m n ℝ) (ωr : n → ℝ) (ωl : m → ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  leftProj (probeU G W ωr) * rightProj (parV G W ωl)

theorem parV_capture (G W : Matrix m n ℝ) (ωl : m → ℝ) :
    parV G W ωl * (parV G W ωl)ᵀ * thinV W = thinV W ∧
      parV G W ωl * (parV G W ωl)ᵀ * (Gᵀ * thinU W) = Gᵀ * thinU W ∧
      (parV G W ωl * (parV G W ωl)ᵀ) *ᵥ (Gᵀ *ᵥ ωl) = Gᵀ *ᵥ ωl := by
  have h := capture_fromCols (thinU_capture (parK G W ωl))
  have h' := capture_fromCols h.1
  exact ⟨h'.1, h'.2, mulVec_of_mul_replicateCol h.2⟩

theorem isOrthProj_parProj (G W : Matrix m n ℝ) (ωr : n → ℝ) (ωl : m → ℝ) :
    IsOrthProj (parProj G W ωr ωl) :=
  isOrthProj_leftProj_mul_rightProj (thinU_orthonormal _) (thinU_orthonormal _)

theorem parPre_eq_projGradStep (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ωr : n → ℝ)
    (ωl : m → ℝ) (W : Matrix m n ℝ) :
    parPre g lr ωr ωl W = projGradStep (parProj (g W) W ωr ωl) g lr W := by
  have h := augStep_eq_projGradStep (probeU_capture (g W) W ωr).1 (parV_capture (g W) W ωl).1
    (Matrix.diagonal (thinσ W)) g lr
  rw [← thin_eq] at h
  exact h

/-- Both parallel bases have at most `2 r + 1` columns, and so has the rank of `Ŵ`. -/
theorem rank_parK_le (G W : Matrix m n ℝ) (ωl : m → ℝ) :
    (parK G W ωl).rank ≤ 2 * W.rank + 1 := by
  refine (Matrix.rank_le_card_width _).trans (le_of_eq ?_)
  simp [Fintype.card_sum]
  ring

/-- The parallel step has rank at most `2 r + 1` before truncation. -/
theorem rank_parPre_le (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ωr : n → ℝ) (ωl : m → ℝ)
    (W : Matrix m n ℝ) : (parPre g lr ωr ωl W).rank ≤ 2 * W.rank + 1 := by
  refine le_trans ?_ (rank_probeK_le (g W) W ωr)
  have e : parPre g lr ωr ωl W = probeU (g W) W ωr * ((probeU (g W) W ωr)ᵀ * (W - lr • g W) *
      (parV (g W) W ωl * (parV (g W) W ωl)ᵀ)) := by
    simp only [parPre, augStep, Matrix.mul_assoc]
  rw [e]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (le_of_eq ?_))
  simp

/-- The deterministic inequality for the concrete parallel bases. -/
theorem par_capture_ge [DecidableEq m] (G W : Matrix m n ℝ) (ωr : n → ℝ) (ωl : m → ℝ) :
    ‖tangentProj (thinU W) (thinV W) G‖ ^ 2 +
        twoProbeRatio (normalBlock (thinU W) (thinV W) G) ωr ωl ≤
      ‖parProj G W ωr ωl G‖ ^ 2 := by
  have e : ‖parProj G W ωr ωl G‖ = ‖(probeU G W ωr)ᵀ * G * parV G W ωl‖ :=
    norm_galerkin_apply (thinU_orthonormal _) (thinU_orthonormal _) G
  rw [e]
  obtain ⟨h1, h2, h3⟩ := probeU_capture G W ωr
  obtain ⟨h4, h5, h6⟩ := parV_capture G W ωl
  exact norm_sq_galerkin_ge_of_two_probes (thinU_orthonormal W) (thinV_orthonormal W)
    (thinU_orthonormal _) (thinU_orthonormal _) h1 h2 h3 h4 h5 h6

omit [DecidableEq n] in
lemma twoProbeRatio_nonneg (N : Matrix m n ℝ) (ωr : n → ℝ) (ωl : m → ℝ) :
    0 ≤ twoProbeRatio N ωr ωl :=
  div_nonneg (sq_nonneg _) (mul_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _))

omit [DecidableEq n] in
/-- The pair ratio is symmetric under transposition. -/
lemma twoProbeRatio_transpose (N : Matrix m n ℝ) (ωr : n → ℝ) (ωl : m → ℝ) :
    twoProbeRatio Nᵀ ωl ωr = twoProbeRatio N ωr ωl := by
  have hadj : ∀ (a : m → ℝ) (b : n → ℝ), a ⬝ᵥ (N *ᵥ b) = (Nᵀ *ᵥ a) ⬝ᵥ b := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have e : (Nᵀ *ᵥ ωl) ⬝ᵥ (Nᵀ *ᵥ (Nᵀᵀ *ᵥ ωr)) = (N *ᵥ ωr) ⬝ᵥ (N *ᵥ (Nᵀ *ᵥ ωl)) := by
    rw [Matrix.transpose_transpose, hadj (N *ᵥ ωr), dotProduct_comm]
  rw [twoProbeRatio, twoProbeRatio, e, Matrix.transpose_transpose, mul_comm]

lemma norm_sq_le_of_specNorm (N : Matrix m n ℝ) (hs : Curvature.specNorm N = 0) :
    ‖N‖ ^ 2 = 0 := by
  have h := Curvature.frob_mul_le N (1 : Matrix n n ℝ)
  rw [hs, zero_mul, Matrix.mul_one] at h
  rw [le_antisymm h (norm_nonneg _)]
  simp

variable {Ξr Ξl : Type*} [MeasurableSpace Ξr] [MeasurableSpace Ξl] {μr : Measure Ξr}
  {μl : Measure Ξl} [IsProbabilityMeasure μr] [IsProbabilityMeasure μl] {ωr : Ξr → n → ℝ}
  {ωl : Ξl → m → ℝ}

/-- The worst-case constant of `lintegral_twoProbeRatio_ge`. -/
lemma le_of_specNorm_bound [Nonempty m] [Nonempty n] (N : Matrix m n ℝ) :
    ‖N‖ ^ 2 / (Fintype.card m * Fintype.card n ^ 2) ≤
      (‖N‖ ^ 2 / Fintype.card n) ^ 2 / (Fintype.card m * Curvature.specNorm N ^ 2) := by
  set s := Curvature.specNorm N with hs
  have hM : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  rcases (Curvature.specNorm_nonneg N).eq_or_lt with h0 | h0
  · have := norm_sq_le_of_specNorm N h0.symm
    simp [this]
  have hsF : s ^ 2 ≤ ‖N‖ ^ 2 := pow_le_pow_left₀ h0.le (Curvature.specNorm_le_frob N) 2
  rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hN : 0 ≤ ‖N‖ ^ 2 := sq_nonneg _
  have : ‖N‖ ^ 2 * (Fintype.card n ^ 2 * (Fintype.card m * s ^ 2)) ≤
      ‖N‖ ^ 2 * (Fintype.card n ^ 2 * (Fintype.card m * ‖N‖ ^ 2)) := by
    gcongr
  nlinarith [this]

/-- The expected-capture bound for the pair of probes, for any dominated capture . -/
theorem lintegral_pair_ge [Nonempty m] [Nonempty n] (hr : IsIsotropicLaw μr ωr)
    (hl : IsIsotropicLaw μl ωl) (N : Matrix m n ℝ) {t : ℝ} (ht0 : 0 ≤ t) {C : Ξr × Ξl → ℝ}
    (hC : ∀ ξ, t + twoProbeRatio N (ωr ξ.1) (ωl ξ.2) ≤ C ξ) :
    ENNReal.ofReal (t + (‖N‖ ^ 2 / Fintype.card n) ^ 2 /
        (Fintype.card m * Curvature.specNorm N ^ 2)) ≤ ∫⁻ ξ, ENNReal.ofReal (C ξ) ∂μr.prod μl ∧
      ENNReal.ofReal (t + (‖N‖ ^ 2 / Fintype.card m) ^ 2 /
        (Fintype.card n * Curvature.specNorm N ^ 2)) ≤ ∫⁻ ξ, ENNReal.ofReal (C ξ) ∂μr.prod μl := by
  classical
  have hm : Measurable fun ξ : Ξr × Ξl => twoProbeRatio N (ωr ξ.1) (ωl ξ.2) :=
    measurable_twoProbeRatio N (hr.measurable.comp measurable_fst)
      (hl.measurable.comp measurable_snd)
  have hlow : ENNReal.ofReal t +
      ∫⁻ ξ, ENNReal.ofReal (twoProbeRatio N (ωr ξ.1) (ωl ξ.2)) ∂μr.prod μl ≤
        ∫⁻ ξ, ENNReal.ofReal (C ξ) ∂μr.prod μl := by
    have hc : ∫⁻ _ξ : Ξr × Ξl, ENNReal.ofReal t ∂μr.prod μl = ENNReal.ofReal t := by
      rw [lintegral_const, measure_univ, mul_one]
    nth_rw 1 [← hc]
    rw [← lintegral_add_left measurable_const]
    refine lintegral_mono fun ξ => ?_
    rw [← ENNReal.ofReal_add ht0 (twoProbeRatio_nonneg _ _ _)]
    exact ENNReal.ofReal_le_ofReal (hC ξ)
  have h1 : ENNReal.ofReal ((‖N‖ ^ 2 / Fintype.card n) ^ 2 /
      (Fintype.card m * Curvature.specNorm N ^ 2)) ≤
      ∫⁻ ξ, ENNReal.ofReal (twoProbeRatio N (ωr ξ.1) (ωl ξ.2)) ∂μr.prod μl := by
    rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
    exact lintegral_twoProbeRatio_ge hr hl N
  have h2 : ENNReal.ofReal ((‖N‖ ^ 2 / Fintype.card m) ^ 2 /
      (Fintype.card n * Curvature.specNorm N ^ 2)) ≤
      ∫⁻ ξ, ENNReal.ofReal (twoProbeRatio N (ωr ξ.1) (ωl ξ.2)) ∂μr.prod μl := by
    rw [lintegral_prod_symm _ hm.ennreal_ofReal.aemeasurable]
    have h := lintegral_twoProbeRatio_ge hl hr Nᵀ
    rw [Frobenius.norm_transpose, Curvature.specNorm_transpose] at h
    simpa only [twoProbeRatio_transpose] using h
  constructor
  · rw [ENNReal.ofReal_add ht0 (by positivity)]
    exact (add_le_add_right h1 _).trans hlow
  · rw [ENNReal.ofReal_add ht0 (by positivity)]
    exact (add_le_add_right h2 _).trans hlow

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- The numerics of the worst-case parallel constant. -/
lemma parallel_constant {M n t F A B : ℝ} (hM : 1 ≤ M) (hn : 1 ≤ n) (ht : 0 ≤ t)
    (hA : F / (M * n ^ 2) ≤ A) (hB : F / (n * M ^ 2) ≤ B) :
    (1 / (M * n * min M n)) * (t + F) ≤ t + A ∨ (1 / (M * n * min M n)) * (t + F) ≤ t + B := by
  have hM0 : 0 < M := by linarith
  have hn0 : 0 < n := by linarith
  rcases le_total M n with h | h
  · right
    have hd : min M n = M := min_eq_left h
    rw [hd]
    have h1 : 1 ≤ M * n * M := by nlinarith [mul_pos hM0 hn0]
    have h2 : (1 / (M * n * M)) * t ≤ t := by
      refine mul_le_of_le_one_left ht ?_
      rw [div_le_one (by positivity)]
      exact h1
    have h3 : (1 / (M * n * M)) * F = F / (n * M ^ 2) := by
      field_simp
    rw [mul_add, h3]
    linarith
  · left
    have hd : min M n = n := min_eq_right h
    rw [hd]
    have h1 : 1 ≤ M * n * n := by nlinarith [mul_pos hM0 hn0]
    have h2 : (1 / (M * n * n)) * t ≤ t := by
      refine mul_le_of_le_one_left ht ?_
      rw [div_le_one (by positivity)]
      exact h1
    have h3 : (1 / (M * n * n)) * F = F / (M * n ^ 2) := by
      field_simp
    rw [mul_add, h3]
    linarith

/-- **Item 5: expected capture of the concrete parallel ordering.**  With
independent isotropic probes `ξ = (ξᵣ, ξₗ) ∼ μᵣ ⊗ μₗ`,
`E ‖Π̂ G‖² ≥ ‖P(W) G‖² + ‖N‖_F⁴ / (m n² ‖N‖₂²)`, the same with `m`, `n` exchanged, and so
`E ‖Π̂ G‖² ≥ ‖G‖²_F / (m n min(m, n))`. The sequential constant is `1/n`. It is not sharp: numerics
suggest `‖N‖²_F / (m n)` in general and `‖N‖²_F / min(m, n)²` for Gaussian probes. -/
theorem lintegral_parProj_ge [Nonempty m] [Nonempty n]
    (hr : IsIsotropicLaw μr ωr) (hl : IsIsotropicLaw μl ωl) (G W : Matrix m n ℝ) :
    ENNReal.ofReal ((1 / (Fintype.card m * Fintype.card n *
        min (Fintype.card m : ℝ) (Fintype.card n))) * ‖G‖ ^ 2) ≤
      ∫⁻ ξ, ENNReal.ofReal (‖parProj G W (ωr ξ.1) (ωl ξ.2) G‖ ^ 2) ∂μr.prod μl := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, N = normalBlock (thinU W) (thinV W) G := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = ‖tangentProj (thinU W) (thinV W) G‖ ^ 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hpyth : ‖G‖ ^ 2 = t + ‖N‖ ^ 2 := by
    rw [ht, hN]
    exact (norm_sq_tangentProj_add_normal (thinU_orthonormal W) (thinV_orthonormal W) G).symm
  have hcap := lintegral_pair_ge hr hl N ht0
    (C := fun ξ => ‖parProj G W (ωr ξ.1) (ωl ξ.2) G‖ ^ 2) (fun ξ => by
      rw [ht, hN]
      exact par_capture_ge G W _ _)
  have hM : (1 : ℝ) ≤ Fintype.card m := by exact_mod_cast Fintype.card_pos
  have hn : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hA := le_of_specNorm_bound N
  have hB := le_of_specNorm_bound Nᵀ
  rw [Frobenius.norm_transpose, Curvature.specNorm_transpose] at hB
  rw [hpyth]
  rcases parallel_constant hM hn ht0 hA hB with h | h
  · exact (ENNReal.ofReal_le_ofReal h).trans hcap.1
  · exact (ENNReal.ofReal_le_ofReal h).trans hcap.2

/-- The concrete parallel iteration along a pair-probe path. -/
noncomputable def parIter (T : Matrix m n ℝ → Matrix m n ℝ) (g : Matrix m n ℝ → Matrix m n ℝ)
    (lr : ℝ) (ωr : Ξr → n → ℝ) (ωl : Ξl → m → ℝ) (W₀ : Matrix m n ℝ) :
    (k : ℕ) → (Fin k → Ξr × Ξl) → Matrix m n ℝ :=
  pathIter (fun ξ W => T (parPre g lr (ωr ξ.1) (ωl ξ.2) W)) W₀

/-- **Item 5: convergence of the parallel ordering.**  The concrete GeoLoRA-ordered method with one
right and one left probe satisfies the bound of `exists_iterE_grad_sq_le_probeIter` with `n`
replaced by the weaker constant `m n min(m, n)`. -/
theorem exists_iterE_grad_sq_le_parIter [Nonempty m] [Nonempty n] [Nonempty Ξr] [Nonempty Ξl]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hr : IsIsotropicLaw μr ωr) (hl : IsIsotropicLaw μl ωl) {T : Matrix m n ℝ → Matrix m n ℝ}
    {ϑ : ℝ} (hT : ∀ X, ‖T X - X‖ ≤ ϑ) (W₀ : Matrix m n ℝ) {lr B ℒinf : ℝ} {K : ℕ}
    (hB : ∀ k < K, ∀ ω' (ξ : Ξr × Ξl), ∀ w ∈ segment ℝ
      (parPre g lr (ωr ξ.1) (ωl ξ.2) (parIter T g lr ωr ωl W₀ k ω'))
      (T (parPre g lr (ωr ξ.1) (ωl ξ.2) (parIter T g lr ωr ωl W₀ k ω'))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) (hK : 0 < K) :
    ∃ k < K, iterE (μr.prod μl) k
        (fun ω' => ENNReal.ofReal (‖g (parIter T g lr ωr ωl W₀ k ω')‖ ^ 2)) ≤
      ENNReal.ofReal ((Fintype.card m * Fintype.card n *
          min (Fintype.card m : ℝ) (Fintype.card n)) *
        ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) + B * ϑ / (lr * (1 - β * lr / 2)))) := by
  classical
  set x := parIter T g lr ωr ωl W₀ with hx
  have hsucc : ∀ k (ω' : Fin k → Ξr × Ξl) (ξ : Ξr × Ξl), x (k + 1) (Fin.snoc ω' ξ) =
      T (projGradStep (parProj (g (x k ω')) (x k ω') (ωr ξ.1) (ωl ξ.2)) g lr (x k ω')) :=
    fun k ω' ξ => by
      rw [← parPre_eq_projGradStep]
      exact pathIter_snoc _ _ _ _ _
  have hM : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hγ0 : (0 : ℝ) < 1 / (Fintype.card m * Fintype.card n *
      min (Fintype.card m : ℝ) (Fintype.card n)) := by
    have : 0 < min (Fintype.card m : ℝ) (Fintype.card n) := lt_min hM hn
    positivity
  obtain ⟨k, hk, hle⟩ := exists_iterE_grad_sq_le (μ := μr.prod μl) (x := x) hℒ hg
    (P := fun k ω' ξ => parProj (g (x k ω')) (x k ω') (ωr ξ.1) (ωl ξ.2))
    (fun k ω' ξ => isOrthProj_parProj _ _ _ _) (ϑ := ϑ) (B := B) (h := lr) (ℒinf := ℒinf)
    (fun k ω' ξ => by rw [hsucc]; exact hT _)
    (fun k hk ω' ξ w hw => by
      rw [hsucc, ← parPre_eq_projGradStep] at hw
      exact hB k hk ω' ξ w hw)
    (fun k ω' => hinf _) hγ0
    (fun k ω' => lintegral_parProj_ge hr hl (g (x k ω')) (x k ω')) hh hK
  refine ⟨k, hk, hle.trans (le_of_eq ?_)⟩
  have hx0 : x 0 (fun i => i.elim0) = W₀ := rfl
  rw [hx0, div_div_eq_mul_div, div_one, mul_comm]

end ParallelConcrete

/-! ### Measurability: the iterates are Borel functions of the probes -/

section MatrixMeasurable

variable {α : Type*} [MeasurableSpace α] {m n k : Type*}

lemma measurable_mat_mul [Fintype n] {A : α → Matrix m n ℝ} {B : α → Matrix n k ℝ}
    (hA : Measurable A) (hB : Measurable B) : Measurable fun x => A x * B x :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun l _ => hA.eval_matrix.mul hB.eval_matrix

lemma measurable_mat_transpose {A : α → Matrix m n ℝ} (hA : Measurable A) :
    Measurable fun x => (A x)ᵀ :=
  Measurable.of_eval_matrix _ fun _ _ => hA.eval_matrix

lemma measurable_mat_sub {A B : α → Matrix m n ℝ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x - B x :=
  Measurable.of_eval_matrix _ fun _ _ => hA.eval_matrix.sub hB.eval_matrix

lemma measurable_mat_add {A B : α → Matrix m n ℝ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x + B x :=
  Measurable.of_eval_matrix _ fun _ _ => hA.eval_matrix.add hB.eval_matrix

lemma measurable_mat_const_smul (c : ℝ) {A : α → Matrix m n ℝ} (hA : Measurable A) :
    Measurable fun x => c • A x :=
  Measurable.of_eval_matrix _ fun _ _ => hA.eval_matrix.const_mul c

lemma measurable_mat_fromCols {n' : Type*} {A : α → Matrix m n ℝ} {B : α → Matrix m n' ℝ}
    (hA : Measurable A) (hB : Measurable B) : Measurable fun x => Matrix.fromCols (A x) (B x) :=
  Measurable.of_eval_matrix _ fun _ j => by
    rcases j with j | j
    · exact hA.eval_matrix
    · exact hB.eval_matrix

lemma measurable_mat_replicateCol {y : α → m → ℝ} (hy : Measurable y) :
    Measurable fun x => Matrix.replicateCol Unit (y x) :=
  Measurable.of_eval_matrix _ fun i _ => measurable_pi_iff.1 hy i

lemma measurable_mat_mulVec [Fintype n] {A : α → Matrix m n ℝ} {y : α → n → ℝ}
    (hA : Measurable A) (hy : Measurable y) : Measurable fun x => A x *ᵥ y x :=
  measurable_pi_iff.2 fun _ => Finset.measurable_sum _ fun j _ =>
    hA.eval_matrix.mul (measurable_pi_iff.1 hy j)

lemma measurable_det [Fintype n] [DecidableEq n] {A : α → Matrix n n ℝ} (hA : Measurable A) :
    Measurable fun x => (A x).det := by
  simp only [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ => (Finset.measurable_prod _ fun i _ =>
    hA.eval_matrix).const_mul _

lemma measurable_adjugate [Fintype n] [DecidableEq n] {A : α → Matrix n n ℝ}
    (hA : Measurable A) : Measurable fun x => (A x).adjugate :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.adjugate_apply]
    refine measurable_det (Measurable.of_eval_matrix _ fun a b => ?_)
    by_cases h : a = j
    · simp [Matrix.updateRow_apply, h]
    · simpa [Matrix.updateRow_apply, h] using hA.eval_matrix

lemma measurable_mat_inv [Fintype n] [DecidableEq n] {A : α → Matrix n n ℝ}
    (hA : Measurable A) : Measurable fun x => (A x)⁻¹ := by
  have h : (fun x => (A x)⁻¹) = fun x => ((A x).det)⁻¹ • (A x).adjugate := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact Measurable.of_eval_matrix _ fun i j =>
    (measurable_det hA).inv.mul (measurable_adjugate hA).eval_matrix

end MatrixMeasurable

section ColProj

variable {m j j' : Type*} [Fintype m] [Fintype j] [Fintype j'] [DecidableEq j] [DecidableEq j']

/-- **Bridge.** The orthogonal projector `orth K (orth K)ᵀ` onto the column space of `K` is the
core column-space projector `Matrix.rangeProj K = K K⁺` (the local `colProj` of an earlier
version of this file was this matrix, unification batch C2). It does not depend on the chosen basis
(`colProj_eq_of_capture`). -/
theorem rangeProj_eq_orth_mul_transpose (K : Matrix m j ℝ) :
    K.rangeProj = orth K * (orth K)ᵀ := by
  obtain ⟨B, hB⟩ := exists_orth_eq K
  exact Matrix.rangeProj_eq_of_capture (thinU_capture K) hB

omit [Fintype j'] [DecidableEq j] [DecidableEq j'] in
/-- The column-space projector is symmetric (the core `Matrix.transpose_rangeProj`). -/
lemma colProj_transpose (K : Matrix m j ℝ) : (rangeProj K)ᵀ = rangeProj K :=
  Matrix.transpose_rangeProj K

omit [Fintype j'] [DecidableEq j] [DecidableEq j'] in
/-- The column-space projector fixes the columns of `K` (the core `Matrix.rangeProj_mul_self`). -/
lemma colProj_mul_self (K : Matrix m j ℝ) : rangeProj K * K = K :=
  Matrix.rangeProj_mul_self K

omit [Fintype j'] [DecidableEq j] [DecidableEq j'] in
/-- A matrix fixing all columns of `K` fixes the projector onto its column space. -/
lemma mul_colProj_of_capture {P : Matrix m m ℝ} {K : Matrix m j ℝ} (h : P * K = K) :
    P * rangeProj K = rangeProj K := by
  classical
  obtain ⟨B, hB⟩ := exists_orth_eq K
  have h1 : P * orth K = orth K := by rw [hB, ← Matrix.mul_assoc, h]
  rw [rangeProj_eq_orth_mul_transpose, ← Matrix.mul_assoc, h1]

omit [DecidableEq j] [DecidableEq j'] in
/-- The projector depends only on the column space. -/
theorem colProj_eq_of_capture {K : Matrix m j ℝ} {K' : Matrix m j' ℝ}
    (h : rangeProj K * K' = K') (h' : rangeProj K' * K = K) : rangeProj K = rangeProj K' := by
  have h1 : rangeProj K * rangeProj K' = rangeProj K' := mul_colProj_of_capture h
  have h2 : rangeProj K' * rangeProj K = rangeProj K := mul_colProj_of_capture h'
  have h3 := congrArg Matrix.transpose h2
  rw [Matrix.transpose_mul, colProj_transpose, colProj_transpose] at h3
  rw [← h3, h1]

/-- The Tikhonov regularised projector. -/
noncomputable def tikProj (ε : ℝ) (K : Matrix m j ℝ) : Matrix m m ℝ :=
  K * (Kᵀ * K + ε • (1 : Matrix j j ℝ))⁻¹ * Kᵀ

lemma isUnit_gram_add {ε : ℝ} (hε : 0 < ε) (K : Matrix m j ℝ) :
    IsUnit (Kᵀ * K + ε • (1 : Matrix j j ℝ)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : (Kᵀ * K + ε • (1 : Matrix j j ℝ)) *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub, sub_eq_zero]
    exact hab
  set x := a - b with hx
  have h1 : x ⬝ᵥ ((Kᵀ * K + ε • (1 : Matrix j j ℝ)) *ᵥ x) =
      (K *ᵥ x) ⬝ᵥ (K *ᵥ x) + ε * (x ⬝ᵥ x) := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_transpose]
  rw [h0, dotProduct_zero] at h1
  have h2 : 0 ≤ (K *ᵥ x) ⬝ᵥ (K *ᵥ x) := dotProduct_self_nonneg _
  have h3 : 0 ≤ x ⬝ᵥ x := dotProduct_self_nonneg _
  have h4 : x ⬝ᵥ x = 0 := by
    have : ε * (x ⬝ᵥ x) = 0 := by linarith [mul_nonneg hε.le h3]
    exact (mul_eq_zero.1 this).resolve_left hε.ne'
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h4)

/-- The explicit form of the regularised projector. -/
theorem tikProj_eq {ε : ℝ} (hε : 0 < ε) (K : Matrix m j ℝ) :
    tikProj ε K = orth K * Matrix.diagonal (fun i => thinσ K i ^ 2 / (thinσ K i ^ 2 + ε)) *
      (orth K)ᵀ := by
  set U := thinU K with hU
  set V := thinV K with hV
  set σ := thinσ K with hσ
  set D := Matrix.diagonal σ with hD
  set E := Matrix.diagonal (fun i => σ i / (σ i ^ 2 + ε)) with hE
  set M := Kᵀ * K + ε • (1 : Matrix j j ℝ) with hM
  have hUU : Uᵀ * U = 1 := thinU_orthonormal K
  have hVV : Vᵀ * V = 1 := thinV_orthonormal K
  have hK : K = U * D * Vᵀ := thin_eq K
  have hKt : Kᵀ = V * D * Uᵀ := by
    calc Kᵀ = (U * D * Vᵀ)ᵀ := by rw [← hK]
      _ = V * D * Uᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hD,
          Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hGram : Kᵀ * K = V * (D * D) * Vᵀ := by
    calc Kᵀ * K = (V * D * Uᵀ) * (U * D * Vᵀ) := by rw [← hKt, ← hK]
      _ = V * D * (Uᵀ * U) * D * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = V * (D * D) * Vᵀ := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hdd : (D * D + ε • (1 : Matrix (Fin K.rank) (Fin K.rank) ℝ)) * E = D := by
    have e1 : D * D + ε • (1 : Matrix (Fin K.rank) (Fin K.rank) ℝ) =
        Matrix.diagonal (fun i => σ i ^ 2 + ε) := by
      rw [hD, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal, Matrix.diagonal_add]
      congr 1
      funext i
      ring
    rw [e1, hE, Matrix.diagonal_mul_diagonal, hD]
    congr 1
    funext i
    have : σ i ^ 2 + ε ≠ 0 := by positivity
    field_simp
  have hMY : M * (V * E * Uᵀ) = Kᵀ := by
    have e1 : M * V = V * (D * D + ε • (1 : Matrix (Fin K.rank) (Fin K.rank) ℝ)) := by
      rw [hM, Matrix.add_mul, hGram, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_assoc (V * (D * D)), hVV, Matrix.mul_one, Matrix.mul_add, Matrix.mul_smul,
        Matrix.mul_one]
    calc M * (V * E * Uᵀ) = (M * V) * E * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = V * ((D * D + ε • (1 : Matrix (Fin K.rank) (Fin K.rank) ℝ)) * E) * Uᵀ := by
        rw [e1]; simp only [Matrix.mul_assoc]
      _ = Kᵀ := by rw [hdd, hKt]
  have hinv : M⁻¹ * Kᵀ = V * E * Uᵀ := by
    rw [← hMY, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_gram_add hε K), Matrix.one_mul]
  have hDE : D * E = Matrix.diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + ε)) := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    field_simp
  rw [tikProj, Matrix.mul_assoc, hinv]
  calc K * (V * E * Uᵀ) = (U * D * Vᵀ) * (V * E * Uᵀ) := by rw [← hK]
    _ = U * D * (Vᵀ * V) * E * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * (D * E) * Uᵀ := by rw [hVV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hDE]

/-- The Tikhonov limit: `K (KᵀK + ε)⁻¹ Kᵀ → orth K (orth K)ᵀ` entrywise as `ε ↓ 0`. -/
theorem tendsto_tikProj (K : Matrix m j ℝ) (a b : m) :
    Tendsto (fun t : ℕ => tikProj (1 / ((t : ℝ) + 1)) K a b) atTop (𝓝 (rangeProj K a b)) := by
  have hε : ∀ t : ℕ, (0 : ℝ) < 1 / ((t : ℝ) + 1) := fun t => by positivity
  have hlim : Tendsto (fun t : ℕ => (1 : ℝ) / ((t : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hi : ∀ i, Tendsto (fun t : ℕ => thinσ K i ^ 2 / (thinσ K i ^ 2 + 1 / ((t : ℝ) + 1)))
      atTop (𝓝 1) := fun i => by
    have h0 : thinσ K i ^ 2 ≠ 0 := by have := thinσ_pos K i; positivity
    have h1 : Tendsto (fun t : ℕ => thinσ K i ^ 2 / (thinσ K i ^ 2 + 1 / ((t : ℝ) + 1))) atTop
        (𝓝 (thinσ K i ^ 2 / (thinσ K i ^ 2 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add hlim) (by rwa [add_zero])
    rwa [add_zero, div_self h0] at h1
  have hexp : ∀ t : ℕ, tikProj (1 / ((t : ℝ) + 1)) K a b = ∑ l, orth K a l *
      (thinσ K l ^ 2 / (thinσ K l ^ 2 + 1 / ((t : ℝ) + 1))) * orth K b l := fun t => by
    rw [tikProj_eq (hε t), Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  have hcp : rangeProj K a b = ∑ l, orth K a l * 1 * orth K b l := by
    simp [rangeProj_eq_orth_mul_transpose, Matrix.mul_apply]
  simp_rw [hexp]
  rw [hcp]
  exact tendsto_finsetSum _ fun l _ => ((hi l).const_mul _).mul_const _

omit [Fintype j'] [DecidableEq j] [DecidableEq j'] in
/-- **The column-space projector is a Borel function of the matrix.** -/
theorem measurable_colProj : Measurable (rangeProj (m := m) (k := j)) := by
  classical
  refine Measurable.of_eval_matrix _ fun a b => ?_
  refine measurable_of_tendsto_metrizable
    (f := fun (t : ℕ) (K : Matrix m j ℝ) => tikProj (1 / ((t : ℝ) + 1)) K a b) (fun t => ?_)
    (tendsto_pi_nhds.2 fun K => tendsto_tikProj K a b)
  have hK : Measurable fun K : Matrix m j ℝ => K := measurable_id
  exact (measurable_mat_mul (measurable_mat_mul hK (measurable_mat_inv (measurable_mat_add
    (measurable_mat_mul (measurable_mat_transpose hK) hK) measurable_const)))
    (measurable_mat_transpose hK)).eval_matrix

end ColProj

section MeasurableStep

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

section Capture

omit [DecidableEq n]

variable {k l : Type*} [Fintype k]

lemma mul_mul_of_capture {k' : Type*} {P : Matrix k k ℝ} {A : Matrix k l ℝ} [Fintype l]
    (h : P * A = A) (B : Matrix l k' ℝ) : P * (A * B) = A * B := by
  rw [← Matrix.mul_assoc, h]

end Capture

variable {k : Type*} [Fintype k]

/-- Fixing `A U` is the same as fixing `A W`, for the thin SVD `W = U S Vᵀ`. -/
lemma capture_mul_self {P : Matrix k k ℝ} {A : Matrix k m ℝ} {W : Matrix m n ℝ}
    (h : P * (A * thinU W) = A * thinU W) : P * (A * W) = A * W := by
  have e : A * W = (A * thinU W) * (Matrix.diagonal (thinσ W) * (thinV W)ᵀ) := by
    calc A * W = A * (thinU W * Matrix.diagonal (thinσ W) * (thinV W)ᵀ) := by rw [← thin_eq]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, mul_mul_of_capture h]

lemma capture_mul_thinU {P : Matrix k k ℝ} {A : Matrix k m ℝ} {W : Matrix m n ℝ}
    (h : P * (A * W) = A * W) : P * (A * thinU W) = A * thinU W := by
  have e : A * thinU W =
      (A * W) * (thinV W * Matrix.diagonal fun i => (thinσ W i)⁻¹) := by
    calc A * thinU W = A * (W * thinV W * Matrix.diagonal fun i => (thinσ W i)⁻¹) := by
          rw [mul_thinV]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, mul_mul_of_capture h]

lemma capture_mul_transpose {P : Matrix k k ℝ} {A : Matrix k n ℝ} {W : Matrix m n ℝ}
    (h : P * (A * thinV W) = A * thinV W) : P * (A * Wᵀ) = A * Wᵀ := by
  have e : A * Wᵀ = (A * thinV W) * (Matrix.diagonal (thinσ W) * (thinU W)ᵀ) := by
    calc A * Wᵀ = A * (thinU W * Matrix.diagonal (thinσ W) * (thinV W)ᵀ)ᵀ := by rw [← thin_eq]
      _ = _ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
          Matrix.mul_assoc]
  rw [e, mul_mul_of_capture h]

lemma capture_mul_thinV {P : Matrix k k ℝ} {A : Matrix k n ℝ} {W : Matrix m n ℝ}
    (h : P * (A * Wᵀ) = A * Wᵀ) : P * (A * thinV W) = A * thinV W := by
  have e : A * thinV W =
      (A * Wᵀ) * (thinU W * Matrix.diagonal fun i => (thinσ W i)⁻¹) := by
    calc A * thinV W = A * (Wᵀ * thinU W * Matrix.diagonal fun i => (thinσ W i)⁻¹) := by
          rw [transpose_mul_thinU]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, mul_mul_of_capture h]

variable [DecidableEq m]

omit [DecidableEq m] in
/-- The left projector of the probed step in terms of explicit, measurable data. -/
theorem colProj_probeK (G W : Matrix m n ℝ) (ω : n → ℝ) :
    rangeProj (probeK G W ω) = rangeProj (Matrix.fromCols (Matrix.fromCols W (G * Wᵀ))
      (Matrix.replicateCol Unit (G *ᵥ ω))) := by
  classical
  set K := Matrix.fromCols (Matrix.fromCols W (G * Wᵀ)) (Matrix.replicateCol Unit (G *ᵥ ω))
    with hK
  have h1 := capture_fromCols (colProj_mul_self (probeK G W ω))
  have h1' := capture_fromCols h1.1
  have h2 := capture_fromCols (colProj_mul_self K)
  have h2' := capture_fromCols h2.1
  refine colProj_eq_of_capture ?_ ?_
  · rw [hK, Matrix.mul_fromCols, Matrix.mul_fromCols, h1.2]
    have e1 : rangeProj (probeK G W ω) * W = W := by
      simpa using capture_mul_self (A := (1 : Matrix m m ℝ)) (W := W) (by simpa using h1'.1)
    rw [e1, capture_mul_transpose h1'.2]
  · rw [Matrix.mul_fromCols, Matrix.mul_fromCols, h2.2]
    have e1 : rangeProj K * thinU W = thinU W := by
      simpa using capture_mul_thinU (A := (1 : Matrix m m ℝ)) (W := W) (by simpa using h2'.1)
    rw [e1, capture_mul_thinV h2'.2]

omit [DecidableEq m] in
/-- The right projector of the sequential step in terms of explicit, measurable data. -/
theorem colProj_probeV (G W : Matrix m n ℝ) (ω : n → ℝ) :
    rangeProj (Matrix.fromCols (thinV W) (Gᵀ * probeU G W ω)) =
      rangeProj (Matrix.fromCols Wᵀ (Gᵀ * rangeProj (probeK G W ω))) := by
  classical
  set K := Matrix.fromCols Wᵀ (Gᵀ * rangeProj (probeK G W ω)) with hK
  set K₃ := Matrix.fromCols (thinV W) (Gᵀ * probeU G W ω) with hK₃
  have h1 := capture_fromCols (colProj_mul_self K₃)
  have h2 := capture_fromCols (colProj_mul_self K)
  have hfac : Gᵀ * rangeProj (probeK G W ω) = (Gᵀ * probeU G W ω) * (probeU G W ω)ᵀ := by
    rw [rangeProj_eq_orth_mul_transpose, Matrix.mul_assoc]
  have hfac' : Gᵀ * probeU G W ω = (Gᵀ * rangeProj (probeK G W ω)) * probeU G W ω := by
    rw [hfac, Matrix.mul_assoc, thinU_orthonormal, Matrix.mul_one]
  refine colProj_eq_of_capture ?_ ?_
  · rw [hK, Matrix.mul_fromCols, hfac, mul_mul_of_capture h1.2]
    have e1 : rangeProj K₃ * Wᵀ = Wᵀ := by
      simpa using capture_mul_transpose (A := (1 : Matrix n n ℝ)) (W := W) (by simpa using h1.1)
    rw [e1]
  · rw [hK₃, Matrix.mul_fromCols, hfac', mul_mul_of_capture h2.2]
    have e1 : rangeProj K * thinV W = thinV W := by
      simpa using capture_mul_thinV (A := (1 : Matrix n n ℝ)) (W := W) (by simpa using h2.1)
    rw [e1]

omit [DecidableEq m] in
/-- The right projector of the parallel step in terms of explicit, measurable data. -/
theorem colProj_parK (G W : Matrix m n ℝ) (ωl : m → ℝ) :
    rangeProj (parK G W ωl) = rangeProj (Matrix.fromCols (Matrix.fromCols Wᵀ (Gᵀ * W))
      (Matrix.replicateCol Unit (Gᵀ *ᵥ ωl))) := by
  classical
  set K := Matrix.fromCols (Matrix.fromCols Wᵀ (Gᵀ * W)) (Matrix.replicateCol Unit (Gᵀ *ᵥ ωl))
    with hK
  have h1 := capture_fromCols (colProj_mul_self (parK G W ωl))
  have h1' := capture_fromCols h1.1
  have h2 := capture_fromCols (colProj_mul_self K)
  have h2' := capture_fromCols h2.1
  refine colProj_eq_of_capture ?_ ?_
  · rw [hK, Matrix.mul_fromCols, Matrix.mul_fromCols, h1.2]
    have e1 : rangeProj (parK G W ωl) * Wᵀ = Wᵀ := by
      simpa using capture_mul_transpose (A := (1 : Matrix n n ℝ)) (W := W) (by simpa using h1'.1)
    rw [e1, capture_mul_self h1'.2]
  · rw [Matrix.mul_fromCols, Matrix.mul_fromCols, h2.2]
    have e1 : rangeProj K * thinV W = thinV W := by
      simpa using capture_mul_thinV (A := (1 : Matrix n n ℝ)) (W := W) (by simpa using h2'.1)
    rw [e1, capture_mul_thinU h2'.2]

/-- The left projector of the sequential probed step, from explicit data. -/
noncomputable def probeL (G W : Matrix m n ℝ) (ω : n → ℝ) : Matrix m m ℝ :=
  rangeProj (Matrix.fromCols (Matrix.fromCols W (G * Wᵀ)) (Matrix.replicateCol Unit (G *ᵥ ω)))

/-- The right projector of the sequential probed step, from explicit data. -/
noncomputable def probeR (G W : Matrix m n ℝ) (ω : n → ℝ) : Matrix n n ℝ :=
  rangeProj (Matrix.fromCols Wᵀ (Gᵀ * probeL G W ω))

omit [DecidableEq m] in
/-- The probed projector `Π̂ X = P̂ X Q̂` with the explicit projectors `probeL`, `probeR`. -/
theorem probeProj_eq (G W : Matrix m n ℝ) (ω : n → ℝ) (X : Matrix m n ℝ) :
    probeProj G W ω X = probeL G W ω * X * probeR G W ω := by
  classical
  have e1 : probeL G W ω = probeU G W ω * (probeU G W ω)ᵀ :=
    (colProj_probeK G W ω).symm.trans (rangeProj_eq_orth_mul_transpose _)
  have e2 : probeR G W ω = probeV G W ω * (probeV G W ω)ᵀ := by
    rw [probeR, probeL, ← colProj_probeK]
    exact (colProj_probeV G W ω).symm.trans (rangeProj_eq_orth_mul_transpose _)
  change leftProj (probeU G W ω) (rightProj (probeV G W ω) X) = _
  rw [leftProj_apply, rightProj_apply', e1, e2]
  simp only [Matrix.mul_assoc]

omit [DecidableEq m] in
/-- The probed pre-truncation step `P̂ (W - λ G) Q̂` with the explicit projectors. -/
theorem probePre_eq (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ω : n → ℝ) (W : Matrix m n ℝ) :
    probePre g lr ω W = probeL (g W) W ω * (W - lr • g W) * probeR (g W) W ω := by
  classical
  have e1 : probeL (g W) W ω = probeU (g W) W ω * (probeU (g W) W ω)ᵀ :=
    (colProj_probeK (g W) W ω).symm.trans (rangeProj_eq_orth_mul_transpose _)
  have e2 : probeR (g W) W ω = probeV (g W) W ω * (probeV (g W) W ω)ᵀ := by
    rw [probeR, probeL, ← colProj_probeK]
    exact (colProj_probeV (g W) W ω).symm.trans (rangeProj_eq_orth_mul_transpose _)
  rw [e1, e2]
  rfl

omit [DecidableEq n] [DecidableEq m] in
/-- `probeL` is a Borel function of the data. -/
theorem measurable_probeL {α : Type*} [MeasurableSpace α] {G W : α → Matrix m n ℝ}
    {ω : α → n → ℝ} (hG : Measurable G) (hW : Measurable W) (hω : Measurable ω) :
    Measurable fun x => probeL (G x) (W x) (ω x) :=
  measurable_colProj.comp (measurable_mat_fromCols
    (measurable_mat_fromCols hW (measurable_mat_mul hG (measurable_mat_transpose hW)))
    (measurable_mat_replicateCol (measurable_mat_mulVec hG hω)))

omit [DecidableEq n] [DecidableEq m] in
/-- `probeR` is a Borel function of the data. -/
theorem measurable_probeR {α : Type*} [MeasurableSpace α] {G W : α → Matrix m n ℝ}
    {ω : α → n → ℝ} (hG : Measurable G) (hW : Measurable W) (hω : Measurable ω) :
    Measurable fun x => probeR (G x) (W x) (ω x) :=
  measurable_colProj.comp (measurable_mat_fromCols (measurable_mat_transpose hW)
    (measurable_mat_mul (measurable_mat_transpose hG) (measurable_probeL hG hW hω)))

omit [DecidableEq m] in
set_option linter.unusedDecidableInType false in
/-- **The sequential pre-truncation map is Borel** in the iterate and the probe. -/
theorem measurable_probePre {α : Type*} [MeasurableSpace α] {g : Matrix m n ℝ → Matrix m n ℝ}
    (hg : Measurable g) (lr : ℝ) {W : α → Matrix m n ℝ} {ω : α → n → ℝ} (hW : Measurable W)
    (hω : Measurable ω) : Measurable fun x => probePre g lr (ω x) (W x) := by
  have hG : Measurable fun x => g (W x) := hg.comp hW
  simp only [probePre_eq]
  exact measurable_mat_mul (measurable_mat_mul (measurable_probeL hG hW hω) (measurable_mat_sub hW
    (measurable_mat_const_smul lr hG))) (measurable_probeR hG hW hω)

omit [DecidableEq m] in
set_option linter.unusedDecidableInType false in
/-- **The parallel pre-truncation map is Borel** in the iterate and the probes. -/
theorem measurable_parPre {α : Type*} [MeasurableSpace α] {g : Matrix m n ℝ → Matrix m n ℝ}
    (hg : Measurable g) (lr : ℝ) {W : α → Matrix m n ℝ} {ωr : α → n → ℝ} {ωl : α → m → ℝ}
    (hW : Measurable W) (hr : Measurable ωr) (hl : Measurable ωl) :
    Measurable fun x => parPre g lr (ωr x) (ωl x) (W x) := by
  classical
  have hG : Measurable fun x => g (W x) := hg.comp hW
  have hP : Measurable fun x =>
      rangeProj (Matrix.fromCols (Matrix.fromCols (W x) (g (W x) * (W x)ᵀ))
        (Matrix.replicateCol Unit (g (W x) *ᵥ ωr x))) :=
    measurable_colProj.comp (measurable_mat_fromCols
      (measurable_mat_fromCols hW (measurable_mat_mul hG (measurable_mat_transpose hW)))
      (measurable_mat_replicateCol (measurable_mat_mulVec hG hr)))
  have hQ : Measurable fun x =>
      rangeProj (Matrix.fromCols (Matrix.fromCols (W x)ᵀ ((g (W x))ᵀ * W x))
        (Matrix.replicateCol Unit ((g (W x))ᵀ *ᵥ ωl x))) :=
    measurable_colProj.comp (measurable_mat_fromCols
      (measurable_mat_fromCols (measurable_mat_transpose hW)
        (measurable_mat_mul (measurable_mat_transpose hG) hW))
      (measurable_mat_replicateCol
        (measurable_mat_mulVec (measurable_mat_transpose hG) hl)))
  have e : (fun x => parPre g lr (ωr x) (ωl x) (W x)) = fun x =>
      rangeProj (Matrix.fromCols (Matrix.fromCols (W x) (g (W x) * (W x)ᵀ))
          (Matrix.replicateCol Unit (g (W x) *ᵥ ωr x))) * (W x - lr • g (W x)) *
        rangeProj (Matrix.fromCols (Matrix.fromCols (W x)ᵀ ((g (W x))ᵀ * W x))
          (Matrix.replicateCol Unit ((g (W x))ᵀ *ᵥ ωl x))) := by
    funext x
    rw [← colProj_probeK, ← colProj_parK, rangeProj_eq_orth_mul_transpose,
      rangeProj_eq_orth_mul_transpose]
    rfl
  rw [e]
  exact measurable_mat_mul (measurable_mat_mul hP (measurable_mat_sub hW
    (measurable_mat_const_smul lr hG))) hQ

omit [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m] [Fintype k] in
/-- The iterates of a jointly measurable step are measurable functions of the probe path. -/
theorem measurable_pathIter {Ξ E : Type*} [MeasurableSpace Ξ] [MeasurableSpace E]
    {step : Ξ → E → E} (hstep : Measurable fun p : Ξ × E => step p.1 p.2) (x₀ : E) (K : ℕ) :
    Measurable (pathIter step x₀ K) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    have hinit : Measurable fun ω : Fin (K + 1) → Ξ => (Fin.init ω : Fin K → Ξ) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    exact hstep.comp ((measurable_pi_apply _).prodMk (ih.comp hinit))

omit [DecidableEq n] [DecidableEq m] [Fintype k] in
lemma measurable_norm_sq : Measurable fun X : Matrix m n ℝ => ‖X‖ ^ 2 := by
  simp_rw [Frobenius.norm_sq_eq_sum]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (Matrix.measurable_apply).pow_const 2

omit [DecidableEq n] [DecidableEq m] [Fintype k] in
/-- A Lipschitz gradient is Borel. -/
lemma measurable_of_lipschitz {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) : Measurable g := by
  have hc : Continuous g := by
    have hL : LipschitzWith (Real.toNNReal β) g := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hg x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal β) (norm_nonneg _))
    exact hL.continuous
  have hB : BorelSpace (Matrix m n ℝ) := inferInstanceAs (BorelSpace (m → n → ℝ))
  exact hc.measurable

end MeasurableStep

/-! ### A Borel tolerance truncation exists -/

section Selection

variable {X E : Type*} [MeasurableSpace X] [MetricSpace E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **Measurable selection** (the Kuratowski–Ryll-Nardzewski construction, which Mathlib does not
have yet).  If `S x` is nonempty and closed and `{x | S x meets F}` is measurable for closed `F`,
then `S` has a measurable selection. -/
theorem exists_measurable_selection [Nonempty E] {S : X → Set E} (hne : ∀ x, (S x).Nonempty)
    (hcl : ∀ x, IsClosed (S x))
    (hm : ∀ F : Set E, IsClosed F → MeasurableSet {x | (S x ∩ F).Nonempty}) :
    ∃ f : X → E, Measurable f ∧ ∀ x, f x ∈ S x := by
  classical
  set D := TopologicalSpace.denseSeq E with hD
  have hdense : DenseRange D := TopologicalSpace.denseRange_denseSeq E
  set r : ℕ → ℝ := fun t => (1 / 2) ^ t with hr
  have hr0 : ∀ t, 0 < r t := fun t => by positivity
  have hnear : ∀ (y : E) (ε : ℝ), 0 < ε → ∃ i, y ∈ Metric.closedBall (D i) ε := fun y ε hε => by
    obtain ⟨i, hi⟩ := hdense.exists_dist_lt y hε
    exact ⟨i, Metric.mem_closedBall.2 hi.le⟩
  -- the invariant
  let Q : ℕ → (X → ℕ) → Prop := fun t f =>
    Measurable f ∧ ∀ x, (S x ∩ Metric.closedBall (D (f x)) (r t)).Nonempty
  -- the first approximation
  have hbase : ∃ f, Q 0 f := by
    have hp : ∀ x, ∃ i, (S x ∩ Metric.closedBall (D i) (r 0)).Nonempty := fun x => by
      obtain ⟨y, hy⟩ := hne x
      obtain ⟨i, hi⟩ := hnear y (r 0) (hr0 0)
      exact ⟨i, y, hy, hi⟩
    refine ⟨fun x => Nat.find (hp x), measurable_find hp fun k => ?_, fun x => Nat.find_spec (hp x)⟩
    exact hm _ Metric.isClosed_closedBall
  -- the refinement
  have hstep : ∀ t (f : X → ℕ), Q t f → ∃ f', Q (t + 1) f' ∧
      ∀ x, dist (D (f x)) (D (f' x)) ≤ r t + r (t + 1) := by
    rintro t f ⟨hf, hinv⟩
    have hp : ∀ x, ∃ i, (S x ∩ (Metric.closedBall (D (f x)) (r t) ∩
        Metric.closedBall (D i) (r (t + 1)))).Nonempty := fun x => by
      obtain ⟨y, hy, hy'⟩ := hinv x
      obtain ⟨i, hi⟩ := hnear y (r (t + 1)) (hr0 _)
      exact ⟨i, y, hy, hy', hi⟩
    have hmeas : ∀ k, MeasurableSet {x | (S x ∩ (Metric.closedBall (D (f x)) (r t) ∩
        Metric.closedBall (D k) (r (t + 1)))).Nonempty} := fun k => by
      have e : {x | (S x ∩ (Metric.closedBall (D (f x)) (r t) ∩
          Metric.closedBall (D k) (r (t + 1)))).Nonempty} =
          ⋃ a, (f ⁻¹' {a} ∩ {x | (S x ∩ (Metric.closedBall (D a) (r t) ∩
            Metric.closedBall (D k) (r (t + 1)))).Nonempty}) := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => ⟨f x, rfl, h⟩, fun ⟨a, ha, h⟩ => by subst ha; exact h⟩
      rw [e]
      exact MeasurableSet.iUnion fun a => (hf (measurableSet_singleton a)).inter
        (hm _ (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall))
    refine ⟨fun x => Nat.find (hp x), ⟨measurable_find hp hmeas, fun x => ?_⟩, fun x => ?_⟩
    · obtain ⟨y, hy, -, hy'⟩ := Nat.find_spec (hp x)
      exact ⟨y, hy, hy'⟩
    · obtain ⟨y, -, hy, hy'⟩ := Nat.find_spec (hp x)
      rw [Metric.mem_closedBall] at hy hy'
      calc dist (D (f x)) (D (Nat.find (hp x)))
          ≤ dist (D (f x)) y + dist y (D (Nat.find (hp x))) := dist_triangle _ _ _
        _ ≤ r t + r (t + 1) := by
            rw [dist_comm (D (f x))]
            exact add_le_add hy hy'
  choose f₀ hf₀ using hbase
  choose next hnextQ hnextd using hstep
  let F : (t : ℕ) → {f : X → ℕ // Q t f} := fun t =>
    Nat.rec ⟨f₀, hf₀⟩ (fun t f => ⟨next t f.1 f.2, hnextQ t f.1 f.2⟩) t
  have hFsucc : ∀ t x, dist (D ((F t).1 x)) (D ((F (t + 1)).1 x)) ≤ r t + r (t + 1) :=
    fun t x => hnextd t (F t).1 (F t).2 x
  have hcauchy : ∀ x, CauchySeq fun t => D ((F t).1 x) := fun x => by
    refine cauchySeq_of_le_geometric (1 / 2) (3 / 2) (by norm_num) fun t => ?_
    refine (hFsucc t x).trans (le_of_eq ?_)
    simp only [hr, pow_succ]
    ring
  choose h hlim using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨h, ?_, fun x => ?_⟩
  · refine measurable_of_tendsto_metrizable (f := fun t x => D ((F t).1 x)) (fun t => ?_)
      (tendsto_pi_nhds.2 hlim)
    exact (measurable_from_nat (f := D)).comp (F t).2.1
  · have hy : ∀ t, ∃ y, y ∈ S x ∧ dist y (D ((F t).1 x)) ≤ r t := fun t => by
      obtain ⟨y, hy, hy'⟩ := (F t).2.2 x
      exact ⟨y, hy, hy'⟩
    choose y hyS hyd using hy
    have hr' : Tendsto r atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hyl : Tendsto y atTop (𝓝 (h x)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have h1 : Tendsto (fun t => r t + dist (D ((F t).1 x)) (h x)) atTop (𝓝 0) := by
        simpa using hr'.add (tendsto_iff_dist_tendsto_zero.1 (hlim x))
      refine squeeze_zero (fun _ => dist_nonneg) (fun t => ?_) h1
      exact (dist_triangle _ _ _).trans (add_le_add_left (hyd t) _)
    exact (hcl x).mem_of_tendsto hyl (Filter.Eventually.of_forall hyS)

end Selection

section BorelTruncation

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The set of best approximations of rank at most `r`. -/
def bestSet (r : ℕ) (X : Matrix m n ℝ) : Set (Matrix m n ℝ) :=
  {Y | Y.rank ≤ r ∧ ‖X - Y‖ ≤ distLR r X}

lemma continuous_distLR (r : ℕ) : Continuous (distLR r : Matrix m n ℝ → ℝ) :=
  Metric.continuous_infDist_pt _

lemma isClosed_bestSet (r : ℕ) (X : Matrix m n ℝ) : IsClosed (bestSet r X) := by
  have e : bestSet r X = lowRankSet m n r ∩ {Y | ‖X - Y‖ ≤ distLR r X} := rfl
  rw [e]
  exact (isClosed_lowRankSet r).inter
    (isClosed_le (continuous_const.sub continuous_id).norm continuous_const)

lemma bestSet_nonempty (r : ℕ) (X : Matrix m n ℝ) : (bestSet r X).Nonempty := by
  obtain ⟨Z, hZ, h⟩ := exists_best_approx r X
  exact ⟨Z, hZ, h.le⟩

/-- The set of matrices having a best approximation in a closed set `F` is closed. -/
theorem isClosed_bestSet_meet (r : ℕ) {F : Set (Matrix m n ℝ)} (hF : IsClosed F) :
    IsClosed {X : Matrix m n ℝ | (bestSet r X ∩ F).Nonempty} := by
  have : ProperSpace (Matrix m n ℝ) := FiniteDimensional.proper_real _
  refine IsSeqClosed.isClosed fun X Xlim hX hlim => ?_
  choose Y hY using hX
  have hbdX : Bornology.IsBounded (Set.range X) := Metric.isBounded_range_of_tendsto _ hlim
  obtain ⟨C, hC⟩ := hbdX.exists_norm_le
  have hYbd : ∀ k, Y k ∈ Metric.closedBall (0 : Matrix m n ℝ) (2 * C) := fun k => by
    have h1 : ‖X k‖ ≤ C := hC _ ⟨k, rfl⟩
    have h2 : ‖X k - Y k‖ ≤ distLR r (X k) := (hY k).1.2
    have h3 : distLR r (X k) ≤ ‖X k - 0‖ := distLR_le_norm_sub (by simp [Matrix.rank_zero])
    rw [sub_zero] at h3
    rw [mem_closedBall_zero_iff]
    calc ‖Y k‖ = ‖X k - (X k - Y k)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖X k‖ + ‖X k - Y k‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith
  obtain ⟨a, -, φ, hφ, ha⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hYbd
  have hXφ : Tendsto (X ∘ φ) atTop (𝓝 Xlim) := hlim.comp hφ.tendsto_atTop
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · exact (isClosed_lowRankSet r).mem_of_tendsto ha
      (Filter.Eventually.of_forall fun k => (hY (φ k)).1.1)
  · refine le_of_tendsto_of_tendsto' (hXφ.sub ha).norm
      ((continuous_distLR r).continuousAt.tendsto.comp hXφ) fun k => ?_
    exact (hY (φ k)).1.2
  · exact hF.mem_of_tendsto ha (Filter.Eventually.of_forall fun k => (hY (φ k)).2)

/-- **Borel best approximation of each rank.** -/
theorem exists_measurable_bestApprox (r : ℕ) :
    ∃ s : Matrix m n ℝ → Matrix m n ℝ, Measurable s ∧ ∀ X, s X ∈ bestSet r X := by
  have : BorelSpace (Matrix m n ℝ) := inferInstanceAs (BorelSpace (m → n → ℝ))
  exact exists_measurable_selection (bestSet_nonempty r) (isClosed_bestSet r) fun F hF =>
    (isClosed_bestSet_meet r hF).measurableSet

/-- **A Borel family of tolerance truncations.**  There is a jointly Borel map `(ϑ, X) ↦ T ϑ X`
such that `T ϑ` is a tolerance truncation for every `ϑ ≥ 0`: at each `X` a best approximation of
the tolerance rank, chosen by `exists_measurable_selection`.  This is what the expectation over
Gaussian probe paths needs: `EckartYoung.truncation` goes through a `Classical.choice` eigenbasis
and is not known to be Borel at ties. -/
theorem exists_measurable_toleranceFamily :
    ∃ T : ℝ → Matrix m n ℝ → Matrix m n ℝ, Measurable (Function.uncurry T) ∧
      ∀ ϑ, 0 ≤ ϑ → IsToleranceTruncation (T ϑ) ϑ := by
  have : BorelSpace (Matrix m n ℝ) := inferInstanceAs (BorelSpace (m → n → ℝ))
  choose s hsm hs using fun r : ℕ => exists_measurable_bestApprox (m := m) (n := n) r
  set ρ : ℝ × Matrix m n ℝ → ℕ := fun p => epsRank (max p.1 0) p.2 with hρ
  have hρm : Measurable ρ := by
    refine measurable_of_Iic fun k => ?_
    have e : ρ ⁻¹' Set.Iic k = {p : ℝ × Matrix m n ℝ | distLR k p.2 ≤ max p.1 0} := by
      ext p
      exact epsRank_le_iff (le_max_right _ _)
    rw [e]
    refine (isClosed_le ((continuous_distLR k).comp continuous_snd)
      (continuous_fst.max continuous_const)).measurableSet
  refine ⟨fun ϑ X => s (ρ (ϑ, X)) X, ?_, fun ϑ hϑ => ?_⟩
  · refine fun u hu => ?_
    have e : Function.uncurry (fun ϑ X => s (ρ (ϑ, X)) X) ⁻¹' u =
        ⋃ r, (ρ ⁻¹' {r} ∩ {p | s r p.2 ∈ u}) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff,
        Function.uncurry]
      exact ⟨fun h => ⟨ρ p, rfl, h⟩, fun ⟨r, hr, h⟩ => by rw [hr]; exact h⟩
    rw [e]
    exact MeasurableSet.iUnion fun r => (hρm (measurableSet_singleton r)).inter
      (measurable_snd (hsm r hu) : MeasurableSet {p : ℝ × Matrix m n ℝ | s r p.2 ∈ u})
  · have hmax : max ϑ 0 = ϑ := max_eq_left hϑ
    have hb : ∀ X, (s (epsRank ϑ X) X).rank ≤ epsRank ϑ X ∧
        ‖X - s (epsRank ϑ X) X‖ ≤ distLR (epsRank ϑ X) X := fun X => hs _ X
    have hT : ∀ X, s (ρ (ϑ, X)) X = s (epsRank ϑ X) X := fun X => by
      simp only [hρ, hmax]
    refine ⟨fun X => ?_, fun X Y hY => ?_, fun X Y hY => ?_⟩
    · beta_reduce
      rw [hT, norm_sub_rev]
      exact (hb X).2.trans (distLR_epsRank_le hϑ)
    · beta_reduce
      rw [hT]
      exact (hb X).1.trans (epsRank_le_of_norm_sub_le le_rfl (by rwa [norm_sub_rev]))
    · beta_reduce at hY ⊢
      rw [hT] at hY ⊢
      rw [norm_sub_rev, norm_sub_rev Y]
      exact (hb X).2.trans (distLR_le_norm_sub (hY.trans (hb X).1))

/-- **A Borel tolerance truncation exists** for every `ϑ ≥ 0`. -/
theorem exists_measurable_isToleranceTruncation {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    ∃ T : Matrix m n ℝ → Matrix m n ℝ, Measurable T ∧ IsToleranceTruncation T ϑ := by
  obtain ⟨T, hTm, hT⟩ := exists_measurable_toleranceFamily (m := m) (n := n)
  exact ⟨T ϑ, hTm.comp (measurable_const.prodMk measurable_id), hT ϑ hϑ⟩

end BorelTruncation

/-! ### The statements for the actual probes -/

section Final

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The tail is the Frobenius distance to the low-rank matrices. -/
theorem svTail_eq_distLR (X : Matrix m n ℝ) (r : ℕ) : tailNorm X r = distLR r X :=
  (infDist_setOf_rank_le X r).symm

/-- The truncated SVD at a tolerance never increases the rank. -/
theorem rank_svdTrunc_le {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (X : Matrix m n ℝ) :
    (svdTrunc ϑ X).rank ≤ X.rank := by
  rw [rank_svdTrunc hϑ]
  refine tolRank_le_of_svTail_le ?_
  rw [svTail_eq_zero_of_rank_le le_rfl]
  exact hϑ

/-- **Item 4 for the output of the step.**  The concrete probed step has rank `≤ 2 r + 1` before
and, with the library's truncation, after truncation. -/
theorem rank_probeStep_svdTrunc_le (g : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (ω : n → ℝ)
    {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (W : Matrix m n ℝ) :
    (probeStep (svdTrunc ϑ) g lr ω W).rank ≤ 2 * W.rank + 1 :=
  (rank_svdTrunc_le hϑ _).trans (rank_probePre_le g lr ω W)

/-- **Theorem A for the quadratic loss and the library's truncation.**  For
`L(W) = ½ ‖W − (A + N)‖²`, `N` doubly normal to `A`, and `0 ≤ ϑ` below all nonzero singular values
of `A`, the concrete method started at `A` stays at `A` forever, for every `λ`; the loss gap is
`½ ‖N‖²` and `‖∇L(A)‖ = ‖N‖`.  See `blindSpot_dichotomy` for the geometry of `A`. -/
theorem bugStep_iterate_quadratic {A N : Matrix m n ℝ} (hl : Aᵀ * N = 0) (hr : N * Aᵀ = 0)
    {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ) (hϑ : ∀ i < A.rank, ϑ < (Matrix.toEuclideanLin A).singularValues i)
    (lr : ℝ) (t : ℕ) :
    (bugStep (svdTrunc ϑ) (fun W => W - (A + N)) lr)^[t] A = A ∧
      quadLoss (A + N) A - quadLoss (A + N) (A + N) = ‖N‖ ^ 2 / 2 ∧ ‖A - (A + N)‖ = ‖N‖ := by
  have hg : A - (A + N) = -N := by abel
  have hNtA : Nᵀ * A = 0 := by
    have := congrArg Matrix.transpose hl
    simpa [Matrix.transpose_mul] using this
  have hG : tangentProj (thinU A) (thinV A) (A - (A + N)) = 0 := by
    rw [hg, tangentProj_thin_eq_zero_iff]
    simp [Matrix.neg_mul, hNtA, hr]
  refine ⟨bugStep_iterate_eq_self (g := fun W => W - (A + N)) hG hϑ0 hϑ lr t, ?_, ?_⟩
  · simp [quadLoss, hg]
  · rw [hg, norm_neg]

/-- **Non-vacuity**: a rank-one `A` and a doubly-normal `N` with `‖N‖₂ > σ_min(A)`.  By
`blindSpot_dichotomy` and `bugStep_iterate_quadratic` this `A` is a saddle and an exact fixed point
of the concrete method. -/
theorem exists_blindSpot_saddle :
    ∃ A N : Matrix (Fin 2) (Fin 2) ℝ, 0 < A.rank ∧ Aᵀ * N = 0 ∧ N * Aᵀ = 0 ∧
      (Matrix.toEuclideanLin A).singularValues (A.rank - 1) < Curvature.specNorm N := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0] with hA
  set N : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 2] with hN
  have hA0 : A ≠ 0 := fun h => by
    have := congrFun (congrFun h 0) 0
    simp [hA] at this
  have hrank : 0 < A.rank := Nat.pos_of_ne_zero fun h => hA0 (eq_zero_of_rank_eq_zero h)
  refine ⟨A, N, hrank, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, hN, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, hN, Matrix.mul_apply, Fin.sum_univ_two]
  · have h1 : (Matrix.toEuclideanLin A).singularValues (A.rank - 1) ≤ 1 := by
      have h2 : (Matrix.toEuclideanLin A).singularValues (A.rank - 1) ≤
          (Matrix.toEuclideanLin A).singularValues 0 :=
        (Matrix.toEuclideanLin A).singularValues_antitone (Nat.zero_le _)
      rw [← specNorm_eq_singularValues_zero] at h2
      refine h2.trans ((Curvature.specNorm_le_frob A).trans ?_)
      have h3 : ‖A‖ ^ 2 = 1 := by
        rw [Frobenius.norm_sq_eq_sum]
        simp [hA, Fin.sum_univ_two]
      nlinarith [norm_nonneg A]
    refine h1.trans_lt ?_
    refine (lt_specNorm_iff_exists zero_le_one N).2 ⟨![0, 1], ![0, 1], ?_, ?_, ?_⟩ <;>
      simp [hN, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

omit [DecidableEq n] in
/-- A correlated left probe `ωₗ = N ω`: the capture of the parallel basis is at least the
sequential bound.  This is the parsimonious variant of the sequential step:
`Û = orth[U, G V, G ω]`, `V̂ = orth[V, Gᵀ U, Gᵀ N ω]`, both with at most `2 r + 1` columns (the
K-then-L basis `orth[V, Gᵀ Û]` can have `3 r + 1`), with the constant `1/n` of Theorem B. -/
theorem div_le_twoProbeRatio (N : Matrix m n ℝ) (ω : n → ℝ) :
    (N *ᵥ ω) ⬝ᵥ (N *ᵥ ω) / (ω ⬝ᵥ ω) ≤ twoProbeRatio N ω (N *ᵥ ω) := by
  set u := N *ᵥ ω with hu
  set z := Nᵀ *ᵥ u with hz
  set p := u ⬝ᵥ u with hp
  set q := z ⬝ᵥ z with hq
  set w := ω ⬝ᵥ ω with hw
  have hp0 : 0 ≤ p := dotProduct_self_nonneg _
  have hq0 : 0 ≤ q := dotProduct_self_nonneg _
  have hw0 : 0 ≤ w := dotProduct_self_nonneg _
  have e1 : u ⬝ᵥ (N *ᵥ z) = q := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have e2 : ω ⬝ᵥ z = p := by
    rw [hz, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      dotProduct_comm]
  have hcs : p ^ 2 ≤ w * q := by
    have := sq_dotProduct_le ω z
    rwa [e2] at this
  rw [twoProbeRatio, ← hu, ← hz, e1]
  rcases hw0.eq_or_lt with hw1 | hw1
  · rw [← hw1, div_zero]
    positivity
  rcases hp0.eq_or_lt with hp1 | hp1
  · rw [← hp1, zero_div]
    positivity
  have hq1 : 0 < q := by
    by_contra hcon
    have h0 : q = 0 := le_antisymm (not_lt.1 hcon) hq0
    rw [h0, mul_zero] at hcs
    have : 0 < p ^ 2 := by positivity
    linarith
  rw [div_le_div_iff₀ hw1 (by positivity)]
  have : p * (p * q) ≤ q ^ 2 * w := by nlinarith
  exact this

/-- The capture of the parsimonious variant `V̂ = orth[V, Gᵀ U, Gᵀ N ω]`, with `2 r + 1` columns:
the bound of Theorem B with the sequential constant.  See `div_le_twoProbeRatio`. -/
theorem par_capture_ge_correlated [DecidableEq m] (G W : Matrix m n ℝ) (ω : n → ℝ) :
    ‖tangentProj (thinU W) (thinV W) G‖ ^ 2 +
        (normalBlock (thinU W) (thinV W) G *ᵥ ω) ⬝ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω) /
          (ω ⬝ᵥ ω) ≤
      ‖parProj G W ω (normalBlock (thinU W) (thinV W) G *ᵥ ω) G‖ ^ 2 :=
  (add_le_add_right (div_le_twoProbeRatio _ ω) _).trans (par_capture_ge G W _ _)

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ] {ω : Ξ → n → ℝ}

/-- The concrete iterates of a Borel truncation are Borel functions of the probe path. -/
theorem measurable_probeIter {T : Matrix m n ℝ → Matrix m n ℝ} (hT : Measurable T)
    {g : Matrix m n ℝ → Matrix m n ℝ} (hg : Measurable g) (hω : Measurable ω) (lr : ℝ)
    (W₀ : Matrix m n ℝ) (k : ℕ) : Measurable (probeIter T g lr ω W₀ k) := by
  classical
  refine measurable_pathIter (step := fun ξ W => probeStep T g lr (ω ξ) W) ?_ W₀ k
  exact hT.comp (measurable_probePre hg lr measurable_snd (hω.comp measurable_fst))

/-- **Theorem B for the concrete method, as a genuine expectation.**  With a Borel truncation
(`exists_measurable_isToleranceTruncation`) and any isotropic probe law, the iterates are Borel
functions of the probe path, and under the product law `μ^k`
`min_{k<K} E ‖∇ℒ(W_k)‖² ≤ n [(ℒ(W₀) − ℒ_inf) / (K c) + B ϑ / c]`, `c = λ (1 − βλ/2)`. -/
theorem exists_lintegral_pi_grad_sq_le_probeIter [Nonempty n] [Nonempty Ξ]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hiso : IsIsotropicLaw μ ω) {T : Matrix m n ℝ → Matrix m n ℝ} (hTm : Measurable T) {ϑ : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) (W₀ : Matrix m n ℝ) {lr B ℒinf : ℝ} {K : ℕ}
    (hB : ∀ k < K, ∀ ω' ξ, ∀ w ∈ segment ℝ (probePre g lr (ω ξ) (probeIter T g lr ω W₀ k ω'))
      (T (probePre g lr (ω ξ) (probeIter T g lr ω W₀ k ω'))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) (hK : 0 < K) :
    ∃ k < K, ∫⁻ ω', ENNReal.ofReal (‖g (probeIter T g lr ω W₀ k ω')‖ ^ 2)
        ∂Measure.pi (fun _ : Fin k => μ) ≤
      ENNReal.ofReal (Fintype.card n * ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        B * ϑ / (lr * (1 - β * lr / 2)))) := by
  obtain ⟨k, hk, hle⟩ := exists_iterE_grad_sq_le_probeIter hℒ hg hiso hT W₀ hB hinf hh hK
  refine ⟨k, hk, ?_⟩
  have hgm := measurable_of_lipschitz hg
  have hm : Measurable fun ω' => ENNReal.ofReal (‖g (probeIter T g lr ω W₀ k ω')‖ ^ 2) :=
    (measurable_norm_sq.comp (hgm.comp (measurable_probeIter hTm hgm hiso.measurable lr W₀ k))
      ).ennreal_ofReal
  rw [← iterE_eq_lintegral_pi hm]
  exact hle

/-- **Theorem B with the library's truncation and a discrete probe law.**  For a finitely supported
isotropic probe every function of the path is measurable, so `EckartYoung.truncation` at the
tolerance rank needs no measurable tie-breaking: this is a genuine expectation over the paths. -/
theorem exists_lintegral_pi_grad_sq_le_svdTrunc_finite [Nonempty n] {Ξ' : Type*} [Fintype Ξ']
    [Nonempty Ξ'] [MeasurableSpace Ξ'] [MeasurableSingletonClass Ξ'] {p : Ξ' → ℝ}
    {ω' : Ξ' → n → ℝ} (hiso : IsIsotropicProbe p ω') {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (W₀ : Matrix m n ℝ)
    {lr B ℒinf : ℝ} {K : ℕ}
    (hB : ∀ k < K, ∀ a ξ, ∀ w ∈ segment ℝ
      (probePre g lr (ω' ξ) (probeIter (svdTrunc ϑ) g lr ω' W₀ k a))
      (svdTrunc ϑ (probePre g lr (ω' ξ) (probeIter (svdTrunc ϑ) g lr ω' W₀ k a))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) (hK : 0 < K) :
    ∃ k < K, ∫⁻ a, ENNReal.ofReal (‖g (probeIter (svdTrunc ϑ) g lr ω' W₀ k a)‖ ^ 2)
        ∂Measure.pi (fun _ : Fin k => finiteLaw p) ≤
      ENNReal.ofReal (Fintype.card n * ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        B * ϑ / (lr * (1 - β * lr / 2)))) := by
  have := isProbabilityMeasure_finiteLaw (Ξ := Ξ') hiso.nonneg hiso.sum_eq_one
  obtain ⟨k, hk, hle⟩ := exists_iterE_grad_sq_le_svdTrunc hℒ hg (isIsotropicLaw_ofProbe hiso) hϑ
    W₀ hB hinf hh hK
  refine ⟨k, hk, ?_⟩
  rw [← iterE_eq_lintegral_pi (measurable_of_finite _)]
  exact hle

/-- **The convergence bound with the library's truncation, in the form of the blind-spot module**
(item 1): the statement of `BlindSpot.exists_pathExp_grad_sq_le_probe` for the concrete iterates,
with all bases and the tolerance discharged. -/
theorem exists_pathExp_grad_sq_le_svdTrunc [Nonempty n] {Ξ' : Type*} [Fintype Ξ'] {p : Ξ' → ℝ}
    {ω' : Ξ' → n → ℝ} (hiso : IsIsotropicProbe p ω') {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (W₀ : Matrix m n ℝ)
    {lr B ℒinf : ℝ}
    (hB : ∀ k a ξ, ∀ w ∈ segment ℝ (probePre g lr (ω' ξ)
        (pathIter (fun ξ W => probeStep (svdTrunc ϑ) g lr (ω' ξ) W) W₀ k a))
      (svdTrunc ϑ (probePre g lr (ω' ξ)
        (pathIter (fun ξ W => probeStep (svdTrunc ϑ) g lr (ω' ξ) W) W₀ k a))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) {K : ℕ} (hK : 0 < K) :
    ∃ k < K, pathExp p k (fun a => ‖g (pathIter (fun ξ W => probeStep (svdTrunc ϑ) g lr (ω' ξ) W)
        W₀ k a)‖ ^ 2) ≤
      Fintype.card n * ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        B * ϑ / (lr * (1 - β * lr / 2))) := by
  classical
  set x := pathIter (fun ξ W => probeStep (svdTrunc ϑ) g lr (ω' ξ) W) W₀ with hx
  have hsucc : ∀ k (a : Fin k → Ξ') ξ, x (k + 1) (Fin.snoc a ξ) =
      svdTrunc ϑ (probePre g lr (ω' ξ) (x k a)) := fun k a ξ => pathIter_snoc _ _ _ _ _
  exact exists_pathExp_grad_sq_le_probe (x := x) hℒ hg hiso (r := fun k a => (x k a).rank)
    (U := fun k a => thinU (x k a)) (S := fun k a => Matrix.diagonal (thinσ (x k a)))
    (V := fun k a => thinV (x k a)) (fun _ _ => thinU_orthonormal _)
    (fun _ _ => thinV_orthonormal _) (fun _ _ => thin_eq _)
    (Uh := fun k a ξ => probeU (g (x k a)) (x k a) (ω' ξ))
    (Vh := fun k a ξ => probeV (g (x k a)) (x k a) (ω' ξ))
    (fun _ _ _ => thinU_orthonormal _) (fun _ _ _ => thinU_orthonormal _)
    (fun _ _ _ => (probeU_capture _ _ _).1) (fun _ _ _ => (probeU_capture _ _ _).2.1)
    (fun _ _ _ => (probeU_capture _ _ _).2.2) (fun _ _ _ => (probeV_capture _ _ _).1)
    (fun _ _ _ => (probeV_capture _ _ _).2) (ϑ := ϑ) (B := B) (h := lr) (ℒinf := ℒinf)
    (fun k a ξ => by rw [hsucc]; exact norm_svdTrunc_sub_le hϑ _)
    (fun k a ξ w hw => by
      rw [hsucc] at hw
      exact hB k a ξ w hw)
    (fun _ _ => hinf _) hh hK

/-- The concrete parallel iterates of a Borel truncation are Borel functions of the probe path. -/
theorem measurable_parIter {Ξr Ξl : Type*} [MeasurableSpace Ξr]
    [MeasurableSpace Ξl] {ωr : Ξr → n → ℝ} {ωl : Ξl → m → ℝ} {T : Matrix m n ℝ → Matrix m n ℝ}
    (hT : Measurable T) {g : Matrix m n ℝ → Matrix m n ℝ} (hg : Measurable g)
    (hr : Measurable ωr) (hl : Measurable ωl) (lr : ℝ) (W₀ : Matrix m n ℝ) (k : ℕ) :
    Measurable (parIter T g lr ωr ωl W₀ k) := by
  classical
  have h1 : Measurable fun p : (Ξr × Ξl) × Matrix m n ℝ => p.2 := measurable_snd
  have h2 : Measurable fun p : (Ξr × Ξl) × Matrix m n ℝ => ωr p.1.1 :=
    hr.comp (measurable_fst.comp measurable_fst)
  have h3 : Measurable fun p : (Ξr × Ξl) × Matrix m n ℝ => ωl p.1.2 :=
    hl.comp (measurable_snd.comp measurable_fst)
  have h4 : Measurable fun p : (Ξr × Ξl) × Matrix m n ℝ =>
      parPre g lr (ωr p.1.1) (ωl p.1.2) p.2 := measurable_parPre hg lr h1 h2 h3
  have h5 : Measurable fun p : (Ξr × Ξl) × Matrix m n ℝ =>
      T (parPre g lr (ωr p.1.1) (ωl p.1.2) p.2) := hT.comp h4
  exact measurable_pathIter h5 W₀ k

/-- **The parallel ordering, genuine expectation.**  The bound of
`exists_iterE_grad_sq_le_parIter` under the product of the laws of the pairs of probes, for a Borel
truncation; the Gaussian probes are an instance. -/
theorem exists_lintegral_pi_grad_sq_le_parIter [Nonempty m] [Nonempty n] {Ξr Ξl : Type*}
    [MeasurableSpace Ξr] [MeasurableSpace Ξl] {μr : Measure Ξr} {μl : Measure Ξl}
    [IsProbabilityMeasure μr] [IsProbabilityMeasure μl] [Nonempty Ξr] [Nonempty Ξl]
    {ωr : Ξr → n → ℝ} {ωl : Ξl → m → ℝ} {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hr : IsIsotropicLaw μr ωr)
    (hl : IsIsotropicLaw μl ωl) {T : Matrix m n ℝ → Matrix m n ℝ} (hTm : Measurable T) {ϑ : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) (W₀ : Matrix m n ℝ) {lr B ℒinf : ℝ} {K : ℕ}
    (hB : ∀ k < K, ∀ ω' (ξ : Ξr × Ξl), ∀ w ∈ segment ℝ
      (parPre g lr (ωr ξ.1) (ωl ξ.2) (parIter T g lr ωr ωl W₀ k ω'))
      (T (parPre g lr (ωr ξ.1) (ωl ξ.2) (parIter T g lr ωr ωl W₀ k ω'))), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) (hh : 0 < lr * (1 - β * lr / 2)) (hK : 0 < K) :
    ∃ k < K, ∫⁻ ω', ENNReal.ofReal (‖g (parIter T g lr ωr ωl W₀ k ω')‖ ^ 2)
        ∂Measure.pi (fun _ : Fin k => μr.prod μl) ≤
      ENNReal.ofReal ((Fintype.card m * Fintype.card n *
          min (Fintype.card m : ℝ) (Fintype.card n)) *
        ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) + B * ϑ / (lr * (1 - β * lr / 2)))) := by
  obtain ⟨k, hk, hle⟩ := exists_iterE_grad_sq_le_parIter hℒ hg hr hl hT W₀ hB hinf hh hK
  refine ⟨k, hk, ?_⟩
  have hgm := measurable_of_lipschitz hg
  have hm : Measurable fun ω' => ENNReal.ofReal (‖g (parIter T g lr ωr ωl W₀ k ω')‖ ^ 2) :=
    (measurable_norm_sq.comp (hgm.comp
      (measurable_parIter hTm hgm hr.measurable hl.measurable lr W₀ k))).ennreal_ofReal
  rw [← iterE_eq_lintegral_pi hm]
  exact hle

end Final

/-! ### The gradient bound is a consequence of smoothness -/

section SelfBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ℒ : E → ℝ} {g : E → E}
  {β ℒinf : ℝ}

/-- The self-bounding potential `Φ(x) = (2 β (ℒ(x) − ℒ_inf))^{1/2}`. -/
noncomputable def gradPot (ℒ : E → ℝ) (β ℒinf : ℝ) (x : E) : ℝ := √(2 * β * (ℒ x - ℒinf))

/-- A `β`-smooth function bounded below satisfies `‖∇ℒ(x)‖ ≤ Φ(x)`. -/
theorem norm_grad_le_gradPot (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) (hinf : ∀ x, ℒinf ≤ ℒ x) (x : E) :
    ‖g x‖ ≤ gradPot ℒ β ℒinf x := by
  refine Real.le_sqrt_of_sq_le ?_
  have h1 := descent_lemma hℒ hg x (x - (1 / β) • g x)
  have e1 : x - (1 / β) • g x - x = -((1 / β) • g x) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs] at h1
  have h2 := hinf (x - (1 / β) • g x)
  have h3 : β / 2 * ((1 / β) ^ 2 * ‖g x‖ ^ 2) = (1 / (2 * β)) * ‖g x‖ ^ 2 := by
    field_simp
  have h4 : ‖g x‖ ^ 2 = 2 * β * ((1 / β) * ‖g x‖ ^ 2 - (1 / (2 * β)) * ‖g x‖ ^ 2) := by
    field_simp
    ring
  rw [h4]
  have h5 : 0 ≤ 2 * β := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h5
  linarith

/-- One truncated step raises `Φ` by at most `β ϑ`, and the gradient on the truncation segment is
at most `Φ(x) + β ϑ`. -/
theorem gradPot_step_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) (hinf : ∀ x, ℒinf ≤ ℒ x)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) {h : ℝ} (hh : 0 ≤ h * (1 - β * h / 2)) (x : E) {x₁ : E}
    {ϑ : ℝ} (htr : ‖x₁ - projGradStep P g h x‖ ≤ ϑ) :
    gradPot ℒ β ℒinf x₁ ≤ gradPot ℒ β ℒinf x + β * ϑ ∧
      ∀ w ∈ segment ℝ (projGradStep P g h x) x₁, ‖g w‖ ≤ gradPot ℒ β ℒinf x + β * ϑ := by
  set xh := projGradStep P g h x with hxh
  have hϑ : 0 ≤ ϑ := (norm_nonneg _).trans htr
  have hmono : ℒ xh ≤ ℒ x := loss_projGradStep_le_self hℒ hg hP hh x
  have hpot : gradPot ℒ β ℒinf xh ≤ gradPot ℒ β ℒinf x :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hgxh : ‖g xh‖ ≤ gradPot ℒ β ℒinf x := (norm_grad_le_gradPot hℒ hg hβ hinf xh).trans hpot
  set Φ := gradPot ℒ β ℒinf x with hΦ
  have hΦ0 : 0 ≤ Φ := Real.sqrt_nonneg _
  have hΦsq : Φ ^ 2 = 2 * β * (ℒ x - ℒinf) :=
    Real.sq_sqrt (mul_nonneg (by positivity) (sub_nonneg.2 (hinf x)))
  constructor
  · have h1 := loss_truncated_projGradStep_le' hℒ hg hβ.le hP h x htr
    rw [← hxh] at h1
    have h2 : 0 ≤ h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2 := mul_nonneg hh (sq_nonneg _)
    have h3 : ‖g xh‖ * ϑ ≤ Φ * ϑ := mul_le_mul_of_nonneg_right hgxh hϑ
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h4 : ℒ x₁ - ℒinf ≤ (ℒ x - ℒinf) + Φ * ϑ + β / 2 * ϑ ^ 2 := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 2 * β by positivity)
    calc 2 * β * (ℒ x₁ - ℒinf) ≤ 2 * β * ((ℒ x - ℒinf) + Φ * ϑ + β / 2 * ϑ ^ 2) := h5
      _ = (Φ + β * ϑ) ^ 2 := by rw [add_sq, hΦsq]; ring
  · intro w hw
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
    have e : (a • xh + b • x₁) - xh = b • (x₁ - xh) := by
      have : a = 1 - b := by linarith
      rw [this, sub_smul, one_smul, smul_sub]
      abel
    have h1 : ‖(a • xh + b • x₁) - xh‖ ≤ ϑ := by
      rw [e, norm_smul, Real.norm_of_nonneg hb]
      have hb1 : b ≤ 1 := by linarith
      calc b * ‖x₁ - xh‖ ≤ 1 * ‖x₁ - xh‖ := mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
        _ ≤ ϑ := by rw [one_mul]; exact htr
    have h2 := hg (a • xh + b • x₁) xh
    have h3 : ‖g (a • xh + b • x₁) - g xh‖ ≤ β * ϑ :=
      h2.trans (mul_le_mul_of_nonneg_left h1 hβ.le)
    calc ‖g (a • xh + b • x₁)‖ = ‖g xh + (g (a • xh + b • x₁) - g xh)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖g xh‖ + ‖g (a • xh + b • x₁) - g xh‖ := norm_add_le _ _
      _ ≤ Φ + β * ϑ := add_le_add hgxh h3

end SelfBound

section SmoothConvergence

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ] {ω : Ξ → n → ℝ}

/-- The convergence bound with a capture fraction `γ` and no gradient-bound hypothesis: the constant
`B_K = (2 β (ℒ(W₀) − ℒ_inf))^{1/2} + K β ϑ` is derived from smoothness. -/
theorem exists_iterE_grad_sq_le_of_capture_of_smooth [Nonempty Ξ]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hβ : 0 < β)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hcap : ∀ G W : Matrix m n ℝ, ENNReal.ofReal (γ * ‖G‖ ^ 2) ≤
      ∫⁻ ξ, ENNReal.ofReal (‖probeProj G W (ω ξ) G‖ ^ 2) ∂μ)
    {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) (W₀ : Matrix m n ℝ) {lr ℒinf : ℝ} (hinf : ∀ W, ℒinf ≤ ℒ W)
    (hh : 0 < lr * (1 - β * lr / 2)) {K : ℕ} (hK : 0 < K) :
    ∃ k < K, iterE μ k (fun ω' => ENNReal.ofReal (‖g (probeIter T g lr ω W₀ k ω')‖ ^ 2)) ≤
      ENNReal.ofReal (((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        (gradPot ℒ β ℒinf W₀ + K * (β * ϑ)) * ϑ / (lr * (1 - β * lr / 2))) / γ) := by
  have hϑ0 : 0 ≤ ϑ := (norm_nonneg _).trans (hT 0)
  have hpre : ∀ W ξ, probePre g lr (ω ξ) W = projGradStep (probeProj (g W) W (ω ξ)) g lr W :=
    fun W ξ => probePre_eq_projGradStep g lr (ω ξ) W
  have hstep : ∀ W ξ, gradPot ℒ β ℒinf (T (probePre g lr (ω ξ) W)) ≤
        gradPot ℒ β ℒinf W + β * ϑ ∧
      ∀ w ∈ segment ℝ (probePre g lr (ω ξ) W) (T (probePre g lr (ω ξ) W)),
        ‖g w‖ ≤ gradPot ℒ β ℒinf W + β * ϑ := fun W ξ => by
    rw [hpre]
    exact gradPot_step_le hℒ hg hβ hinf (isOrthProj_probeProj _ _ _) hh.le W (hT _)
  have hpath : ∀ k (ω' : Fin k → Ξ), gradPot ℒ β ℒinf (probeIter T g lr ω W₀ k ω') ≤
      gradPot ℒ β ℒinf W₀ + k * (β * ϑ) := by
    intro k
    induction k with
    | zero => intro ω'; simp [probeIter, pathIter]
    | succ k ih =>
      intro ω'
      have h1 := (hstep (probeIter T g lr ω W₀ k (Fin.init ω')) (ω' (Fin.last k))).1
      have h2 := ih (Fin.init ω')
      have e : probeIter T g lr ω W₀ (k + 1) ω' =
          T (probePre g lr (ω (ω' (Fin.last k))) (probeIter T g lr ω W₀ k (Fin.init ω'))) := rfl
      rw [e]
      push_cast
      linarith
  refine exists_iterE_grad_sq_le_of_capture hℒ hg hγ0 hcap hT W₀ (fun k hk ω' ξ w hw => ?_) hinf
    hh hK
  have h1 := (hstep (probeIter T g lr ω W₀ k ω') ξ).2 w hw
  have h2 := hpath k ω'
  have hβϑ : 0 ≤ β * ϑ := by positivity
  have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
  have h3 : (k : ℝ) * (β * ϑ) + β * ϑ ≤ K * (β * ϑ) := by nlinarith
  linarith

/-- **Theorem B without the gradient-bound hypothesis.**  For a `β`-smooth loss bounded below and an
isotropic probe, `min_{k<K} E ‖∇ℒ(W_k)‖² ≤ n [(ℒ(W₀) − ℒ_inf) / (K c) + B_K ϑ / c]` with the derived
`B_K = (2 β (ℒ(W₀) − ℒ_inf))^{1/2} + K β ϑ`.  With `ϑ = O(1/K)` the right-hand side is
`O(n / K)`. -/
theorem exists_iterE_grad_sq_le_probeIter_of_smooth [Nonempty n] [Nonempty Ξ]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hβ : 0 < β)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hiso : IsIsotropicLaw μ ω) {T : Matrix m n ℝ → Matrix m n ℝ} {ϑ : ℝ}
    (hT : ∀ X, ‖T X - X‖ ≤ ϑ) (W₀ : Matrix m n ℝ) {lr ℒinf : ℝ} (hinf : ∀ W, ℒinf ≤ ℒ W)
    (hh : 0 < lr * (1 - β * lr / 2)) {K : ℕ} (hK : 0 < K) :
    ∃ k < K, iterE μ k (fun ω' => ENNReal.ofReal (‖g (probeIter T g lr ω W₀ k ω')‖ ^ 2)) ≤
      ENNReal.ofReal (Fintype.card n * ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
        (gradPot ℒ β ℒinf W₀ + K * (β * ϑ)) * ϑ / (lr * (1 - β * lr / 2)))) := by
  classical
  have hγ0 : (0 : ℝ) < 1 / Fintype.card n := by
    have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    positivity
  obtain ⟨k, hk, hle⟩ := exists_iterE_grad_sq_le_of_capture_of_smooth hβ hℒ hg hγ0
    (fun G W => (lintegral_probeProj_ge hiso G W).2) hT W₀ hinf hh hK
  refine ⟨k, hk, hle.trans (le_of_eq ?_)⟩
  rw [div_div_eq_mul_div, div_one, mul_comm]

end SmoothConvergence

/-! ### The Gaussian probe: dimension factor `rank N ≤ min(m, n)` -/

section GaussianRank

open ProbabilityTheory

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- With the correlated left probe `N ω`, the pair ratio is the Rayleigh quotient of `N Nᵀ` at
`N ω`. -/
lemma twoProbeRatio_correlated (N : Matrix m n ℝ) (ω : n → ℝ) :
    twoProbeRatio N ω (N *ᵥ ω) =
      (Nᵀ *ᵥ (N *ᵥ ω)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ ω)) / ((N *ᵥ ω) ⬝ᵥ (N *ᵥ ω)) := by
  set u := N *ᵥ ω with hu
  set z := Nᵀ *ᵥ u with hz
  have e1 : u ⬝ᵥ (N *ᵥ z) = z ⬝ᵥ z := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [twoProbeRatio, ← hu, ← hz, e1]
  set p := u ⬝ᵥ u with hp
  set q := z ⬝ᵥ z with hq
  rcases eq_or_ne q 0 with h | h
  · simp [h]
  rcases eq_or_ne p 0 with h' | h'
  · simp [h']
  field_simp

/-- **The sharper deterministic capture**: `‖Π̂ G‖² ≥ ‖P(W) G‖² + ‖Nᵀ N ω‖² / ‖N ω‖²`, which
improves Theorem B by Cauchy–Schwarz (`‖Nᵀ u‖² / ‖u‖² ≥ ‖u‖² / ‖ω‖²` for `u = N ω`). -/
theorem probe_capture_ge_rayleigh [DecidableEq m] (G W : Matrix m n ℝ) (ω : n → ℝ) :
    ‖tangentProj (thinU W) (thinV W) G‖ ^ 2 +
        ((normalBlock (thinU W) (thinV W) G)ᵀ *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω)) ⬝ᵥ
          ((normalBlock (thinU W) (thinV W) G)ᵀ *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω)) /
          ((normalBlock (thinU W) (thinV W) G *ᵥ ω) ⬝ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω)) ≤
      ‖probeProj G W ω G‖ ^ 2 := by
  obtain ⟨N, hN⟩ : ∃ N, N = normalBlock (thinU W) (thinV W) G := ⟨_, rfl⟩
  rw [← hN, ← twoProbeRatio_correlated, norm_probeProj_apply, hN]
  obtain ⟨h1, h2, h3⟩ := probeU_capture G W ω
  obtain ⟨h4, h5⟩ := probeV_capture G W ω
  have hu : (probeU G W ω * (probeU G W ω)ᵀ) *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω) =
      normalBlock (thinU W) (thinV W) G *ᵥ ω := mulVec_normalBlock_capture h1 h2 h3
  have hGU : Gᵀ * thinU W = (Gᵀ * probeU G W ω) * ((probeU G W ω)ᵀ * thinU W) := by
    calc Gᵀ * thinU W = Gᵀ * (probeU G W ω * (probeU G W ω)ᵀ * thinU W) := by rw [h1]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hVG : probeV G W ω * (probeV G W ω)ᵀ * (Gᵀ * thinU W) = Gᵀ * thinU W := by
    rw [hGU]
    exact mul_mul_of_capture h5 _
  have hVu : (probeV G W ω * (probeV G W ω)ᵀ) *ᵥ
      (Gᵀ *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω)) =
      Gᵀ *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω) := by
    have e : Gᵀ *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω) =
        (Gᵀ * probeU G W ω) *ᵥ ((probeU G W ω)ᵀ *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω)) := by
      calc Gᵀ *ᵥ (normalBlock (thinU W) (thinV W) G *ᵥ ω)
          = Gᵀ *ᵥ ((probeU G W ω * (probeU G W ω)ᵀ) *ᵥ
              (normalBlock (thinU W) (thinV W) G *ᵥ ω)) := by rw [hu]
        _ = _ := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, mulVec_mulVec_of_mul_eq h5]
  exact norm_sq_galerkin_ge_of_two_probes (thinU_orthonormal W) (thinV_orthonormal W)
    (thinU_orthonormal _) (thinU_orthonormal _) h1 h2 h3 h4 hVG hVu

omit [DecidableEq n] in
/-- The Rayleigh quotient is a bounded Borel function of the probe. -/
lemma measurable_rayleigh (N : Matrix m n ℝ) :
    Measurable fun x : EuclideanSpace ℝ n =>
      (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) / ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) := by
  have hx : Measurable fun x : EuclideanSpace ℝ n => x.ofLp := measurable_ofLp'
  have hu : Measurable fun x : EuclideanSpace ℝ n => N *ᵥ x.ofLp :=
    (measurable_mulVec_const N).comp hx
  have hz : Measurable fun x : EuclideanSpace ℝ n => Nᵀ *ᵥ (N *ᵥ x.ofLp) :=
    (measurable_mulVec_const Nᵀ).comp hu
  exact (measurable_dotProduct hz hz).div (measurable_dotProduct hu hu)

omit [DecidableEq n] in
lemma integrable_rayleigh {ν : Measure (EuclideanSpace ℝ n)} [IsProbabilityMeasure ν]
    (N : Matrix m n ℝ) : Integrable (fun x : EuclideanSpace ℝ n =>
      (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) / ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp))) ν := by
  classical
  refine Integrable.of_bound (measurable_rayleigh N).aestronglyMeasurable
    (Curvature.specNorm Nᵀ ^ 2) (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) /
      ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) :=
    div_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _)
  rw [Real.norm_of_nonneg h0]
  exact div_le_of_le_mul₀ (dotProduct_self_nonneg _) (sq_nonneg _)
    (dotProduct_mulVec_le_specNorm Nᵀ _)

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- The numerics: a rank at most `d` turns the Rayleigh bound into the fraction `1/d`. -/
lemma capture_fraction {t F r d : ℝ} (ht : 0 ≤ t) (hd : 1 ≤ d) (hr : r ≤ d) (hr0 : 0 < r)
    (hF : 0 ≤ F) : (1 / d) * (t + F) ≤ t + F / r := by
  have hd0 : 0 < d := by linarith
  have h1 : (1 / d) * t ≤ t := mul_le_of_le_one_left ht (by rw [div_le_one hd0]; exact hd)
  have h2 : (1 / d) * F ≤ F / r := by
    rw [one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hF hr0 hr
  rw [mul_add]
  linarith

/-- **Theorem B for the Gaussian probe with the rank constant.**  For standard
Gaussian `ω`, `E ‖Π̂ G‖² ≥ ‖P(W) G‖² + ‖N‖²_F / rank N`, in particular
`E ‖Π̂ G‖² ≥ ‖G‖²_F / min(m, n)`.  Rotation invariance gives the rank of
`N` in place of `n`, and no such improvement holds for coordinate probes. The bases may be any
selection: the expectation is the lower integral. -/
theorem lintegral_probeProj_gaussian_ge [Nonempty m] [Nonempty n] (G W : Matrix m n ℝ) :
    ENNReal.ofReal ((1 / min (Fintype.card m : ℝ) (Fintype.card n)) * ‖G‖ ^ 2) ≤
      ∫⁻ x : EuclideanSpace ℝ n, ENNReal.ofReal (‖probeProj G W x.ofLp G‖ ^ 2)
        ∂stdGaussian (EuclideanSpace ℝ n) := by
  classical
  have hrot := isRotationInvariant_stdGaussian (n := n)
  obtain ⟨N, hN⟩ : ∃ N, N = normalBlock (thinU W) (thinV W) G := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = ‖tangentProj (thinU W) (thinV W) G‖ ^ 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hpyth : ‖G‖ ^ 2 = t + ‖N‖ ^ 2 := by
    rw [ht, hN]
    exact (norm_sq_tangentProj_add_normal (thinU_orthonormal W) (thinV_orthonormal W) G).symm
  set f : EuclideanSpace ℝ n → ℝ := fun x => t +
    (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) / ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) with hf
  have hfi : Integrable f (stdGaussian (EuclideanSpace ℝ n)) :=
    (integrable_const _).add (integrable_rayleigh N)
  have hf0 : ∀ x, 0 ≤ f x := fun x =>
    add_nonneg ht0 (div_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _))
  have hdom : ∀ x : EuclideanSpace ℝ n, f x ≤ ‖probeProj G W x.ofLp G‖ ^ 2 := fun x => by
    have := probe_capture_ge_rayleigh G W x.ofLp
    rw [← hN, ← ht] at this
    exact this
  have hval : ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ n) = t +
      ∫ x : EuclideanSpace ℝ n, (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) /
        ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) ∂stdGaussian (EuclideanSpace ℝ n) := by
    rw [hf, integral_add (integrable_const _) (integrable_rayleigh N)]
    simp
  have hmain : (1 / min (Fintype.card m : ℝ) (Fintype.card n)) * ‖G‖ ^ 2 ≤
      ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ n) := by
    rw [hval, hpyth]
    have hM : (1 : ℝ) ≤ Fintype.card m := by exact_mod_cast Fintype.card_pos
    have hn : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
    have hd1 : (1 : ℝ) ≤ min (Fintype.card m : ℝ) (Fintype.card n) := le_min hM hn
    rcases eq_or_ne N 0 with h0 | h0
    · have hI : 0 ≤ ∫ x : EuclideanSpace ℝ n, (Nᵀ *ᵥ (N *ᵥ x.ofLp)) ⬝ᵥ (Nᵀ *ᵥ (N *ᵥ x.ofLp)) /
          ((N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp)) ∂stdGaussian (EuclideanSpace ℝ n) :=
        integral_nonneg fun x => div_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _)
      have h1 : (1 / min (Fintype.card m : ℝ) (Fintype.card n)) * t ≤ t :=
        mul_le_of_le_one_left ht0 (by rw [div_le_one (by linarith)]; exact hd1)
      simp only [h0, norm_zero] at hI ⊢
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      linarith
    · have hrank : 0 < N.rank := Nat.pos_of_ne_zero fun h => h0 (eq_zero_of_rank_eq_zero h)
      have hrr : (0 : ℝ) < N.rank := by exact_mod_cast hrank
      have hrd : (N.rank : ℝ) ≤ min (Fintype.card m : ℝ) (Fintype.card n) :=
        le_min (by exact_mod_cast Matrix.rank_le_card_height N)
          (by exact_mod_cast Matrix.rank_le_card_width N)
      have h1 := capture_fraction ht0 hd1 hrd hrr (sq_nonneg ‖N‖)
      have h2 := div_rank_le_integral_ratio hrot N (ae_mulVec_ne_zero_stdGaussian h0)
      linarith
  calc ENNReal.ofReal ((1 / min (Fintype.card m : ℝ) (Fintype.card n)) * ‖G‖ ^ 2)
      ≤ ENNReal.ofReal (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ n)) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂stdGaussian (EuclideanSpace ℝ n) :=
        ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)
    _ ≤ _ := lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hdom x)

/-- **Theorem B for the concrete method with Gaussian probes.**  Let `ℒ` be
`β`-smooth and bounded below, `T` a Borel tolerance truncation
(`exists_measurable_isToleranceTruncation`), and `W_k` the concrete probed iterates
`Û = orth[U, G V, G ω]`, `V̂ = orth[V, Gᵀ Û]`, `W_{k+1} = T(Û Ûᵀ (W_k − λ G) V̂ V̂ᵀ)`, with
independent standard Gaussian probes.  Then, under the product Gaussian law, with
`c = λ (1 − βλ/2) > 0`,
`min_{k<K} E ‖∇ℒ(W_k)‖² ≤ min(m, n) [(ℒ(W₀) − ℒ_inf) / (K c) + B_K ϑ / c]`,
`B_K = (2 β (ℒ(W₀) − ℒ_inf))^{1/2} + K β ϑ`.
This is the convergence statement with `min(m, n)` in place of `n`, the bound `B` derived
rather than assumed, and every basis concrete.  Contrast `bugStep_iterate_quadratic`: without the
probe the method is stuck for ever at a point with `‖∇ℒ‖` arbitrary. -/
theorem exists_lintegral_gaussian_grad_sq_le [Nonempty m] [Nonempty n]
    {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hβ : 0 < β)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {T : Matrix m n ℝ → Matrix m n ℝ} (hTm : Measurable T) {ϑ : ℝ}
    (hT : IsToleranceTruncation T ϑ) (W₀ : Matrix m n ℝ) {lr ℒinf : ℝ} (hinf : ∀ W, ℒinf ≤ ℒ W)
    (hh : 0 < lr * (1 - β * lr / 2)) {K : ℕ} (hK : 0 < K) :
    ∃ k < K, ∫⁻ ω', ENNReal.ofReal
          (‖g (probeIter T g lr (fun x : EuclideanSpace ℝ n => x.ofLp) W₀ k ω')‖ ^ 2)
        ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ n)) ≤
      ENNReal.ofReal (min (Fintype.card m : ℝ) (Fintype.card n) *
        ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
          (gradPot ℒ β ℒinf W₀ + K * (β * ϑ)) * ϑ / (lr * (1 - β * lr / 2)))) := by
  have hM : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hγ0 : (0 : ℝ) < 1 / min (Fintype.card m : ℝ) (Fintype.card n) :=
    one_div_pos.2 (lt_min hM hn)
  obtain ⟨k, hk, hle⟩ := exists_iterE_grad_sq_le_of_capture_of_smooth (μ := stdGaussian _)
    (ω := fun x : EuclideanSpace ℝ n => x.ofLp) hβ hℒ hg hγ0
    (fun G W => lintegral_probeProj_gaussian_ge G W) hT.norm_sub_le W₀ hinf hh hK
  refine ⟨k, hk, ?_⟩
  have hgm := measurable_of_lipschitz hg
  have hm : Measurable fun ω' => ENNReal.ofReal
      (‖g (probeIter T g lr (fun x : EuclideanSpace ℝ n => x.ofLp) W₀ k ω')‖ ^ 2) :=
    (measurable_norm_sq.comp (hgm.comp (measurable_probeIter hTm hgm measurable_ofLp' lr W₀ k))
      ).ennreal_ofReal
  rw [← iterE_eq_lintegral_pi hm]
  refine hle.trans (le_of_eq ?_)
  rw [div_div_eq_mul_div, div_one, mul_comm]

/-- **The Gaussian convergence theorem is not vacuous**: for every `ϑ ≥ 0` a Borel tolerance
truncation exists, so the bound of `exists_lintegral_gaussian_grad_sq_le` holds for a truncated SVD
with a Borel choice at tied singular values. -/
theorem exists_gaussian_convergence [Nonempty m] [Nonempty n] {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hβ : 0 < β)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (W₀ : Matrix m n ℝ) {lr ℒinf : ℝ} (hinf : ∀ W, ℒinf ≤ ℒ W)
    (hh : 0 < lr * (1 - β * lr / 2)) {K : ℕ} (hK : 0 < K) :
    ∃ T : Matrix m n ℝ → Matrix m n ℝ, Measurable T ∧ IsToleranceTruncation T ϑ ∧
      ∃ k < K, ∫⁻ ω', ENNReal.ofReal
            (‖g (probeIter T g lr (fun x : EuclideanSpace ℝ n => x.ofLp) W₀ k ω')‖ ^ 2)
          ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ n)) ≤
        ENNReal.ofReal (min (Fintype.card m : ℝ) (Fintype.card n) *
          ((ℒ W₀ - ℒinf) / (K * (lr * (1 - β * lr / 2))) +
            (gradPot ℒ β ℒinf W₀ + K * (β * ϑ)) * ϑ / (lr * (1 - β * lr / 2)))) := by
  obtain ⟨T, hTm, hT⟩ := exists_measurable_isToleranceTruncation (m := m) (n := n) hϑ
  exact ⟨T, hTm, hT, exists_lintegral_gaussian_grad_sq_le hβ hℒ hg hTm hT W₀ hinf hh hK⟩

/-- **Convergence to a stationary point of the full problem, Gaussian probes.**
For a Borel family `T` of truncations and the gradient-coupled tolerance
`ϑ_k = c₀ λ ‖Π̂_k ∇ℒ(W_k)‖² / B`, `0 ≤ c₀ < 1 − βλ/2`, with `B` a gradient bound on the truncation
segments, `E ‖∇ℒ(W_k)‖² → 0` under the product Gaussian law. -/
theorem tendsto_lintegral_gaussian_grad_sq [Nonempty m] [Nonempty n] {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {T : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hTm : Measurable (Function.uncurry T)) (hT : ∀ ϑ, 0 ≤ ϑ → IsToleranceTruncation (T ϑ) ϑ)
    (W₀ : Matrix m n ℝ) {lr B c₀ ℒinf : ℝ} (hB0 : 0 < B) (hlr : 0 < lr) (hc0 : 0 ≤ c₀)
    (hc : c₀ < 1 - β * lr / 2)
    (hB : ∀ k ω' (ξ : EuclideanSpace ℝ n), ∀ w ∈ segment ℝ
      (probePre g lr ξ.ofLp (pathIter
        (fun (ξ : EuclideanSpace ℝ n) W => coupledStep T g lr c₀ B ξ.ofLp W) W₀ k ω'))
      (coupledStep T g lr c₀ B ξ.ofLp (pathIter
        (fun (ξ : EuclideanSpace ℝ n) W => coupledStep T g lr c₀ B ξ.ofLp W) W₀ k ω')), ‖g w‖ ≤ B)
    (hinf : ∀ W, ℒinf ≤ ℒ W) :
    Tendsto (fun k => ∫⁻ ω', ENNReal.ofReal (‖g (pathIter
        (fun (ξ : EuclideanSpace ℝ n) W => coupledStep T g lr c₀ B ξ.ofLp W) W₀ k ω')‖ ^ 2)
      ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ n))) atTop (𝓝 0) := by
  classical
  have hM : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hγ0 : (0 : ℝ) < 1 / min (Fintype.card m : ℝ) (Fintype.card n) :=
    one_div_pos.2 (lt_min hM hn)
  have hgm := measurable_of_lipschitz hg
  have hstep : Measurable fun p : EuclideanSpace ℝ n × Matrix m n ℝ =>
      coupledStep T g lr c₀ B p.1.ofLp p.2 := by
    have hW : Measurable fun p : EuclideanSpace ℝ n × Matrix m n ℝ => p.2 := measurable_snd
    have hω : Measurable fun p : EuclideanSpace ℝ n × Matrix m n ℝ => p.1.ofLp :=
      measurable_ofLp'.comp measurable_fst
    have hG : Measurable fun p : EuclideanSpace ℝ n × Matrix m n ℝ => g p.2 := hgm.comp hW
    have hcap : Measurable fun p : EuclideanSpace ℝ n × Matrix m n ℝ =>
        ‖probeProj (g p.2) p.2 p.1.ofLp (g p.2)‖ ^ 2 := by
      simp only [probeProj_eq]
      exact measurable_norm_sq.comp (measurable_mat_mul (measurable_mat_mul
        (measurable_probeL hG hW hω) hG) (measurable_probeR hG hW hω))
    have hϑ : Measurable fun p : EuclideanSpace ℝ n × Matrix m n ℝ =>
        c₀ * lr * ‖probeProj (g p.2) p.2 p.1.ofLp (g p.2)‖ ^ 2 / B :=
      (hcap.const_mul _).div_const _
    exact hTm.comp (hϑ.prodMk (measurable_probePre hgm lr hW hω))
  have hlim := tendsto_iterE_grad_sq_coupled (μ := stdGaussian (EuclideanSpace ℝ n))
    (ω := fun x : EuclideanSpace ℝ n => x.ofLp) hℒ hg hγ0
    (fun G W => lintegral_probeProj_gaussian_ge G W) (fun ϑ hϑ => (hT ϑ hϑ).norm_sub_le) W₀ hB0
    hlr hc0 hc hB hinf
  refine hlim.congr fun k => ?_
  exact iterE_eq_lintegral_pi ((measurable_norm_sq.comp (hgm.comp
    (measurable_pathIter (step := fun (ξ : EuclideanSpace ℝ n) W =>
      coupledStep T g lr c₀ B ξ.ofLp W) hstep W₀ k))).ennreal_ofReal)

end GaussianRank

/-- The local column-space projector `orth K (orth K)ᵀ` of this file, replaced by the core
`Matrix.rangeProj` (equal: `rangeProj_eq_orth_mul_transpose`). -/
@[deprecated (since := "2026-11-09")] alias colProj := Matrix.rangeProj

/-- The local singular-value tail of this file, replaced by the core `WeylSingular.tailNorm` (same
definition). -/
@[deprecated (since := "2026-11-10")] alias svTail := WeylSingular.tailNorm

/-- The local tolerance rank `sInf {r | τ_r(X) ≤ ϑ}` of this file, replaced by the core `epsRank`
(equal: `WeylSingular.epsRank_eq_sInf_tailNorm`). -/
@[deprecated (since := "2026-11-10")] alias tolRank := epsRank

/-- The bridge `tolRank ϑ X = epsRank ϑ X` of an earlier version; the core form is
`WeylSingular.epsRank_eq_sInf_tailNorm`. -/
@[deprecated (since := "2026-11-10")] alias tolRank_eq_epsRank :=
  WeylSingular.epsRank_eq_sInf_tailNorm

end LeanDLRA.Novel.BlindSpotII
