import LeanDLRA.FixedRank.TangentSpace
import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.WeylSingular

/-!
# Curvature bounds at a matrix, tangent velocities and first-order optimality

The curvature bounds of `LeanDLRA/Matrix/Curvature.lean` are stated for given orthonormal factors.
This file states them for the tangent projector at a matrix, `tangentProjAt`, with the lower bound
`ρ ≤ σ_{r-1}(X)` for the `r`-th singular value of a matrix `X` of rank `r` (`σ₀ ≥ σ₁ ≥ ⋯`,
`0`-indexed), and derives two facts about the fixed-rank manifold `ℳ_r` used in the analysis of
dynamical low-rank approximation: the velocity of a differentiable curve in `ℳ_r` is a tangent
vector, and a best approximation of rank at most `r` satisfies the first-order optimality condition
`P(X) (A - X) = 0`. All norms of matrices are Frobenius norms.

## Main results

* `LeanDLRA.norm_tangentProj_sub_tangentProjAt_le`: for `X` of rank `r` with `ρ ≤ σ_{r-1}(X)` and
  orthonormal `U`, `V` with `r` columns, `‖tangentProj U V B - P(X) B‖ ≤ 2 ρ⁻¹ ‖U S Vᵀ - X‖ ‖B‖`
  for every core `S` (invertible or not).
* `LeanDLRA.norm_tangentProjAt_sub_le`: for `X`, `Y` of rank `r`,
  `‖P(Y) B - P(X) B‖ ≤ 2 ρ⁻¹ ‖Y - X‖ ‖B‖` (Lipschitz bound of `Y ↦ P(Y)`).
* `LeanDLRA.norm_one_sub_tangentProjAt_apply_sub_le`: `‖(1 - P(Y)) (Y - X)‖ ≤ ρ⁻¹ ‖Y - X‖²`.
* `LeanDLRA.norm_deriv_le_of_norm_le_norm_sub_mul`: a bound `‖φ u‖ ≤ ‖X u - X t‖ g(u)` with
  `φ t = 0` bounds the derivative of `φ` by `‖X'‖ g(t)`.
* `LeanDLRA.mem_tangentSpaceAt_of_hasDerivWithinAt`: the derivative of a curve of rank-`r` matrices
  with `σ_{r-1} ≥ ρ > 0` lies in the tangent space at the curve.
* `LeanDLRA.tangentProjAt_sub_eq_zero_of_forall_norm_sub_le`: if `X` is a best approximation of
  `A` among the matrices of rank at most `r`, then `P(X) (A - X) = 0`;
  `LeanDLRA.tangentProjAt_truncation_sub_eq_zero`: the truncated SVD satisfies it.

## Implementation notes

The bounds need the lower bound `ρ` at one of the two points only; there is no smallness condition
on `‖Y - X‖`. The first-order condition is proved with the curve `(1 + ε M) X (1 + ε N)` of rank at
most `r`, whose velocity at `ε = 0` is the tangent vector `M X + X N`; no factorization of `X` is
chosen.

## References

* [KochLubich2007, §2 and Lemma 4.2]
-/

open Set Filter Matrix
open scoped Topology RealInnerProductSpace

namespace LeanDLRA

section AtPoint

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Lipschitz bound of the tangent projector, factored second point.** Let `X` have rank `r`
and `0 < ρ ≤ σ_{r-1}(X)`, and let `U`, `V` have `r` orthonormal columns. For every core `S`
(invertible or not) and every `B`:
`‖tangentProj U V B - P(X) B‖ ≤ 2 ρ⁻¹ ‖U S Vᵀ - X‖ ‖B‖`. -/
theorem norm_tangentProj_sub_tangentProjAt_le {r : ℕ} {X : Matrix m n ℝ} (hX : X.rank = r)
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) (B : Matrix m n ℝ) :
    ‖tangentProj U V B - tangentProjAt X B‖ ≤ 2 * ρ⁻¹ * ‖U * S * Vᵀ - X‖ * ‖B‖ := by
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, hS₀, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU₀ hV₀ rfl hρ
    (by simpa using hσ)
  rw [tangentProjAt_eq_tangentProj hU₀ hV₀ hS₀]
  have h := Curvature.koch_lubich_tangent_frob (S' := S) hρ hU₀ hV₀ hU hV hb B
  rwa [Curvature.tangentProjMat_eq_tangentProj, Curvature.tangentProjMat_eq_tangentProj] at h

/-- **Lipschitz bound of the tangent projector at a matrix** [KochLubich2007, Lemma 4.2; constant
of `Curvature.koch_lubich_tangent_frob`]. For `X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)`:
`‖P(Y) B - P(X) B‖ ≤ 2 ρ⁻¹ ‖Y - X‖ ‖B‖`. No smallness of `‖Y - X‖` is needed. -/
theorem norm_tangentProjAt_sub_le {r : ℕ} {X Y : Matrix m n ℝ} (hX : X.rank = r)
    (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1))
    (B : Matrix m n ℝ) :
    ‖tangentProjAt Y B - tangentProjAt X B‖ ≤ 2 * ρ⁻¹ * ‖Y - X‖ * ‖B‖ := by
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  rw [tangentProjAt_eq_tangentProj hU hV hS]
  exact norm_tangentProj_sub_tangentProjAt_le hX hρ hσ hU hV S B

/-- **Normal curvature bound at a matrix** [KochLubich2007, Lemma 4.2; constant of
`Curvature.koch_lubich_normal`]. For `X`, `Y` of rank `r` with `0 < ρ ≤ σ_{r-1}(X)`, the normal
component of `Y - X` at `Y` is quadratic: `‖(1 - P(Y)) (Y - X)‖ ≤ ρ⁻¹ ‖Y - X‖²`. -/
theorem norm_one_sub_tangentProjAt_apply_sub_le {r : ℕ} {X Y : Matrix m n ℝ}
    (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) :
    ‖(1 - tangentProjAt Y) (Y - X)‖ ≤ ρ⁻¹ * ‖Y - X‖ ^ 2 := by
  classical
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, -, rfl⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  obtain ⟨U, S, V, hU, hV, hS, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y).1 hY
  have hb := WeylSingular.mul_norm_le_norm_toEuclideanLin_core hU₀ hV₀ rfl hρ
    (by simpa using hσ)
  have h := Curvature.koch_lubich_normal (S' := S) hρ hU₀ hV₀ hU hV hb
  rw [tangentProjAt_eq_tangentProj hU hV hS, sub_apply,
    one_apply_eq_self, sub_eq_iff_eq_add'.mpr
      (tangentProj_add_normal U V (U * S * Vᵀ - U₀ * S₀ * V₀ᵀ)).symm]
  exact h

end AtPoint

/-! ### Derivatives bounded through a slope bound -/

/-- **A derivative bounded through a slope bound.** Let `φ t = 0` and `‖φ u‖ ≤ ‖X u - X t‖ g(u)`
for `u ∈ s`, with `g` continuous at `t` within `s` and `t` an accumulation point of `s`. Then the
derivatives `d` of `φ` and `X'` of `X` at `t` within `s` satisfy `‖d‖ ≤ ‖X'‖ g(t)`. -/
theorem norm_deriv_le_of_norm_le_norm_sub_mul {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] {s : Set ℝ} {t : ℝ} {φ : ℝ → H}
    {X : ℝ → G} {d : H} {X' : G} {g : ℝ → ℝ} (hφ : HasDerivWithinAt φ d s t)
    (hX : HasDerivWithinAt X X' s t) (hs : (𝓝[s \ {t}] t).NeBot) (hφ0 : φ t = 0)
    (hg : ContinuousWithinAt g s t) (hb : ∀ u ∈ s, ‖φ u‖ ≤ ‖X u - X t‖ * g u) :
    ‖d‖ ≤ ‖X'‖ * g t := by
  have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 hφ).norm
  have h2 := (hasDerivWithinAt_iff_tendsto_slope.1 hX).norm
  have hg' : Tendsto g (𝓝[s \ {t}] t) (𝓝 (g t)) :=
    hg.tendsto.mono_left (nhdsWithin_mono _ Set.sdiff_subset)
  refine le_of_tendsto_of_tendsto h1 (h2.mul hg') ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hut : u ≠ t := hu.2
  have hpos : 0 < |u - t|⁻¹ := inv_pos.2 (abs_pos.2 (sub_ne_zero.2 hut))
  simp only [slope_def_module, norm_smul, hφ0, sub_zero, Real.norm_eq_abs, norm_inv]
  rw [mul_assoc, mul_comm (‖X u - X t‖), ← mul_assoc]
  calc |u - t|⁻¹ * ‖φ u‖ ≤ |u - t|⁻¹ * (‖X u - X t‖ * g u) :=
        mul_le_mul_of_nonneg_left (hb u hu.1) hpos.le
    _ = _ := by ring

/-! ### Curves on the fixed-rank manifold -/

section Curves

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The velocity of a curve of rank-`r` matrices is tangent** [KochLubich2007, §2]. Let
`X u` have rank `r` and `ρ ≤ σ_{r-1}(X u)` (`ρ > 0`) for `u ∈ s`, and let `X` have the derivative
`X'` at `t ∈ s` within `s`, `t` an accumulation point of `s`. Then `X'` lies in the tangent space
at `X t`. Proof: the normal component of `X u - X t` at `X t` is at most `ρ⁻¹ ‖X u - X t‖²`. -/
theorem mem_tangentSpaceAt_of_hasDerivWithinAt {r : ℕ} {X : ℝ → Matrix m n ℝ}
    {X' : Matrix m n ℝ} {s : Set ℝ} {t ρ : ℝ} (hX : HasDerivWithinAt X X' s t) (ht : t ∈ s)
    (hs : (𝓝[s \ {t}] t).NeBot) (hρ : 0 < ρ) (hrank : ∀ u ∈ s, (X u).rank = r)
    (hσ : ∀ u ∈ s, ρ ≤ (toEuclideanLin (X u)).singularValues (r - 1)) :
    X' ∈ tangentSpaceAt (X t) := by
  set N := (1 - tangentProjAt (X t) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) with hN
  have hφ : HasDerivWithinAt (fun u => N (X u - X t)) (N X') s t :=
    N.hasFDerivAt.comp_hasDerivWithinAt t (hX.sub_const (X t))
  have hb : ∀ u ∈ s, ‖N (X u - X t)‖ ≤ ‖X u - X t‖ * (ρ⁻¹ * ‖X u - X t‖) := fun u hu => by
    have h := norm_one_sub_tangentProjAt_apply_sub_le (hrank u hu) (hrank t ht) hρ (hσ u hu)
    rw [← neg_sub (X t) (X u), map_neg, norm_neg, norm_neg, hN]
    calc _ ≤ _ := h
      _ = _ := by ring
  have hg : ContinuousWithinAt (fun u => ρ⁻¹ * ‖X u - X t‖) s t :=
    continuousWithinAt_const.mul ((hX.continuousWithinAt.sub continuousWithinAt_const).norm)
  have h := norm_deriv_le_of_norm_le_norm_sub_mul hφ hX hs (by simp) hg hb
  simp only [sub_self, norm_zero, mul_zero] at h
  have h0 : N X' = 0 := norm_le_zero_iff.mp h
  rw [hN, sub_apply, one_apply_eq_self, sub_eq_zero] at h0
  exact tangentProjAt_eq_self_iff.mp h0.symm

omit [DecidableEq n] in
/-- **First-order optimality of a best approximation of rank at most `r`.** If `X` has rank at
most `r` and `‖A - X‖ ≤ ‖A - Z‖` for every `Z` of rank at most `r`, then `A - X` is orthogonal to
the tangent space at `X`: `P(X) (A - X) = 0`. Proof: for a tangent vector `M X + X N` the curve
`(1 + ε M) X (1 + ε N)` has rank at most `r`, so `ε ↦ ‖A - (1 + ε M) X (1 + ε N)‖²` is minimal at
`ε = 0`, where its derivative is `-2 ⟪A - X, M X + X N⟫`. -/
theorem tangentProjAt_sub_eq_zero_of_forall_norm_sub_le {r : ℕ} {A X : Matrix m n ℝ}
    (hX : X.rank ≤ r) (hbest : ∀ Z : Matrix m n ℝ, Z.rank ≤ r → ‖A - X‖ ≤ ‖A - Z‖) :
    tangentProjAt X (A - X) = 0 := by
  classical
  have horth : ∀ Z ∈ tangentSpaceAt X, ⟪A - X, Z⟫ = 0 := by
    rintro _ ⟨M, N, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℝ → Matrix m n ℝ,
        c = fun ε => A - X - ε • (M * X + X * N) - (ε ^ 2) • (M * X * N) := ⟨_, rfl⟩
    have hcurve : ∀ ε : ℝ, c ε = A - (1 + ε • M) * X * (1 + ε • N) := fun ε => by
      simp only [hc, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      module
    have h0 : c 0 = A - X := by simp [hc]
    have hmin : IsLocalMin (fun ε => ‖c ε‖ ^ 2) 0 := Filter.Eventually.of_forall fun ε => by
      have hrank : ((1 + ε • M) * X * (1 + ε • N)).rank ≤ r :=
        ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)).trans hX
      change ‖c 0‖ ^ 2 ≤ ‖c ε‖ ^ 2
      rw [h0, hcurve ε]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbest _ hrank) 2
    have hd : HasDerivAt c (-(M * X + X * N)) 0 := by
      have h1 := (hasDerivAt_id (0 : ℝ)).smul_const (M * X + X * N)
      have h2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const (M * X * N)
      rw [hc]
      convert ((hasDerivAt_const (0 : ℝ) (A - X)).sub h1).sub h2 using 1 <;>
        first | (funext ε; rfl) | simp
    have h := hmin.hasDerivAt_eq_zero hd.norm_sq
    rw [h0, inner_neg_right] at h
    linarith
  have hP := isOrthProj_tangentProjAt X
  have hmem : tangentProjAt X (A - X) ∈ tangentSpaceAt X :=
    tangentProjAt_eq_self_iff.mp (hP.idem _)
  have hsq : ‖tangentProjAt X (A - X)‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, hP.symm, hP.idem]
    exact horth _ hmem
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-- **The truncated SVD satisfies the first-order optimality condition**:
`P(T_r(A)) (A - T_r(A)) = 0` for every `A` and `r`. -/
theorem tangentProjAt_truncation_sub_eq_zero (A : Matrix m n ℝ) (r : ℕ) :
    tangentProjAt (EckartYoung.truncation A r) (A - EckartYoung.truncation A r) = 0 :=
  tangentProjAt_sub_eq_zero_of_forall_norm_sub_le (EckartYoung.rank_truncation_le A r)
    fun _ hZ => EckartYoung.norm_sub_truncation_le A hZ

end Curves

/-! ### Examples -/

section Examples

open scoped LeanDLRA.Frobenius

/-- The `1 × 1` matrix `c • 1` with `c ≥ 1` has rank `1` and `σ₀ ≥ 1`. -/
private theorem rank_and_singularValues_smul_one {c : ℝ} (hc : 1 ≤ c) :
    ((c • 1 : Matrix (Fin 1) (Fin 1) ℝ)).rank = 1 ∧
      (1 : ℝ) ≤ (toEuclideanLin (c • 1 : Matrix (Fin 1) (Fin 1) ℝ)).singularValues (1 - 1) := by
  have hc0 : c ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (c • 1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [Matrix.isUnit_iff_isUnit_det, det_smul, det_one, mul_one, Fintype.card_fin, pow_one]
      exact isUnit_iff_ne_zero.mpr hc0
    simpa using rank_of_isUnit _ hu
  · refine (SVD.forall_mul_norm_le_iff_fin one_pos _).mp fun v => ?_
    rw [LinearEquiv.map_smul, toLpLin_one]
    change 1 * ‖v‖ ≤ ‖c • v‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith [norm_nonneg v]

/-- `norm_tangentProj_sub_tangentProjAt_le`, `norm_tangentProjAt_sub_le` and
`norm_one_sub_tangentProjAt_apply_sub_le` apply to `X = 1`, `Y = 2 • 1` (`1 × 1`, `r = 1`,
`ρ = 1`, `‖Y - X‖ = 1`). -/
example (B : Matrix (Fin 1) (Fin 1) ℝ) :
    ‖tangentProj (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) B -
        tangentProjAt ((1 : ℝ) • 1) B‖ ≤
      2 * 1⁻¹ * ‖(1 : Matrix (Fin 1) (Fin 1) ℝ) * ((2 : ℝ) • 1) * 1ᵀ - (1 : ℝ) • 1‖ * ‖B‖ ∧
    ‖tangentProjAt ((2 : ℝ) • 1) B - tangentProjAt ((1 : ℝ) • 1) B‖ ≤
      2 * 1⁻¹ * ‖(2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : ℝ) • 1‖ * ‖B‖ ∧
    ‖(1 - tangentProjAt ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
        ((2 : ℝ) • 1 - (1 : ℝ) • 1)‖ ≤
      1⁻¹ * ‖(2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : ℝ) • 1‖ ^ 2 := by
  obtain ⟨h1r, h1σ⟩ := rank_and_singularValues_smul_one (le_refl (1 : ℝ))
  obtain ⟨h2r, -⟩ := rank_and_singularValues_smul_one (by norm_num : (1 : ℝ) ≤ 2)
  exact ⟨norm_tangentProj_sub_tangentProjAt_le h1r one_pos h1σ (by simp) (by simp) _ B,
    norm_tangentProjAt_sub_le h1r h2r one_pos h1σ B,
    norm_one_sub_tangentProjAt_apply_sub_le h1r h2r one_pos h1σ⟩

/-- `mem_tangentSpaceAt_of_hasDerivWithinAt` for the moving curve `X u = (1 + u) • 1` on
`s = [0, 1]` at `t = 0` (`r = 1`, `ρ = 1`, velocity `1`). -/
example : (1 : Matrix (Fin 1) (Fin 1) ℝ) ∈ tangentSpaceAt (((1 : ℝ) + 0) • 1) := by
  have hX : HasDerivWithinAt (fun u : ℝ => (1 + u) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
      (Icc 0 1) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const
      (1 : Matrix (Fin 1) (Fin 1) ℝ)).hasDerivWithinAt (s := Icc 0 1)
    simpa using this
  have hs : (𝓝[Icc (0 : ℝ) 1 \ {0}] 0).NeBot := by
    rw [Icc_sdiff_left]
    exact left_nhdsWithin_Ioc_neBot one_pos
  exact mem_tangentSpaceAt_of_hasDerivWithinAt (r := 1) hX ⟨le_rfl, zero_le_one⟩ hs one_pos
    (fun u hu => (rank_and_singularValues_smul_one (by linarith [hu.1])).1)
    (fun u hu => (rank_and_singularValues_smul_one (by linarith [hu.1])).2)

/-- The hypotheses of `tangentProjAt_sub_eq_zero_of_forall_norm_sub_le` hold for the truncated SVD
of every matrix (Eckart–Young). -/
example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) (r : ℕ) :
    (EckartYoung.truncation A r).rank ≤ r ∧ ∀ Z : Matrix m n ℝ, Z.rank ≤ r →
      ‖A - EckartYoung.truncation A r‖ ≤ ‖A - Z‖ :=
  ⟨EckartYoung.rank_truncation_le A r, fun _ hZ => EckartYoung.norm_sub_truncation_le A hZ⟩

end Examples

end LeanDLRA
