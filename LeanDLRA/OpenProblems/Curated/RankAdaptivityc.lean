import LeanDLRA.Classical.SVD
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Projectors

/-!
# Quasi-optimality of dynamical low-rank approximation for matrices

Let `A` be a differentiable curve of matrices and `X t = truncation (A t) r` its best
approximation of rank `r`. The dynamical low-rank approximation `Y` of rank `r` has the form
`Y t = U t * S t * (V t)ᵀ` with orthonormal columns of `U t` and `V t`, solves
`Y' = tangentProj (U t) (V t) (A' t)` and starts at `Y 0 = X 0`. As long as `X` stays close to
`A` and the `r`-th singular value of `A` stays away from zero, the distance of `Y` to the best
approximation is bounded by the time integral of the best-approximation error, with explicit
constants. All norms are Frobenius norms.

## Main results

* `dlra_norm_sub_truncation_le_integral`: assume on `[0, T]` that `‖A' t‖ ≤ μ`, that the `r`-th
  singular value of `A t` is at least `ρ > 0`, that `‖X t - A t‖ ≤ ρ / 16`, and that `X` is
  differentiable. Then, with `β = 8 μ / ρ`, for every `t ∈ [0, T]`,
  `‖Y t - X t‖ ≤ 2 β e^{β t} ∫₀ᵗ ‖X s - A s‖ ds`.
* `dlra_quasiOptimal_matrix`: the same bound under the additional hypotheses that the derivative
  of `X` is continuous and that `‖Y s - X s‖ ≤ ρ / 16` for all `s ∈ [0, t]`.

## Implementation notes

The first theorem assumes neither smallness of `‖Y - X‖` nor continuity of the derivative of
`X`. The Lipschitz bound of `tangentProj` in its base point that the proof uses
(`Curvature.koch_lubich_tangent_frob`) needs the lower bound `ρ` for the singular values at one
of the two base points only, here at `X t`. The proof is the matrix case of the comparison
argument of `ODESolution.dlra_norm_sub_le_of_comparison_integral`, with this Lipschitz bound as
the curvature bound.

## References

* O. Koch, Ch. Lubich, Dynamical low-rank approximation, SIAM J. Matrix Anal. Appl. 29 (2007),
  Theorem 5.1.
-/

open Set Finset Matrix

namespace LeanDLRA

section Truncation

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n]

end Truncation

section Tie

open EckartYoung

end Tie

section Distance

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

end Distance

section Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L t₀ t₁ : ℝ} {A : ℝ → E}

end Galerkin

section RankAdaptive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L B ε : ℝ}

end RankAdaptive

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem norm_deriv_le_of_slope_bound {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) {φ : ℝ → H} {X : ℝ → G} {d : H} {X' : G} {g : ℝ → ℝ}
    (hφ : HasDerivWithinAt φ d (Icc a b) t) (hX : HasDerivWithinAt X X' (Icc a b) t)
    (hφ0 : φ t = 0) (hg : ContinuousWithinAt g (Icc a b) t)
    (hb : ∀ s ∈ Icc a b, ‖φ s‖ ≤ ‖X s - X t‖ * g s) : ‖d‖ ≤ ‖X'‖ * g t := by
  have hne : (nhdsWithin t (Icc a b \ {t})).NeBot :=
    accPt_principal_iff_nhdsWithin.mp (uniqueDiffOn_Icc hab t ht).accPt
  have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 hφ).norm
  have h2 := (hasDerivWithinAt_iff_tendsto_slope.1 hX).norm
  have hg' : Filter.Tendsto g (nhdsWithin t (Icc a b \ {t})) (nhds (g t)) :=
    hg.tendsto.mono_left (nhdsWithin_mono _ Set.sdiff_subset)
  refine le_of_tendsto_of_tendsto h1 (h2.mul hg') ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hst : s ≠ t := hs.2
  have hpos : 0 < |s - t|⁻¹ := inv_pos.2 (abs_pos.2 (sub_ne_zero.2 hst))
  simp only [slope_def_module, norm_smul, hφ0, sub_zero, Real.norm_eq_abs, norm_inv]
  rw [mul_assoc, mul_comm (‖X s - X t‖), ← mul_assoc]
  calc |s - t|⁻¹ * ‖φ s‖ ≤ |s - t|⁻¹ * (‖X s - X t‖ * g s) :=
        mul_le_mul_of_nonneg_left (hb s hs.1) hpos.le
    _ = _ := by ring

omit [DecidableEq m] [DecidableEq n] in
private theorem tangentProj_sub_le {r : ℕ} {U U' : Matrix m (Fin r) ℝ} {V V' : Matrix n (Fin r) ℝ}
    {σ : Fin r → ℝ} {S' : Matrix (Fin r) (Fin r) ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hσ : ∀ i, ρ ≤ σ i)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (B : Matrix m n ℝ) :
    ‖tangentProj U' V' B - tangentProj U V B‖ ≤
      2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * diagonal σ * Vᵀ‖ * ‖B‖ := by
  have h := Curvature.koch_lubich_tangent_frob (S' := S') hρ hU hV hU' hV'
    (Curvature.diagonal_bounded_below hρ.le hσ) B
  rwa [Curvature.tangentProjMat_eq_tangentProj, Curvature.tangentProjMat_eq_tangentProj] at h

omit [DecidableEq m] in
private theorem truncation_factor {r : ℕ} (hr : 0 < r) {A : Matrix m n ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1)) :
    ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (σ : Fin r → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, ρ ≤ σ i) ∧ truncation A r = U * diagonal σ * Vᵀ ∧
      tangentProj U V (A - truncation A r) = 0 := by
  have hd : r ≤ Module.finrank ℝ (EuclideanSpace ℝ n) := by
    have h0 : 0 < (toEuclideanLin A).singularValues (r - 1) := lt_of_lt_of_le hρ hσ
    rw [LinearMap.singularValues_pos_iff_lt_finrank_range] at h0
    have := (toEuclideanLin A).finrank_range_le_finrank
    omega
  let e : Fin r → Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) := Fin.castLE hd
  let ε : Fin r ≃ {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r} :=
    ⟨fun j => ⟨e j, j.2⟩, fun x => ⟨x.1.1, x.2⟩, fun j => rfl, fun x => rfl⟩
  let V : Matrix n (Fin r) ℝ := fun a j => rightSingularVectors A (e j) a
  have hVV : V * Vᵀ = topRightSingularVectors A r * (topRightSingularVectors A r)ᵀ := by
    ext a b
    simp only [V, Matrix.mul_apply, transpose_apply, topRightSingularVectors]
    exact Equiv.sum_comp ε (fun i => rightSingularVectors A i a * rightSingularVectors A i b)
  have hV : Vᵀ * V = 1 := by
    ext i j
    have h := orthonormal_iff_ite.mp (rightSingularVectors A).orthonormal (e i) (e j)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
    have hij : e i = e j ↔ i = j := (Fin.castLE_injective hd).eq_iff
    simp only [hij] at h
    simp only [Matrix.one_apply]
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
  let σ : Fin r → ℝ := fun j => (toEuclideanLin A).singularValues (e j)
  have hσr : ∀ j, ρ ≤ σ j := fun j =>
    hσ.trans ((toEuclideanLin A).singularValues_antitone (by simp [e, Fin.castLE]; omega))
  have hσpos : ∀ j, σ j ≠ 0 := fun j => (lt_of_lt_of_le hρ (hσr j)).ne'
  have h1 : Aᵀ * A * V = V * diagonal (fun j => σ j ^ 2) := by
    ext a j
    have h := congrFun (transpose_mul_self_mulVec_rightSingularVectors A (e j)) a
    have h' : (Aᵀ * A * V) a j =
        ((Aᵀ * A) *ᵥ WithLp.ofLp (rightSingularVectors A (e j))) a := by
      rfl
    rw [h', h, Matrix.mul_diagonal]
    simp [V, σ, mul_comm]
  have h1T : Vᵀ * (Aᵀ * A) = diagonal (fun j => σ j ^ 2) * Vᵀ := by
    have := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  let D' : Matrix (Fin r) (Fin r) ℝ := diagonal fun j => (σ j)⁻¹
  have hD : D' * diagonal σ = 1 := by
    simp only [D', diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext j
    exact inv_mul_cancel₀ (hσpos j)
  have hD2 : D' * diagonal (fun j => σ j ^ 2) * D' = 1 := by
    simp only [D', diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext j
    have := hσpos j
    field_simp
  have hT : truncation A r = A * V * Vᵀ := by
    rw [truncation, Matrix.mul_assoc, ← hVV, Matrix.mul_assoc]
  refine ⟨A * V * D', V, σ, ?_, hV, hσr, ?_, ?_⟩
  · have : (A * V * D')ᵀ * (A * V * D') = D' * (Vᵀ * (Aᵀ * A * V)) * D' := by
      simp [D', Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, h1, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
    exact hD2
  · have h3 : A * V * D' * diagonal σ * Vᵀ = A * (V * Vᵀ) := by
      rw [Matrix.mul_assoc (A * V), hD, Matrix.mul_one, Matrix.mul_assoc]
    rw [h3, hVV, truncation, Matrix.mul_assoc]
  · have hEV : (A - A * V * Vᵀ) * V = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc (A * V), hV, Matrix.mul_one, sub_self]
    have hVE : Vᵀ * Aᵀ * (A - A * V * Vᵀ) = 0 := by
      calc Vᵀ * Aᵀ * (A - A * V * Vᵀ)
          = Vᵀ * (Aᵀ * A) - Vᵀ * (Aᵀ * A * V) * Vᵀ := by
            simp only [Matrix.mul_sub, Matrix.mul_assoc]
        _ = 0 := by
            rw [h1, h1T, ← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul, sub_self]
    have hUE : (A * V * D')ᵀ * (A - A * V * Vᵀ) = 0 := by
      have : (A * V * D')ᵀ = D' * (Vᵀ * Aᵀ) := by
        simp [D', Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, Matrix.mul_assoc D', hVE, Matrix.mul_zero]
    have t1 : A * V * D' * (A * V * D')ᵀ * (A - A * V * Vᵀ) = 0 := by
      rw [Matrix.mul_assoc, hUE, Matrix.mul_zero]
    have t2 : (A - A * V * Vᵀ) * V * Vᵀ = 0 := by rw [hEV, Matrix.zero_mul]
    have t3 : A * V * D' * (A * V * D')ᵀ * (A - A * V * Vᵀ) * V * Vᵀ = 0 := by
      rw [t1, Matrix.zero_mul, Matrix.zero_mul]
    rw [hT, tangentProj_apply, t3, t1, t2]
    simp

omit [DecidableEq m] in
/-- **Quasi-optimality of matrix DLRA without a condition on `‖Y - X‖`** (the statement of
`dlra_quasiOptimal_matrix`, whose docstring names the source, with two hypotheses removed). Let
`X(t) = T_r(A(t))` be a differentiable best rank-`r` approximation with `σ_r(A(t)) ≥ ρ`,
`‖X(t) - A(t)‖_F ≤ ρ/16` and `‖Ȧ‖_F ≤ μ`, and let `Y = U S Vᵀ` solve the DLRA equation
`Ẏ = P(Y) Ȧ` with `Y(0) = X(0)`. Then, for every `t ∈ [0, T]`,
`‖Y(t) - X(t)‖_F ≤ 2 β e^{β t} ∫₀ᵗ ‖X(s) - A(s)‖_F ds`, `β = 8 μ / ρ`. Neither continuity of
the derivative of `X` nor smallness of `‖Y - X‖_F` is assumed. -/
theorem dlra_norm_sub_truncation_le_integral {r : ℕ} (hr : 0 < r)
    {A A' X X' Y : ℝ → Matrix m n ℝ} {T μ ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t)
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 16)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, ‖Y t - X t‖ ≤
      2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  classical
  intro t0 ht0
  rcases eq_or_lt_of_le ht0.1 with h0 | hpos
  · subst h0
    simp [hY₀]
  have hT : 0 < T := hpos.trans_le ht0.2
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ 0 ⟨le_rfl, hT.le⟩)
  have hfac : ∀ t ∈ Icc (0 : ℝ) T, ∃ (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (σ₀ : Fin r → ℝ), U₀ᵀ * U₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧ (∀ i, ρ ≤ σ₀ i) ∧
      X t = U₀ * diagonal σ₀ * V₀ᵀ ∧ tangentProj U₀ V₀ (A t - X t) = 0 := fun t ht => by
    obtain ⟨U₀, V₀, σ₀, h1, h2, h3, h4, h5⟩ := truncation_factor hr hρ (hσ t ht)
    rw [← hXbest t ht] at h4 h5
    exact ⟨U₀, V₀, σ₀, h1, h2, h3, h4, h5⟩
  choose! UX VX σX hUX hVX hσX hXeq hPE using hfac
  obtain ⟨PX, hPXdef⟩ : ∃ PX : ℝ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ,
      ∀ t, PX t = tangentProj (UX t) (VX t) := ⟨_, fun _ => rfl⟩
  obtain ⟨PY, hPYdef⟩ : ∃ PY : ℝ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ,
      ∀ t, PY t = tangentProj (U t) (V t) := ⟨_, fun _ => rfl⟩
  have hPXproj : ∀ t ∈ Icc (0 : ℝ) T, IsOrthProj (PX t) := fun t ht => by
    rw [hPXdef]; exact isOrthProj_tangentProj (hUX t ht) (hVX t ht)
  have hPYproj : ∀ t ∈ Icc (0 : ℝ) T, IsOrthProj (PY t) := fun t ht => by
    rw [hPYdef]; exact isOrthProj_tangentProj (hUV t ht).1 (hUV t ht).2.1
  have hPXE : ∀ t ∈ Icc (0 : ℝ) T, PX t (A t - X t) = 0 := fun t ht => by
    rw [hPXdef]; exact hPE t ht
  have hLipXX : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ B : Matrix m n ℝ,
      ‖PX s B - PX t B‖ ≤ 2 * ρ⁻¹ * ‖X s - X t‖ * ‖B‖ := fun s hs t ht B => by
    rw [hPXdef, hPXdef]
    have h := tangentProj_sub_le hρ (hσX t ht) (hUX t ht) (hVX t ht) (hUX s hs) (hVX s hs)
      (S' := diagonal (σX s)) B
    rwa [← hXeq s hs, ← hXeq t ht] at h
  have hLipYX : ∀ s ∈ Icc (0 : ℝ) T, ∀ B : Matrix m n ℝ,
      ‖PY s B - PX s B‖ ≤ 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖B‖ := fun s hs B => by
    rw [hPXdef, hPYdef]
    obtain ⟨hU1, hV1, hYe⟩ := hUV s hs
    have h := tangentProj_sub_le hρ (hσX s hs) (hUX s hs) (hVX s hs) hU1 hV1
      (S' := S s) B
    rwa [← hXeq s hs, ← hYe] at h
  have htan : ∀ t ∈ Icc (0 : ℝ) T, PX t (X' t) = X' t := fun t ht => by
    have hXd : HasDerivWithinAt X (X' t) (Icc 0 T) t := (hX t ht).hasDerivWithinAt
    have hφ : HasDerivWithinAt (fun s => (1 - PX t) (X s - X t)) ((1 - PX t) (X' t))
        (Icc 0 T) t :=
      (1 - PX t).hasFDerivAt.comp_hasDerivWithinAt t (hXd.sub_const (X t))
    have hb : ∀ s ∈ Icc (0 : ℝ) T,
        ‖(1 - PX t) (X s - X t)‖ ≤ ‖X s - X t‖ * (ρ⁻¹ * ‖X s - X t‖) := fun s hs => by
      have hn := Curvature.koch_lubich_normal hρ (hUX s hs) (hVX s hs) (hUX t ht) (hVX t ht)
        (Curvature.diagonal_bounded_below hρ.le (hσX s hs)) (S' := diagonal (σX t))
      rw [← hXeq s hs, ← hXeq t ht] at hn
      have hz0 : (1 - PX t) (X s - X t) =
          (1 - UX t * (UX t)ᵀ) * (X s - X t) * (1 - VX t * (VX t)ᵀ) := by
        rw [sub_apply, one_apply_eq_self, hPXdef]
        exact sub_eq_iff_eq_add'.mpr (tangentProj_add_normal (UX t) (VX t) (X s - X t)).symm
      have hz : (1 - PX t) (X s - X t) =
          -((1 - UX t * (UX t)ᵀ) * (X t - X s) * (1 - VX t * (VX t)ᵀ)) := by
        rw [hz0, ← neg_sub (X t) (X s), Matrix.mul_neg, Matrix.neg_mul]
      rw [hz, norm_neg, norm_sub_rev (X s) (X t)]
      calc _ ≤ _ := hn
        _ = _ := by ring
    have hg : ContinuousWithinAt (fun s => ρ⁻¹ * ‖X s - X t‖) (Icc 0 T) t :=
      continuousWithinAt_const.mul ((hXd.continuousWithinAt.sub continuousWithinAt_const).norm)
    have h := norm_deriv_le_of_slope_bound hT ht hφ hXd (by simp) hg hb
    simp only [sub_self, norm_zero, mul_zero] at h
    have h0 : (1 - PX t) (X' t) = 0 := norm_le_zero_iff.mp h
    rw [sub_apply, one_apply_eq_self, sub_eq_zero] at h0
    exact h0.symm
  have hdef : ∀ t ∈ Icc (0 : ℝ) T,
      ‖PX t (A' t - X' t)‖ ≤ 2 * ρ⁻¹ * ‖X' t‖ * ‖A t - X t‖ := fun t ht => by
    have hXd : HasDerivWithinAt X (X' t) (Icc 0 T) t := (hX t ht).hasDerivWithinAt
    have hAd : HasDerivWithinAt A (A' t) (Icc 0 T) t := (hA t ht).hasDerivWithinAt
    have hφ : HasDerivWithinAt (fun s => PX t (A s - X s - (A t - X t))) (PX t (A' t - X' t))
        (Icc 0 T) t :=
      (PX t).hasFDerivAt.comp_hasDerivWithinAt t ((hAd.sub hXd).sub_const (A t - X t))
    have hb : ∀ s ∈ Icc (0 : ℝ) T, ‖PX t (A s - X s - (A t - X t))‖ ≤
        ‖X s - X t‖ * (2 * ρ⁻¹ * ‖A s - X s‖) := fun s hs => by
      have e1 : PX t (A s - X s - (A t - X t)) = PX t (A s - X s) - PX s (A s - X s) := by
        rw [map_sub, hPXE t ht, hPXE s hs, sub_zero]
      rw [e1, norm_sub_rev (X s) (X t)]
      calc _ ≤ _ := hLipXX t ht s hs _
        _ = _ := by ring
    have hg : ContinuousWithinAt (fun s => 2 * ρ⁻¹ * ‖A s - X s‖) (Icc 0 T) t :=
      continuousWithinAt_const.mul ((hAd.continuousWithinAt.sub hXd.continuousWithinAt).norm)
    have h := norm_deriv_le_of_slope_bound hT ht hφ hXd (by simp) hg hb
    calc _ ≤ _ := h
      _ = _ := by ring
  -- velocity bound for `X'`
  have hX'b : ∀ t ∈ Icc (0 : ℝ) T, ‖X' t‖ ≤ 8 * μ / 7 := fun t ht => by
    have hE : ρ⁻¹ * ‖A t - X t‖ ≤ 1 / 16 := by
      rw [inv_mul_le_iff₀ hρ, norm_sub_rev]
      linarith [hd t ht]
    have h1 : X' t = PX t (A' t) - PX t (A' t - X' t) := by
      rw [map_sub, htan t ht]; abel
    have h2 : ‖PX t (A' t)‖ ≤ μ := ((hPXproj t ht).norm_le _).trans (hμ t ht)
    have h3 := hdef t ht
    have h4 : 2 * ρ⁻¹ * ‖X' t‖ * ‖A t - X t‖ ≤ ‖X' t‖ / 8 := by
      have := mul_le_mul_of_nonneg_left hE (norm_nonneg (X' t))
      nlinarith
    have h5 : ‖X' t‖ ≤ ‖PX t (A' t)‖ + ‖PX t (A' t - X' t)‖ := by
      calc ‖X' t‖ = ‖PX t (A' t) - PX t (A' t - X' t)‖ := by rw [← h1]
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hbest : ∀ t ∈ Icc (0 : ℝ) T,
      ‖PX t (A' t - X' t)‖ ≤ 16 * μ / (7 * ρ) * ‖X t - A t‖ := fun t ht => by
    refine (hdef t ht).trans ?_
    rw [norm_sub_rev (A t)]
    have h1 := hX'b t ht
    have h2 : 2 * ρ⁻¹ * ‖X' t‖ ≤ 2 * ρ⁻¹ * (8 * μ / 7) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc _ ≤ 2 * ρ⁻¹ * (8 * μ / 7) * ‖X t - A t‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := by field_simp; ring
  -- the comparison on `[0, t0]`
  have hT0 : t0 ≤ T := ht0.2
  have hIcc : Icc (0 : ℝ) t0 ⊆ Icc 0 T := Icc_subset_Icc_right hT0
  obtain ⟨ηc, hηc⟩ : ∃ ηc : ℝ → ℝ, ∀ s, ηc s = ‖X (Set.projIcc 0 T hT.le s) -
      A (Set.projIcc 0 T hT.le s)‖ := ⟨_, fun _ => rfl⟩
  have hηcont : Continuous ηc := by
    have hc : ContinuousOn (fun x => ‖X x - A x‖) (Icc 0 T) := fun x hx =>
      ((hX x hx).continuousAt.continuousWithinAt.sub
        (hA x hx).continuousAt.continuousWithinAt).norm
    have := hc.comp_continuous (continuous_subtype_val.comp (continuous_projIcc (h := hT.le)))
      (fun s => (Set.projIcc 0 T hT.le s).2)
    have e : ηc = fun s => ‖X (Set.projIcc 0 T hT.le s) - A (Set.projIcc 0 T hT.le s)‖ :=
      funext hηc
    rw [e]
    exact this
  have hηeq : ∀ s ∈ Icc (0 : ℝ) T, ηc s = ‖X s - A s‖ := fun s hs => by
    rw [hηc, Set.projIcc_of_mem _ hs]
  have hmemT : ∀ s ∈ Ico (0 : ℝ) t0, s ∈ Icc 0 T := fun s hs => ⟨hs.1, hs.2.le.trans hT0⟩
  have hYsol : ODESolution (fun t _ => PY t (A' t)) Y 0 t0 :=
    ⟨hY.cont.mono hIcc, fun s hs => by
      have := hY.deriv s ⟨hs.1, hs.2.trans_le hT0⟩
      rwa [← hPYdef] at this⟩
  have hF : IsLipschitzField (fun t (_ : Matrix m n ℝ) => A' t) 0 := fun t x y => by simp
  have hXc : ContinuousOn X (Icc 0 t0) := fun x hx =>
    (hX x (hIcc hx)).continuousAt.continuousWithinAt
  have h₁ : ∀ s ∈ Ico (0 : ℝ) t0, ‖PY s (A' s - X' s)‖ ≤
      2 * ρ⁻¹ * μ * ‖Y s - X s‖ + 16 * μ / (7 * ρ) * ηc s := fun s hs => by
    have hsT := hmemT s hs
    rw [hηeq s hsT]
    have hsplit : A' s - X' s = (A' s - PX s (A' s)) + PX s (A' s - X' s) := by
      rw [map_sub, htan s hsT]; abel
    have hz : PX s (A' s - PX s (A' s)) = 0 := by
      rw [map_sub, (hPXproj s hsT).idem, sub_self]
    have t1 : ‖PY s (A' s - PX s (A' s))‖ ≤ 2 * ρ⁻¹ * μ * ‖Y s - X s‖ := by
      have e : PY s (A' s - PX s (A' s)) =
          PY s (A' s - PX s (A' s)) - PX s (A' s - PX s (A' s)) := by rw [hz, sub_zero]
      rw [e]
      refine (hLipYX s hsT _).trans ?_
      have hn : ‖A' s - PX s (A' s)‖ ≤ μ := by
        have := (hPXproj s hsT).compl.norm_le (A' s)
        simp only [sub_apply, one_apply_eq_self] at this
        exact this.trans (hμ s hsT)
      have := norm_nonneg (Y s - X s)
      have := inv_pos.2 hρ
      calc 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖A' s - PX s (A' s)‖
          ≤ 2 * ρ⁻¹ * ‖Y s - X s‖ * μ := by gcongr
        _ = _ := by ring
    have t2 : ‖PY s (PX s (A' s - X' s))‖ ≤ 16 * μ / (7 * ρ) * ‖X s - A s‖ :=
      ((hPYproj s hsT).norm_le _).trans (hbest s hsT)
    rw [hsplit, map_add]
    refine (norm_add_le _ _).trans ?_
    linarith
  have h₂ : ∀ s ∈ Ico (0 : ℝ) t0, ‖(1 - PY s) (X' s)‖ ≤
      2 * ρ⁻¹ * (8 * μ / 7) * ‖Y s - X s‖ + (fun _ : ℝ => (0 : ℝ)) s := fun s hs => by
    have hsT := hmemT s hs
    have e : (1 - PY s) (X' s) = -(PY s (X' s) - PX s (X' s)) := by
      rw [sub_apply, one_apply_eq_self, neg_sub, htan s hsT]
    rw [e, norm_neg, add_zero]
    refine (hLipYX s hsT _).trans ?_
    have := norm_nonneg (Y s - X s)
    have := inv_pos.2 hρ
    calc 2 * ρ⁻¹ * ‖Y s - X s‖ * ‖X' s‖ ≤ 2 * ρ⁻¹ * ‖Y s - X s‖ * (8 * μ / 7) := by
          gcongr; exact hX'b s hsT
      _ = _ := by ring
  have hcmp := ODESolution.dlra_norm_sub_le_of_comparison_integral (P := PY)
    (F := fun t (_ : Matrix m n ℝ) => A' t) (Y := Y) (a := 0) (b := t0) (L := 0)
    (κ₁ := 2 * ρ⁻¹ * μ) (κ₂ := 2 * ρ⁻¹ * (8 * μ / 7)) (δ := 0)
    (η₁ := fun s => 16 * μ / (7 * ρ) * ηc s) (η₂ := fun _ => 0)
    (continuous_const.mul hηcont) continuous_const hF hYsol
    (fun s hs => hPYproj s (hmemT s hs)) hXc (fun s hs => (hX s (hmemT s hs)).hasDerivWithinAt)
    h₁ h₂ (by rw [hY₀, sub_self, norm_zero]) t0 ⟨ht0.1, le_rfl⟩
  have hρμ : 0 ≤ ρ⁻¹ * μ := by positivity
  have hK : 0 ≤ 0 + 2 * ρ⁻¹ * μ + 2 * ρ⁻¹ * (8 * μ / 7) := by positivity
  have hc0 : 0 ≤ 16 * μ / (7 * ρ) := by positivity
  have hgb := gronwallIntegralBound_le (δ := 0)
    (η := fun s => 16 * μ / (7 * ρ) * ηc s + (fun _ : ℝ => (0 : ℝ)) s)
    ((continuous_const.mul hηcont).add continuous_const) hK ht0.1 (fun s hs => by
      have : 0 ≤ ηc s := by rw [hηeq s (hIcc hs)]; exact norm_nonneg _
      simp only [add_zero]
      positivity)
  have hI : 0 ≤ ∫ s in (0 : ℝ)..t0, ‖X s - A s‖ :=
    intervalIntegral.integral_nonneg ht0.1 (fun _ _ => norm_nonneg _)
  have hJ : ∫ s in (0 : ℝ)..t0, (16 * μ / (7 * ρ) * ηc s + (fun _ : ℝ => (0 : ℝ)) s) =
      16 * μ / (7 * ρ) * ∫ s in (0 : ℝ)..t0, ‖X s - A s‖ := by
    simp only [add_zero]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht0.1] at hs
    exact hηeq s (hIcc hs)
  have hKle : 0 + 2 * ρ⁻¹ * μ + 2 * ρ⁻¹ * (8 * μ / 7) ≤ 8 * μ / ρ := by
    have e1 : 8 * μ / ρ = 8 * (ρ⁻¹ * μ) := by field_simp
    rw [e1]; linarith
  have hcle : 16 * μ / (7 * ρ) ≤ 2 * (8 * μ / ρ) := by
    have : 16 * μ / (7 * ρ) = 16 / 7 * (ρ⁻¹ * μ) := by field_simp
    rw [this, div_eq_inv_mul]; linarith
  have hexp : Real.exp ((0 + 2 * ρ⁻¹ * μ + 2 * ρ⁻¹ * (8 * μ / 7)) * (t0 - 0)) ≤
      Real.exp (8 * μ / ρ * t0) := by
    apply Real.exp_le_exp.2
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_right hKle ht0.1
  refine hcmp.trans (hgb.trans ?_)
  rw [hJ]
  calc _ ≤ Real.exp (8 * μ / ρ * t0) * (2 * (8 * μ / ρ) * ∫ s in (0 : ℝ)..t0, ‖X s - A s‖) :=
        mul_le_mul hexp (by rw [zero_add]; exact mul_le_mul_of_nonneg_right hcle hI)
          (by rw [zero_add]; positivity) (Real.exp_pos _).le
    _ = _ := by ring

set_option linter.unusedDecidableInType false in
/-- **Quasi-optimality of matrix DLRA** (source: Koch–Lubich, SIAM J. Matrix Anal. Appl. 29
(2007), Theorem 5.1). Let `X(t) = T_r(A(t))` be a `C¹` best rank-`r` approximation with
`σ_r(X(t)) ≥ ρ` and `‖X(t) - A(t)‖_F ≤ ρ/16`, `‖Ȧ‖_F ≤ μ`, and let `Y = U S Vᵀ` solve the DLRA
equation `Ẏ = P(Y) Ȧ` with `Y(0) = X(0)`. While `‖Y - X‖_F ≤ ρ/16`,
`‖Y(t) - X(t)‖_F ≤ 2 β e^{β t} ∫₀ᵗ ‖X(s) - A(s)‖_F ds`, `β = 8 μ / ρ`.
This is the recorded form of the statement, with the redundant hypotheses that the derivative of
`X` is continuous and that `‖Y s - X s‖ ≤ ρ / 16` on `[0, t]`, and with the instance
`DecidableEq m`, which its type does not use; `dlra_norm_sub_truncation_le_integral` is the same
statement without them. -/
theorem dlra_quasiOptimal_matrix {r : ℕ} (hr : 0 < r) {A A' X X' Y : ℝ → Matrix m n ℝ}
    {T μ ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t) (hX'c : ContinuousOn X' (Icc 0 T))
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 16)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, ‖Y s - X s‖ ≤ ρ / 16) →
      ‖Y t - X t‖ ≤
        2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  have _ := hX'c
  let _ : DecidableEq m := inferInstance
  exact fun t ht _ =>
    dlra_norm_sub_truncation_le_integral hr hρ hA hμ hXbest hX hσ hd hUV hY hY₀ t ht

end QuasiOptimal

end LeanDLRA
