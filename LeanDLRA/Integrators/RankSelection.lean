import LeanDLRA.Classical.SVD
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Dynamics.ContinuousDLRA

/-!
# Rank selection: retained singular values, basis enrichment, ties, and Galerkin quasi-optimality

Statements behind the rank decisions of rank-adaptive integrators: what the tolerance rule
`epsRank` keeps, how much one new basis vector can gain, why the truncated SVD `truncation` is
not continuous at equal singular values, and a quasi-optimality bound for the Galerkin flow in a
fixed subspace.

## Main results

* `singularValues_pred_epsRank_gt`: if `r₁ = epsRank θ A > 0` for `A ∈ ℝ^{m×n}`, the smallest
  retained singular value satisfies `σ_{r₁-1}(A) > θ / √(n - r₁ + 1)` (singular values counted
  from `σ₀`).
* `norm_sq_sub_specNorm_sq_le_norm_sq_enrich`: for a unit vector `w` with `Uᵀ w = 0`, passing
  from `1 - U Uᵀ` to `1 - U Uᵀ - w wᵀ` lowers `‖(1 - U Uᵀ) G‖²` (Frobenius norm) by at most the
  squared spectral norm of `(1 - U Uᵀ) G`.
* `norm_sq_enrich_ge`: the same statement with the additional hypothesis `Uᵀ U = 1`, that is,
  for the enlargement of an orthonormal basis `U` by `w`.
* `exists_enrich_top_singular`: if `(1 - U Uᵀ) G ≠ 0`, some unit vector `w ⊥ U` attains this
  bound with equality.
* `not_continuousAt_truncation_tie`: the rank-one truncation of `2 × 2` matrices is not
  continuous at the identity matrix.
* `galerkin_quasiOptimal`: the Galerkin flow `YS' = R F(t, YS)`, `YS t₀ = R (A t₀)`, satisfies
  `‖YS t - A t‖ ≤ ‖A t - R (A t)‖ + (e^{L (t - t₀)} - 1) d` on `[t₀, t₁]`, where `d` bounds
  `‖A s - R (A s)‖` on the interval.
-/

open Set Finset Matrix

namespace LeanDLRA

section Truncation

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Minimal-rank truncation keeps singular values above `θ/√(n - r₁ + 1)`** (source: OP-RA-29
(ii)). If the tolerance rule selects rank `r₁ = epsRank θ A > 0`, the smallest retained singular
value satisfies `σ_{r₁-1}(A) > θ / √(n - r₁ + 1)`, so truncation never keeps negligible
directions. -/
theorem singularValues_pred_epsRank_gt [DecidableEq n] (A : Matrix m n ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hpos : 0 < epsRank θ A) :
    θ / √((Fintype.card n - epsRank θ A + 1 : ℕ) : ℝ) <
      (toEuclideanLin A).singularValues (epsRank θ A - 1) := by
  have h1 : θ < distLR (epsRank θ A - 1) A := lt_distLR_of_lt_epsRank (by omega)
  have h2 : distLR (epsRank θ A - 1) A = √(∑ i ∈ Ico (epsRank θ A - 1) (Fintype.card n),
      (toEuclideanLin A).singularValues i ^ 2) := infDist_setOf_rank_le A _
  rw [h2] at h1
  set k := epsRank θ A - 1 with hk
  set σ := (toEuclideanLin A).singularValues k with hσ
  have hσ0 : 0 ≤ σ := (toEuclideanLin A).singularValues_nonneg _
  rcases le_or_gt (Fintype.card n) k with hnk | hnk
  · rw [Finset.Ico_eq_empty_of_le hnk, Finset.sum_empty, Real.sqrt_zero] at h1
    exact absurd h1 (not_lt.2 hθ)
  · have hc : Fintype.card n - epsRank θ A + 1 = Fintype.card n - k := by omega
    have hcpos : (0 : ℝ) < ((Fintype.card n - epsRank θ A + 1 : ℕ) : ℝ) := by
      rw [hc]; exact_mod_cast Nat.sub_pos_of_lt hnk
    have hsum : ∑ i ∈ Ico k (Fintype.card n), (toEuclideanLin A).singularValues i ^ 2 ≤
        ((Fintype.card n - epsRank θ A + 1 : ℕ) : ℝ) * σ ^ 2 := by
      have := Finset.sum_le_card_nsmul (Ico k (Fintype.card n))
        (fun i => (toEuclideanLin A).singularValues i ^ 2) (σ ^ 2)
        (fun i hi => sq_singularValues_antitone _ (Finset.mem_Ico.1 hi).1)
      rw [Nat.card_Ico, nsmul_eq_mul, ← hc] at this
      exact this
    have h3 : θ < √((Fintype.card n - epsRank θ A + 1 : ℕ) : ℝ) * σ := by
      calc θ < _ := h1
        _ ≤ √(((Fintype.card n - epsRank θ A + 1 : ℕ) : ℝ) * σ ^ 2) := Real.sqrt_le_sqrt hsum
        _ = _ := by rw [Real.sqrt_mul hcpos.le, Real.sqrt_sq hσ0]
    rw [div_lt_iff₀ (Real.sqrt_pos.2 hcpos)]
    linarith

private theorem norm_wT_mul_le [DecidableEq n] {w : Matrix m (Fin 1) ℝ}
    (hw : wᵀ * w = 1) (R : Matrix m n ℝ) : ‖wᵀ * R‖ ≤ Curvature.specNorm R := by
  classical
  have hw1 : ‖w‖ = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by
      rw [Curvature.frob_sq_eq_trace, hw]; simp
    nlinarith [norm_nonneg w]
  have : wᵀ * R = (Rᵀ * w)ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [this, Frobenius.norm_transpose]
  have h := Curvature.frob_mul_le Rᵀ w
  rwa [Curvature.specNorm_transpose, hw1, mul_one] at h

private theorem norm_sq_enrich_eq [DecidableEq m] {k : Type*} [Fintype k] {U : Matrix m k ℝ}
    (G : Matrix m n ℝ)
    {w : Matrix m (Fin 1) ℝ} (hw : wᵀ * w = 1) (hUw : Uᵀ * w = 0) :
    ‖(1 - U * Uᵀ - w * wᵀ) * G‖ ^ 2 =
      ‖(1 - U * Uᵀ) * G‖ ^ 2 - ‖wᵀ * ((1 - U * Uᵀ) * G)‖ ^ 2 := by
  have hwU : wᵀ * U = 0 := by
    have := congrArg Matrix.transpose hUw
    simpa [Matrix.transpose_mul] using this
  have hwR : wᵀ * ((1 - U * Uᵀ) * G) = wᵀ * G := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hwU]
    simp
  have hX : (1 - U * Uᵀ - w * wᵀ) * G = (1 - U * Uᵀ) * G - w * (wᵀ * ((1 - U * Uᵀ) * G)) := by
    rw [hwR, Matrix.sub_mul (1 - U * Uᵀ), Matrix.mul_assoc]
  generalize (1 - U * Uᵀ) * G = R at hX ⊢
  rw [hX, norm_sub_sq_real, Frobenius.inner_mul_left', real_inner_self_eq_norm_sq,
    Frobenius.norm_mul_of_orthonormal hw]
  ring

/-- **One-vector enrichment gains at most `σ₁` of the residual, for any `U`** (the statement of
`norm_sq_enrich_ge`, whose docstring names the source, without the hypothesis `Uᵀ U = 1`). For a
unit vector `w` with `Uᵀ w = 0`,
`‖(I - U Uᵀ) G‖_F² - ‖(I - U Uᵀ) G‖₂² ≤ ‖(I - U Uᵀ - w wᵀ) G‖_F²`. The inequality uses
`wᵀ w = 1` and `Uᵀ w = 0` only; the columns of `U` need not be orthonormal. -/
theorem norm_sq_sub_specNorm_sq_le_norm_sq_enrich [DecidableEq m] [DecidableEq n] {k : Type*}
    [Fintype k] {U : Matrix m k ℝ} (G : Matrix m n ℝ) {w : Matrix m (Fin 1) ℝ}
    (hw : wᵀ * w = 1) (hUw : Uᵀ * w = 0) :
    ‖(1 - U * Uᵀ) * G‖ ^ 2 - Curvature.specNorm ((1 - U * Uᵀ) * G) ^ 2 ≤
      ‖(1 - U * Uᵀ - w * wᵀ) * G‖ ^ 2 := by
  rw [norm_sq_enrich_eq G hw hUw]
  have h3 : ‖wᵀ * ((1 - U * Uᵀ) * G)‖ ^ 2 ≤ Curvature.specNorm ((1 - U * Uᵀ) * G) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_wT_mul_le hw _) 2
  linarith

/-- **One-vector enrichment gains at most `σ₁` of the residual** (source: OP-RA-27). Enlarging
an orthonormal basis `U` by one unit vector `w ⊥ U` reduces `‖(I - U Uᵀ) G‖_F²` by at most
`‖(I - U Uᵀ) G‖₂² = σ₁((I - U Uᵀ) G)²`.
This is the recorded form of the statement, with the redundant hypothesis `Uᵀ U = 1`;
`norm_sq_sub_specNorm_sq_le_norm_sq_enrich` is the same statement without it. -/
theorem norm_sq_enrich_ge [DecidableEq m] [DecidableEq n] {k : Type*} [Fintype k]
    [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (G : Matrix m n ℝ)
    {w : Matrix m (Fin 1) ℝ} (hw : wᵀ * w = 1) (hUw : Uᵀ * w = 0) :
    ‖(1 - U * Uᵀ) * G‖ ^ 2 - Curvature.specNorm ((1 - U * Uᵀ) * G) ^ 2 ≤
      ‖(1 - U * Uᵀ - w * wᵀ) * G‖ ^ 2 := by
  have _ := hU
  exact norm_sq_sub_specNorm_sq_le_norm_sq_enrich G hw hUw

/-- The hypotheses of `norm_sq_sub_specNorm_sq_le_norm_sq_enrich` hold for `U = e₁` and
`w = e₂` in `ℝ^{2×1}` and every `G ∈ ℝ^{2×2}`. -/
example (G : Matrix (Fin 2) (Fin 2) ℝ) (U w : Matrix (Fin 2) (Fin 1) ℝ) (hU : U = !![1; 0])
    (hw : w = !![0; 1]) :
    ‖(1 - U * Uᵀ) * G‖ ^ 2 - Curvature.specNorm ((1 - U * Uᵀ) * G) ^ 2 ≤
      ‖(1 - U * Uᵀ - w * wᵀ) * G‖ ^ 2 := by
  subst hU hw
  refine norm_sq_sub_specNorm_sq_le_norm_sq_enrich G ?_ ?_
  · ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem norm_col_eq {p : Type*} [Fintype p] (v : EuclideanSpace ℝ p) :
    ‖(Matrix.of fun i (_ : Fin 1) => v i : Matrix p (Fin 1) ℝ)‖ = ‖v‖ := by
  have h : ‖(Matrix.of fun i (_ : Fin 1) => v i : Matrix p (Fin 1) ℝ)‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [Curvature.frob_sq_eq_trace, EuclideanSpace.norm_sq_eq]
    simp [Matrix.trace, Matrix.mul_apply, sq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

private theorem exists_unit_top [DecidableEq n] {k : Type*}
    {U : Matrix m k ℝ} {R : Matrix m n ℝ} (hR : R ≠ 0) (hUR : Uᵀ * R = 0) :
    ∃ w : Matrix m (Fin 1) ℝ, wᵀ * w = 1 ∧ Uᵀ * w = 0 ∧ ‖wᵀ * R‖ = Curvature.specNorm R := by
  have hσ : 0 < Curvature.specNorm R := by
    rcases (Curvature.specNorm_nonneg R).eq_or_lt with h | h
    · exfalso
      apply hR
      ext i j
      have := Curvature.norm_toEuclideanLin_le R (EuclideanSpace.single j 1)
      rw [← h, zero_mul] at this
      have h0 := norm_le_zero_iff.1 this
      have := congrFun (congrArg (fun v : EuclideanSpace ℝ m => (v : m → ℝ)) h0) i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    · exact h
  have hn : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hR (by ext i j; exact h.elim j)
  have hd : 0 < Module.finrank ℝ (EuclideanSpace ℝ n) := by
    simpa [finrank_euclideanSpace] using Fintype.card_pos
  set e := (Matrix.toEuclideanLin R).rightSingularBasis ⟨0, hd⟩ with he
  have he1 : ‖e‖ = 1 := OrthonormalBasis.norm_eq_one _ _
  have heσ : ‖Matrix.toEuclideanLin R e‖ = Curvature.specNorm R := by
    rw [he, LinearMap.norm_apply_rightSingularBasis, EckartYoung.specNorm_eq_singularValues_zero]
  set xc : Matrix n (Fin 1) ℝ := Matrix.of fun j _ => e j with hxc
  have hRx : R * xc = Matrix.of fun i (_ : Fin 1) => (Matrix.toEuclideanLin R e) i := by
    ext i a
    simp [hxc, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hxc1 : ‖xc‖ = 1 := by rw [hxc, norm_col_eq, he1]
  have hRx1 : ‖R * xc‖ = Curvature.specNorm R := by rw [hRx, norm_col_eq, heσ]
  set w : Matrix m (Fin 1) ℝ := (Curvature.specNorm R)⁻¹ • (R * xc) with hwdef
  have hn1 : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, hRx1, norm_inv, Real.norm_of_nonneg hσ.le, inv_mul_cancel₀ hσ.ne']
  have hw : wᵀ * w = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by rw [hn1]; norm_num
    rw [Curvature.frob_sq_eq_trace] at h
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simpa [Matrix.trace] using h
  refine ⟨w, hw, ?_, le_antisymm (norm_wT_mul_le hw R) ?_⟩
  · rw [hwdef, Matrix.mul_smul, ← Matrix.mul_assoc, hUR, Matrix.zero_mul, smul_zero]
  · have hRxw : R * xc = Curvature.specNorm R • w := by
      rw [hwdef, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
    have h1 : inner ℝ (Rᵀ * w) xc = Curvature.specNorm R := by
      rw [Frobenius.inner_mul_left, Matrix.transpose_transpose, hRxw, inner_smul_right,
        real_inner_self_eq_norm_sq, hn1]
      ring
    have h2 := real_inner_le_norm (Rᵀ * w) xc
    rw [h1, hxc1, mul_one] at h2
    have : wᵀ * R = (Rᵀ * w)ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rwa [this, Frobenius.norm_transpose]

/-- **Enrichment by the top singular vector of the residual is optimal** (source: OP-RA-27;
rank-adaptive symplectic model reduction). If `R = (I - U Uᵀ) G ≠ 0`, its top left singular vector
`w` is orthogonal to `U` and attains the bound of `norm_sq_enrich_ge`, a reduction by exactly
`σ₁(R)²`. -/
theorem exists_enrich_top_singular [DecidableEq m] [DecidableEq n] {k : Type*} [Fintype k]
    [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (G : Matrix m n ℝ)
    (hR : (1 - U * Uᵀ) * G ≠ 0) :
    ∃ w : Matrix m (Fin 1) ℝ, wᵀ * w = 1 ∧ Uᵀ * w = 0 ∧
      ‖(1 - U * Uᵀ - w * wᵀ) * G‖ ^ 2 =
        ‖(1 - U * Uᵀ) * G‖ ^ 2 - Curvature.specNorm ((1 - U * Uᵀ) * G) ^ 2 := by
  have hUR : Uᵀ * ((1 - U * Uᵀ) * G) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU,
      Matrix.one_mul, sub_self, Matrix.zero_mul]
  obtain ⟨w, hw, hUw, hwR⟩ := exists_unit_top hR hUR
  exact ⟨w, hw, hUw, by rw [norm_sq_enrich_eq G hw hUw, hwR]⟩

end Truncation

section Tie

open EckartYoung

private theorem truncation_diagonal_one (d : Fin 2 → ℝ) (i j : Fin 2) (hij : i ≠ j)
    (hj : 0 < d j) (hlt : d j < d i) (a b : Fin 2) :
    truncation (diagonal d) 1 a b = if a = i ∧ b = i then d i else 0 := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  let i0 : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := ⟨0, by rw [hdim]; norm_num⟩
  set A : Matrix (Fin 2) (Fin 2) ℝ := diagonal d with hA
  set v := rightSingularVectors A i0 with hv
  have heig := transpose_mul_self_mulVec_rightSingularVectors A i0
  have hσ : (toEuclideanLin A).singularValues (i0 : ℕ) = Curvature.specNorm A := by
    rw [EckartYoung.specNorm_eq_singularValues_zero]
  have hAA : Aᵀ * A = diagonal (fun c => d c * d c) := by
    rw [hA, diagonal_transpose, diagonal_mul_diagonal]
  rw [hAA] at heig
  rw [hσ] at heig
  have hc : ∀ c, d c * d c * v c = Curvature.specNorm A ^ 2 * v c := fun c => by
    have := congrFun heig c
    simpa [mulVec_diagonal] using this
  have hσge : d i ≤ Curvature.specNorm A := by
    have h1 := Curvature.norm_toEuclideanLin_le A (EuclideanSpace.single i 1)
    have h2 : ‖(toEuclideanLin A (EuclideanSpace.single i 1)) i‖ ≤
        ‖toEuclideanLin A (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ _
    have h3 : (toEuclideanLin A (EuclideanSpace.single i 1)) i = d i := by
      simp [hA, mulVec_diagonal]
    rw [h3, Real.norm_of_nonneg (hj.le.trans hlt.le)] at h2
    simpa using h2.trans h1
  have hvj : v j = 0 := by
    have h := hc j
    have h' : (d j * d j - Curvature.specNorm A ^ 2) * v j = 0 := by linarith
    rcases mul_eq_zero.1 h' with h0 | h0
    · nlinarith
    · exact h0
  have hnorm : ∑ c, v c ^ 2 = 1 := by
    have h1 : ‖v‖ = 1 := (rightSingularVectors A).orthonormal.1 i0
    have h2 := EuclideanSpace.norm_sq_eq v
    rw [h1] at h2
    simpa using h2.symm
  have hvi : v i ^ 2 = 1 := by
    fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_two]
  have hsum : ∀ f : {k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) // (k : ℕ) < 1} → ℝ,
      ∑ k, f k = f ⟨i0, by simp [i0]⟩ := fun f => by
    refine Fintype.sum_eq_single _ fun k hk => ?_
    exfalso
    apply hk
    ext
    have := k.2
    simp only [i0]
    omega
  have hentry : truncation A 1 a b = d a * v a * v b := by
    simp only [truncation, topRightSingularVectors, Matrix.mul_apply, Matrix.transpose_apply,
      hsum]
    simp [hA, hv, i0, diagonal_apply]
  rw [hentry]
  have hv2 : ∀ c, c ≠ i → v c = 0 := fun c hc => by
    have : c = j := by
      fin_cases c <;> fin_cases i <;> fin_cases j <;> simp_all
    rw [this, hvj]
  by_cases ha : a = i
  · by_cases hb : b = i
    · subst ha hb; simp only [and_self, ite_true]; nlinarith
    · simp [hb, hv2 b hb]
  · simp [ha, hv2 a ha]

/-- **The truncated SVD is discontinuous at a tie** (source: OP-RA-45). At `I₂`, where
`σ₁ = σ₂`, the rank-one truncation is not continuous: for `s > 0`, `diag(1 + s, 1)` and
`diag(1, 1 + s)` truncate to `(1 + s) e₁e₁ᵀ` and `(1 + s) e₂e₂ᵀ`, whose limits as `s → 0` differ. -/
theorem not_continuousAt_truncation_tie :
    ¬ ContinuousAt (fun B : Matrix (Fin 2) (Fin 2) ℝ => truncation B 1) 1 := by
  intro hcont
  have hentry : Continuous fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 0 :=
    (continuous_apply 0).comp (continuous_apply 0)
  have hf : Filter.Tendsto (fun s : ℝ => (diagonal ![1 + s, 1] : Matrix (Fin 2) (Fin 2) ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hc : Continuous fun s : ℝ => (diagonal ![1 + s, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
      refine Continuous.matrix_diagonal (continuous_pi fun a => ?_)
      fin_cases a
      · exact continuous_const.add continuous_id
      · exact continuous_const
    have h0 : (diagonal ![1, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      ext a b; fin_cases a <;> fin_cases b <;> simp
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [add_zero] at h
    rwa [h0] at h
  have hg : Filter.Tendsto (fun s : ℝ => (diagonal ![1, 1 + s] : Matrix (Fin 2) (Fin 2) ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hc : Continuous fun s : ℝ => (diagonal ![1, 1 + s] : Matrix (Fin 2) (Fin 2) ℝ) := by
      refine Continuous.matrix_diagonal (continuous_pi fun a => ?_)
      fin_cases a
      · exact continuous_const
      · exact continuous_const.add continuous_id
    have h0 : (diagonal ![1, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      ext a b; fin_cases a <;> fin_cases b <;> simp
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [add_zero] at h
    rwa [h0] at h
  have h1 : Filter.Tendsto (fun s : ℝ => truncation (diagonal ![1 + s, 1]) 1 0 0)
      (nhdsWithin 0 (Ioi 0)) (nhds (truncation (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 0)) :=
    (hentry.tendsto _).comp (hcont.tendsto.comp hf)
  have h2 : Filter.Tendsto (fun s : ℝ => truncation (diagonal ![1, 1 + s]) 1 0 0)
      (nhdsWithin 0 (Ioi 0)) (nhds (truncation (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 0)) :=
    (hentry.tendsto _).comp (hcont.tendsto.comp hg)
  have e1 : truncation (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 0 = 1 := by
    refine tendsto_nhds_unique_of_eventuallyEq h1
      (g := fun s : ℝ => 1 + s) ?_ ?_
    · have : Filter.Tendsto (fun s : ℝ => 1 + s) (nhdsWithin 0 (Ioi 0)) (nhds (1 + 0)) :=
        (tendsto_const_nhds.add Filter.tendsto_id).mono_left nhdsWithin_le_nhds
      simpa using this
    · refine eventually_nhdsWithin_of_forall fun s hs => ?_
      have hs' : (0 : ℝ) < s := hs
      have := truncation_diagonal_one ![1 + s, 1] 0 1 (by decide) (by simp) (by simpa using hs') 0 0
      simpa using this
  have e2 : truncation (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 0 = 0 := by
    refine tendsto_nhds_unique_of_eventuallyEq h2
      (g := fun _ : ℝ => 0) tendsto_const_nhds ?_
    refine eventually_nhdsWithin_of_forall fun s hs => ?_
    have hs' : (0 : ℝ) < s := hs
    have := truncation_diagonal_one ![1, 1 + s] 1 0 (by decide) (by simp) (by simpa using hs') 0 0
    simpa using this
  rw [e1] at e2
  exact one_ne_zero e2

end Tie

section Distance

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

end Distance

section Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L t₀ t₁ : ℝ} {A : ℝ → E}

/-- **Céa lemma for Galerkin flows** (source: research idea; continuous analogue of
`implicitGalerkin_cea`). The Galerkin flow `YS' = R F(t, YS)`, `YS(t₀) = R A(t₀)`, satisfies
`‖YS(t) - A(t)‖ ≤ ‖(1 - R) A(t)‖ + (e^{L(t - t₀)} - 1) sup_s ‖(1 - R) A(s)‖`: it is
quasi-optimal relative to the best approximation in `range R`. -/
theorem galerkin_quasiOptimal {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hA : ODESolution F A t₀ t₁) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = R (A t₀)) {d : ℝ}
    (hd : ∀ t ∈ Icc t₀ t₁, ‖A t - R (A t)‖ ≤ d) :
    ∀ t ∈ Icc t₀ t₁, ‖YS t - A t‖ ≤ ‖A t - R (A t)‖ + (Real.exp (L * (t - t₀)) - 1) * d := by
  have hrange : ∀ t ∈ Icc t₀ t₁, R (YS t) = YS t := by
    intro t ht
    have hgc : ContinuousOn (fun s => YS s - R (YS s)) (Icc t₀ t₁) :=
      hS.cont.sub (R.continuous.comp_continuousOn hS.cont)
    have hgd : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun s => YS s - R (YS s)) 0 (Ici s) s := by
      intro s hs
      have h1 := hS.deriv s hs
      have h2 := R.hasFDerivAt.comp_hasDerivWithinAt s h1
      convert h1.sub h2 using 1
      all_goals first | rfl | rw [hR.idem, sub_self]
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd (C := 0)
      (fun _ _ => by simp) t ht
    rw [hS₀, hR.idem, sub_self, sub_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] at h
    exact h.symm
  have hRA : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun s => R (A s)) (R (F t (A t))) (Ici t) t :=
    fun t ht => R.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
  have hRAc : ContinuousOn (fun s => R (A s)) (Icc t₀ t₁) :=
    R.continuous.comp_continuousOn hA.cont
  have hmain := norm_sub_le_gronwallBound_of_inner_le (F := fun t x => R (F t x)) (ℓ := L)
    (y := YS) (z := fun s => R (A s)) (u := fun t => R (F t (YS t)))
    (w := fun t => R (F t (A t))) (a := t₀) (b := t₁) (ηy := 0) (ηz := L * d) (δ := 0)
    (fun t ht => by
      have h1 := hrange t (Ico_subset_Icc_self ht)
      have h2 : R (R (A t)) = R (A t) := hR.idem _
      have hd : R (YS t - R (A t)) = YS t - R (A t) := by rw [map_sub, h1, h2]
      calc inner ℝ (R (F t (YS t)) - R (F t (R (A t)))) (YS t - R (A t))
          = inner ℝ (F t (YS t) - F t (R (A t))) (R (YS t - R (A t))) := by
            rw [← map_sub, hR.symm]
        _ = inner ℝ (F t (YS t) - F t (R (A t))) (YS t - R (A t)) := by rw [hd]
        _ ≤ ‖F t (YS t) - F t (R (A t))‖ * ‖YS t - R (A t)‖ := real_inner_le_norm _ _
        _ ≤ L * ‖YS t - R (A t)‖ * ‖YS t - R (A t)‖ :=
            mul_le_mul_of_nonneg_right (hF t _ _) (norm_nonneg _)
        _ = L * ‖YS t - R (A t)‖ ^ 2 := by ring)
    hS.cont (fun t ht => hS.deriv t ht) (fun t ht => by simp) hRAc hRA
    (fun t ht => by
      have hdt := hd t (Ico_subset_Icc_self ht)
      calc ‖R (F t (A t)) - R (F t (R (A t)))‖ = ‖R (F t (A t) - F t (R (A t)))‖ := by
            rw [map_sub]
        _ ≤ ‖F t (A t) - F t (R (A t))‖ := hR.norm_le _
        _ ≤ L * ‖A t - R (A t)‖ := hF t _ _
        _ ≤ L * d := mul_le_mul_of_nonneg_left hdt hL)
    (by rw [hS₀]; simp)
  intro t ht
  have hb := hmain t ht
  have hgb : gronwallBound 0 L (L * d) (t - t₀) = (Real.exp (L * (t - t₀)) - 1) * d := by
    unfold gronwallBound
    split_ifs with h0
    · subst h0; simp
    · field_simp; ring
  rw [zero_add, hgb] at hb
  calc ‖YS t - A t‖ ≤ ‖YS t - R (A t)‖ + ‖R (A t) - A t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by rw [norm_sub_rev (R (A t)) (A t)]; linarith

end Galerkin

section RankAdaptive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L B ε : ℝ}

end RankAdaptive

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end QuasiOptimal

end LeanDLRA
