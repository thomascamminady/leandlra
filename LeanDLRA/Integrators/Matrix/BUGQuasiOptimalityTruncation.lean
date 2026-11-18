import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityStep
import LeanDLRA.DLRA.QuasiOptimalityTimeLocal

/-!
# Quasi-optimality of the BUG integrator against the truncated singular value decomposition

For the matrix approximation problem (given data `A(t)`, field `F(t, Y) = Ȧ(t)`) this file bounds
the error of the fixed-rank BUG integrator of [CerutiLubich2022] against the truncated singular
value decomposition `T_r(A(t_n))` on a uniform grid `t_n = n h`, in the quantities of the
continuous bound
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt`: with
`‖Ȧ‖ ≤ μ` and `σ_r(A) ≤ τ < ρ ≤ σ_{r-1}(A)` (indices start at `0`), `lam = μ / (ρ - τ)` and
`h lam ≤ 1/16`,

  `‖Y_n - T_r(A(t_n))‖ ≤ e^{9/2 lam t_n} (‖Y_0 - T_r(A(0))‖ + 12/5 lam t_n τ)`,

as long as the right-hand side at the final time is at most `ρ/16`. All norms are Frobenius
norms. In the sharper forms `t_n τ` is a Riemann sum of `σ_r(A)` on the grid, and the constants
may depend on the step.

## Main results

* `EckartYoung.exists_ginv_truncation`: the truncated singular value decomposition has a
  generalized inverse of norm `≤ ρ⁻¹` with symmetric projectors of trace `r`, and its tail is
  orthogonal to its column and row space.
* `EckartYoung.norm_truncation_sub_truncation_le_mul_sub`: along a curve,
  `‖T_r(A b) - T_r(A a)‖ ≤ ρ μ / (ρ - τ) (b - a)`, and the same for the tail.
* `Exactness.IsBUGIncrementStep.norm_sub_truncation_le`: one step,
  `‖Y₁ - X₁‖ ≤ (1 + 9/2 η) ‖Y₀ - X₀‖ + 11/5 η σ_r(A b) + 4/3 η² (σ_r(A a) + σ_r(A b))` with
  `η = (b - a) lam`.
* `norm_bugRun_sub_truncation_le`: `N` steps with constants of the steps.
* `norm_bugRun_sub_truncation_le_of_forall_le`,
  `norm_bugRun_sub_truncation_le_mul_of_forall_le`: `N` steps with constants on `[0, N h]`.

## Implementation notes

The step is `MatrixBUG.norm_projStep_sub_le_of_trace` for the references `T_r(A(t_k))`; the sines
of the angles between the bases and the lower bound of the iterate on its row and column space
are derived there, so nothing is assumed on the iterates besides the orthonormality of the bases
and the equations of the step. The data are seen on the grid only, so the bound has the values
`σ_r(A(t_k))` and not the integral of `σ_r(A)`: between two grid points the tail does not enter
the integrator. The smallness condition on the bound (or on the error) is needed for the
overlap of the bases of the iterate with those of the reference. The exponent `9/2 lam` is not
sharp: the continuous bound has `μ / ρ`.

## References

* [CerutiLubich2022]
-/

open Set Finset Matrix Filter
open scoped Topology LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### The truncated singular value decomposition as a reference -/

section Reference

open EckartYoung Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The truncated singular value decomposition is a reference with an orthogonal tail.** If
`0 < ρ ≤ σ_{r-1}(A)` (indices start at `0`), then `X = T_r(A)` has a generalized inverse `G`
(the Moore–Penrose inverse) with `X G X = X`, symmetric `X G` and `G X` of trace `r`,
`(A - X) G = 0`, `G (A - X) = 0` and `‖G‖₂ ≤ ρ⁻¹`. -/
theorem EckartYoung.exists_ginv_truncation {r : ℕ} {A : Matrix m n ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin A).singularValues (r - 1)) :
    ∃ G : Matrix n m ℝ, truncation A r * G * truncation A r = truncation A r ∧
      (truncation A r * G)ᵀ = truncation A r * G ∧
      (G * truncation A r)ᵀ = G * truncation A r ∧
      (A - truncation A r) * G = 0 ∧ G * (A - truncation A r) = 0 ∧ specNorm G ≤ ρ⁻¹ ∧
      trace (truncation A r * G) = r ∧ trace (G * truncation A r) = r := by
  obtain ⟨U, V, σ, hU, hV, hσi, hT⟩ := exists_truncation_eq_mul_diagonal_mul_transpose hρ hσ
  have hS := diagonal_bounded_below hρ.le hσi
  have hdet : IsUnit (diagonal σ).det := isUnit_det_of_bounded_below hρ hS
  have hopt := tangentProjAt_truncation_sub_eq_zero A r
  rw [hT] at hopt ⊢
  rw [tangentProjAt_eq_tangentProj hU hV hdet, tangentProj_apply] at hopt
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = A - U * diagonal σ * Vᵀ := ⟨_, rfl⟩
  rw [← hZ] at hopt ⊢
  have hU' : ∀ M : Matrix (Fin r) n ℝ, Uᵀ * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hZV : Z * V = 0 := by
    have h := congrArg (fun M => M * V) hopt
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hV,
      Matrix.mul_one] at h
    simpa using h
  have hUZ : Uᵀ * Z = 0 := by
    have h := congrArg (fun M => Uᵀ * M) hopt
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_zero, Matrix.mul_assoc, hU'] at h
    simpa using h
  refine ⟨V * (diagonal σ)⁻¹ * Uᵀ, factor_ginv_factor hU hV hdet, ?_, ?_, ?_, ?_,
    specNorm_ginv_le hρ hU hV hS, ?_, ?_⟩
  · rw [factor_mul_ginv hV hdet, Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [ginv_mul_factor hU hdet, Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hZV, Matrix.zero_mul, Matrix.zero_mul]
  · rw [Matrix.mul_assoc (V * (diagonal σ)⁻¹), hUZ, Matrix.mul_zero]
  · rw [factor_mul_ginv hV hdet, trace_mul_transpose hU, Fintype.card_fin]
  · rw [ginv_mul_factor hU hdet, trace_mul_transpose hV, Fintype.card_fin]

omit [DecidableEq m] in
/-- **The increments of the truncated singular value decomposition and of its tail along a
curve.** Let `A` be continuous on `[a, b]` with right derivative `A'`, `‖A'‖ ≤ μ`, and
`σ_r(A t) ≤ τ < ρ ≤ σ_{r-1}(A t)` on `[a, b]` (indices start at `0`). Then
`‖T_r(A b) - T_r(A a)‖ ≤ ρ μ / (ρ - τ) (b - a)`, and the same bound holds for the increment of
the tail `A - T_r(A)`. -/
theorem EckartYoung.norm_truncation_sub_truncation_le_mul_sub {r : ℕ}
    {A A' : ℝ → Matrix m n ℝ} {a b ρ μ τ : ℝ} (hab : a ≤ b)
    (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ) :
    ‖truncation (A b) r - truncation (A a) r‖ ≤ ρ * (μ / (ρ - τ)) * (b - a) ∧
      ‖A b - truncation (A b) r - (A a - truncation (A a) r)‖ ≤
        ρ * (μ / (ρ - τ)) * (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hτ0 : 0 ≤ τ := ((toEuclideanLin (A a)).singularValues_nonneg r).trans (hτ a ha)
  have hρ : 0 < ρ := hτ0.trans_lt hτρ
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by
    subst h0
    have h1 := hσ a ha
    have h2 := hτ a ha
    simp only [Nat.zero_sub] at h1
    linarith
  have hθ : τ / ρ < 1 := (div_lt_one hρ).mpr hτρ
  have hθρ : τ / ρ * ρ = τ := div_mul_cancel₀ τ hρ.ne'
  have hgap : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r <
      (toEuclideanLin (A t)).singularValues (r - 1) :=
    fun t ht => (hτ t ht).trans_lt (hτρ.trans_le (hσ t ht))
  have hC : μ / (1 - τ / ρ) = ρ * (μ / (ρ - τ)) := by
    have h1 : ρ - τ ≠ 0 := (sub_pos.mpr hτρ).ne'
    have h2 : 1 - τ / ρ ≠ 0 := (sub_pos.mpr hθ).ne'
    field_simp
  have hXc : ContinuousOn (fun t => truncation (A t) r) (Icc a b) := fun s hs =>
    (continuousAt_truncation (hgap s hs)).comp_continuousWithinAt (hAc s hs)
  have hX : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => truncation (A t) r)
      (fderiv ℝ (fun B => truncation B r) (A t) (A' t)) (Ici t) t := fun s hs =>
    hasDerivWithinAt_truncation (hA s hs) (hgap s (Ico_subset_Icc_self hs))
  have hb : ∀ t ∈ Ico a b,
      ‖fderiv ℝ (fun B => truncation B r) (A t) (A' t)‖ ≤ ρ * (μ / (ρ - τ)) ∧
      ‖A' t - fderiv ℝ (fun B => truncation B r) (A t) (A' t)‖ ≤ ρ * (μ / (ρ - τ)) := by
    intro t ht
    have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
    have hts : t ∈ Icc t b := ⟨le_rfl, ht.2.le⟩
    have hs : (𝓝[Icc t b \ {t}] t).NeBot := by
      rw [Icc_sdiff_left]
      exact left_nhdsWithin_Ioc_neBot ht.2
    have hA' := (hA t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
    have hX' := (hX t ht).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
    have hrank : ∀ u ∈ Icc t b, (truncation (A u) r).rank = r := fun u hu =>
      rank_truncation_of_le_singularValues hρ (hσ u (hsub hu))
    have hσ' : ∀ u ∈ Icc t b, ρ ≤ (toEuclideanLin (truncation (A u) r)).singularValues (r - 1) :=
      fun u hu => le_singularValues_truncation hr hρ (hσ u (hsub hu))
    have hopt : ∀ u ∈ Icc t b,
        tangentProjAt (truncation (A u) r) (A u - truncation (A u) r) = 0 :=
      fun u _ => tangentProjAt_truncation_sub_eq_zero _ _
    have hd : specNorm (truncation (A t) r - A t) ≤ τ / ρ * ρ := by
      rw [specNorm_sub_comm, specNorm_sub_truncation, hθρ]
      exact hτ t (hsub hts)
    have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ t ht)
    have b1 := norm_le_div_one_sub_of_specNorm_sub_le hA' hX' hts hs hρ hrank hσ' hopt
      (hμ t ht) hθ hd
    have b2 := norm_sub_tangentProjAt_le_div_one_sub_mul_specNorm hA' hX' hts hs hρ hrank hσ'
      hopt (hμ t ht) hθ hd
    rw [hC] at b1
    refine ⟨b1, ?_⟩
    have hn : ‖A' t - tangentProjAt (truncation (A t) r) (A' t)‖ ≤ μ := by
      have := (isOrthProj_tangentProjAt (truncation (A t) r)).compl.norm_le (A' t)
      simp only [sub_apply, one_apply_eq_self] at this
      exact this.trans (hμ t ht)
    have hq : 0 ≤ μ / ((1 - τ / ρ) * ρ) :=
      div_nonneg hμ0 (mul_nonneg (sub_pos.mpr hθ).le hρ.le)
    have hsp : specNorm (A t - truncation (A t) r) ≤ τ := by
      rw [specNorm_sub_truncation]
      exact hτ t (hsub hts)
    have b3 : ‖fderiv ℝ (fun B => truncation B r) (A t) (A' t) -
        tangentProjAt (truncation (A t) r) (A' t)‖ ≤ μ / ((1 - τ / ρ) * ρ) * τ :=
      b2.trans (mul_le_mul_of_nonneg_left hsp hq)
    have e : A' t - fderiv ℝ (fun B => truncation B r) (A t) (A' t) =
        A' t - tangentProjAt (truncation (A t) r) (A' t) -
          (fderiv ℝ (fun B => truncation B r) (A t) (A' t) -
            tangentProjAt (truncation (A t) r) (A' t)) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ((add_le_add hn b3).trans_eq ?_)
    rw [← hC]
    have h1 : ρ ≠ 0 := hρ.ne'
    have h2 : 1 - τ / ρ ≠ 0 := (sub_pos.mpr hθ).ne'
    have h3 : ρ - τ ≠ 0 := (sub_pos.mpr hτρ).ne'
    field_simp
    ring
  refine ⟨norm_image_sub_le_of_norm_deriv_right_le_segment hXc hX (fun t ht => (hb t ht).1) b
    ⟨hab, le_rfl⟩, ?_⟩
  exact norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun t => A t - truncation (A t) r) (hAc.sub hXc)
    (fun t ht => (hA t ht).sub (hX t ht)) (fun t ht => (hb t ht).2) b ⟨hab, le_rfl⟩

end Reference

/-! ### One step and the run -/

section Run

open EckartYoung Curvature MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- **One BUG step for given data against the truncated singular value decomposition.** Let `A`
be continuous on `[a, b]`, `a < b`, with right derivative `A'`, `‖A'‖ ≤ μ` and
`σ_r(A t) ≤ τ < ρ ≤ σ_{r-1}(A t)` on `[a, b]` (indices start at `0`), and let `lam ≥ μ / (ρ - τ)`
with `(b - a) lam ≤ 1/16`. For a BUG step `(U₀, S₀, V₀) ↦ (U₁, S₁, V₁)` with exact substeps for
`F(t, Y) = Ȧ(t)` from `t = a` to `t = b`, bases with `r` orthonormal columns and
`‖Y₀ - T_r(A a)‖ ≤ ρ/16`, with `η = (b - a) lam`,

  `‖Y₁ - T_r(A b)‖ ≤ (1 + 9/2 η) ‖Y₀ - T_r(A a)‖ + 11/5 η σ_r(A b) + 4/3 η² (σ_r(A a) + σ_r(A b))`.

Nothing is assumed on the singular values of `S₀`. -/
theorem Exactness.IsBUGIncrementStep.norm_sub_truncation_le {r : ℕ} {A A' : ℝ → Matrix m n ℝ}
    {a b ρ μ τ lam : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ S₁ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ V₁ : Matrix n (Fin r) ℝ}
    (hs : Exactness.IsBUGIncrementStep (A a) (A b) U₀ S₀ V₀ U₁ S₁ V₁) (hab : a < b)
    (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico a b, ‖A' t‖ ≤ μ)
    (hσ : ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc a b, (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ)
    (hlam : μ ≤ lam * (ρ - τ)) (hstep : (b - a) * lam ≤ 1 / 16)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (he : ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ ≤ ρ / 16) :
    ‖U₁ * S₁ * V₁ᵀ - truncation (A b) r‖ ≤
      (1 + 9 / 2 * ((b - a) * lam)) * ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ +
        11 / 5 * ((b - a) * lam) * (toEuclideanLin (A b)).singularValues r +
        4 / 3 * ((b - a) * lam) ^ 2 * ((toEuclideanLin (A a)).singularValues r +
          (toEuclideanLin (A b)).singularValues r) := by
  classical
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hτ0 : 0 ≤ τ := ((toEuclideanLin (A a)).singularValues_nonneg r).trans (hτ a ha)
  have hρ : 0 < ρ := hτ0.trans_lt hτρ
  have hgap : 0 < ρ - τ := sub_pos.mpr hτρ
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩)
  have hlam0 : 0 ≤ lam := nonneg_of_mul_nonneg_left (hμ0.trans hlam) hgap
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab.le
  obtain ⟨G₀, hX₀, hc₀, hr₀, hRG₀, hGR₀, hG₀, htc₀, htr₀⟩ :=
    exists_ginv_truncation (r := r) hρ (hσ a ha)
  obtain ⟨G₁, hX₁, hc₁, hr₁, hRG₁, hGR₁, hG₁, -, -⟩ :=
    exists_ginv_truncation (r := r) hρ (hσ b hb)
  obtain ⟨hinc, htail⟩ := norm_truncation_sub_truncation_le_mul_sub hab.le hAc hA hμ hσ hτ hτρ
  have hAinc : ‖A b - A a‖ ≤ μ * (b - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hAc hA hμ b hb
  have hq : μ / (ρ - τ) ≤ lam := (div_le_iff₀ hgap).mpr hlam
  have hinv : ρ⁻¹ * (ρ * (μ / (ρ - τ)) * (b - a)) ≤ (b - a) * lam := by
    have e : ρ⁻¹ * (ρ * (μ / (ρ - τ)) * (b - a)) = (b - a) * (μ / (ρ - τ)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hq hba
  have hρi : 0 ≤ ρ⁻¹ := (inv_pos.mpr hρ).le
  have hξ : ρ⁻¹ * ‖truncation (A b) r - truncation (A a) r‖ ≤ (b - a) * lam :=
    (mul_le_mul_of_nonneg_left hinc hρi).trans hinv
  have hδ : ρ⁻¹ * specNorm (A b - truncation (A b) r - (A a - truncation (A a) r)) ≤
      (b - a) * lam :=
    (mul_le_mul_of_nonneg_left ((specNorm_le_frob _).trans htail) hρi).trans hinv
  have hν : ρ⁻¹ * ‖A b - A a‖ ≤ (b - a) * lam := by
    have h1 : μ ≤ lam * ρ := hlam.trans (by nlinarith)
    have h2 : ρ⁻¹ * (μ * (b - a)) ≤ (b - a) * lam := by
      have e : ρ⁻¹ * (μ * (b - a)) = (b - a) * (μ / ρ) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hρ).mpr h1) hba
    exact (mul_le_mul_of_nonneg_left hAinc hρi).trans h2
  have he' : ρ⁻¹ * ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ ≤ 1 / 16 := by
    have := mul_le_mul_of_nonneg_left he hρi
    have e : ρ⁻¹ * (ρ / 16) = 1 / 16 := by field_simp
    linarith
  have htrU : ∀ {W : Matrix m (Fin r) ℝ}, Wᵀ * W = 1 → trace (W * Wᵀ) = (r : ℝ) := fun hW => by
    rw [trace_mul_transpose hW, Fintype.card_fin]
  have htrV : ∀ {W : Matrix n (Fin r) ℝ}, Wᵀ * W = 1 → trace (W * Wᵀ) = (r : ℝ) := fun hW => by
    rw [trace_mul_transpose hW, Fintype.card_fin]
  have h := norm_projStep_sub_le_of_trace (isOrthProjMat_mul_transpose hU₁)
    (isOrthProjMat_mul_transpose hV₁) (isOrthProjMat_mul_transpose hU₀)
    (isOrthProjMat_mul_transpose hV₀) (colProj_mul_factor hU₀) (factor_mul_rowProj hV₀)
    (hs.proj_capK hV₀) (hs.proj_capL hU₀) hX₀ hc₀ hr₀ hX₁ hc₁ hr₁ hRG₀ hGR₀ hRG₁ hGR₁
    ((htrU hU₁).trans (htrU hU₀).symm) ((htrV hV₁).trans (htrV hV₀).symm)
    ((htrU hU₀).trans htc₀.symm) ((htrV hV₀).trans htr₀.symm) hG₀ hG₁
    ((mul_le_mul_of_nonneg_left (specNorm_le_frob _) hρi).trans hξ) hδ hξ hν le_rfl hstep he'
    (specNorm_sub_truncation (A b) r).le
  rw [← hs.eq_proj_mul] at h
  have hΔ : specNorm (A b - truncation (A b) r - (A a - truncation (A a) r)) ≤
      (toEuclideanLin (A a)).singularValues r + (toEuclideanLin (A b)).singularValues r := by
    have e : A b - truncation (A b) r - (A a - truncation (A a) r) =
        A b - truncation (A b) r + (truncation (A a) r - A a) := by abel
    have h1 := WeylSingular.specNorm_add_le (A b - truncation (A b) r) (truncation (A a) r - A a)
    rw [specNorm_sub_comm (truncation (A a) r) (A a), specNorm_sub_truncation,
      specNorm_sub_truncation] at h1
    rw [e]
    linarith
  have hη2 : 0 ≤ 4 / 3 * ((b - a) * lam) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hΔ hη2
  have hηe : 0 ≤ (b - a) * lam * ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ :=
    mul_nonneg (mul_nonneg hba hlam0) (norm_nonneg _)
  have e1 : (1 + 23 / 10 * ((b - a) * lam) + 43 / 20 * ((b - a) * lam)) *
      ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ = ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ +
        89 / 20 * ((b - a) * lam * ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖) := by ring
  have e2 : (1 + 9 / 2 * ((b - a) * lam)) * ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ =
      ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖ +
        9 / 2 * ((b - a) * lam * ‖U₀ * S₀ * V₀ᵀ - truncation (A a) r‖) := by ring
  rw [e1] at h
  rw [e2]
  linarith

/-- One step of the recursion: `(1 + a) (e^s c) + b ≤ e^{s + a} (c + b)`. -/
private theorem one_add_mul_exp_mul_add_le {s a c b : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hb : 0 ≤ b) : (1 + a) * (Real.exp s * c) + b ≤ Real.exp (s + a) * (c + b) := by
  rw [Real.exp_add]
  have h1 : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have h4 : (1 + a) * (Real.exp s * c) ≤ Real.exp a * (Real.exp s * c) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg (Real.exp_pos s).le hc)
  have h5 : b ≤ Real.exp s * Real.exp a * b :=
    le_mul_of_one_le_left hb
      (one_le_mul_of_one_le_of_one_le (Real.one_le_exp hs) (Real.one_le_exp ha))
  calc (1 + a) * (Real.exp s * c) + b
      ≤ Real.exp a * (Real.exp s * c) + Real.exp s * Real.exp a * b := add_le_add h4 h5
    _ = Real.exp s * Real.exp a * (c + b) := by ring

omit [DecidableEq m] in
/-- **Quasi-optimality of the BUG integrator for given data, with constants of the steps.** Let
`A` be continuous on `[0, N h]` with right derivative `A'`. On the `k`-th step
`[k h, (k + 1) h]` let `‖A'‖ ≤ μ k` and `σ_r(A t) ≤ τ k < ρ k ≤ σ_{r-1}(A t)` (indices start at
`0`), and let `lam k ≥ μ k / (ρ k - τ k)` with `h lam k ≤ 1/16`. Let `Y k = U k S k (V k)ᵀ` be
`N` steps of the BUG integrator of [CerutiLubich2022] with exact substeps for `F(t, Y) = Ȧ(t)`
and bases with `r` orthonormal columns. Then, with the truncated singular value decompositions
`X k = T_r(A (k h))` and `s k = σ_r(A (k h))`, for `n ≤ N`

  `‖Y n - X n‖ ≤ e^{9/2 ∑_{j<n} h lam j} (‖Y 0 - X 0‖
      + ∑_{k<n} h lam k (11/5 s (k + 1) + 4/3 h lam k (s k + s (k + 1))))`,

provided that for `n < N` this bound or the error `‖Y n - X n‖` itself is at most `ρ n / 16`.
The sum is `11/5` times a Riemann sum of `∫ μ / (ρ - τ) σ_r(A)` up to a term of the size of the
step times the tail, and every term vanishes with the tail. -/
theorem norm_bugRun_sub_truncation_le {r N : ℕ} {A A' : ℝ → Matrix m n ℝ}
    {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {h : ℝ} {ρ μ τ lam : ℕ → ℝ} (hh : 0 < h)
    (hAc : ContinuousOn A (Icc 0 (N * h)))
    (hA : ∀ t ∈ Ico 0 (N * h), HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ k < N, ∀ t ∈ Ico (k * h) ((k + 1 : ℕ) * h), ‖A' t‖ ≤ μ k)
    (hσ : ∀ k < N, ∀ t ∈ Icc (k * h) ((k + 1 : ℕ) * h),
      ρ k ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ k < N, ∀ t ∈ Icc (k * h) ((k + 1 : ℕ) * h),
      (toEuclideanLin (A t)).singularValues r ≤ τ k)
    (hτρ : ∀ k < N, τ k < ρ k) (hlam : ∀ k < N, μ k ≤ lam k * (ρ k - τ k))
    (hstep : ∀ k < N, h * lam k ≤ 1 / 16)
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (hs : ∀ k < N, Exactness.IsBUGIncrementStep (A (k * h)) (A ((k + 1 : ℕ) * h)) (U k) (S k)
      (V k) (U (k + 1)) (S (k + 1)) (V (k + 1)))
    (htube : ∀ n < N, min
      (Real.exp (9 / 2 * ∑ j ∈ range n, h * lam j) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
          ∑ k ∈ range n, h * lam k *
            (11 / 5 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
              4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
                (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r))))
      ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤ ρ n / 16) :
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤
      Real.exp (9 / 2 * ∑ j ∈ range n, h * lam j) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
          ∑ k ∈ range n, h * lam k *
            (11 / 5 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
              4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
                (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r))) := by
  have hlam0 : ∀ k < N, 0 ≤ lam k := fun k hk => by
    have hk0 : (k : ℝ) * h < ((k + 1 : ℕ) : ℝ) * h := by
      push_cast
      linarith
    have hμ0 : 0 ≤ μ k := (norm_nonneg _).trans (hμ k hk _ ⟨le_rfl, hk0⟩)
    exact nonneg_of_mul_nonneg_left (hμ0.trans (hlam k hk)) (sub_pos.mpr (hτρ k hk))
  have hterm : ∀ k < N, 0 ≤ h * lam k *
      (11 / 5 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
        4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
          (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)) := fun k hk => by
    have h1 := (toEuclideanLin (A (k * h))).singularValues_nonneg r
    have h2 := (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues_nonneg r
    have h3 := mul_nonneg hh.le (hlam0 k hk)
    positivity
  intro n
  induction n with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro hn
    have hnN : n < N := hn
    have ihn := ih hnN.le
    have hen : ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤ ρ n / 16 :=
      (le_min ihn le_rfl).trans (htube n hnN)
    have hab : (n : ℝ) * h < ((n + 1 : ℕ) : ℝ) * h := by
      push_cast
      linarith
    have hba : ((n + 1 : ℕ) : ℝ) * h - n * h = h := by
      push_cast
      ring
    have ha0 : (0 : ℝ) ≤ n * h := mul_nonneg (Nat.cast_nonneg n) hh.le
    have hbN : ((n + 1 : ℕ) : ℝ) * h ≤ N * h :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hh.le
    have hstepn : (((n + 1 : ℕ) : ℝ) * h - n * h) * lam n ≤ 1 / 16 := by
      rw [hba]
      exact hstep n hnN
    have key := (hs n hnN).norm_sub_truncation_le hab
      (hAc.mono (Icc_subset_Icc ha0 hbN))
      (fun t ht => hA t ⟨ha0.trans ht.1, ht.2.trans_le hbN⟩) (hμ n hnN) (hσ n hnN) (hτ n hnN)
      (hτρ n hnN) (hlam n hnN) hstepn (hU n hnN.le) (hV n hnN.le) (hU (n + 1) hn)
      (hV (n + 1) hn) hen
    rw [hba] at key
    have hs0 : 0 ≤ 9 / 2 * ∑ j ∈ range n, h * lam j :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun j hj =>
        mul_nonneg hh.le (hlam0 j ((Finset.mem_range.mp hj).trans hnN)))
    have hc0 : 0 ≤ ‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
        ∑ k ∈ range n, h * lam k *
          (11 / 5 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
            4 / 3 * (h * lam k) * ((toEuclideanLin (A (k * h))).singularValues r +
              (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)) :=
      add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun k hk =>
        hterm k ((Finset.mem_range.mp hk).trans hnN))
    have ha9 : 0 ≤ 9 / 2 * (h * lam n) :=
      mul_nonneg (by norm_num) (mul_nonneg hh.le (hlam0 n hnN))
    have hG := one_add_mul_exp_mul_add_le hs0 ha9 hc0 (hterm n hnN)
    have hmono := mul_le_mul_of_nonneg_left ihn (by linarith : 0 ≤ 1 + 9 / 2 * (h * lam n))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add (9 / 2 : ℝ), ← add_assoc]
    refine le_trans ?_ hG
    refine key.trans ?_
    have e : 11 / 5 * (h * lam n) * (toEuclideanLin (A ((n + 1 : ℕ) * h))).singularValues r +
        4 / 3 * (h * lam n) ^ 2 * ((toEuclideanLin (A (n * h))).singularValues r +
          (toEuclideanLin (A ((n + 1 : ℕ) * h))).singularValues r) =
        h * lam n * (11 / 5 * (toEuclideanLin (A ((n + 1 : ℕ) * h))).singularValues r +
          4 / 3 * (h * lam n) * ((toEuclideanLin (A (n * h))).singularValues r +
            (toEuclideanLin (A ((n + 1 : ℕ) * h))).singularValues r)) := by ring
    rw [add_assoc, e]
    exact add_le_add hmono le_rfl

/-- The sum of the bound for constants that do not depend on the step and a tail of at most
`τ`. -/
private theorem sum_mul_le_mul_mul {n : ℕ} {h lam τ : ℝ} {s : ℕ → ℝ} (hh : 0 ≤ h)
    (hlam : 0 ≤ lam) (hstep : h * lam ≤ 1 / 16) (hs0 : ∀ k, 0 ≤ s k)
    (hsτ : ∀ k ≤ n, s k ≤ τ) :
    ∑ k ∈ range n, h * lam * (11 / 5 * s (k + 1) + 4 / 3 * (h * lam) * (s k + s (k + 1))) ≤
      12 / 5 * lam * (n * h) * τ := by
  have hhl : 0 ≤ h * lam := mul_nonneg hh hlam
  have hterm : ∀ k ∈ range n,
      h * lam * (11 / 5 * s (k + 1) + 4 / 3 * (h * lam) * (s k + s (k + 1))) ≤
        h * lam * (12 / 5 * τ) := fun k hk => by
    have hk' := Finset.mem_range.mp hk
    have h1 := hsτ k hk'.le
    have h2 := hsτ (k + 1) hk'
    have h3 : 4 / 3 * (h * lam) * (s k + s (k + 1)) ≤ 4 / 3 * (1 / 16) * (s k + s (k + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (hs0 k) (hs0 (k + 1)))
    exact mul_le_mul_of_nonneg_left (by linarith [hs0 k, hs0 (k + 1)]) hhl
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

omit [DecidableEq m] in
/-- `norm_bugRun_sub_truncation_le` for constants that do not depend on the step. -/
private theorem norm_bugRun_sub_truncation_le_aux {r N : ℕ} {A A' : ℝ → Matrix m n ℝ}
    {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {h ρ μ τ : ℝ} (hh : 0 < h)
    (hAc : ContinuousOn A (Icc 0 (N * h)))
    (hA : ∀ t ∈ Ico 0 (N * h), HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico 0 (N * h), ‖A' t‖ ≤ μ)
    (hσ : ∀ t ∈ Icc 0 (N * h), ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc 0 (N * h), (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ)
    (hstep : h * (μ / (ρ - τ)) ≤ 1 / 16)
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (hs : ∀ k < N, Exactness.IsBUGIncrementStep (A (k * h)) (A ((k + 1 : ℕ) * h)) (U k) (S k)
      (V k) (U (k + 1)) (S (k + 1)) (V (k + 1)))
    (htube : Real.exp (9 / 2 * (μ / (ρ - τ)) * (N * h)) *
      (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ + 12 / 5 * (μ / (ρ - τ)) * (N * h) * τ) ≤
        ρ / 16) :
    (N = 0 ∨ 0 ≤ μ / (ρ - τ)) ∧
    (∀ k ≤ N, (toEuclideanLin (A (k * h))).singularValues r ≤ τ) ∧
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤
      Real.exp (9 / 2 * ∑ _j ∈ range n, h * (μ / (ρ - τ))) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
          ∑ k ∈ range n, h * (μ / (ρ - τ)) *
            (11 / 5 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
              4 / 3 * (h * (μ / (ρ - τ))) * ((toEuclideanLin (A (k * h))).singularValues r +
                (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r))) := by
  have hgap : 0 < ρ - τ := sub_pos.mpr hτρ
  have hk0 : ∀ k : ℕ, (0 : ℝ) ≤ k * h := fun k => mul_nonneg (Nat.cast_nonneg k) hh.le
  have hkN : ∀ k : ℕ, k ≤ N → (k : ℝ) * h ≤ N * h := fun k hk =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh.le
  have hlam0 : N = 0 ∨ 0 ≤ μ / (ρ - τ) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr (div_nonneg ((norm_nonneg _).trans (hμ 0 ⟨le_rfl, ?_⟩)) hgap.le)
      exact mul_pos (Nat.cast_pos.mpr hpos) hh
  have hsτ : ∀ k ≤ N, (toEuclideanLin (A (k * h))).singularValues r ≤ τ := fun k hk =>
    hτ _ ⟨hk0 k, hkN k hk⟩
  refine ⟨hlam0, hsτ, ?_⟩
  refine norm_bugRun_sub_truncation_le (ρ := fun _ => ρ) (μ := fun _ => μ) (τ := fun _ => τ)
    (lam := fun _ => μ / (ρ - τ)) hh hAc hA
    (fun k hk t ht => hμ t ⟨(hk0 k).trans ht.1, ht.2.trans_le (hkN (k + 1) hk)⟩)
    (fun k hk t ht => hσ t ⟨(hk0 k).trans ht.1, ht.2.trans (hkN (k + 1) hk)⟩)
    (fun k hk t ht => hτ t ⟨(hk0 k).trans ht.1, ht.2.trans (hkN (k + 1) hk)⟩)
    (fun _ _ => hτρ) (fun _ _ => (div_mul_cancel₀ μ hgap.ne').ge) (fun _ _ => hstep) hU hV hs
    fun n hn => ?_
  have hl : 0 ≤ μ / (ρ - τ) := hlam0.resolve_left (by omega)
  refine (min_le_left _ _).trans (le_trans ?_ htube)
  have hsum := sum_mul_le_mul_mul (n := n) (s := fun k : ℕ =>
    (toEuclideanLin (A (k * h))).singularValues r) hh.le hl hstep
    (fun k => (toEuclideanLin (A (k * h))).singularValues_nonneg r)
    (fun k hk => hsτ k (hk.trans hn.le))
  have hτ0 : 0 ≤ τ := ((toEuclideanLin (A 0)).singularValues_nonneg r).trans
    (hτ 0 ⟨le_rfl, hk0 N⟩)
  have hnN : (n : ℝ) * h ≤ N * h := hkN n hn.le
  have hmono : 12 / 5 * (μ / (ρ - τ)) * (n * h) * τ ≤ 12 / 5 * (μ / (ρ - τ)) * (N * h) * τ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnN (by positivity)) hτ0
  have hexp : 9 / 2 * ∑ _j ∈ range n, h * (μ / (ρ - τ)) ≤ 9 / 2 * (μ / (ρ - τ)) * (N * h) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_left hnN (by positivity : 0 ≤ 9 / 2 * (μ / (ρ - τ)))
    linarith
  exact mul_le_mul (Real.exp_le_exp.mpr hexp) (add_le_add le_rfl (hsum.trans hmono))
    (add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun k _ => by
      have h1 := (toEuclideanLin (A (k * h))).singularValues_nonneg r
      have h2 := (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues_nonneg r
      have h3 := mul_nonneg hh.le hl
      positivity)) (Real.exp_pos _).le

omit [DecidableEq m] in
/-- **Quasi-optimality of the BUG integrator for given data against the truncated singular value
decomposition.** Let `A` be continuous on `[0, T]`, `T = N h`, with right derivative `A'`,
`‖A'‖ ≤ μ` and `σ_r(A t) ≤ τ < ρ ≤ σ_{r-1}(A t)` (indices start at `0`), and let
`lam = μ / (ρ - τ)` with `h lam ≤ 1/16`. Let `Y k = U k S k (V k)ᵀ` be `N` steps of the BUG
integrator of [CerutiLubich2022] with exact substeps for `F(t, Y) = Ȧ(t)` and bases with `r`
orthonormal columns, and `X k = T_r(A (k h))`, `s k = σ_r(A (k h))`. If
`e^{9/2 lam T} (‖Y 0 - X 0‖ + 12/5 lam T τ) ≤ ρ/16`, then for `n ≤ N`

  `‖Y n - X n‖ ≤ e^{9/2 lam n h} (‖Y 0 - X 0‖ + 11/5 lam h ∑_{k<n} s (k + 1)
      + 4/3 h lam lam h ∑_{k<n} (s k + s (k + 1)))`.

The sums are Riemann sums of `∫ σ_r(A)` on the grid; no term is of the size of the step alone.
For data of rank `r` this is the exactness property of [CerutiLubich2022, Theorem 3]. The
continuous counterpart is
`IsDLRASolution.norm_sub_truncation_le_integral_exp_integral_of_singularValues_lt`, with the
factor `1` in the exponent and in front of the integral. -/
theorem norm_bugRun_sub_truncation_le_of_forall_le {r N : ℕ} {A A' : ℝ → Matrix m n ℝ}
    {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {h ρ μ τ : ℝ} (hh : 0 < h)
    (hAc : ContinuousOn A (Icc 0 (N * h)))
    (hA : ∀ t ∈ Ico 0 (N * h), HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico 0 (N * h), ‖A' t‖ ≤ μ)
    (hσ : ∀ t ∈ Icc 0 (N * h), ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc 0 (N * h), (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ)
    (hstep : h * (μ / (ρ - τ)) ≤ 1 / 16)
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (hs : ∀ k < N, Exactness.IsBUGIncrementStep (A (k * h)) (A ((k + 1 : ℕ) * h)) (U k) (S k)
      (V k) (U (k + 1)) (S (k + 1)) (V (k + 1)))
    (htube : Real.exp (9 / 2 * (μ / (ρ - τ)) * (N * h)) *
      (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ + 12 / 5 * (μ / (ρ - τ)) * (N * h) * τ) ≤
        ρ / 16) :
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤
      Real.exp (9 / 2 * (μ / (ρ - τ)) * (n * h)) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ +
          11 / 5 * (μ / (ρ - τ)) *
            (h * ∑ k ∈ range n, (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r) +
          4 / 3 * (h * (μ / (ρ - τ))) * ((μ / (ρ - τ)) *
            (h * ∑ k ∈ range n, ((toEuclideanLin (A (k * h))).singularValues r +
              (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)))) := by
  intro n hn
  have key := (norm_bugRun_sub_truncation_le_aux hh hAc hA hμ hσ hτ hτρ hstep hU hV hs
    htube).2.2 n hn
  have e1 : 9 / 2 * ∑ _j ∈ range n, h * (μ / (ρ - τ)) = 9 / 2 * (μ / (ρ - τ)) * (n * h) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have e2 : ∑ k ∈ range n, h * (μ / (ρ - τ)) *
      (11 / 5 * (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r +
        4 / 3 * (h * (μ / (ρ - τ))) * ((toEuclideanLin (A (k * h))).singularValues r +
          (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r)) =
      11 / 5 * (μ / (ρ - τ)) *
          (h * ∑ k ∈ range n, (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r) +
        4 / 3 * (h * (μ / (ρ - τ))) * ((μ / (ρ - τ)) *
          (h * ∑ k ∈ range n, ((toEuclideanLin (A (k * h))).singularValues r +
            (toEuclideanLin (A ((k + 1 : ℕ) * h))).singularValues r))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2, ← add_assoc] at key
  exact key

omit [DecidableEq m] in
/-- **Quasi-optimality of the BUG integrator for given data, with the largest tail.** Under the
hypotheses of `norm_bugRun_sub_truncation_le_of_forall_le`, with `lam = μ / (ρ - τ)` and
`τ ≥ σ_r(A t)` on `[0, N h]`,

  `‖Y n - T_r(A (n h))‖ ≤ e^{9/2 lam n h} (‖Y 0 - T_r(A 0)‖ + 12/5 lam n h τ)`. -/
theorem norm_bugRun_sub_truncation_le_mul_of_forall_le {r N : ℕ} {A A' : ℝ → Matrix m n ℝ}
    {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {h ρ μ τ : ℝ} (hh : 0 < h)
    (hAc : ContinuousOn A (Icc 0 (N * h)))
    (hA : ∀ t ∈ Ico 0 (N * h), HasDerivWithinAt A (A' t) (Ici t) t)
    (hμ : ∀ t ∈ Ico 0 (N * h), ‖A' t‖ ≤ μ)
    (hσ : ∀ t ∈ Icc 0 (N * h), ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hτ : ∀ t ∈ Icc 0 (N * h), (toEuclideanLin (A t)).singularValues r ≤ τ) (hτρ : τ < ρ)
    (hstep : h * (μ / (ρ - τ)) ≤ 1 / 16)
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (hs : ∀ k < N, Exactness.IsBUGIncrementStep (A (k * h)) (A ((k + 1 : ℕ) * h)) (U k) (S k)
      (V k) (U (k + 1)) (S (k + 1)) (V (k + 1)))
    (htube : Real.exp (9 / 2 * (μ / (ρ - τ)) * (N * h)) *
      (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ + 12 / 5 * (μ / (ρ - τ)) * (N * h) * τ) ≤
        ρ / 16) :
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - truncation (A (n * h)) r‖ ≤
      Real.exp (9 / 2 * (μ / (ρ - τ)) * (n * h)) *
        (‖U 0 * S 0 * (V 0)ᵀ - truncation (A 0) r‖ + 12 / 5 * (μ / (ρ - τ)) * (n * h) * τ) := by
  intro n hn
  obtain ⟨hlam0, hsτ, key⟩ := norm_bugRun_sub_truncation_le_aux hh hAc hA hμ hσ hτ hτρ hstep
    hU hV hs htube
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  have hl : 0 ≤ μ / (ρ - τ) := hlam0.resolve_left (by omega)
  have hsum := sum_mul_le_mul_mul (n := n) (s := fun k : ℕ =>
    (toEuclideanLin (A (k * h))).singularValues r) hh.le hl hstep
    (fun k => (toEuclideanLin (A (k * h))).singularValues_nonneg r)
    (fun k hk => hsτ k (hk.trans hn))
  have e1 : 9 / 2 * ∑ _j ∈ range n, h * (μ / (ρ - τ)) = 9 / 2 * (μ / (ρ - τ)) * (n * h) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  refine (key n hn).trans ?_
  rw [e1]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (Real.exp_pos _).le

end Run

/-! ### Examples -/

namespace BUGQuasiOptimalityTruncationExamples

open scoped LeanDLRA.Frobenius
open QuasiOptimalityExamples EckartYoung

/-- The tail `diag(0, 1/16)` of the example. -/
local notation "N₁₆" => (!![0, 0; 0, 1 / 16] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem hasDerivAt_smul_e₁_add_N₁₆ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (e₁ * e₁ᵀ) t := by
  simpa using (hasDerivAt_smul_e₁ 1 t).add_const N₁₆

/-- A BUG step with exact substeps for the data `A(t) = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)` from the
time `s` to the time `t`: the core `c` becomes `c + (t - s)` and the bases stay `e₁`. -/
theorem isBUGIncrementStep_smul_e₁ (c s t : ℝ) :
    Exactness.IsBUGIncrementStep ((1 + s) • (e₁ * e₁ᵀ) + N₁₆) ((1 + t) • (e₁ * e₁ᵀ) + N₁₆) e₁
      (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)) e₁ e₁
      ((c + (t - s)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) e₁ := by
  have hd : (1 + t) • (e₁ * e₁ᵀ) + N₁₆ - ((1 + s) • (e₁ * e₁ᵀ) + N₁₆) =
      (t - s) • (e₁ * e₁ᵀ) := by
    rw [add_sub_add_right_eq_sub, ← sub_smul]
    congr 1
    ring
  have hk : e₁ * c • (1 : Matrix (Fin 1) (Fin 1) ℝ) + (t - s) • (e₁ * e₁ᵀ) * e₁ =
      (c + (t - s)) • e₁ := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc,
      e₁_transpose_mul_self, Matrix.mul_one, add_smul]
  have hcap : e₁ * e₁ᵀ * ((c + (t - s)) • e₁) = (c + (t - s)) • e₁ := by
    rw [Matrix.mul_smul, Matrix.mul_assoc, e₁_transpose_mul_self, Matrix.mul_one]
  have ht : ((t - s) • (e₁ * e₁ᵀ))ᵀ = (t - s) • (e₁ * e₁ᵀ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hSt : (c • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ = c • 1 := by
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  have h2 : e₁ᵀ * ((t - s) • (e₁ * e₁ᵀ)) * e₁ = (t - s) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, e₁_transpose_mul_self,
      Matrix.one_mul, e₁_transpose_mul_self]
  refine ⟨?_, ?_, ?_⟩
  · rw [hd, hk, hcap]
  · rw [hd, ht, hSt, hk, hcap]
  · rw [hd, h2, e₁_transpose_mul_self, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
      add_smul]

/-- **Non-vacuity of `norm_bugRun_sub_truncation_le_mul_of_forall_le`** (and of
`norm_bugRun_sub_truncation_le_of_forall_le`, `norm_bugRun_sub_truncation_le`,
`Exactness.IsBUGIncrementStep.norm_sub_truncation_le`, `MatrixBUG.norm_projStep_sub_le_of_trace`
and the lemmas they use): one step of size `h = 1/32` for the data
`A(t) = (1 + t) e₁ e₁ᵀ + diag(0, 1/16)`, `r = 1`, `ρ = μ = 1`, `τ = 1/16`. The reference
`T₁(A(t)) = (1 + t) e₁ e₁ᵀ` moves, the tail `diag(0, 1/16)` is not zero, and the iterates
`Y n = (101/100 + n h) e₁ e₁ᵀ` differ from the reference. -/
example : ∀ n : ℕ, n ≤ 1 →
    ‖e₁ * ((101 / 100 + (n : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ -
        truncation ((1 + (n : ℝ) * (1 / 32)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤
      Real.exp (9 / 2 * (1 / (1 - 1 / 16)) * (n * (1 / 32))) *
        (‖e₁ * ((101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * e₁ᵀ -
            truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ +
          12 / 5 * (1 / (1 - 1 / 16)) * (n * (1 / 32)) * (1 / 16)) := by
  have hY : ‖e₁ * ((101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      e₁ᵀ - truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ ≤ 1 / 100 := by
    have ha : ‖(101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) - (1 + 0)‖ = 1 / 100 := by
      rw [Real.norm_eq_abs]
      norm_num
    rw [truncation_smul_e₁_add le_rfl, ← smul_e₁_mul, ← sub_smul, norm_smul, ha]
    nlinarith [norm_e₁_mul_le, norm_nonneg (e₁ * e₁ᵀ)]
  have hexp : Real.exp (9 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32))) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(9 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32))))
    have h2 := Real.exp_pos (9 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32)))
    have h3 : Real.exp (9 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32))) *
        Real.exp (-(9 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32)))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h4 : (1 : ℝ) / 2 ≤
        Real.exp (-(9 / 2 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32)))) := by
      refine le_trans ?_ h1
      norm_num
    nlinarith
  exact norm_bugRun_sub_truncation_le_mul_of_forall_le (N := 1)
    (A := fun t : ℝ => (1 + t) • (e₁ * e₁ᵀ) + N₁₆) (A' := fun _ => e₁ * e₁ᵀ)
    (U := fun _ => e₁) (S := fun k : ℕ => (101 / 100 + (k : ℝ) * (1 / 32)) • 1)
    (V := fun _ => e₁) (h := 1 / 32) (ρ := 1) (μ := 1) (τ := 1 / 16) (by norm_num)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_smul_e₁_add_N₁₆ s).hasDerivWithinAt)
    (fun _ _ => norm_e₁_mul_le)
    (fun t ht => one_le_singularValues_smul_e₁_add ht.1)
    (fun t ht => by
      have h1 : (toEuclideanLin ((1 + t) • (e₁ * e₁ᵀ) + N₁₆)).singularValues 1 ≤ 1 / 16 := by
        rw [← specNorm_sub_truncation, truncation_smul_e₁_add ht.1,
          Curvature.specNorm_sub_comm]
        exact (Curvature.specNorm_le_frob _).trans (norm_smul_e₁_sub_add_le t)
      exact h1)
    (by norm_num) (by norm_num) (fun _ _ => e₁_transpose_mul_self)
    (fun _ _ => e₁_transpose_mul_self)
    (fun k _ => by
      have h := isBUGIncrementStep_smul_e₁ (101 / 100 + (k : ℝ) * (1 / 32)) ((k : ℝ) * (1 / 32))
        (((k + 1 : ℕ) : ℝ) * (1 / 32))
      have e : 101 / 100 + (k : ℝ) * (1 / 32) +
          (((k + 1 : ℕ) : ℝ) * (1 / 32) - (k : ℝ) * (1 / 32)) =
          101 / 100 + ((k + 1 : ℕ) : ℝ) * (1 / 32) := by ring
      rw [e] at h
      exact h)
    (by
      calc Real.exp (9 / 2 * ((1 : ℝ) / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32))) *
            (‖e₁ * ((101 / 100 + ((0 : ℕ) : ℝ) * (1 / 32)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
                e₁ᵀ - truncation ((1 + (0 : ℝ)) • (e₁ * e₁ᵀ) + N₁₆) 1‖ +
              12 / 5 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32)) * (1 / 16))
          ≤ 2 * (1 / 100 + 12 / 5 * (1 / (1 - 1 / 16)) * (((1 : ℕ) : ℝ) * (1 / 32)) * (1 / 16)) :=
            mul_le_mul hexp (add_le_add hY le_rfl) (by positivity) (by norm_num)
        _ ≤ 1 / 16 := by norm_num)

end BUGQuasiOptimalityTruncationExamples

end LeanDLRA
