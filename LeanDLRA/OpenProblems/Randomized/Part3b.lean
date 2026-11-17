import LeanDLRA.OpenProblems.Randomized.Part3Defs
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Classical.EckartYoung
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Open problems OP-RS-24, OP-RS-25, OP-RS-26, OP-RS-27
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius Topology

namespace LeanDLRA.OpenProblems.Randomized

open LeanDLRA.Curvature

private theorem redrawSq_eq {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U₁ U₂ : Matrix m k ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) {W : Matrix k k ℝ}
    (hW : Wᵀ * W = 1) :
    ‖U₁ - U₂ * W‖ ^ 2 = 2 * Fintype.card k - 2 * ⟪U₂ᵀ * U₁, W⟫ := by
  classical
  have h1 : ‖U₁‖ ^ 2 = Fintype.card k := by
    rw [frob_sq_eq_trace, hU₁, Matrix.trace_one]
  have h2 : ‖W‖ ^ 2 = Fintype.card k := by
    rw [frob_sq_eq_trace, hW, Matrix.trace_one]
  rw [norm_sub_sq_real, h1, LeanDLRA.Frobenius.norm_mul_of_orthonormal hU₂, h2,
    LeanDLRA.Frobenius.inner_mul_left']
  ring

private theorem norm_mul_orth_right {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℝ) {W : Matrix k k ℝ} (hW : Wᵀ * W = 1) : ‖X * W‖ = ‖X‖ := by
  have hW' : Wᵀᵀ * Wᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.1 hW
  rw [← LeanDLRA.Frobenius.norm_transpose, Matrix.transpose_mul,
    LeanDLRA.Frobenius.norm_mul_of_orthonormal hW', LeanDLRA.Frobenius.norm_transpose]

private theorem redrawDist_le_add {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (U₁ V V' : Matrix m k ℝ) : redrawDist U₁ V ≤ redrawDist U₁ V' + ‖V - V'‖ := by
  have : Nonempty {W : Matrix k k ℝ // Wᵀ * W = 1} := ⟨⟨1, by simp⟩⟩
  have h : ∀ W : {W : Matrix k k ℝ // Wᵀ * W = 1},
      redrawDist U₁ V - ‖V - V'‖ ≤ ‖U₁ - V' * W.1‖ := by
    rintro ⟨W, hW⟩
    have h1 : redrawDist U₁ V ≤ ‖U₁ - V * W‖ :=
      ciInf_le (f := fun W : {W : Matrix k k ℝ // Wᵀ * W = 1} => ‖U₁ - V * W.1‖)
        ⟨0, by rintro _ ⟨W, rfl⟩; exact norm_nonneg _⟩ ⟨W, hW⟩
    have h2 : ‖U₁ - V * W‖ ≤ ‖U₁ - V' * W‖ + ‖V' * W - V * W‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h3 : ‖V' * W - V * W‖ = ‖V - V'‖ := by
      rw [← Matrix.sub_mul, norm_mul_orth_right _ hW, norm_sub_rev]
    linarith
  have : redrawDist U₁ V - ‖V - V'‖ ≤ redrawDist U₁ V' := le_ciInf h
  linarith

private theorem redrawDist_nonneg {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (U₁ U₂ : Matrix m k ℝ) : 0 ≤ redrawDist U₁ U₂ :=
  Real.iInf_nonneg fun _ => norm_nonneg _

private theorem redrawDist_sq_le {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U₁ U₂ : Matrix m k ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) :
    redrawDist U₁ U₂ ^ 2 ≤ 2 * Fintype.card k := by
  have key : ∃ W : Matrix k k ℝ, Wᵀ * W = 1 ∧ 0 ≤ ⟪U₂ᵀ * U₁, W⟫ := by
    rcases le_total 0 ⟪U₂ᵀ * U₁, (1 : Matrix k k ℝ)⟫ with h | h
    · exact ⟨1, by simp, h⟩
    · exact ⟨-1, by simp, by rw [inner_neg_right]; linarith⟩
  obtain ⟨W, hW, hip⟩ := key
  have h1 : redrawDist U₁ U₂ ≤ ‖U₁ - U₂ * W‖ :=
    ciInf_le (f := fun W : {W : Matrix k k ℝ // Wᵀ * W = 1} => ‖U₁ - U₂ * W.1‖)
      ⟨0, by rintro _ ⟨W, rfl⟩; exact norm_nonneg _⟩ ⟨W, hW⟩
  have h2 := redrawSq_eq hU₁ hU₂ hW
  have h3 := redrawDist_nonneg U₁ U₂
  nlinarith [norm_nonneg (U₁ - U₂ * W)]

private theorem redrawDist_sq_ge {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U₁ U₂ : Matrix m k ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) :
    2 * Fintype.card k - 2 * √(Fintype.card k : ℝ) * ‖U₂ᵀ * U₁‖ ≤ redrawDist U₁ U₂ ^ 2 := by
  set t : ℝ := 2 * Fintype.card k - 2 * √(Fintype.card k : ℝ) * ‖U₂ᵀ * U₁‖ with ht
  have hlow : ∀ W : {W : Matrix k k ℝ // Wᵀ * W = 1}, √(max t 0) ≤ ‖U₁ - U₂ * W.1‖ := by
    rintro ⟨W, hW⟩
    have h2 := redrawSq_eq hU₁ hU₂ hW
    have hWn : ‖W‖ = √(Fintype.card k : ℝ) := by
      rw [← Real.sqrt_sq (norm_nonneg W), frob_sq_eq_trace, hW, Matrix.trace_one]
    have h4 : ⟪U₂ᵀ * U₁, W⟫ ≤ ‖U₂ᵀ * U₁‖ * ‖W‖ := real_inner_le_norm _ _
    rw [hWn] at h4
    have h5 : max t 0 ≤ ‖U₁ - U₂ * W‖ ^ 2 := by
      refine max_le ?_ (sq_nonneg _)
      rw [h2, ht]; nlinarith
    calc √(max t 0) ≤ √(‖U₁ - U₂ * W‖ ^ 2) := Real.sqrt_le_sqrt h5
      _ = ‖U₁ - U₂ * W‖ := Real.sqrt_sq (norm_nonneg _)
  have : Nonempty {W : Matrix k k ℝ // Wᵀ * W = 1} := ⟨⟨1, by simp⟩⟩
  have h6 : √(max t 0) ≤ redrawDist U₁ U₂ := le_ciInf hlow
  have h7 : max t 0 ≤ redrawDist U₁ U₂ ^ 2 := by
    calc max t 0 = √(max t 0) ^ 2 := (Real.sq_sqrt (le_max_right _ _)).symm
      _ ≤ _ := by gcongr
  exact (le_max_left _ _).trans h7

private theorem norm_orth_eq {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) : ‖U‖ = √(Fintype.card k : ℝ) := by
  classical
  rw [← Real.sqrt_sq (norm_nonneg U), frob_sq_eq_trace, hU, Matrix.trace_one]

/-- **OP-RS-24 (b)** (Haar-like sub-threshold directions; the claim of the paper's Appendix A):
if the redrawn basis `U₂` is random with isotropic projector, `E[U₂U₂ᵀ] = (r/d) I`, then
`2r (1 - √(r/d)) ≤ E[redrawDist(U₁, U₂)²] ≤ 2r`; hence the redraw distance tends to `√(2r)` as
`r/d → 0`.  Meaning: random redraws move the subspace maximally. -/
theorem integral_redrawDist_sq_bounds {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {U₁ : Matrix m k ℝ} {U₂ : Ω → Matrix m k ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hU₂ : ∀ ω, (U₂ ω)ᵀ * U₂ ω = 1) (hmeas : ∀ i j, Measurable fun ω => U₂ ω i j)
    (hiso : ∀ i j, ∫ ω, (U₂ ω * (U₂ ω)ᵀ) i j ∂μ =
      (Fintype.card k / Fintype.card m : ℝ) * (1 : Matrix m m ℝ) i j) :
    2 * Fintype.card k * (1 - √(Fintype.card k / Fintype.card m : ℝ)) ≤
        ∫ ω, redrawDist U₁ (U₂ ω) ^ 2 ∂μ ∧
      ∫ ω, redrawDist U₁ (U₂ ω) ^ 2 ∂μ ≤ 2 * Fintype.card k := by
  classical
  set r : ℝ := (Fintype.card k : ℝ) with hr
  set d : ℝ := (Fintype.card m : ℝ) with hd
  have hgc : Continuous fun V : m → k → ℝ => redrawDist U₁ (Matrix.of V) := by
    rw [continuous_iff_continuousAt]
    intro V₀
    have hc : Continuous fun V : m → k → ℝ => ‖Matrix.of V - Matrix.of V₀‖ := by
      simp_rw [LeanDLRA.Frobenius.norm_def, Matrix.sub_apply, Matrix.of_apply]
      fun_prop
    have h0 : Tendsto (fun V : m → k → ℝ => ‖Matrix.of V - Matrix.of V₀‖) (𝓝 V₀) (𝓝 0) := by
      simpa using hc.tendsto V₀
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun V => ?_) h0
    rw [Real.dist_eq, abs_le]
    constructor
    · have := redrawDist_le_add U₁ (Matrix.of V₀) (Matrix.of V)
      rw [norm_sub_rev] at this; linarith
    · have := redrawDist_le_add U₁ (Matrix.of V) (Matrix.of V₀); linarith
  have hgm : Measurable fun ω => redrawDist U₁ (U₂ ω) := by
    have h1 : Measurable fun ω => fun i j => U₂ ω i j :=
      measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hmeas i j
    exact hgc.measurable.comp h1
  have hnn : ∀ ω, 0 ≤ redrawDist U₁ (U₂ ω) ^ 2 := fun ω => sq_nonneg _
  have hle : ∀ ω, redrawDist U₁ (U₂ ω) ^ 2 ≤ 2 * r := fun ω => redrawDist_sq_le hU₁ (hU₂ ω)
  have hint : Integrable (fun ω => redrawDist U₁ (U₂ ω) ^ 2) μ :=
    Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable (2 * r)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hnn ω)]; exact hle ω)
  refine ⟨?_, ?_⟩
  swap
  · calc ∫ ω, redrawDist U₁ (U₂ ω) ^ 2 ∂μ ≤ ∫ _ω, 2 * r ∂μ :=
          integral_mono hint (integrable_const _) hle
      _ = 2 * r := by simp
  set F : Ω → ℝ := fun ω => ‖(U₂ ω)ᵀ * U₁‖ with hF
  have hFm : Measurable F := by
    simp only [hF, LeanDLRA.Frobenius.norm_def, Matrix.mul_apply, Matrix.transpose_apply]
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (Finset.measurable_sum _ fun l _ => (hmeas l i).mul_const _).pow_const 2)
  have hFb : ∀ ω, F ω ≤ r := by
    intro ω
    have h1 : ‖(U₂ ω)ᵀ * U₁‖ ≤ ‖(U₂ ω)ᵀ‖ * ‖U₁‖ := LeanDLRA.Frobenius.norm_mul_le _ _
    rw [LeanDLRA.Frobenius.norm_transpose, norm_orth_eq (hU₂ ω), norm_orth_eq hU₁,
      Real.mul_self_sqrt (Nat.cast_nonneg _)] at h1
    exact h1
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => norm_nonneg _
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hFi : Integrable F μ :=
    Integrable.of_bound hFm.aestronglyMeasurable r (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hF0 ω)]; exact hFb ω)
  have hF2i : Integrable (fun ω => F ω ^ 2) μ :=
    Integrable.of_bound (hFm.pow_const 2).aestronglyMeasurable (r ^ 2)
      (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hF0 ω) (hFb ω) 2)
  have hjen : (∫ ω, F ω ∂μ) ^ 2 ≤ ∫ ω, F ω ^ 2 ∂μ := by
    set mF := ∫ ω, F ω ∂μ with hmF
    have h0 : 0 ≤ ∫ ω, (F ω - mF) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have h1 : ∫ ω, (F ω - mF) ^ 2 ∂μ = ∫ ω, F ω ^ 2 ∂μ - mF ^ 2 := by
      have : (fun ω => (F ω - mF) ^ 2) = fun ω => (F ω ^ 2 - 2 * mF * F ω) + mF ^ 2 := by
        funext ω; ring
      have hG : Integrable (fun ω => 2 * mF * F ω) μ := hFi.const_mul _
      have hA : Integrable (fun ω => F ω ^ 2 - 2 * mF * F ω) μ := hF2i.sub hG
      rw [this, integral_add hA (integrable_const _), integral_sub hF2i hG, integral_const_mul]
      simp [← hmF]
      ring
    linarith
  have hF2 : ∀ ω, F ω ^ 2 = ∑ i, ∑ j, (U₁ * U₁ᵀ) j i * (U₂ ω * (U₂ ω)ᵀ) i j := by
    intro ω
    simp only [hF]
    rw [frob_sq_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
    have : U₁ᵀ * U₂ ω * ((U₂ ω)ᵀ * U₁) = U₁ᵀ * ((U₂ ω * (U₂ ω)ᵀ) * U₁) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hPi : ∀ i j, Integrable (fun ω => (U₂ ω * (U₂ ω)ᵀ) i j) μ := by
    intro i j
    have hm : Measurable fun ω => (U₂ ω * (U₂ ω)ᵀ) i j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.measurable_sum _ fun l _ => (hmeas i l).mul (hmeas j l)
    refine Integrable.of_bound hm.aestronglyMeasurable (√r) (Eventually.of_forall fun ω => ?_)
    have h1 := LeanDLRA.Frobenius.abs_apply_le_norm (U₂ ω * (U₂ ω)ᵀ) i j
    rw [LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal (hU₂ ω), norm_orth_eq (hU₂ ω)] at h1
    simpa using h1
  have hEF2 : ∫ ω, F ω ^ 2 ∂μ = r * (r / d) := by
    simp_rw [hF2]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hPi i j).const_mul _]
    have h2 : ∀ i, ∫ ω, ∑ j, (U₁ * U₁ᵀ) j i * (U₂ ω * (U₂ ω)ᵀ) i j ∂μ =
        ∑ j, (U₁ * U₁ᵀ) j i * (r / d * (1 : Matrix m m ℝ) i j) := by
      intro i
      rw [integral_finsetSum _ fun j _ => (hPi i j).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, hiso]
    simp_rw [h2]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    rw [← Finset.sum_mul]
    have htr := trace_mul_transpose hU₁
    simp only [Matrix.trace, Matrix.diag] at htr
    rw [htr]
  have hmF : ∫ ω, F ω ∂μ ≤ √r * √(r / d) := by
    rw [← Real.sqrt_mul hr0, ← hEF2]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hjen)
  have hG : Integrable (fun ω => 2 * √r * F ω) μ := hFi.const_mul _
  have hlow : ∫ ω, (2 * r - 2 * √r * F ω) ∂μ ≤ ∫ ω, redrawDist U₁ (U₂ ω) ^ 2 ∂μ :=
    integral_mono ((integrable_const _).sub hG) hint fun ω => redrawDist_sq_ge hU₁ (hU₂ ω)
  have h1 : ∫ ω, 2 * √r * F ω ∂μ = 2 * √r * ∫ ω, F ω ∂μ := integral_const_mul _ _
  have h2 : ∫ _ω, (2 * r : ℝ) ∂μ = 2 * r := by simp
  rw [integral_sub (integrable_const _) hG, h1, h2] at hlow
  have hs : √r * √r = r := Real.mul_self_sqrt hr0
  have hq : 0 ≤ √(r / d) := Real.sqrt_nonneg _
  have hsr : 0 ≤ √r := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hmF hsr]

private theorem specNorm_kronecker_one_le {n a : Type*} [Fintype n] [Fintype a]
    [DecidableEq n] [DecidableEq a] (N : Matrix a a ℝ) :
    specNorm (Matrix.kronecker (1 : Matrix n n ℝ) N) ≤ specNorm N := by
  classical
  refine specNorm_le_of_col (specNorm_nonneg _) fun B => ?_
  set B' : Matrix a n ℝ := Matrix.of fun β i => B (i, β) () with hB'
  have h1 : ‖B‖ = ‖B'‖ := by
    have e : ‖B‖ ^ 2 = ‖B'‖ ^ 2 := by
      rw [LeanDLRA.Frobenius.norm_sq_eq_sum, LeanDLRA.Frobenius.norm_sq_eq_sum,
        Fintype.sum_prod_type, Finset.sum_comm]
      simp [hB']
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e
  have h2 : ‖Matrix.kronecker (1 : Matrix n n ℝ) N * B‖ = ‖N * B'‖ := by
    have e : ‖Matrix.kronecker (1 : Matrix n n ℝ) N * B‖ ^ 2 = ‖N * B'‖ ^ 2 := by
      rw [LeanDLRA.Frobenius.norm_sq_eq_sum, LeanDLRA.Frobenius.norm_sq_eq_sum,
        Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mul_apply, hB', Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
        Matrix.one_apply]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e
  rw [h1, h2]
  exact frob_mul_le N B'

/-- **OP-RS-25** (TT-cross with nested DEIM; one level of the induction): let `G` be an
orthonormal-column core unfolding, `M` the previous interface matrix, `H = (I ⊗ M) G = Q R`
(orthonormal `Q`) the restricted matrix, and let the next indices `S` be selected on `Q` with DEIM
constant `‖(SᵀQ)⁻¹‖₂ ≤ c`.  Then the new interface matrix `Sᵀ H` is invertible and
`‖(SᵀH)⁻¹‖₂ ≤ c ‖M⁻¹‖₂`; by induction `‖M_j⁻¹‖₂ ≤ ∏ level-wise DEIM constants`.  Meaning: nested
TT-cross-DEIM stays well conditioned level by level. -/
theorem nested_deim_inv_le {n a s : Type*} [Fintype n] [Fintype a] [Fintype s] [DecidableEq n]
    [DecidableEq a] [DecidableEq s] {G Q S : Matrix (n × a) s ℝ} {Mp : Matrix a a ℝ}
    {R : Matrix s s ℝ} {c : ℝ} (hG : Gᵀ * G = 1) (hM : IsUnit Mp.det) (hQ : Qᵀ * Q = 1)
    (hQR : Matrix.kronecker (1 : Matrix n n ℝ) Mp * G = Q * R) (hSQ : IsUnit (Sᵀ * Q).det)
    (hc : specNorm (Sᵀ * Q)⁻¹ ≤ c) :
    IsUnit (Sᵀ * (Matrix.kronecker (1 : Matrix n n ℝ) Mp * G)).det ∧
      specNorm (Sᵀ * (Matrix.kronecker (1 : Matrix n n ℝ) Mp * G))⁻¹ ≤ c * specNorm Mp⁻¹ := by
  set K : Matrix (n × a) (n × a) ℝ := Matrix.kronecker (1 : Matrix n n ℝ) Mp with hK
  set K' : Matrix (n × a) (n × a) ℝ := Matrix.kronecker (1 : Matrix n n ℝ) Mp⁻¹ with hK'
  have hKK : K' * K = 1 := by
    have h := Matrix.mul_kronecker_mul (1 : Matrix n n ℝ) (1 : Matrix n n ℝ) Mp⁻¹ Mp
    rw [Matrix.one_mul, Matrix.nonsing_inv_mul _ hM, Matrix.one_kronecker_one] at h
    exact h.symm
  set L : Matrix s (n × a) ℝ := Gᵀ * K' with hL
  have hLH : L * (Q * R) = 1 := by
    rw [← hQR, hL, Matrix.mul_assoc, ← Matrix.mul_assoc K', hKK, Matrix.one_mul, hG]
  set R' : Matrix s s ℝ := L * Q with hR'
  have hR'R : R' * R = 1 := by rw [hR', Matrix.mul_assoc]; exact hLH
  have hRdet : IsUnit R.det := by
    have := congrArg Matrix.det hR'R
    rw [Matrix.det_mul, Matrix.det_one] at this
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hRinv : R⁻¹ = R' := (Matrix.inv_eq_left_inv hR'R)
  have hR'norm : specNorm R' ≤ specNorm Mp⁻¹ := by
    have h1 : specNorm R' ≤ specNorm L * specNorm Q := specNorm_mul_le _ _
    have h2 : specNorm L ≤ specNorm Gᵀ * specNorm K' := specNorm_mul_le _ _
    have h3 : specNorm Gᵀ ≤ 1 := by
      rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hG
    have h4 : specNorm K' ≤ specNorm Mp⁻¹ := specNorm_kronecker_one_le _
    have h5 : specNorm Q ≤ 1 := specNorm_le_one_of_orthonormal hQ
    have n1 := specNorm_nonneg Q
    have n2 := specNorm_nonneg K'
    have n3 := specNorm_nonneg L
    have n4 := specNorm_nonneg Gᵀ
    have h6 : specNorm L ≤ specNorm Mp⁻¹ := by nlinarith
    nlinarith
  have hdet : IsUnit (Sᵀ * (K * G)).det := by
    rw [hQR, ← Matrix.mul_assoc, Matrix.det_mul]
    exact hSQ.mul hRdet
  refine ⟨hdet, ?_⟩
  have hinv : (Sᵀ * (K * G))⁻¹ = R⁻¹ * (Sᵀ * Q)⁻¹ := by
    rw [hQR, ← Matrix.mul_assoc, Matrix.mul_inv_rev]
  rw [hinv, hRinv]
  have h1 := specNorm_mul_le R' (Sᵀ * Q)⁻¹
  have n5 := specNorm_nonneg (Sᵀ * Q)⁻¹
  have n6 := specNorm_nonneg Mp⁻¹
  nlinarith

/-- **OP-RS-26 (a)** (predictor–corrector rank adaptivity; exact criterion): the R-SVD estimator
`ν = √(‖QQᵀR‖² + c σ²)` (sketched residual plus `c = θ - l - p` unseen singular values padded with
`σ = σ_{l+p}`) is conservative, `‖R‖ ≤ ν`, iff the unsketched residual energy satisfies
`‖(I - QQᵀ)R‖² ≤ c σ²`.  Meaning: conservativity is a checkable spectral-decay condition, not a
theorem. -/
theorem rsvdEstimator_conservative_iff {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq k] {Q : Matrix m k ℝ} (hQ : Qᵀ * Q = 1) (R : Matrix m n ℝ)
    {c σ : ℝ} (hc : 0 ≤ c) :
    ‖R‖ ≤ √(‖Q * Qᵀ * R‖ ^ 2 + c * σ ^ 2) ↔ ‖R - Q * Qᵀ * R‖ ^ 2 ≤ c * σ ^ 2 := by
  have hpy : ‖R‖ ^ 2 = ‖Q * Qᵀ * R‖ ^ 2 + ‖R - Q * Qᵀ * R‖ ^ 2 := by
    rw [Matrix.mul_assoc, norm_sub_sq_real]
    have h1 : ⟪R, Q * (Qᵀ * R)⟫ = ‖Qᵀ * R‖ ^ 2 := by
      rw [LeanDLRA.Frobenius.inner_mul_left', real_inner_self_eq_norm_sq]
    rw [h1, LeanDLRA.Frobenius.norm_mul_of_orthonormal hQ]
    ring
  have := mul_nonneg hc (sq_nonneg σ)
  rw [Real.le_sqrt (norm_nonneg _)]
  · constructor <;> intro h <;> linarith
  · positivity

/-- **OP-RS-26 (b), counterexample**: for `R = diag(1, 2, 2)` and the sketch basis `Q = e₁`
(`l + p = 1`, `θ = 3`, so `c = 2`; `σ_{l+p} = ‖QᵀR‖₂ = 1`), the estimator underestimates:
`ν = √3 < 3 = ‖R‖_F`.  Meaning: the estimator is not conservative when residual energy is hidden
from the sketch. -/
theorem rsvdEstimator_not_conservative :
    let R : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 2, 0; 0, 0, 2]
    let Q : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]
    Qᵀ * Q = 1 ∧ √(‖Q * Qᵀ * R‖ ^ 2 + 2 * specNorm (Qᵀ * R) ^ 2) < ‖R‖ := by
  intro R Q
  have hQ : Qᵀ * Q = 1 := by
    ext i j
    fin_cases i; fin_cases j
    rw [Matrix.mul_apply]
    simp [Q, Fin.sum_univ_succ]
  refine ⟨hQ, ?_⟩
  have hR : ‖R‖ = 3 := by
    rw [LeanDLRA.Frobenius.norm_def]
    simp only [R, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
  have hP : ‖Q * Qᵀ * R‖ = 1 := by
    rw [LeanDLRA.Frobenius.norm_def]
    have : Q * Qᵀ * R = !![1, 0, 0; 0, 0, 0; 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Q, R, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct,
            Function.swap, Matrix.vecHead, Matrix.vecTail]
    rw [this]
    simp [Fin.sum_univ_succ]
  have hS : specNorm (Qᵀ * R) ≤ 1 := by
    refine (specNorm_le_frob _).trans (le_of_eq ?_)
    rw [LeanDLRA.Frobenius.norm_def]
    have : Qᵀ * R = !![1, 0, 0] := by
      ext i j
      fin_cases i; fin_cases j <;> simp [Q, R, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [this]
    simp [Fin.sum_univ_succ]
  rw [hR, hP]
  have h0 := specNorm_nonneg (Qᵀ * R)
  calc √(1 ^ 2 + 2 * specNorm (Qᵀ * R) ^ 2) ≤ √(1 ^ 2 + 2 * 1 ^ 2) := by
        gcongr
    _ < 3 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **OP-RS-27 (a)** (Filippov analysis for DEIM, SRRQR, Osinsky; abstract greedy-pivoting
lemma): if the scores are continuous in `x` and the selection at `x₀` is tie-free, every greedy
selection near `x₀` equals it.  Meaning: greedy index selections are locally constant off the tie
set, so the selection-dependent field is piecewise smooth.  (The error bound itself is
selection-agnostic and already certified: `norm_sub_le_of_filippov`.) -/
theorem greedySelection_eventually_eq {X ι : Type*} [TopologicalSpace X] [Finite ι]
    [DecidableEq ι] {s : X → Finset ι → ι → ℝ} (hs : ∀ T i, Continuous fun x => s x T i)
    {k : ℕ} {x₀ : X} {p₀ : Fin k → ι} (hp₀ : IsStrictGreedySelection s x₀ p₀) :
    ∀ᶠ x in 𝓝 x₀, ∀ p : Fin k → ι, IsGreedySelection s x p → p = p₀ := by
  have hev : ∀ᶠ x in 𝓝 x₀, IsStrictGreedySelection s x p₀ := by
    unfold IsStrictGreedySelection
    refine (eventually_all.2 fun j => ?_)
    refine (eventually_all.2 fun i => ?_)
    by_cases hi : i = p₀ j
    · exact Eventually.of_forall fun x h => absurd hi h
    · have h1 := hp₀ j i hi
      have hc1 : Continuous fun x => s x ((Finset.univ.filter (· < j)).image p₀) i := hs _ _
      have hc2 : Continuous fun x => s x ((Finset.univ.filter (· < j)).image p₀) (p₀ j) := hs _ _
      exact (hc1.continuousAt.eventually_lt hc2.continuousAt h1).mono fun x hx _ => hx
  filter_upwards [hev] with x hx p hp
  have key : ∀ j : Fin k, p j = p₀ j := by
    intro j
    induction j using WellFoundedLT.induction with
    | _ j ih =>
      have himg : (Finset.univ.filter (· < j)).image p = (Finset.univ.filter (· < j)).image p₀ := by
        apply Finset.image_congr
        intro i hi
        exact ih i (by simpa using hi)
      by_contra hne
      have h1 := hx j (p j) hne
      have h2 := hp j (p₀ j)
      rw [himg] at h2
      exact absurd h2 (not_le.2 h1)
  exact funext key

/-- **OP-RS-27 (b)** (limits of selections): a selection that is greedy along a sequence
`x_n → x₀` is greedy at `x₀`; together with (a), the Filippov regularization is generated by
greedy selections at limit points. -/
theorem isGreedySelection_of_tendsto {X ι : Type*} [TopologicalSpace X] [DecidableEq ι]
    {s : X → Finset ι → ι → ℝ} (hs : ∀ T i, Continuous fun x => s x T i) {k : ℕ}
    {x : ℕ → X} {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) {p : Fin k → ι}
    (hp : ∀ n, IsGreedySelection s (x n) p) : IsGreedySelection s x₀ p := by
  intro j i
  have hc : ∀ i', Tendsto (fun n => s (x n) ((Finset.univ.filter (· < j)).image p) i') atTop
      (𝓝 (s x₀ ((Finset.univ.filter (· < j)).image p) i')) := fun i' =>
    ((hs _ i').tendsto x₀).comp hx
  exact le_of_tendsto_of_tendsto' (hc i) (hc (p j)) fun n => hp n j i

end LeanDLRA.OpenProblems.Randomized
