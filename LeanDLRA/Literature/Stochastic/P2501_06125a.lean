import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Results of arXiv 2501.06125: Low-rank control variates for uncertain radiative transfer

Scope of this module (arXiv:2501.06125, Patwardhan, Stammer, Løvbak, Kusch, Krumscheid).

* **Sec. 3.1, Eq. 6** (`mc_mse_decomp`). For i.i.d. realisations `X i` of a random vector in
  `ℝ^d` with finite second moments, the mean squared error of the Monte Carlo estimator
  `(1/N) ∑ X i` against a deterministic target `Q` is `(1/N) Var + ‖E X − Q‖²`, with
  `Var = E‖X − E X‖²`. This is Eq. 6 combined with the unnumbered display after it,
  `E‖Q̂ − E Q̂‖² = (1/N) Var`. The paper's `Q_{r;MC}` is `(1/N) ∑ G(Y_k(v_i))` and
  `Q_r = E[G(Y_k)]`. The target `Q` here is an arbitrary deterministic vector, so the statement
  is the same bias-variance identity for any target. The underlying random vector is an
  arbitrary `EuclideanSpace ℝ (Fin d)`-valued sequence, not the radiative transfer solution; the
  paper's matrix-valued QoI in `ℝ^{m̃×ñ}` with the Frobenius norm is the case `d = m̃ ñ` after
  vectorisation (the paper allows any norm induced by an inner product).
* **Sec. 3.2, Eq. 8** (`cv_estimator_eq`). The control-variate estimator
  `(1/N) ∑ G_CV(v_i)`, with `G_CV = G(Y^r) − α (G(Y^s) − E G(Y^s))`, equals
  `α E[G(Y^s)] + (1/N) ∑ (G(Y^r(v_i)) − α G(Y^s(v_i)))`. This is pure algebra and holds
  for any sample sequences `a`, `b` in a real vector space with `N > 0`.
* **Sec. 3.2, variance formula** (`cv_variance_expand`). The paper states
  `Var(G_CV) = Var_r + α² Var_s − 2α Cov_rs`, with `Cov_rs = E⟨G(Y^r) − Q_r, G(Y^s) − Q_s⟩`.
  Proved here for a real inner product space `E`, with `Var` defined as `E‖· − E ·‖²`.
* **Sec. 3.2, optimal α** (`cv_optimal_alpha`). For `Var_s > 0`, the quadratic
  `α ↦ Var_r − 2α Cov + α² Var_s` (real numbers `VA`, `VB`, `C`, not tied to random variables)
  is minimised at `α* = Cov / Var_s`. This is the paper's `α* = Cov_rs / Var_s`. The minimum
  value `Var_r − Cov² / Var_s` is computed in the proof but is not part of the statement. The
  hypothesis `Var_s > 0` is needed for `α*` to be defined; the paper does not state it. The
  paper takes `α > 0`; here every real `α` is allowed.

**Not formalized.**
* **Thm 1** (local error bound for augmented BUG with truncation under uncertain initial data)
  and **Thm 2** (global error bound). Their proofs use the augmented BUG local error analysis
  of [6, 7], the truncation lemma of [27, Lemma 3], and the Lipschitz / Gronwall argument on
  the random realisations. The library has the deterministic ingredients
  (`galerkin_step_error`, `kstep_capture_inexact`, `lady_windermere`), but not the random
  ensemble version with the paper's constants `c̃₀`, `c̃₁`, `c₂`. Neither is stated here.
* The sample-size heuristic `N_CVdiff = Var_r (1 − Corr²_rs)/ϵ²` of Sec. 4.2 (numerical
  experiments), which the paper states for known `α*` without proof, is not formalized.
* The i.i.d. assumption in `mc_mse_decomp` is the paper's standing assumption for the Monte
  Carlo estimator, and is what gives the `1/N` factor. It is not an extra assumption.

**Core definitions used.** None of the library's DLRA definitions are needed: the results
are about Monte Carlo averages and variances of vector-valued random variables, with the
dynamical integrator entering only through the random variable `G(Y)`. Local definitions are
the coordinate-sum split of the Euclidean norm and the variance as `E‖· − E ·‖²`, both
expressed directly with Mathlib's `integral` and `variance`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.Literature.P2501_06125

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real bias-variance identity: `E[(f − c)²] = Var f + (E f − c)²`. -/
lemma integral_sq_sub_const {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : MemLp f 2 P) (c : ℝ) :
    ∫ ω, (f ω - c) ^ 2 ∂P = variance f P + (∫ ω, f ω ∂P - c) ^ 2 := by
  have h1 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
  have h2 : Integrable f P := hf.integrable (by norm_num)
  have i1 : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω) P := h1.sub (h2.const_mul (2 * c))
  have e : (fun ω => (f ω - c) ^ 2) = fun ω => (f ω ^ 2 - 2 * c * f ω) + c ^ 2 := by
    funext ω; ring
  rw [variance_eq_sub hf, e, integral_add i1 (integrable_const _),
    integral_sub h1 (h2.const_mul (2 * c)), integral_const_mul, integral_const]
  simp
  ring

/-- The squared Euclidean norm is the sum of squared coordinates. -/
lemma norm_sq_eq_sum_coord {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = ∑ k, (x k) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Eq. 6** (bias-variance decomposition of the Monte Carlo MSE), together with the display
after it, `Var(Q̂) = (1/N) Var`. Let `X i` be i.i.d.
`ℝ^d`-valued random vectors with finite second moments and `N > 0`. Then with
`μ = E X₀`, `Var = E‖X₀ − μ‖²` and deterministic target `Q`:
`E‖(1/N) ∑_{i<N} X i − Q‖² = (1/N) Var + ‖μ − Q‖²`. -/
theorem mc_mse_decomp {d N : ℕ} (hN : 0 < N) {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)} (hX : ∀ i, MemLp (X i) 2 P)
    (hind : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (Q : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, ‖(N : ℝ)⁻¹ • ∑ i ∈ range N, X i ω - Q‖ ^ 2 ∂P
      = (N : ℝ)⁻¹ * ∫ ω, ‖X 0 ω - ∫ ω', X 0 ω' ∂P‖ ^ 2 ∂P
        + ‖(∫ ω, X 0 ω ∂P) - Q‖ ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hint : ∀ i, Integrable (X i) P := fun i => (hX i).integrable (by norm_num)
  set μ : EuclideanSpace ℝ (Fin d) := ∫ ω, X 0 ω ∂P with hμ
  have hc : ∀ i k, MemLp (fun ω => X i ω k) 2 P := fun i k =>
    (hX i).continuousLinearMap_comp
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
  have hmeas : ∀ k, Measurable (fun x : EuclideanSpace ℝ (Fin d) => x k) := fun k =>
    (EuclideanSpace.proj k).continuous.measurable
  have hcoord_id : ∀ i k, ∫ ω, X i ω k ∂P = ∫ ω, X 0 ω k ∂P := fun i k =>
    ((hid i).comp (hmeas k)).integral_eq
  have hmu : ∀ k, ∫ ω, X 0 ω k ∂P = μ k := fun k => by
    have h := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj k) (hint 0)
    rw [hμ]
    exact h
  set V : Fin d → ℝ := fun k => variance (fun ω => X 0 ω k) P with hV
  have hv : ∀ i k, variance (fun ω => X i ω k) P = V k := fun i k =>
    ((hid i).comp (hmeas k)).variance_eq
  -- pointwise coordinate expansion of the estimator error
  have hpt : ∀ ω, ‖(N : ℝ)⁻¹ • ∑ i ∈ range N, X i ω - Q‖ ^ 2
      = ∑ k, ((N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω k - Q k) ^ 2 := by
    intro ω
    rw [norm_sq_eq_sum_coord]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_apply]
  have hYmem : ∀ k, MemLp (fun ω => (N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω k) 2 P := fun k => by
    have h := (memLp_finsetSum' (range N) (fun i _ => hc i k)).const_mul ((N : ℝ)⁻¹)
    convert h using 1
    funext ω
    simp [Finset.sum_apply]
  -- mean of each coordinate of the estimator
  have hmeanY : ∀ k, ∫ ω, (N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω k ∂P = μ k := fun k => by
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hc i k).integrable (by norm_num)),
      Finset.sum_congr rfl (fun i _ => hcoord_id i k), hmu k]
    simp [Finset.sum_const, card_range]
    field_simp
  -- variance of each coordinate of the estimator
  have hVmean : ∀ k,
      variance (fun ω => (N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω k) P = (N : ℝ)⁻¹ * V k := by
    intro k
    have hfun : (fun ω => (N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω k)
        = fun ω => (N : ℝ)⁻¹ * (∑ i ∈ range N, (fun ω => X i ω k)) ω := by
      funext ω; simp [Finset.sum_apply]
    have hpair : Set.Pairwise (↑(range N) : Set ℕ) fun i j =>
        (fun ω => X i ω k) ⟂ᵢ[P] (fun ω => X j ω k) := by
      intro i _ j _ hij
      exact (hind.indepFun hij).comp (hmeas k) (hmeas k)
    rw [hfun, variance_const_mul, IndepFun.variance_sum (fun i _ => hc i k) hpair]
    simp only [hv]
    simp [Finset.sum_const, card_range]
    field_simp
  -- total variance as the sum of coordinate variances
  have hsqsum : ∫ ω, ‖X 0 ω - μ‖ ^ 2 ∂P = ∑ k, V k := by
    have hp : ∀ ω, ‖X 0 ω - μ‖ ^ 2 = ∑ k, (X 0 ω k - μ k) ^ 2 := fun ω => by
      rw [norm_sq_eq_sum_coord]; simp
    have hint2 : ∀ k ∈ (univ : Finset (Fin d)), Integrable (fun ω => (X 0 ω k - μ k) ^ 2) P :=
      fun k _ => ((hc 0 k).sub (memLp_const (μ k))).integrable_sq
    simp_rw [hp]
    rw [integral_finsetSum _ hint2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_sq_sub_const (hc 0 k), hmu k, sub_self]
    simp [hV]
  have hmuQ : ‖μ - Q‖ ^ 2 = ∑ k, (μ k - Q k) ^ 2 := by
    rw [norm_sq_eq_sum_coord]; simp
  have key : ∀ k, ∫ ω, ((N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω k - Q k) ^ 2 ∂P
      = (N : ℝ)⁻¹ * V k + (μ k - Q k) ^ 2 := fun k => by
    rw [integral_sq_sub_const (hYmem k), hmeanY k, hVmean k]
  simp only [hpt]
  have hYint : ∀ k ∈ (univ : Finset (Fin d)),
      Integrable (fun ω => ((N : ℝ)⁻¹ * ∑ i ∈ range N, X i ω k - Q k) ^ 2) P :=
    fun k _ => ((hYmem k).sub (memLp_const (Q k))).integrable_sq
  rw [integral_finsetSum _ hYint,
    Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib, ← Finset.mul_sum, hmuQ,
    hsqsum]

/-- Squared norm of a difference with a scalar multiple, integrated. Used for Eq. 8. -/
lemma integral_norm_sub_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Measure Ω} [IsProbabilityMeasure P] {u v : Ω → E} (hu : MemLp u 2 P)
    (hv : MemLp v 2 P) (α : ℝ) :
    ∫ ω, ‖u ω - α • v ω‖ ^ 2 ∂P
      = ∫ ω, ‖u ω‖ ^ 2 ∂P - 2 * α * ∫ ω, inner ℝ (u ω) (v ω) ∂P + α ^ 2 * ∫ ω, ‖v ω‖ ^ 2 ∂P := by
  have hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P := hu.norm.integrable_sq
  have hv2 : Integrable (fun ω => ‖v ω‖ ^ 2) P := hv.norm.integrable_sq
  have hi : Integrable (fun ω => inner ℝ (u ω) (v ω)) P := by
    have hm : AEStronglyMeasurable (fun ω => inner ℝ (u ω) (v ω)) P :=
      AEStronglyMeasurable.inner hu.aestronglyMeasurable hv.aestronglyMeasurable
    refine Integrable.mono' (hu2.add hv2) hm (Filter.Eventually.of_forall fun ω => ?_)
    change ‖inner ℝ (u ω) (v ω)‖ ≤ ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2
    have h : ‖inner ℝ (u ω) (v ω)‖ ≤ ‖u ω‖ * ‖v ω‖ := norm_inner_le_norm _ _
    nlinarith [sq_nonneg (‖u ω‖ - ‖v ω‖), norm_nonneg (u ω), norm_nonneg (v ω)]
  have hpt : ∀ ω, ‖u ω - α • v ω‖ ^ 2
      = ‖u ω‖ ^ 2 - 2 * α * inner ℝ (u ω) (v ω) + α ^ 2 * ‖v ω‖ ^ 2 := by
    intro ω
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  simp_rw [hpt]
  have i1 : Integrable (fun ω => ‖u ω‖ ^ 2 - 2 * α * inner ℝ (u ω) (v ω)) P :=
    hu2.sub (hi.const_mul (2 * α))
  rw [integral_add i1 (hv2.const_mul _), integral_sub hu2 (hi.const_mul _),
    integral_const_mul, integral_const_mul]

/-- **Sec. 3.2 variance of the control variate.** With `G_CV = A − α (B − E B)`, the variance
`E‖G_CV − E G_CV‖²` equals `Var_A + α² Var_B − 2α Cov_AB`, where `Cov_AB = E⟨A − E A, B − E B⟩`. -/
theorem cv_variance_expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {A B : Ω → E} (hA : MemLp A 2 P)
    (hB : MemLp B 2 P) (α : ℝ) :
    ∫ ω, ‖(A ω - α • (B ω - ∫ ω', B ω' ∂P))
        - ∫ ω', (A ω' - α • (B ω' - ∫ ω'', B ω'' ∂P)) ∂P‖ ^ 2 ∂P
      = ∫ ω, ‖A ω - ∫ ω', A ω' ∂P‖ ^ 2 ∂P
        - 2 * α * ∫ ω, inner ℝ (A ω - ∫ ω', A ω' ∂P) (B ω - ∫ ω', B ω' ∂P) ∂P
        + α ^ 2 * ∫ ω, ‖B ω - ∫ ω', B ω' ∂P‖ ^ 2 ∂P := by
  have hAi : Integrable A P := hA.integrable (by norm_num)
  have hBi : Integrable B P := hB.integrable (by norm_num)
  have hic : Integrable (fun ω => B ω - ∫ ω', B ω' ∂P) P := hBi.sub (integrable_const _)
  have hmean : ∫ ω, (A ω - α • (B ω - ∫ ω', B ω' ∂P)) ∂P = ∫ ω, A ω ∂P := by
    have h2 : ∫ ω, α • (B ω - ∫ ω', B ω' ∂P) ∂P = 0 := by
      rw [integral_smul, integral_sub hBi (integrable_const _), integral_const]
      simp
    have h3 : ∫ ω, (A ω - α • (B ω - ∫ ω', B ω' ∂P)) ∂P
        = ∫ ω, A ω ∂P - ∫ ω, α • (B ω - ∫ ω', B ω' ∂P) ∂P :=
      integral_sub hAi (Integrable.smul α hic)
    rw [h3, h2, sub_zero]
  have hfun : ∀ ω, (A ω - α • (B ω - ∫ ω', B ω' ∂P)) - ∫ ω', A ω' ∂P
      = (A ω - ∫ ω', A ω' ∂P) - α • (B ω - ∫ ω', B ω' ∂P) := fun ω => by abel
  rw [hmean]
  simp_rw [hfun]
  exact integral_norm_sub_smul_sq (hA.sub (memLp_const _)) (hB.sub (memLp_const _)) α

/-- **Sec. 3.2 optimal control-variate coefficient.** If `Var_B > 0`, the quadratic
`α ↦ Var_A − 2α Cov + α² Var_B` is minimised at `α* = Cov / Var_B` (the paper's
`α* = Cov_rs / Var_s`). The minimum value `Var_A − Cov² / Var_B` is used in the proof but not
stated. `VA`, `VB`, `C` are arbitrary reals; combine with `cv_variance_expand` for variances. -/
theorem cv_optimal_alpha {VA VB C : ℝ} (hVB : 0 < VB) (α : ℝ) :
    VA - 2 * (C / VB) * C + (C / VB) ^ 2 * VB ≤ VA - 2 * α * C + α ^ 2 * VB := by
  have h3 : VA - 2 * (C / VB) * C + (C / VB) ^ 2 * VB = VA - C ^ 2 / VB := by
    field_simp
    ring
  have h : VB * (α - C / VB) ^ 2 = α ^ 2 * VB - 2 * α * C + C ^ 2 / VB := by
    field_simp
    ring
  have h4 : 0 ≤ VB * (α - C / VB) ^ 2 := mul_nonneg hVB.le (sq_nonneg _)
  rw [h3]
  nlinarith [h, h4]

/-- **Sec. 3.2, Eq. 8** (rearrangement of the control-variate estimator). For `N > 0`,
the average of `G_CV(v_i) = a i − α (b i − m)` equals `α m + (1/N) ∑ (a i − α b i)`, where
`m` plays the role of `E[G(Y^s)]`. -/
theorem cv_estimator_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {N : ℕ} (hN : 0 < N)
    (a b : ℕ → E) (m : E) (α : ℝ) :
    (N : ℝ)⁻¹ • ∑ i ∈ range N, (a i - α • (b i - m))
      = α • m + (N : ℝ)⁻¹ • ∑ i ∈ range N, (a i - α • b i) := by
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have h1 : ∀ i, a i - α • (b i - m) = (a i - α • b i) + α • m := fun i => by
    rw [smul_sub]; abel
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_add, smul_smul, inv_mul_cancel₀ hNr, one_smul, add_comm]

end LeanDLRA.Literature.P2501_06125
