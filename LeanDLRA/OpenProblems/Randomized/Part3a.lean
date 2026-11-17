import LeanDLRA.OpenProblems.Randomized.Part3Defs
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Classical.EckartYoung
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Function.L2Space
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Foundations.ODE

/-!
# Open problems OP-RS-20, OP-RS-21, OP-RS-22, OP-RS-23, OP-RS-24
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius Topology

namespace LeanDLRA.OpenProblems.Randomized

open LeanDLRA.Curvature

/-- **OP-RS-20** (AP semi-Lagrangian DLR method, Lemma 3 with NNLS fallback): let the sampled
weights `w̃` (on `M` samples, mapped by `P`) replace the full weights `w` with exactness residual
`ρ = ‖(PᵀZ)ᵀ w̃ - Zᵀ w‖₂` on the target space `range Z` (`ρ = 0` is the exactness condition (9)).
For `ξ = Z c + e` with `|eᵢ| ≤ η`,
`|w̃ᵀ Pᵀ ξ - wᵀ ξ| ≤ ρ ‖c‖₂ + (‖P w̃‖₁ + ‖w‖₁) η`.  Meaning: Lemma 3 holds with an extra term
proportional to the NNLS residual. -/
theorem nnls_quadrature_error {N M d : Type*} [Fintype N] [Fintype M] [Fintype d]
    {Z : Matrix N d ℝ} {P : Matrix N M ℝ} {w : N → ℝ} {wt : M → ℝ} {c : d → ℝ} {e : N → ℝ}
    {η : ℝ} (he : ∀ i, |e i| ≤ η) :
    |wt ⬝ᵥ (Pᵀ *ᵥ (Z *ᵥ c + e)) - w ⬝ᵥ (Z *ᵥ c + e)| ≤
      √(∑ j, (((Pᵀ * Z)ᵀ *ᵥ wt) j - (Zᵀ *ᵥ w) j) ^ 2) * √(∑ j, c j ^ 2) +
        (∑ i, |(P *ᵥ wt) i| + ∑ i, |w i|) * η := by
  have h1 : wt ⬝ᵥ (Pᵀ *ᵥ (Z *ᵥ c + e)) - w ⬝ᵥ (Z *ᵥ c + e) =
      (((Pᵀ * Z)ᵀ *ᵥ wt) - (Zᵀ *ᵥ w)) ⬝ᵥ c + ((P *ᵥ wt) - w) ⬝ᵥ e := by
    have k1 : wt ⬝ᵥ (Pᵀ *ᵥ (Z *ᵥ c + e)) = (P *ᵥ wt) ⬝ᵥ (Z *ᵥ c + e) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have k2 : (P *ᵥ wt) ⬝ᵥ (Z *ᵥ c) = (Zᵀ *ᵥ (P *ᵥ wt)) ⬝ᵥ c := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have k3 : w ⬝ᵥ (Z *ᵥ c) = (Zᵀ *ᵥ w) ⬝ᵥ c := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have k4 : (Pᵀ * Z)ᵀ *ᵥ wt = Zᵀ *ᵥ (P *ᵥ wt) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]
    rw [k1, k4, dotProduct_add, dotProduct_add, sub_dotProduct,
      sub_dotProduct, k2, k3]
    ring
  rw [h1]
  set a : d → ℝ := ((Pᵀ * Z)ᵀ *ᵥ wt) - (Zᵀ *ᵥ w) with ha
  set b : N → ℝ := (P *ᵥ wt) - w with hb
  have hA : |a ⬝ᵥ c| ≤ √(∑ j, a j ^ 2) * √(∑ j, c j ^ 2) := by
    calc |a ⬝ᵥ c| ≤ ∑ j, |a j| * |c j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          simp [abs_mul]
      _ ≤ √(∑ j, |a j| ^ 2) * √(∑ j, |c j| ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = _ := by simp only [sq_abs]
  have hB : |b ⬝ᵥ e| ≤ (∑ i, |(P *ᵥ wt) i| + ∑ i, |w i|) * η := by
    rcases isEmpty_or_nonempty N with hN | hN
    · simp
    have hη : 0 ≤ η := (abs_nonneg _).trans (he (Classical.arbitrary _))
    calc |b ⬝ᵥ e| ≤ ∑ i, |b i| * |e i| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          simp [abs_mul]
      _ ≤ ∑ i, (|(P *ᵥ wt) i| + |w i|) * η := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : |b i| ≤ |(P *ᵥ wt) i| + |w i| := by
            simpa [hb] using abs_sub (((P *ᵥ wt)) i) (w i)
          calc |b i| * |e i| ≤ |b i| * η := mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_right this hη
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_add_distrib]
  calc |a ⬝ᵥ c + b ⬝ᵥ e| ≤ |a ⬝ᵥ c| + |b ⬝ᵥ e| := abs_add_le _ _
    _ ≤ _ := add_le_add hA hB

/-- **OP-RS-21, counterexample** (oversampled interpolative TT cores): for the oversampled
interpolation matrix `U` (row set `I` of size `2 > 1 = |J|`), the row block `Π = U[I,:]` is an
idempotent different from the identity; the canonical-form condition `Π R = R` holds for
`R = M[I,:]` and its scalar multiples, but fails for a generic update `R'`.  Meaning: PS-type
sweeps with frozen interpolation matrices lose the (relaxed) canonical form. -/
theorem oversampled_tt_canonical_counterexample :
    let Pint : Matrix (Fin 2) (Fin 2) ℝ := ttInterp.submatrix ![0, 1] id
    Pint * Pint = Pint ∧ Pint ≠ 1 ∧ Pint * ttM.submatrix ![0, 1] id = ttM.submatrix ![0, 1] id ∧
      (∀ a : ℝ, Pint * (a • ttM.submatrix ![0, 1] id) = a • ttM.submatrix ![0, 1] id) ∧
      ∃ R' : Matrix (Fin 2) (Fin 2) ℝ, Pint * R' ≠ R' := by
  have hc : ttM.submatrix ![0, 1] ![0] = !![1; 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ttM]
  have hc2 : ttM.submatrix id ![0] = !![1; 1; 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ttM]
  have hG : (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) =
      (!![2] : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  have hGi : ((!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ))⁻¹ =
      (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [hG]
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i; fin_cases j
    simp
  have hU : ttInterp = !![1 / 2, 1 / 2; 1 / 2, 1 / 2; 1, 1] := by
    unfold ttInterp
    rw [hc, hc2, hGi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Function.swap, Matrix.vecHead, Matrix.vecTail]
  intro Pint
  have hP : Pint = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] := by
    simp only [Pint, hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hR : ttM.submatrix ![0, 1] id = !![1, 2; 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ttM]
  refine ⟨?_, ?_, ?_, ?_, 1, ?_⟩
  · rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · rw [hP]
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this
  · rw [hP, hR]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · intro a
    rw [hP, hR]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · rw [hP, Matrix.mul_one]
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this

private theorem deriv_poly_exp (p p' : ℝ → ℝ) (hp : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun t => p t * Real.exp (t ^ 2 / 2)) =
      fun t => (p' t + t * p t) * Real.exp (t ^ 2 / 2) := by
  ext t
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (Real.exp (t ^ 2 / 2) * t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert this using 1
    simp
  exact ((hp t).mul h2).deriv.trans (by ring)

private theorem gauss_moment_two_four :
    ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 ∧ ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have h0 : 0 ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by simp
  have hm : mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := by
    rw [mgf_fun_id_gaussianReal]
    ext t
    simp
  have s1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
    have := deriv_poly_exp (fun _ => 1) (fun _ => 0) (fun t => hasDerivAt_const t 1)
    simpa using this
  have s2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    have := deriv_poly_exp (fun t => t) (fun _ => 1) (fun t => hasDerivAt_id t)
    simpa [sq] using this
  have s3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    have := deriv_poly_exp (fun t => 1 + t ^ 2) (fun t => 2 * t) (fun t => by
      simpa using (hasDerivAt_pow 2 t).const_add 1)
    rw [this]
    ext t
    ring
  have s4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    have := deriv_poly_exp (fun t => 3 * t + t ^ 3) (fun t => 3 + 3 * t ^ 2) (fun t => by
      simpa using ((hasDerivAt_id t).const_mul 3).fun_add (hasDerivAt_pow 3 t))
    rw [this]
    ext t
    ring
  constructor
  · have := iteratedDeriv_mgf_zero h0 2
    rw [hm, iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero, s1, s2] at this
    simpa using this.symm
  · have := iteratedDeriv_mgf_zero h0 4
    rw [hm, iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
      iteratedDeriv_zero, s1, s2, s3, s4] at this
    simpa using this.symm


private theorem gp_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1) (i : Fin M) (a : Fin d) :
    MemLp (fun ω => z ω i a) 4 μ := by
  have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by simp)
  rw [← hz i a] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id (hzm i a).aemeasurable).1 h

private theorem gp_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1) (i : Fin M) (a : Fin d) :
    ∫ ω, z ω i a ∂μ = 0 := by
  have h := integral_map (μ := μ) (hzm i a).aemeasurable (f := fun x : ℝ => x)
    aestronglyMeasurable_id
  rw [hz i a, integral_id_gaussianReal] at h
  exact h.symm

private theorem gp_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1) (i : Fin M) (a : Fin d) :
    ∫ ω, z ω i a ^ 2 ∂μ = 1 := by
  have h := integral_map (μ := μ) (hzm i a).aemeasurable (f := fun x : ℝ => x ^ 2)
    (by fun_prop)
  rw [hz i a, gauss_moment_two_four.1] at h
  exact h.symm

private theorem gp_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1) (i : Fin M) (a : Fin d) :
    ∫ ω, z ω i a ^ 4 ∂μ = 3 := by
  have h := integral_map (μ := μ) (hzm i a).aemeasurable (f := fun x : ℝ => x ^ 4)
    (by fun_prop)
  rw [hz i a, gauss_moment_two_four.2] at h
  exact h.symm

private theorem gp_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {M d : ℕ}
    {z : Ω → Fin M → Fin d → ℝ}
    (hind : iIndepFun (fun (p : Fin M × Fin d) ω => z ω p.1 p.2) μ)
    {p q : Fin M × Fin d} (hpq : p ≠ q) :
    IndepFun (fun ω => z ω p.1 p.2) (fun ω => z ω q.1 q.2) μ :=
  hind.indepFun hpq

private theorem gp_E2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1)
    (hind : iIndepFun (fun (p : Fin M × Fin d) ω => z ω p.1 p.2) μ) (i : Fin M) (a c : Fin d) :
    ∫ ω, z ω i a * z ω i c ∂μ = if a = c then 1 else 0 := by
  by_cases h : a = c
  · subst h
    simp only [ite_true, ← sq]
    exact gp_sq hzm hz i a
  · simp only [h, ↓reduceIte]
    have hi := gp_indep hind (p := (i, a)) (q := (i, c)) (by simpa using h)
    have := hi.integral_fun_mul_eq_mul_integral (hzm i a).aestronglyMeasurable
      (hzm i c).aestronglyMeasurable
    simpa [gp_mean hzm hz] using this

private theorem gp_holder : ENNReal.HolderTriple 4 4 2 :=
  ⟨by
    rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
      ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩

private theorem gp_X_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1) (i : Fin M) (a c : Fin d) :
    MemLp (fun ω => z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) 2 μ := by
  have := gp_holder
  exact ((gp_memLp hzm hz i a).mul (gp_memLp hzm hz i c)).sub (memLp_const _)

private theorem gp_X_int {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1) (i j : Fin M) (a a' c e : Fin d) :
    Integrable (fun ω => (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) *
      (z ω j a' * z ω j e - (if a' = e then (1 : ℝ) else 0))) μ :=
  (gp_X_memLp hzm hz i a c).integrable_mul (gp_X_memLp hzm hz j a' e)

private theorem gp_X_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1)
    (hind : iIndepFun (fun (p : Fin M × Fin d) ω => z ω p.1 p.2) μ) (i : Fin M) (a c : Fin d) :
    ∫ ω, (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) ∂μ = 0 := by
  have := gp_holder
  have h1 : Integrable (fun ω => z ω i a * z ω i c) μ := by
    have := ((gp_memLp hzm hz i a).mul (gp_memLp hzm hz i c)).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
    exact this
  rw [integral_sub h1 (integrable_const _), gp_E2 hzm hz hind]
  simp

private theorem gp_cov_ne {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1)
    (hind : iIndepFun (fun (p : Fin M × Fin d) ω => z ω p.1 p.2) μ) {i j : Fin M} (hij : i ≠ j)
    (a a' c e : Fin d) :
    ∫ ω, (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) *
      (z ω j a' * z ω j e - (if a' = e then (1 : ℝ) else 0)) ∂μ = 0 := by
  have hI := hind.indepFun_prodMk_prodMk (fun p => hzm p.1 p.2) (i, a) (i, c) (j, a') (j, e)
    (fun h => hij (congrArg Prod.fst h)) (fun h => hij (congrArg Prod.fst h))
    (fun h => hij (congrArg Prod.fst h)) (fun h => hij (congrArg Prod.fst h))
  have hI2 := hI.comp (φ := fun x : ℝ × ℝ => x.1 * x.2 - (if a = c then (1 : ℝ) else 0))
    (ψ := fun x : ℝ × ℝ => x.1 * x.2 - (if a' = e then (1 : ℝ) else 0)) (by fun_prop)
    (by fun_prop)
  have := hI2.integral_fun_mul_eq_mul_integral
    ((((hzm i a).mul (hzm i c)).sub measurable_const).aestronglyMeasurable)
    ((((hzm j a').mul (hzm j e)).sub measurable_const).aestronglyMeasurable)
  simp only [Function.comp_def] at this
  rw [this, gp_X_mean hzm hz hind, zero_mul]

private theorem gp_int_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1) (i : Fin M) (a : Fin d) :
    Integrable (fun ω => z ω i a ^ 2) μ ∧ Integrable (fun ω => z ω i a ^ 4) μ := by
  refine ⟨((gp_memLp hzm hz i a).mono_exponent (by norm_num : (2 : ENNReal) ≤ 4)).integrable_sq,
    ?_⟩
  have := (gp_memLp hzm hz i a).integrable_norm_pow (p := 4) (by norm_num)
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  exact Even.pow_abs ⟨2, by norm_num⟩ _

private theorem gp_cov_same {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d : ℕ} {z : Ω → Fin M → Fin d → ℝ}
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1)
    (hind : iIndepFun (fun (p : Fin M × Fin d) ω => z ω p.1 p.2) μ) (i : Fin M) (a c e : Fin d) :
    ∫ ω, (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) *
      (z ω i a * z ω i e - (if a = e then (1 : ℝ) else 0)) ∂μ =
      if c = e then 1 + (if a = c then (1 : ℝ) else 0) else 0 := by
  by_cases hce : c = e
  · subst hce
    by_cases hac : a = c
    · subst hac
      obtain ⟨h2, h4⟩ := gp_int_pow hzm hz i a
      have e1 : (fun ω => (z ω i a * z ω i a - (if a = a then (1 : ℝ) else 0)) *
          (z ω i a * z ω i a - (if a = a then (1 : ℝ) else 0))) =
          fun ω => z ω i a ^ 4 - 2 * z ω i a ^ 2 + 1 := by
        ext ω
        simp only [ite_true]
        ring
      have h42 : Integrable (fun ω => z ω i a ^ 4 - 2 * z ω i a ^ 2) μ :=
        h4.sub (h2.const_mul 2)
      rw [e1, integral_add h42 (integrable_const (1 : ℝ)), integral_sub h4 (h2.const_mul 2),
        integral_const_mul, gp_four hzm hz, gp_sq hzm hz]
      simp only [ite_true]
      norm_num
    · have e1 : (fun ω => (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) *
          (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0))) =
          fun ω => z ω i a ^ 2 * z ω i c ^ 2 := by
        ext ω
        simp only [hac, ↓reduceIte]
        ring
      have hI := (gp_indep hind (p := (i, a)) (q := (i, c)) (fun h => hac (congrArg Prod.snd h)))
      have hI2 := hI.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2) (by fun_prop)
        (by fun_prop)
      have := hI2.integral_fun_mul_eq_mul_integral
        ((hzm i a).pow_const 2).aestronglyMeasurable ((hzm i c).pow_const 2).aestronglyMeasurable
      simp only [Function.comp_def] at this
      rw [e1, this, gp_sq hzm hz, gp_sq hzm hz]
      simp [hac]
  · simp only [hce, ↓reduceIte]
    by_cases hac : a = c
    · subst hac
      have e1 : (fun ω => (z ω i a * z ω i a - (if a = a then (1 : ℝ) else 0)) *
          (z ω i a * z ω i e - (if a = e then (1 : ℝ) else 0))) =
          fun ω => ((z ω i a ^ 2 - 1) * z ω i a) * z ω i e := by
        ext ω
        simp only [hce, ↓reduceIte]
        ring
      have hI := (gp_indep hind (p := (i, a)) (q := (i, e)) (fun h => hce (congrArg Prod.snd h)))
      have hI2 := hI.comp (φ := fun x : ℝ => (x ^ 2 - 1) * x) (ψ := fun x : ℝ => x)
        (by fun_prop) (by fun_prop)
      have := hI2.integral_fun_mul_eq_mul_integral
        ((((hzm i a).pow_const 2).sub_const 1).mul (hzm i a)).aestronglyMeasurable
        (hzm i e).aestronglyMeasurable
      simp only [Function.comp_def] at this
      rw [e1, this, gp_mean hzm hz, mul_zero]
    · by_cases hae : a = e
      · subst hae
        have e1 : (fun ω => (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) *
            (z ω i a * z ω i a - (if a = a then (1 : ℝ) else 0))) =
            fun ω => ((z ω i a ^ 2 - 1) * z ω i a) * z ω i c := by
          ext ω
          simp only [hac, ↓reduceIte]
          ring
        have hI := (gp_indep hind (p := (i, a)) (q := (i, c))
          (fun h => hac (congrArg Prod.snd h)))
        have hI2 := hI.comp (φ := fun x : ℝ => (x ^ 2 - 1) * x) (ψ := fun x : ℝ => x)
          (by fun_prop) (by fun_prop)
        have := hI2.integral_fun_mul_eq_mul_integral
          ((((hzm i a).pow_const 2).sub_const 1).mul (hzm i a)).aestronglyMeasurable
          (hzm i c).aestronglyMeasurable
        simp only [Function.comp_def] at this
        rw [e1, this, gp_mean hzm hz, mul_zero]
      · have e1 : (fun ω => (z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0)) *
            (z ω i a * z ω i e - (if a = e then (1 : ℝ) else 0))) =
            fun ω => z ω i a ^ 2 * (z ω i c * z ω i e) := by
          ext ω
          simp only [hac, hae, ↓reduceIte]
          ring
        have hI := hind.indepFun_mul_left (fun p => hzm p.1 p.2) (i, c) (i, e) (i, a)
          (fun h => hac (congrArg Prod.snd h).symm) (fun h => hae (congrArg Prod.snd h).symm)
        have hI2 := hI.symm.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x) (by fun_prop)
          (by fun_prop)
        have := hI2.integral_fun_mul_eq_mul_integral
          ((hzm i a).pow_const 2).aestronglyMeasurable
          ((hzm i c).mul (hzm i e)).aestronglyMeasurable
        simp only [Function.comp_def, Pi.mul_apply] at this
        rw [e1, this, gp_sq hzm hz, gp_E2 hzm hz hind]
        simp [hce]

/-- **OP-RS-22** (PSI surrogate with stochastic transpose estimates; erratum): for `M` independent
standard Gaussian probes `zᵢ ∈ ℝ^d`, the unnormalized estimator `∑ᵢ zᵢ zᵢᵀ B` of
`B = ΔAᵀ U` has expectation `M B` (so the `1/M` factor is missing), and the normalized estimator
`(1/M) ∑ᵢ zᵢ zᵢᵀ B` has mean-square error `(d + 1) ‖B‖_F² / M`.  Meaning: the corrected estimator is
unbiased with explicit variance. -/
theorem gaussianProbe_mean_mse {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M d k : ℕ} (hM : 0 < M) (z : Ω → Fin M → Fin d → ℝ)
    (hzm : ∀ i a, Measurable fun ω => z ω i a)
    (hz : ∀ i a, μ.map (fun ω => z ω i a) = gaussianReal 0 1)
    (hind : iIndepFun (fun (p : Fin M × Fin d) ω => z ω p.1 p.2) μ)
    (B : Matrix (Fin d) (Fin k) ℝ) :
    (∀ a b, ∫ ω, (∑ i, Matrix.vecMulVec (z ω i) (z ω i) * B) a b ∂μ = M * B a b) ∧
      ∫ ω, ∑ a, ∑ b,
          (((M : ℝ)⁻¹ • ∑ i, Matrix.vecMulVec (z ω i) (z ω i) * B) a b - B a b) ^ 2 ∂μ =
        (d + 1) / M * ∑ a, ∑ b, B a b ^ 2 := by
  have := gp_holder
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hprod : ∀ i a c, Integrable (fun ω => z ω i a * z ω i c) μ := fun i a c =>
    ((gp_memLp hzm hz i a).mul (gp_memLp hzm hz i c)).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  constructor
  · intro a b
    have e1 : (fun ω => (∑ i, Matrix.vecMulVec (z ω i) (z ω i) * B) a b) =
        fun ω => ∑ i, ∑ c, z ω i a * z ω i c * B c b := by
      ext ω
      simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
    rw [e1, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun c _ => (hprod i a c).mul_const _))]
    have : ∀ i : Fin M, ∫ ω, ∑ c, z ω i a * z ω i c * B c b ∂μ = B a b := by
      intro i
      rw [integral_finsetSum _ (fun c _ => (hprod i a c).mul_const _)]
      simp only [integral_mul_const, gp_E2 hzm hz hind]
      simp
    simp [this]
  · obtain ⟨X, hXdef⟩ : ∃ X : Fin M → Fin d → Fin d → Ω → ℝ, ∀ i a c ω,
        X i a c ω = z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0) :=
      ⟨fun i a c ω => z ω i a * z ω i c - (if a = c then (1 : ℝ) else 0), fun _ _ _ _ => rfl⟩
    have hXint : ∀ i j a c e, Integrable (fun ω => X i a c ω * X j a e ω) μ := by
      intro i j a c e
      simp only [hXdef]
      exact gp_X_int hzm hz i j a a c e
    have hK : ∀ i j a c e, ∫ ω, X i a c ω * X j a e ω ∂μ =
        if i = j then (if c = e then 1 + (if a = c then (1 : ℝ) else 0) else 0) else 0 := by
      intro i j a c e
      simp only [hXdef]
      by_cases hij : i = j
      · subst hij
        simp only [ite_true]
        exact gp_cov_same hzm hz hind i a c e
      · simp only [hij, ↓reduceIte]
        exact gp_cov_ne hzm hz hind hij a a c e
    have hpt : ∀ ω a b, (((M : ℝ)⁻¹ • ∑ i, Matrix.vecMulVec (z ω i) (z ω i) * B) a b - B a b) =
        (M : ℝ)⁻¹ * ∑ i, ∑ c, X i a c ω * B c b := by
      intro ω a b
      simp only [hXdef, sub_mul, Finset.sum_sub_distrib, Matrix.smul_apply, Matrix.sum_apply,
        Matrix.mul_apply, Matrix.vecMulVec_apply, smul_eq_mul, ite_mul, zero_mul, one_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hsq : ∀ ω a b, ((M : ℝ)⁻¹ * ∑ i, ∑ c, X i a c ω * B c b) ^ 2 =
        (M : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ∑ c, ∑ e,
          (X i a c ω * X j a e ω) * (B c b * B e b) := by
      intro ω a b
      rw [mul_pow, sq (∑ i, ∑ c, X i a c ω * B c b)]
      congr 1
      simp only [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
      ring
    have hT : ∀ (a : Fin d) (b : Fin k) (i j : Fin M) (c e : Fin d),
        Integrable (fun ω => (X i a c ω * X j a e ω) * (B c b * B e b)) μ :=
      fun a b i j c e => (hXint i j a c e).mul_const _
    have hS : ∀ (a : Fin d) (b : Fin k), Integrable (fun ω => ∑ i, ∑ j, ∑ c, ∑ e,
        (X i a c ω * X j a e ω) * (B c b * B e b)) μ := fun a b =>
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun e _ => hT a b i j c e
    have hin : ∀ (a : Fin d) (b : Fin k),
        ∫ ω, ∑ i, ∑ j, ∑ c, ∑ e, (X i a c ω * X j a e ω) * (B c b * B e b) ∂μ =
        ∑ i : Fin M, ∑ j : Fin M, ∑ c, ∑ e, (if i = j then
          (if c = e then 1 + (if a = c then (1 : ℝ) else 0) else 0) else 0) *
            (B c b * B e b) := by
      intro a b
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun e _ => hT a b i j c e)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ =>
        integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun e _ => hT a b i j c e)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ fun e _ => hT a b i j c e)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [integral_finsetSum _ (fun e _ => hT a b i j c e)]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [integral_mul_const, hK]
    have e1 : (fun ω => ∑ a, ∑ b, (((M : ℝ)⁻¹ • ∑ i, Matrix.vecMulVec (z ω i) (z ω i) * B) a b -
        B a b) ^ 2) = fun ω => ∑ a, ∑ b, (M : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ∑ c, ∑ e,
          (X i a c ω * X j a e ω) * (B c b * B e b) := by
      ext ω
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hpt, hsq]
    have hcalc : ∀ (a : Fin d) (b : Fin k), ∑ i : Fin M, ∑ j : Fin M, ∑ c, ∑ e,
        (if i = j then (if c = e then 1 + (if a = c then (1 : ℝ) else 0) else 0) else 0) *
          (B c b * B e b) = M * ∑ c, (1 + (if a = c then (1 : ℝ) else 0)) * (B c b * B c b) := by
      intro a b
      have h1 : ∀ i j : Fin M, ∑ c, ∑ e,
          (if i = j then (if c = e then 1 + (if a = c then (1 : ℝ) else 0) else 0) else 0) *
            (B c b * B e b) =
          if i = j then ∑ c, (1 + (if a = c then (1 : ℝ) else 0)) * (B c b * B c b) else 0 := by
        intro i j
        by_cases hij : i = j
        · simp [hij, ite_mul]
        · simp [hij]
      simp only [h1]
      simp
    rw [e1, integral_finsetSum _ (fun a _ => integrable_finsetSum _
      fun b _ => (hS a b).const_mul _)]
    have e2 : ∀ a : Fin d, ∫ ω, ∑ b, (M : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ∑ c, ∑ e,
        (X i a c ω * X j a e ω) * (B c b * B e b) ∂μ =
        ∑ b, (M : ℝ)⁻¹ ^ 2 * (M * ∑ c, (1 + (if a = c then (1 : ℝ) else 0)) *
          (B c b * B c b)) := by
      intro a
      rw [integral_finsetSum _ (fun b _ => (hS a b).const_mul _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul, hin a b, hcalc a b]
    simp only [e2]
    have h4 : ∀ b : Fin k, ∑ a : Fin d, (M : ℝ)⁻¹ ^ 2 * ((M : ℝ) *
        ∑ c, (1 + (if a = c then (1 : ℝ) else 0)) * (B c b * B c b)) =
        (d + 1) / M * ∑ c, B c b ^ 2 := by
      intro b
      have h3 : ∀ c : Fin d, ∑ a : Fin d, (1 + (if a = c then (1 : ℝ) else 0)) = d + 1 := by
        intro c
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      have h5 : ∀ y : Fin d, ∑ x : Fin d, (1 + (if x = y then (1 : ℝ) else 0)) *
          (B y b * B y b) = (d + 1) * (B y b * B y b) := by
        intro y
        rw [← Finset.sum_mul, h3]
      rw [Finset.sum_congr rfl (fun y _ => h5 y), ← Finset.mul_sum]
      simp only [sq]
      field_simp
    rw [Finset.sum_comm]
    simp only [h4]
    rw [← Finset.mul_sum, Finset.sum_comm]

private theorem prk_step_aux {U V : Matrix (Fin 2) (Fin 1) ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {a : ℝ} (ha : a ≠ 0) (hUY : U * Uᵀ * !![a, 0; 0, 0] = !![a, 0; 0, 0])
    (hVY : !![a, 0; 0, 0] * V * Vᵀ = !![a, 0; 0, 0]) :
    tangentProj U V !![-1, 0; 0, 1] = !![-1, 0; 0, 0] := by
  have e1 : U 0 0 * U 0 0 + U 1 0 * U 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 0) 0
  have e2 : V 0 0 * V 0 0 + V 1 0 * V 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hV 0) 0
  have e3 : U 0 0 * U 0 0 * a = a := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hUY 0) 0
  have e4 : V 0 0 * V 0 0 * a = a := by
    have := congrFun (congrFun hVY 0) 0
    have h2 : a * V 0 0 * V 0 0 = a := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] at this
      simpa [Matrix.of_apply, Matrix.cons_val', Fin.isValue] using this
    linarith
  have u0 : U 0 0 * U 0 0 = 1 := by
    have : a * (U 0 0 * U 0 0 - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ha
    · linarith
  have v0 : V 0 0 * V 0 0 = 1 := by
    have : a * (V 0 0 * V 0 0 - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ha
    · linarith
  have u1 : U 1 0 = 0 := by nlinarith
  have v1 : V 1 0 = 0 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tangentProj_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, u1,
      v1, u0, v0]

private theorem rank_diag_aux (c : ℝ) : (!![c, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank ≤ 1 := by
  have : (!![c, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![c; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  rw [this]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_width _)

/-- **OP-RS-23 (a), PRK lower bound** (randomized low-rank RK vs projected RK, Example 1 type):
for `A' = diag(-1, 1)`, `A(0) = diag(1, 0)` (exact solution `A(t) = diag(1-t, t)`, of rank one at
`t = 1`), the projected Euler method with rank-one truncation,
`Y_{j+1} = T₁(Y_j + h P(Y_j) G)`, `h = 1/N`, keeps every iterate diagonal with zero `(2,2)` entry
and has error `≥ 1` at `t = 1`, for every `N`.  Meaning: PRK incurs an `O(1)` error where a
randomized method (whose sketch sees the `e₂` direction) can converge. -/
theorem prk_stuck (N : ℕ) (hN : 0 < N) {Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    {U V : ℕ → Matrix (Fin 2) (Fin 1) ℝ} (hU : ∀ j, (U j)ᵀ * U j = 1)
    (hV : ∀ j, (V j)ᵀ * V j = 1) (hUY : ∀ j, U j * (U j)ᵀ * Y j = Y j)
    (hVY : ∀ j, Y j * V j * (V j)ᵀ = Y j) (hY0 : Y 0 = !![1, 0; 0, 0])
    (hY : ∀ j, Y (j + 1) = EckartYoung.truncation
      (Y j + (1 / N : ℝ) • tangentProj (U j) (V j) !![-1, 0; 0, 1]) 1) :
    (∀ j ≤ N, Y j 1 1 = 0) ∧ 1 ≤ ‖Y N - !![0, 0; 0, 1]‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ j ≤ N, Y j = !![1 - (j : ℝ) / N, 0; 0, 0] := by
    intro j
    induction j with
    | zero => intro _; simp [hY0]
    | succ j ih =>
      intro hj
      have hjN : j < N := hj
      have ih := ih hjN.le
      have hlt : (j : ℝ) / N < 1 := by
        rw [div_lt_one hNr]; exact_mod_cast hjN
      have ha : (1 - (j : ℝ) / N) ≠ 0 := by linarith
      have hUY' := hUY j
      have hVY' := hVY j
      rw [ih] at hUY' hVY'
      have ht := prk_step_aux (hU j) (hV j) ha hUY' hVY'
      rw [hY j, ht, ih]
      have : (!![1 - (j : ℝ) / N, 0; 0, 0] + (1 / N : ℝ) • !![-1, 0; 0, 0] :
          Matrix (Fin 2) (Fin 2) ℝ) = !![1 - ((j + 1 : ℕ) : ℝ) / N, 0; 0, 0] := by
        ext i k
        fin_cases i <;> fin_cases k <;> simp; field_simp; ring
      rw [this]
      have h2 := EckartYoung.norm_sub_truncation_le
        (!![1 - ((j + 1 : ℕ) : ℝ) / N, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        (rank_diag_aux (1 - ((j + 1 : ℕ) : ℝ) / N))
      rw [sub_self, norm_zero] at h2
      exact (sub_eq_zero.mp (norm_le_zero_iff.mp h2)).symm
  refine ⟨fun j hj => by simp [key j hj], ?_⟩
  rw [key N le_rfl, div_self hNr.ne', sub_self]
  have : (!![0, 0; 0, 0] - !![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = -!![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [this, norm_neg, Matrix.frobenius_norm_def]
  simp [Fin.sum_univ_two]

/-- **OP-RS-23 (b), counterexample** (degenerate case): `distLR_two_mul_le` is false as stated,
because `IsLipschitzField F L` does not force `0 ≤ L` when the matrix space is a singleton (here
`m = Fin 0`), so the right-hand side `h (ε + L B h)` can be negative while `distLR ≥ 0`.  With
`L = -1`, `B = 1`, `h = 1`, `ε = 0` all hypotheses hold.  The statement needs the extra hypothesis
`0 ≤ L`. -/
theorem distLR_two_mul_le_counterexample :
    ∃ (F : ℝ → Matrix (Fin 0) (Fin 1) ℝ → Matrix (Fin 0) (Fin 1) ℝ) (L B ε t₀ h : ℝ)
      (U : Matrix (Fin 0) (Fin 0) ℝ) (V : Matrix (Fin 1) (Fin 0) ℝ) (S : Matrix (Fin 0) (Fin 0) ℝ)
      (A : ℝ → Matrix (Fin 0) (Fin 1) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsLipschitzField F L ∧ IsBoundedField F B ∧ 0 ≤ h ∧
        ODESolution F A t₀ (t₀ + h) ∧ A t₀ = U * S * Vᵀ ∧
        (∀ t ∈ Icc t₀ (t₀ + h),
          ‖F t (U * S * Vᵀ) - tangentProj U V (F t (U * S * Vᵀ))‖ ≤ ε) ∧
        ¬ (distLR (2 * Fintype.card (Fin 0)) (A (t₀ + h)) ≤ h * (ε + L * B * h)) := by
  have hs : ∀ x y : Matrix (Fin 0) (Fin 1) ℝ, x = y := fun x y => Subsingleton.elim x y
  refine ⟨fun _ _ => 0, -1, 1, 0, 0, 1, 0, 0, 0, fun _ => 0, Subsingleton.elim _ _,
    Subsingleton.elim _ _, ?_, ?_, zero_le_one, ?_, rfl, ?_, ?_⟩
  · intro t x y
    rw [hs x y]
    simp
  · intro t x
    simp
  · refine ⟨continuousOn_const, fun t _ => ?_⟩
    simpa using hasDerivWithinAt_const t (Ici t) (0 : Matrix (Fin 0) (Fin 1) ℝ)
  · intro t _
    simp
  · have := distLR_nonneg (r := 2 * Fintype.card (Fin 0)) (X := (0 : Matrix (Fin 0) (Fin 1) ℝ))
    simp only [Fintype.card_fin, mul_zero] at this ⊢
    norm_num
    exact lt_of_lt_of_le (by norm_num) this

/-- **OP-RS-24 (a)** (deterministic trace inequalities): for orthonormal `U₁, U₂ ∈ ℝ^{d × r}`,
`2r - 2 √(r tr(P₁ P₂)) ≤ redrawDist(U₁, U₂)² ≤ 2r`. -/
theorem redrawDist_sq_bounds {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U₁ U₂ : Matrix m k ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) :
    2 * Fintype.card k - 2 * √(Fintype.card k * Matrix.trace (U₁ * U₁ᵀ * (U₂ * U₂ᵀ))) ≤
        redrawDist U₁ U₂ ^ 2 ∧ redrawDist U₁ U₂ ^ 2 ≤ 2 * Fintype.card k := by
  have hcard : ∀ {W : Matrix k k ℝ}, Wᵀ * W = 1 → ‖W‖ ^ 2 = Fintype.card k := by
    intro W hW
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hW, Matrix.trace_one]
  have h1 : ‖U₁‖ ^ 2 = Fintype.card k := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hU₁, Matrix.trace_one]
  have hsq : ∀ W : Matrix k k ℝ, Wᵀ * W = 1 →
      ‖U₁ - U₂ * W‖ ^ 2 = 2 * Fintype.card k - 2 * ⟪U₁, U₂ * W⟫ := by
    intro W hW
    rw [norm_sub_sq_real, h1, Frobenius.norm_mul_of_orthonormal hU₂, hcard hW]
    ring
  have hD : ‖U₂ᵀ * U₁‖ ^ 2 = Matrix.trace (U₁ * U₁ᵀ * (U₂ * U₂ᵀ)) := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    calc Matrix.trace (U₁ᵀ * U₂ * (U₂ᵀ * U₁))
        = Matrix.trace (U₁ * (U₁ᵀ * U₂ * (U₂ᵀ))) := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hle : ∀ W : Matrix k k ℝ, Wᵀ * W = 1 →
      ⟪U₁, U₂ * W⟫ ≤ √(Fintype.card k * Matrix.trace (U₁ * U₁ᵀ * (U₂ * U₂ᵀ))) := by
    intro W hW
    rw [Frobenius.inner_mul_left']
    refine (real_inner_le_norm _ _).trans ?_
    rw [Real.sqrt_mul (Nat.cast_nonneg _), ← hD, ← hcard hW,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm]
  have hne : Nonempty {W : Matrix k k ℝ // Wᵀ * W = 1} := ⟨⟨1, by simp⟩⟩
  have hbdd : BddBelow (Set.range fun W : {W : Matrix k k ℝ // Wᵀ * W = 1} => ‖U₁ - U₂ * W.1‖) :=
    ⟨0, by rintro _ ⟨W, rfl⟩; exact norm_nonneg _⟩
  have hnn : 0 ≤ redrawDist U₁ U₂ := Real.iInf_nonneg fun W => norm_nonneg _
  constructor
  · set c : ℝ := 2 * Fintype.card k - 2 * √(Fintype.card k * Matrix.trace (U₁ * U₁ᵀ * (U₂ * U₂ᵀ)))
      with hc
    by_cases hc0 : c ≤ 0
    · exact hc0.trans (sq_nonneg _)
    replace hc0 : 0 < c := not_le.1 hc0
    have : √c ≤ redrawDist U₁ U₂ := by
      refine le_ciInf fun W => ?_
      refine Real.sqrt_le_iff.2 ⟨norm_nonneg _, ?_⟩
      rw [hsq W.1 W.2]
      have := hle W.1 W.2
      linarith
    calc c = √c ^ 2 := (Real.sq_sqrt hc0.le).symm
      _ ≤ _ := by gcongr
  · have hx : ∃ W : {W : Matrix k k ℝ // Wᵀ * W = 1}, 0 ≤ ⟪U₁, U₂ * W.1⟫ := by
      rcases le_total 0 ⟪U₁, U₂ * (1 : Matrix k k ℝ)⟫ with h | h
      · exact ⟨⟨1, by simp⟩, h⟩
      · refine ⟨⟨-1, by simp⟩, ?_⟩
        simp only [Matrix.mul_neg, Matrix.mul_one, inner_neg_right] at h ⊢
        linarith
    obtain ⟨W, hW⟩ := hx
    have h2 : redrawDist U₁ U₂ ≤ ‖U₁ - U₂ * W.1‖ := ciInf_le hbdd W
    calc redrawDist U₁ U₂ ^ 2 ≤ ‖U₁ - U₂ * W.1‖ ^ 2 := by gcongr
      _ ≤ _ := by rw [hsq W.1 W.2]; linarith

end LeanDLRA.OpenProblems.Randomized
