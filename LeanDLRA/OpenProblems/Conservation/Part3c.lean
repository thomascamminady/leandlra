import LeanDLRA.OpenProblems.Conservation.Part3Defs
import LeanDLRA.Stability.Conservation
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.KStep
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Conservation.Part1Defs

/-!
# Open problems OP-CO-22, OP-CO-23, OP-CO-26, OP-CO-27, OP-CO-30
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Conservation

section Abstract3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Abstract3

section Matrix3

open scoped LeanDLRA.Frobenius

/-- Auxiliary: an affine curve `a + (t - t₀) • c` solves the ODE with constant field `c`. -/
private theorem odeSolution_affine_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a c : E) (t₀ t₁ : ℝ) :
    ODESolution (fun (_ : ℝ) (_ : E) => c) (fun t => a + (t - t₀) • c) t₀ t₁ := by
  refine ⟨?_, fun t _ => ?_⟩
  · exact (continuous_const.add ((continuous_id.sub continuous_const).smul
      continuous_const)).continuousOn
  · have h := (((hasDerivAt_id t).sub_const t₀).smul_const c).const_add a
    simpa using h.hasDerivWithinAt

/-- **OP-CO-22** (arXiv 1705.10175, Sec. 3.2).  For the differential Lyapunov equation with
constant symmetric right-hand side `F(Y) = Q`, one exact-substep KSL step from the symmetric
`Y₀ = e₁e₁ᵀ` with `r = 1`, `τ = 1/2` returns `Y₁ = P₁ (Y₀ + τ Q)` with asymmetry
`(Y₁)₁₂ - (Y₁)₂₁ = 1/10`: projector splitting does not preserve symmetry (the symmetric BUG
step does, `bug_symm`). -/
theorem ksl_breaks_symmetry :
    ∃ (U₁ : Matrix (Fin 2) (Fin 1) ℝ) (ε : ℝ) (YK YS YL : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      U₁ᵀ * U₁ = 1 ∧
      IsKSLStep (fun _ _ => coQ) ε (leftProj U₁) (rightProj coE1) 0 (1 / 2) coE11 YK YS YL ∧
      YL (1 / 2) 0 1 - YL (1 / 2) 1 0 = 1 / 10 := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin 2) (Fin 1) ℝ, U = !![2 / √5; 1 / √5] := ⟨_, rfl⟩
  have h5 : (√5 : ℝ) * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h5ne : (√5 : ℝ) ≠ 0 := by positivity
  have hU : Uᵀ * U = 1 := by
    rw [hUdef]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
    field_simp
    linarith
  have hE : coE1ᵀ * coE1 = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [coE1, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨U, ‖(1 - leftProj U) ((1 - rightProj coE1) coQ)‖,
    fun t => coE11 + (t - 0) • rightProj coE1 coQ,
    fun t => (coE11 + ((1 / 2 : ℝ) - 0) • rightProj coE1 coQ) +
      (t - 0) • -(leftProj U (rightProj coE1 coQ)),
    fun t => ((coE11 + ((1 / 2 : ℝ) - 0) • rightProj coE1 coQ) +
      ((1 / 2 : ℝ) - 0) • -(leftProj U (rightProj coE1 coQ))) + (t - 0) • leftProj U coQ,
    hU, ?_, ?_⟩
  · refine ⟨isOrthProj_leftProj hU, isOrthProj_rightProj hE,
      odeSolution_affine_const _ _ _ _, by simp, ?_, fun t _ => le_rfl,
      odeSolution_affine_const _ _ _ _, by simp, odeSolution_affine_const _ _ _ _, by simp⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [leftProj_apply, rightProj_apply, hUdef, coE11, coQ, coE1, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;>
      field_simp <;> nlinarith [h5]
  · simp [leftProj_apply, rightProj_apply, hUdef, coE11, coQ, coE1, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
    field_simp
    nlinarith [h5]

/-- **OP-CO-23, negative (ii)** (arXiv 2311.06399 §5; 2101.12571 §6.1).  A continuous-time Galerkin
S-step on the spatial basis `X̂` cannot reproduce local moment laws: for `F(Y) = W Y` (rotation in
`x`), conserved velocity direction `U = e₁` (moment map `Y ↦ Y e₁e₁ᵀ`) and `X̂ = span e₁`, the
projected moment flux `P̂ ⟨F(Y_S), U⟩` vanishes while `⟨F(Y_S), U⟩ = W e₁ ≠ 0` at `Y_S = e₁e₁ᵀ`.
The negative claim (i) on explicit Euler for the factor equations is not stated (the scheme is
not specified). -/
theorem galerkinS_misses_moment_law :
    leftProj coE1 (rightProj coE1 (coRot * coE11)) = 0 ∧ rightProj coE1 (coRot * coE11) ≠ 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [leftProj_apply, rightProj_apply, coE1, coRot, coE11, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Function.swap, Matrix.vecHead, Matrix.vecTail]
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    simp [rightProj_apply, coE1, coRot, coE11, Matrix.mul_apply] at h10

/-- **OP-CO-30** (arXiv 2011.06072, Sec. 3.3, eq. (25)).  The HOLO moment-matching correction
`K ↦ K + δK` with `(K + δK) V₃ = T` (`V₃ ∈ ℝ^{r×3}` the projections of the three moment
directions onto the angular basis) is solvable for every `T` iff `rank V₃ = 3`. -/
theorem holo_correction_solvable_iff {nx r : Type*} [Fintype r] [Nonempty nx]
    (K : Matrix nx r ℝ) (V3 : Matrix r (Fin 3) ℝ) :
    (∀ T : Matrix nx (Fin 3) ℝ, ∃ dK : Matrix nx r ℝ, (K + dK) * V3 = T) ↔ V3.rank = 3 := by
  have hrk : V3.rank = 3 ↔ Function.Surjective V3.vecMul := by
    rw [Matrix.vecMul_surjective_iff_rank_eq_card, Fintype.card_fin]
  rw [hrk]
  constructor
  · intro h y
    obtain ⟨x0⟩ := ‹Nonempty nx›
    obtain ⟨dK, hdK⟩ := h (Matrix.of fun _ j => y j)
    refine ⟨(K + dK) x0, ?_⟩
    have hx := congrFun hdK x0
    rw [Matrix.mul_apply_eq_vecMul] at hx
    exact hx
  · intro h T
    obtain ⟨B, hB⟩ := Matrix.vecMul_surjective_iff_exists_left_inverse.mp h
    refine ⟨(T - K * V3) * B, ?_⟩
    rw [Matrix.add_mul, Matrix.mul_assoc, hB, Matrix.mul_one]
    abel

/-- Auxiliary: right multiplication by a symmetric idempotent is a Frobenius contraction. -/
private theorem norm_mul_proj_le_frob {nx r : Type*} [Fintype nx] [Fintype r]
    (X : Matrix nx r ℝ) (P : Matrix r r ℝ) (hPt : Pᵀ = P) (hPP : P * P = P) :
    ‖X * P‖ ≤ ‖X‖ := by
  have h1 : ⟪X * P, X * P⟫ = ⟪X, X * P⟫ := by
    rw [Frobenius.inner_mul_right, hPt, Matrix.mul_assoc, hPP]
  have h2 : ⟪X, X * P⟫ ≤ ‖X‖ * ‖X * P‖ := real_inner_le_norm _ _
  have h3 : ⟪X * P, X * P⟫ = ‖X * P‖ ^ 2 := real_inner_self_eq_norm_sq _
  nlinarith [norm_nonneg X, norm_nonneg (X * P)]

/-- **OP-CO-30, minimum-norm correction** (arXiv 2011.06072, eq. (25)).  If `V₃ᵀ V₃` is
invertible, `δK = (T - K V₃)(V₃ᵀ V₃)⁻¹ V₃ᵀ` solves `(K + δK) V₃ = T` with minimal Frobenius norm;
if the moment directions lie in the basis (`V₃ᵀ V₃ = 1`) it is exact moment replacement
`(T - K V₃) V₃ᵀ`. -/
theorem holo_correction_min_norm {nx r : Type*} [Fintype nx] [Fintype r]
    (K : Matrix nx r ℝ) (V3 : Matrix r (Fin 3) ℝ) (hV : IsUnit (V3ᵀ * V3).det)
    (T : Matrix nx (Fin 3) ℝ) :
    (K + (T - K * V3) * (V3ᵀ * V3)⁻¹ * V3ᵀ) * V3 = T ∧
      (∀ dK' : Matrix nx r ℝ, (K + dK') * V3 = T →
        ‖(T - K * V3) * (V3ᵀ * V3)⁻¹ * V3ᵀ‖ ≤ ‖dK'‖) ∧
      (V3ᵀ * V3 = 1 → (T - K * V3) * (V3ᵀ * V3)⁻¹ * V3ᵀ = (T - K * V3) * V3ᵀ) := by
  have hPt : (V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ)ᵀ = V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ := by
    simp [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.mul_assoc]
  have hPP : (V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ) * (V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ) =
      V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ := by
    have e : (V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ) * (V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ) =
        V3 * ((V3ᵀ * V3)⁻¹ * (V3ᵀ * V3)) * ((V3ᵀ * V3)⁻¹ * V3ᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.nonsing_inv_mul _ hV, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · have hmid : (T - K * V3) * (V3ᵀ * V3)⁻¹ * V3ᵀ * V3 = T - K * V3 := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV, Matrix.mul_one]
    rw [Matrix.add_mul, hmid]
    abel
  · intro dK' hdK'
    have h2 : dK' * V3 = T - K * V3 := by
      rw [← hdK', Matrix.add_mul]
      abel
    have hP : dK' * (V3 * (V3ᵀ * V3)⁻¹ * V3ᵀ) = (T - K * V3) * (V3ᵀ * V3)⁻¹ * V3ᵀ := by
      rw [← h2]
      simp only [Matrix.mul_assoc]
    rw [← hP]
    exact norm_mul_proj_le_frob dK' _ hPt hPP
  · intro h1
    rw [h1, inv_one, Matrix.mul_one]

end Matrix3

/-- **OP-CO-27 (a)** (arXiv 2311.09425 Rem. 1; 2608.00397 §4).  On a periodic grid (`ZMod N`), the
Poisson operator `D₊D₋` and the centred derivative `D_c = (D₊ + D₋)/2` satisfy
`Σᵢ (D₊D₋φ)ᵢ (D_cφ)ᵢ = 0` and `Σᵢ ρ₀ (D_cφ)ᵢ = 0`, which gives current conservation together
with Gauss's law. -/
theorem periodic_sbp_identities {N : ℕ} [NeZero N] (φ : ZMod N → ℝ) (Δx ρ₀ : ℝ) :
    ∑ i, (φ (i + 1) - 2 * φ i + φ (i - 1)) / Δx ^ 2 * ((φ (i + 1) - φ (i - 1)) / (2 * Δx)) = 0 ∧
      ∑ i, ρ₀ * ((φ (i + 1) - φ (i - 1)) / (2 * Δx)) = 0 := by
  have hsub : ∀ g : ZMod N → ℝ, ∑ i, g (i - 1) = ∑ i, g i := fun g =>
    Equiv.sum_comp (Equiv.subRight (1 : ZMod N)) g
  have hadd : ∀ g : ZMod N → ℝ, ∑ i, g (i + 1) = ∑ i, g i := fun g =>
    Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) g
  constructor
  · have key : ∀ i : ZMod N,
        (φ (i + 1) - 2 * φ i + φ (i - 1)) / Δx ^ 2 * ((φ (i + 1) - φ (i - 1)) / (2 * Δx)) =
          1 / (2 * Δx ^ 3) * ((φ (i + 1) - φ i) ^ 2 - (φ i - φ (i - 1)) ^ 2) := by
      intro i
      ring
    rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, Finset.sum_sub_distrib]
    have h1 : ∑ i : ZMod N, (φ (i + 1) - φ i) ^ 2 = ∑ i : ZMod N, (φ i - φ (i - 1)) ^ 2 := by
      have := hsub (fun i => (φ (i + 1) - φ i) ^ 2)
      simp only [sub_add_cancel] at this
      exact this.symm
    rw [h1, sub_self, mul_zero]
  · have key : ∀ i : ZMod N,
        ρ₀ * ((φ (i + 1) - φ (i - 1)) / (2 * Δx)) =
          ρ₀ / (2 * Δx) * (φ (i + 1) - φ (i - 1)) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, Finset.sum_sub_distrib,
      hadd φ, hsub φ, sub_self, mul_zero]

end LeanDLRA.OpenProblems.Conservation
