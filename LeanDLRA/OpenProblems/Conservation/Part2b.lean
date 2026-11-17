import LeanDLRA.OpenProblems.Conservation.Part2Defs
import LeanDLRA.Stability.Conservation
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.OpenProblems.Conservation.Part1Defs

/-!
# Open problems OP-CO-14, OP-CO-15, OP-CO-16, OP-CO-17
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Conservation

section APLimit

variable {nx nv r : Type*} [Fintype nx] [Fintype nv] [Fintype r] [DecidableEq r]

end APLimit

section Oblique

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Oblique

section Constrained

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **OP-CO-14 (c), size of the correction** (arXiv 1803.00499 §5.3; 1807.02338 §3).  If the Gram
matrix of the `P c_j` is bounded below by `γ > 0`, `‖c_j‖ ≤ M` and the normal component is at most
`ε`, the correction satisfies `‖Σ λ_j P c_j‖ ≤ √k M ε / √γ`, so the constrained DLRA inherits the
robust continuous error bound with `ε` replaced by `ε (1 + √k M / √γ)`. -/
theorem constrainedDF_correction_le {k : ℕ} {P : E →L[ℝ] E} (hP : IsOrthProj P)
    (c : Fin k → E) {γ M ε : ℝ} (hγ : 0 < γ)
    (hG : ∀ μ : Fin k → ℝ, γ * ∑ j, μ j ^ 2 ≤ ‖∑ j, μ j • P (c j)‖ ^ 2)
    (hM : ∀ j, ‖c j‖ ≤ M) {F : E} (hε : ‖F - P F‖ ≤ ε) {lam : Fin k → ℝ}
    (hlam : ∀ i, ∑ j, ⟪P (c i), P (c j)⟫ * lam j = ⟪c i, F - P F⟫) :
    ‖∑ j, lam j • P (c j)‖ ≤ Real.sqrt k * M * ε / Real.sqrt γ := by
  have _ := hP
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ⟨0, hk⟩)
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  set r : Fin k → ℝ := fun i => ⟪c i, F - P F⟫ with hr
  have hri : ∀ i, r i ^ 2 ≤ (M * ε) ^ 2 := by
    intro i
    have h1 : |r i| ≤ ‖c i‖ * ‖F - P F‖ := abs_real_inner_le_norm _ _
    have h2 : |r i| ≤ M * ε :=
      h1.trans (mul_le_mul (hM i) hε (norm_nonneg _) hM0)
    exact (sq_le_sq' (by linarith [neg_abs_le (r i)]) (le_trans (le_abs_self _) h2))
  set A : ℝ := ∑ j, lam j ^ 2 with hA
  set z : E := ∑ j, lam j • P (c j) with hz
  have hB : ∑ i, r i ^ 2 ≤ k * (M * ε) ^ 2 := by
    calc ∑ i, r i ^ 2 ≤ ∑ _i : Fin k, (M * ε) ^ 2 := Finset.sum_le_sum fun i _ => hri i
      _ = k * (M * ε) ^ 2 := by simp
  have hzsq : ‖z‖ ^ 2 = ∑ i, lam i * r i := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hz]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum]
    simp only [inner_smul_right, RCLike.conj_to_real]
    have := hlam i
    simp only [hr]
    rw [← this, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hCS : (∑ i, lam i * r i) ^ 2 ≤ A * ∑ i, r i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ lam r
  have hγA : γ * A ≤ ‖z‖ ^ 2 := hG lam
  have hkey : γ * ‖z‖ ^ 2 ≤ k * (M * ε) ^ 2 := by
    rcases (sq_nonneg ‖z‖).eq_or_lt with h0 | hpos
    · rw [← h0]; have : 0 ≤ (k : ℝ) * (M * ε) ^ 2 := by positivity
      linarith
    · set T := ‖z‖ ^ 2
      have hA0 : 0 ≤ A := by positivity
      have h1 : T ^ 2 ≤ A * (k * (M * ε) ^ 2) := by
        rw [hzsq] at hpos ⊢
        exact hCS.trans (mul_le_mul_of_nonneg_left hB hA0)
      have h2 : γ * T ^ 2 ≤ T * (k * (M * ε) ^ 2) := by
        calc γ * T ^ 2 ≤ γ * (A * (k * (M * ε) ^ 2)) := by gcongr
          _ = (γ * A) * (k * (M * ε) ^ 2) := by ring
          _ ≤ T * (k * (M * ε) ^ 2) := by gcongr
      have h3 : T * (γ * T) ≤ T * (k * (M * ε) ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left h3 hpos
  have hsg : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  rw [le_div_iff₀ hsg]
  have hrhs : 0 ≤ Real.sqrt k * M * ε := by positivity
  have hsq : (‖z‖ * Real.sqrt γ) ^ 2 ≤ (Real.sqrt k * M * ε) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hγ.le, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) hrhs (by norm_num)).1 hsq

end Constrained

section MassCounterexample

open scoped LeanDLRA.Frobenius

private theorem odeSol_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {y y' : ℝ → E} {a b : ℝ} (hd : ∀ t, HasDerivAt y (y' t) t)
    (hf : ∀ t, f t (y t) = y' t) : ODESolution f y a b where
  cont := fun t _ => (hd t).continuousAt.continuousWithinAt
  deriv := fun t _ => by rw [hf t]; exact (hd t).hasDerivWithinAt

private theorem coE1_mul_transpose : coE1 * coE1ᵀ = coE11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coE1, coE11, Matrix.mul_apply]

private theorem coE1_transpose_mul : coE1ᵀ * coE1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [coE1, Matrix.mul_apply]

/-- **OP-CO-15, fixed-basis Galerkin step** (arXiv 1804.04561 §5.1; 1912.07522 §3.4; 2105.04358).
For `F(Y) = D Y` the mass `⟪1 1ᵀ, Y⟫` is conserved by the full flow, but the Galerkin step with
fixed bases `U = V = e₁` from `Y₀ = e₁e₁ᵀ` gives mass `e^{-h}`. -/
theorem fixedBasis_galerkin_loses_mass {h : ℝ} (hh : 0 ≤ h) :
    (∀ Y : Matrix (Fin 2) (Fin 2) ℝ, ⟪coOnes, coD * Y⟫ = 0) ∧
      ∃ y : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
        ODESolution (fun _ Y => leftProj coE1 (rightProj coE1 (coD * Y))) y 0 h ∧
        y 0 = coE11 ∧ ⟪coOnes, y h⟫ = Real.exp (-h) := by
  have _ := hh
  refine ⟨?_, fun t => Real.exp (-t) • coE11, ?_, by simp, ?_⟩
  · intro Y
    rw [Frobenius.inner_def]
    simp [Fin.sum_univ_two, coOnes, coD, Matrix.mul_apply]
    ring
  · refine odeSol_of_hasDerivAt (y' := fun t => (-Real.exp (-t)) • coE11) (fun t => ?_)
      (fun t => ?_)
    · simpa using (hasDerivAt_neg t).exp.smul_const coE11
    · rw [leftProj_apply, rightProj_apply', coE1_mul_transpose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coE11, coD, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [inner_smul_right, Frobenius.inner_def]
    simp [Fin.sum_univ_two, coOnes, coE11]

private theorem coD_mul (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    coD * Y = !![-Y 0 0 + Y 1 0, -Y 0 1 + Y 1 1; Y 0 0 - Y 1 0, Y 0 1 - Y 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [coD] <;> ring

private theorem col_mul_transpose (u1 u2 : ℝ) :
    (!![u1; u2] : Matrix (Fin 2) (Fin 1) ℝ) * (!![u1; u2] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ
      = !![u1 * u1, u1 * u2; u2 * u1, u2 * u2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

private theorem mass_gt_one (q : ℝ) (h0 : 0 < q) (h1 : q < 2 / 5) :
    1 < ((1 + q) / 2) / ((1 + q ^ 2) / 2) * (1 - q ^ 2 / (2 * ((1 + q ^ 2) / 2))) := by
  have hp : 0 < 1 + q ^ 2 := by positivity
  have : ((1 + q) / 2) / ((1 + q ^ 2) / 2) * (1 - q ^ 2 / (2 * ((1 + q ^ 2) / 2)))
      = (1 + q) / (1 + q ^ 2) ^ 2 := by
    field_simp
    ring
  rw [this, lt_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg q, mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0, sq_nonneg (q ^ 2)]

/-- **OP-CO-15, fixed-rank BUG step** (arXiv 2302.01391 §7.2; 2309.08252; 2601.11900).  For
`F(Y) = D Y`, `Y₀ = e₁e₁ᵀ`, `r = 1` and `h = 1/2`, the exact-substep BUG step changes the mass (to
about `1.069`): the L-step basis stays `e₁`, so `Q₁ (1 1ᵀ) ≠ 1 1ᵀ`. -/
theorem fixedRankBUG_changes_mass :
    ∃ (U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (ε : ℝ) (YK YL YS : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      U₁ᵀ * U₁ = 1 ∧ V₁ᵀ * V₁ = 1 ∧
      IsBUGStep (fun _ Y => coD * Y) ε (leftProj coE1) (rightProj coE1) (leftProj U₁)
        (rightProj V₁) 0 (1 / 2) coE11 YK YL YS ∧
      ⟪coOnes, YS (1 / 2)⟫ ≠ 1 := by
  set q : ℝ := Real.exp (-1) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 2 / 5 := by
    have h := Real.exp_one_gt_d9
    have : q = (Real.exp 1)⁻¹ := by rw [hqdef, Real.exp_neg]
    rw [this, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  obtain ⟨n, hnpos, hn⟩ : ∃ n : ℝ, 0 < n ∧ n ^ 2 = (1 + q ^ 2) / 2 :=
    ⟨Real.sqrt ((1 + q ^ 2) / 2), Real.sqrt_pos.2 (by positivity),
      Real.sq_sqrt (by positivity)⟩
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ, u1 = (1 + q) / 2 / n := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2 : ℝ, u2 = (1 - q) / 2 / n := ⟨_, rfl⟩
  have ha : (1 + q) / 2 = n * u1 := by rw [hu1]; field_simp
  have hb : (1 - q) / 2 = n * u2 := by rw [hu2]; field_simp
  have hu : u1 ^ 2 + u2 ^ 2 = 1 := by
    have : n ^ 2 * (u1 ^ 2 + u2 ^ 2) = n ^ 2 * 1 := by
      have h1 : n ^ 2 * (u1 ^ 2 + u2 ^ 2) = ((1 + q) / 2) ^ 2 + ((1 - q) / 2) ^ 2 := by
        rw [ha, hb]; ring
      rw [h1, hn]; ring
    exact mul_left_cancel₀ (by positivity) this
  set c : ℝ := (u1 - u2) ^ 2 with hc
  refine ⟨!![u1; u2], coE1, 0,
    fun t => Real.exp (-(2 * t)) • (!![1 / 2, 0; -1 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      + (!![1 / 2, 0; 1 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ),
    fun t => Real.exp (-t) • coE11,
    fun t => (u1 * Real.exp (-(c * t))) • (!![u1, 0; u2, 0] : Matrix (Fin 2) (Fin 2) ℝ),
    ?_, coE1_transpose_mul, ?_, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simpa [pow_two] using hu
  · have hU : (!![u1; u2] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![u1; u2] = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simpa [pow_two] using hu
    refine ⟨isOrthProj_leftProj coE1_transpose_mul, isOrthProj_rightProj coE1_transpose_mul,
      isOrthProj_leftProj hU, isOrthProj_rightProj coE1_transpose_mul,
      fun x => leftProj_rightProj_comm _ _ x, ?kSol, ?kStart, ?kCap, ?kNormal, ?lSol, ?lStart,
      ?lCap, ?lNormal, ?sSol, ?sStart⟩
    case kSol =>
      refine odeSol_of_hasDerivAt
        (y' := fun t => (-(2 * Real.exp (-(2 * t)))) •
          (!![1 / 2, 0; -1 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ)) (fun t => ?_) (fun t => ?_)
      · have h1 : HasDerivAt (fun t : ℝ => -(2 * t)) (-2) t := by
          simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).fun_neg
        have := (h1.exp.smul_const (!![1 / 2, 0; -1 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ)).add_const
          (!![1 / 2, 0; 1 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        convert this using 2
        rw [mul_neg, mul_comm]
      · rw [rightProj_apply', coE1_mul_transpose]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [coE11, coD, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    case kStart =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coE11] <;> norm_num
    case kCap =>
      have hq : Real.exp (-(2 * (1 / 2 : ℝ))) = q := by norm_num [hqdef]
      have hK : (Real.exp (-(2 * (1 / 2 : ℝ))) •
            (!![1 / 2, 0; -1 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ)
          + (!![1 / 2, 0; 1 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ))
          = n • (!![u1, 0; u2, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [hq]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> linarith
      change leftProj _ (Real.exp (-(2 * (1 / 2 : ℝ))) • _ + _) = _
      rw [hK, map_smul, leftProj_apply, col_mul_transpose]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination u1 * hu
      · linear_combination u2 * hu
    case kNormal =>
      have key : ∀ Y : Matrix (Fin 2) (Fin 2) ℝ, Y 0 1 = 0 → Y 1 1 = 0 →
          (1 - rightProj coE1) (coD * Y) = 0 := by
        intro Y h01 h11
        rw [one_sub_rightProj_apply, coE1_mul_transpose, coD_mul]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [coE11, Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
      intro t _
      rw [key _ (by simp) (by simp), map_zero, norm_zero]
    case lSol =>
      refine odeSol_of_hasDerivAt (y' := fun t => (-Real.exp (-t)) • coE11) (fun t => ?_)
        (fun t => ?_)
      · simpa using (hasDerivAt_neg t).exp.smul_const coE11
      · rw [leftProj_apply, coE1_mul_transpose, coD_mul]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [coE11, Matrix.mul_apply, Fin.sum_univ_two]
    case lStart => simp
    case lCap =>
      rw [rightProj_apply', coE1_mul_transpose]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coE11, Matrix.mul_apply, Fin.sum_univ_two]
    case lNormal =>
      have key : ∀ Y : Matrix (Fin 2) (Fin 2) ℝ, Y 0 1 = 0 → Y 1 1 = 0 →
          (1 - rightProj coE1) ((1 - leftProj coE1) (coD * Y)) = 0 := by
        intro Y h01 h11
        rw [one_sub_rightProj_apply, one_sub_leftProj_apply, coE1_mul_transpose, coD_mul]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [coE11, Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
      intro t _
      rw [key _ (by simp [coE11]) (by simp [coE11]), norm_zero]
    case sSol =>
      refine odeSol_of_hasDerivAt (y' := fun t => (u1 * (Real.exp (-(c * t)) * (-c))) •
        (!![u1, 0; u2, 0] : Matrix (Fin 2) (Fin 2) ℝ)) (fun t => ?_) (fun t => ?_)
      · have h1 : HasDerivAt (fun t : ℝ => -(c * t)) (-c) t := by
          simpa using ((hasDerivAt_id t).const_mul c).fun_neg
        exact (h1.exp.const_mul u1).smul_const _
      · rw [leftProj_apply, col_mul_transpose, rightProj_apply', coE1_mul_transpose, coD_mul]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [coE11, hc, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    case sStart =>
      rw [leftProj_apply, col_mul_transpose, rightProj_apply', coE1_mul_transpose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coE11, Matrix.mul_apply, Fin.sum_univ_two]
      ring
  · have hn1 : n * (u1 + u2) = 1 := by linarith
    have hn2 : n * (u1 - u2) = q := by linarith
    have e1 : u1 * (u1 + u2) = ((1 + q) / 2) / ((1 + q ^ 2) / 2) := by
      rw [eq_div_iff (by positivity), ← hn]
      calc u1 * (u1 + u2) * n ^ 2 = (n * u1) * (n * (u1 + u2)) := by ring
        _ = _ := by rw [← ha, hn1]; ring
    have e2 : c = q ^ 2 / ((1 + q ^ 2) / 2) := by
      rw [eq_div_iff (by positivity), ← hn]
      calc c * n ^ 2 = (n * (u1 - u2)) ^ 2 := by rw [hc]; ring
        _ = _ := by rw [hn2]
    have hexp : 1 - c * (1 / 2) ≤ Real.exp (-(c * (1 / 2))) := by
      linarith [Real.add_one_le_exp (-(c * (1 / 2)))]
    have hpos : 0 < u1 * (u1 + u2) := by rw [e1]; positivity
    have hmass : ⟪coOnes, (u1 * Real.exp (-(c * (1 / 2)))) •
        (!![u1, 0; u2, 0] : Matrix (Fin 2) (Fin 2) ℝ)⟫
        = (u1 * (u1 + u2)) * Real.exp (-(c * (1 / 2))) := by
      rw [inner_smul_right, Frobenius.inner_def]
      simp [Fin.sum_univ_two, coOnes]
      ring
    have hlow := mass_gt_one q hq0 hq1
    have hc2 : 1 - c * (1 / 2) = 1 - q ^ 2 / (2 * ((1 + q ^ 2) / 2)) := by
      rw [e2]; field_simp
    intro hone
    change ⟪coOnes, (u1 * Real.exp (-(c * (1 / 2)))) •
        (!![u1, 0; u2, 0] : Matrix (Fin 2) (Fin 2) ℝ)⟫ = 1 at hone
    rw [hmass] at hone
    rw [← e1, ← hc2] at hlow
    nlinarith [mul_le_mul_of_nonneg_left hexp hpos.le]

end MassCounterexample

section VPEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **OP-CO-16** (arXiv 2101.12571 §6.1; 2206.09374, proof of Thm 3).  Abstract core on the field
space: if the low-rank scheme reproduces the kinetic-energy moment law `κ_{n+1} = κ_n + τ ⟪Eₙ, jₙ⟫`
exactly and the field is advanced by `E_{n+1} = Eₙ - τ Π_grad jₙ` (`Π_grad` the orthogonal projector
onto gradient fields, `Eₙ ∈ range Π_grad`), the total energy changes per step by exactly
`‖E_{n+1} - Eₙ‖²/2 ≤ τ² ‖jₙ‖²/2`; so exact conservation is impossible whenever `Π_grad jₙ ≠ 0`, and
the defect is `O(τ)` on `[0, T]`.
-/
theorem vp_energy_defect {Pg : E →L[ℝ] E} (hPg : IsOrthProj Pg) {τ J : ℝ} {N : ℕ}
    {κ : ℕ → ℝ} {Ef j : ℕ → E} (hE0 : Pg (Ef 0) = Ef 0)
    (hamp : ∀ n < N, Ef (n + 1) = Ef n - τ • Pg (j n))
    (hkin : ∀ n < N, κ (n + 1) = κ n + τ * ⟪Ef n, j n⟫) (hJ : ∀ n < N, ‖j n‖ ≤ J) :
    (∀ n < N, vpEnergy κ Ef (n + 1) - vpEnergy κ Ef n = ‖Ef (n + 1) - Ef n‖ ^ 2 / 2 ∧
      ‖Ef (n + 1) - Ef n‖ ≤ |τ| * ‖j n‖) ∧
      vpEnergy κ Ef N - vpEnergy κ Ef 0 ≤ N * τ ^ 2 * J ^ 2 / 2 := by
  have hfix : ∀ n ≤ N, Pg (Ef n) = Ef n := by
    intro n
    induction n with
    | zero => intro _; exact hE0
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      rw [hamp n (by omega), map_sub, map_smul, hPg.idem, h1]
  have hstep : ∀ n < N, ‖Ef (n + 1) - Ef n‖ = |τ| * ‖Pg (j n)‖ := by
    intro n hn
    rw [hamp n hn, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
  have hdiff : ∀ n < N, vpEnergy κ Ef (n + 1) - vpEnergy κ Ef n
      = ‖Ef (n + 1) - Ef n‖ ^ 2 / 2 := by
    intro n hn
    have hin : ⟪Ef n, Pg (j n)⟫ = ⟪Ef n, j n⟫ := by
      rw [← hPg.symm, hfix n hn.le]
    have hd : Ef (n + 1) - Ef n = -(τ • Pg (j n)) := by
      rw [hamp n hn]; abel
    have hsq : ‖Ef (n + 1)‖ ^ 2 = ‖Ef n‖ ^ 2 + 2 * (-(τ * ⟪Ef n, j n⟫))
        + ‖Ef (n + 1) - Ef n‖ ^ 2 := by
      have : Ef (n + 1) = Ef n + (Ef (n + 1) - Ef n) := by abel
      conv_lhs => rw [this, norm_add_sq_real]
      rw [hd, inner_neg_right, inner_smul_right, hin]
    unfold vpEnergy
    rw [hkin n hn, hsq]
    ring
  refine ⟨fun n hn => ⟨hdiff n hn, ?_⟩, ?_⟩
  · rw [hstep n hn]
    exact mul_le_mul_of_nonneg_left (hPg.norm_le _) (abs_nonneg _) |>.trans
      (mul_le_mul_of_nonneg_left le_rfl (abs_nonneg _))
  · have key : ∀ m ≤ N, vpEnergy κ Ef m - vpEnergy κ Ef 0 ≤ m * τ ^ 2 * J ^ 2 / 2 := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := hdiff m (by omega)
        have h3 : ‖Ef (m + 1) - Ef m‖ ≤ |τ| * J := by
          rw [hstep m (by omega)]
          exact mul_le_mul_of_nonneg_left
            ((hPg.norm_le _).trans (hJ m (by omega))) (abs_nonneg _)
        have h4 : ‖Ef (m + 1) - Ef m‖ ^ 2 ≤ (|τ| * J) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
        have h5 : (|τ| * J) ^ 2 = τ ^ 2 * J ^ 2 := by rw [mul_pow, sq_abs]
        push_cast
        nlinarith
    exact key N le_rfl

end VPEnergy

section PositivityFeasibility

open scoped LeanDLRA.Frobenius

variable {nx nv r : Type*} [Fintype nx] [Fintype nv] [Fintype r] [DecidableEq r]

omit [Fintype nv] [DecidableEq r] in
/-- **OP-CO-17 (a)** (arXiv 2606.31662, (3.3)).  The PP-KL correction problem
`min ‖δK‖ s.t. (K̃ + δK) Vᵀ ≥ 0` is always feasible (`δK = -K̃`), its feasible set is closed and
convex, and it has a unique minimiser. -/
theorem ppKL_feasible_unique (V : Matrix nv r ℝ) (Kt : Matrix nx r ℝ) :
    -Kt ∈ {dK : Matrix nx r ℝ | ∀ i j, 0 ≤ ((Kt + dK) * Vᵀ) i j} ∧
      Convex ℝ {dK : Matrix nx r ℝ | ∀ i j, 0 ≤ ((Kt + dK) * Vᵀ) i j} ∧
      IsClosed {dK : Matrix nx r ℝ | ∀ i j, 0 ≤ ((Kt + dK) * Vᵀ) i j} ∧
      ∃! dK : Matrix nx r ℝ, (∀ i j, 0 ≤ ((Kt + dK) * Vᵀ) i j) ∧
        ∀ dK' : Matrix nx r ℝ, (∀ i j, 0 ≤ ((Kt + dK') * Vᵀ) i j) → ‖dK‖ ≤ ‖dK'‖ := by
  set S : Set (Matrix nx r ℝ) := {dK : Matrix nx r ℝ | ∀ i j, 0 ≤ ((Kt + dK) * Vᵀ) i j} with hS
  have hent : ∀ (dK : Matrix nx r ℝ) i j,
      ((Kt + dK) * Vᵀ) i j = ∑ k, (Kt i k + dK i k) * V j k := by
    intro dK i j
    simp [Matrix.mul_apply]
  have hneg : -Kt ∈ S := by
    intro i j
    simp
  have hconv : Convex ℝ S := by
    intro a ha b hb s t hs ht hst i j
    have h1 := ha i j
    have h2 := hb i j
    rw [hent] at h1 h2 ⊢
    have h : ∑ k, (Kt i k + (s • a + t • b) i k) * V j k
        = s * ∑ k, (Kt i k + a i k) * V j k + t * ∑ k, (Kt i k + b i k) * V j k := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination (-(Kt i k * V j k)) * hst
    rw [h]
    positivity
  have hclosed : IsClosed S := by
    have : S = ⋂ i, ⋂ j, {dK : Matrix nx r ℝ | 0 ≤ ((Kt + dK) * Vᵀ) i j} := by
      ext dK; simp [hS]
    rw [this]
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const ?_
    simp only [hent]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ continuous_const
    exact continuous_const.add ((continuous_apply k).comp (continuous_apply i))
  obtain ⟨u, hu, hvi⟩ := exists_metricProj (E := Matrix nx r ℝ) ⟨-Kt, hneg⟩
    hclosed.isComplete hconv 0
  have hmin : ∀ w ∈ S, ‖u‖ ≤ ‖w‖ := fun w hw => by
    simpa using (norm_sub_le_of_metricProj hvi hw).2
  refine ⟨hneg, hconv, hclosed, u, ⟨hu, hmin⟩, ?_⟩
  rintro v ⟨hv, hvmin⟩
  have h := norm_sub_sq_add_le_of_metricProj hvi hv
  have h2 : ‖v‖ ≤ ‖u‖ := hvmin u hu
  have h3 : ‖u‖ ≤ ‖v‖ := hmin v hv
  have h4 : ‖u - v‖ ^ 2 ≤ 0 := by
    simp only [zero_sub, norm_neg] at h
    rw [le_antisymm h3 h2] at h
    linarith
  have h5 : ‖u - v‖ = 0 := by
    have := sq_nonneg ‖u - v‖
    have h6 : ‖u - v‖ ^ 2 = 0 := le_antisymm h4 this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h6
  exact (sub_eq_zero.1 (norm_eq_zero.1 h5)).symm

omit [DecidableEq r] in
/-- **OP-CO-17 (b), Gordan criterion** (arXiv 2606.31662).  With the strict constraint
`F ≥ ε 1`, the K-problem is feasible iff `range V` meets the open positive orthant, which by
Gordan's alternative holds iff no nonzero `λ ≥ 0` has `Vᵀ λ = 0`; it is guaranteed if
`1 ∈ range V` (e.g. a positive Maxwellian-like basis vector). -/
theorem gordan_positive_range (V : Matrix nv r ℝ) :
    (∃ w, ∀ i, 0 < (V *ᵥ w) i) ↔
      ¬ ∃ lam : nv → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧ Vᵀ *ᵥ lam = 0 := by
  constructor
  · rintro ⟨w, hw⟩ ⟨lam, hl0, hlne, hlV⟩
    have h1 : lam ⬝ᵥ (V *ᵥ w) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hlV]; simp
    have hnn : ∀ i, 0 ≤ lam i * (V *ᵥ w) i := fun i => mul_nonneg (hl0 i) (hw i).le
    have hall : ∀ i, lam i * (V *ᵥ w) i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h1
      exact fun i => this i (Finset.mem_univ i)
    apply hlne
    funext i
    have := hall i
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (hw i).ne'
  · intro hno
    classical
    by_contra hnw
    simp only [not_exists, not_forall, not_lt] at hnw
    let O : Set (nv → ℝ) := {x | ∀ i, 0 < x i}
    let Tm : Submodule ℝ (nv → ℝ) := LinearMap.range (Matrix.mulVecLin V)
    let T : Set (nv → ℝ) := (Tm : Set (nv → ℝ))
    have hOc : Convex ℝ O := by
      intro x hx y hy a b ha hb hab i
      have hxi := hx i
      have hyi := hy i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases ha.eq_or_lt with rfl | ha'
      · have : 0 < b := by linarith
        simp only [zero_mul, zero_add]; positivity
      · have := mul_pos ha' hxi
        have := mul_nonneg hb hyi.le
        linarith
    have hOo : IsOpen O := by
      have : O = ⋂ i, {x : nv → ℝ | 0 < x i} := by ext x; simp [O]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have hTc : Convex ℝ T := Tm.convex
    have hdisj : Disjoint O T := by
      rw [Set.disjoint_left]
      rintro x hx ⟨w, rfl⟩
      obtain ⟨i, hi⟩ := hnw w
      exact absurd (hx i) (by simpa using not_lt.2 hi)
    obtain ⟨f, u, hfO, hfT⟩ := geometric_hahn_banach_open hOc hOo hTc hdisj
    have hu0 : u ≤ 0 := by
      have := hfT 0 ⟨0, by simp⟩
      simpa using this
    have hfT0 : ∀ b ∈ T, f b = 0 := by
      intro b hb
      by_contra hne
      have hcb : ((u - 1) / f b) • b ∈ T := Tm.smul_mem _ hb
      have := hfT _ hcb
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    have hdec : ∀ x : nv → ℝ, f x = ∑ i, x i * f (Pi.single i 1) := by
      intro x
      have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : nv → ℝ) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hx]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have hone : f (fun _ => 1) < 0 := by
      have := hfO (fun _ => 1) (fun _ => one_pos)
      linarith
    refine hno ⟨fun i => -f (Pi.single i 1), ?_, ?_, ?_⟩
    · intro i
      by_contra hneg
      have hc : 0 < f (Pi.single i 1) := by linarith [not_le.1 hneg]
      set c := f (Pi.single i 1) with hcdef
      set m := |f (fun _ => 1)| with hm
      have hm0 : 0 ≤ m := abs_nonneg _
      set ε := c / (1 + m) with hε
      have hε0 : 0 < ε := by positivity
      have hεm : ε * (1 + m) = c := by rw [hε]; field_simp
      have hmem : (ε • (fun _ => (1 : ℝ)) + Pi.single i 1 : nv → ℝ) ∈ O := by
        intro j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
        have : 0 ≤ (Pi.single i (1 : ℝ) : nv → ℝ) j := by
          rw [Pi.single_apply]; split_ifs <;> norm_num
        linarith
      have h1 := hfO _ hmem
      rw [map_add, map_smul, smul_eq_mul] at h1
      have h2 : -(ε * m) ≤ ε * f (fun _ => 1) := by
        have := neg_abs_le (f (fun _ => 1))
        nlinarith
      nlinarith
    · intro hz
      have h0 : ∀ i, f (Pi.single i 1) = 0 := fun i => by
        have := congrFun hz i
        simpa using this
      rw [hdec] at hone
      simp [h0] at hone
    · funext k
      have hmem : (fun i => V i k) ∈ T := ⟨Pi.single k 1, by ext i; simp⟩
      have h0 := hfT0 _ hmem
      rw [hdec] at h0
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
      have : ∑ i, V i k * -f (Pi.single i 1) = -∑ i, V i k * f (Pi.single i 1) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, h0, neg_zero]


end PositivityFeasibility

section Nonnegativity

open scoped LeanDLRA.Frobenius

end Nonnegativity

section AugmentedTypes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end AugmentedTypes

section Involutions

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

end Involutions

end LeanDLRA.OpenProblems.Conservation
