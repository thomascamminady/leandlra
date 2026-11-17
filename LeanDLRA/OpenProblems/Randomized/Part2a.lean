import LeanDLRA.OpenProblems.Randomized.Part2Defs
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Stability.Energy
import LeanDLRA.Classical.EckartYoung
import Mathlib.Probability.Moments.Variance

/-!
# Open problems OP-RS-10, OP-RS-11, OP-RS-12, OP-RS-13
-/

open Set MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius ENNReal

universe u

namespace LeanDLRA.OpenProblems.Randomized

open LeanDLRA.Curvature

/-- **OP-RS-10 (a)** (randomized truncation in the stable rank-adaptive step-and-truncate
finite-volume scheme): the randomized truncation `M ↦ Q T_r(Qᵀ M)` (orthonormal range basis `Q`,
truncated SVD `T_r`) is an orthogonal projection of `M`, hence Pythagorean:
`‖Q T_r(QᵀM)‖² + ‖M - Q T_r(QᵀM)‖² = ‖M‖²`.  Meaning: randomized truncations are nonexpansive,
which is exactly the hypothesis of the stability theorems. -/
theorem randomizedTruncation_pythagoras {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
    [DecidableEq n] [DecidableEq l] {Q : Matrix m l ℝ} (hQ : Qᵀ * Q = 1)
    (M : Matrix m n ℝ) (r : ℕ) :
    ‖Q * EckartYoung.truncation (Qᵀ * M) r‖ ^ 2 +
      ‖M - Q * EckartYoung.truncation (Qᵀ * M) r‖ ^ 2 = ‖M‖ ^ 2 := by
  set X : Matrix l n ℝ := Qᵀ * M with hX
  set V := EckartYoung.topRightSingularVectors X r with hVdef
  have hV : Vᵀ * V = 1 := EckartYoung.transpose_mul_topRightSingularVectors X r
  have hT : EckartYoung.truncation X r = (X * V) * Vᵀ := rfl
  have h1 : ‖Q * EckartYoung.truncation X r‖ = ‖X * V‖ := by
    rw [LeanDLRA.Frobenius.norm_mul_of_orthonormal hQ, hT,
      LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hV]
  have h2 : ⟪Q * EckartYoung.truncation X r, M⟫ = ‖X * V‖ ^ 2 := by
    rw [LeanDLRA.Frobenius.inner_mul_left, ← hX, hT, LeanDLRA.Frobenius.inner_mul_right,
      Matrix.transpose_transpose, ← real_inner_self_eq_norm_sq]
  have h3 : ‖M - Q * EckartYoung.truncation X r‖ ^ 2 =
      ‖M‖ ^ 2 - 2 * ⟪Q * EckartYoung.truncation X r, M⟫ +
        ‖Q * EckartYoung.truncation X r‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  rw [h3, h2, h1]
  ring

/-- **OP-RS-10 (b)** (stability of step-and-truncate with randomized truncation; the analogue of
Thm 4.2 of the stable rank-adaptive scheme): if the full explicit step is `γ`-stable,
`‖X + h F X‖ ≤ γ ‖X‖`, then the iterates `u_{j+1} = Q_j T_{r_j}(Q_jᵀ (u_j + h F u_j))` with
arbitrary (random, data-dependent) orthonormal range bases `Q_j` and ranks `r_j` satisfy
`‖u_j‖ ≤ γ^j ‖u₀‖`.  Meaning: stability is deterministic and survives randomization; only the
error bound (Thm 4.3) needs probabilistic truncation tolerances (HMT bounds, out of scope). -/
theorem randomizedStepTruncate_norm_le {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
    [DecidableEq n] [DecidableEq l] {F : Matrix m n ℝ → Matrix m n ℝ}
    {h γ : ℝ} (hγ : 0 ≤ γ) (hF : ∀ X, ‖eulerStep F h X‖ ≤ γ * ‖X‖)
    {Q : ℕ → Matrix m l ℝ} (hQ : ∀ j, (Q j)ᵀ * Q j = 1) {r : ℕ → ℕ} {u : ℕ → Matrix m n ℝ}
    (hu : ∀ j, u (j + 1) = Q j * EckartYoung.truncation ((Q j)ᵀ * eulerStep F h (u j)) (r j)) :
    ∀ j, ‖u j‖ ≤ γ ^ j * ‖u 0‖ := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hp := randomizedTruncation_pythagoras (hQ j) (eulerStep F h (u j)) (r j)
    have hle : ‖u (j + 1)‖ ≤ ‖eulerStep F h (u j)‖ := by
      rw [hu j]
      have h0 : ‖Q j * EckartYoung.truncation ((Q j)ᵀ * eulerStep F h (u j)) (r j)‖ ^ 2 ≤
          ‖eulerStep F h (u j)‖ ^ 2 := by
        have := sq_nonneg ‖eulerStep F h (u j) -
          Q j * EckartYoung.truncation ((Q j)ᵀ * eulerStep F h (u j)) (r j)‖
        linarith
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h0
    calc ‖u (j + 1)‖ ≤ γ * ‖u j‖ := hle.trans (hF _)
      _ ≤ γ * (γ ^ j * ‖u 0‖) := mul_le_mul_of_nonneg_left ih hγ
      _ = γ ^ (j + 1) * ‖u 0‖ := by ring

private theorem specNorm_inv_perturb {k : Type*} [Fintype k] [DecidableEq k]
    {A B : Matrix k k ℝ} (hA : IsUnit A.det) (hsmall : specNorm A⁻¹ * specNorm (B - A) < 1) :
    IsUnit B.det ∧
      specNorm B⁻¹ ≤ specNorm A⁻¹ / (1 - specNorm A⁻¹ * specNorm (B - A)) := by
  set a := specNorm A⁻¹ with ha
  set t := specNorm (B - A) with ht
  have ha0 : 0 ≤ a := specNorm_nonneg _
  have hpos : 0 < 1 - a * t := by linarith
  have hmul : ∀ (M N : Matrix k k ℝ) (x : EuclideanSpace ℝ k),
      Matrix.toEuclideanLin M (Matrix.toEuclideanLin N x) = Matrix.toEuclideanLin (M * N) x := by
    intro M N x
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  have hx : ∀ x : EuclideanSpace ℝ k, ‖x‖ ≤ a * ‖Matrix.toEuclideanLin A x‖ := by
    intro x
    have h1 := norm_toEuclideanLin_le A⁻¹ (Matrix.toEuclideanLin A x)
    rw [hmul, Matrix.nonsing_inv_mul _ hA] at h1
    simpa using h1
  have key : ∀ x : EuclideanSpace ℝ k,
      (1 - a * t) * ‖x‖ ≤ a * ‖Matrix.toEuclideanLin B x‖ := by
    intro x
    have h1 : Matrix.toEuclideanLin B x =
        Matrix.toEuclideanLin A x + Matrix.toEuclideanLin (B - A) x := by
      rw [map_sub, LinearMap.sub_apply]; abel
    have h2 : ‖Matrix.toEuclideanLin A x‖ ≤
        ‖Matrix.toEuclideanLin B x‖ + t * ‖x‖ := by
      have h3 : Matrix.toEuclideanLin A x =
          Matrix.toEuclideanLin B x - Matrix.toEuclideanLin (B - A) x := by
        rw [h1]; abel
      calc ‖Matrix.toEuclideanLin A x‖
          ≤ ‖Matrix.toEuclideanLin B x‖ + ‖Matrix.toEuclideanLin (B - A) x‖ := by
            rw [h3]; exact norm_sub_le _ _
        _ ≤ _ := add_le_add le_rfl (norm_toEuclideanLin_le _ _)
    have h4 := hx x
    have h5 : t * ‖x‖ ≤ t * (a * ‖Matrix.toEuclideanLin A x‖) :=
      mul_le_mul_of_nonneg_left h4 (specNorm_nonneg _)
    have h6 : a * ‖Matrix.toEuclideanLin A x‖ ≤
        a * ‖Matrix.toEuclideanLin B x‖ + a * (t * ‖x‖) := by
      have := mul_le_mul_of_nonneg_left h2 ha0
      linarith
    nlinarith
  have hdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 := key (WithLp.toLp 2 v)
    have h2 : Matrix.toEuclideanLin B (WithLp.toLp 2 v) = 0 := by
      rw [Matrix.toLpLin_toLp]
      change WithLp.toLp 2 (B *ᵥ v) = 0
      rw [hBv]; rfl
    rw [h2, norm_zero, mul_zero] at h1
    have h3 : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ k)‖ ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    have h4 : (WithLp.toLp 2 v : EuclideanSpace ℝ k) = 0 := norm_le_zero_iff.mp h3
    exact hv (by simpa using congrArg WithLp.ofLp h4)
  refine ⟨hdet, ?_⟩
  have hC : 0 ≤ a / (1 - a * t) := div_nonneg ha0 hpos.le
  refine specNorm_le_of hC fun y => ?_
  have h1 := key (Matrix.toEuclideanLin B⁻¹ y)
  rw [hmul, Matrix.mul_nonsing_inv _ hdet] at h1
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

/-- **OP-RS-11 (a)** (index freezing; perturbation of the DEIM constant): if the indices `S`
(`‖S‖₂ ≤ 1`) were selected for `U₀` and the basis moves to `U₁` with
`‖(SᵀU₀)⁻¹‖₂ ‖U₁ - U₀‖₂ < 1`, then `SᵀU₁` is invertible and
`‖(SᵀU₁)⁻¹‖₂ ≤ ‖(SᵀU₀)⁻¹‖₂ / (1 - ‖(SᵀU₀)⁻¹‖₂ ‖U₁ - U₀‖₂)`.  Meaning: a certified criterion for
keeping interpolation indices while the basis moves. -/
theorem specNorm_inv_transpose_mul_le_of_perturb {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k] {S U₀ U₁ : Matrix m k ℝ} (hS : specNorm S ≤ 1)
    (hU₀ : IsUnit (Sᵀ * U₀).det) (hsmall : specNorm (Sᵀ * U₀)⁻¹ * specNorm (U₁ - U₀) < 1) :
    IsUnit (Sᵀ * U₁).det ∧
      specNorm (Sᵀ * U₁)⁻¹ ≤
        specNorm (Sᵀ * U₀)⁻¹ / (1 - specNorm (Sᵀ * U₀)⁻¹ * specNorm (U₁ - U₀)) := by
  classical
  set a := specNorm (Sᵀ * U₀)⁻¹ with ha
  set δ := specNorm (U₁ - U₀) with hδ
  have ha0 : 0 ≤ a := specNorm_nonneg _
  have hD : specNorm (Sᵀ * U₁ - Sᵀ * U₀) ≤ δ := by
    rw [← Matrix.mul_sub]
    calc specNorm (Sᵀ * (U₁ - U₀)) ≤ specNorm Sᵀ * specNorm (U₁ - U₀) := specNorm_mul_le _ _
      _ ≤ 1 * δ := by
          rw [specNorm_transpose]
          exact mul_le_mul_of_nonneg_right hS (specNorm_nonneg _)
      _ = δ := one_mul _
  have hsm : a * specNorm (Sᵀ * U₁ - Sᵀ * U₀) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hD ha0) hsmall
  obtain ⟨hdet, hb⟩ := specNorm_inv_perturb hU₀ hsm
  refine ⟨hdet, hb.trans ?_⟩
  have hpos : 0 < 1 - a * specNorm (Sᵀ * U₁ - Sᵀ * U₀) := by linarith
  have hpos' : 0 < 1 - a * δ := by linarith
  exact div_le_div_of_nonneg_left ha0 hpos' (by nlinarith)

private theorem specNorm_sub_le_add {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (A B C : Matrix m k ℝ) : specNorm (A - C) ≤ specNorm (A - B) + specNorm (B - C) := by
  refine specNorm_le_of (add_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) fun x => ?_
  have h : Matrix.toEuclideanLin (A - C) x =
      Matrix.toEuclideanLin (A - B) x + Matrix.toEuclideanLin (B - C) x := by
    rw [← LinearMap.add_apply, ← map_add, sub_add_sub_cancel]
  rw [h, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_toEuclideanLin_le _ _)
    (norm_toEuclideanLin_le _ _))

private theorem specNorm_sub_zero_le {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U : ℕ → Matrix m k ℝ} {μ : ℝ} (hμ : ∀ j, specNorm (U (j + 1) - U j) ≤ μ) (j : ℕ) :
    specNorm (U j - U 0) ≤ j * μ := by
  induction j with
  | zero => simp [specNorm_le_of]
  | succ j ih =>
    calc specNorm (U (j + 1) - U 0) ≤ specNorm (U (j + 1) - U j) + specNorm (U j - U 0) :=
          specNorm_sub_le_add _ _ _
      _ ≤ μ + j * μ := add_le_add (hμ j) ih
      _ = ((j + 1 : ℕ) : ℝ) * μ := by push_cast; ring

/-- **OP-RS-11 (b)** (uniform Lebesgue constants along frozen indices): if the (aligned) bases
move by at most `μ` per step in the spectral norm and the indices selected at step `0` give
`‖(SᵀU₀)⁻¹‖₂ ≤ c₀`, they can be kept for `J` steps with `J μ c₀ < 1`, and
`‖(SᵀU_j)⁻¹‖₂ ≤ c₀ / (1 - j μ c₀)` for `j ≤ J`.  Meaning: the uniform-`C` hypothesis of the oblique
error theorems holds over a certified number of steps without re-selection. -/
theorem lebesgue_bound_frozen_indices {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k] {S : Matrix m k ℝ} {U : ℕ → Matrix m k ℝ} {μ c₀ : ℝ} {J : ℕ}
    (hS : specNorm S ≤ 1) (hU0 : IsUnit (Sᵀ * U 0).det) (hc₀ : specNorm (Sᵀ * U 0)⁻¹ ≤ c₀)
    (hμ : ∀ j, specNorm (U (j + 1) - U j) ≤ μ) (hJ : (J : ℝ) * μ * c₀ < 1) :
    ∀ j ≤ J, IsUnit (Sᵀ * U j).det ∧ specNorm (Sᵀ * U j)⁻¹ ≤ c₀ / (1 - j * μ * c₀) := by
  intro j hj
  have hμ0 : 0 ≤ μ := (specNorm_nonneg _).trans (hμ 0)
  have hc0 : 0 ≤ c₀ := (specNorm_nonneg _).trans hc₀
  have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
  have hjμ : (j : ℝ) * μ * c₀ ≤ J * μ * c₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjJ hμ0) hc0
  have hδ := specNorm_sub_zero_le hμ j
  have ha0 : 0 ≤ specNorm (Sᵀ * U 0)⁻¹ := specNorm_nonneg _
  have hprod : specNorm (Sᵀ * U 0)⁻¹ * specNorm (U j - U 0) ≤ j * μ * c₀ :=
    calc specNorm (Sᵀ * U 0)⁻¹ * specNorm (U j - U 0) ≤ c₀ * (j * μ) :=
          mul_le_mul hc₀ hδ (specNorm_nonneg _) hc0
      _ = j * μ * c₀ := by ring
  obtain ⟨hu, hb⟩ := specNorm_inv_transpose_mul_le_of_perturb hS hU0 (hprod.trans_lt (by linarith))
  refine ⟨hu, hb.trans ?_⟩
  have hpos : 0 < 1 - j * μ * c₀ := by linarith
  have hpos' : 0 < 1 - specNorm (Sᵀ * U 0)⁻¹ * specNorm (U j - U 0) := by linarith
  calc specNorm (Sᵀ * U 0)⁻¹ / (1 - specNorm (Sᵀ * U 0)⁻¹ * specNorm (U j - U 0))
      ≤ specNorm (Sᵀ * U 0)⁻¹ / (1 - j * μ * c₀) :=
        div_le_div_of_nonneg_left ha0 hpos (by linarith)
    _ ≤ c₀ / (1 - j * μ * c₀) := div_le_div_of_nonneg_right hc₀ hpos.le

private theorem prod_filter_lt_succ {d : ℕ} (f : Fin (d + 1) → ℝ) (i : Fin d) :
    ∏ j ∈ Finset.univ.filter (· < i.succ), f j =
      f 0 * ∏ j ∈ Finset.univ.filter (· < i), f j.succ := by
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
  simp [Fin.succ_lt_succ_iff]

private theorem norm_sub_modeProd_le_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {d : ℕ} (P : Fin d → E →L[ℝ] E) (x : E) :
    ‖x - modeProd P x‖ ≤
      ∑ i, (∏ j ∈ Finset.univ.filter (· < i), ‖P j‖) * ‖x - P i x‖ := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hih := ih (fun i => P i.succ)
    have hdec : x - modeProd P x = (x - P 0 x) + P 0 (x - modeProd (fun i => P i.succ) x) := by
      rw [modeProd_succ]
      simp only [mul_apply_eq_comp, map_sub]
      abel
    rw [Fin.sum_univ_succ]
    simp only [prod_filter_lt_succ, Fin.not_lt_zero, Finset.filter_false, Finset.prod_empty,
      one_mul, mul_assoc, ← Finset.mul_sum]
    calc ‖x - modeProd P x‖ ≤ ‖x - P 0 x‖ + ‖P 0 (x - modeProd (fun i => P i.succ) x)‖ := by
          rw [hdec]; exact norm_add_le _ _
      _ ≤ ‖x - P 0 x‖ + ‖P 0‖ * ‖x - modeProd (fun i => P i.succ) x‖ :=
          add_le_add le_rfl ((P 0).le_opNorm _)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hih (norm_nonneg _))

/-- **OP-RS-12** (DEIM-FS Tucker approximation vs HOSVD): for mode-wise oblique projectors `Π_i`
onto orthogonal projectors `Q_i ≠ 0` (`Q_i = U_i U_iᵀ` acting on mode `i`), the DEIM-Tucker
approximation `Π₀ ⋯ Π_{d-1} x` satisfies
`‖x - Π₀⋯Π_{d-1} x‖ ≤ ∑_i (∏_{j<i} ‖Π_j‖) ‖Π_i‖ ‖x - Q_i x‖`, the HOSVD-type bound with
Lebesgue constants.  Meaning: DEIM-Tucker is quasi-optimal mode by mode.  The second half of the
entry (fiber-sampled factor errors vs HOSVD) is a cross-approximation question and research-level;
not stated. -/
theorem norm_sub_modeProd_oblique_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} {Pa Q : Fin d → E →L[ℝ] E} (hPa : ∀ i, IsObliqueProj (Pa i) (Q i))
    (hQ : ∀ i, Q i ≠ 0) (x : E) :
    ‖x - modeProd Pa x‖ ≤
      ∑ i, (∏ j ∈ Finset.univ.filter (· < i), ‖Pa j‖) * ‖Pa i‖ * ‖x - Q i x‖ := by
  refine (norm_sub_modeProd_le_sum Pa x).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hPa i).norm_sub_le_opNorm (hQ i) x)
    (Finset.prod_nonneg fun j _ => norm_nonneg _)

/-- **OP-RS-13** (randomized low-rank Runge–Kutta for an arbitrary random approximation operator,
arXiv 2410.17091 and successors; pathwise skeleton + `L^q` norms): let the exact one-step flow `Φ`
be `e^{Lh}`-Lipschitz, the deterministic increment `Ψ` (e.g. an RK step) be consistent,
`‖Ψ x - Φ x‖ ≤ h τ`, and the random approximation errors `e_n = R_n(Ψ Y_n) - Ψ Y_n` have
`‖e_n‖_{L^q} ≤ h ρ` (what an `L^q` quasi-best moment bound of the operator `R_n` supplies).
Then `‖Y_n - A(t_n)‖_{L^q} ≤ e^{L n h} (δ + n h (τ + ρ))`.  Meaning: any random approximation
operator with an `L^q` moment bound (SRFT, Khatri–Rao, rank-adaptive, …) plugs into the
convergence theory. -/
theorem randomized_lq_global_error {E : Type*} [NormedAddCommGroup E] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Φ Ψ : E → E} {a : ℕ → E}
    {L h τ ρ δ : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hL : 0 ≤ L) (hh : 0 ≤ h) (hτ : 0 ≤ τ)
    (hρ : 0 ≤ ρ) (hΦ : ∀ x y, ‖Φ x - Φ y‖ ≤ Real.exp (L * h) * ‖x - y‖)
    (ha : ∀ n, a (n + 1) = Φ (a n)) (hΨ : ∀ x, ‖Ψ x - Φ x‖ ≤ h * τ) {Y e : ℕ → Ω → E}
    (hYm : ∀ n, AEStronglyMeasurable (Y n) μ) (hem : ∀ n, AEStronglyMeasurable (e n) μ)
    (hY : ∀ n ω, Y (n + 1) ω = Ψ (Y n ω) + e n ω)
    (he : ∀ n, eLpNorm (e n) q μ ≤ ENNReal.ofReal (h * ρ)) (hY₀ : ∀ ω, ‖Y 0 ω - a 0‖ ≤ δ) :
    ∀ n, eLpNorm (fun ω => Y n ω - a n) q μ ≤
      ENNReal.ofReal (Real.exp (L * (n * h)) * (δ + n * h * (τ + ρ))) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hK0 : 0 ≤ Real.exp (L * h) := (Real.exp_pos _).le
  have hdm : ∀ n, AEStronglyMeasurable (fun ω => Y n ω - a n) μ :=
    fun n => (hYm n).sub aestronglyMeasurable_const
  have hconst : ∀ c : ℝ, 0 ≤ c → eLpNorm (fun _ : Ω => c) q μ = ENNReal.ofReal c := by
    intro c hc
    rw [eLpNorm_const c hq0 (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow,
      mul_one, Real.eNorm_eq_ofReal hc]
  have step : ∀ n, eLpNorm (fun ω => Y (n + 1) ω - a (n + 1)) q μ ≤
      ENNReal.ofReal (h * τ) + ENNReal.ofReal (Real.exp (L * h)) *
        eLpNorm (fun ω => Y n ω - a n) q μ + ENNReal.ofReal (h * ρ) := by
    intro n
    set w : Ω → E := fun ω => (Y (n + 1) ω - a (n + 1)) - e n ω with hw
    have hwm : AEStronglyMeasurable w μ := (hdm (n + 1)).sub (hem n)
    have hsplit : (fun ω => Y (n + 1) ω - a (n + 1)) = w + e n := by
      funext ω; simp [hw]
    have hpt : ∀ ω, ‖w ω‖ ≤ ‖h * τ + Real.exp (L * h) * ‖Y n ω - a n‖‖ := by
      intro ω
      have h1 : w ω = (Ψ (Y n ω) - Φ (Y n ω)) + (Φ (Y n ω) - Φ (a n)) := by
        simp only [hw, hY n ω, ha n]; abel
      have h2 : ‖w ω‖ ≤ h * τ + Real.exp (L * h) * ‖Y n ω - a n‖ := by
        rw [h1]
        exact (norm_add_le _ _).trans (add_le_add (hΨ _) (hΦ _ _))
      exact h2.trans (le_abs_self _ |>.trans (Real.norm_eq_abs _).ge)
    have h3 : eLpNorm w q μ ≤ eLpNorm (fun ω => h * τ + Real.exp (L * h) * ‖Y n ω - a n‖) q μ :=
      eLpNorm_mono_ae hwm (Filter.Eventually.of_forall hpt)
    have h4 := eLpNorm_add_le (μ := μ)
      (f := fun _ : Ω => h * τ) (g := fun ω => Real.exp (L * h) * ‖Y n ω - a n‖) hq
    have h5 : eLpNorm (fun ω => Real.exp (L * h) * ‖Y n ω - a n‖) q μ =
        ENNReal.ofReal (Real.exp (L * h)) * eLpNorm (fun ω => Y n ω - a n) q μ := by
      have := eLpNorm_const_smul (μ := μ) (p := q) (Real.exp (L * h))
        (fun ω => ‖Y n ω - a n‖)
      rw [eLpNorm_norm, Real.eNorm_eq_ofReal hK0] at this
      · exact this
      · exact hdm n
    have h6 := eLpNorm_add_le (μ := μ) (f := w) (g := e n) hq
    rw [hsplit]
    calc eLpNorm (w + e n) q μ ≤ eLpNorm w q μ + eLpNorm (e n) q μ := h6
      _ ≤ (ENNReal.ofReal (h * τ) + ENNReal.ofReal (Real.exp (L * h)) *
            eLpNorm (fun ω => Y n ω - a n) q μ) + ENNReal.ofReal (h * ρ) := by
          refine add_le_add (h3.trans ?_) ((he n))
          have h4' : eLpNorm (fun ω => h * τ + Real.exp (L * h) * ‖Y n ω - a n‖) q μ ≤
              eLpNorm (fun _ : Ω => h * τ) q μ +
                eLpNorm (fun ω => Real.exp (L * h) * ‖Y n ω - a n‖) q μ := h4
          rw [hconst _ (mul_nonneg hh hτ), h5] at h4'
          exact h4'
      _ = _ := by rw [add_assoc]
  intro n
  induction n with
  | zero =>
    have hδ : 0 ≤ δ := by
      obtain ⟨ω⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
      exact (norm_nonneg _).trans (hY₀ ω)
    have : eLpNorm (fun ω => Y 0 ω - a 0) q μ ≤ eLpNorm (fun _ : Ω => δ) q μ :=
      eLpNorm_mono_ae (hdm 0) (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs, abs_of_nonneg hδ] using hY₀ ω)
    rw [hconst δ hδ] at this
    simpa using this
  | succ n ih =>
    refine (step n).trans ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hE : 1 ≤ Real.exp (L * ((n + 1 : ℕ) * h)) := Real.one_le_exp (by positivity)
    have hs : 0 ≤ τ + ρ := add_nonneg hτ hρ
    have hδ : 0 ≤ δ := by
      obtain ⟨ω⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
      exact (norm_nonneg _).trans (hY₀ ω)
    calc ENNReal.ofReal (h * τ) + ENNReal.ofReal (Real.exp (L * h)) *
          eLpNorm (fun ω => Y n ω - a n) q μ + ENNReal.ofReal (h * ρ)
        ≤ ENNReal.ofReal (h * τ) + ENNReal.ofReal (Real.exp (L * h)) *
          ENNReal.ofReal (Real.exp (L * (n * h)) * (δ + n * h * (τ + ρ))) +
            ENNReal.ofReal (h * ρ) := by gcongr
      _ = ENNReal.ofReal (h * τ + Real.exp (L * h) *
            (Real.exp (L * (n * h)) * (δ + n * h * (τ + ρ))) + h * ρ) := by
          rw [← ENNReal.ofReal_mul hK0,
            ← ENNReal.ofReal_add (mul_nonneg hh hτ) (mul_nonneg hK0 (by positivity)),
            ← ENNReal.ofReal_add (by positivity) (mul_nonneg hh hρ)]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hexp : Real.exp (L * h) * Real.exp (L * (n * h)) =
              Real.exp (L * ((n + 1 : ℕ) * h)) := by
            rw [← Real.exp_add]; congr 1; push_cast; ring
          have hnn : 0 ≤ h * (τ + ρ) := mul_nonneg hh hs
          push_cast at hE hexp ⊢
          rw [← mul_assoc, hexp]
          have key := mul_nonneg hnn (sub_nonneg.2 hE)
          linarith


section Empirical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Empirical

section Sketch

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']

end Sketch

end LeanDLRA.OpenProblems.Randomized
