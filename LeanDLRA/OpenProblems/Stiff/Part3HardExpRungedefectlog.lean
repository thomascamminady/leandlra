import LeanDLRA.OpenProblems.Stiff.Part3Defs
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Frobenius

/-!
# `expRunge_defect_log`
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Stiff

open LeanDLRA

section DRB

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end DRB

section Newton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Newton

section Rank

open scoped LeanDLRA.Frobenius

end Rank

section EnKF

open scoped LeanDLRA.Frobenius

end EnKF

/-- An eigenvector of `T` is an eigenvector of every power of `T`. -/
private theorem pow_apply_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →L[ℝ] E} {v : E} {μ : ℝ} (hv : T v = μ • v) (n : ℕ) :
    (T ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hv, smul_smul, pow_succ]

/-- The operator exponential acts on an eigenvector through the scalar exponential. -/
private theorem exp_apply_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} {v : E} {μ : ℝ} (hv : A v = μ • v) :
    NormedSpace.exp A v = Real.exp μ • v := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mapL
    (ContinuousLinearMap.apply ℝ E v)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) μ).smul_const v
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.unique (h2.congr_fun fun n => ?_)
  simp [pow_apply_of_eigen hv, smul_smul]

/-- A map that is diagonal in an orthonormal basis, with entries bounded by `C`, has norm at
most `C`. -/
private theorem norm_apply_le_of_diag {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {T : E →L[ℝ] E} {c : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, T (b i) = c i • b i)
    (hc : ∀ i, |c i| ≤ C) (x : E) : ‖T x‖ ≤ C * ‖x‖ := by
  have hcoord : ∀ i, ⟪b i, T x⟫ = c i * ⟪b i, x⟫ := by
    intro i
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, hT, inner_sum, inner_smul_right]
    rw [Finset.sum_eq_single i]
    · simp [b.orthonormal.1 i, mul_comm]
    · intro j _ hj
      simp [b.orthonormal.2 hj.symm]
    · simp
  have hsq : ‖T x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_inner_right (T x), ← b.sum_sq_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hcoord, mul_pow, mul_comm (C ^ 2)]
    have : c i ^ 2 ≤ C ^ 2 := sq_le_sq' (by linarith [neg_abs_le (c i), hc i])
      ((le_abs_self _).trans (hc i))
    nlinarith [sq_nonneg ⟪b i, x⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).1 hsq

/-- The scalar smoothing bound behind `‖hL e^{jhL}‖ ≤ 1/(e j)`, in the form the sum needs. -/
private theorem abs_mul_exp_pow_le {μ : ℝ} (hμ : μ ≤ 0) {k : ℕ} (hk : 0 < k) :
    |μ * Real.exp μ ^ k| ≤ 1 / ((k : ℝ) + 1) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set y : ℝ := k * -μ with hy
  have hy0 : 0 ≤ y := mul_nonneg (by linarith) (by linarith)
  have h2y : 2 * y ≤ Real.exp y := by
    have h1 : y ≤ Real.exp (y - 1) := by linarith [Real.add_one_le_exp (y - 1)]
    have h2 : Real.exp y = Real.exp 1 * Real.exp (y - 1) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    nlinarith [Real.exp_pos (y - 1)]
  have hpow : Real.exp μ ^ k = (Real.exp y)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; rw [hy]; ring
  rw [hpow, abs_mul, abs_of_nonpos hμ, abs_of_pos (inv_pos.2 (Real.exp_pos y)),
    le_div_iff₀ (by linarith), ← div_eq_mul_inv, div_mul_eq_mul_div,
    div_le_one (Real.exp_pos y)]
  nlinarith

/-- The smoothing bound for a symmetric negative semidefinite operator: `‖e^{kA} A‖ ≤ 1/(k+1)`
for every `k ≥ 1`, through the orthonormal eigenbasis of `A`. -/
private theorem norm_pow_exp_apply_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {A : E →L[ℝ] E}
    (hsym : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (hneg : ∀ x, ⟪A x, x⟫ ≤ 0) {k : ℕ} (hk : 0 < k)
    (x : E) : ‖(NormedSpace.exp A ^ k) (A x)‖ ≤ 1 / ((k : ℝ) + 1) * ‖x‖ := by
  have hT : (A : E →ₗ[ℝ] E).IsSymmetric := fun u v => hsym u v
  set b := hT.eigenvectorBasis rfl
  set μ := hT.eigenvalues rfl
  have hb : ∀ i, A (b i) = μ i • b i := fun i => hT.apply_eigenvectorBasis rfl i
  have hμ : ∀ i, μ i ≤ 0 := fun i => by
    have h := hneg (b i)
    rw [hb, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h
    simpa using h
  have hdiag : ∀ i, ((NormedSpace.exp A ^ k) * A) (b i)
      = (μ i * Real.exp (μ i) ^ k) • b i := fun i => by
    have hP : NormedSpace.exp A (b i) = Real.exp (μ i) • b i := exp_apply_of_eigen (hb i)
    rw [mul_apply_eq_comp, hb, map_smul, pow_apply_of_eigen hP, smul_smul]
  exact norm_apply_le_of_diag b (by positivity) hdiag
    (fun i => abs_mul_exp_pow_le (hμ i) hk) x

/-- OP-ST-32 (order two up to a logarithm; source: two-stage exponential Runge methods,
observed order 2).  For symmetric negative semidefinite `L` and the error recursion
`e_{n+1} = e^{hL} eₙ + δₙ` with defects `δₙ = (hL) rₙ` (`ψ₂(z) = z χ(z)`), `‖rₙ‖, ‖δₙ‖ ≤ K h²`
and `e₀ = 0`, the smoothing bound `‖hL e^{jhL}‖ ≤ 1/(e j)` gives `‖eₙ‖ ≤ K h² (2 + log n)`. -/
theorem expRunge_defect_log {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {L : E →L[ℝ] E} (hsym : ∀ x y, ⟪L x, y⟫ = ⟪x, L y⟫)
    (hneg : ∀ x, ⟪L x, x⟫ ≤ 0) {h K : ℝ} (hh : 0 < h) (hK : 0 ≤ K) {e r δ : ℕ → E}
    (he0 : e 0 = 0) (hrec : ∀ n, e (n + 1) = NormedSpace.exp (h • L) (e n) + δ n)
    (hδ : ∀ n, δ n = (h • L) (r n)) (hr : ∀ n, ‖r n‖ ≤ K * h ^ 2)
    (hδn : ∀ n, ‖δ n‖ ≤ K * h ^ 2) (n : ℕ) :
    ‖e n‖ ≤ K * h ^ 2 * (2 + Real.log n) := by
  have hsymA : ∀ x y, ⟪(h • L) x, y⟫ = ⟪x, (h • L) y⟫ := fun x y => by
    simp [inner_smul_left, inner_smul_right, hsym]
  have hnegA : ∀ x, ⟪(h • L) x, x⟫ ≤ 0 := fun x => by
    simpa [inner_smul_left] using mul_nonpos_of_nonneg_of_nonpos hh.le (hneg x)
  set P := NormedSpace.exp (h • L)
  set B := K * h ^ 2
  have hB : 0 ≤ B := by positivity
  have hstep : ∀ j k : ℕ, ‖(P ^ k) (δ j)‖ ≤ B / ((k : ℝ) + 1) := by
    intro j k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hδn j
    · rw [hδ j]
      calc ‖(P ^ k) ((h • L) (r j))‖ ≤ 1 / ((k : ℝ) + 1) * ‖r j‖ :=
            norm_pow_exp_apply_le hsymA hnegA hk (r j)
        _ ≤ 1 / ((k : ℝ) + 1) * B := by
            gcongr
            exact hr j
        _ = B / ((k : ℝ) + 1) := by ring
  have hmain : ∀ n m : ℕ, ‖(P ^ m) (e n)‖ ≤ ∑ j ∈ Finset.range n, B / (((m + j : ℕ) : ℝ) + 1) := by
    intro n
    induction n with
    | zero => intro m; simp [he0]
    | succ n ih =>
      intro m
      rw [hrec, map_add, ← mul_apply_eq_comp, ← pow_succ, Finset.sum_range_succ']
      refine (norm_add_le _ _).trans (add_le_add ?_ (hstep n m))
      refine (ih (m + 1)).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
      congr 3
      omega
  have hharm : ∑ j ∈ Finset.range n, B / (((0 + j : ℕ) : ℝ) + 1) = B * (harmonic n : ℝ) := by
    simp [harmonic, div_eq_mul_inv, Finset.mul_sum]
  calc ‖e n‖ = ‖(P ^ 0) (e n)‖ := by simp
    _ ≤ B * (harmonic n : ℝ) := hharm ▸ hmain n 0
    _ ≤ B * (1 + Real.log n) := by gcongr; exact harmonic_le_one_add_log n
    _ ≤ B * (2 + Real.log n) := by gcongr; norm_num

end LeanDLRA.OpenProblems.Stiff
