import LeanDLRA.OpenProblems.TensorNetworks.Part3Defs
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.LowRankDistance
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Open problems OP-TN-31, OP-TN-32
-/

open Set Finset Filter Topology
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.OpenProblems.TensorNetworks

open LeanDLRA

section Tensor3

variable {n₁ n₂ n₃ r₁ r₂ r₃ : Type*} [Fintype r₁] [Fintype r₂] [Fintype r₃]

end Tensor3

section Tucker3

open scoped Matrix Kronecker

end Tucker3

section SStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end SStep

section Hierarchical

open scoped Matrix LeanDLRA.Frobenius

variable {m₁ m₂ n : Type*} [Fintype m₁] [Fintype m₂] [Fintype n]

end Hierarchical

section Reversal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Reversal

section Equilibrium

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Equilibrium

section Symmetric

open scoped Matrix

end Symmetric

section GaussSeidel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussSeidel

section Certified

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Certified

section Curvature

open scoped Matrix LeanDLRA.Frobenius

end Curvature

section RAIL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end RAIL

section SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end SecondOrder

section Conditioning

open scoped Matrix Kronecker

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Conditioning

section Restriction

open scoped Matrix

end Restriction

section CP

private theorem cpRankLE_two_cpApprox (N : ℕ) : cpRankLE 2 (cpApprox N) := by
  refine ⟨![fun i => (N : ℝ) * (if i = 0 then 1 else 1 / (N : ℝ)),
      fun i => -(N : ℝ) * (if i = 0 then 1 else 0)],
    ![fun i => if i = 0 then 1 else 1 / (N : ℝ), fun i => if i = 0 then 1 else 0],
    ![fun i => if i = 0 then 1 else 1 / (N : ℝ), fun i => if i = 0 then 1 else 0], ?_⟩
  funext i j k
  simp only [cpApprox, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

set_option linter.flexible false in
private theorem tendsto_cpApprox : Tendsto cpApprox atTop (𝓝 wTensor) := by
  rw [tendsto_pi_nhds]; intro i
  rw [tendsto_pi_nhds]; intro j
  rw [tendsto_pi_nhds]; intro k
  have hN : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact Nat.cast_ne_zero.2 (by omega)
  have h0 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) := by simpa using h0
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹ ^ 2) atTop (𝓝 0) := by simpa using h1.pow 2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [cpApprox, wTensor]
  all_goals first
    | (refine tendsto_const_nhds.congr' ?_
       filter_upwards [hN] with N h
       field_simp
       done)
    | (refine h1.congr' ?_
       filter_upwards [hN] with N h
       field_simp
       done)
    | (refine h2.congr' ?_
       filter_upwards [hN] with N h
       field_simp)

private theorem cp_aux (x0 x1 y1 p0 p1 q0 q1 s0 s1 t0 t1 : ℝ)
    (e1 : x0 * p0 * s0 + x1 * p1 * s1 = 0) (e2 : x0 * p0 * t0 + x1 * p1 * t1 = 1)
    (e3 : x0 * q0 * s0 + x1 * q1 * s1 = 1) (e4 : x0 * q0 * t0 + x1 * q1 * t1 = 0)
    (f1 : y1 * p1 * s1 = 1) (f2 : y1 * p1 * t1 = 0) (f3 : y1 * q1 * s1 = 0)
    (f4 : y1 * q1 * t1 = 0) : False := by
  have hy : y1 ≠ 0 := by rintro rfl; simp at f1
  have hp : p1 ≠ 0 := by rintro rfl; simp at f1
  have hs : s1 ≠ 0 := by rintro rfl; simp at f1
  have ht : t1 = 0 := by
    have : y1 * p1 ≠ 0 := mul_ne_zero hy hp
    rcases mul_eq_zero.1 f2 with h | h
    · exact absurd h this
    · exact h
  have hq : q1 = 0 := by
    have : y1 * s1 ≠ 0 := mul_ne_zero hy hs
    have h : (y1 * s1) * q1 = 0 := by linarith [f3]
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h this
    · exact h
  subst ht hq
  simp only [mul_zero, add_zero] at e2 e3 e4
  have h2 : x0 * p0 ≠ 0 := by intro h; rw [h] at e2; simp at e2
  have h3 : x0 * q0 ≠ 0 := by intro h; simp_all
  have h4 : t0 ≠ 0 := by intro h; simp_all
  have : x0 * q0 * t0 ≠ 0 := mul_ne_zero h3 h4
  exact this e4

private theorem cp_aux' (x0 x1 y0 y1 p0 p1 q0 q1 s0 s1 t0 t1 : ℝ)
    (e1 : x0 * p0 * s0 + x1 * p1 * s1 = 0) (e2 : x0 * p0 * t0 + x1 * p1 * t1 = 1)
    (e3 : x0 * q0 * s0 + x1 * q1 * s1 = 1) (e4 : x0 * q0 * t0 + x1 * q1 * t1 = 0)
    (f1 : y0 * p0 * s0 + y1 * p1 * s1 = 1) (f2 : y0 * p0 * t0 + y1 * p1 * t1 = 0)
    (f3 : y0 * q0 * s0 + y1 * q1 * s1 = 0) (f4 : y0 * q0 * t0 + y1 * q1 * t1 = 0) : False := by
  have hdet0 : (p0 * q1 - p1 * q0) * (s0 * t1 - s1 * t0) * (x0 * x1) = -1 := by
    have : (x0 * p0 * s0 + x1 * p1 * s1) * (x0 * q0 * t0 + x1 * q1 * t1)
        - (x0 * p0 * t0 + x1 * p1 * t1) * (x0 * q0 * s0 + x1 * q1 * s1) = -1 := by
      rw [e1, e2, e3, e4]; norm_num
    rw [← this]; ring
  have hdet1 : (p0 * q1 - p1 * q0) * (s0 * t1 - s1 * t0) * (y0 * y1) = 0 := by
    have : (y0 * p0 * s0 + y1 * p1 * s1) * (y0 * q0 * t0 + y1 * q1 * t1)
        - (y0 * p0 * t0 + y1 * p1 * t1) * (y0 * q0 * s0 + y1 * q1 * s1) = 0 := by
      rw [f1, f2, f3, f4]; norm_num
    rw [← this]; ring
  have hne : (p0 * q1 - p1 * q0) * (s0 * t1 - s1 * t0) ≠ 0 := by
    intro h; rw [h] at hdet0; norm_num at hdet0
  have hy : y0 * y1 = 0 := by
    rcases mul_eq_zero.1 hdet1 with h | h
    · exact absurd h hne
    · exact h
  rcases mul_eq_zero.1 hy with h | h
  · subst h
    exact cp_aux x0 x1 y1 p0 p1 q0 q1 s0 s1 t0 t1 e1 e2 e3 e4 (by simpa using f1)
      (by simpa using f2) (by simpa using f3) (by simpa using f4)
  · subst h
    exact cp_aux x1 x0 y0 p1 p0 q1 q0 s1 s0 t1 t0 (by linarith) (by linarith) (by linarith)
      (by linarith) (by simpa using f1) (by simpa using f2) (by simpa using f3)
      (by simpa using f4)

private theorem not_cpRankLE_w : ¬ cpRankLE 2 wTensor := by
  rintro ⟨a, b, c, h⟩
  have key : ∀ i j k, wTensor i j k = ∑ l, a l i * b l j * c l k := fun i j k => by rw [h]
  have k000 := key 0 0 0
  have k001 := key 0 0 1
  have k010 := key 0 1 0
  have k011 := key 0 1 1
  have k100 := key 1 0 0
  have k101 := key 1 0 1
  have k110 := key 1 1 0
  have k111 := key 1 1 1
  simp [wTensor, Fin.sum_univ_two] at k000 k001 k010 k011 k100 k101 k110 k111
  exact cp_aux' (a 0 0) (a 1 0) (a 0 1) (a 1 1) (b 0 0) (b 1 0) (b 0 1) (b 1 1) (c 0 0) (c 1 0)
    (c 0 1) (c 1 1) k000.symm (by linarith) (by linarith) k011.symm k100.symm k101.symm
    k110.symm k111.symm

private theorem cp_not_closed_aux : ¬ IsClosed {T : Fin 2 → Fin 2 → Fin 2 → ℝ | cpRankLE 2 T} := by
  intro h
  exact not_cpRankLE_w (h.mem_of_tendsto tendsto_cpApprox
    (Eventually.of_forall cpRankLE_two_cpApprox))

/-- OP-TN-31 (source: arXiv 2305.19059 §4.1; de Silva–Lim 2008).  The precise obstruction to CP
DLRT: `W` has CP rank `> 2`, it is the limit of the CP-rank-`≤ 2` tensors `cpApprox N`, and hence
the set of tensors of CP rank `≤ 2` is not closed (best low-CP-rank approximations may fail to
exist). -/
theorem cp_rank_two_not_closed :
    ¬ cpRankLE 2 wTensor ∧ (∀ N, cpRankLE 2 (cpApprox N)) ∧
      Tendsto cpApprox atTop (𝓝 wTensor) ∧
      ¬ IsClosed {T : Fin 2 → Fin 2 → Fin 2 → ℝ | cpRankLE 2 T} :=
  ⟨not_cpRankLE_w, cpRankLE_two_cpApprox, tendsto_cpApprox, cp_not_closed_aux⟩

end CP

section SchmidtGradient

-- `HasDerivAt` on `ℝ` needs `ContinuousSMul ℝ ℝ`, found either as
-- `PolynormableSpace.continuousSMul` or as `IsModuleTopology.toContinuousSMul`; which comes first
-- depends on the order in which the imports are loaded. The statements of this section keep
-- the first one, with which they were elaborated originally.
attribute [local instance high] PolynormableSpace.continuousSMul

private theorem exists_antiderivative_poly (q : Polynomial ℝ) :
    ∃ P : Polynomial ℝ, Polynomial.derivative P = q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by rw [map_add, hP, hQ]⟩
  | monomial n a =>
    refine ⟨Polynomial.monomial (n + 1) (a / ((n : ℝ) + 1)), ?_⟩
    rw [Polynomial.derivative_monomial]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    congr 1
    field_simp

private theorem exists_poly_C1_approx {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (R ε : ℝ) (hR : 0 < R)
    (hε : 0 < ε) : ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc (-R) R,
      |p.eval x - f x| ≤ ε ∧ |(Polynomial.derivative p).eval x - deriv f x| ≤ ε := by
  have hδ : 0 < ε / (R + 1) := by positivity
  have hcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-R) R (deriv f)
    hcont.continuousOn _ hδ
  obtain ⟨P, hP⟩ := exists_antiderivative_poly q
  set p : Polynomial ℝ := P - Polynomial.C (P.eval 0) + Polynomial.C (f 0) with hp
  have hpd : Polynomial.derivative p = q := by simp [hp, hP]
  have hp0 : p.eval 0 = f 0 := by simp [hp]
  have hdiff : ∀ x : ℝ, HasDerivAt (fun x => p.eval x - f x)
      (q.eval x - deriv f x) x := by
    intro x
    have h1 : HasDerivAt (fun x => p.eval x) (q.eval x) x := by
      simpa [hpd] using p.hasDerivAt x
    have h2 : HasDerivAt f (deriv f x) x :=
      ((hf.differentiable one_ne_zero) x).hasDerivAt
    exact h1.sub h2
  refine ⟨p, fun x hx => ?_⟩
  have hb : ‖(p.eval x - f x) - (p.eval 0 - f 0)‖ ≤ ε / (R + 1) * ‖x - 0‖ := by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x => p.eval x - f x)
      (s := Set.Icc (-R) R) (C := ε / (R + 1)) (x := 0) (y := x)
      (fun y _ => (hdiff y).differentiableAt)
      (fun y hy => by rw [(hdiff y).deriv]; exact (hq y hy).le)
      (convex_Icc _ _) ⟨by linarith, hR.le⟩ hx
    simpa using this
  have hxR : ‖x - 0‖ ≤ R := by
    rw [sub_zero, Real.norm_eq_abs, abs_le]; exact ⟨hx.1, hx.2⟩
  have hle : ε / (R + 1) * ‖x - 0‖ ≤ ε := by
    calc ε / (R + 1) * ‖x - 0‖ ≤ ε / (R + 1) * R := by gcongr
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  refine ⟨?_, ?_⟩
  · rw [hp0, sub_self, sub_zero, Real.norm_eq_abs] at hb
    exact (hb.trans hle)
  · rw [hpd]
    refine (hq x hx).le.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith

set_option linter.style.longLine false in
private theorem cfc_entry_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {g : ℝ → ℝ} {ε : ℝ} (h : ∀ x ∈ spectrum ℝ A, |g x| ≤ ε) (j k : n) :
    |cfc g A j k| ≤ ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h _ (hA.eigenvalues_mem_spectrum_real j))
  have hrow : ∀ j : n, ∑ x, (hA.eigenvectorBasis x).ofLp j ^ 2 = 1 := by
    intro j
    have := congr_fun (congr_fun (Unitary.coe_mul_star_self hA.eigenvectorUnitary) j) j
    simpa [Matrix.mul_apply, sq, Matrix.IsHermitian.eigenvectorUnitary_apply] using this
  rw [hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, RCLike.ofReal_real_eq_id,
    Function.comp_apply, id_eq, mul_ite, mul_zero, sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Matrix.star_apply, star_trivial, ge_iff_le]
  calc |∑ x, (hA.eigenvectorBasis x).ofLp j * g (hA.eigenvalues x) * (hA.eigenvectorBasis x).ofLp k|
      ≤ ∑ x, |(hA.eigenvectorBasis x).ofLp j * g (hA.eigenvalues x) * (hA.eigenvectorBasis x).ofLp k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ε * (((hA.eigenvectorBasis x).ofLp j ^ 2 + (hA.eigenvectorBasis x).ofLp k ^ 2) / 2) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hg := h _ (hA.eigenvalues_mem_spectrum_real x)
        rw [abs_mul, abs_mul]
        have h2 : |(hA.eigenvectorBasis x).ofLp j| * |(hA.eigenvectorBasis x).ofLp k| ≤
            ((hA.eigenvectorBasis x).ofLp j ^ 2 + (hA.eigenvectorBasis x).ofLp k ^ 2) / 2 := by
          nlinarith [sq_abs ((hA.eigenvectorBasis x).ofLp j), sq_abs ((hA.eigenvectorBasis x).ofLp k),
            sq_nonneg (|(hA.eigenvectorBasis x).ofLp j| - |(hA.eigenvectorBasis x).ofLp k|)]
        calc _ = |(hA.eigenvectorBasis x).ofLp j| * |(hA.eigenvectorBasis x).ofLp k| *
              |g (hA.eigenvalues x)| := by ring
          _ ≤ ((hA.eigenvectorBasis x).ofLp j ^ 2 + (hA.eigenvectorBasis x).ofLp k ^ 2) / 2 * ε := by
            gcongr
          _ = _ := by ring
    _ = ε := by
        rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, hrow j, hrow k]
        ring

open scoped Matrix.Norms.Operator in
private theorem hasDerivAt_trace_pow {n : Type*} [Fintype n] [DecidableEq n] (ρ H : Matrix n n ℝ)
    (m : ℕ) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => ((ρ + s • H) ^ m).trace)
      (m * ((ρ + s0 • H) ^ (m - 1) * H).trace) s0 := by
  have hB : HasDerivAt (fun s : ℝ => ρ + s • H) H s0 := by
    have := ((hasDerivAt_id s0).smul_const H).const_add ρ
    rwa [one_smul] at this
  have h1 := hB.fun_pow' m
  simp only [Nat.pred_eq_sub_one] at h1
  have hT : HasDerivAt (fun s : ℝ => ((ρ + s • H) ^ m).trace)
      (∑ i ∈ Finset.range m, ((ρ + s0 • H) ^ (m - 1 - i) * H * (ρ + s0 • H) ^ i).trace) s0 := by
    let L : Matrix n n ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℝ)
    have := L.hasFDerivAt.comp_hasDerivAt s0 h1
    convert this using 1
    · rfl
    · exact (map_sum L _ _).symm
  refine hT.congr_deriv ?_
  rw [Finset.sum_congr rfl (g := fun _ => ((ρ + s0 • H) ^ (m - 1) * H).trace)]
  · simp
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Matrix.trace_mul_comm, ← mul_assoc, ← pow_add]
    congr 3
    omega

open scoped Matrix.Norms.Operator in
private theorem hasDerivAt_trace_aeval {n : Type*} [Fintype n] [DecidableEq n] (ρ H : Matrix n n ℝ)
    (p : Polynomial ℝ) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => (Polynomial.aeval (ρ + s • H) p).trace)
      ((Polynomial.aeval (ρ + s0 • H) (Polynomial.derivative p) * H).trace) s0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have := hp.add hq
    simp only [map_add, Matrix.trace_add, add_mul]
    exact this
  | monomial k c =>
    have := (hasDerivAt_trace_pow ρ H k s0).const_mul c
    rw [Polynomial.derivative_monomial]
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.trace_smul, smul_eq_mul]
    convert this using 1
    ring

open scoped Matrix.Norms.Operator in
private theorem spec_bound {n : Type*} [Fintype n] [DecidableEq n] (ρ H : Matrix n n ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℝ, |s| ≤ 1 → ∀ x ∈ spectrum ℝ (ρ + s • H), x ∈ Icc (-R) R := by
  refine ⟨‖ρ‖ + ‖H‖ + 1, by positivity, fun s hs x hx => ?_⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · exfalso
    rw [spectrum.mem_iff] at hx
    exact hx (isUnit_of_subsingleton _)
  have h1 : ‖x‖ ≤ ‖ρ + s • H‖ := spectrum.norm_le_norm_of_mem hx
  have h2 : ‖ρ + s • H‖ ≤ ‖ρ‖ + ‖H‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have : |s| * ‖H‖ ≤ 1 * ‖H‖ := by gcongr
    linarith
  rw [Real.norm_eq_abs] at h1
  constructor <;> cases abs_le.1 (h1.trans h2) <;> linarith

private theorem abs_trace_cfc_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {g : ℝ → ℝ} {ε : ℝ} (h : ∀ x ∈ spectrum ℝ A, |g x| ≤ ε) :
    |(cfc g A).trace| ≤ ε * Fintype.card n := by
  rw [Matrix.trace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |(cfc g A).diag i| ≤ ∑ _i : n, ε :=
        Finset.sum_le_sum fun i _ => cfc_entry_le hA h i i
    _ = ε * Fintype.card n := by simp [mul_comm]

private theorem abs_trace_cfc_mul_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {g : ℝ → ℝ} {ε : ℝ} (h : ∀ x ∈ spectrum ℝ A, |g x| ≤ ε)
    (M : Matrix n n ℝ) : |(cfc g A * M).trace| ≤ ε * ∑ j, ∑ k, |M k j| := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  have := cfc_entry_le hA h j k
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

/-- OP-TN-32 (source: arXiv 2609.11811, Eq. (9) and footnote [52]).  For `f ∈ C¹` the trace
functional `ρ ↦ Tr f(ρ)` of a symmetric matrix (e.g. a reduced density matrix, `f(p) = -p log p`
regularized or `p^μ`) is differentiable along every symmetric direction `H` with derivative
`Tr(f'(ρ) H)`, **also at degenerate spectra**.  (For `f(p) = p^μ`, `μ < 1`, zero Schmidt values
need a separate treatment: restrict to the support or regularize.) -/
theorem hasDerivAt_trace_cfc {n : Type*} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {ρ H : Matrix n n ℝ} (hρ : ρ.IsHermitian) (hH : H.IsHermitian) :
    HasDerivAt (fun s : ℝ => (cfc f (ρ + s • H)).trace) ((cfc (deriv f) ρ * H).trace) 0 := by
  have hA : ∀ s : ℝ, (ρ + s • H).IsHermitian := fun s => hρ.add (hH.smul (IsSelfAdjoint.all s))
  obtain ⟨R, hR0, hR⟩ := spec_bound ρ H
  have hpex : ∀ k : ℕ, ∃ p : Polynomial ℝ, ∀ x ∈ Icc (-R) R,
      |p.eval x - f x| ≤ 1 / ((k : ℝ) + 1) ∧
        |(Polynomial.derivative p).eval x - deriv f x| ≤ 1 / ((k : ℝ) + 1) :=
    fun k => exists_poly_C1_approx hf R _ hR0 (by positivity)
  choose p hp using hpex
  have hfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfcont : Continuous f := hf.continuous
  set CH : ℝ := ∑ j, ∑ k, |H k j| with hCH
  have hCH0 : 0 ≤ CH := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, |s| < 1 := by
    have : Continuous (fun s : ℝ => |s|) := continuous_abs
    exact this.continuousAt.eventually (gt_mem_nhds (by simp))
  have key : HasDerivAt (fun s : ℝ => (cfc f (ρ + s • H)).trace)
      ((cfc (deriv f) (ρ + (0 : ℝ) • H) * H).trace) 0 := by
    refine hasDerivAt_of_tendstoUniformlyOnFilter
      (f := fun (k : ℕ) (s : ℝ) => (cfc (fun x => (p k).eval x) (ρ + s • H)).trace)
      (f' := fun (k : ℕ) (s : ℝ) =>
        (cfc (fun x => (Polynomial.derivative (p k)).eval x) (ρ + s • H) * H).trace)
      (g' := fun s : ℝ => (cfc (deriv f) (ρ + s • H) * H).trace) (l := atTop) ?_ ?_ ?_
    · rw [Metric.tendstoUniformlyOnFilter_iff]
      intro ε hε
      have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) * (CH + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (CH + 1)
      have hk : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) * (CH + 1) < ε :=
        hlim.eventually (gt_mem_nhds hε)
      filter_upwards [hk.prod_mk hsmall] with q hq
      obtain ⟨hk, hs⟩ := hq
      have hcs1 : ContinuousOn (deriv f) (spectrum ℝ (ρ + q.2 • H)) := hfc.continuousOn
      have hcs2 : ContinuousOn (fun x => (Polynomial.derivative (p q.1)).eval x)
          (spectrum ℝ (ρ + q.2 • H)) := (Polynomial.continuous _).continuousOn
      have hdiff : (cfc (deriv f) (ρ + q.2 • H) * H).trace -
          (cfc (fun x => (Polynomial.derivative (p q.1)).eval x) (ρ + q.2 • H) * H).trace =
          (cfc (fun x => deriv f x - (Polynomial.derivative (p q.1)).eval x)
            (ρ + q.2 • H) * H).trace := by
        rw [← Matrix.trace_sub, ← sub_mul, cfc_sub _ _ _ hcs1 hcs2]
      have hb := abs_trace_cfc_mul_le (hA q.2)
        (g := fun x => deriv f x - (Polynomial.derivative (p q.1)).eval x)
        (ε := 1 / ((q.1 : ℝ) + 1))
        (fun x hx => by
          rw [abs_sub_comm]; exact (hp q.1 x (hR q.2 hs.le x hx)).2) H
      rw [Real.dist_eq, hdiff]
      refine hb.trans_lt (lt_of_le_of_lt ?_ hk)
      have : 0 ≤ 1 / ((q.1 : ℝ) + 1) := by positivity
      nlinarith
    · refine Eventually.of_forall fun q => ?_
      have h := hasDerivAt_trace_aeval ρ H (p q.1) q.2
      have e : ∀ s : ℝ, cfc (fun x => (p q.1).eval x) (ρ + s • H) =
          Polynomial.aeval (ρ + s • H) (p q.1) := fun s => cfc_polynomial _ _ (hA s)
      have e' : cfc (fun x => (Polynomial.derivative (p q.1)).eval x) (ρ + q.2 • H) =
          Polynomial.aeval (ρ + q.2 • H) (Polynomial.derivative (p q.1)) :=
        cfc_polynomial _ _ (hA q.2)
      simp only [e, e']
      exact h
    · filter_upwards [hsmall] with y hy
      have hcs1 : ∀ k : ℕ, ContinuousOn (fun x => (p k).eval x) (spectrum ℝ (ρ + y • H)) :=
        fun k => (Polynomial.continuous _).continuousOn
      have hcs2 : ContinuousOn f (spectrum ℝ (ρ + y • H)) := hfcont.continuousOn
      have hb : ∀ k : ℕ, dist (cfc (fun x => (p k).eval x) (ρ + y • H)).trace
          (cfc f (ρ + y • H)).trace ≤ 1 / ((k : ℝ) + 1) * Fintype.card n := by
        intro k
        rw [Real.dist_eq, ← Matrix.trace_sub, ← cfc_sub _ _ _ (hcs1 k) hcs2]
        exact abs_trace_cfc_le (hA y)
          (g := fun x => (p k).eval x - f x) (fun x hx => (hp k x (hR y hy.le x hx)).1)
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) hb ?_
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
        (Fintype.card n : ℝ)
  simpa using key

end SchmidtGradient

end LeanDLRA.OpenProblems.TensorNetworks
