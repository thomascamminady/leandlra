import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Results of arXiv 2606.27888: Dynamical low-rank multilevel Monte Carlo for kinetic equations

Formalized from Sec. 2.2.1 of arXiv 2606.27888 (Patwardhan, Krumscheid, Kusch, Løvbak,
Stammer). The module proves two statements on a probability space with values in a real
Hilbert space `H`, with expectations as Bochner integrals:

* `mse_decomposition` (Sec. 2.2.1): for `M` identically distributed, pairwise independent copies
  `S i` of the low-rank QoI `Q_r` and the exact QoI `Q` (both square integrable), the mean squared
  error of the Monte Carlo estimator `M⁻¹ ∑ S i` of `E[Q]` equals `V_r / M + B_r²`, with
  `V_r = E‖Q_r - E Q_r‖²` and `B_r = ‖E[Q_r - Q]‖`. The paper's i.i.d. hypothesis is stated as
  `IdentDistrib` plus pairwise `IndepFun`; the cross terms vanish by `IndepFun.integral_bilin`.
* `bias_le_lipschitz` (Sec. 2.2.1): if the QoI is `Q = F ∘ u` with `F : E → H` `L`-Lipschitz on a
  normed state space `E`, then `B_r ≤ L E‖u_r - u_full‖ + L E‖u_full - u‖`. The expectations of
  the two state distances are assumed integrable, which the paper needs for its right-hand side to
  be finite. The paper's intermediate split `B_r ≤ ‖E[Q_r - Q_full]‖ + ‖E[Q_full - Q]‖` is used
  pointwise inside the proof and is not stated separately.

The two `example`s at the end show that the hypotheses of both theorems are satisfiable.

Not formalized, and why:
* The empirical error model `‖u_r - u_full‖ ≤ K₃Δt + K₄sϑ + K₅ε` behind the bias estimate of the
  augmented BUG integrator. The paper states it as an observation from experiments, not as a
  theorem, so it cannot be proved here and is not assumed.
* Sec. 3.1, eqs. (3.1)-(3.4) (CFL step size, tolerance `ϑ` versus `h_x`, and the bias bound
  `B_r ≤ K̂₆ h_x + K̂₂ h_v^q + K̂₅ ε`). These follow from that unproved error model.
* Sec. 3.2, Theorem 3.2 (Giles' MLMC complexity theorem, quoted from reference [22]). Its proof
  chooses the finest level `L` and the sample sizes `M_ℓ` and sums a geometric series over levels;
  this was not formalized in this pass.
* The MLMC MSE identity `e(Q̂^ML)² = ∑ V_ℓ / M_ℓ + ‖E[Q_L - Q]‖²` of Sec. 3.2. It is the same
  computation as `mse_decomposition`, applied level by level, and is not formalized here.

Core definitions used: none. The results are stated for a general real inner product space `H`
and a general normed space `E`, so no `LeanDLRA` definition applies.
-/

open Set Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2606_27888

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Inner products of two square-integrable `H`-valued functions are integrable. -/
lemma integrable_inner_of_memLp {μ : Measure Ω} {f g : Ω → H} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : Integrable (fun ω => ⟪f ω, g ω⟫) μ := by
  have hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ := hf.integrable_norm_pow (by norm_num)
  have hg2 : Integrable (fun ω => ‖g ω‖ ^ 2) μ := hg.integrable_norm_pow (by norm_num)
  refine Integrable.mono' ((hf2.add hg2).div_const 2)
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable) ?_
  refine Eventually.of_forall fun ω => ?_
  have h := abs_real_inner_le_norm (f ω) (g ω)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (‖f ω‖ - ‖g ω‖), abs_nonneg ⟪f ω, g ω⟫, norm_nonneg (f ω),
    norm_nonneg (g ω)]

/-- **Sec. 2.2.1 (MSE and bias decomposition), arXiv 2606.27888.** Let `Q_r` be the QoI computed
with the low-rank approximation and `Q` the exact QoI, both square-integrable `H`-valued random
variables on a probability space. Let `S i`, `i < M`, be i.i.d. copies of `Q_r` (`IdentDistrib`
to `Q_r`, pairwise independent). Then the MSE of the Monte Carlo estimator `M⁻¹ ∑ S i` of
`E[Q]` equals `V_r / M + B_r²`, where `V_r = E‖Q_r - E[Q_r]‖²` and `B_r = ‖E[Q_r - Q]‖`. -/
theorem mse_decomposition [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Qr Q : Ω → H}
    (hQr : MemLp Qr 2 μ) (hQ : MemLp Q 2 μ) {M : ℕ} (hM : 0 < M) (S : Fin M → Ω → H)
    (hid : ∀ i, IdentDistrib (S i) Qr μ μ)
    (hind : Pairwise fun i j => IndepFun (S i) (S j) μ) :
    ∫ ω, ‖(M : ℝ)⁻¹ • (∑ i, S i ω) - ∫ ω', Q ω' ∂μ‖ ^ 2 ∂μ
      = (M : ℝ)⁻¹ * (∫ ω, ‖Qr ω - ∫ ω', Qr ω' ∂μ‖ ^ 2 ∂μ)
        + ‖∫ ω, (Qr ω - Q ω) ∂μ‖ ^ 2 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  set m : H := ∫ ω, Qr ω ∂μ with hm
  set Qbar : H := ∫ ω, Q ω ∂μ with hQbar
  have hSi : ∀ i, MemLp (S i) 2 μ := fun i => (hid i).memLp_iff.2 hQr
  have hSint : ∀ i, Integrable (S i) μ := fun i => (hSi i).integrable one_le_two
  have hZint : ∀ i, Integrable (fun ω => S i ω - m) μ := fun i =>
    (hSint i).sub (integrable_const m)
  have hZmem : ∀ i, MemLp (fun ω => S i ω - m) 2 μ := fun i => (hSi i).sub (memLp_const m)
  have hEZ : ∀ i, ∫ ω, (S i ω - m) ∂μ = 0 := by
    intro i
    rw [integral_sub (hSint i) (integrable_const m), (hid i).integral_eq, integral_const]
    simp [hm]
  -- the centred estimator `A` and the constant `D = E Q_r - E Q`
  set A : Ω → H := fun ω => (M : ℝ)⁻¹ • ∑ i, (S i ω - m) with hA
  set D : H := m - Qbar with hD
  have hAmem : MemLp A 2 μ := by
    have hsum : MemLp (fun ω => ∑ i, (S i ω - m)) 2 μ :=
      memLp_finsetSum _ fun i _ => hZmem i
    exact hsum.const_smul _
  have hAint : Integrable A μ := hAmem.integrable one_le_two
  have hA0 : ∫ ω, A ω ∂μ = 0 := by
    simp only [hA]
    rw [integral_smul, integral_finsetSum _ fun i _ => hZint i]
    simp [hEZ]
  have hdecomp : ∀ ω, (M : ℝ)⁻¹ • (∑ i, S i ω) - Qbar = A ω + D := by
    intro ω
    have key : (M : ℝ)⁻¹ • ∑ _i : Fin M, m = m := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul, inv_mul_cancel₀ hM', one_smul]
    simp only [hA, hD, smul_sub, Finset.sum_sub_distrib, key]
    abel
  have hsq : (fun ω => ‖(M : ℝ)⁻¹ • (∑ i, S i ω) - Qbar‖ ^ 2)
      = fun ω => (‖A ω‖ ^ 2 + 2 * ⟪A ω, D⟫ + ‖D‖ ^ 2) := by
    funext ω
    rw [hdecomp ω, norm_add_sq_real]
  have hA2 : Integrable (fun ω => ‖A ω‖ ^ 2) μ := by
    have h := integrable_inner_of_memLp hAmem hAmem
    simpa [real_inner_self_eq_norm_sq] using h
  have hAD : Integrable (fun ω => ⟪A ω, D⟫) μ := hAint.inner_const D
  have hAD0 : ∫ ω, ⟪A ω, D⟫ ∂μ = 0 := by
    have h1 : (fun ω => ⟪A ω, D⟫) = fun ω => ⟪D, A ω⟫ :=
      funext fun ω => real_inner_comm _ _
    rw [h1, integral_inner hAint D, hA0, inner_zero_right]
  -- the variance term: E‖A‖² = M⁻¹ V_r
  set V : ℝ := ∫ ω, ‖Qr ω - m‖ ^ 2 ∂μ with hV
  have hcross : ∀ i j, ∫ ω, ⟪S i ω - m, S j ω - m⟫ ∂μ = if i = j then V else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have hcomp : IdentDistrib (fun ω => ‖S i ω - m‖ ^ 2) (fun ω => ‖Qr ω - m‖ ^ 2) μ μ :=
        (hid i).comp (u := fun x : H => ‖x - m‖ ^ 2) (by fun_prop)
      simp only [real_inner_self_eq_norm_sq]
      rw [hcomp.integral_eq]
    · simp only [hij, ↓reduceIte]
      have hind' : IndepFun (fun ω => S i ω - m) (fun ω => S j ω - m) μ :=
        (hind hij).comp (φ := fun x : H => x - m) (ψ := fun x : H => x - m)
          (by fun_prop) (by fun_prop)
      have hb : ∫ ω, ⟪S i ω - m, S j ω - m⟫ ∂μ
          = ⟪∫ ω, (S i ω - m) ∂μ, ∫ ω, (S j ω - m) ∂μ⟫ :=
        hind'.integral_bilin (hZint i) (hZint j) (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)
      rw [hb, hEZ i, hEZ j, inner_zero_left]
  have hAA : ∀ ω, ‖A ω‖ ^ 2 = (M : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ⟪S i ω - m, S j ω - m⟫ := by
    intro ω
    rw [← real_inner_self_eq_norm_sq]
    simp only [hA, real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hin : ∀ i j, Integrable (fun ω => ⟪S i ω - m, S j ω - m⟫) μ :=
    fun i j => integrable_inner_of_memLp (hZmem i) (hZmem j)
  have hVar : ∫ ω, ‖A ω‖ ^ 2 ∂μ = (M : ℝ)⁻¹ * V := by
    simp_rw [hAA]
    rw [integral_const_mul,
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hin i j)]
    have hrow : ∀ i, ∫ ω, ∑ j, ⟪S i ω - m, S j ω - m⟫ ∂μ = ∑ j, (if i = j then V else 0) :=
      fun i => by
        rw [integral_finsetSum _ fun j _ => hin i j]
        exact Finset.sum_congr rfl fun j _ => hcross i j
    simp only [hrow, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- assemble
  have hint1 : Integrable (fun ω => ‖A ω‖ ^ 2 + 2 * ⟪A ω, D⟫) μ :=
    hA2.add (hAD.const_mul 2)
  have hfinal : ∫ ω, ‖(M : ℝ)⁻¹ • (∑ i, S i ω) - Qbar‖ ^ 2 ∂μ
      = (M : ℝ)⁻¹ * V + ‖D‖ ^ 2 := by
    rw [hsq, integral_add hint1 (integrable_const _), integral_add hA2 (hAD.const_mul 2),
      integral_const_mul, hAD0, hVar]
    simp
  have hDint : D = ∫ ω, (Qr ω - Q ω) ∂μ := by
    rw [integral_sub (hQr.integrable one_le_two) (hQ.integrable one_le_two)]
  rw [hfinal, hDint]

/-- **Sec. 2.2.1 (bias bound), arXiv 2606.27888.** Let the QoI be `Q = F ∘ u`, where the state
`u` takes values in a normed space `E` and `F : E → H` satisfies `‖F x - F y‖ ≤ L ‖x - y‖`
(Lipschitz continuity of the QoI in the state). Let `u_r` be the low-rank approximation and
`u_full` the full-rank approximation with the same discretization. Then the bias
`B_r = ‖E[Q_r - Q]‖`, with `Q_r = F ∘ u_r`, satisfies
`B_r ≤ L E‖u_r - u_full‖ + L E‖u_full - u‖`. The expectations of the two state distances are
assumed integrable, which the right-hand side needs to be finite. -/
theorem bias_le_lipschitz {E : Type*} [NormedAddCommGroup E] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : E → H) (L : ℝ) (hF : ∀ x y : E, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (ur ufull u : Ω → E)
    (h1 : Integrable (fun ω => ‖ur ω - ufull ω‖) μ)
    (h2 : Integrable (fun ω => ‖ufull ω - u ω‖) μ) :
    ‖∫ ω, (F (ur ω) - F (u ω)) ∂μ‖
      ≤ L * ∫ ω, ‖ur ω - ufull ω‖ ∂μ + L * ∫ ω, ‖ufull ω - u ω‖ ∂μ := by
  have hg : Integrable (fun ω => L * ‖ur ω - ufull ω‖ + L * ‖ufull ω - u ω‖) μ :=
    (h1.const_mul L).add (h2.const_mul L)
  have hpt : ∀ ω, ‖F (ur ω) - F (u ω)‖
      ≤ L * ‖ur ω - ufull ω‖ + L * ‖ufull ω - u ω‖ := by
    intro ω
    calc ‖F (ur ω) - F (u ω)‖
        ≤ ‖F (ur ω) - F (ufull ω)‖ + ‖F (ufull ω) - F (u ω)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * ‖ur ω - ufull ω‖ + L * ‖ufull ω - u ω‖ := add_le_add (hF _ _) (hF _ _)
  have hmain := norm_integral_le_of_norm_le hg (Eventually.of_forall hpt)
  rw [integral_add (h1.const_mul L) (h2.const_mul L), integral_const_mul,
    integral_const_mul] at hmain
  exact hmain

/-- Non-vacuity of `mse_decomposition`: with `M = 1` and the single copy `S 0 = Q_r`, the
hypotheses hold for constant (hence square-integrable) `Q_r` and `Q`. -/
example {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ∫ ω, ‖((1 : ℕ) : ℝ)⁻¹ • (∑ _i : Fin 1, (fun _ : Ω => (1 : ℝ)) ω)
        - ∫ _ω', (0 : ℝ) ∂μ‖ ^ 2 ∂μ
      = ((1 : ℕ) : ℝ)⁻¹ * (∫ _ω, ‖(1 : ℝ) - ∫ _ω', (1 : ℝ) ∂μ‖ ^ 2 ∂μ)
        + ‖∫ _ω, ((1 : ℝ) - 0) ∂μ‖ ^ 2 :=
  mse_decomposition (Qr := fun _ => (1 : ℝ)) (Q := fun _ => (0 : ℝ)) (memLp_const _)
    (memLp_const _) one_pos (fun _ => fun _ => (1 : ℝ))
    (fun _ => IdentDistrib.refl aemeasurable_const)
    (fun i j h => (h (Subsingleton.elim i j)).elim)

/-- Non-vacuity of `bias_le_lipschitz`: `F = id` on `ℝ` is `1`-Lipschitz, and constant states
have integrable distances. -/
example {μ : Measure Ω} [IsProbabilityMeasure μ] (a b c : ℝ) :
    ‖∫ _ω, (id a - id c) ∂μ‖ ≤ 1 * ∫ _ω, ‖a - b‖ ∂μ + 1 * ∫ _ω, ‖b - c‖ ∂μ :=
  bias_le_lipschitz (H := ℝ) id 1 (fun x y => by simp) (fun _ => a) (fun _ => b) (fun _ => c)
    (integrable_const _) (integrable_const _)

end LeanDLRA.Literature.P2606_27888
