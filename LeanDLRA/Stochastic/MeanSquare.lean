import LeanDLRA.Foundations.Projector
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG

/-!
# Abstract `L²(Ω)` cores of stochastic DLRA

Stochastic calculus is out of scope of LeanDLRA.  Everything in this file is therefore stated
either in an abstract real inner product space `E` (to be read as `L²(Ω; ℝᵈ)`, where `‖X‖²` is
`E|X|²` and `⟪X, Y⟫` is `E[X·Y]`) or with Bochner integrals over an arbitrary measure (the
probability law of a random parameter `ν`).  Independence, the martingale property of Itô
increments and the isometry `E|b ΔW|² = Δt E|b|²` enter **only** as explicit orthogonality / norm
hypotheses.  Measurability of the DLRA iterates (SVD truncation is discontinuous at repeated
singular values) is never assumed: it is replaced by integrability of the *bounds*.

## Main results

* **OP-SL-03** (2501.06125 Thm 2, Sec. 3.1; 2606.27888 Sec. 2.2): `integral_norm_le_of_pathwise`,
  `norm_weighted_sum_le_of_pathwise` (Monte Carlo / finitely supported laws),
  `integrable_of_pathwise`, `bug_error_integrable`, and `bug_expected_error_le`: the
  deterministic robust BUG bound, applied realisation by realisation with parameter-dependent
  Lipschitz constant, field bound, normal component and (random) rank, gives
  `‖E[Yₙ - A(tₙ)]‖ ≤ E‖Yₙ - A(tₙ)‖ ≤ E[e^{LT}] δ + E[T e^{LT} c₁ ε] + E[T e^{LT} c₂] h`.
* **MSE / bias decomposition** (2501.06125 Sec. 3.1 Eq. (6), 2606.27888 Sec. 2.2.1):
  `mse_decomposition`, `bias_le`.
* **OP-SB-16** (2609.20292 Sec. 2.6; 2601.21428 Lemma C.1 / Lemma 5.1): `staggered_step_le` and
  `staggeredDLR_second_moment` (proved):
  `‖Xₙ‖² ≤ e^{C tₙ} (‖X₀‖² + C tₙ)` with `C = 1 + 3K`.
* **Mean-square stability of the linear DLR Euler–Maruyama scheme** (2601.21428 Props. 5.7, 5.8,
  6.5; OP-SB-40 (i) / OP-SL-26): `dlrEulerMaruyama_meanSquare_le` (proved) and
  `dlrEulerMaruyama_meanSquare_tendsto_zero`; no Gramian enters.
* **OP-SL-22** (2601.21428 Alg. 3, 2609.20292 Rem. 2.3): `tangent_apply_eq_add_extra`,
  `norm_extraTerm_le`, `extraTerm_eq_zero`, `norm_sum_extraTerm_le_of_orthogonal`.
* **OP-SL-07** (2607.27432 Lemma 4.1): `norm_bilin_sub_le` (corrected covariance bound),
  `secondMoment_bound_sharp`, the counterexample `secondMoment_gap` to the proof step, and the
  exact trace identity `secondMoment_trace_eq_of_fixed` in the lemma's own setting.
* **OP-SL-06** (2501.06125 Remark 3, Table 1): `corr_ge`, `abs_optCoeff_sub_one_le`,
  `corr_optCoeff_uniform`, `tendsto_corr_optCoeff`.
* **OP-SL-08** (2601.21428 Thm 5.4, def. (51)): `isOrthProj_starProjection`,
  `tangent_apply_eq_self_of_right`, `hasOrthogonalProjection_span`,
  `pinvStaggered_second_moment`, `pinvTangent_apply_eq_self`.
* **1803.00499 Theorem 3** (error propagation of the low-rank Fokker–Planck dynamics):
  `integral_gronwall_le`, `E(t) ≤ (E(0) + ε² t) exp(∫₀ᵗ γ)` from the integral inequality.

## What remains open

* OP-SL-03: the statement is proved under integrability of the *bounds*.  The Bochner integrals
  in it are genuine expectations only if `ν ↦ Yₙ(ν)` is a.e. strongly measurable (then
  `bug_error_integrable` gives integrability); without it they are `0` by Lean's convention and
  the bound says nothing.  That measurability (SVD truncation is discontinuous) is open; the
  finitely-supported version `norm_weighted_sum_le_of_pathwise` needs no measurability at all.
* OP-SL-22: the per-step extra term of Alg. 3 is bounded by `‖(I - P_U) ξ‖` without `γ`, and its
  accumulation is `O(ε √T)` *if* the extra terms are pairwise orthogonal; their orthogonality
  (they are not adapted) and the propagation through the nonlinear scheme remain open.
* OP-SL-07: the counterexample refutes only the generic proof step of Lemma 4.1, not (44)
  itself; in the lemma's setting the trace version holds exactly
  (`secondMoment_trace_eq_of_fixed`).  Whether the Frobenius-norm bound (44), i.e. an `O(Λ)`
  bound on the off-diagonal cross covariances, holds is open.
* OP-SL-08: the identification of `E[· Ỹᵀ] C⁺ Ỹ` with the orthogonal projector onto `span Ỹ` is
  standard linear algebra and is used as the *definition* of `P_Ỹ` here; the strong error bound
  of Thm 5.4 itself (with `ε` over rank-`≤ k` processes) is not formalised, only its projector
  and second-moment ingredients.
-/

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.MeanSquare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Pythagoras for orthogonal families -/

/-- Pythagoras for a pairwise orthogonal finite family. -/
theorem norm_sq_sum_of_orthogonal {ι : Type*} (s : Finset ι) (Z : ι → E)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪Z i, Z j⟫ = 0) :
    ‖∑ i ∈ s, Z i‖ ^ 2 = ∑ i ∈ s, ‖Z i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single i (fun j hj hji => h i hi j hj (Ne.symm hji))
    (fun h' => absurd hi h'), real_inner_self_eq_norm_sq]

/-! ### OP-SL-03: robust bounds in expectation -/

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Pathwise bounds pass to expectations** (OP-SL-03).  If `‖f ν‖ ≤ c₀ ν δ + c₁ ν + c₂ ν h` for
almost every parameter `ν` and the three coefficient functions are integrable, then
`‖E f‖ ≤ E‖f‖ ≤ E[c₀] δ + E[c₁] + E[c₂] h` (the coefficient `c₁` stands for the product
`c₁(ν) ε(ν)`).  No measurability of `f` is assumed, but then the statement is only informative
when `f` is a.e. strongly measurable: otherwise both Bochner integrals are `0` by convention.
See `integrable_of_pathwise`; the finitely supported version
`norm_weighted_sum_le_of_pathwise` has no such caveat. -/
theorem integral_norm_le_of_pathwise {f : Ω → E} {c₀ c₁ c₂ : Ω → ℝ} {δ h : ℝ}
    (hc₀ : Integrable c₀ μ) (hc₁ : Integrable c₁ μ) (hc₂ : Integrable c₂ μ)
    (hf : ∀ᵐ ν ∂μ, ‖f ν‖ ≤ c₀ ν * δ + c₁ ν + c₂ ν * h) :
    ‖∫ ν, f ν ∂μ‖ ≤ ∫ ν, ‖f ν‖ ∂μ ∧
      ∫ ν, ‖f ν‖ ∂μ ≤ (∫ ν, c₀ ν ∂μ) * δ + ∫ ν, c₁ ν ∂μ + (∫ ν, c₂ ν ∂μ) * h := by
  refine ⟨norm_integral_le_integral_norm _, ?_⟩
  have hg : Integrable (fun ν => c₀ ν * δ + c₁ ν + c₂ ν * h) μ :=
    ((hc₀.mul_const δ).add hc₁).add (hc₂.mul_const h)
  calc ∫ ν, ‖f ν‖ ∂μ ≤ ∫ ν, (c₀ ν * δ + c₁ ν + c₂ ν * h) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hg hf
    _ = _ := by
        have i1 : Integrable (fun ν => c₀ ν * δ + c₁ ν) μ := (hc₀.mul_const δ).add hc₁
        rw [integral_add i1 (hc₂.mul_const h), integral_add (hc₀.mul_const δ) hc₁,
          integral_mul_const, integral_mul_const]

omit [InnerProductSpace ℝ E] in
/-- **When the expectation bound is informative** (OP-SL-03).  Lean's Bochner integral of a
function that is not a.e. strongly measurable is `0` by convention, so the conclusion of
`integral_norm_le_of_pathwise` carries information about `E‖f‖` and `E f` only when
`ν ↦ f ν` is a.e. strongly measurable.  Under that (and only that) extra hypothesis the pathwise
bound with integrable coefficients makes `f` Bochner integrable, so both integrals are genuine
expectations. -/
theorem integrable_of_pathwise {f : Ω → E} {c₀ c₁ c₂ : Ω → ℝ} {δ h : ℝ}
    (hc₀ : Integrable c₀ μ) (hc₁ : Integrable c₁ μ) (hc₂ : Integrable c₂ μ)
    (hfm : AEStronglyMeasurable f μ) (hf : ∀ᵐ ν ∂μ, ‖f ν‖ ≤ c₀ ν * δ + c₁ ν + c₂ ν * h) :
    Integrable f μ :=
  Integrable.mono' (((hc₀.mul_const δ).add hc₁).add (hc₂.mul_const h)) hfm hf

/-- **Monte Carlo version** (OP-SL-03 for finitely supported laws / sample averages).  For
nonnegative weights `w` and pathwise bounds on every sample,
`‖∑ wᵢ fᵢ‖ ≤ (∑ wᵢ c₀ᵢ) δ + ∑ wᵢ c₁ᵢ + (∑ wᵢ c₂ᵢ) h`.  No measurability issue arises. -/
theorem norm_weighted_sum_le_of_pathwise {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : ι → E} {c₀ c₁ c₂ : ι → ℝ} {δ h : ℝ}
    (hf : ∀ i ∈ s, ‖f i‖ ≤ c₀ i * δ + c₁ i + c₂ i * h) :
    ‖∑ i ∈ s, w i • f i‖ ≤
      (∑ i ∈ s, w i * c₀ i) * δ + ∑ i ∈ s, w i * c₁ i + (∑ i ∈ s, w i * c₂ i) * h := by
  calc ‖∑ i ∈ s, w i • f i‖ ≤ ∑ i ∈ s, ‖w i • f i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, w i * (c₀ i * δ + c₁ i + c₂ i * h) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_smul, Real.norm_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (hf i hi) (hw i hi)
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- **Robust BUG error bound in expectation** (OP-SL-03; 2501.06125 Thm 2 for general robust
BUG).  For every parameter `ν` let `Yₙ(ν)` be a BUG trajectory (`IsBUGStep`) for the field
`F ν` with Lipschitz constant `L ν`, bound `B ν` and normal-component level `ε ν`; the projectors
`P ν n`, `Q ν n` (hence the rank) may depend on `ν` arbitrarily.  With a common initial error
bound `δ` and integrable coefficient functions,
`‖E[Yₙ - A(tₙ)]‖ ≤ E‖Yₙ - A(tₙ)‖ ≤ E[e^{LT}] δ + E[T e^{LT} c₁(L) ε] + E[T e^{LT} c₂(L,B)] h`.
This is the pathwise bound `bug_global_error_le` averaged: the deterministic robust bound, which
2501.06125 (Sec. 3.1) says does not carry over to the uncertain setting, holds realisation by
realisation and hence in mean.  Caveat: the two integrals on the left are genuine expectations
only if `ν ↦ Yₙ(ν) - A(tₙ; ν)` is a.e. strongly measurable (then it is integrable,
`bug_error_integrable`); this measurability (SVD truncation is discontinuous) is not proved. -/
theorem bug_expected_error_le {F : Ω → ℝ → E → E} {L B ε : Ω → ℝ}
    (hF : ∀ ν, IsLipschitzField (F ν) (L ν)) (hL : ∀ ν, 0 ≤ L ν)
    (hB : ∀ ν, IsBoundedField (F ν) (B ν)) (hε : ∀ ν, 0 ≤ ε ν) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : Ω → ℝ → E} (hA : ∀ ν, ODESolution (F ν) (A ν) t₀ (t₀ + N * h))
    {P Q : Ω → ℕ → E →L[ℝ] E} {Y : Ω → ℕ → E} {YK YL YS Φ : Ω → ℕ → ℝ → E}
    (hstep : ∀ ν, ∀ n < N, IsBUGStep (F ν) (ε ν) (P ν n) (Q ν n) (P ν (n + 1)) (Q ν (n + 1))
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y ν n) (YK ν n) (YL ν n) (YS ν n))
    (hY : ∀ ν, ∀ n < N, Y ν (n + 1) = YS ν n (t₀ + (n + 1) * h))
    (hΦ : ∀ ν, ∀ n < N, ODESolution (F ν) (Φ ν n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ ν, ∀ n < N, Φ ν n (t₀ + n * h) = Y ν n) {δ T : ℝ}
    (hδ : ∀ ν, ‖Y ν 0 - A ν t₀‖ ≤ δ)
    (hi₀ : Integrable (fun ν => Real.exp (L ν * T)) μ)
    (hi₁ : Integrable (fun ν => T * Real.exp (L ν * T) * bugC₁ (L ν) H * ε ν) μ)
    (hi₂ : Integrable (fun ν => T * Real.exp (L ν * T) * bugC₂ (L ν) (B ν) H) μ)
    {n : ℕ} (hn : n ≤ N) (hT : (n : ℝ) * h ≤ T) :
    ‖∫ ν, (Y ν n - A ν (t₀ + n * h)) ∂μ‖ ≤ ∫ ν, ‖Y ν n - A ν (t₀ + n * h)‖ ∂μ ∧
      ∫ ν, ‖Y ν n - A ν (t₀ + n * h)‖ ∂μ ≤ (∫ ν, Real.exp (L ν * T) ∂μ) * δ
        + ∫ ν, T * Real.exp (L ν * T) * bugC₁ (L ν) H * ε ν ∂μ
        + (∫ ν, T * Real.exp (L ν * T) * bugC₂ (L ν) (B ν) H ∂μ) * h := by
  refine integral_norm_le_of_pathwise hi₀ hi₁ hi₂ (Eventually.of_forall fun ν => ?_)
  have := bug_global_error_le (hF ν) (hL ν) (hB ν) (hε ν) hh hhH (hA ν) (hstep ν) (hY ν) (hΦ ν)
    (hΦ₀ ν) (hδ ν) n hn hT
  exact this.trans_eq (by ring)

/-- **Integrability of the random BUG error** (OP-SL-03).  Under the hypotheses of
`bug_expected_error_le`, if in addition `ν ↦ Yₙ(ν) - A(tₙ; ν)` is a.e. strongly measurable, then it
is Bochner integrable, so `E[Yₙ - A(tₙ)]` and `E‖Yₙ - A(tₙ)‖` in `bug_expected_error_le` are
genuine (non-conventional) expectations.  The measurability hypothesis itself is the part of
OP-SL-03 that remains open. -/
theorem bug_error_integrable {F : Ω → ℝ → E → E} {L B ε : Ω → ℝ}
    (hF : ∀ ν, IsLipschitzField (F ν) (L ν)) (hL : ∀ ν, 0 ≤ L ν)
    (hB : ∀ ν, IsBoundedField (F ν) (B ν)) (hε : ∀ ν, 0 ≤ ε ν) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : Ω → ℝ → E} (hA : ∀ ν, ODESolution (F ν) (A ν) t₀ (t₀ + N * h))
    {P Q : Ω → ℕ → E →L[ℝ] E} {Y : Ω → ℕ → E} {YK YL YS Φ : Ω → ℕ → ℝ → E}
    (hstep : ∀ ν, ∀ n < N, IsBUGStep (F ν) (ε ν) (P ν n) (Q ν n) (P ν (n + 1)) (Q ν (n + 1))
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y ν n) (YK ν n) (YL ν n) (YS ν n))
    (hY : ∀ ν, ∀ n < N, Y ν (n + 1) = YS ν n (t₀ + (n + 1) * h))
    (hΦ : ∀ ν, ∀ n < N, ODESolution (F ν) (Φ ν n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ ν, ∀ n < N, Φ ν n (t₀ + n * h) = Y ν n) {δ T : ℝ}
    (hδ : ∀ ν, ‖Y ν 0 - A ν t₀‖ ≤ δ)
    (hi₀ : Integrable (fun ν => Real.exp (L ν * T)) μ)
    (hi₁ : Integrable (fun ν => T * Real.exp (L ν * T) * bugC₁ (L ν) H * ε ν) μ)
    (hi₂ : Integrable (fun ν => T * Real.exp (L ν * T) * bugC₂ (L ν) (B ν) H) μ)
    {n : ℕ} (hn : n ≤ N) (hT : (n : ℝ) * h ≤ T)
    (hm : AEStronglyMeasurable (fun ν => Y ν n - A ν (t₀ + n * h)) μ) :
    Integrable (fun ν => Y ν n - A ν (t₀ + n * h)) μ := by
  refine integrable_of_pathwise (δ := δ) (h := h) hi₀ hi₁ hi₂ hm
    (Eventually.of_forall fun ν => ?_)
  have := bug_global_error_le (hF ν) (hL ν) (hB ν) (hε ν) hh hhH (hA ν) (hstep ν) (hY ν) (hΦ ν)
    (hΦ₀ ν) (hδ ν) n hn hT
  exact this.trans_eq (by ring)

/-! ### MSE and bias decomposition -/

/-- **MSE decomposition** (2501.06125 Sec. 3.1 Eq. (6); 2606.27888 Sec. 2.2.1).  In
`E = L²(Ω)` let `Zᵢ = Xᵢ - E X` be the centred i.i.d. samples (pairwise orthogonal, of common
squared norm `V = Var X`) and `b = E X - Q` the bias, a constant and hence orthogonal to centred
variables.  Then the sample mean `X̄ = Q + b + (1/N) ∑ Zᵢ` has
`E|X̄ - Q|² = V / N + b²`. -/
theorem mse_decomposition {N : ℕ} (hN : 0 < N) {Z : Fin N → E} {b : E} {V : ℝ}
    (horth : ∀ i j, i ≠ j → ⟪Z i, Z j⟫ = 0) (hb : ∀ i, ⟪Z i, b⟫ = 0) (hV : ∀ i, ‖Z i‖ ^ 2 = V) :
    ‖(1 / (N : ℝ)) • ∑ i, Z i + b‖ ^ 2 = V / N + ‖b‖ ^ 2 := by
  have hS : ‖∑ i, Z i‖ ^ 2 = N * V := by
    rw [norm_sq_sum_of_orthogonal _ _ fun i _ j _ hij => horth i j hij]
    simp [hV]
  have hin : ⟪(1 / (N : ℝ)) • ∑ i, Z i, b⟫ = 0 := by
    rw [real_inner_smul_left, sum_inner]
    simp [hb]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_add_sq_real, hin, norm_smul, mul_pow, hS, Real.norm_of_nonneg (by positivity)]
  field_simp
  ring

/-- **Bias bound for a Lipschitz quantity of interest** (2501.06125 Sec. 3.1; 2606.27888
Sec. 2.2.1): `|E[G(u_r)] - E[G(u)]| ≤ L E‖u_r - u_full‖ + L E‖u_full - u‖`, splitting the bias
into the DLRA (rank) error and the discretisation error of the full-rank solver. -/
theorem bias_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {V : Type*}
    [NormedAddCommGroup V] {G : V → ℝ} {Lg : ℝ} (hG : ∀ x y, |G x - G y| ≤ Lg * ‖x - y‖)
    {ur uf u : Ω → V} (hi₁ : Integrable (fun ν => ‖ur ν - uf ν‖) μ)
    (hi₂ : Integrable (fun ν => ‖uf ν - u ν‖) μ) :
    |∫ ν, (G (ur ν) - G (u ν)) ∂μ| ≤
      Lg * ∫ ν, ‖ur ν - uf ν‖ ∂μ + Lg * ∫ ν, ‖uf ν - u ν‖ ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi₁.const_mul Lg)
    (hi₂.const_mul Lg), ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) ((hi₁.const_mul Lg).add (hi₂.const_mul Lg))
    (Eventually.of_forall fun ν => ?_))
  simp only [Real.norm_eq_abs]
  calc |G (ur ν) - G (u ν)| = |(G (ur ν) - G (uf ν)) + (G (uf ν) - G (u ν))| := by ring_nf
    _ ≤ |G (ur ν) - G (uf ν)| + |G (uf ν) - G (u ν)| := abs_add_le _ _
    _ ≤ _ := add_le_add (hG _ _) (hG _ _)

end Expectation

/-! ### OP-SB-16: second moments of the staggered DLR scheme -/

/-- **One-step mean-square bound** (2601.21428 Lemma C.1 / Lemma 5.1; 2609.20292 Sec. 2.6).  For
`X' = X + Π (Δt a(X) + ξ)` with an orthogonal projector `Π`, a noise increment whose projection
is orthogonal to `X` and to `Π a(X)` (martingale property), `‖Π ξ‖² ≤ Δt K (1 + ‖X‖²)`
(Itô isometry plus linear growth of `b`), linear growth of `a` and `Δt ≤ 1`:
`‖X'‖² ≤ (1 + (1 + 3K) Δt) ‖X‖² + (1 + 3K) Δt`. -/
theorem staggered_step_le {K dt : ℝ} (hdt : 0 ≤ dt) (hdt1 : dt ≤ 1)
    {Pr : E →L[ℝ] E} (hPr : IsOrthProj Pr) {a : E → E} (ha : ∀ x, ‖a x‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2))
    {X ξ X' : E} (h1 : ⟪X, Pr ξ⟫ = 0) (h2 : ⟪Pr (a X), Pr ξ⟫ = 0)
    (hξ : ‖Pr ξ‖ ^ 2 ≤ dt * K * (1 + ‖X‖ ^ 2)) (hX' : X' = X + Pr (dt • a X + ξ)) :
    ‖X'‖ ^ 2 ≤ (1 + (1 + 3 * K) * dt) * ‖X‖ ^ 2 + (1 + 3 * K) * dt := by
  have huv : ⟪X + dt • Pr (a X), Pr ξ⟫ = 0 := by
    rw [inner_add_left, real_inner_smul_left, h1, h2]; ring
  have hX'' : X' = (X + dt • Pr (a X)) + Pr ξ := by
    rw [hX', map_add, map_smul, add_assoc]
  have hu : ‖X + dt • Pr (a X)‖ ^ 2 =
      ‖X‖ ^ 2 + dt * (2 * ⟪X, Pr (a X)⟫) + dt ^ 2 * ‖Pr (a X)‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hPa : ‖Pr (a X)‖ ^ 2 ≤ ‖a X‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hPr.norm_le _) 2
  have hin : 2 * ⟪X, Pr (a X)⟫ ≤ ‖X‖ ^ 2 + ‖a X‖ ^ 2 := by
    have := real_inner_le_norm X (Pr (a X))
    nlinarith [sq_nonneg (‖X‖ - ‖Pr (a X)‖)]
  have hK := ha X
  have e1 : dt * (2 * ⟪X, Pr (a X)⟫) ≤ dt * (‖X‖ ^ 2 + ‖a X‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hin hdt
  have e2 : dt ^ 2 * ‖Pr (a X)‖ ^ 2 ≤ dt * ‖a X‖ ^ 2 := by
    have : dt ^ 2 ≤ dt := by nlinarith
    exact mul_le_mul this hPa (sq_nonneg _) hdt
  have e3 : dt * ‖a X‖ ^ 2 ≤ dt * (K * (1 + ‖X‖ ^ 2)) := mul_le_mul_of_nonneg_left hK hdt
  rw [hX'', norm_add_sq_real, huv, hu]
  nlinarith

/-- **OP-SB-16, second-moment boundedness of the staggered DLR scheme** (2609.20292 Sec. 2.6,
after Eq. (36); claimed there by analogy with Lemma 6.1 of Part I).  Abstract core: in
`E = L²(Ω; ℝᵈ)` let `Xₙ₊₁ = Xₙ + Πₙ (dt a(Xₙ) + ξₙ)` with orthogonal tangent projectors `Πₙ`
and noise increments satisfying the martingale orthogonality and the Itô-isometry bound.  Then
`E|Xₙ|² ≤ e^{C tₙ} (E|X₀|² + C tₙ)` with `C = 1 + 3K` depending only on the linear-growth
constant.  This is the statement `staggeredDLR_second_moment`. -/
theorem staggeredDLR_second_moment (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ {X ξ : ℕ → E} {Pr : ℕ → E →L[ℝ] E} {a : E → E} {dt : ℝ}, 0 ≤ dt → dt ≤ 1 →
      (∀ n, IsOrthProj (Pr n)) → (∀ x, ‖a x‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2)) →
      (∀ n, ⟪X n, Pr n (ξ n)⟫ = 0) → (∀ n, ⟪Pr n (a (X n)), Pr n (ξ n)⟫ = 0) →
      (∀ n, ‖Pr n (ξ n)‖ ^ 2 ≤ dt * K * (1 + ‖X n‖ ^ 2)) →
      (∀ n, X (n + 1) = X n + Pr n (dt • a (X n) + ξ n)) →
      ∀ n : ℕ, ‖X n‖ ^ 2 ≤ Real.exp (C * (n * dt)) * (‖X 0‖ ^ 2 + C * (n * dt)) := by
  refine ⟨1 + 3 * K, ?_⟩
  intro X ξ Pr a dt hdt hdt1 hPr ha h1 h2 hξ hX n
  have hC : 0 ≤ 1 + 3 * K := by linarith
  have hstep : ∀ n, ‖X (n + 1)‖ ^ 2 ≤
      Real.exp ((1 + 3 * K) * dt) * ‖X n‖ ^ 2 + (1 + 3 * K) * dt := by
    intro n
    refine (staggered_step_le hdt hdt1 (hPr n) ha (h1 n) (h2 n) (hξ n) (hX n)).trans ?_
    have := Real.add_one_le_exp ((1 + 3 * K) * dt)
    have := mul_le_mul_of_nonneg_right (show 1 + (1 + 3 * K) * dt ≤
      Real.exp ((1 + 3 * K) * dt) by linarith) (sq_nonneg ‖X n‖)
    linarith
  have := discrete_gronwall_exp (e := fun n => ‖X n‖ ^ 2) hC hdt (mul_nonneg hC hdt) hstep n
  exact this.trans_eq (by ring)

/-- **Stochastic tangent projectors** (2601.21428 Eqs. (16), (19), (21)): for commuting
orthogonal projectors `L = P_U ⊗ I` and `R = I ⊗ P_Y` the tangent projector
`P_U + (I - P_U) P_Y` is an orthogonal projector, so `staggeredDLR_second_moment` applies to the
projected / staggered Euler–Maruyama schemes with `Πₙ = tangent Lₙ Rₙ`. -/
theorem tangent_staggered_second_moment {K : ℝ} (hK : 0 ≤ K) {X ξ : ℕ → E}
    {Lp Rp : ℕ → E →L[ℝ] E} {a : E → E} {dt : ℝ} (hdt : 0 ≤ dt) (hdt1 : dt ≤ 1)
    (hL : ∀ n, IsOrthProj (Lp n)) (hR : ∀ n, IsOrthProj (Rp n))
    (hc : ∀ n x, Lp n (Rp n x) = Rp n (Lp n x)) (ha : ∀ x, ‖a x‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2))
    (h1 : ∀ n, ⟪X n, tangent (Lp n) (Rp n) (ξ n)⟫ = 0)
    (h2 : ∀ n, ⟪tangent (Lp n) (Rp n) (a (X n)), tangent (Lp n) (Rp n) (ξ n)⟫ = 0)
    (hξ : ∀ n, ‖tangent (Lp n) (Rp n) (ξ n)‖ ^ 2 ≤ dt * K * (1 + ‖X n‖ ^ 2))
    (hX : ∀ n, X (n + 1) = X n + tangent (Lp n) (Rp n) (dt • a (X n) + ξ n)) (n : ℕ) :
    ‖X n‖ ^ 2 ≤ Real.exp ((1 + 3 * K) * (n * dt)) * (‖X 0‖ ^ 2 + (1 + 3 * K) * (n * dt)) := by
  have hC : 0 ≤ 1 + 3 * K := by linarith
  have hstep : ∀ n, ‖X (n + 1)‖ ^ 2 ≤
      Real.exp ((1 + 3 * K) * dt) * ‖X n‖ ^ 2 + (1 + 3 * K) * dt := by
    intro n
    refine (staggered_step_le hdt hdt1 ((hL n).tangent (hR n) (hc n)) ha (h1 n) (h2 n) (hξ n)
      (hX n)).trans ?_
    have := Real.add_one_le_exp ((1 + 3 * K) * dt)
    have := mul_le_mul_of_nonneg_right (show 1 + (1 + 3 * K) * dt ≤
      Real.exp ((1 + 3 * K) * dt) by linarith) (sq_nonneg ‖X n‖)
    linarith
  have := discrete_gronwall_exp (e := fun n => ‖X n‖ ^ 2) hC hdt (mul_nonneg hC hdt) hstep n
  exact this.trans_eq (by ring)

/-! ### Mean-square stability for linear coefficients -/

/-- **Mean-square stability of projected (DLR) Euler–Maruyama** (2601.21428 Props. 5.7, 5.8, 6.5;
OP-SB-40 (i) / OP-SL-26).
For `x_{n+1} = Pₙ (xₙ + h F xₙ + ξₙ)` with orthogonal projectors `Pₙ`, a linear drift with
one-sided bound `μ` and bound `L`, and multiplicative noise increments orthogonal to the drift
step with `‖ξₙ‖² ≤ h σ² ‖xₙ‖²`:
`‖xₙ‖² ≤ (1 + h (2 μ + σ²) + h² L²)ⁿ ‖x₀‖²`.  No Gramian or singular value appears. -/
theorem dlrEulerMaruyama_meanSquare_le {Fd : E →L[ℝ] E} {P : ℕ → E →L[ℝ] E} {x ξ : ℕ → E}
    {h μ L σ : ℝ} (hP : ∀ n, IsOrthProj (P n)) (hμ : ∀ y, ⟪Fd y, y⟫ ≤ μ * ‖y‖ ^ 2)
    (hL : ∀ y, ‖Fd y‖ ≤ L * ‖y‖) (hh : 0 ≤ h)
    (hx : ∀ n, x (n + 1) = P n (x n + h • Fd (x n) + ξ n))
    (horth : ∀ n, ⟪x n + h • Fd (x n), ξ n⟫ = 0)
    (hnoise : ∀ n, ‖ξ n‖ ^ 2 ≤ h * σ ^ 2 * ‖x n‖ ^ 2) :
    ∀ n, ‖x n‖ ^ 2 ≤ (1 + h * (2 * μ + σ ^ 2) + h ^ 2 * L ^ 2) ^ n * ‖x 0‖ ^ 2 := by
  set q := 1 + h * (2 * μ + σ ^ 2) + h ^ 2 * L ^ 2 with hq_def
  have step : ∀ n, ‖x (n + 1)‖ ^ 2 ≤ q * ‖x n‖ ^ 2 := by
    intro n
    have hy := x n
    have h1 : ‖x (n + 1)‖ ^ 2 ≤ ‖x n + h • Fd (x n) + ξ n‖ ^ 2 := by
      rw [hx n]; exact pow_le_pow_left₀ (norm_nonneg _) ((hP n).norm_le _) 2
    have h2 : ‖x n + h • Fd (x n) + ξ n‖ ^ 2 = ‖x n + h • Fd (x n)‖ ^ 2 + ‖ξ n‖ ^ 2 := by
      rw [norm_add_sq_real, horth n]; ring
    have h3 : ‖x n + h • Fd (x n)‖ ^ 2 =
        ‖x n‖ ^ 2 + h * (2 * ⟪Fd (x n), x n⟫) + h ^ 2 * ‖Fd (x n)‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_comm]
      ring
    have h4 : ‖Fd (x n)‖ ^ 2 ≤ L ^ 2 * ‖x n‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2
    have e1 : h * (2 * ⟪Fd (x n), x n⟫) ≤ h * (2 * (μ * ‖x n‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith [hμ (x n)]) hh
    have e2 : h ^ 2 * ‖Fd (x n)‖ ^ 2 ≤ h ^ 2 * (L ^ 2 * ‖x n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h4 (sq_nonneg h)
    rw [hq_def]
    nlinarith [hnoise n]
  by_cases hq : 0 ≤ q
  · intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc ‖x (n + 1)‖ ^ 2 ≤ q * ‖x n‖ ^ 2 := step n
        _ ≤ q * (q ^ n * ‖x 0‖ ^ 2) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * ‖x 0‖ ^ 2 := by ring
  · push Not at hq
    have hz : ∀ n, ‖x n‖ ^ 2 = 0 := by
      intro n
      have := step n
      have : 0 ≤ q * ‖x n‖ ^ 2 := (sq_nonneg _).trans this
      nlinarith [sq_nonneg ‖x n‖]
    intro n
    rw [hz n, hz 0, mul_zero]

/-- **Geometric mean-square decay** (2601.21428 Props. 5.7, 5.8): if
`0 ≤ 1 + h (2 μ + σ²) + h² L² < 1`, the DLR Euler–Maruyama iterates tend to zero in mean
square, for every choice of the orthogonal projectors (in particular independently of the
Gramian of the stochastic basis). -/
theorem dlrEulerMaruyama_meanSquare_tendsto_zero {Fd : E →L[ℝ] E} {P : ℕ → E →L[ℝ] E}
    {x ξ : ℕ → E} {h μ L σ : ℝ} (hP : ∀ n, IsOrthProj (P n))
    (hμ : ∀ y, ⟪Fd y, y⟫ ≤ μ * ‖y‖ ^ 2) (hL : ∀ y, ‖Fd y‖ ≤ L * ‖y‖) (hh : 0 ≤ h)
    (hx : ∀ n, x (n + 1) = P n (x n + h • Fd (x n) + ξ n))
    (horth : ∀ n, ⟪x n + h • Fd (x n), ξ n⟫ = 0)
    (hnoise : ∀ n, ‖ξ n‖ ^ 2 ≤ h * σ ^ 2 * ‖x n‖ ^ 2)
    (hq0 : 0 ≤ 1 + h * (2 * μ + σ ^ 2) + h ^ 2 * L ^ 2)
    (hq1 : 1 + h * (2 * μ + σ ^ 2) + h ^ 2 * L ^ 2 < 1) :
    Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 0) := by
  have hb := dlrEulerMaruyama_meanSquare_le hP hμ hL hh hx horth hnoise
  have ht : Tendsto (fun n => (1 + h * (2 * μ + σ ^ 2) + h ^ 2 * L ^ 2) ^ n * ‖x 0‖ ^ 2) atTop
      (𝓝 (0 * ‖x 0‖ ^ 2)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _
  rw [zero_mul] at ht
  exact squeeze_zero (fun n => sq_nonneg _) hb ht

/-! ### OP-SL-22: the extra term of DLR projector splitting for Euler–Maruyama -/

section ExtraTerm

variable {Lp Rp : E →L[ℝ] E}

/-- **Splitting of the stochastic tangent projector** (2601.21428 identity (21)):
`(P_U + (I - P_U) P_Y) v = P_U v + D` with the extra term `D = (I - P_U) P_Y v`.  For
`v = a Δt + b ΔW` the term `P_U v` is the Alg. 2 increment and `D` is the difference between
Alg. 3 and Alg. 2. -/
theorem tangent_apply_eq_add_extra (v : E) :
    tangent Lp Rp v = Lp v + (Rp v - Lp (Rp v)) := by
  rw [tangent_apply]; abel

/-- **Gramian-free bound of the extra term** (OP-SL-22; 2609.20292 Rem. 2.3): for commuting
orthogonal projectors `‖(I - P_U) P_Y ξ‖ ≤ ‖(I - P_U) ξ‖`.  With `ξ = b ΔW`,
`‖(I - P_U) ξ‖ ≤ ε √Δt` where `ε` bounds the normal component of the diffusion, so no smallest
singular value `γ` of the Gramian enters. -/
theorem norm_extraTerm_le (hR : IsOrthProj Rp) (hc : ∀ x, Lp (Rp x) = Rp (Lp x)) (ξ : E) :
    ‖Rp ξ - Lp (Rp ξ)‖ ≤ ‖ξ - Lp ξ‖ := by
  have : Rp ξ - Lp (Rp ξ) = Rp (ξ - Lp ξ) := by rw [map_sub, hc]
  rw [this]
  exact hR.norm_le _

/-- **Vanishing of the extra term for tangent diffusion** (2609.20292 Rem. 2.3; 2601.21428
Rem. 6.4): if `ξ ∈ range P_U` then `(I - P_U) P_Y ξ = 0`, so Alg. 3 coincides with Alg. 2. -/
theorem extraTerm_eq_zero (hc : ∀ x, Lp (Rp x) = Rp (Lp x)) {ξ : E} (hξ : Lp ξ = ξ) :
    Rp ξ - Lp (Rp ξ) = 0 := by
  rw [hc, hξ, sub_self]

/-- **Accumulation of the extra terms** (OP-SL-22, partial).  If the extra terms `Dₙ` of the
`N` steps are pairwise orthogonal (a martingale-difference property, assumed here, not proved)
and `‖Dₙ‖² ≤ Δt ε²`, then `‖∑ₙ Dₙ‖² ≤ N Δt ε² = T ε²`: the accumulated perturbation of Alg. 3
relative to Alg. 2 is `O(ε √T)`, independent of `γ`.  Without orthogonality only the trivial
non-summable bound `N √Δt ε` holds; establishing the orthogonality for the non-adapted
increments and propagating through the scheme remain open. -/
theorem norm_sum_extraTerm_le_of_orthogonal {N : ℕ} {D : ℕ → E} {dt ε : ℝ}
    (horth : ∀ i < N, ∀ j < N, i ≠ j → ⟪D i, D j⟫ = 0) (hD : ∀ n < N, ‖D n‖ ^ 2 ≤ dt * ε ^ 2) :
    ‖∑ n ∈ range N, D n‖ ^ 2 ≤ N * dt * ε ^ 2 := by
  rw [norm_sq_sum_of_orthogonal _ _ fun i hi j hj hij =>
    horth i (mem_range.1 hi) j (mem_range.1 hj) hij]
  calc ∑ n ∈ range N, ‖D n‖ ^ 2 ≤ ∑ _n ∈ range N, dt * ε ^ 2 :=
        Finset.sum_le_sum fun n hn => hD n (mem_range.1 hn)
    _ = N * dt * ε ^ 2 := by simp; ring

end ExtraTerm

/-! ### OP-SL-07: covariance bounds need cross terms -/

section Covariance

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Corrected covariance bound** (OP-SL-07, repairing 2607.27432 Lemma 4.1).  For a bilinear
second-moment map `β` with `‖β u v‖ ≤ ‖u‖ ‖v‖` (e.g. `β u v = E[u vᵀ]` on `L²(Ω; ℝᵈ)` with the
Frobenius norm, by Cauchy–Schwarz):
`‖β X X - β Y Y‖ ≤ ‖X - Y‖² + 2 ‖X - Y‖ ‖Y‖`, i.e.
`‖E XXᵀ - E YYᵀ‖_F ≤ E|X - Y|² + 2 (E|X - Y|²)^{1/2} (E|Y|²)^{1/2}`. -/
theorem norm_bilin_sub_le (β : E →ₗ[ℝ] E →ₗ[ℝ] G) (hβ : ∀ u v, ‖β u v‖ ≤ ‖u‖ * ‖v‖) (X Y : E) :
    ‖β X X - β Y Y‖ ≤ ‖X - Y‖ ^ 2 + 2 * ‖X - Y‖ * ‖Y‖ := by
  have key : β X X - β Y Y = β (X - Y) (X - Y) + β (X - Y) Y + β Y (X - Y) := by
    simp only [map_sub, LinearMap.sub_apply]; abel
  rw [key]
  calc ‖β (X - Y) (X - Y) + β (X - Y) Y + β Y (X - Y)‖
      ≤ ‖β (X - Y) (X - Y)‖ + ‖β (X - Y) Y‖ + ‖β Y (X - Y)‖ := norm_add₃_le
    _ ≤ ‖X - Y‖ * ‖X - Y‖ + ‖X - Y‖ * ‖Y‖ + ‖Y‖ * ‖X - Y‖ :=
        add_le_add (add_le_add (hβ _ _) (hβ _ _)) (hβ _ _)
    _ = _ := by ring

/-- **The corrected bound is sharp** (OP-SL-07): for `X = (1 + δ) Y` and `β = ⟪·,·⟫`
(the trace of the second moment) equality holds. -/
theorem secondMoment_bound_sharp (Y : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    |‖(1 + δ) • Y‖ ^ 2 - ‖Y‖ ^ 2| = ‖(1 + δ) • Y - Y‖ ^ 2 + 2 * ‖(1 + δ) • Y - Y‖ * ‖Y‖ := by
  have hd : (1 + δ) • Y - Y = δ • Y := by rw [add_smul, one_smul]; abel
  rw [hd, norm_smul, norm_smul, Real.norm_of_nonneg hδ, Real.norm_of_nonneg (by linarith)]
  have h0 : 0 ≤ ((1 + δ) * ‖Y‖) ^ 2 - ‖Y‖ ^ 2 := by
    have := mul_nonneg hδ (sq_nonneg ‖Y‖)
    have := mul_nonneg (mul_nonneg hδ hδ) (sq_nonneg ‖Y‖)
    nlinarith
  rw [abs_of_nonneg h0]
  ring

/-- **Counterexample to the proof step of Lemma 4.1 of 2607.27432** (OP-SL-07, Appendix B).  For
any nonzero `Y` there is no constant `C` with `|E|X|² - E|Y|²| ≤ C E|X - Y|²` for all
`X = (1 + δ) Y`, `δ > 0`: the difference of second moments is of first order in `δ`, the second
moment of the difference of second order.  So the generic step "covariance difference ≤ second
moment of the difference" used in the proof of (44) is invalid.  This does **not** refute (44)
itself: the pair `X = (1 + δ) Y` is not of the form of the lemma, and for pairs of that form the
trace version even holds with equality (`secondMoment_trace_eq_of_fixed`).  Whether the
Frobenius-norm bound (44) holds is open. -/
theorem secondMoment_gap {Y : E} (hY : Y ≠ 0) :
    ¬ ∃ C : ℝ, ∀ δ : ℝ, 0 < δ →
      |‖(1 + δ) • Y‖ ^ 2 - ‖Y‖ ^ 2| ≤ C * ‖(1 + δ) • Y - Y‖ ^ 2 := by
  rintro ⟨C, hC⟩
  set δ : ℝ := 1 / (|C| + 1) with hδ_def
  have hpos : 0 < |C| + 1 := by positivity
  have hδ : 0 < δ := by positivity
  have hδC : δ * (|C| + 1) = 1 := by rw [hδ_def]; field_simp
  have hs : 0 < ‖Y‖ ^ 2 := by positivity
  have h := hC δ hδ
  rw [secondMoment_bound_sharp Y hδ.le] at h
  have hd : (1 + δ) • Y - Y = δ • Y := by rw [add_smul, one_smul]; abel
  rw [hd, norm_smul, Real.norm_of_nonneg hδ.le] at h
  -- `h : (δ‖Y‖)² + 2 δ ‖Y‖ ‖Y‖ ≤ C (δ ‖Y‖)²`
  have hCa : C * (δ * ‖Y‖) ^ 2 ≤ |C| * (δ * ‖Y‖) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
  have hny : 0 < ‖Y‖ := norm_pos_iff.2 hY
  have : |C| * δ = 1 - δ := by linarith
  nlinarith [mul_pos hδ hny, mul_pos (mul_pos hδ hny) hny]

/-- **Trace version of (44) in the setting of Lemma 4.1** (OP-SL-07; 2607.27432 Lemma 4.1).  Let
`X̂ = Xₙ + v` be the Euler–Maruyama step and `X̂ᴰᴸᴿᴬ = Xₙ + Π v` the projector-splitting step
from a common `Xₙ` fixed by the orthogonal tangent projector `Π` (`Π Xₙ = Xₙ`).  Then the
difference of the *traces* of the second moments equals the second moment of the difference:
`E|X̂|² - E|X̂ᴰᴸᴿᴬ|² = E|X̂ - X̂ᴰᴸᴿᴬ|²`, with no cross term.  Hence the trace analogue of (44)
holds with the constant of (43), and the scalar counterexample `secondMoment_gap` does not apply
to the lemma's setting.  The full matrix (Frobenius) version of (44) involves off-diagonal cross
covariances `E[(I - Π) v (Π v)ᵀ]` that the trace does not see; it remains open. -/
theorem secondMoment_trace_eq_of_fixed {Pt : E →L[ℝ] E} (hPt : IsOrthProj Pt) {X v : E}
    (hX : Pt X = X) : ‖X + v‖ ^ 2 - ‖X + Pt v‖ ^ 2 = ‖(X + v) - (X + Pt v)‖ ^ 2 := by
  have hsplit : X + v = (X + Pt v) + (v - Pt v) := by abel
  have hfix : X + Pt v = Pt (X + v) := by rw [map_add, hX]
  have horth : ⟪X + Pt v, v - Pt v⟫ = 0 := by
    have := hPt.inner_sub_self (X + v) v
    rwa [← hfix] at this
  have hd : (X + v) - (X + Pt v) = v - Pt v := by abel
  rw [hd, hsplit, norm_add_sq_real, horth]
  ring

end Covariance

/-! ### OP-SL-06: correlation and optimal control-variate coefficient -/

/-- **Correlation lower bound** (OP-SL-06): in any real inner product space (here `L²` of the
centred QoIs) `corr(X, Y) ≥ 1 - ‖X - Y‖² / (2 ‖X‖ ‖Y‖)`. -/
theorem corr_ge {X Y : E} (hX : X ≠ 0) (hY : Y ≠ 0) :
    1 - ‖X - Y‖ ^ 2 / (2 * (‖X‖ * ‖Y‖)) ≤ ⟪X, Y⟫ / (‖X‖ * ‖Y‖) := by
  have hx : 0 < ‖X‖ := norm_pos_iff.2 hX
  have hy : 0 < ‖Y‖ := norm_pos_iff.2 hY
  have hin : ⟪X, Y⟫ = (‖X‖ ^ 2 + ‖Y‖ ^ 2 - ‖X - Y‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]; ring
  have : ⟪X, Y⟫ / (‖X‖ * ‖Y‖) = 1 - ‖X - Y‖ ^ 2 / (2 * (‖X‖ * ‖Y‖))
      + (‖X‖ - ‖Y‖) ^ 2 / (2 * (‖X‖ * ‖Y‖)) := by
    rw [hin]; field_simp; ring
  rw [this]
  have : 0 ≤ (‖X‖ - ‖Y‖) ^ 2 / (2 * (‖X‖ * ‖Y‖)) := by positivity
  linarith

/-- **Optimal control-variate coefficient** (OP-SL-06): for `α* = ⟪X, Y⟫ / ‖Y‖²`
(`= Cov_rs / Var_s`), `|α* - 1| ≤ ‖X - Y‖ / ‖Y‖`. -/
theorem abs_optCoeff_sub_one_le {X Y : E} (hY : Y ≠ 0) :
    |⟪X, Y⟫ / ‖Y‖ ^ 2 - 1| ≤ ‖X - Y‖ / ‖Y‖ := by
  have hy : 0 < ‖Y‖ := norm_pos_iff.2 hY
  have h1 : ⟪X, Y⟫ / ‖Y‖ ^ 2 - 1 = ⟪X - Y, Y⟫ / ‖Y‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]; field_simp
  rw [h1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖Y‖ ^ 2),
    div_le_div_iff₀ (by positivity) hy]
  calc |⟪X - Y, Y⟫| * ‖Y‖ ≤ ‖X - Y‖ * ‖Y‖ * ‖Y‖ :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) hy.le
    _ = ‖X - Y‖ * ‖Y‖ ^ 2 := by ring

/-- **Uniform version** (OP-SL-06): if the coarse and fine centred QoIs are `η`-close in `L²`
and both have standard deviation at least `m > 0`, then
`1 - η² / (2 m²) ≤ corr ≤ 1` and `|α* - 1| ≤ η / m`.  The bounds involve only `η` and `m`, hence
are uniform in the fine rank `r`. -/
theorem corr_optCoeff_uniform {X Y : E} {η m : ℝ} (hm : 0 < m) (hX : m ≤ ‖X‖) (hY : m ≤ ‖Y‖)
    (hη : ‖X - Y‖ ≤ η) :
    1 - η ^ 2 / (2 * m ^ 2) ≤ ⟪X, Y⟫ / (‖X‖ * ‖Y‖) ∧ ⟪X, Y⟫ / (‖X‖ * ‖Y‖) ≤ 1 ∧
      |⟪X, Y⟫ / ‖Y‖ ^ 2 - 1| ≤ η / m := by
  have hX0 : X ≠ 0 := norm_pos_iff.1 (hm.trans_le hX)
  have hY0 : Y ≠ 0 := norm_pos_iff.1 (hm.trans_le hY)
  have hy : 0 < ‖Y‖ := hm.trans_le hY
  refine ⟨(sub_le_sub_left ?_ 1).trans (corr_ge hX0 hY0), ?_, ?_⟩
  · have h1 : ‖X - Y‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hη 2
    have h2 : 2 * m ^ 2 ≤ 2 * (‖X‖ * ‖Y‖) := by nlinarith
    exact div_le_div₀ (by nlinarith [norm_nonneg (X - Y)]) h1 (by positivity) h2
  · exact (le_abs_self _).trans (abs_real_inner_div_norm_mul_norm_le_one X Y)
  · refine (abs_optCoeff_sub_one_le hY0).trans ?_
    exact div_le_div₀ ((norm_nonneg _).trans hη) hη hm hY

/-- **Correlation and optimal coefficient tend to one** (OP-SL-06; observed in 2501.06125
Table 1): if the `L²` distance `ηₛ` between coarse and fine centred QoIs tends to zero (as
guaranteed by `bug_expected_error_le` for a Lipschitz QoI when the coarse-rank normal component
`ε(s) → 0`) and the standard deviations stay above `m > 0`, then `corr → 1` and `α* → 1`; the
rate `1 - corr ≤ ηₛ² / (2m²)` holds uniformly over all fine ranks `r ∈ ι`. -/
theorem tendsto_corr_optCoeff {ι : Type*} {X : ι → ℕ → E} {Y : ℕ → E} {η : ℕ → ℝ} {m : ℝ}
    (hm : 0 < m) (hX : ∀ r s, m ≤ ‖X r s‖) (hY : ∀ s, m ≤ ‖Y s‖)
    (hη : ∀ r s, ‖X r s - Y s‖ ≤ η s) (hη0 : Tendsto η atTop (𝓝 0)) (r : ι) :
    Tendsto (fun s => ⟪X r s, Y s⟫ / (‖X r s‖ * ‖Y s‖)) atTop (𝓝 1) ∧
      Tendsto (fun s => ⟪X r s, Y s⟫ / ‖Y s‖ ^ 2) atTop (𝓝 1) := by
  have hb := fun s => corr_optCoeff_uniform hm (hX r s) (hY s) (hη r s)
  constructor
  · have hlow : Tendsto (fun s => 1 - η s ^ 2 / (2 * m ^ 2)) atTop (𝓝 1) := by
      have : Tendsto (fun s => 1 - η s ^ 2 / (2 * m ^ 2)) atTop (𝓝 (1 - 0 ^ 2 / (2 * m ^ 2))) :=
        tendsto_const_nhds.sub ((hη0.pow 2).div_const _)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun s => (hb s).1) (fun s => (hb s).2.1)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have : Tendsto (fun s => η s / m) atTop (𝓝 0) := by simpa using hη0.div_const m
    exact squeeze_zero (fun _ => norm_nonneg _) (fun s => by
      rw [Real.norm_eq_abs]; exact (hb s).2.2) this

/-! ### OP-SL-08: pseudo-inverse Gramians -/

section PseudoInverse

/-- **The tangent projector fixes the iterate** (OP-SL-08): if `R X = X` (the iterate lies in the
range of the stochastic projector, e.g. `Xₙ ∈ ℝᵈ ⊗ span Ỹₙ`), then `tangent L R X = X`; neither
commutation nor exact rank is needed. -/
theorem tangent_apply_eq_self_of_right {Lp Rp : E →L[ℝ] E} {X : E} (hX : Rp X = X) :
    tangent Lp Rp X = X := by
  rw [tangent_apply, hX]; abel

/-- The span of finitely many (possibly linearly dependent) vectors is finite-dimensional, hence
complete, hence admits an orthogonal projection. -/
theorem hasOrthogonalProjection_span {k : ℕ} (y : Fin k → E) :
    (Submodule.span ℝ (Set.range y)).HasOrthogonalProjection := by
  have := FiniteDimensional.span_of_finite ℝ (Set.finite_range y)
  infer_instance

attribute [local instance] hasOrthogonalProjection_span

/-- **OP-SL-08: second moments without exact rank** (ingredient of the repair of 2601.21428
Thm 5.4 / def. (51)).  Let `Rₙ` be the orthogonal projector onto the span of an *arbitrary*
finite family `Ỹₙ` (rank `≤ k`, Gramian possibly singular, i.e. the pseudo-inverse projector),
commuting with the orthogonal projectors `Lₙ = P_U ⊗ I`.  Then the stochastic tangent projector
`P_U + (I - P_U) P_Ỹ` is an orthogonal projector and the second-moment bound of
`staggeredDLR_second_moment` holds verbatim, without the non-degenerate-noise (ellipticity)
assumption of Prop. 5.2.  This is only the projector / second-moment part: the strong error
bound of Thm 5.3 / Thm 5.4 (`E max |Xₙᴱᴹ - Xₙ|²`) with `ε` taken over rank-`≤ k` processes is
not formalised here. -/
theorem pinvStaggered_second_moment {k : ℕ} {K : ℝ} (hK : 0 ≤ K) {X ξ : ℕ → E}
    {Lp : ℕ → E →L[ℝ] E} {Yt : ℕ → Fin k → E} {a : E → E} {dt : ℝ} (hdt : 0 ≤ dt)
    (hdt1 : dt ≤ 1) (hL : ∀ n, IsOrthProj (Lp n))
    (hc : ∀ n x, Lp n ((Submodule.span ℝ (Set.range (Yt n))).starProjection x) =
      (Submodule.span ℝ (Set.range (Yt n))).starProjection (Lp n x))
    (ha : ∀ x, ‖a x‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2))
    (h1 : ∀ n, ⟪X n, tangent (Lp n) (Submodule.span ℝ (Set.range (Yt n))).starProjection
      (ξ n)⟫ = 0)
    (h2 : ∀ n, ⟪tangent (Lp n) (Submodule.span ℝ (Set.range (Yt n))).starProjection (a (X n)),
      tangent (Lp n) (Submodule.span ℝ (Set.range (Yt n))).starProjection (ξ n)⟫ = 0)
    (hξ : ∀ n, ‖tangent (Lp n) (Submodule.span ℝ (Set.range (Yt n))).starProjection (ξ n)‖ ^ 2
      ≤ dt * K * (1 + ‖X n‖ ^ 2))
    (hX : ∀ n, X (n + 1) = X n +
      tangent (Lp n) (Submodule.span ℝ (Set.range (Yt n))).starProjection (dt • a (X n) + ξ n))
    (n : ℕ) :
    ‖X n‖ ^ 2 ≤ Real.exp ((1 + 3 * K) * (n * dt)) * (‖X 0‖ ^ 2 + (1 + 3 * K) * (n * dt)) :=
  tangent_staggered_second_moment hK hdt hdt1 hL
    (fun _ => isOrthProj_starProjection _) hc ha h1 h2 hξ hX n

/-- The iterate is fixed by the pseudo-inverse tangent projector whenever it lies in the span of
the stochastic basis, `Xₙ ∈ span Ỹₙ` (the rank-`≤ k` condition of the repaired def. (51)). -/
theorem pinvTangent_apply_eq_self {k : ℕ} (Lp : E →L[ℝ] E) (Yt : Fin k → E) {X : E}
    (hX : X ∈ Submodule.span ℝ (Set.range Yt)) :
    tangent Lp (Submodule.span ℝ (Set.range Yt)).starProjection X = X :=
  tangent_apply_eq_self_of_right (Submodule.starProjection_eq_self_iff.mpr hX)

end PseudoInverse

/-! ### Error propagation for the low-rank Fokker–Planck dynamics (1803.00499 Thm 3) -/

/-- **Integral Grönwall inequality with variable rate** (1803.00499 Theorem 3, the step "and
thus by Grönwall's inequality").  If a continuous error `e` satisfies
`e(t) ≤ e₀ + c t + ∫₀ᵗ γ e` on `[0, T]` with a continuous rate `γ ≥ 0` and `c ≥ 0`, then
`e(t) ≤ (e₀ + c t) exp(∫₀ᵗ γ)`.  In 1803.00499, `e = E(t)` is the Hilbert–Schmidt error of the
second moments, `c = ε²` bounds the normal part of the diffusion and `γ` is the consistency rate
of assumption 2; the integral inequality itself is the (measure-theoretic) first half of the
proof and is taken as hypothesis here.  No sign condition on `e₀` is needed. -/
theorem integral_gronwall_le {e γ : ℝ → ℝ} {e₀ c T : ℝ} (he : Continuous e) (hγ : Continuous γ)
    (hγ0 : ∀ s, 0 ≤ γ s) (hc : 0 ≤ c)
    (hint : ∀ t ∈ Set.Icc 0 T, e t ≤ e₀ + c * t + ∫ s in (0 : ℝ)..t, γ s * e s) :
    ∀ t ∈ Set.Icc 0 T, e t ≤ (e₀ + c * t) * Real.exp (∫ s in (0 : ℝ)..t, γ s) := by
  intro t ht
  set Φ : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, γ s * e s with hΦ
  set Γ : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, γ s with hΓ
  have dΦ : ∀ u, HasDerivAt Φ (γ u * e u) u := fun u =>
    ((hγ.mul he).integral_hasStrictDerivAt 0 u).hasDerivAt
  have dΓ : ∀ u, HasDerivAt Γ (γ u) u := fun u => (hγ.integral_hasStrictDerivAt 0 u).hasDerivAt
  set g : ℝ → ℝ := fun u => (Φ u + e₀ + c * t) * Real.exp (-Γ u) with hg
  have dg : ∀ u, HasDerivAt g (γ u * e u * Real.exp (-Γ u)
      + (Φ u + e₀ + c * t) * (Real.exp (-Γ u) * -γ u)) u := fun u =>
    (((dΦ u).add_const e₀).add_const (c * t)).mul (dΓ u).neg.exp
  have hanti : AntitoneOn g (Set.Icc 0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
      (fun u _ => (dg u).continuousAt.continuousWithinAt) (fun u _ => (dg u).hasDerivWithinAt)
      fun u hu => ?_
    rw [interior_Icc] at hu
    have hu' : u ∈ Set.Icc 0 T := ⟨hu.1.le, hu.2.le.trans ht.2⟩
    have h1 := hint u hu'
    have h2 : c * u ≤ c * t := mul_le_mul_of_nonneg_left hu.2.le hc
    have h3 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.exp_pos (-Γ u)).le (hγ0 u))
      (show e u - (Φ u + e₀ + c * t) ≤ 0 by simp only [hΦ]; linarith)
    calc _ = Real.exp (-Γ u) * γ u * (e u - (Φ u + e₀ + c * t)) := by ring
      _ ≤ 0 := h3
  have h0 : g t ≤ g 0 :=
    hanti (Set.left_mem_Icc.2 ht.1) (Set.right_mem_Icc.2 ht.1) ht.1
  have hg0 : g 0 = e₀ + c * t := by simp [hg, hΦ, hΓ]
  have het : e t * Real.exp (-Γ t) ≤ g t :=
    mul_le_mul_of_nonneg_right (by have := hint t ht; simp only [hΦ]; linarith)
      (Real.exp_pos _).le
  have key : e t * Real.exp (-Γ t) ≤ e₀ + c * t := by linarith
  have := mul_le_mul_of_nonneg_right key (Real.exp_pos (Γ t)).le
  rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this

/-! ### Non-degeneracy examples -/

/-- The hypotheses of `staggeredDLR_second_moment` are satisfiable with nonzero noise: in `ℝ²`,
`Π = id`, `a = 0`, `X₀ = e₁` and `ξₙ = √dt e₂`-type increments orthogonal to the state.  Here we
check the one-step identity `‖e₁ + e₂‖² = ‖e₁‖² + ‖e₂‖²` behind it. -/
example : ‖(EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2
    = ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2
      + ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
  rw [norm_add_sq_real]
  simp [EuclideanSpace.inner_single_left]

/-- Non-vacuity of `staggered_step_le` with genuinely nonzero noise: in `ℝ²` with `Π = 1`,
`a = 0`, `K = 1`, `dt = 1`, state `X = e₀` and noise `ξ = e₁ ⊥ X` (`‖ξ‖² = 1 ≤ dt K (1 + ‖X‖²)`),
all hypotheses hold and the step `X' = e₀ + e₁` satisfies the bound. -/
example : ‖(EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2
    ≤ (1 + (1 + 3 * 1) * 1) * ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2
      + (1 + 3 * 1) * 1 :=
  staggered_step_le (K := 1) (dt := 1) zero_le_one le_rfl IsOrthProj.one (a := fun _ => 0)
    (X := EuclideanSpace.single 0 1) (ξ := EuclideanSpace.single 1 1)
    (fun x => by simp only [norm_zero]; nlinarith [sq_nonneg ‖x‖])
    (by simp [EuclideanSpace.inner_single_left]) (by simp)
    (by simp) (by simp)

/-- Non-vacuity of `secondMoment_gap`: it applies to `Y = 1 ∈ ℝ`. -/
example : ¬ ∃ C : ℝ, ∀ δ : ℝ, 0 < δ →
    |‖(1 + δ) • (1 : ℝ)‖ ^ 2 - ‖(1 : ℝ)‖ ^ 2| ≤ C * ‖(1 + δ) • (1 : ℝ) - 1‖ ^ 2 :=
  secondMoment_gap one_ne_zero

/-- Non-vacuity of `corr_ge`: for `X = 2`, `Y = 1` in `ℝ` the correlation is `1` and the bound
gives `1 - 1/4`. -/
example : 1 - ‖(2 : ℝ) - 1‖ ^ 2 / (2 * (‖(2 : ℝ)‖ * ‖(1 : ℝ)‖)) ≤
    ⟪(2 : ℝ), 1⟫ / (‖(2 : ℝ)‖ * ‖(1 : ℝ)‖) :=
  corr_ge two_ne_zero one_ne_zero

/-- Non-vacuity of `integral_gronwall_le`: `e(t) = t` with `γ = 0`, `c = 1` satisfies the
integral inequality with equality. -/
example (T : ℝ) : ∀ t ∈ Set.Icc 0 T,
    id t ≤ (0 + 1 * t) * Real.exp (∫ _ in (0 : ℝ)..t, (0 : ℝ)) :=
  integral_gronwall_le (e := id) (γ := fun _ => 0) continuous_id continuous_const
    (fun _ => le_rfl) zero_le_one (fun t _ => by simp)

end LeanDLRA.MeanSquare
