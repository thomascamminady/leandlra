import LeanDLRA.Analysis.Defs
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.HighOrder.RungeKuttaBUG

/-!
# Randomized low-rank Runge–Kutta methods (arXiv 2409.06384, Lam–Ceruti–Kressner)

This module proves the error analysis of randomized low-rank time integrators in `L^q`, with all
randomness explicit: a randomized low-rank map is `R(ξ, ·)` with a sketch `ξ` on a probability
space, sketches of different steps and stages are independent (`iIndepFun`), and the moment
assumption (7), `‖R(ξ, Z) - Z‖_{L^q} ≤ C_N dist(Z, S)` for fixed `Z`, is transferred to random
inputs independent of the sketch by Tonelli on the product law (`eLpNorm_indep_le`). On this basis
it proves Theorem 3 and Corollary 4 (idealized randomized projection method, `thm3`, `cor4`),
Theorem 11 and the local error bound of the randomized low-rank Runge–Kutta method (`thm11`,
`rk_step_error`, `rrk_local`, `rrk_global`, `rrk_refined`), Theorem 5 in both cases `b₂ ≠ 0` and `b₂
= 0` with tail bounds (`thm5`, `thm5_b2_zero`) and its RK4 instance of order `2` (`thm5_rk4`), the
Section 2.2 implication from a small normal component to flow approximability (`sec22_defect`,
`sec22_assumption3`, `sec22_matrix`), Example 1 (`Example1.exact_flow`, `Example1.dlra_flow`,
`Example1.approx_error` `≤ 1.24 · 10⁻¹⁰`, `Example1.dlra_error` `≥ 0.008`,
`Example1.normal_component`), Lemmas 7 and 8 (`lemma7`, `lemma8`), Lemma 9 and Theorem 10 for the
stage-oversampled RK4 method (`lemma9`, `thm10`, `thm10_tail`); `example`s show that the hypotheses
of `thm3`, `thm5` and `thm10` are consistent. Core definitions used: `ODESolution`, `distLR`,
`lowRankSet`, `tangentProj`, `EckartYoung.rank_add_le`; local definitions: `idealIter`, the explicit
Runge–Kutta stages `rkK`/`rkZ` with stage maps and the iteration `rrkIter` (`isGalerkinRKStep_rk`
shows that with identity stage maps they form a full step in the sense of the core
`RungeKuttaBUG.IsGalerkinRKStep`), the RK4 tableau `rk4a`/`rk4b` and the constants `thm5K`, `rk4K`.
Differences from the paper: Theorem 2 (the moment bound for Gaussian generalized Nyström, which
relies on a Gaussian estimate from the literature) is not formalized, so (7) is a hypothesis, for
any `1 ≤ q < ∞` and any set `S` (`S = {rank ≤ r}` for matrices); joint measurability of the
randomized map is assumed; Assumptions 3 and (21) are imposed on rank `≤ r` (resp. `≤ k`) rather
than on the manifolds `M_r`, `M_k`, because iterates may lose rank (equivalent by density, not
formalized); Assumption 2 is not used: the classical RK order `τ` and the stage orders are
hypotheses on `S`, and the nodes `c_j` are assumed in `[0, 1]`; the existence of the projected
(DLRA) flow in Section 2.2 is a hypothesis, and in Example 1 the DLRA solution is exhibited but its
uniqueness is not proved; Remark 6 (localized assumptions) is not formalized. No claim of the paper
was found to be false.
-/

open Set Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix ENNReal

namespace LeanDLRA.Literature.P2409_06384

section Prob

variable {Ω K E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace K] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Freezing an independent argument (auxiliary; arXiv 2409.06384, proof of Theorem 3): if `ξ` and
`X` are independent and `∫ f(ξ, z) ≤ g(z)` for every fixed `z`, then `∫ f(ξ, X) ≤ ∫ g(X)` (Tonelli
on the product law). -/
theorem lintegral_indep_le {ξ : Ω → K} {β : Type*} [MeasurableSpace β] {X : Ω → β}
    (hξ : Measurable ξ) (hX : Measurable X) (hind : IndepFun ξ X P) {f : K → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) {g : β → ℝ≥0∞}
    (hfg : ∀ z, ∫⁻ ω, f (ξ ω) z ∂P ≤ g z) :
    ∫⁻ ω, f (ξ ω) (X ω) ∂P ≤ ∫⁻ ω, g (X ω) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hξ.aemeasurable hX.aemeasurable).1 hind
  calc ∫⁻ ω, f (ξ ω) (X ω) ∂P
        = ∫⁻ p, Function.uncurry f p ∂(P.map (fun ω => (ξ ω, X ω))) := by
          rw [lintegral_map hf (hξ.prodMk hX)]; rfl
    _ = ∫⁻ p, Function.uncurry f p ∂((P.map ξ).prod (P.map X)) := by rw [hmap]
    _ = ∫⁻ z, ∫⁻ k, f k z ∂(P.map ξ) ∂(P.map X) := lintegral_prod_symm' _ hf
    _ = ∫⁻ z, ∫⁻ ω, f (ξ ω) z ∂P ∂(P.map X) := by
          congr 1; funext z; rw [lintegral_map hf.of_uncurry_right hξ]
    _ ≤ ∫⁻ z, g z ∂(P.map X) := lintegral_mono hfg
    _ ≤ ∫⁻ ω, g (X ω) ∂P := lintegral_map_le g hX.aemeasurable

/-- The moment assumption (7) with a random input (auxiliary; arXiv 2409.06384, Step 1 of the proof
of Theorem 3): if `‖R(ξ, z) - z‖_{L^q} ≤ d(z)` for every fixed `z` and `X` is independent of the
sketch `ξ`, then `‖R(ξ, X) - X‖_{L^q} ≤ ‖d(X)‖_{L^q}`. -/
theorem eLpNorm_indep_le {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) {R : K → E → E}
    (hR : Measurable (Function.uncurry R)) {ξ : Ω → K} {X : Ω → E} (hξ : Measurable ξ)
    (hX : Measurable X) (hind : IndepFun ξ X P) {d : E → ℝ}
    (hmom : ∀ z, eLpNorm (fun ω => R (ξ ω) z - z) q P ≤ ENNReal.ofReal (d z)) :
    eLpNorm (fun ω => R (ξ ω) (X ω) - X ω) q P ≤ eLpNorm (fun ω => d (X ω)) q P := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hm1 : Measurable (fun ω => R (ξ ω) (X ω) - X ω) :=
    (hR.comp (hξ.prodMk hX)).sub hX
  by_cases hd : AEStronglyMeasurable (fun ω => d (X ω)) P
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hm1.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hd]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine lintegral_indep_le (f := fun k z => ‖R k z - z‖ₑ ^ q.toReal)
      (g := fun z => ‖d z‖ₑ ^ q.toReal) hξ hX hind ?_ ?_
    · exact ((hR.sub measurable_snd).enorm).pow_const _
    · intro z
      have hmz : Measurable (fun ω => R (ξ ω) z - z) :=
        (hR.comp (hξ.prodMk measurable_const)).sub measurable_const
      have h1 := hmom z
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hmz.aestronglyMeasurable] at h1
      have h2 := ENNReal.rpow_le_rpow h1 hqr.le
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hqr.ne', ENNReal.rpow_one] at h2
      refine h2.trans (ENNReal.rpow_le_rpow ?_ hqr.le)
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · rw [eLpNorm_of_not_aestronglyMeasurable hd]
    exact le_top

omit [IsProbabilityMeasure P] in
/-- A sketch is independent of everything computed from the other sketches (auxiliary; arXiv
2409.06384, independence of the sketches across stages and steps). -/
theorem indepFun_of_measurable_iSup {ι : Type*} {ξ : ι → Ω → K} (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) {S : Set ι} {i : ι} (hi : i ∉ S) {β : Type*} [mβ : MeasurableSpace β]
    {X : Ω → β} (hX : Measurable[⨆ j ∈ S, MeasurableSpace.comap (ξ j) inferInstance] X) :
    IndepFun (ξ i) X P := by
  rw [IndepFun_iff_Indep]
  have h := indep_iSup_of_disjoint (m := fun j => MeasurableSpace.comap (ξ j) inferInstance)
    (fun j => (hξ j).comap_le) hind.iIndep (S := {i}) (T := S)
    (Set.disjoint_singleton_left.2 hi)
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) hX.comap_le
  exact le_iSup₂ (f := fun j (_ : j ∈ ({i} : Set ι)) => MeasurableSpace.comap (ξ j) inferInstance)
    i rfl

end Prob


section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Time shift of a solution of an autonomous ODE (auxiliary; arXiv 2409.06384). -/
theorem odeSolution_shift {F : E → E} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ => F) y a b) (c : ℝ) :
    ODESolution (fun _ => F) (fun t => y (c + t)) (a - c) (b - c) where
  cont := hy.cont.comp (continuous_const.add continuous_id).continuousOn fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  deriv t ht := by
    have h1 := hy.deriv (c + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 : HasDerivWithinAt (fun t : ℝ => c + t) 1 (Ici t) t :=
      (hasDerivWithinAt_id t _).const_add c
    have h3 := h1.scomp t h2 (fun s hs => by simp only [Set.mem_Ici] at hs ⊢; linarith)
    simpa [Function.comp_def] using h3

/-- Stability of the exact flow, `‖Φ^t X - Φ^t Y‖ ≤ e^{Lt} ‖X - Y‖` (auxiliary; arXiv 2409.06384,
proof of Theorem 3), from `ODESolution.norm_sub_le_exp`. -/
theorem flow_lipschitz {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {t : ℝ} (ht : t ∈ Icc 0 h₀) (X Y : E) :
    ‖Φ t X - Φ t Y‖ ≤ Real.exp (L * t) * ‖X - Y‖ := by
  have := (hΦ X).norm_sub_le_exp (L := L) (fun _ x y => hF x y) hL (hΦ Y) t ht
  simpa [hΦ0] using this

/-- The exact solution on the grid is generated by the flow, `A(t₀ + h) = Φ^h(A(t₀))` (auxiliary;
arXiv 2409.06384), by uniqueness for Lipschitz `F`. -/
theorem flow_step {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {T : ℝ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A 0 T)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hT : t₀ + h ≤ T) :
    A (t₀ + h) = Φ h (A t₀) := by
  have hy : ODESolution (fun _ => F) (fun t => A (t₀ + t)) 0 h := by
    have := odeSolution_shift (hA.mono ht₀ hT) t₀
    simpa using this
  have hz : ODESolution (fun _ => F) (fun t => Φ t (A t₀)) 0 h := (hΦ _).mono le_rfl hh₀
  have := hy.eqOn hz (L := L) (fun _ x y => hF x y) hL (by simp [hΦ0])
  exact this ⟨hh, le_rfl⟩

end Flow

section Fan

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [NormedAddCommGroup E]

/-- Lady Windermere's fan in `L^q` (auxiliary; arXiv 2409.06384, Steps 2–4 of the proof of Theorem
3): `e_N ≤ κ^N (e_0 + N ℓ)` for local errors `≤ ℓ` in `L^q` and a `κ`-Lipschitz one-step flow, by
Minkowski's inequality. -/
theorem lq_fan {q : ℝ≥0∞} (hq : 1 ≤ q) {Φh : E → E} {κ : ℝ} (hκ : 1 ≤ κ)
    (hΦ : ∀ x y, ‖Φh x - Φh y‖ ≤ κ * ‖x - y‖) {N : ℕ} {a : ℕ → E}
    (ha : ∀ n < N, a (n + 1) = Φh (a n))
    {Y : ℕ → Ω → E} (hYm : ∀ n, AEStronglyMeasurable (Y n) P) {ℓ : ℝ≥0∞}
    (hloc : ∀ n < N, eLpNorm (fun ω => Y (n + 1) ω - Φh (Y n ω)) q P ≤ ℓ) :
    ∀ n ≤ N, eLpNorm (fun ω => Y n ω - a n) q P ≤
      ENNReal.ofReal κ ^ n * (eLpNorm (fun ω => Y 0 ω - a 0) q P + n * ℓ) := by
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hc : Continuous Φh := by
    have : LipschitzWith ⟨κ, hκ0⟩ Φh := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact hΦ x y
    exact this.continuous
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    have hsplit : (fun ω => Y (n + 1) ω - a (n + 1)) =
        (fun ω => Y (n + 1) ω - Φh (Y n ω)) + (fun ω => Φh (Y n ω) - Φh (a n)) := by
      funext ω; simp [ha n (by omega)]
    have hm1 : AEStronglyMeasurable (fun ω => Y (n + 1) ω - Φh (Y n ω)) P :=
      (hYm (n + 1)).sub (hc.comp_aestronglyMeasurable (hYm n))
    have hm2 : AEStronglyMeasurable (fun ω => Φh (Y n ω) - Φh (a n)) P :=
      (hc.comp_aestronglyMeasurable (hYm n)).sub aestronglyMeasurable_const
    have h2 : eLpNorm (fun ω => Φh (Y n ω) - Φh (a n)) q P ≤
        ENNReal.ofReal κ * eLpNorm (fun ω => Y n ω - a n) q P :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm2 (Eventually.of_forall fun ω => hΦ _ _) q
    have hK1 : 1 ≤ ENNReal.ofReal κ := by simpa using ENNReal.ofReal_le_ofReal hκ
    rw [hsplit]
    calc eLpNorm ((fun ω => Y (n + 1) ω - Φh (Y n ω)) + (fun ω => Φh (Y n ω) - Φh (a n))) q P
        ≤ ℓ + ENNReal.ofReal κ * eLpNorm (fun ω => Y n ω - a n) q P :=
          (eLpNorm_add_le hq).trans (add_le_add (hloc n (by omega)) h2)
      _ ≤ ℓ + ENNReal.ofReal κ *
            (ENNReal.ofReal κ ^ n * (eLpNorm (fun ω => Y 0 ω - a 0) q P + n * ℓ)) := by
          gcongr
      _ ≤ ENNReal.ofReal κ ^ (n + 1) *
            (eLpNorm (fun ω => Y 0 ω - a 0) q P + ((n + 1 : ℕ) : ℝ≥0∞) * ℓ) := by
          have hpow : 1 ≤ ENNReal.ofReal κ ^ (n + 1) := one_le_pow₀ hK1
          rw [← mul_assoc, ← pow_succ']
          push_cast
          rw [mul_add, mul_add, add_mul, one_mul, mul_add]
          calc ℓ + (ENNReal.ofReal κ ^ (n + 1) * eLpNorm (fun ω => Y 0 ω - a 0) q P +
                ENNReal.ofReal κ ^ (n + 1) * (↑n * ℓ))
              ≤ ENNReal.ofReal κ ^ (n + 1) * ℓ + (ENNReal.ofReal κ ^ (n + 1) *
                eLpNorm (fun ω => Y 0 ω - a 0) q P + ENNReal.ofReal κ ^ (n + 1) * (↑n * ℓ)) :=
                add_le_add (le_mul_of_one_le_left zero_le hpow) le_rfl
            _ = _ := by ring

/-- Markov's inequality in the form of Corollary 4 of arXiv 2409.06384: `‖X‖_{L^q} ≤ c` with `c > 0`
gives `P(‖X‖ ≥ η c) ≤ η^{-q}` for every `η > 0`. -/
theorem markov_tail {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) {X : Ω → E} {c : ℝ} (hc : 0 < c)
    (hX : eLpNorm X q P ≤ ENNReal.ofReal c) {η : ℝ} (hη : 0 < η) :
    P {ω | η * c ≤ ‖X ω‖} ≤ ENNReal.ofReal (η ^ (-q.toReal)) := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hηc : 0 < η * c := mul_pos hη hc
  have hset : {ω | η * c ≤ ‖X ω‖} = {ω | ENNReal.ofReal (η * c) ≤ ‖X ω‖ₑ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← ofReal_norm]
    rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  rw [hset]
  refine (meas_ge_le_mul_pow_eLpNorm_enorm P hq0 hqt (by simpa using hηc)
    (by simp)).trans ?_
  calc (ENNReal.ofReal (η * c))⁻¹ ^ q.toReal * eLpNorm X q P ^ q.toReal
      ≤ (ENNReal.ofReal (η * c))⁻¹ ^ q.toReal * ENNReal.ofReal c ^ q.toReal := by
        gcongr
    _ = ENNReal.ofReal (η ^ (-q.toReal)) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hqr.le, ← ENNReal.ofReal_inv_of_pos hηc,
          ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hqr.le,
          Real.rpow_neg hη.le, ← Real.inv_rpow hη.le]
        congr 2
        field_simp

end Fan


section Thm3

variable {Ω K E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- A pointwise bound by a constant bounds the `L^q` norm on a probability space (auxiliary; arXiv
2409.06384). -/
theorem eLpNorm_le_ofReal {F : Type*} [NormedAddCommGroup F] {q : ℝ≥0∞} (hq0 : q ≠ 0)
    {f : Ω → F} (hf : AEStronglyMeasurable f P) {c : ℝ} (hc : 0 ≤ c) (h : ∀ ω, ‖f ω‖ ≤ c) :
    eLpNorm f q P ≤ ENNReal.ofReal c := by
  calc eLpNorm f q P ≤ eLpNorm (fun _ : Ω => c) q P := eLpNorm_mono_real hf h
    _ = ENNReal.ofReal c := by
        rw [eLpNorm_const c hq0 (IsProbabilityMeasure.ne_zero P), measure_univ, ENNReal.one_rpow,
          mul_one, Real.enorm_eq_ofReal hc]

/-- The idealized randomized projection method of arXiv 2409.06384, Sec. 2.4: `Y₀ = 𝒩₀(A₀)`,
`Y_{i+1} = 𝒩_{i+1}(Φ^h(Y_i))`, where `𝒩_i = R (ξ i ω)` is the randomized low-rank approximation
drawn with the `i`-th sketch `ξ i`. -/
noncomputable def idealIter (R : K → E → E) (Φh : E → E) (ξ : ℕ → Ω → K) (A₀ : E) :
    ℕ → Ω → E
  | 0 => fun ω => R (ξ 0 ω) A₀
  | n + 1 => fun ω => R (ξ (n + 1) ω) (Φh (idealIter R Φh ξ A₀ n ω))

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] in
/-- The `n`-th iterate of the idealized method is measurable with respect to the sketches `ξ_0, …,
ξ_n` (auxiliary; arXiv 2409.06384). -/
theorem measurable_idealIter {R : K → E → E} (hR : Measurable (Function.uncurry R))
    {Φh : E → E} (hΦ : Measurable Φh) {ξ : ℕ → Ω → K} (A₀ : E)
    (n : ℕ) : Measurable[⨆ j ∈ {j : ℕ | j ≤ n}, MeasurableSpace.comap (ξ j) inferInstance]
      (idealIter R Φh ξ A₀ n) := by
  have hξ' : ∀ n j, j ≤ n →
      Measurable[⨆ j ∈ {j : ℕ | j ≤ n}, MeasurableSpace.comap (ξ j) inferInstance] (ξ j) :=
    fun n j hj => Measurable.of_comap_le (le_iSup₂
      (f := fun j (_ : j ∈ {j : ℕ | j ≤ n}) => MeasurableSpace.comap (ξ j) inferInstance) j hj)
  induction n with
  | zero => exact hR.comp ((hξ' 0 0 le_rfl).prodMk measurable_const)
  | succ n ih =>
    have hmono : (⨆ j ∈ {j : ℕ | j ≤ n}, MeasurableSpace.comap (ξ j) inferInstance) ≤
        ⨆ j ∈ {j : ℕ | j ≤ n + 1}, MeasurableSpace.comap (ξ j) inferInstance :=
      iSup₂_le fun j hj => le_iSup₂
        (f := fun j (_ : j ∈ {j : ℕ | j ≤ n + 1}) => MeasurableSpace.comap (ξ j) inferInstance)
        j (show j ≤ n + 1 by have : j ≤ n := hj; omega)
    exact hR.comp ((hξ' (n + 1) (n + 1) le_rfl).prodMk (hΦ.comp (ih.mono hmono le_rfl)))

/-- **Theorem 3 of arXiv 2409.06384** (idealized randomized projection method). Let `F` be
`L`-Lipschitz (Assumption 1) with exact flow `Φ` on `[0, h₀]`, and let the flow be low-rank
approximable on a set `S`: `dist(Φ^h(Y), S) ≤ C_M h ε` for `Y ∈ S` and `0 < h ≤ h₀` (Assumption 3,
eq. (6)); let `dist(A₀, S) ≤ δ`. Let the randomized maps `𝒩_i = R(ξ_i, ·)` take values in `S`, use
independent sketches `ξ_i`, and satisfy the moment assumption (7): `‖𝒩_i(Z) - Z‖_{L^q} ≤ C_N dist(Z,
S)` for every fixed `Z`. Then `Y₀ = 𝒩₀(A₀)`, `Y_{i+1} = 𝒩_{i+1}(Φ^h(Y_i))` satisfy, for `0 < h ≤ h₀`
and `N h ≤ T`, `‖Y_N - A(N h)‖_{L^q} ≤ C (δ + ε)` with the explicit `C = C_N e^{LT} max(1, C_M T)`.

Differences from the paper: the paper takes `𝒩_i` to be generalized Nyström with Gaussian sketches,
for which (7) is its Theorem 2 (`C_N = 1 + 2√((1+r+p)(1+r))`, `q = min(p, ℓ)`); Theorem 2 is not
formalized, so (7) is a hypothesis, for any `1 ≤ q < ∞`, any measurable sketch space and any set `S`
(for matrices `S = {rank ≤ r}`, where `dist(·, S) = distLR r`). Joint measurability of `(k, Z) ↦ R k
Z` is assumed. Assumption 3 is required on `S` (rank `≤ r`) rather than on `M_r` (rank exactly `r`)
since the iterates can have rank `< r`; the two agree by density when `r ≤ min(m, n)` (not
formalized). -/
theorem thm3 {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {S : Set E} {C_M ε : ℝ} (hCM : 0 ≤ C_M) (hε : 0 ≤ ε)
    (happrox : ∀ Y ∈ S, ∀ h ∈ Ioc 0 h₀, Metric.infDist (Φ h Y) S ≤ C_M * h * ε)
    {T : ℝ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A 0 T) {δ : ℝ}
    (hδ : Metric.infDist (A 0) S ≤ δ)
    {R : K → E → E} (hR : Measurable (Function.uncurry R)) (hRS : ∀ k z, R k z ∈ S)
    {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ → Ω → K} (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom : ∀ i z, eLpNorm (fun ω => R (ξ i ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z S))
    {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) {N : ℕ} (hN : N * h ≤ T) :
    eLpNorm (fun ω => idealIter R (Φ h) ξ (A 0) N ω - A (N * h)) q P ≤
      ENNReal.ofReal (C_N * Real.exp (L * T) * max 1 (C_M * T) * (δ + ε)) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hht : h ∈ Icc 0 h₀ := ⟨hh.le, hh₀⟩
  have hLip : ∀ x y, ‖Φ h x - Φ h y‖ ≤ Real.exp (L * h) * ‖x - y‖ :=
    flow_lipschitz hL hF hΦ hΦ0 hht
  have hΦc : Continuous (Φ h) := by
    have : LipschitzWith ⟨Real.exp (L * h), (Real.exp_pos _).le⟩ (Φ h) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hLip x y
    exact this.continuous
  set Y := idealIter R (Φ h) ξ (A 0) with hYdef
  have hYm' := measurable_idealIter hR hΦc.measurable (ξ := ξ) (A 0)
  have hle : ∀ n, (⨆ j ∈ {j : ℕ | j ≤ n}, MeasurableSpace.comap (ξ j) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω) := fun n => iSup₂_le fun j _ => (hξ j).comap_le
  have hYm : ∀ n, Measurable (Y n) := fun n => (hYm' n).mono (hle n) le_rfl
  have hYS : ∀ n ω, Y n ω ∈ S := by
    intro n ω; cases n <;> exact hRS _ _
  -- the exact solution on the grid
  set a : ℕ → E := fun n => A (n * h) with ha_def
  have hT0 : 0 ≤ T := le_trans (by positivity) hN
  -- local errors
  have hloc : ∀ n, eLpNorm (fun ω => Y (n + 1) ω - Φ h (Y n ω)) q P ≤
      ENNReal.ofReal (C_N * (C_M * h * ε)) := by
    intro n
    have hind' : IndepFun (ξ (n + 1)) (fun ω => Φ h (Y n ω)) P :=
      indepFun_of_measurable_iSup hξ hind (S := {j : ℕ | j ≤ n}) (by simp)
        (hΦc.measurable.comp (hYm' n))
    have h1 := eLpNorm_indep_le hq0 hqt hR (hξ (n + 1)) (hΦc.measurable.comp (hYm n)) hind'
      (hmom (n + 1))
    have hdm : Measurable (fun ω => C_N * Metric.infDist (Φ h (Y n ω)) S) :=
      (((Metric.continuous_infDist_pt S).comp hΦc).measurable.comp (hYm n)).const_mul C_N
    refine h1.trans (eLpNorm_le_ofReal hq0 hdm.aestronglyMeasurable (by positivity) fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hCN Metric.infDist_nonneg)]
    exact mul_le_mul_of_nonneg_left (happrox _ (hYS n ω) h ⟨hh, hh₀⟩) hCN
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg.trans hδ
  have hstep : ∀ n < N, a (n + 1) = Φ h (a n) := by
    intro n hn
    have hn' : ((n : ℝ) + 1) * h ≤ T := le_trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.succ_le_of_lt hn) hh.le) hN
    simp only [ha_def]
    rw [← flow_step hL hF hΦ hΦ0 hA (by positivity) hh.le hh₀ (by linarith)]
    congr 1; push_cast; ring
  have h0 : eLpNorm (fun ω => Y 0 ω - a 0) q P ≤ ENNReal.ofReal (C_N * δ) := by
    have : a 0 = A 0 := by simp [ha_def]
    rw [this]
    exact (hmom 0 (A 0)).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hδ hCN))
  have hfan := lq_fan (P := P) hq (Real.one_le_exp (by positivity)) hLip hstep
    (fun n => (hYm n).aestronglyMeasurable) (fun n _ => hloc n) N le_rfl
  have hκ0 : 0 ≤ Real.exp (L * h) := (Real.exp_pos _).le
  calc eLpNorm (fun ω => Y N ω - A (N * h)) q P = eLpNorm (fun ω => Y N ω - a N) q P := rfl
    _ ≤ ENNReal.ofReal (Real.exp (L * h)) ^ N *
          (ENNReal.ofReal (C_N * δ) + N * ENNReal.ofReal (C_N * (C_M * h * ε))) := by
        refine hfan.trans ?_
        gcongr
    _ = ENNReal.ofReal (Real.exp (L * h) ^ N * (C_N * δ + N * (C_N * (C_M * h * ε)))) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hκ0 N), ENNReal.ofReal_pow hκ0,
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C_N * Real.exp (L * T) * max 1 (C_M * T) * (δ + ε)) := by
        apply ENNReal.ofReal_le_ofReal
        have hexp : Real.exp (L * h) ^ N ≤ Real.exp (L * T) := by
          rw [← Real.exp_nat_mul]
          exact Real.exp_le_exp.2 (by nlinarith)
        have hinner : C_N * δ + N * (C_N * (C_M * h * ε)) ≤
            C_N * (max 1 (C_M * T) * (δ + ε)) := by
          have h1 : δ ≤ max 1 (C_M * T) * δ := le_mul_of_one_le_left hδ0 (le_max_left _ _)
          have h2 : C_M * (N * h) * ε ≤ max 1 (C_M * T) * ε :=
            mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hN hCM).trans
              (le_max_right _ _)) hε
          have : C_N * δ + N * (C_N * (C_M * h * ε)) = C_N * (δ + C_M * (N * h) * ε) := by ring
          rw [this]
          refine mul_le_mul_of_nonneg_left ?_ hCN
          nlinarith
        calc Real.exp (L * h) ^ N * (C_N * δ + N * (C_N * (C_M * h * ε)))
            ≤ Real.exp (L * T) * (C_N * (max 1 (C_M * T) * (δ + ε))) :=
              mul_le_mul hexp hinner (by positivity) (Real.exp_pos _).le
          _ = _ := by ring

/-- **Corollary 4 of arXiv 2409.06384** (tail bound): under the hypotheses of `thm3`, with `C_N > 0`
and `δ + ε > 0`, for every `η > 0`: `P(‖Y_N - A(Nh)‖ ≥ C η (δ + ε)) ≤ η^{-q}` with `C = C_N e^{LT}
max(1, C_M T)` (the paper takes `η ≥ 1`). -/
theorem cor4 {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {S : Set E} {C_M ε : ℝ} (hCM : 0 ≤ C_M) (hε : 0 ≤ ε)
    (happrox : ∀ Y ∈ S, ∀ h ∈ Ioc 0 h₀, Metric.infDist (Φ h Y) S ≤ C_M * h * ε)
    {T : ℝ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A 0 T) {δ : ℝ}
    (hδ : Metric.infDist (A 0) S ≤ δ)
    {R : K → E → E} (hR : Measurable (Function.uncurry R)) (hRS : ∀ k z, R k z ∈ S)
    {C_N : ℝ} (hCN : 0 < C_N) {ξ : ℕ → Ω → K} (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom : ∀ i z, eLpNorm (fun ω => R (ξ i ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z S))
    {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) {N : ℕ} (hN : N * h ≤ T) (hpos : 0 < δ + ε)
    {η : ℝ} (hη : 0 < η) :
    P {ω | C_N * Real.exp (L * T) * max 1 (C_M * T) * η * (δ + ε) ≤
        ‖idealIter R (Φ h) ξ (A 0) N ω - A (N * h)‖} ≤ ENNReal.ofReal (η ^ (-q.toReal)) := by
  have h3 := thm3 hL hF hΦ hΦ0 hCM hε happrox hA hδ hR hRS hCN.le hξ hind hq hqt hmom hh hh₀ hN
  have hC : 0 < C_N * Real.exp (L * T) * max 1 (C_M * T) * (δ + ε) :=
    mul_pos (mul_pos (mul_pos hCN (Real.exp_pos _)) (lt_of_lt_of_le zero_lt_one
      (le_max_left _ _))) hpos
  have := markov_tail (P := P) (zero_lt_one.trans_le hq).ne' hqt hC h3 hη
  rw [show C_N * Real.exp (L * T) * max 1 (C_M * T) * η * (δ + ε) =
    η * (C_N * Real.exp (L * T) * max 1 (C_M * T) * (δ + ε)) by ring]
  exact this

end Thm3


section RK

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Stage increments of an explicit Runge–Kutta method with stage maps `N j` (arXiv 2409.06384,
scheme (16)): `rkK j = F(N_j(Z_j))`, `Z_j = Y + h ∑_{l<j} a j l • rkK l`. With `N = id` these are
the classical stages; with `N_j` a randomized low-rank map, those of the randomized method. -/
noncomputable def rkK (F : E → E) (N : ℕ → E → E) (a : ℕ → ℕ → ℝ) (h : ℝ) (Y : E) : ℕ → E
  | j => F (N j (Y + h • ∑ l : Fin j, a j l • rkK F N a h Y l))
termination_by j => j
decreasing_by exact l.isLt

/-- The stage `Z_j = Y + h ∑_{l<j} a j l • F(N_l(Z_l))` of an explicit Runge–Kutta method with stage
maps `N` (arXiv 2409.06384, scheme (16)). -/
noncomputable def rkZ (F : E → E) (N : ℕ → E → E) (a : ℕ → ℕ → ℝ) (h : ℝ) (Y : E) (j : ℕ) : E :=
  Y + h • ∑ l : Fin j, a j l • rkK F N a h Y l

/-- Unfolding equation of `rkK` (auxiliary; arXiv 2409.06384). -/
theorem rkK_eq (F : E → E) (N : ℕ → E → E) (a : ℕ → ℕ → ℝ) (h : ℝ) (Y : E) (j : ℕ) :
    rkK F N a h Y j = F (N j (rkZ F N a h Y j)) := by
  rw [rkK]; rfl

/-- Measurability of the stages with respect to the σ-algebra of the sketches used so far
(auxiliary; arXiv 2409.06384). -/
theorem measurable_rkK {Ω : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {F : E → E} (hF : Measurable F) {N : ℕ → Ω → E → E}
    (a : ℕ → ℕ → ℝ) (h : ℝ) {Y : Ω → E} (hY : Measurable Y) (j : ℕ)
    (hN : ∀ l ≤ j, ∀ X : Ω → E, Measurable X → Measurable (fun ω => N l ω (X ω))) :
    Measurable (fun ω => rkK F (fun l => N l ω) a h (Y ω) j) ∧
      Measurable (fun ω => rkZ F (fun l => N l ω) a h (Y ω) j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hZ : Measurable (fun ω => rkZ F (fun l => N l ω) a h (Y ω) j) := by
      unfold rkZ
      refine hY.add (Measurable.const_smul (Finset.measurable_sum _ fun l _ => ?_) h)
      exact ((ih l l.isLt fun l' hl' => hN l' (by omega)).1).const_smul _
    refine ⟨?_, hZ⟩
    simp_rw [rkK_eq]
    exact hF.comp (hN j le_rfl _ hZ)

/-- The stage `Z_j` only depends measurably on the stage maps `l < j` (auxiliary; arXiv 2409.06384).
-/
theorem measurable_rkZ {Ω : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {F : E → E} (hF : Measurable F) {N : ℕ → Ω → E → E}
    (a : ℕ → ℕ → ℝ) (h : ℝ) {Y : Ω → E} (hY : Measurable Y) (j : ℕ)
    (hN : ∀ l < j, ∀ X : Ω → E, Measurable X → Measurable (fun ω => N l ω (X ω))) :
    Measurable (fun ω => rkZ F (fun l => N l ω) a h (Y ω) j) := by
  unfold rkZ
  refine hY.add (Measurable.const_smul (Finset.measurable_sum _ fun l _ => ?_) h)
  exact ((measurable_rkK hF a h hY l fun l' hl' => hN l' (by omega)).1).const_smul _

end RK


section RKStep

variable {Ω K E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- `‖c + ‖f‖‖_{L^q} ≤ c + ‖f‖_{L^q}` on a probability space (auxiliary; arXiv 2409.06384). -/
theorem eLpNorm_const_add_norm_le {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Ω → E}
    (hf : AEStronglyMeasurable f P) {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun ω => c + ‖f ω‖) q P ≤ ENNReal.ofReal c + eLpNorm f q P := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have : (fun ω => c + ‖f ω‖) = (fun _ : Ω => c) + (fun ω => ‖f ω‖) := rfl
  rw [this]
  refine (eLpNorm_add_le hq).trans (add_le_add ?_ ?_)
  · rw [eLpNorm_const c hq0 (IsProbabilityMeasure.ne_zero P), measure_univ, ENNReal.one_rpow,
      mul_one, Real.enorm_eq_ofReal hc]
  · exact (eLpNorm_norm f hf).le

omit [NormedSpace ℝ E] in
/-- The moment assumption (7) of arXiv 2409.06384 applied to a random input `X` independent of the
sketch, with `dist(X, S)` controlled through a nearby point `Xt` with `dist(Xt, S) ≤ θ`. -/
theorem eLpNorm_sketch_le_of_near {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞) {R : K → E → E}
    (hR : Measurable (Function.uncurry R)) {ξ : Ω → K} (hξ : Measurable ξ) {S : Set E}
    {C_N : ℝ} (hCN : 0 ≤ C_N)
    (hmom : ∀ z, eLpNorm (fun ω => R (ξ ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z S))
    {X Xt : Ω → E} (hX : Measurable X) (hXt : Measurable Xt) (hind : IndepFun ξ X P)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ ω, Metric.infDist (Xt ω) S ≤ θ) :
    eLpNorm (fun ω => R (ξ ω) (X ω) - X ω) q P ≤
      ENNReal.ofReal C_N * (ENNReal.ofReal θ + eLpNorm (fun ω => X ω - Xt ω) q P) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  refine (eLpNorm_indep_le hq0 hqt hR hξ hX hind hmom).trans ?_
  have hm : Measurable (fun ω => C_N * Metric.infDist (X ω) S) :=
    ((Metric.continuous_infDist_pt S).measurable.comp hX).const_mul C_N
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := fun ω => θ + ‖X ω - Xt ω‖) (c := C_N)
    hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_) q).trans ?_
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hCN Metric.infDist_nonneg),
      abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ hCN
    calc Metric.infDist (X ω) S ≤ Metric.infDist (Xt ω) S + dist (X ω) (Xt ω) :=
          Metric.infDist_le_infDist_add_dist
      _ ≤ θ + ‖X ω - Xt ω‖ := by rw [dist_eq_norm]; linarith [hθ ω]
  · gcongr
    exact eLpNorm_const_add_norm_le hq (hX.sub hXt).aestronglyMeasurable hθ0

/-- **Theorem 11 of arXiv 2409.06384** (stage errors of the randomized low-rank RK method), in
majorant form: one step from a random `Y`, stage maps `R j (ξ j)` with the moment assumption (7)
and sketches independent of the stage inputs, classical stages `Z̃_j` with `dist(Z̃_j, S_j) ≤ β_j`.
If the real numbers `Eb j ≥ 0` satisfy `L (C_N β_j + (C_N + 1) ∑_{l<j} |h a_{jl}| Eb_l) ≤ Eb_j`,
then `‖F(𝒩_j(Z_j)) - F(Z̃_j)‖_{L^q} ≤ Eb_j` and `‖Z_j - Z̃_j‖_{L^q} ≤ ∑_{l<j} |h a_{jl}| Eb_l`.
The paper's rates (`0` at the first stage, `O(hε + h^{γ̃_j+1})` later) are obtained in
`rrk_refined` with explicit majorants. -/
theorem thm11 {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {R : ℕ → K → E → E} (hR : ∀ j, Measurable (Function.uncurry (R j))) {S : ℕ → Set E}
    {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ → Ω → K} (hξ : ∀ j, Measurable (ξ j))
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom : ∀ j z, eLpNorm (fun ω => R j (ξ j ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z (S j)))
    (a : ℕ → ℕ → ℝ) (s : ℕ) (h : ℝ) {Y : Ω → E} (hY : Measurable Y)
    (hind : ∀ j < s, IndepFun (ξ j) (fun ω => rkZ F (fun l => R l (ξ l ω)) a h (Y ω) j) P)
    {β : ℕ → ℝ}
    (hβ : ∀ j < s, ∀ ω, Metric.infDist (rkZ F (fun _ => id) a h (Y ω) j) (S j) ≤ β j)
    {Eb : ℕ → ℝ} (hE0 : ∀ j, 0 ≤ Eb j)
    (hE : ∀ j < s, L * (C_N * β j + (C_N + 1) * ∑ l : Fin j, |h * a j l| * Eb l) ≤ Eb j) :
    ∀ j < s, eLpNorm (fun ω => rkK F (fun l => R l (ξ l ω)) a h (Y ω) j -
        rkK F (fun _ => id) a h (Y ω) j) q P ≤ ENNReal.ofReal (Eb j) ∧
      eLpNorm (fun ω => rkZ F (fun l => R l (ξ l ω)) a h (Y ω) j -
        rkZ F (fun _ => id) a h (Y ω) j) q P ≤
          ENNReal.ofReal (∑ l : Fin j, |h * a j l| * Eb l) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hβ0 : ∀ j < s, 0 ≤ β j := fun j hj => Metric.infDist_nonneg.trans (hβ j hj ω₀)
  have hFm : Measurable F := by
    have : LipschitzWith ⟨L, hL⟩ F := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact hF x y
    exact this.continuous.measurable
  have hNm : ∀ l, ∀ X : Ω → E, Measurable X → Measurable (fun ω => R l (ξ l ω) (X ω)) :=
    fun l X hX => (hR l).comp ((hξ l).prodMk hX)
  have hK : ∀ j, Measurable (fun ω => rkK F (fun l => R l (ξ l ω)) a h (Y ω) j) :=
    fun j => (measurable_rkK hFm a h hY j (fun l _ => hNm l)).1
  have hZ : ∀ j, Measurable (fun ω => rkZ F (fun l => R l (ξ l ω)) a h (Y ω) j) :=
    fun j => (measurable_rkK hFm a h hY j (fun l _ => hNm l)).2
  have hKt : ∀ j, Measurable (fun ω => rkK F (fun _ => id) a h (Y ω) j) :=
    fun j => (measurable_rkK (N := fun _ _ => id) hFm a h hY j (fun _ _ _ hX => hX)).1
  have hZt : ∀ j, Measurable (fun ω => rkZ F (fun _ => id) a h (Y ω) j) :=
    fun j => (measurable_rkK (N := fun _ _ => id) hFm a h hY j (fun _ _ _ hX => hX)).2
  set e : ℕ → ℝ≥0∞ := fun j => eLpNorm (fun ω => rkK F (fun l => R l (ξ l ω)) a h (Y ω) j -
    rkK F (fun _ => id) a h (Y ω) j) q P with he_def
  -- stage differences
  have hd : ∀ j, eLpNorm (fun ω => rkZ F (fun l => R l (ξ l ω)) a h (Y ω) j -
      rkZ F (fun _ => id) a h (Y ω) j) q P ≤ ∑ l : Fin j, ENNReal.ofReal |h * a j l| * e l := by
    intro j
    have : (fun ω => rkZ F (fun l => R l (ξ l ω)) a h (Y ω) j -
        rkZ F (fun _ => id) a h (Y ω) j) = ∑ l : Fin j, (h * a j l) • (fun ω =>
          rkK F (fun l => R l (ξ l ω)) a h (Y ω) l - rkK F (fun _ => id) a h (Y ω) l) := by
      funext ω
      simp only [rkZ, Finset.sum_apply, Pi.smul_apply, add_sub_add_left_eq_sub, ← smul_sub,
        ← Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    rw [this]
    refine (eLpNorm_sum_le hq).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  -- stage recursion
  have hstage : ∀ j < s, e j ≤ ENNReal.ofReal L * (ENNReal.ofReal C_N * ENNReal.ofReal (β j) +
      ENNReal.ofReal (C_N + 1) * ∑ l : Fin j, ENNReal.ofReal |h * a j l| * e l) := by
    intro j hj
    set Z := fun ω => rkZ F (fun l => R l (ξ l ω)) a h (Y ω) j with hZdef
    set Zt := fun ω => rkZ F (fun _ => id) a h (Y ω) j with hZtdef
    have h1 : e j ≤ ENNReal.ofReal L * eLpNorm (fun ω => R j (ξ j ω) (Z ω) - Zt ω) q P := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hK j).sub (hKt j)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_) q
      simp only [hZdef, hZtdef, Pi.sub_apply]
      rw [rkK_eq, rkK_eq]
      exact hF _ _
    have h2 : eLpNorm (fun ω => R j (ξ j ω) (Z ω) - Zt ω) q P ≤
        eLpNorm (fun ω => R j (ξ j ω) (Z ω) - Z ω) q P + eLpNorm (fun ω => Z ω - Zt ω) q P := by
      have : (fun ω => R j (ξ j ω) (Z ω) - Zt ω) =
          (fun ω => R j (ξ j ω) (Z ω) - Z ω) + (fun ω => Z ω - Zt ω) := by
        funext ω; simp
      rw [this]; exact eLpNorm_add_le hq
    have h3 := eLpNorm_sketch_le_of_near hq hqt (hR j) (hξ j) hCN (hmom j) (hZ j) (hZt j)
      (hind j hj) (hβ0 j hj) (hβ j hj)
    refine h1.trans ?_
    gcongr
    refine h2.trans ((add_le_add h3 le_rfl).trans ?_)
    have h4 := hd j
    calc ENNReal.ofReal C_N * (ENNReal.ofReal (β j) + eLpNorm (fun ω => Z ω - Zt ω) q P) +
          eLpNorm (fun ω => Z ω - Zt ω) q P
        = ENNReal.ofReal C_N * ENNReal.ofReal (β j) +
          ENNReal.ofReal (C_N + 1) * eLpNorm (fun ω => Z ω - Zt ω) q P := by
          rw [ENNReal.ofReal_add hCN zero_le_one, ENNReal.ofReal_one]; ring
      _ ≤ _ := by gcongr
  -- real majorants
  have hmaj : ∀ j < s, e j ≤ ENNReal.ofReal (Eb j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      refine (hstage j hj).trans ?_
      refine le_trans ?_ (ENNReal.ofReal_le_ofReal (hE j hj))
      have hsum : ∑ l : Fin j, ENNReal.ofReal |h * a j l| * e l ≤
          ENNReal.ofReal (∑ l : Fin j, |h * a j l| * Eb l) := by
        rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
          (f := fun l : Fin j => |h * a j l| * Eb l)
          (fun l _ => mul_nonneg (abs_nonneg _) (hE0 l))]
        refine Finset.sum_le_sum fun l _ => ?_
        rw [ENNReal.ofReal_mul (abs_nonneg _)]
        gcongr
        exact ih l l.isLt (by omega)
      calc ENNReal.ofReal L * (ENNReal.ofReal C_N * ENNReal.ofReal (β j) +
            ENNReal.ofReal (C_N + 1) * ∑ l : Fin j, ENNReal.ofReal |h * a j l| * e l)
          ≤ ENNReal.ofReal L * (ENNReal.ofReal C_N * ENNReal.ofReal (β j) +
            ENNReal.ofReal (C_N + 1) * ENNReal.ofReal (∑ l : Fin j, |h * a j l| * Eb l)) := by
            gcongr
        _ = _ := by
            have h1 : 0 ≤ C_N * β j := mul_nonneg hCN (hβ0 j hj)
            have h2 : 0 ≤ (C_N + 1) * ∑ l : Fin j, |h * a j l| * Eb l :=
              mul_nonneg (by linarith)
                (Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (hE0 l))
            rw [ENNReal.ofReal_mul hL, ENNReal.ofReal_add h1 h2, ENNReal.ofReal_mul hCN,
              ENNReal.ofReal_mul (by linarith)]
  intro j hj
  refine ⟨hmaj j hj, (hd j).trans ?_⟩
  rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun l : Fin j => |h * a j l| * Eb l)
    (fun l _ => mul_nonneg (abs_nonneg _) (hE0 l))]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  gcongr
  exact hmaj l (l.isLt.trans hj)

/-- **Per-step `L^q` analysis of the randomized low-rank RK method** (arXiv 2409.06384, proof of
Theorem 11 and of the local error bound in the appendix).  `Eb j` are real majorants of the stage
errors `‖F(𝒩_j(Z_j)) - F(Z̃_j)‖_{L^q}` (`Z̃_j` the classical stages); `β j` bounds the best
approximation error of the classical stage `Z̃_j`, `θ` that of `Φ^h(Y)`, `ρ` the classical RK local
error. -/
theorem rk_step_error {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {R : ℕ → K → E → E} (hR : ∀ j, Measurable (Function.uncurry (R j))) {S : ℕ → Set E}
    {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ → Ω → K} (hξ : ∀ j, Measurable (ξ j))
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom : ∀ j z, eLpNorm (fun ω => R j (ξ j ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z (S j)))
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (s : ℕ) (h : ℝ) {Y : Ω → E} (hY : Measurable Y)
    (hind : ∀ j < s, IndepFun (ξ j) (fun ω => rkZ F (fun l => R l (ξ l ω)) a h (Y ω) j) P)
    (hindf : IndepFun (ξ s) (fun ω => Y ω + h • ∑ j ∈ range s,
      b j • rkK F (fun l => R l (ξ l ω)) a h (Y ω) j) P)
    {Φh : E → E} (hΦh : Measurable Φh) {β : ℕ → ℝ}
    (hβ : ∀ j < s, ∀ ω, Metric.infDist (rkZ F (fun _ => id) a h (Y ω) j) (S j) ≤ β j)
    {θ ρ : ℝ} (hθ : ∀ ω, Metric.infDist (Φh (Y ω)) (S s) ≤ θ)
    (hρ : ∀ ω, ‖(Y ω + h • ∑ j ∈ range s, b j • rkK F (fun _ => id) a h (Y ω) j) - Φh (Y ω)‖ ≤ ρ)
    {Eb : ℕ → ℝ} (hE0 : ∀ j, 0 ≤ Eb j)
    (hE : ∀ j < s, L * (C_N * β j + (C_N + 1) * ∑ l : Fin j, |h * a j l| * Eb l) ≤ Eb j) :
    eLpNorm (fun ω => R s (ξ s ω) (Y ω + h • ∑ j ∈ range s,
        b j • rkK F (fun l => R l (ξ l ω)) a h (Y ω) j) - Φh (Y ω)) q P ≤
      ENNReal.ofReal (C_N * θ + (C_N + 1) * (∑ j ∈ range s, |h * b j| * Eb j + ρ)) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hθ0 : 0 ≤ θ := Metric.infDist_nonneg.trans (hθ ω₀)
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ ω₀)
  have hFm : Measurable F := by
    have : LipschitzWith ⟨L, hL⟩ F := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact hF x y
    exact this.continuous.measurable
  have hNm : ∀ l, ∀ X : Ω → E, Measurable X → Measurable (fun ω => R l (ξ l ω) (X ω)) :=
    fun l X hX => (hR l).comp ((hξ l).prodMk hX)
  have hK : ∀ j, Measurable (fun ω => rkK F (fun l => R l (ξ l ω)) a h (Y ω) j) :=
    fun j => (measurable_rkK hFm a h hY j (fun l _ => hNm l)).1
  have hKt : ∀ j, Measurable (fun ω => rkK F (fun _ => id) a h (Y ω) j) :=
    fun j => (measurable_rkK (N := fun _ _ => id) hFm a h hY j (fun _ _ _ hX => hX)).1
  have hmaj : ∀ j < s, eLpNorm (fun ω => rkK F (fun l => R l (ξ l ω)) a h (Y ω) j -
      rkK F (fun _ => id) a h (Y ω) j) q P ≤ ENNReal.ofReal (Eb j) := fun j hj =>
    (thm11 (P := P) hL hF hR hCN hξ hq hqt hmom a s h hY hind hβ hE0 hE j hj).1
  -- final truncation
  set X := fun ω => Y ω + h • ∑ j ∈ range s, b j • rkK F (fun l => R l (ξ l ω)) a h (Y ω) j
    with hXdef
  set Xt := fun ω => Y ω + h • ∑ j ∈ range s, b j • rkK F (fun _ => id) a h (Y ω) j
    with hXtdef
  have hXm : Measurable X :=
    hY.add ((Finset.measurable_sum _ fun j _ => (hK j).const_smul _).const_smul _)
  have hXtm : Measurable Xt :=
    hY.add ((Finset.measurable_sum _ fun j _ => (hKt j).const_smul _).const_smul _)
  have hΦm : Measurable (fun ω => Φh (Y ω)) := hΦh.comp hY
  have hXX : eLpNorm (fun ω => X ω - Xt ω) q P ≤
      ENNReal.ofReal (∑ j ∈ range s, |h * b j| * Eb j) := by
    have : (fun ω => X ω - Xt ω) = ∑ j ∈ range s, (h * b j) • (fun ω =>
        rkK F (fun l => R l (ξ l ω)) a h (Y ω) j - rkK F (fun _ => id) a h (Y ω) j) := by
      funext ω
      simp only [hXdef, hXtdef, Finset.sum_apply, Pi.smul_apply, add_sub_add_left_eq_sub,
        ← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    rw [this, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hE0 j))]
    refine (eLpNorm_sum_le hq).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg _)]
    gcongr
    exact hmaj j (Finset.mem_range.1 hj)
  have hXΦ : eLpNorm (fun ω => X ω - Φh (Y ω)) q P ≤
      ENNReal.ofReal (∑ j ∈ range s, |h * b j| * Eb j + ρ) := by
    have : (fun ω => X ω - Φh (Y ω)) = (fun ω => X ω - Xt ω) + (fun ω => Xt ω - Φh (Y ω)) := by
      funext ω; simp
    rw [this, ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hE0 j))
      hρ0]
    refine (eLpNorm_add_le hq).trans (add_le_add hXX ?_)
    exact eLpNorm_le_ofReal hq0 (hXtm.sub hΦm).aestronglyMeasurable hρ0 hρ
  have hfin := eLpNorm_sketch_le_of_near hq hqt (hR s) (hξ s) hCN (hmom s) hXm hΦm hindf hθ0 hθ
  have hsplit : (fun ω => R s (ξ s ω) (X ω) - Φh (Y ω)) =
      (fun ω => R s (ξ s ω) (X ω) - X ω) + (fun ω => X ω - Φh (Y ω)) := by
    funext ω; simp
  have hrw : (fun ω => R s (ξ s ω) (Y ω + h • ∑ j ∈ range s,
        b j • rkK F (fun l => R l (ξ l ω)) a h (Y ω) j) - Φh (Y ω)) =
      (fun ω => R s (ξ s ω) (X ω) - Φh (Y ω)) := rfl
  rw [hrw, hsplit]
  have hS0 : 0 ≤ ∑ j ∈ range s, |h * b j| * Eb j + ρ :=
    add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hE0 j)) hρ0
  calc eLpNorm ((fun ω => R s (ξ s ω) (X ω) - X ω) + fun ω => X ω - Φh (Y ω)) q P
      ≤ ENNReal.ofReal C_N * (ENNReal.ofReal θ + eLpNorm (fun ω => X ω - Φh (Y ω)) q P) +
          eLpNorm (fun ω => X ω - Φh (Y ω)) q P :=
        (eLpNorm_add_le hq).trans (add_le_add hfin le_rfl)
    _ ≤ ENNReal.ofReal C_N * (ENNReal.ofReal θ +
          ENNReal.ofReal (∑ j ∈ range s, |h * b j| * Eb j + ρ)) +
          ENNReal.ofReal (∑ j ∈ range s, |h * b j| * Eb j + ρ) := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg hCN hθ0) (mul_nonneg (by linarith) hS0),
          ENNReal.ofReal_mul hCN, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_add hCN
          zero_le_one, ENNReal.ofReal_one]
        ring

end RKStep


section RRK

variable {Ω K E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- **Randomized low-rank Runge–Kutta method** (arXiv 2409.06384, Sec. 3, scheme (16)–(17)): `Y₀ =
𝒩(A₀)` and `Y_{n+1} = 𝒩_s(Y_n + h ∑_{j<s} b_j F(𝒩_j(Z_j)))`, `Z_j = Y_n + h ∑_{l<j} a_{jl}
F(𝒩_l(Z_l))`, where the map of stage `j` in step `n+1` is `R j (ξ (n+1, j) ω)` (stage `s` is the
final truncation, also used for `Y₀` with sketch `ξ (0, s)`). -/
noncomputable def rrkIter (F : E → E) (R : ℕ → K → E → E) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (s : ℕ)
    (h : ℝ) (ξ : ℕ × ℕ → Ω → K) (A₀ : E) : ℕ → Ω → E
  | 0 => fun ω => R s (ξ (0, s) ω) A₀
  | n + 1 => fun ω => R s (ξ (n + 1, s) ω) (rrkIter F R a b s h ξ A₀ n ω + h • ∑ j ∈ range s,
      b j • rkK F (fun l => R l (ξ (n + 1, l) ω)) a h (rrkIter F R a b s h ξ A₀ n ω) j)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [NormedSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- A sketch is measurable for the σ-algebra of the past that contains it (auxiliary; arXiv
2409.06384). -/
theorem measurable_of_mem_past {ι : Type*} {ξ : ι → Ω → K} {T : Set ι} {p : ι} (hp : p ∈ T) :
    Measurable[⨆ i ∈ T, MeasurableSpace.comap (ξ i) inferInstance] (ξ p) :=
  Measurable.of_comap_le (le_iSup₂
    (f := fun i (_ : i ∈ T) => MeasurableSpace.comap (ξ i) inferInstance) p hp)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [NormedSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Monotonicity of the σ-algebra generated by a set of sketches (auxiliary; arXiv 2409.06384). -/
theorem past_mono {ι : Type*} {ξ : ι → Ω → K} {T T' : Set ι} (h : T ⊆ T') :
    (⨆ i ∈ T, MeasurableSpace.comap (ξ i) inferInstance) ≤
      ⨆ i ∈ T', MeasurableSpace.comap (ξ i) inferInstance :=
  iSup₂_le fun i hi => le_iSup₂
    (f := fun i (_ : i ∈ T') => MeasurableSpace.comap (ξ i) inferInstance) i (h hi)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The `n`-th iterate of the randomized RK method is measurable with respect to the sketches of
steps `≤ n` (auxiliary; arXiv 2409.06384). -/
theorem measurable_rrkIter {F : E → E} (hF : Measurable F) {R : ℕ → K → E → E}
    (hR : ∀ j, Measurable (Function.uncurry (R j))) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (s : ℕ) (h : ℝ)
    (ξ : ℕ × ℕ → Ω → K) (A₀ : E) (n : ℕ) :
    Measurable[⨆ p ∈ {p : ℕ × ℕ | p.1 ≤ n}, MeasurableSpace.comap (ξ p) inferInstance]
      (rrkIter F R a b s h ξ A₀ n) := by
  induction n with
  | zero =>
    exact (hR s).comp ((measurable_of_mem_past (T := {p : ℕ × ℕ | p.1 ≤ 0})
      (show (0, s) ∈ {p : ℕ × ℕ | p.1 ≤ 0} from le_refl 0)).prodMk measurable_const)
  | succ n ih =>
    set m := ⨆ p ∈ {p : ℕ × ℕ | p.1 ≤ n + 1}, MeasurableSpace.comap (ξ p) inferInstance
    have hY : Measurable[m] (rrkIter F R a b s h ξ A₀ n) :=
      ih.mono (past_mono fun p (hp : p.1 ≤ n) => show p.1 ≤ n + 1 by omega) le_rfl
    have hξm : ∀ l, Measurable[m] (ξ (n + 1, l)) := fun l =>
      measurable_of_mem_past (T := {p : ℕ × ℕ | p.1 ≤ n + 1})
        (show (n + 1, l) ∈ {p : ℕ × ℕ | p.1 ≤ n + 1} from le_refl (n + 1))
    have hK : ∀ j, Measurable[m] (fun ω =>
        rkK F (fun l => R l (ξ (n + 1, l) ω)) a h (rrkIter F R a b s h ξ A₀ n ω) j) :=
      fun j => (measurable_rkK (m := m) hF a h hY j
        (fun l _ X hX => (hR l).comp ((hξm l).prodMk hX))).1
    exact (hR s).comp ((hξm s).prodMk (hY.add
      ((Finset.measurable_sum _ fun j _ => (hK j).const_smul _).const_smul _)))

/-- **Local error of the randomized low-rank RK method in `L^q`** (arXiv 2409.06384, appendix, local
error bound): at every step `n`, `‖Y_{n+1} - Φ^h(Y_n)‖_{L^q} ≤ C_N θ + (C_N + 1) (∑_j |h b_j| Eb_j +
ρ)`, where the stage majorants `Eb` satisfy the recursion of Theorem 11. -/
theorem rrk_local {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {R : ℕ → K → E → E} (hR : ∀ j, Measurable (Function.uncurry (R j))) {S : ℕ → Set E}
    (s : ℕ) (hRS : ∀ k z, R s k z ∈ S s) {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ × ℕ → Ω → K}
    (hξ : ∀ p, Measurable (ξ p)) (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom : ∀ n j z, eLpNorm (fun ω => R j (ξ (n, j) ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z (S j)))
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (h : ℝ) (A₀ : E) {Φh : E → E} (hΦh : Measurable Φh)
    {β : ℕ → ℝ}
    (hβ : ∀ y ∈ S s, ∀ j < s, Metric.infDist (rkZ F (fun _ => id) a h y j) (S j) ≤ β j)
    {θ ρ : ℝ} (hθ : ∀ y ∈ S s, Metric.infDist (Φh y) (S s) ≤ θ)
    (hρ : ∀ y ∈ S s, ‖(y + h • ∑ j ∈ range s, b j • rkK F (fun _ => id) a h y j) - Φh y‖ ≤ ρ)
    {Eb : ℕ → ℝ} (hE0 : ∀ j, 0 ≤ Eb j)
    (hE : ∀ j < s, L * (C_N * β j + (C_N + 1) * ∑ l : Fin j, |h * a j l| * Eb l) ≤ Eb j)
    (n : ℕ) :
    eLpNorm (fun ω => rrkIter F R a b s h ξ A₀ (n + 1) ω -
        Φh (rrkIter F R a b s h ξ A₀ n ω)) q P ≤
      ENNReal.ofReal (C_N * θ + (C_N + 1) * (∑ j ∈ range s, |h * b j| * Eb j + ρ)) := by
  have hFm : Measurable F := by
    have : LipschitzWith ⟨L, hL⟩ F := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact hF x y
    exact this.continuous.measurable
  set Y := rrkIter F R a b s h ξ A₀ with hYdef
  have hYm' := measurable_rrkIter hFm hR a b s h ξ A₀
  have hle : ∀ T' : Set (ℕ × ℕ), (⨆ p ∈ T', MeasurableSpace.comap (ξ p) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω) := fun T' => iSup₂_le fun p _ => (hξ p).comap_le
  have hYm : ∀ n, Measurable (Y n) := fun n => (hYm' n).mono (hle _) le_rfl
  have hYS : ∀ n ω, Y n ω ∈ S s := by
    intro n ω; cases n <;> exact hRS _ _
  have hpast : ∀ j, ∀ X : Ω → E,
      Measurable[⨆ p ∈ {p : ℕ × ℕ | p.1 ≤ n ∨ (p.1 = n + 1 ∧ p.2 < j)},
        MeasurableSpace.comap (ξ p) inferInstance] X →
      IndepFun (ξ (n + 1, j)) X P := fun j X hX =>
    indepFun_of_measurable_iSup hξ hind (by simp) hX
  have hYj : ∀ j, Measurable[⨆ p ∈ {p : ℕ × ℕ | p.1 ≤ n ∨ (p.1 = n + 1 ∧ p.2 < j)},
      MeasurableSpace.comap (ξ p) inferInstance] (Y n) := fun j =>
    (hYm' n).mono (past_mono fun p (hp : p.1 ≤ n) => Or.inl hp) le_rfl
  have hξj : ∀ j l, l < j → Measurable[⨆ p ∈ {p : ℕ × ℕ | p.1 ≤ n ∨ (p.1 = n + 1 ∧ p.2 < j)},
      MeasurableSpace.comap (ξ p) inferInstance] (ξ (n + 1, l)) := fun j l hl =>
    measurable_of_mem_past (show (n + 1, l) ∈ {p : ℕ × ℕ | p.1 ≤ n ∨ (p.1 = n + 1 ∧ p.2 < j)}
      from Or.inr ⟨rfl, hl⟩)
  have hind_stage : ∀ j < s, IndepFun (ξ (n + 1, j))
      (fun ω => rkZ F (fun l => R l (ξ (n + 1, l) ω)) a h (Y n ω) j) P := by
    intro j _
    refine hpast j _ (measurable_rkZ hFm a h (hYj j) j fun l hl X hX => ?_)
    exact (hR l).comp ((hξj j l hl).prodMk hX)
  have hind_fin : IndepFun (ξ (n + 1, s)) (fun ω => Y n ω + h • ∑ j ∈ range s,
      b j • rkK F (fun l => R l (ξ (n + 1, l) ω)) a h (Y n ω) j) P := by
    refine hpast s _ ((hYj s).add ((Finset.measurable_sum _ fun j hj => ?_).const_smul _))
    refine Measurable.const_smul (measurable_rkK hFm a h (hYj s) j fun l hl X hX => ?_).1 _
    exact (hR l).comp ((hξj s l (lt_of_le_of_lt hl (Finset.mem_range.1 hj))).prodMk hX)
  have := rk_step_error (P := P) hL hF hR hCN (ξ := fun j => ξ (n + 1, j)) (fun j => hξ _)
    hq hqt (fun j z => hmom (n + 1) j z) a b s h (hYm n) hind_stage hind_fin
    hΦh (fun j hj ω => hβ _ (hYS n ω) j hj) (fun ω => hθ _ (hYS n ω))
    (fun ω => hρ _ (hYS n ω)) hE0 hE
  exact this

/-- **Global error of the randomized low-rank RK method in `L^q`** (arXiv 2409.06384, proof of
Theorem 5, from the local bound by the accumulation of the proof of Theorem 3): with the stage
majorants of `rrk_local`, `‖Y_N - A(Nh)‖_{L^q} ≤ e^{LT} (C_N δ + N ℓ)`, `ℓ = C_N θ + (C_N + 1)(∑_j
|h b_j| Eb_j + ρ)`. -/
theorem rrk_global {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {T : ℝ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A 0 T)
    {R : ℕ → K → E → E} (hR : ∀ j, Measurable (Function.uncurry (R j))) {S : ℕ → Set E}
    (s : ℕ) (hRS : ∀ k z, R s k z ∈ S s) {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ × ℕ → Ω → K}
    (hξ : ∀ p, Measurable (ξ p)) (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom : ∀ n j z, eLpNorm (fun ω => R j (ξ (n, j) ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z (S j)))
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) {δ : ℝ}
    (hδ : Metric.infDist (A 0) (S s) ≤ δ) {β : ℕ → ℝ}
    (hβ : ∀ y ∈ S s, ∀ j < s, Metric.infDist (rkZ F (fun _ => id) a h y j) (S j) ≤ β j)
    {θ ρ : ℝ} (hθ : ∀ y ∈ S s, Metric.infDist (Φ h y) (S s) ≤ θ)
    (hρ : ∀ y ∈ S s, ‖(y + h • ∑ j ∈ range s, b j • rkK F (fun _ => id) a h y j) - Φ h y‖ ≤ ρ)
    {Eb : ℕ → ℝ} (hE0 : ∀ j, 0 ≤ Eb j)
    (hE : ∀ j < s, L * (C_N * β j + (C_N + 1) * ∑ l : Fin j, |h * a j l| * Eb l) ≤ Eb j)
    {N : ℕ} (hN : N * h ≤ T) :
    eLpNorm (fun ω => rrkIter F R a b s h ξ (A 0) N ω - A (N * h)) q P ≤
      ENNReal.ofReal (Real.exp (L * T) * (C_N * δ +
        N * (C_N * θ + (C_N + 1) * (∑ j ∈ range s, |h * b j| * Eb j + ρ)))) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hht : h ∈ Icc 0 h₀ := ⟨hh.le, hh₀⟩
  have hLip : ∀ x y, ‖Φ h x - Φ h y‖ ≤ Real.exp (L * h) * ‖x - y‖ :=
    flow_lipschitz hL hF hΦ hΦ0 hht
  have hΦc : Continuous (Φ h) := by
    have : LipschitzWith ⟨Real.exp (L * h), (Real.exp_pos _).le⟩ (Φ h) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hLip x y
    exact this.continuous
  have hFm : Measurable F := by
    have : LipschitzWith ⟨L, hL⟩ F := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact hF x y
    exact this.continuous.measurable
  set Y := rrkIter F R a b s h ξ (A 0) with hYdef
  have hYm' := measurable_rrkIter hFm hR a b s h ξ (A 0)
  have hle : ∀ T' : Set (ℕ × ℕ), (⨆ p ∈ T', MeasurableSpace.comap (ξ p) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω) := fun T' => iSup₂_le fun p _ => (hξ p).comap_le
  have hYm : ∀ n, Measurable (Y n) := fun n => (hYm' n).mono (hle _) le_rfl
  have hYS : ∀ n ω, Y n ω ∈ S s := by
    intro n ω; cases n <;> exact hRS _ _
  -- local error at every step
  have hloc := rrk_local (P := P) hL hF hR s hRS hCN hξ hind hq hqt hmom a b h (A 0)
    hΦc.measurable hβ hθ hρ hE0 hE
  -- fan
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg.trans hδ
  have hθ0 : 0 ≤ θ := Metric.infDist_nonneg.trans (hθ _ (hYS 0 ω₀))
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ _ (hYS 0 ω₀))
  set ℓ := C_N * θ + (C_N + 1) * (∑ j ∈ range s, |h * b j| * Eb j + ρ) with hℓ
  have hℓ0 : 0 ≤ ℓ := add_nonneg (mul_nonneg hCN hθ0) (mul_nonneg (by linarith)
    (add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hE0 j)) hρ0))
  set av : ℕ → E := fun n => A (n * h) with hav
  have hstep : ∀ n < N, av (n + 1) = Φ h (av n) := by
    intro n hn
    have hn' : ((n : ℝ) + 1) * h ≤ T := le_trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.succ_le_of_lt hn) hh.le) hN
    simp only [hav]
    rw [← flow_step hL hF hΦ hΦ0 hA (by positivity) hh.le hh₀ (by linarith)]
    congr 1; push_cast; ring
  have h0 : eLpNorm (fun ω => Y 0 ω - av 0) q P ≤ ENNReal.ofReal (C_N * δ) := by
    have : av 0 = A 0 := by simp [hav]
    rw [this]
    exact (hmom 0 s (A 0)).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hδ hCN))
  have hfan := lq_fan (P := P) hq (Real.one_le_exp (by positivity)) hLip hstep
    (fun n => (hYm n).aestronglyMeasurable) (fun n _ => hloc n) N le_rfl
  have hκ0 : 0 ≤ Real.exp (L * h) := (Real.exp_pos _).le
  calc eLpNorm (fun ω => Y N ω - A (N * h)) q P = eLpNorm (fun ω => Y N ω - av N) q P := rfl
    _ ≤ ENNReal.ofReal (Real.exp (L * h)) ^ N *
          (ENNReal.ofReal (C_N * δ) + N * ENNReal.ofReal ℓ) := by
        refine hfan.trans ?_
        gcongr
    _ = ENNReal.ofReal (Real.exp (L * h) ^ N * (C_N * δ + N * ℓ)) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hκ0 N), ENNReal.ofReal_pow hκ0,
          ENNReal.ofReal_add (mul_nonneg hCN hδ0) (mul_nonneg (Nat.cast_nonneg N) hℓ0),
          ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (L * T) * (C_N * δ + N * ℓ)) := by
        apply ENNReal.ofReal_le_ofReal
        have hexp : Real.exp (L * h) ^ N ≤ Real.exp (L * T) := by
          rw [← Real.exp_nat_mul]
          exact Real.exp_le_exp.2 (by nlinarith)
        exact mul_le_mul_of_nonneg_right hexp
          (add_nonneg (mul_nonneg hCN hδ0) (mul_nonneg (Nat.cast_nonneg N) hℓ0))

end RRK


section Thm5

/-- `h^m ≤ h₀^{m-k} h^k` for `0 ≤ h ≤ h₀`, `k ≤ m` (auxiliary; arXiv 2409.06384). -/
theorem pow_le_pow_mul_pow {h h₀ : ℝ} (hh : 0 ≤ h) (hh₀ : h ≤ h₀) {k m : ℕ} (hkm : k ≤ m) :
    h ^ m ≤ h₀ ^ (m - k) * h ^ k := by
  rw [show h ^ m = h ^ (m - k) * h ^ k by rw [← pow_add]; congr 1; omega]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hh₀ _) (pow_nonneg hh _)

/-- The constant `K` of the local error bound in `rrk_refined` (arXiv 2409.06384, Theorem 5): it
depends only on `L`, `h₀`, `C_M`, `C_N`, `C_L`, `C_1`, the stage orders and the tableau. -/
noncomputable def thm5K (L h₀ C_M C_N C_L C_1 : ℝ) (s : ℕ) (γ : ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (b : ℕ → ℝ) : ℝ :=
  let Aa := ∑ j ∈ range s, ∑ l ∈ range j, |a j l|
  let B₂ := C_M + C_L * ∑ j ∈ range s, h₀ ^ (γ j - γ 2)
  let c₁ := L * C_N * (C_M * h₀ + C_L)
  let κ := L * (C_N + 1) * Aa * h₀
  let α₂ := L * C_N * B₂ + L * (C_N + 1) * Aa * c₁
  let G := α₂ * (1 + κ) ^ s * (h₀ + 1)
  C_N * C_M + (C_N + 1) * (|b 1| * c₁ + (∑ i ∈ range (s - 2), |b (i + 2)|) * G + c₁ + G + C_1)

end Thm5


section Thm5Real

/-- Real-number step of the stage majorant for stages `j ≥ 2` (auxiliary; arXiv 2409.06384, proof of
Theorem 11). -/
theorem stage_majorant_step {L C_N B₂ Aa c₁ h₀ α₂ κ X₂ βj Sj : ℝ} (j : ℕ) (hL : 0 ≤ L)
    (hCN : 0 ≤ C_N) (hκ0 : 0 ≤ κ) (hα₂0 : 0 ≤ α₂) (hX₂0 : 0 ≤ X₂) (hβ : βj ≤ B₂ * X₂)
    (hS : Sj ≤ Aa * ((c₁ + h₀ * α₂ * (1 + κ) ^ j) * X₂))
    (hα₂ : α₂ = L * C_N * B₂ + L * (C_N + 1) * Aa * c₁) (hκ : κ = L * (C_N + 1) * Aa * h₀) :
    L * (C_N * βj + (C_N + 1) * Sj) ≤ α₂ * (1 + κ) ^ (j + 1) * X₂ := by
  have hC1 : 0 ≤ C_N + 1 := by linarith
  have h1 : L * (C_N * βj + (C_N + 1) * Sj) ≤
      L * (C_N * (B₂ * X₂) + (C_N + 1) * (Aa * ((c₁ + h₀ * α₂ * (1 + κ) ^ j) * X₂))) := by
    gcongr
  have h2 : L * (C_N * (B₂ * X₂) + (C_N + 1) * (Aa * ((c₁ + h₀ * α₂ * (1 + κ) ^ j) * X₂))) =
      α₂ * X₂ + κ * (α₂ * (1 + κ) ^ j * X₂) := by
    rw [hα₂, hκ]; ring
  have hp : 1 ≤ (1 + κ) ^ j := one_le_pow₀ (by linarith)
  have h3 : α₂ * X₂ + κ * (α₂ * (1 + κ) ^ j * X₂) ≤ α₂ * (1 + κ) ^ (j + 1) * X₂ := by
    have hq : 0 ≤ α₂ * X₂ := mul_nonneg hα₂0 hX₂0
    have : α₂ * (1 + κ) ^ (j + 1) * X₂ =
        α₂ * X₂ * (1 + κ) ^ j + κ * (α₂ * (1 + κ) ^ j * X₂) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hp hq
    linarith
  linarith

/-- Real-number bound for the contribution of stage `1` (paper's stage `2`) (auxiliary; arXiv
2409.06384). -/
theorem stage_one_bound {L C_N C_M C_L h h₀ ε Y : ℝ} (g : ℕ) (hL : 0 ≤ L) (hCN : 0 ≤ C_N)
    (hCM : 0 ≤ C_M) (hCL : 0 ≤ C_L) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hε : 0 ≤ ε) (hY : 0 ≤ Y) :
    h * (L * C_N * (C_M * h * ε + C_L * h ^ (g + 1))) ≤
      L * C_N * (C_M * h₀ + C_L) * (h * ε + Y + h ^ (g + 2)) := by
  have hLC : 0 ≤ L * C_N := mul_nonneg hL hCN
  have e1 : h * (L * C_N * (C_M * h * ε + C_L * h ^ (g + 1))) =
      L * C_N * (C_M * h * (h * ε) + C_L * h ^ (g + 2)) := by ring
  rw [e1]
  have hhε : 0 ≤ h * ε := mul_nonneg hh hε
  have h2 : C_M * h * (h * ε) ≤ C_M * h₀ * (h * ε) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh₀ hCM) hhε
  have h3 : C_M * h * (h * ε) + C_L * h ^ (g + 2) ≤
      (C_M * h₀ + C_L) * (h * ε + Y + h ^ (g + 2)) := by
    have hp : 0 ≤ h ^ (g + 2) := pow_nonneg hh _
    have hh₀0 : 0 ≤ h₀ := hh.trans hh₀
    have := mul_nonneg (mul_nonneg hCM hh₀0) hY
    have := mul_nonneg (mul_nonneg hCM hh₀0) hp
    have := mul_nonneg hCL hhε
    have := mul_nonneg hCL hY
    nlinarith
  rw [mul_assoc (L * C_N)]
  exact mul_le_mul_of_nonneg_left h3 hLC

/-- Real-number form of the local error bound (auxiliary; arXiv 2409.06384, proof of Theorem 5). -/
theorem local_majorant {h ε C_N C_M C_1 b1 c₁ Bb₂ G Y₂ p1 pτ sv : ℝ} (hh : 0 ≤ h) (hε : 0 ≤ ε)
    (hCN : 0 ≤ C_N) (hCM : 0 ≤ C_M) (hC1 : 0 ≤ C_1) (hb1 : 0 ≤ b1) (hc₁ : 0 ≤ c₁)
    (hBb₂ : 0 ≤ Bb₂) (hG : 0 ≤ G) (hY₂ : 0 ≤ Y₂) (hp1 : 0 ≤ p1) (hpτ : 0 ≤ pτ)
    (hsv : sv ≤ h * (b1 * c₁ * (ε + p1) + Bb₂ * G * (ε + Y₂))) :
    C_N * (C_M * h * ε) + (C_N + 1) * (sv + C_1 * (h * pτ)) ≤
      h * (C_N * C_M + (C_N + 1) * (b1 * c₁ + Bb₂ * G + c₁ + G + C_1)) *
        (ε + pτ + b1 * p1 + Bb₂ * Y₂) := by
  have hC : 0 ≤ C_N + 1 := by linarith
  have h1 : C_N * (C_M * h * ε) + (C_N + 1) * (sv + C_1 * (h * pτ)) ≤
      C_N * (C_M * h * ε) + (C_N + 1) * (h * (b1 * c₁ * (ε + p1) + Bb₂ * G * (ε + Y₂)) +
        C_1 * (h * pτ)) := by gcongr
  refine h1.trans ?_
  have key : C_N * C_M * ε + (C_N + 1) * ((b1 * c₁ * (ε + p1) + Bb₂ * G * (ε + Y₂)) + C_1 * pτ)
      ≤ (C_N * C_M + (C_N + 1) * (b1 * c₁ + Bb₂ * G + c₁ + G + C_1)) *
        (ε + pτ + b1 * p1 + Bb₂ * Y₂) := by
    have e : (C_N * C_M + (C_N + 1) * (b1 * c₁ + Bb₂ * G + c₁ + G + C_1)) *
        (ε + pτ + b1 * p1 + Bb₂ * Y₂) - (C_N * C_M * ε + (C_N + 1) *
          ((b1 * c₁ * (ε + p1) + Bb₂ * G * (ε + Y₂)) + C_1 * pτ)) =
        C_N * C_M * (pτ + b1 * p1 + Bb₂ * Y₂) +
        (C_N + 1) * ((b1 * c₁ + Bb₂ * G) * (pτ + b1 * p1 + Bb₂ * Y₂) +
          c₁ * (ε + pτ + Bb₂ * Y₂) + G * (ε + pτ + b1 * p1) + C_1 * (ε + b1 * p1 + Bb₂ * Y₂)) := by
      ring
    have : 0 ≤ C_N * C_M * (pτ + b1 * p1 + Bb₂ * Y₂) +
        (C_N + 1) * ((b1 * c₁ + Bb₂ * G) * (pτ + b1 * p1 + Bb₂ * Y₂) +
          c₁ * (ε + pτ + Bb₂ * Y₂) + G * (ε + pτ + b1 * p1) + C_1 * (ε + b1 * p1 + Bb₂ * Y₂)) := by
      positivity
    linarith
  have := mul_le_mul_of_nonneg_left key hh
  calc C_N * (C_M * h * ε) + (C_N + 1) * (h * (b1 * c₁ * (ε + p1) + Bb₂ * G * (ε + Y₂)) +
        C_1 * (h * pτ))
      = h * (C_N * C_M * ε + (C_N + 1) * ((b1 * c₁ * (ε + p1) + Bb₂ * G * (ε + Y₂)) +
        C_1 * pτ)) := by ring
    _ ≤ _ := by rw [mul_assoc h]; exact this

/-- Absorption of the error terms into `h^{min(τ, γ₂+1)}` (auxiliary; arXiv 2409.06384, Theorem 5,
case `b₂ ≠ 0`). -/
theorem W_le_case1 {h h₀ ε b1 Bb₂ : ℝ} {τ g1 g2 : ℕ} (hh : 0 < h) (hh₀ : h ≤ h₀) (hb1 : 0 ≤ b1)
    (hBb₂ : 0 ≤ Bb₂) (hcase : Bb₂ ≠ 0 → g1 ≤ g2) :
    ε + h ^ τ + b1 * h ^ (g1 + 1) + Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2)) ≤
      ε + (h₀ ^ (τ - min τ (g1 + 1)) + h₀ ^ (g1 + 1 - min τ (g1 + 1)) *
        (b1 + Bb₂ * (h₀ ^ (g2 - g1) + h₀))) * h ^ (min τ (g1 + 1)) := by
  set g := min τ (g1 + 1)
  have hh₀0 : 0 ≤ h₀ := hh.le.trans hh₀
  have h1 : h ^ τ ≤ h₀ ^ (τ - g) * h ^ g := pow_le_pow_mul_pow hh.le hh₀ (min_le_left _ _)
  have h2 : h ^ (g1 + 1) ≤ h₀ ^ (g1 + 1 - g) * h ^ g :=
    pow_le_pow_mul_pow hh.le hh₀ (min_le_right _ _)
  have h3 : Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2)) ≤ Bb₂ * (h₀ ^ (g2 - g1) + h₀) * h ^ (g1 + 1) := by
    rcases eq_or_ne Bb₂ 0 with h0 | h0
    · rw [h0]; simp
    · have hg := hcase h0
      have k1 : h ^ (g2 + 1) ≤ h₀ ^ (g2 - g1) * h ^ (g1 + 1) := by
        have := pow_le_pow_mul_pow hh.le hh₀ (show g1 + 1 ≤ g2 + 1 by omega)
        rwa [show g2 + 1 - (g1 + 1) = g2 - g1 by omega] at this
      have k2 : h ^ (g1 + 2) ≤ h₀ * h ^ (g1 + 1) := by
        rw [show g1 + 2 = (g1 + 1) + 1 by omega, pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_right hh₀ (pow_nonneg hh.le _)
      have := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hBb₂
      calc Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2))
          ≤ Bb₂ * (h₀ ^ (g2 - g1) * h ^ (g1 + 1) + h₀ * h ^ (g1 + 1)) := this
        _ = _ := by ring
  have h4 : b1 * h ^ (g1 + 1) + Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2)) ≤
      (b1 + Bb₂ * (h₀ ^ (g2 - g1) + h₀)) * (h₀ ^ (g1 + 1 - g) * h ^ g) := by
    have hc : 0 ≤ b1 + Bb₂ * (h₀ ^ (g2 - g1) + h₀) :=
      add_nonneg hb1 (mul_nonneg hBb₂ (add_nonneg (pow_nonneg hh₀0 _) hh₀0))
    calc b1 * h ^ (g1 + 1) + Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2))
        ≤ b1 * h ^ (g1 + 1) + Bb₂ * (h₀ ^ (g2 - g1) + h₀) * h ^ (g1 + 1) := by linarith
      _ = (b1 + Bb₂ * (h₀ ^ (g2 - g1) + h₀)) * h ^ (g1 + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hc
  calc ε + h ^ τ + b1 * h ^ (g1 + 1) + Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2))
      ≤ ε + h₀ ^ (τ - g) * h ^ g + (b1 + Bb₂ * (h₀ ^ (g2 - g1) + h₀)) *
          (h₀ ^ (g1 + 1 - g) * h ^ g) := by linarith
    _ = _ := by ring

/-- Absorption of the error terms into `h^{min(τ, γ₃+1, γ₂+2)}` (auxiliary; arXiv 2409.06384,
Theorem 5, case `b₂ = 0`). -/
theorem W_le_case2 {h h₀ ε Bb₂ : ℝ} {τ g1 g2 : ℕ} (hh : 0 < h) (hh₀ : h ≤ h₀) (hBb₂ : 0 ≤ Bb₂) :
    ε + h ^ τ + 0 * h ^ (g1 + 1) + Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2)) ≤
      ε + (h₀ ^ (τ - min τ (min (g2 + 1) (g1 + 2))) +
        Bb₂ * (h₀ ^ (g2 + 1 - min τ (min (g2 + 1) (g1 + 2))) +
          h₀ ^ (g1 + 2 - min τ (min (g2 + 1) (g1 + 2))))) *
        h ^ (min τ (min (g2 + 1) (g1 + 2))) := by
  set g := min τ (min (g2 + 1) (g1 + 2))
  have h1 : h ^ τ ≤ h₀ ^ (τ - g) * h ^ g := pow_le_pow_mul_pow hh.le hh₀ (min_le_left _ _)
  have h2 : h ^ (g2 + 1) ≤ h₀ ^ (g2 + 1 - g) * h ^ g :=
    pow_le_pow_mul_pow hh.le hh₀ ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : h ^ (g1 + 2) ≤ h₀ ^ (g1 + 2 - g) * h ^ g :=
    pow_le_pow_mul_pow hh.le hh₀ ((min_le_right _ _).trans (min_le_right _ _))
  have := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hBb₂
  calc ε + h ^ τ + 0 * h ^ (g1 + 1) + Bb₂ * (h ^ (g2 + 1) + h ^ (g1 + 2))
      ≤ ε + h₀ ^ (τ - g) * h ^ g +
          Bb₂ * (h₀ ^ (g2 + 1 - g) * h ^ g + h₀ ^ (g1 + 2 - g) * h ^ g) := by
        linarith
    _ = _ := by ring

/-- `δ + (ε + D x) ≤ max(1, D)(δ + ε + x)` (auxiliary; arXiv 2409.06384). -/
theorem le_max_one_mul {δ ε D x : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    δ + (ε + D * x) ≤ max 1 D * (δ + ε + x) := by
  have h1 : 1 ≤ max 1 D := le_max_left _ _
  have h2 : D ≤ max 1 D := le_max_right _ _
  have := mul_le_mul_of_nonneg_right h1 (add_nonneg hδ hε)
  have := mul_le_mul_of_nonneg_right h2 hx
  nlinarith

/-- A uniform stage majorant (auxiliary; arXiv 2409.06384, Theorem 11): if every `β j ≤ B X`, then
`Eb j = L C_N B (1 + κ)^{j+1} X`, `κ = L (C_N + 1) (∑ |a|) h₀`, satisfies the stage recursion. -/
theorem uniform_majorant {L C_N B h h₀ X : ℝ} (hL : 0 ≤ L) (hCN : 0 ≤ C_N) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hX : 0 ≤ X) (a : ℕ → ℕ → ℝ) (s : ℕ) {β : ℕ → ℝ}
    (hβ : ∀ j < s, β j ≤ B * X) :
    ∀ j < s, L * (C_N * β j + (C_N + 1) * ∑ l : Fin j, |h * a j l| *
      (L * C_N * B * (1 + L * (C_N + 1) * (∑ j ∈ range s, ∑ l ∈ range j, |a j l|) * h₀) ^
        ((l : ℕ) + 1) * X)) ≤
      L * C_N * B * (1 + L * (C_N + 1) * (∑ j ∈ range s, ∑ l ∈ range j, |a j l|) * h₀) ^
        (j + 1) * X := by
  set Aa := ∑ j ∈ range s, ∑ l ∈ range j, |a j l| with hAa
  set κ := L * (C_N + 1) * Aa * h₀ with hκ
  set α := L * C_N * B with hα
  have hAa0 : 0 ≤ Aa := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hh₀0 : 0 ≤ h₀ := hh.trans hh₀
  have hκ0 : 0 ≤ κ := mul_nonneg (mul_nonneg (mul_nonneg hL (by linarith)) hAa0) hh₀0
  have hα0 : 0 ≤ α := mul_nonneg (mul_nonneg hL hCN) hB
  intro j hj
  refine stage_majorant_step (c₁ := 0) (Aa := Aa) j hL hCN hκ0 hα0 hX (hβ j hj) ?_ (by ring) hκ
  have hterm : ∀ l : Fin j, |h * a j l| * (α * (1 + κ) ^ ((l : ℕ) + 1) * X) ≤
      |a j l| * ((0 + h₀ * α * (1 + κ) ^ j) * X) := by
    intro l
    rw [abs_mul, abs_of_nonneg hh, mul_comm h, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hpow : (1 + κ) ^ ((l : ℕ) + 1) ≤ (1 + κ) ^ j :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have t1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hα0) hX
    have t2 := mul_le_mul hh₀ t1 (mul_nonneg (mul_nonneg hα0 (pow_nonneg (by linarith) _)) hX)
      hh₀0
    calc h * (α * (1 + κ) ^ ((l : ℕ) + 1) * X) ≤ h₀ * (α * (1 + κ) ^ j * X) := t2
      _ = (0 + h₀ * α * (1 + κ) ^ j) * X := by ring
  refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by
    have := pow_nonneg (show (0 : ℝ) ≤ 1 + κ by linarith) j
    positivity) hX)
  rw [Fin.sum_univ_eq_sum_range (fun l => |a j l|) j, hAa]
  exact Finset.single_le_sum (f := fun j => ∑ l ∈ range j, |a j l|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 hj)

end Thm5Real


section Thm5Main

variable {Ω K E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- **Theorem 11 and the refined error bound behind Theorem 5 of arXiv 2409.06384.** For the
randomized low-rank RK method with `s ≥ 2` stages (one randomized map `R` with values in `S` for all
stages and for the final truncation, independent sketches `ξ (n, j)`, moment assumption (7)),
Lipschitz `F`, Assumption 3, nodes `c_j = ∑_l a_{jl} ∈ [0, 1]`, stage orders `‖Z̃_j - Φ^{c_j h}(Y)‖
≤ C_L h^{γ_j+1}` (`j ≥ 1`, i.e. the paper's stages `≥ 2`, ordered) and classical order `τ`, `‖Y_N -
A(Nh)‖_{L^q} ≤ e^{LT} max(C_N, T K) (δ + ε + h^τ + |b₁| h^{γ₁+1} + (∑_{j≥2} |b_j|) (h^{γ₂+1} +
h^{γ₁+2}))` with `K = thm5K …` (0-indexed stages: `b₁, γ₁, γ₂` are the paper's `b₂, γ₂, γ₃`). The
stage recursion is Theorem 11; stage errors are `0` at stage `0`, `O(hε + h^{γ₁+1})` at stage `1`
and `O(hε + h^{γ₂+1} + h^{γ₁+2})` at later stages. -/
theorem rrk_refined {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {S : Set E} {C_M ε : ℝ} (hCM : 0 ≤ C_M) (hε : 0 ≤ ε)
    (happrox : ∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, Metric.infDist (Φ t Y) S ≤ C_M * t * ε)
    {T : ℝ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A 0 T) {δ : ℝ}
    (hδ : Metric.infDist (A 0) S ≤ δ)
    {R : K → E → E} (hR : Measurable (Function.uncurry R)) (hRS : ∀ k z, R k z ∈ S)
    {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ × ℕ → Ω → K} (hξ : ∀ p, Measurable (ξ p))
    (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom : ∀ p z, eLpNorm (fun ω => R (ξ p ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z S))
    {s : ℕ} (hs : 2 ≤ s) {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    (hc : ∀ j < s, 0 ≤ ∑ l : Fin j, a j l ∧ ∑ l : Fin j, a j l ≤ 1)
    {γ : ℕ → ℕ} (hγ : ∀ j k, 1 ≤ j → j ≤ k → k < s → γ j ≤ γ k) {C_L : ℝ} (hCL : 0 ≤ C_L)
    (hstage : ∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, ∀ j, 1 ≤ j → j < s →
      ‖rkZ F (fun _ => id) a t Y j - Φ ((∑ l : Fin j, a j l) * t) Y‖ ≤ C_L * t ^ (γ j + 1))
    {τ : ℕ} {C_1 : ℝ} (hC1 : 0 ≤ C_1)
    (horder : ∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀,
      ‖(Y + t • ∑ j ∈ range s, b j • rkK F (fun _ => id) a t Y j) - Φ t Y‖ ≤ C_1 * t ^ (τ + 1))
    {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) {N : ℕ} (hN : N * h ≤ T) :
    eLpNorm (fun ω => rrkIter F (fun _ => R) a b s h ξ (A 0) N ω - A (N * h)) q P ≤
      ENNReal.ofReal (Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) *
        (δ + (ε + h ^ τ + |b 1| * h ^ (γ 1 + 1) +
          (∑ i ∈ range (s - 2), |b (i + 2)|) * (h ^ (γ 2 + 1) + h ^ (γ 1 + 2))))) := by
  have hh₀0 : 0 ≤ h₀ := hh.le.trans hh₀
  have hT0 : 0 ≤ T := le_trans (by positivity) hN
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg.trans hδ
  obtain ⟨Aa, hAa⟩ : ∃ x : ℝ, x = ∑ j ∈ range s, ∑ l ∈ range j, |a j l| := ⟨_, rfl⟩
  obtain ⟨Hs2, hHs2⟩ : ∃ x : ℝ, x = ∑ j ∈ range s, h₀ ^ (γ j - γ 2) := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ x : ℝ, x = C_M + C_L * Hs2 := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ x : ℝ, x = L * C_N * (C_M * h₀ + C_L) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ x : ℝ, x = L * (C_N + 1) * Aa * h₀ := ⟨_, rfl⟩
  obtain ⟨α₂, hα₂⟩ : ∃ x : ℝ, x = L * C_N * B₂ + L * (C_N + 1) * Aa * c₁ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ x : ℝ, x = α₂ * (1 + κ) ^ s * (h₀ + 1) := ⟨_, rfl⟩
  obtain ⟨Bb₂, hBb₂⟩ : ∃ x : ℝ, x = ∑ i ∈ range (s - 2), |b (i + 2)| := ⟨_, rfl⟩
  have hK : thm5K L h₀ C_M C_N C_L C_1 s γ a b =
      C_N * C_M + (C_N + 1) * (|b 1| * c₁ + Bb₂ * G + c₁ + G + C_1) := by
    subst hAa hHs2 hB₂ hc₁ hκ hα₂ hG hBb₂; rfl
  rw [hK, ← hBb₂]
  obtain ⟨X₂, hX₂⟩ : ∃ x : ℝ, x = h * ε + h ^ (γ 2 + 1) + h ^ (γ 1 + 2) := ⟨_, rfl⟩
  have hAa0 : 0 ≤ Aa := hAa ▸ Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hHs20 : 0 ≤ Hs2 := hHs2 ▸ Finset.sum_nonneg fun _ _ => pow_nonneg hh₀0 _
  have hB₂0 : 0 ≤ B₂ := hB₂ ▸ add_nonneg hCM (mul_nonneg hCL hHs20)
  have hc₁0 : 0 ≤ c₁ :=
    hc₁ ▸ mul_nonneg (mul_nonneg hL hCN) (add_nonneg (mul_nonneg hCM hh₀0) hCL)
  have hκ0 : 0 ≤ κ := hκ ▸ mul_nonneg (mul_nonneg (mul_nonneg hL (by linarith)) hAa0) hh₀0
  have hα₂0 : 0 ≤ α₂ := hα₂ ▸ add_nonneg (mul_nonneg (mul_nonneg hL hCN) hB₂0)
    (mul_nonneg (mul_nonneg (mul_nonneg hL (by linarith)) hAa0) hc₁0)
  have hG0 : 0 ≤ G := hG ▸ mul_nonneg (mul_nonneg hα₂0 (pow_nonneg (by linarith) _)) (by linarith)
  have hBb₂0 : 0 ≤ Bb₂ := hBb₂ ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hX₂0 : 0 ≤ X₂ := hX₂ ▸ by positivity
  obtain ⟨β, hβ_def⟩ : ∃ β : ℕ → ℝ, β = fun j => if j = 0 then 0 else
      C_M * ((∑ l : Fin j, a j l) * h) * ε + C_L * h ^ (γ j + 1) := ⟨_, rfl⟩
  obtain ⟨Eb, hEb_def⟩ : ∃ Eb : ℕ → ℝ, Eb = fun j => if j = 0 then 0 else if j = 1 then
      L * C_N * (C_M * h * ε + C_L * h ^ (γ 1 + 1)) else α₂ * (1 + κ) ^ (j + 1) * X₂ :=
    ⟨_, rfl⟩
  have hEb0 : Eb 0 = 0 := by rw [hEb_def]; simp
  have hEb1 : Eb 1 = L * C_N * (C_M * h * ε + C_L * h ^ (γ 1 + 1)) := by rw [hEb_def]; simp
  have hEbj : ∀ j, 2 ≤ j → Eb j = α₂ * (1 + κ) ^ (j + 1) * X₂ := by
    intro j hj
    rw [hEb_def]
    simp only [show j ≠ 0 by omega, show j ≠ 1 by omega, ite_false]
  have hβj : ∀ j, 1 ≤ j → β j = C_M * ((∑ l : Fin j, a j l) * h) * ε + C_L * h ^ (γ j + 1) := by
    intro j hj
    rw [hβ_def]
    simp only [show j ≠ 0 by omega, ite_false]
  -- best approximation errors of the classical stages
  have hβ : ∀ y ∈ S, ∀ j < s, Metric.infDist (rkZ F (fun _ => id) a h y j) S ≤ β j := by
    intro y hy j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hβ_def]; simp [rkZ, Metric.infDist_zero_of_mem hy]
    · rw [hβj j hj0]
      have h1 := Metric.infDist_le_infDist_add_dist (x := rkZ F (fun _ => id) a h y j)
        (y := Φ ((∑ l : Fin j, a j l) * h) y) (s := S)
      rw [dist_eq_norm] at h1
      have h2 := hstage y hy h ⟨hh, hh₀⟩ j hj0 hj
      have h3 : Metric.infDist (Φ ((∑ l : Fin j, a j l) * h) y) S ≤
          C_M * ((∑ l : Fin j, a j l) * h) * ε := by
        rcases (hc j hj).1.eq_or_lt with h0 | hpos
        · rw [← h0, zero_mul, hΦ0, Metric.infDist_zero_of_mem hy]; simp
        · refine happrox y hy _ ⟨mul_pos hpos hh, ?_⟩
          calc (∑ l : Fin j, a j l) * h ≤ 1 * h :=
                mul_le_mul_of_nonneg_right (hc j hj).2 hh.le
            _ ≤ h₀ := by linarith
      linarith
  have hE1 : 0 ≤ C_M * h * ε + C_L * h ^ (γ 1 + 1) :=
    add_nonneg (mul_nonneg (mul_nonneg hCM hh.le) hε) (mul_nonneg hCL (pow_nonneg hh.le _))
  have hE0 : ∀ j, 0 ≤ Eb j := by
    intro j
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · rw [hEb0]
      · rw [hEb1]; exact mul_nonneg (mul_nonneg hL hCN) hE1
    · rw [hEbj j hj]; exact mul_nonneg (mul_nonneg hα₂0 (pow_nonneg (by linarith) _)) hX₂0
  have hE : ∀ j < s, L * (C_N * β j + (C_N + 1) * ∑ l : Fin j, |h * a j l| * Eb l) ≤ Eb j := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · rw [hβ_def, hEb0]; simp
      · rw [hβj 1 le_rfl, hEb1]
        have hs0 : ∑ l : Fin 1, |h * a 1 l| * Eb l = 0 := by simp [hEb0]
        rw [hs0, mul_zero, add_zero]
        have hc1 := (hc 1 hj).2
        have e : C_M * ((∑ l : Fin 1, a 1 l) * h) * ε = (C_M * h * ε) * (∑ l : Fin 1, a 1 l) := by
          ring
        have h1 := mul_le_mul_of_nonneg_left hc1 (mul_nonneg (mul_nonneg hCM hh.le) hε)
        rw [mul_one] at h1
        rw [e, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hL hCN)
    · rw [hEbj j hj2]
      refine stage_majorant_step j hL hCN hκ0 hα₂0 hX₂0 ?_ ?_ hα₂ hκ
      · rw [hβj j (by omega)]
        have hγ2 : γ 2 ≤ γ j := hγ 2 j (by norm_num) hj2 hj
        have hp : h ^ (γ j + 1) ≤ h₀ ^ (γ j - γ 2) * h ^ (γ 2 + 1) := by
          have := pow_le_pow_mul_pow hh.le hh₀ (show γ 2 + 1 ≤ γ j + 1 by omega)
          rwa [show γ j + 1 - (γ 2 + 1) = γ j - γ 2 by omega] at this
        have hHs : h₀ ^ (γ j - γ 2) ≤ Hs2 := hHs2 ▸ Finset.single_le_sum
          (f := fun j => h₀ ^ (γ j - γ 2)) (fun _ _ => pow_nonneg hh₀0 _) (Finset.mem_range.2 hj)
        have hcj := (hc j hj).2
        have h1 : C_M * ((∑ l : Fin j, a j l) * h) * ε ≤ C_M * (h * ε) := by
          have e : C_M * ((∑ l : Fin j, a j l) * h) * ε = (C_M * h * ε) * (∑ l : Fin j, a j l) := by
            ring
          rw [e]
          have := mul_le_mul_of_nonneg_left hcj (mul_nonneg (mul_nonneg hCM hh.le) hε)
          linarith
        have h2 : C_L * h ^ (γ j + 1) ≤ C_L * Hs2 * h ^ (γ 2 + 1) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left (hp.trans ?_) hCL
          exact mul_le_mul_of_nonneg_right hHs (pow_nonneg hh.le _)
        have e2 : B₂ * X₂ - (C_M * (h * ε) + C_L * Hs2 * h ^ (γ 2 + 1)) =
            C_M * (h ^ (γ 2 + 1) + h ^ (γ 1 + 2)) + C_L * Hs2 * (h * ε + h ^ (γ 1 + 2)) := by
          rw [hB₂, hX₂]; ring
        have h3 : 0 ≤ C_M * (h ^ (γ 2 + 1) + h ^ (γ 1 + 2)) + C_L * Hs2 * (h * ε + h ^ (γ 1 + 2)) :=
          add_nonneg (mul_nonneg hCM (by positivity))
            (mul_nonneg (mul_nonneg hCL hHs20) (by positivity))
        linarith
      · have hterm : ∀ l : Fin j, |h * a j l| * Eb l ≤
            |a j l| * ((c₁ + h₀ * α₂ * (1 + κ) ^ j) * X₂) := by
          intro l
          have hM0 : 0 ≤ h₀ * α₂ * (1 + κ) ^ j * X₂ :=
            mul_nonneg (mul_nonneg (mul_nonneg hh₀0 hα₂0) (pow_nonneg (by linarith) _)) hX₂0
          rw [abs_mul, abs_of_pos hh, mul_comm h, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rcases Nat.lt_or_ge (l : ℕ) 2 with hl | hl
          · interval_cases hlv : (l : ℕ)
            · rw [hEb0, mul_zero]
              exact mul_nonneg (add_nonneg hc₁0 (mul_nonneg (mul_nonneg hh₀0 hα₂0)
                (pow_nonneg (by linarith) _))) hX₂0
            · rw [hEb1]
              have := stage_one_bound (γ 1) hL hCN hCM hCL hh.le hh₀ hε
                (pow_nonneg hh.le (γ 2 + 1)) (h₀ := h₀)
              rw [← hc₁, ← hX₂] at this
              rw [add_mul]
              exact this.trans (le_add_of_nonneg_right hM0)
          · rw [hEbj l hl]
            have hpow : (1 + κ) ^ ((l : ℕ) + 1) ≤ (1 + κ) ^ j :=
              pow_le_pow_right₀ (by linarith) (by omega)
            have h1 : h * (α₂ * (1 + κ) ^ ((l : ℕ) + 1) * X₂) ≤ h₀ * α₂ * (1 + κ) ^ j * X₂ := by
              have := mul_le_mul_of_nonneg_left hpow hα₂0
              have := mul_le_mul_of_nonneg_right this hX₂0
              have := mul_le_mul this hh₀ hh.le (mul_nonneg (mul_nonneg hα₂0
                (pow_nonneg (by linarith) _)) hX₂0)
              linarith
            rw [add_mul]
            exact h1.trans (le_add_of_nonneg_left (mul_nonneg hc₁0 hX₂0))
        refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (add_nonneg hc₁0 (mul_nonneg
          (mul_nonneg hh₀0 hα₂0) (pow_nonneg (by linarith) _))) hX₂0)
        rw [Fin.sum_univ_eq_sum_range (fun l => |a j l|) j, hAa]
        exact Finset.single_le_sum (f := fun j => ∑ l ∈ range j, |a j l|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 hj)
  have hglob := rrk_global (P := P) hL hF hΦ hΦ0 hA (R := fun _ => R) (fun _ => hR)
    (S := fun _ => S) s hRS hCN hξ hind hq hqt (fun n j z => hmom (n, j) z) a b hh hh₀ hδ hβ
    (θ := C_M * h * ε) (ρ := C_1 * h ^ (τ + 1)) (fun y hy => happrox y hy h ⟨hh, hh₀⟩)
    (fun y hy => horder y hy h ⟨hh, hh₀⟩) hE0 hE hN
  refine hglob.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the weighted sum of stage errors
  set Y₂ := h ^ (γ 2 + 1) + h ^ (γ 1 + 2) with hY₂
  have hY₂0 : 0 ≤ Y₂ := by positivity
  have hsum : ∑ j ∈ range s, |h * b j| * Eb j ≤
      h * (|b 1| * c₁ * (ε + h ^ (γ 1 + 1)) + Bb₂ * G * (ε + Y₂)) := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ', hEb0, mul_zero, add_zero, zero_add]
    have hBb : Bb₂ = ∑ i ∈ range s', |b (i + 2)| := by rw [hBb₂]; simp
    have h1 : |h * b 1| * Eb 1 ≤ h * (|b 1| * c₁ * (ε + h ^ (γ 1 + 1))) := by
      rw [hEb1, abs_mul, abs_of_pos hh, hc₁]
      have hp : 0 ≤ h ^ (γ 1 + 1) := pow_nonneg hh.le _
      have k : C_M * h * ε + C_L * h ^ (γ 1 + 1) ≤ (C_M * h₀ + C_L) * (ε + h ^ (γ 1 + 1)) := by
        have t1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh₀ hCM) hε
        have t2 := mul_nonneg (mul_nonneg hCM hh₀0) hp
        have t3 := mul_nonneg hCL hε
        have e : (C_M * h₀ + C_L) * (ε + h ^ (γ 1 + 1)) =
            C_M * h₀ * ε + C_M * h₀ * h ^ (γ 1 + 1) + C_L * ε + C_L * h ^ (γ 1 + 1) := by ring
        rw [e]
        linarith only [t1, t2, t3]
      have k2 := mul_le_mul_of_nonneg_left k (mul_nonneg hL hCN)
      have k3 := mul_le_mul_of_nonneg_left k2 (mul_nonneg hh.le (abs_nonneg (b 1)))
      calc h * |b 1| * (L * C_N * (C_M * h * ε + C_L * h ^ (γ 1 + 1)))
          ≤ h * |b 1| * (L * C_N * ((C_M * h₀ + C_L) * (ε + h ^ (γ 1 + 1)))) := k3
        _ = h * (|b 1| * (L * C_N * (C_M * h₀ + C_L)) * (ε + h ^ (γ 1 + 1))) := by ring
    have h2 : ∀ i ∈ range s', |h * b (i + 1 + 1)| * Eb (i + 1 + 1) ≤
        h * |b (i + 2)| * (G * (ε + Y₂)) := by
      intro i hi
      rw [hEbj (i + 1 + 1) (by omega), abs_mul, abs_of_pos hh]
      have hi' : i < s' := Finset.mem_range.1 hi
      have hpow : (1 + κ) ^ (i + 1 + 1 + 1) ≤ (1 + κ) ^ (s' + 2) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have hX : X₂ ≤ (h₀ + 1) * (ε + Y₂) := by
        have t1 := mul_le_mul_of_nonneg_right hh₀ hε
        have t2 := mul_nonneg hh₀0 hY₂0
        have e : (h₀ + 1) * (ε + Y₂) = h₀ * ε + h₀ * Y₂ + ε + Y₂ := by ring
        rw [e, hX₂]
        linarith only [t1, t2, hε, hY₂]
      have k : α₂ * (1 + κ) ^ (i + 1 + 1 + 1) * X₂ ≤ G * (ε + Y₂) := by
        rw [hG]
        have t1 := mul_le_mul_of_nonneg_left hpow hα₂0
        have t2 := mul_le_mul t1 hX hX₂0 (mul_nonneg hα₂0 (pow_nonneg (by linarith) _))
        calc α₂ * (1 + κ) ^ (i + 1 + 1 + 1) * X₂
            ≤ α₂ * (1 + κ) ^ (s' + 2) * ((h₀ + 1) * (ε + Y₂)) := t2
          _ = α₂ * (1 + κ) ^ (s' + 2) * (h₀ + 1) * (ε + Y₂) := by ring
      have k2 := mul_le_mul_of_nonneg_left k (mul_nonneg hh.le (abs_nonneg (b (i + 1 + 1))))
      calc h * |b (i + 1 + 1)| * (α₂ * (1 + κ) ^ (i + 1 + 1 + 1) * X₂)
          ≤ h * |b (i + 1 + 1)| * (G * (ε + Y₂)) := k2
        _ = h * |b (i + 2)| * (G * (ε + Y₂)) := rfl
    have h3 := Finset.sum_le_sum h2
    have h4 : ∑ i ∈ range s', h * |b (i + 2)| * (G * (ε + Y₂)) = h * (Bb₂ * G * (ε + Y₂)) := by
      rw [hBb, ← Finset.sum_mul, ← Finset.mul_sum]; ring
    rw [h4] at h3
    have h5 := add_le_add h3 h1
    refine le_trans h5 (le_of_eq ?_)
    ring
  have hloc := local_majorant (pτ := h ^ τ) hh.le hε hCN hCM hC1 (abs_nonneg (b 1)) hc₁0 hBb₂0 hG0
    hY₂0 (pow_nonneg hh.le _) (pow_nonneg hh.le _) hsum
  rw [show h * h ^ τ = h ^ (τ + 1) by ring] at hloc
  set Kc := C_N * C_M + (C_N + 1) * (|b 1| * c₁ + Bb₂ * G + c₁ + G + C_1) with hKc
  set W := ε + h ^ τ + |b 1| * h ^ (γ 1 + 1) + Bb₂ * Y₂ with hW
  have hK0 : 0 ≤ Kc := add_nonneg (mul_nonneg hCN hCM) (mul_nonneg (by linarith)
    (by have := abs_nonneg (b 1); positivity))
  have hW0 : 0 ≤ W := by have := abs_nonneg (b 1); positivity
  have hNl : (N : ℝ) * (C_N * (C_M * h * ε) + (C_N + 1) * (∑ j ∈ range s, |h * b j| * Eb j +
      C_1 * h ^ (τ + 1))) ≤ T * Kc * W := by
    calc (N : ℝ) * (C_N * (C_M * h * ε) + (C_N + 1) * (∑ j ∈ range s, |h * b j| * Eb j +
          C_1 * h ^ (τ + 1))) ≤ N * (h * Kc * W) :=
          mul_le_mul_of_nonneg_left hloc (Nat.cast_nonneg N)
      _ = (N * h) * (Kc * W) := by ring
      _ ≤ T * (Kc * W) := mul_le_mul_of_nonneg_right hN (mul_nonneg hK0 hW0)
      _ = T * Kc * W := by ring
  have hmax1 : C_N ≤ max C_N (T * Kc) := le_max_left _ _
  have hmax2 : T * Kc ≤ max C_N (T * Kc) := le_max_right _ _
  have hfin : C_N * δ + T * Kc * W ≤ max C_N (T * Kc) * (δ + W) := by
    have t1 := mul_le_mul_of_nonneg_right hmax1 hδ0
    have t2 := mul_le_mul_of_nonneg_right hmax2 hW0
    exact (add_le_add t1 t2).trans (le_of_eq (mul_add _ _ _).symm)
  have hexp := (Real.exp_pos (L * T)).le
  calc Real.exp (L * T) * (C_N * δ + N * (C_N * (C_M * h * ε) +
        (C_N + 1) * (∑ j ∈ range s, |h * b j| * Eb j + C_1 * h ^ (τ + 1))))
      ≤ Real.exp (L * T) * (max C_N (T * Kc) * (δ + W)) :=
        mul_le_mul_of_nonneg_left (by linarith) hexp
    _ = _ := by ring

end Thm5Main


section Thm5Statements

/-- **Theorem 5 of arXiv 2409.06384** (randomized low-rank Runge–Kutta, case `b₂ ≠ 0`, which bounds
all cases). There is `C > 0` depending only on `L, T, h₀, C_M, C_N, C_L, C_1` and the method `(s, τ,
γ, a, b)` such that for every probability space, sketch space, real normed space `E`
(finite-dimensional in the application: Borel, second countable), set `S`, Lipschitz `F` with flow
`Φ`, approximability (6) on `S`, randomized map `R` with values in `S` satisfying (7) with
independent sketches, stage orders `γ` and RK order `τ` (as hypotheses on `S`), `0 < h ≤ h₀` and `N
h ≤ T`: `‖Y_N - A(Nh)‖_{L^q} ≤ C (δ + ε + h^{min(τ, γ₂+1)})` (paper indexing; Lean's `γ 1`),
together with the tail bound `P(‖Y_N - A(Nh)‖ ≥ C η (δ + ε + h^γ)) ≤ η^{-q}`.

Differences: as in `thm3`, (7) replaces the Gaussian Nyström Theorem 2; the RK order `τ` and stage
orders are hypotheses on `S` (the paper derives them from Assumption 2 and classical RK theory); the
nodes `c_j` are assumed in `[0, 1]` so that Assumption 3 applies at `c_j h ≤ h₀`; the paper's `Y₀ =
𝒩(A₀)` uses the sketch `ξ (0, s)`. -/
theorem thm5 (L T h₀ C_M C_N C_L C_1 : ℝ) (s τ : ℕ) (γ : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hL : 0 ≤ L) (hCM : 0 ≤ C_M) (hCN : 0 ≤ C_N) (hCL : 0 ≤ C_L) (hC1 : 0 ≤ C_1) (hs : 2 ≤ s)
    (hc : ∀ j < s, 0 ≤ ∑ l : Fin j, a j l ∧ ∑ l : Fin j, a j l ≤ 1)
    (hγ : ∀ j k, 1 ≤ j → j ≤ k → k < s → γ j ≤ γ k) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω K E : Type*} [MeasurableSpace Ω] [MeasurableSpace K] [NormedAddCommGroup E]
      [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      (P : Measure Ω) [IsProbabilityMeasure P] (F : E → E) (Φ : ℝ → E → E) (S : Set E) (ε : ℝ)
      (A : ℝ → E) (δ : ℝ) (R : K → E → E) (ξ : ℕ × ℕ → Ω → K) (q : ℝ≥0∞) (h : ℝ) (N : ℕ),
      (∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) →
      (∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀) → (∀ Y, Φ 0 Y = Y) →
      0 ≤ ε → (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, Metric.infDist (Φ t Y) S ≤ C_M * t * ε) →
      ODESolution (fun _ => F) A 0 T → Metric.infDist (A 0) S ≤ δ →
      Measurable (Function.uncurry R) → (∀ k z, R k z ∈ S) → (∀ p, Measurable (ξ p)) →
      iIndepFun ξ P → 1 ≤ q → q ≠ ∞ →
      (∀ p z, eLpNorm (fun ω => R (ξ p ω) z - z) q P ≤
        ENNReal.ofReal (C_N * Metric.infDist z S)) →
      (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, ∀ j, 1 ≤ j → j < s →
        ‖rkZ F (fun _ => id) a t Y j - Φ ((∑ l : Fin j, a j l) * t) Y‖ ≤ C_L * t ^ (γ j + 1)) →
      (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀,
        ‖(Y + t • ∑ j ∈ range s, b j • rkK F (fun _ => id) a t Y j) - Φ t Y‖ ≤
          C_1 * t ^ (τ + 1)) →
      0 < h → h ≤ h₀ → N * h ≤ T →
      eLpNorm (fun ω => rrkIter F (fun _ => R) a b s h ξ (A 0) N ω - A (N * h)) q P ≤
          ENNReal.ofReal (C * (δ + ε + h ^ min τ (γ 1 + 1))) ∧
        ∀ η : ℝ, 0 < η → P {ω | C * η * (δ + ε + h ^ min τ (γ 1 + 1)) ≤
          ‖rrkIter F (fun _ => R) a b s h ξ (A 0) N ω - A (N * h)‖} ≤
            ENNReal.ofReal (η ^ (-q.toReal)) := by
  set D := h₀ ^ (τ - min τ (γ 1 + 1)) + h₀ ^ (γ 1 + 1 - min τ (γ 1 + 1)) *
    (|b 1| + (∑ i ∈ range (s - 2), |b (i + 2)|) * (h₀ ^ (γ 2 - γ 1) + h₀))
  set C₀ := Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) * max 1 D
  have hC₀ : 0 ≤ C₀ := mul_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_of_le_left hCN))
    (zero_le_one.trans (le_max_left _ _))
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro Ω K E _ _ _ _ _ _ _ P _ F Φ S ε A δ R ξ q h N hF hΦ hΦ0 hε happrox hA hδ hR hRS hξ hind
    hq hqt hmom hstage horder hh hh₀ hN
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg.trans hδ
  have hX0 : 0 < δ + ε + h ^ min τ (γ 1 + 1) := by positivity
  have hbound := rrk_refined hL hF hΦ hΦ0 hCM hε happrox hA hδ hR hRS hCN hξ hind hq hqt hmom hs
    hc hγ hCL hstage hC1 horder hh hh₀ hN
  have hW := W_le_case1 (ε := ε) (τ := τ) (g1 := γ 1) (g2 := γ 2)
    (Bb₂ := ∑ i ∈ range (s - 2), |b (i + 2)|) hh hh₀ (abs_nonneg (b 1))
    (Finset.sum_nonneg fun i _ => abs_nonneg (b (i + 2))) (fun hne => by
      have : 3 ≤ s := by
        by_contra hlt
        exact hne (by rw [show s - 2 = 0 by omega]; simp)
      exact hγ 1 2 le_rfl (by norm_num) (by omega))
  have hLq : eLpNorm (fun ω => rrkIter F (fun _ => R) a b s h ξ (A 0) N ω - A (N * h)) q P ≤
      ENNReal.ofReal ((C₀ + 1) * (δ + ε + h ^ min τ (γ 1 + 1))) := by
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have hm := le_max_one_mul (D := D) hδ0 hε (pow_nonneg hh.le (min τ (γ 1 + 1)))
    have hcref : 0 ≤ Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) :=
      mul_nonneg (Real.exp_pos _).le (le_max_of_le_left hCN)
    calc Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) *
          (δ + (ε + h ^ τ + |b 1| * h ^ (γ 1 + 1) +
            (∑ i ∈ range (s - 2), |b (i + 2)|) * (h ^ (γ 2 + 1) + h ^ (γ 1 + 2))))
        ≤ Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) *
          (max 1 D * (δ + ε + h ^ min τ (γ 1 + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcref
          exact (add_le_add le_rfl hW).trans hm
      _ = C₀ * (δ + ε + h ^ min τ (γ 1 + 1)) := by ring
      _ ≤ (C₀ + 1) * (δ + ε + h ^ min τ (γ 1 + 1)) := by nlinarith
  refine ⟨hLq, fun η hη => ?_⟩
  have := markov_tail (P := P) (zero_lt_one.trans_le hq).ne' hqt
    (mul_pos (by linarith) hX0) hLq hη
  rw [show (C₀ + 1) * η * (δ + ε + h ^ min τ (γ 1 + 1)) =
    η * ((C₀ + 1) * (δ + ε + h ^ min τ (γ 1 + 1))) by ring]
  exact this


/-- **Theorem 5 of arXiv 2409.06384, case `b₂ = 0`** (`s ≥ 3`): the order improves to `min(τ, γ₃+1,
γ₂+2)` (paper indexing; Lean's `b 1 = 0`, `γ 2`, `γ 1`). Same setting and differences as `thm5`. -/
theorem thm5_b2_zero (L T h₀ C_M C_N C_L C_1 : ℝ) (s τ : ℕ) (γ : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hL : 0 ≤ L) (hCM : 0 ≤ C_M) (hCN : 0 ≤ C_N) (hCL : 0 ≤ C_L) (hC1 : 0 ≤ C_1) (hs3 : 3 ≤ s)
    (hb1 : b 1 = 0)
    (hc : ∀ j < s, 0 ≤ ∑ l : Fin j, a j l ∧ ∑ l : Fin j, a j l ≤ 1)
    (hγ : ∀ j k, 1 ≤ j → j ≤ k → k < s → γ j ≤ γ k) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω K E : Type*} [MeasurableSpace Ω] [MeasurableSpace K] [NormedAddCommGroup E]
      [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      (P : Measure Ω) [IsProbabilityMeasure P] (F : E → E) (Φ : ℝ → E → E) (S : Set E) (ε : ℝ)
      (A : ℝ → E) (δ : ℝ) (R : K → E → E) (ξ : ℕ × ℕ → Ω → K) (q : ℝ≥0∞) (h : ℝ) (N : ℕ),
      (∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) →
      (∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀) → (∀ Y, Φ 0 Y = Y) →
      0 ≤ ε → (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, Metric.infDist (Φ t Y) S ≤ C_M * t * ε) →
      ODESolution (fun _ => F) A 0 T → Metric.infDist (A 0) S ≤ δ →
      Measurable (Function.uncurry R) → (∀ k z, R k z ∈ S) → (∀ p, Measurable (ξ p)) →
      iIndepFun ξ P → 1 ≤ q → q ≠ ∞ →
      (∀ p z, eLpNorm (fun ω => R (ξ p ω) z - z) q P ≤
        ENNReal.ofReal (C_N * Metric.infDist z S)) →
      (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, ∀ j, 1 ≤ j → j < s →
        ‖rkZ F (fun _ => id) a t Y j - Φ ((∑ l : Fin j, a j l) * t) Y‖ ≤ C_L * t ^ (γ j + 1)) →
      (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀,
        ‖(Y + t • ∑ j ∈ range s, b j • rkK F (fun _ => id) a t Y j) - Φ t Y‖ ≤
          C_1 * t ^ (τ + 1)) →
      0 < h → h ≤ h₀ → N * h ≤ T →
      eLpNorm (fun ω => rrkIter F (fun _ => R) a b s h ξ (A 0) N ω - A (N * h)) q P ≤
          ENNReal.ofReal (C * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2)))) ∧
        ∀ η : ℝ, 0 < η → P {ω | C * η * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2))) ≤
          ‖rrkIter F (fun _ => R) a b s h ξ (A 0) N ω - A (N * h)‖} ≤
            ENNReal.ofReal (η ^ (-q.toReal)) := by
  have hs : 2 ≤ s := by omega
  set D := h₀ ^ (τ - min τ (min (γ 2 + 1) (γ 1 + 2))) + (∑ i ∈ range (s - 2), |b (i + 2)|) *
    (h₀ ^ (γ 2 + 1 - min τ (min (γ 2 + 1) (γ 1 + 2))) +
      h₀ ^ (γ 1 + 2 - min τ (min (γ 2 + 1) (γ 1 + 2))))
  set C₀ := Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) * max 1 D
  have hC₀ : 0 ≤ C₀ := mul_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_of_le_left hCN))
    (zero_le_one.trans (le_max_left _ _))
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro Ω K E _ _ _ _ _ _ _ P _ F Φ S ε A δ R ξ q h N hF hΦ hΦ0 hε happrox hA hδ hR hRS hξ hind
    hq hqt hmom hstage horder hh hh₀ hN
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg.trans hδ
  have hX0 : 0 < δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2)) := by positivity
  have hbound := rrk_refined hL hF hΦ hΦ0 hCM hε happrox hA hδ hR hRS hCN hξ hind hq hqt hmom hs
    hc hγ hCL hstage hC1 horder hh hh₀ hN
  have hW := W_le_case2 (ε := ε) (τ := τ) (g1 := γ 1) (g2 := γ 2)
    (Bb₂ := ∑ i ∈ range (s - 2), |b (i + 2)|) hh hh₀
    (Finset.sum_nonneg fun i _ => abs_nonneg (b (i + 2)))
  rw [← abs_zero, ← hb1] at hW
  have hLq : eLpNorm (fun ω => rrkIter F (fun _ => R) a b s h ξ (A 0) N ω - A (N * h)) q P ≤
      ENNReal.ofReal ((C₀ + 1) * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2)))) := by
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have hm := le_max_one_mul (D := D) hδ0 hε (pow_nonneg hh.le (min τ (min (γ 2 + 1) (γ 1 + 2))))
    have hcref : 0 ≤ Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) :=
      mul_nonneg (Real.exp_pos _).le (le_max_of_le_left hCN)
    calc Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) *
          (δ + (ε + h ^ τ + |b 1| * h ^ (γ 1 + 1) +
            (∑ i ∈ range (s - 2), |b (i + 2)|) * (h ^ (γ 2 + 1) + h ^ (γ 1 + 2))))
        ≤ Real.exp (L * T) * max C_N (T * thm5K L h₀ C_M C_N C_L C_1 s γ a b) *
          (max 1 D * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcref
          exact (add_le_add le_rfl hW).trans hm
      _ = C₀ * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2))) := by ring
      _ ≤ (C₀ + 1) * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2))) := by nlinarith
  refine ⟨hLq, fun η hη => ?_⟩
  have := markov_tail (P := P) (zero_lt_one.trans_le hq).ne' hqt
    (mul_pos (by linarith) hX0) hLq hη
  rw [show (C₀ + 1) * η * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2))) =
    η * ((C₀ + 1) * (δ + ε + h ^ min τ (min (γ 2 + 1) (γ 1 + 2)))) by ring]
  exact this

end Thm5Statements


section Sec22

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Section 2.2 of arXiv 2409.06384, defect estimate**: a curve `W` with `‖Ẇ - F(W)‖ ≤ ε̃` (for
instance the projected flow `Ẇ = P(W) F(W)` when `‖F(Y) - P(Y)F(Y)‖ ≤ ε̃`) stays within `e^{Lh} h
ε̃` of the exact flow: `‖Φ^h(W(0)) - W(h)‖ ≤ e^{Lh} h ε̃` (Grönwall; the paper cites its reference
[14, Lemma 1]). -/
theorem sec22_defect {F : E → E} {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {G : ℝ → E → E} {W : ℝ → E} {h : ℝ} (hh : 0 ≤ h) (hh₀ : h ≤ h₀)
    (hW : ODESolution G W 0 h) {ε : ℝ} (hdef : ∀ t ∈ Ico 0 h, ‖G t (W t) - F (W t)‖ ≤ ε) :
    ‖Φ h (W 0) - W h‖ ≤ Real.exp (L * h) * h * ε := by
  rcases hh.eq_or_lt with rfl | hpos
  · simp [hΦ0]
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hdef 0 ⟨le_rfl, hpos⟩)
  have hy := (hΦ (W 0)).mono le_rfl hh₀
  have := norm_sub_le_gronwallBound (f := fun _ => F) (L := L) (fun _ x y => hF x y) hL
    (u := fun t => F (Φ t (W 0))) (ηy := 0) (ηz := ε) (δ := 0) hy.cont hy.deriv
    (fun _ _ => by simp) hW.cont hW.deriv hdef (by simp [hΦ0]) h ⟨hh, le_rfl⟩
  refine this.trans ((gronwallBound_le_exp_mul hL (by linarith)).trans (le_of_eq ?_))
  simp only [sub_zero, zero_add]
  ring

/-- **Section 2.2 of arXiv 2409.06384**: a small normal component `‖F(Y) - P(Y)F(Y)‖ ≤ ε̃` on `S`
implies Assumption 3 with `C_M = e^{L h₀}` and `ε = ε̃`: `dist(Φ^h(Y), S) ≤ e^{L h₀} h ε̃`. The
projected field `PF` is abstract and the existence of the projected (DLRA) flow on `S` up to time
`h` is a hypothesis (the paper assumes it implicitly); for matrices see `sec22_matrix`. -/
theorem sec22_assumption3 {F : E → E} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → E → E} {h₀ : ℝ} (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {S : Set E} {PF : E → E} {ε : ℝ}
    (hdef : ∀ Y ∈ S, ‖PF Y - F Y‖ ≤ ε)
    (hflow : ∀ Y ∈ S, ∀ h ∈ Ioc 0 h₀, ∃ W : ℝ → E, W 0 = Y ∧
      ODESolution (fun _ => PF) W 0 h ∧ ∀ t ∈ Icc 0 h, W t ∈ S) :
    ∀ Y ∈ S, ∀ h ∈ Ioc 0 h₀, Metric.infDist (Φ h Y) S ≤ Real.exp (L * h₀) * h * ε := by
  intro Y hY h hh
  obtain ⟨W, hW0, hW, hWS⟩ := hflow Y hY h hh
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hdef Y hY)
  have h1 := sec22_defect hL hF hΦ hΦ0 hh.1.le hh.2 hW (ε := ε)
    (fun t ht => hdef _ (hWS t ⟨ht.1, ht.2.le⟩))
  rw [hW0] at h1
  calc Metric.infDist (Φ h Y) S ≤ dist (Φ h Y) (W h) :=
        Metric.infDist_le_dist_of_mem (hWS h ⟨hh.1.le, le_rfl⟩)
    _ ≤ Real.exp (L * h) * h * ε := by rw [dist_eq_norm]; exact h1
    _ ≤ Real.exp (L * h₀) * h * ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hh.2 hL)) hh.1.le) hε

end Sec22

section Sec22Matrix

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Section 2.2 of arXiv 2409.06384, matrix form**: if `W(t) = U(t) S(t) V(t)ᵀ` (factors with `r`
columns) solves the DLRA equation `Ẇ = P_{U,V} F(W)` with the tangent projector `tangentProj` and
normal component `‖(I - UUᵀ) F(W) (I - VVᵀ)‖ ≤ ε̃`, then `‖Φ^h(W(0)) - W(h)‖ ≤ e^{Lh} h ε̃` and
`distLR r (Φ^h(W(0))) ≤ e^{Lh} h ε̃`. Orthonormality of `U, V` (which makes `tangentProj` the
tangent-space projector) is not needed for the bound. -/
theorem sec22_matrix {r : ℕ} {F : Matrix m n ℝ → Matrix m n ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {Φ : ℝ → Matrix m n ℝ → Matrix m n ℝ} {h₀ : ℝ}
    (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀) (hΦ0 : ∀ Y, Φ 0 Y = Y)
    {U : ℝ → Matrix m (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ} {Sg : ℝ → Matrix (Fin r) (Fin r) ℝ}
    {W : ℝ → Matrix m n ℝ} {h : ℝ} (hh : 0 ≤ h) (hh₀ : h ≤ h₀)
    (hfac : W h = U h * Sg h * (V h)ᵀ)
    (hW : ODESolution (fun t X => tangentProj (U t) (V t) (F X)) W 0 h) {ε : ℝ}
    (hnormal : ∀ t ∈ Ico 0 h, ‖(1 - U t * (U t)ᵀ) * F (W t) * (1 - V t * (V t)ᵀ)‖ ≤ ε) :
    ‖Φ h (W 0) - W h‖ ≤ Real.exp (L * h) * h * ε ∧
      distLR r (Φ h (W 0)) ≤ Real.exp (L * h) * h * ε := by
  have h1 := sec22_defect hL hF hΦ hΦ0 hh hh₀ hW (ε := ε) (fun t ht => by
    have e := tangentProj_add_normal (U t) (V t) (F (W t))
    have : tangentProj (U t) (V t) (F (W t)) - F (W t) =
        -((1 - U t * (U t)ᵀ) * F (W t) * (1 - V t * (V t)ᵀ)) := by
      rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, e, sub_self]
    rw [this, norm_neg]
    exact hnormal t ht)
  refine ⟨h1, ?_⟩
  have hrank : (W h).rank ≤ r := by
    rw [hfac]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)).trans
      ((Matrix.rank_le_card_width _).trans (by simp))
  calc distLR r (Φ h (W 0)) ≤ ‖Φ h (W 0) - W h‖ := distLR_le_norm_sub hrank
    _ ≤ _ := h1

end Sec22Matrix


namespace Example1

open scoped LeanDLRA.Frobenius

/-- Example 1 of arXiv 2409.06384: `L = diag(0, 10, -10)`. -/
noncomputable def Lm : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![0, 10, -10]
/-- `G = diag(0, 10⁻⁵ e⁻¹, 0)`. -/
noncomputable def G : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![0, Real.exp (-1) / 100000, 0]
/-- The right-hand side `F(Y) = L Y + G`. -/
noncomputable def F (Y : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Lm * Y + G
/-- The rank-2 initial value `Y(0) = diag(1, 0, 10⁻⁶ e)`. -/
noncomputable def Y0 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 0, Real.exp 1 / 1000000]
/-- Second diagonal entry of the exact flow, `10⁻⁶ (e^{10t-1} - e^{-1})`. -/
noncomputable def aE (t : ℝ) : ℝ := (Real.exp (10 * t - 1) - Real.exp (-1)) / 1000000
/-- Third diagonal entry of both flows, `10⁻⁶ e^{1-10t}`. -/
noncomputable def cE (t : ℝ) : ℝ := Real.exp (1 - 10 * t) / 1000000
/-- The exact flow `Φ_F^t(Y₀) = diag(1, 10⁻⁶(e^{10t-1} - e⁻¹), 10⁻⁶ e^{1-10t})`. -/
noncomputable def Aex (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, aE t, cE t]
/-- The DLRA (tangent-projected) flow `Φ_{PF}^t(Y₀) = diag(1, 0, 10⁻⁶ e^{1-10t})`. -/
noncomputable def Wex (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 0, cE t]
/-- Orthonormal basis `[e₁, e₃]` of the range and co-range of `Wex t`. -/
noncomputable def U : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 1]

/-- The diagonal unit matrices. -/
noncomputable def E1 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 0, 0]
/-- The diagonal unit matrices. -/
noncomputable def E2 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![0, 1, 0]
/-- The diagonal unit matrices. -/
noncomputable def E3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![0, 0, 1]

/-- Derivative of the second entry of the exact flow (auxiliary; arXiv 2409.06384, Example 1). -/
theorem hasDerivAt_aE (t : ℝ) : HasDerivAt aE (10 * aE t + Real.exp (-1) / 100000) t := by
  have h1 : HasDerivAt (fun t : ℝ => 10 * t - 1) 10 t := by
    simpa using ((hasDerivAt_id t).const_mul (10 : ℝ)).sub_const (1 : ℝ)
  have h2 := (h1.exp.sub_const (Real.exp (-1))).div_const (1000000 : ℝ)
  refine h2.congr_deriv ?_
  unfold aE
  ring

/-- Derivative of the third entry of both flows (auxiliary; arXiv 2409.06384, Example 1). -/
theorem hasDerivAt_cE (t : ℝ) : HasDerivAt cE (-10 * cE t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - 10 * t) (-10) t := by
    simpa using ((hasDerivAt_id t).const_mul (10 : ℝ)).const_sub (1 : ℝ)
  have h2 := h1.exp.div_const (1000000 : ℝ)
  refine h2.congr_deriv ?_
  unfold cE
  ring

/-- A `3 × 3` diagonal matrix in the basis `E1, E2, E3` (auxiliary; arXiv 2409.06384, Example 1). -/
theorem diagonal_eq (x y z : ℝ) : Matrix.diagonal ![x, y, z] = x • E1 + y • E2 + z • E3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E1, E2, E3, Matrix.diagonal]

/-- Entrywise differentiation of a diagonal matrix curve (auxiliary; arXiv 2409.06384, Example 1).
-/
theorem hasDerivAt_diagonal {x y z : ℝ → ℝ} {x' y' z' t : ℝ} (hx : HasDerivAt x x' t)
    (hy : HasDerivAt y y' t) (hz : HasDerivAt z z' t) :
    HasDerivAt (fun t => Matrix.diagonal ![x t, y t, z t]) (Matrix.diagonal ![x', y', z']) t := by
  have e : (fun t => Matrix.diagonal ![x t, y t, z t]) = fun t => x t • E1 + y t • E2 + z t • E3 :=
    funext fun t => diagonal_eq _ _ _
  rw [e, diagonal_eq]
  exact ((hx.smul_const _).add (hy.smul_const _)).add (hz.smul_const _)

/-- **Example 1 of arXiv 2409.06384 (exact flow).** `t ↦ diag(1, 10⁻⁶(e^{10t-1} - e⁻¹), 10⁻⁶
e^{1-10t})` solves `Ẏ = L Y + G` with `Y(0) = Y₀`. -/
theorem exact_flow (t : ℝ) : HasDerivAt Aex (F (Aex t)) t ∧ Aex 0 = Y0 := by
  constructor
  · have := hasDerivAt_diagonal (hasDerivAt_const t (1 : ℝ)) (hasDerivAt_aE t) (hasDerivAt_cE t)
    refine this.congr_deriv ?_
    rw [F, Aex, Lm, G, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1
    ext i; fin_cases i <;> simp
  · rw [Aex, Y0, aE, cE]
    congr 1
    ext i; fin_cases i <;> simp

/-- `U Uᵀ = diag(1, 0, 1)` (auxiliary; arXiv 2409.06384, Example 1). -/
theorem UUt : U * Uᵀ = Matrix.diagonal ![1, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [U, Matrix.mul_apply, Fin.sum_univ_two]

/-- `U` has orthonormal columns (auxiliary; arXiv 2409.06384, Example 1). -/
theorem U_orth : Uᵀ * U = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [U, Matrix.mul_apply, Fin.sum_univ_three]

/-- Factorization `W(t) = U S(t) Uᵀ` of the DLRA flow (auxiliary; arXiv 2409.06384, Example 1). -/
theorem Wex_eq (t : ℝ) : Wex t = U * !![1, 0; 0, cE t] * Uᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Wex, U, Matrix.mul_apply, Fin.sum_univ_two]

/-- The DLRA flow stays on the manifold of rank-`2` matrices (auxiliary; arXiv 2409.06384, Example
1). -/
theorem rank_Wex (t : ℝ) : (Wex t).rank = 2 := by
  classical
  have hc : cE t ≠ 0 := by unfold cE; positivity
  rw [Wex, Matrix.rank_diagonal, Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin 3 => (![1, 0, cE t] : Fin 3 → ℝ) i ≠ 0) = {0, 2} := by
    ext i; fin_cases i <;> simp [hc]
  rw [this]; rfl

/-- **Example 1 of arXiv 2409.06384 (DLRA flow).** `t ↦ diag(1, 0, 10⁻⁶ e^{1-10t}) = U S(t) Uᵀ`
(with `Uᵀ U = I`, rank exactly `2`) solves the tangent-projected equation `Ẏ = P(Y) F(Y)`, `P(Y) =
tangentProj U U`, with `Y(0) = Y₀`. -/
theorem dlra_flow (t : ℝ) :
    HasDerivAt Wex (tangentProj U U (F (Wex t))) t ∧ Wex 0 = Y0 ∧
      Wex t = U * !![1, 0; 0, cE t] * Uᵀ ∧ Uᵀ * U = 1 ∧ (Wex t).rank = 2 := by
  refine ⟨?_, ?_, Wex_eq t, U_orth, rank_Wex t⟩
  · have := hasDerivAt_diagonal (hasDerivAt_const t (1 : ℝ)) (hasDerivAt_const t (0 : ℝ))
      (hasDerivAt_cE t)
    refine this.congr_deriv ?_
    rw [tangentProj_apply, Matrix.mul_assoc (F (Wex t)) U, Matrix.mul_assoc (U * Uᵀ * F (Wex t)) U,
      UUt]
    simp only [F, Wex, Lm, G, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add,
      Matrix.diagonal_sub]
    congr 1
    ext i; fin_cases i <;> simp
  · rw [Wex, Y0, cE]
    congr 1
    ext i; fin_cases i <;> simp

/-- Frobenius norm of a `3 × 3` diagonal matrix (auxiliary; arXiv 2409.06384, Example 1). -/
theorem norm_diagonal (x y z : ℝ) : ‖Matrix.diagonal ![x, y, z]‖ = √(x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [Frobenius.norm_def]
  congr 1
  simp [Fin.sum_univ_three, Matrix.diagonal]

/-- `8100 < e⁹` (auxiliary; arXiv 2409.06384, Example 1). -/
theorem exp_nine_gt : (8100 : ℝ) < Real.exp 9 := by
  have h := Real.exp_one_gt_d9
  have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h9]
  calc (8100 : ℝ) < 2.7182818283 ^ 9 := by norm_num
    _ < Real.exp 1 ^ 9 := by gcongr

/-- **Example 1 of arXiv 2409.06384, flow approximability.** The exact flow at `h = 1` is within
`1.24 · 10⁻¹⁰` of a rank-`2` matrix: `‖Φ_F^1(Y₀) - [[Φ_F^1(Y₀)]]_2‖_F ≤ 1.24 · 10⁻¹⁰`. -/
theorem approx_error : distLR 2 (Aex 1) ≤ 124 / 10 ^ 12 := by
  classical
  have hrank : (Matrix.diagonal ![1, aE 1, 0]).rank ≤ 2 := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    calc (Finset.univ.filter fun i : Fin 3 => (![1, aE 1, 0] : Fin 3 → ℝ) i ≠ 0).card
        ≤ ({0, 1} : Finset (Fin 3)).card := by
          refine Finset.card_le_card fun i hi => ?_
          fin_cases i <;> simp_all
      _ = 2 := rfl
  refine (distLR_le_norm_sub hrank).trans ?_
  have e : Aex 1 - Matrix.diagonal ![1, aE 1, 0] = Matrix.diagonal ![0, 0, cE 1] := by
    rw [Aex, Matrix.diagonal_sub]; congr 1; ext i; fin_cases i <;> simp
  rw [e, norm_diagonal]
  have hc : 0 ≤ cE 1 := by unfold cE; positivity
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + cE 1 ^ 2 = cE 1 ^ 2 by ring, Real.sqrt_sq hc]
  have h9 := exp_nine_gt
  have : cE 1 = (Real.exp 9)⁻¹ / 1000000 := by
    rw [cE, ← Real.exp_neg]; norm_num
  rw [this, div_le_iff₀ (by norm_num)]
  have hpos : 0 < Real.exp 9 := Real.exp_pos 9
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- **Example 1 of arXiv 2409.06384, DLRA error.** At `h = 1` the tangent-projected flow differs
from the exact flow by at least `0.008`: `‖Φ_F^1(Y₀) - Φ_{PF}^1(Y₀)‖_F ≥ 0.008`. -/
theorem dlra_error : (8 / 1000 : ℝ) ≤ ‖Aex 1 - Wex 1‖ := by
  have e : Aex 1 - Wex 1 = Matrix.diagonal ![0, aE 1, 0] := by
    rw [Aex, Wex, Matrix.diagonal_sub]; congr 1; ext i; fin_cases i <;> simp
  rw [e, norm_diagonal]
  have h9 := exp_nine_gt
  have h1 : Real.exp (-1) < 1 := by simp
  have ha : aE 1 = (Real.exp 9 - Real.exp (-1)) / 1000000 := by rw [aE]; norm_num
  have ha0 : 0 ≤ aE 1 := by rw [ha]; apply div_nonneg _ (by norm_num); linarith
  rw [show (0 : ℝ) ^ 2 + aE 1 ^ 2 + 0 ^ 2 = aE 1 ^ 2 by ring, Real.sqrt_sq ha0, ha,
    le_div_iff₀ (by norm_num)]
  linarith

/-- **Example 1 of arXiv 2409.06384, normal component.** Along the DLRA flow the normal component of
the vector field is `‖(I - U Uᵀ) F(Y) (I - U Uᵀ)‖_F = 10⁻⁵ e⁻¹ ≈ 3.7 · 10⁻⁶`, about `3 · 10⁴` times
the rank-`2` approximation error `1.24 · 10⁻¹⁰` of the exact flow (`approx_error`). -/
theorem normal_component (t : ℝ) :
    ‖(1 - U * Uᵀ) * F (Wex t) * (1 - U * Uᵀ)‖ = Real.exp (-1) / 100000 := by
  have e : (1 - U * Uᵀ) * F (Wex t) * (1 - U * Uᵀ) =
      Matrix.diagonal ![0, Real.exp (-1) / 100000, 0] := by
    rw [UUt, F, Wex, Lm, G, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1; ext i; fin_cases i <;> simp
  rw [e, norm_diagonal]
  have hp : 0 ≤ Real.exp (-1) / 100000 := by positivity
  rw [show (0 : ℝ) ^ 2 + (Real.exp (-1) / 100000) ^ 2 + 0 ^ 2 = (Real.exp (-1) / 100000) ^ 2 by
    ring, Real.sqrt_sq hp]

end Example1


section Lemma78

open scoped LeanDLRA.Frobenius

/-- `rank (c • X) ≤ rank X` (auxiliary; arXiv 2409.06384, Lemmas 7 and 8). -/
theorem rank_smul_le' {m n : Type*} [Fintype n] (c : ℝ) (X : Matrix m n ℝ) :
    (c • X).rank ≤ X.rank := by
  classical
  have h : c • X = X * (c • (1 : Matrix n n ℝ)) := by rw [Matrix.mul_smul, Matrix.mul_one]
  rw [h]; exact Matrix.rank_mul_le_left _ _

/-- `rank (Y + c • B) ≤ rank Y + rank B` (auxiliary; arXiv 2409.06384, Lemmas 7 and 8). -/
theorem rank_add_smul_le {m n : Type*} [Finite m] [Fintype n] {Y B : Matrix m n ℝ} {r k : ℕ}
    (hY : Y.rank ≤ r) (hB : B.rank ≤ k) (c : ℝ) : (Y + c • B).rank ≤ r + k := by
  classical
  have := Fintype.ofFinite m
  exact (EckartYoung.rank_add_le _ _).trans (add_le_add hY ((rank_smul_le' _ _).trans hB))

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Lemma 7 of arXiv 2409.06384**: if the flow is approximable at rank `k` for inputs of rank `≤
k`, `distLR k (Φ^t(Y)) ≤ C_M t ε` for `0 < t ≤ h₀` (eq. (21)), then `F` maps rank `≤ k` into an `C_M
ε`-neighbourhood of rank `≤ 2k`: `‖F(Y) - [[F(Y)]]_{2k}‖ = distLR (2k) (F Y) ≤ C_M ε`. Proof: `F(Y)`
is the limit of `(Φ^t(Y) - Y)/t`, and `([[Φ^t(Y)]]_k - Y)/t` has rank `≤ 2k`. Differences: (21) is
assumed only at the one rank `k` used, for inputs of rank `≤ k` (the paper: all `r ≤ k ≤ 15r`,
inputs in `M_k`); no Lipschitz bound is needed. -/
theorem lemma7 {F : Matrix m n ℝ → Matrix m n ℝ} {Φ : ℝ → Matrix m n ℝ → Matrix m n ℝ} {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {k : ℕ} {C_M ε : ℝ}
    (happrox : ∀ Y : Matrix m n ℝ, Y.rank ≤ k → ∀ t ∈ Ioc 0 h₀, distLR k (Φ t Y) ≤ C_M * t * ε)
    {Y : Matrix m n ℝ} (hY : Y.rank ≤ k) : distLR (2 * k) (F Y) ≤ C_M * ε := by
  have hd := (hΦ Y).deriv 0 ⟨le_rfl, hh₀⟩
  simp only [hΦ0] at hd
  have hI : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext x; simp [lt_iff_le_and_ne, eq_comm]
  rw [hasDerivWithinAt_iff_tendsto_slope, hI] at hd
  have hc : Continuous (distLR (m := m) (n := n) (2 * k)) := (lipschitzWith_distLR _).continuous
  have hlim := (hc.tendsto _).comp hd
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hh₀] with t ht
  have ht0 : 0 ≤ t⁻¹ := inv_nonneg.2 ht.1.le
  simp only [Function.comp_apply, slope_def_module, sub_zero, hΦ0]
  obtain ⟨B, hB, hBd⟩ := exists_best_approx k (Φ t Y)
  have hrank : (t⁻¹ • (B - Y)).rank ≤ 2 * k := by
    rw [sub_eq_add_neg, ← neg_one_smul ℝ Y, add_comm]
    have := rank_add_smul_le (Y := t⁻¹ • ((-1 : ℝ) • Y)) (B := B) (r := k) (k := k)
      ((rank_smul_le' _ _).trans ((rank_smul_le' _ _).trans hY)) hB t⁻¹
    rw [smul_add, add_comm]
    simpa [two_mul, add_comm] using this
  calc distLR (2 * k) (t⁻¹ • (Φ t Y - Y)) ≤ ‖t⁻¹ • (Φ t Y - Y) - t⁻¹ • (B - Y)‖ :=
        distLR_le_norm_sub hrank
    _ = t⁻¹ * ‖Φ t Y - B‖ := by
        rw [← smul_sub, norm_smul, sub_sub_sub_cancel_right, Real.norm_of_nonneg ht0]
    _ = t⁻¹ * distLR k (Φ t Y) := by rw [hBd]
    _ ≤ t⁻¹ * (C_M * t * ε) := mul_le_mul_of_nonneg_left (happrox Y hY t ⟨ht.1, ht.2.le⟩) ht0
    _ = C_M * ε := by have ht' : t ≠ 0 := ht.1.ne'; field_simp

/-- **Lemma 8 of arXiv 2409.06384**: for `rank Z ≤ r`, `α ≥ 0` and any `B_k` of rank `≤ k ≤ 14 r`
(e.g. `[[B]]_k`), `‖Z + αX - [[Z + αX]]_{15r}‖ = distLR (15 r) (Z + α X) ≤ α ‖X - B_k‖`. -/
theorem lemma8 {r k : ℕ} (hk : k ≤ 14 * r) {Z : Matrix m n ℝ} (hZ : Z.rank ≤ r)
    (X : Matrix m n ℝ) {α : ℝ} (hα : 0 ≤ α) {Bk : Matrix m n ℝ} (hBk : Bk.rank ≤ k) :
    distLR (15 * r) (Z + α • X) ≤ α * ‖X - Bk‖ := by
  have hrank : (Z + α • Bk).rank ≤ 15 * r := (rank_add_smul_le hZ hBk α).trans (by omega)
  calc distLR (15 * r) (Z + α • X) ≤ ‖Z + α • X - (Z + α • Bk)‖ := distLR_le_norm_sub hrank
    _ = α * ‖X - Bk‖ := by
        rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hα]

end Lemma78


section RK4mod

/-- The classical RK4 tableau `a` (arXiv 2409.06384, Sec. 3.4) (0-indexed: `a₁₀ = a₂₁ = 1/2`, `a₃₂ =
1`). -/
noncomputable def rk4a (j l : ℕ) : ℝ :=
  if j = 1 ∧ l = 0 then 1 / 2 else if j = 2 ∧ l = 1 then 1 / 2 else if j = 3 ∧ l = 2 then 1 else 0

/-- The classical RK4 weights (arXiv 2409.06384, Sec. 3.4) `b = (1/6, 1/3, 1/3, 1/6)`. -/
noncomputable def rk4b (j : ℕ) : ℝ :=
  if j = 0 then 1 / 6 else if j = 1 then 1 / 3 else if j = 2 then 1 / 3 else if j = 3 then 1 / 6
    else 0

/-- **Bridge.** On the stage indices `< 4`, `rk4a` is the Runge–Kutta matrix of the core tableau
`ButcherTableau.rk4`; its extension by `0` to all of `ℕ` is the convention of the stage maps `rkK`,
`rkZ` of this file (an arbitrary choice, so the two are not replaced by each other). -/
theorem rk4a_eq (i j : Fin 4) : rk4a i j = (ButcherTableau.rk4 : ButcherTableau ℝ 4).a i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rk4a, ButcherTableau.rk4]

/-- **Bridge.** On the stage indices `< 4`, `rk4b` are the weights of the core tableau
`ButcherTableau.rk4`. -/
theorem rk4b_eq (i : Fin 4) : rk4b i = (ButcherTableau.rk4 : ButcherTableau ℝ 4).b i := by
  fin_cases i <;> norm_num [rk4b, ButcherTableau.rk4]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- RK4 stage `0` (auxiliary; arXiv 2409.06384, Sec. 3.4). -/
theorem rk4_Z0 (F : E → E) (N : ℕ → E → E) (h : ℝ) (y : E) : rkZ F N rk4a h y 0 = y := by
  simp [rkZ]

/-- RK4 stage `1`: `Z₁ = Y + (h/2) F(N₀(Z₀))` (auxiliary; arXiv 2409.06384, Sec. 3.4). -/
theorem rk4_Z1 (F : E → E) (N : ℕ → E → E) (h : ℝ) (y : E) :
    rkZ F N rk4a h y 1 = y + (h * (1 / 2)) • rkK F N rk4a h y 0 := by
  simp [rkZ, rk4a, smul_smul]

/-- RK4 stage `2`: `Z₂ = Y + (h/2) F(N₁(Z₁))` (auxiliary; arXiv 2409.06384, Sec. 3.4). -/
theorem rk4_Z2 (F : E → E) (N : ℕ → E → E) (h : ℝ) (y : E) :
    rkZ F N rk4a h y 2 = y + (h * (1 / 2)) • rkK F N rk4a h y 1 := by
  simp [rkZ, rk4a, smul_smul, Fin.sum_univ_two]

/-- RK4 stage `3`: `Z₃ = Y + h F(N₂(Z₂))` (auxiliary; arXiv 2409.06384, Sec. 3.4). -/
theorem rk4_Z3 (F : E → E) (N : ℕ → E → E) (h : ℝ) (y : E) :
    rkZ F N rk4a h y 3 = y + h • rkK F N rk4a h y 2 := by
  simp [rkZ, rk4a, Fin.sum_univ_three]

/-- `∑ |a_{jl}| = 2` for RK4 (auxiliary; arXiv 2409.06384). -/
theorem rk4_Aa : ∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l| = 2 := by
  simp [Finset.sum_range_succ, rk4a]; norm_num

/-- `∑ |b_j| = 1` for RK4 (auxiliary; arXiv 2409.06384). -/
theorem rk4_Bb : ∑ j ∈ range 4, |rk4b j| = 1 := by
  simp [Finset.sum_range_succ, rk4b]; norm_num

end RK4mod


section Thm5RK4

/-- The RK4 nodes `0, 1/2, 1/2, 1` lie in `[0, 1]` (auxiliary; arXiv 2409.06384). -/
theorem rk4_nodes : ∀ j < 4, 0 ≤ ∑ l : Fin j, rk4a j l ∧ ∑ l : Fin j, rk4a j l ≤ 1 := by
  intro j hj
  interval_cases j <;>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_one, Fin.sum_univ_two,
      Fin.sum_univ_three] <;> norm_num [rk4a]

/-- **Theorem 5 for RK4** (arXiv 2409.06384, remark after Theorem 5): the randomized low-rank RK4
method (`τ = 4`, stage orders `γ_j = 1`) has error `C (δ + ε + h²)`: order `min(4, 1 + 1) = 2`. -/
theorem thm5_rk4 (L T h₀ C_M C_N C_L C_1 : ℝ) (hL : 0 ≤ L) (hCM : 0 ≤ C_M) (hCN : 0 ≤ C_N)
    (hCL : 0 ≤ C_L) (hC1 : 0 ≤ C_1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω K E : Type*} [MeasurableSpace Ω] [MeasurableSpace K] [NormedAddCommGroup E]
      [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      (P : Measure Ω) [IsProbabilityMeasure P] (F : E → E) (Φ : ℝ → E → E) (S : Set E) (ε : ℝ)
      (A : ℝ → E) (δ : ℝ) (R : K → E → E) (ξ : ℕ × ℕ → Ω → K) (q : ℝ≥0∞) (h : ℝ) (N : ℕ),
      (∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) →
      (∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀) → (∀ Y, Φ 0 Y = Y) →
      0 ≤ ε → (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, Metric.infDist (Φ t Y) S ≤ C_M * t * ε) →
      ODESolution (fun _ => F) A 0 T → Metric.infDist (A 0) S ≤ δ →
      Measurable (Function.uncurry R) → (∀ k z, R k z ∈ S) → (∀ p, Measurable (ξ p)) →
      iIndepFun ξ P → 1 ≤ q → q ≠ ∞ →
      (∀ p z, eLpNorm (fun ω => R (ξ p ω) z - z) q P ≤
        ENNReal.ofReal (C_N * Metric.infDist z S)) →
      (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀, ∀ j, 1 ≤ j → j < 4 →
        ‖rkZ F (fun _ => id) rk4a t Y j - Φ ((∑ l : Fin j, rk4a j l) * t) Y‖ ≤ C_L * t ^ 2) →
      (∀ Y ∈ S, ∀ t ∈ Ioc 0 h₀,
        ‖(Y + t • ∑ j ∈ range 4, rk4b j • rkK F (fun _ => id) rk4a t Y j) - Φ t Y‖ ≤
          C_1 * t ^ 5) →
      0 < h → h ≤ h₀ → N * h ≤ T →
      eLpNorm (fun ω => rrkIter F (fun _ => R) rk4a rk4b 4 h ξ (A 0) N ω - A (N * h)) q P ≤
          ENNReal.ofReal (C * (δ + ε + h ^ 2)) ∧
        ∀ η : ℝ, 0 < η → P {ω | C * η * (δ + ε + h ^ 2) ≤
          ‖rrkIter F (fun _ => R) rk4a rk4b 4 h ξ (A 0) N ω - A (N * h)‖} ≤
            ENNReal.ofReal (η ^ (-q.toReal))  := by
  obtain ⟨C, hC, hall⟩ := thm5 L T h₀ C_M C_N C_L C_1 4 4 (fun _ => 1) rk4a rk4b hL hCM hCN hCL
    hC1 (by norm_num) rk4_nodes (fun _ _ _ _ _ => le_rfl)
  refine ⟨C, hC, ?_⟩
  intro Ω K E _ _ _ _ _ _ _ P _ F Φ S ε A δ R ξ q h N hF hΦ hΦ0 hε happrox hA hδ hR hRS hξ hind
    hq hqt hmom hstage horder hh hh₀ hN
  exact hall P F Φ S ε A δ R ξ q h N hF hΦ hΦ0 hε happrox hA hδ hR hRS hξ hind hq hqt hmom
    hstage horder hh hh₀ hN

end Thm5RK4


section RK4modStages

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Real-number bounds for the oversampled RK4 stages (auxiliary; arXiv 2409.06384, proof of Lemma
9). -/
theorem rk4_real_bound {h h₀ L e : ℝ} (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hL : 0 ≤ L) (he : 0 ≤ e) :
    h * (1 / 2) * e ≤ (1 + L * h₀ * (1 + L * h₀)) * (h * e) ∧
    h * (1 / 2) * (L * (h * (1 / 2) * e) + e) ≤ (1 + L * h₀ * (1 + L * h₀)) * (h * e) ∧
    h * (L * (h * (1 / 2) * (L * (h * (1 / 2) * e) + e)) + e) ≤
      (1 + L * h₀ * (1 + L * h₀)) * (h * e) := by
  have hh₀0 : 0 ≤ h₀ := hh.trans hh₀
  have hu : L * h ≤ L * h₀ := mul_le_mul_of_nonneg_left hh₀ hL
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have hv : 0 ≤ L * h₀ := mul_nonneg hL hh₀0
  have hhe : 0 ≤ h * e := mul_nonneg hh he
  have hw : 0 ≤ L * h₀ * (1 + L * h₀) := mul_nonneg hv (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have e1 : h * (1 / 2) * (L * (h * (1 / 2) * e) + e) = (h * e) * (1 / 2 + L * h / 4) := by ring
    rw [e1]
    have : 1 / 2 + L * h / 4 ≤ 1 + L * h₀ * (1 + L * h₀) := by nlinarith
    nlinarith
  · have e1 : h * (L * (h * (1 / 2) * (L * (h * (1 / 2) * e) + e)) + e) =
        (h * e) * (1 + (L * h) / 2 + (L * h) * (L * h) / 4) := by ring
    rw [e1]
    have : 1 + (L * h) / 2 + (L * h) * (L * h) / 4 ≤ 1 + L * h₀ * (1 + L * h₀) := by nlinarith
    nlinarith

/-- **Stage approximability of the oversampled RK4 method** (arXiv 2409.06384, proof of Lemma 9, via
Lemmas 7 and 8): for `Y` of rank `≤ r` the classical RK4 stages `Z̃_j` are within `C_M (1 + L h₀ (1
+ L h₀)) h ε` of rank `15 r`. -/
theorem rk4_stage_dist {F : Matrix m n ℝ → Matrix m n ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) {Φ : ℝ → Matrix m n ℝ → Matrix m n ℝ} {h₀ : ℝ}
    (hh₀ : 0 < h₀) (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀)
    (hΦ0 : ∀ Y, Φ 0 Y = Y) {r : ℕ} {C_M ε : ℝ} (hCM : 0 ≤ C_M) (hε : 0 ≤ ε)
    (h21 : ∀ k, r ≤ k → k ≤ 15 * r → ∀ Y : Matrix m n ℝ, Y.rank ≤ k → ∀ t ∈ Ioc 0 h₀,
      distLR k (Φ t Y) ≤ C_M * t * ε)
    {h : ℝ} (hh : 0 ≤ h) (hhh₀ : h ≤ h₀) {y : Matrix m n ℝ} (hy : y.rank ≤ r) :
    ∀ j < 4, distLR (15 * r) (rkZ F (fun _ => id) rk4a h y j) ≤
      C_M * (1 + L * h₀ * (1 + L * h₀)) * (h * ε) := by
  set e := C_M * ε with he_def
  have he : 0 ≤ e := mul_nonneg hCM hε
  have hK : ∀ j, rkK F (fun _ => id) rk4a h y j = F (rkZ F (fun _ => id) rk4a h y j) :=
    fun j => rkK_eq _ _ _ _ _ _
  have h7 : ∀ k, r ≤ k → k ≤ 15 * r → ∀ W : Matrix m n ℝ, W.rank ≤ k →
      distLR (2 * k) (F W) ≤ e := fun k hk1 hk2 W hW =>
    lemma7 hh₀ hΦ hΦ0 (h21 k hk1 hk2) hW
  have hR := rk4_real_bound hh hhh₀ hL he
  have hh2 : 0 ≤ h * (1 / 2) := by positivity
  -- the auxiliary low-rank chain
  obtain ⟨B1, hB1r, hB1⟩ := exists_best_approx (2 * r) (F y)
  have hB1e : ‖F y - B1‖ ≤ e := hB1 ▸ h7 r le_rfl (by omega) y hy
  set W2 := y + (h * (1 / 2)) • B1 with hW2
  have hW2r : W2.rank ≤ 3 * r := (rank_add_smul_le hy hB1r _).trans (by omega)
  obtain ⟨B2, hB2r, hB2⟩ := exists_best_approx (2 * (3 * r)) (F W2)
  have hB2e : ‖F W2 - B2‖ ≤ e := hB2 ▸ h7 (3 * r) (by omega) (by omega) W2 hW2r
  set W3 := y + (h * (1 / 2)) • B2 with hW3
  have hW3r : W3.rank ≤ 7 * r := (rank_add_smul_le hy hB2r _).trans (by omega)
  obtain ⟨B3, hB3r, hB3⟩ := exists_best_approx (2 * (7 * r)) (F W3)
  have hB3e : ‖F W3 - B3‖ ≤ e := hB3 ▸ h7 (7 * r) (by omega) (by omega) W3 hW3r
  -- the classical stages
  obtain ⟨Z1, hZ1def⟩ : ∃ Z, Z = rkZ F (fun _ => id) rk4a h y 1 := ⟨_, rfl⟩
  obtain ⟨Z2, hZ2def⟩ : ∃ Z, Z = rkZ F (fun _ => id) rk4a h y 2 := ⟨_, rfl⟩
  have hZ1 : Z1 = y + (h * (1 / 2)) • F y := by
    rw [hZ1def, rk4_Z1, hK, rk4_Z0]
  have hZ2 : Z2 = y + (h * (1 / 2)) • F Z1 := by rw [hZ2def, rk4_Z2, hK, hZ1def]
  have hZ3 : rkZ F (fun _ => id) rk4a h y 3 = y + h • F Z2 := by rw [rk4_Z3, hK, hZ2def]
  have hd1 : ‖Z1 - W2‖ ≤ h * (1 / 2) * e := by
    rw [hZ1, hW2, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hh2]
    exact mul_le_mul_of_nonneg_left hB1e hh2
  have hF2 : ‖F Z1 - B2‖ ≤ L * (h * (1 / 2) * e) + e := by
    calc ‖F Z1 - B2‖ ≤ ‖F Z1 - F W2‖ + ‖F W2 - B2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * ‖Z1 - W2‖ + e := add_le_add (hF _ _) hB2e
      _ ≤ L * (h * (1 / 2) * e) + e := by gcongr
  have hd2 : ‖Z2 - W3‖ ≤ h * (1 / 2) * (L * (h * (1 / 2) * e) + e) := by
    rw [hZ2, hW3, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hh2]
    exact mul_le_mul_of_nonneg_left hF2 hh2
  have hF3 : ‖F Z2 - B3‖ ≤ L * (h * (1 / 2) * (L * (h * (1 / 2) * e) + e)) + e := by
    calc ‖F Z2 - B3‖ ≤ ‖F Z2 - F W3‖ + ‖F W3 - B3‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * ‖Z2 - W3‖ + e := add_le_add (hF _ _) hB3e
      _ ≤ _ := by gcongr
  have hgoal : C_M * (1 + L * h₀ * (1 + L * h₀)) * (h * ε) =
      (1 + L * h₀ * (1 + L * h₀)) * (h * e) := by rw [he_def]; ring
  intro j hj
  rw [hgoal]
  interval_cases j
  · rw [rk4_Z0, distLR_eq_zero_of_rank_le (hy.trans (by omega))]
    exact mul_nonneg (by nlinarith [mul_nonneg hL (hh.trans hhh₀)]) (mul_nonneg hh he)
  · refine (show distLR (15 * r) Z1 ≤ h * (1 / 2) * e from ?_).trans hR.1 |>.trans' (le_of_eq
      (by rw [hZ1def]))
    rw [hZ1]
    exact (lemma8 (k := 2 * r) (by omega) hy (F y) hh2 hB1r).trans
      (mul_le_mul_of_nonneg_left hB1e hh2)
  · refine ((show distLR (15 * r) Z2 ≤ h * (1 / 2) * (L * (h * (1 / 2) * e) + e) from ?_).trans
      hR.2.1).trans' (le_of_eq (by rw [hZ2def]))
    rw [hZ2]
    exact (lemma8 (k := 2 * (3 * r)) (by omega) hy (F Z1) hh2 hB2r).trans
      (mul_le_mul_of_nonneg_left hF2 hh2)
  · refine (show distLR (15 * r) (rkZ F (fun _ => id) rk4a h y 3) ≤
      h * (L * (h * (1 / 2) * (L * (h * (1 / 2) * e) + e)) + e) from ?_).trans hR.2.2
    rw [hZ3]
    exact (lemma8 (k := 2 * (7 * r)) (by omega) hy (F Z2) hh hB3r).trans
      (mul_le_mul_of_nonneg_left hF3 hh)

end RK4modStages


section Thm10

open scoped LeanDLRA.Frobenius

variable {Ω K : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace K] {m n : Type*} [Fintype m] [Fintype n]

/-- Stage maps of the oversampled randomized RK4 method of arXiv 2409.06384, Sec. 3.4: rank `15 r`
for the four stages (`j < 4`), rank `r` for the final update. -/
def rk4R {K E : Type*} (R15 Rr : K → E → E) (j : ℕ) : K → E → E := if j < 4 then R15 else Rr

/-- Target sets of the oversampled RK4 stages (arXiv 2409.06384, Sec. 3.4). -/
def rk4S (m n : Type*) [Fintype n] (r j : ℕ) : Set (Matrix m n ℝ) :=
  if j < 4 then lowRankSet m n (15 * r) else lowRankSet m n r

/-- The constant of Lemma 9 / Theorem 10 of arXiv 2409.06384: it depends only on `L`, `h₀`, `C_M`,
`C_N`, `C_1`. -/
noncomputable def rk4K (L h₀ C_M C_N C_1 : ℝ) : ℝ :=
  C_N * C_M + (C_N + 1) * (L * C_N * (C_M * (1 + L * h₀ * (1 + L * h₀))) *
    (1 + L * (C_N + 1) * 2 * h₀) ^ 4 * h₀ + C_1)

/-- Real-number form of the local error bound of Lemma 9 (auxiliary; arXiv 2409.06384). -/
theorem rk4_ell_le {L h h₀ C_M C_N C_1 ε : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hh₀ : h ≤ h₀)
    (hCM : 0 ≤ C_M) (hCN : 0 ≤ C_N) (hC1 : 0 ≤ C_1) (hε : 0 ≤ ε) :
    C_N * (C_M * h * ε) + (C_N + 1) * (∑ j ∈ range 4, |h * rk4b j| *
      (L * C_N * (C_M * (1 + L * h₀ * (1 + L * h₀))) *
        (1 + L * (C_N + 1) * (∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l|) * h₀) ^ (j + 1) *
          (h * ε)) + C_1 * h ^ 5) ≤
      rk4K L h₀ C_M C_N C_1 * (h * ε + h ^ 5) := by
  rw [rk4_Aa]
  set α := L * C_N * (C_M * (1 + L * h₀ * (1 + L * h₀))) with hα
  set κ := L * (C_N + 1) * 2 * h₀ with hκ
  have hh₀0 : 0 ≤ h₀ := hh.trans hh₀
  have hα0 : 0 ≤ α := mul_nonneg (mul_nonneg hL hCN) (mul_nonneg hCM (by positivity))
  have hκ0 : 0 ≤ κ := by positivity
  have hhε : 0 ≤ h * ε := mul_nonneg hh hε
  have hsum : ∑ j ∈ range 4, |h * rk4b j| * (α * (1 + κ) ^ (j + 1) * (h * ε)) ≤
      α * (1 + κ) ^ 4 * h₀ * (h * ε) := by
    have hterm : ∀ j ∈ range 4, |h * rk4b j| * (α * (1 + κ) ^ (j + 1) * (h * ε)) ≤
        |rk4b j| * (α * (1 + κ) ^ 4 * h₀ * (h * ε)) := by
      intro j hj
      rw [abs_mul, abs_of_nonneg hh, mul_comm h, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hpow : (1 + κ) ^ (j + 1) ≤ (1 + κ) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by have := Finset.mem_range.1 hj; omega)
      have t1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hα0) hhε
      have t2 := mul_le_mul hh₀ t1 (mul_nonneg (mul_nonneg hα0 (pow_nonneg (by linarith) _)) hhε)
        hh₀0
      calc h * (α * (1 + κ) ^ (j + 1) * (h * ε)) ≤ h₀ * (α * (1 + κ) ^ 4 * (h * ε)) := t2
        _ = α * (1 + κ) ^ 4 * h₀ * (h * ε) := by ring
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, rk4_Bb, one_mul]
  have hK : rk4K L h₀ C_M C_N C_1 = C_N * C_M + (C_N + 1) * (α * (1 + κ) ^ 4 * h₀ + C_1) := by
    rw [rk4K]
  rw [hK]
  have hC : 0 ≤ C_N + 1 := by linarith
  have hp5 : 0 ≤ h ^ 5 := pow_nonneg hh 5
  have hG : 0 ≤ α * (1 + κ) ^ 4 * h₀ := mul_nonneg (mul_nonneg hα0 (by positivity)) hh₀0
  have e1 : C_N * (C_M * h * ε) = C_N * C_M * (h * ε) := by ring
  rw [e1]
  have t1 := mul_le_mul_of_nonneg_left (add_le_add_left hsum (C_1 * h ^ 5)) hC
  have key : C_N * C_M * (h * ε) + (C_N + 1) * (C_1 * h ^ 5 + α * (1 + κ) ^ 4 * h₀ * (h * ε)) ≤
      (C_N * C_M + (C_N + 1) * (α * (1 + κ) ^ 4 * h₀ + C_1)) * (h * ε + h ^ 5) := by
    have e2 : (C_N * C_M + (C_N + 1) * (α * (1 + κ) ^ 4 * h₀ + C_1)) * (h * ε + h ^ 5) -
        (C_N * C_M * (h * ε) + (C_N + 1) * (C_1 * h ^ 5 + α * (1 + κ) ^ 4 * h₀ * (h * ε))) =
        C_N * C_M * h ^ 5 + (C_N + 1) * (α * (1 + κ) ^ 4 * h₀ * h ^ 5 + C_1 * (h * ε)) := by
      ring
    have : 0 ≤ C_N * C_M * h ^ 5 + (C_N + 1) * (α * (1 + κ) ^ 4 * h₀ * h ^ 5 + C_1 * (h * ε)) :=
      add_nonneg (mul_nonneg (mul_nonneg hCN hCM) hp5)
        (mul_nonneg hC (add_nonneg (mul_nonneg hG hp5) (mul_nonneg hC1 hhε)))
    linarith
  calc C_N * C_M * (h * ε) + (C_N + 1) * (∑ j ∈ range 4, |h * rk4b j| *
        (α * (1 + κ) ^ (j + 1) * (h * ε)) + C_1 * h ^ 5)
      ≤ C_N * C_M * (h * ε) + (C_N + 1) * (C_1 * h ^ 5 + α * (1 + κ) ^ 4 * h₀ * (h * ε)) := by
        rw [add_comm (∑ j ∈ range 4, _) (C_1 * h ^ 5)]
        linarith
    _ ≤ _ := key


/-- **Lemma 9 of arXiv 2409.06384** (local error of the stage-oversampled randomized RK4, Sec. 3.4):
the four RK4 stages are sketched by a randomized map `R15` (rank `15 r` in the paper) and the update
by a randomized map `Rr` with values of rank `≤ r`, with independent sketches and the moment
assumption (7) at ranks `15 r` and `r` (common constant `C_N`). Under (21), Lipschitz `F` and the
classical RK4 order `‖Ψ^h_{RK4}(Y) - Φ^h(Y)‖ ≤ C_1 h⁵` on rank `≤ r`, every step satisfies `‖Y_{i+1}
- Φ^h(Y_i)‖_{L^q} ≤ K (h ε + h⁵)` with `K = rk4K L h₀ C_M C_N C_1`. Differences: (7) replaces
Theorem 2 (Gaussian Nyström); (21) is assumed for inputs of rank `≤ k` (the paper: `M_k`); the RK4
order is a hypothesis (the paper: Assumption 2 and the classical order conditions); the stage maps
need not have rank `15 r` outputs. The proof compares the classical RK4 stages with the low-rank
chain `Y + (h/2)[[F(Y)]]_{2r}`, … via Lemmas 7 and 8 (ranks `3r, 7r, 15r`) and then applies Theorem
11 (`rrk_local`). -/
theorem lemma9 {F : Matrix m n ℝ → Matrix m n ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) {Φ : ℝ → Matrix m n ℝ → Matrix m n ℝ} {h₀ : ℝ}
    (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀) (hΦ0 : ∀ Y, Φ 0 Y = Y)
    {r : ℕ} {C_M ε : ℝ} (hCM : 0 ≤ C_M) (hε : 0 ≤ ε)
    (h21 : ∀ k, r ≤ k → k ≤ 15 * r → ∀ Y : Matrix m n ℝ, Y.rank ≤ k → ∀ t ∈ Ioc 0 h₀,
      distLR k (Φ t Y) ≤ C_M * t * ε)
    {R15 Rr : K → Matrix m n ℝ → Matrix m n ℝ} (hR15 : Measurable (Function.uncurry R15))
    (hRr : Measurable (Function.uncurry Rr)) (hRr_rank : ∀ k z, (Rr k z).rank ≤ r)
    {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ × ℕ → Ω → K} (hξ : ∀ p, Measurable (ξ p))
    (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom15 : ∀ p z, eLpNorm (fun ω => R15 (ξ p ω) z - z) q P ≤
      ENNReal.ofReal (C_N * distLR (15 * r) z))
    (hmomr : ∀ p z, eLpNorm (fun ω => Rr (ξ p ω) z - z) q P ≤
      ENNReal.ofReal (C_N * distLR r z))
    {C_1 : ℝ} (hC1 : 0 ≤ C_1)
    (hRK4 : ∀ Y : Matrix m n ℝ, Y.rank ≤ r → ∀ t ∈ Ioc 0 h₀,
      ‖(Y + t • ∑ j ∈ range 4, rk4b j • rkK F (fun _ => id) rk4a t Y j) - Φ t Y‖ ≤ C_1 * t ^ 5)
    {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) (A₀ : Matrix m n ℝ) (i : ℕ) :
    eLpNorm (fun ω => rrkIter F (rk4R R15 Rr) rk4a rk4b 4 h ξ A₀ (i + 1) ω -
        Φ h (rrkIter F (rk4R R15 Rr) rk4a rk4b 4 h ξ A₀ i ω)) q P ≤
      ENNReal.ofReal (rk4K L h₀ C_M C_N C_1 * (h * ε + h ^ 5)) := by
  have : BorelSpace (Matrix m n ℝ) := inferInstanceAs (BorelSpace (m → n → ℝ))
  have hΦc : Continuous (Φ h) := by
    have : LipschitzWith ⟨Real.exp (L * h), (Real.exp_pos _).le⟩ (Φ h) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact flow_lipschitz hL hF hΦ hΦ0 ⟨hh.le, hh₀⟩ x y
    exact this.continuous
  have hR : ∀ j, Measurable (Function.uncurry (rk4R R15 Rr j)) := by
    intro j; by_cases hj : j < 4 <;> simp only [rk4R, hj, ite_true, ite_false] <;> assumption
  have hRS : ∀ k z, rk4R R15 Rr 4 k z ∈ rk4S m n r 4 := by
    intro k z; simp only [rk4R, rk4S, lt_irrefl, ite_false, mem_lowRankSet]; exact hRr_rank k z
  have hmom : ∀ i j z, eLpNorm (fun ω => rk4R R15 Rr j (ξ (i, j) ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z (rk4S m n r j)) := by
    intro i j z
    by_cases hj : j < 4
    · simp only [rk4R, rk4S, hj, ite_true]; exact hmom15 (i, j) z
    · simp only [rk4R, rk4S, hj, ite_false]; exact hmomr (i, j) z
  have hS4 : rk4S m n r 4 = lowRankSet m n r := by simp [rk4S]
  have hβ : ∀ y ∈ rk4S m n r 4, ∀ j < 4,
      Metric.infDist (rkZ F (fun _ => id) rk4a h y j) (rk4S m n r j) ≤
        C_M * (1 + L * h₀ * (1 + L * h₀)) * (h * ε) := by
    intro y hy j hj
    rw [hS4, mem_lowRankSet] at hy
    have : rk4S m n r j = lowRankSet m n (15 * r) := by simp [rk4S, hj]
    rw [this]
    exact rk4_stage_dist hL hF (hh.trans_le hh₀) hΦ hΦ0 hCM hε h21 hh.le hh₀ hy j hj
  have hθ : ∀ y ∈ rk4S m n r 4, Metric.infDist (Φ h y) (rk4S m n r 4) ≤ C_M * h * ε := by
    intro y hy
    rw [hS4, mem_lowRankSet] at hy
    rw [hS4]
    exact h21 r le_rfl (by omega) y hy h ⟨hh, hh₀⟩
  have hρ : ∀ y ∈ rk4S m n r 4, ‖(y + h • ∑ j ∈ range 4, rk4b j • rkK F (fun _ => id) rk4a h y j)
      - Φ h y‖ ≤ C_1 * h ^ 5 := by
    intro y hy
    rw [hS4, mem_lowRankSet] at hy
    exact hRK4 y hy h ⟨hh, hh₀⟩
  have hB0 : 0 ≤ C_M * (1 + L * h₀ * (1 + L * h₀)) := by
    have := hh.le.trans hh₀; positivity
  have hE := uniform_majorant hL hCN hB0 hh.le hh₀ (mul_nonneg hh.le hε) rk4a 4
    (β := fun _ => C_M * (1 + L * h₀ * (1 + L * h₀)) * (h * ε)) (fun _ _ => le_rfl)
  have hE0 : ∀ j, 0 ≤ L * C_N * (C_M * (1 + L * h₀ * (1 + L * h₀))) *
      (1 + L * (C_N + 1) * (∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l|) * h₀) ^ (j + 1) *
        (h * ε) := by
    intro j
    have := hh.le.trans hh₀
    have : 0 ≤ ∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have := mul_nonneg hh.le hε
    positivity
  refine (rrk_local (P := P) hL hF hR 4 hRS hCN hξ hind hq hqt hmom rk4a rk4b h A₀
    hΦc.measurable hβ hθ hρ hE0 hE i).trans (ENNReal.ofReal_le_ofReal ?_)
  exact rk4_ell_le hL hh.le hh₀ hCM hCN hC1 hε

/-- **Theorem 10 of arXiv 2409.06384** (the stage-oversampled randomized RK4 has order four): under
the hypotheses of `lemma9`, `distLR r (A₀) ≤ δ`, `Y₀ = 𝒩(A₀)` and `N h ≤ T`, `‖Y_N - A(Nh)‖_{L^q} ≤
e^{LT} max(C_N, T K) (δ + ε + h⁴)`. Same differences as `lemma9`. -/
theorem thm10 {F : Matrix m n ℝ → Matrix m n ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) {Φ : ℝ → Matrix m n ℝ → Matrix m n ℝ} {h₀ : ℝ}
    (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀) (hΦ0 : ∀ Y, Φ 0 Y = Y)
    {r : ℕ} {C_M ε : ℝ} (hCM : 0 ≤ C_M) (hε : 0 ≤ ε)
    (h21 : ∀ k, r ≤ k → k ≤ 15 * r → ∀ Y : Matrix m n ℝ, Y.rank ≤ k → ∀ t ∈ Ioc 0 h₀,
      distLR k (Φ t Y) ≤ C_M * t * ε)
    {R15 Rr : K → Matrix m n ℝ → Matrix m n ℝ} (hR15 : Measurable (Function.uncurry R15))
    (hRr : Measurable (Function.uncurry Rr)) (hRr_rank : ∀ k z, (Rr k z).rank ≤ r)
    {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ × ℕ → Ω → K} (hξ : ∀ p, Measurable (ξ p))
    (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom15 : ∀ p z, eLpNorm (fun ω => R15 (ξ p ω) z - z) q P ≤
      ENNReal.ofReal (C_N * distLR (15 * r) z))
    (hmomr : ∀ p z, eLpNorm (fun ω => Rr (ξ p ω) z - z) q P ≤
      ENNReal.ofReal (C_N * distLR r z))
    {C_1 : ℝ} (hC1 : 0 ≤ C_1)
    (hRK4 : ∀ Y : Matrix m n ℝ, Y.rank ≤ r → ∀ t ∈ Ioc 0 h₀,
      ‖(Y + t • ∑ j ∈ range 4, rk4b j • rkK F (fun _ => id) rk4a t Y j) - Φ t Y‖ ≤ C_1 * t ^ 5)
    {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) {T : ℝ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ => F) A 0 T) {δ : ℝ} (hδ : distLR r (A 0) ≤ δ) {N : ℕ}
    (hN : N * h ≤ T) :
    eLpNorm (fun ω => rrkIter F (rk4R R15 Rr) rk4a rk4b 4 h ξ (A 0) N ω - A (N * h)) q P ≤
      ENNReal.ofReal (Real.exp (L * T) * max C_N (T * rk4K L h₀ C_M C_N C_1) *
        (δ + ε + h ^ 4)) := by
  have : BorelSpace (Matrix m n ℝ) := inferInstanceAs (BorelSpace (m → n → ℝ))
  have hΦc : Continuous (Φ h) := by
    have : LipschitzWith ⟨Real.exp (L * h), (Real.exp_pos _).le⟩ (Φ h) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact flow_lipschitz hL hF hΦ hΦ0 ⟨hh.le, hh₀⟩ x y
    exact this.continuous
  have hR : ∀ j, Measurable (Function.uncurry (rk4R R15 Rr j)) := by
    intro j; by_cases hj : j < 4 <;> simp only [rk4R, hj, ite_true, ite_false] <;> assumption
  have hRS : ∀ k z, rk4R R15 Rr 4 k z ∈ rk4S m n r 4 := by
    intro k z; simp only [rk4R, rk4S, lt_irrefl, ite_false, mem_lowRankSet]; exact hRr_rank k z
  have hmom : ∀ i j z, eLpNorm (fun ω => rk4R R15 Rr j (ξ (i, j) ω) z - z) q P ≤
      ENNReal.ofReal (C_N * Metric.infDist z (rk4S m n r j)) := by
    intro i j z
    by_cases hj : j < 4
    · simp only [rk4R, rk4S, hj, ite_true]; exact hmom15 (i, j) z
    · simp only [rk4R, rk4S, hj, ite_false]; exact hmomr (i, j) z
  have hS4 : rk4S m n r 4 = lowRankSet m n r := by simp [rk4S]
  have hβ : ∀ y ∈ rk4S m n r 4, ∀ j < 4,
      Metric.infDist (rkZ F (fun _ => id) rk4a h y j) (rk4S m n r j) ≤
        C_M * (1 + L * h₀ * (1 + L * h₀)) * (h * ε) := by
    intro y hy j hj
    rw [hS4, mem_lowRankSet] at hy
    have : rk4S m n r j = lowRankSet m n (15 * r) := by simp [rk4S, hj]
    rw [this]
    exact rk4_stage_dist hL hF (hh.trans_le hh₀) hΦ hΦ0 hCM hε h21 hh.le hh₀ hy j hj
  have hθ : ∀ y ∈ rk4S m n r 4, Metric.infDist (Φ h y) (rk4S m n r 4) ≤ C_M * h * ε := by
    intro y hy
    rw [hS4, mem_lowRankSet] at hy
    rw [hS4]
    exact h21 r le_rfl (by omega) y hy h ⟨hh, hh₀⟩
  have hρ : ∀ y ∈ rk4S m n r 4, ‖(y + h • ∑ j ∈ range 4, rk4b j • rkK F (fun _ => id) rk4a h y j)
      - Φ h y‖ ≤ C_1 * h ^ 5 := by
    intro y hy
    rw [hS4, mem_lowRankSet] at hy
    exact hRK4 y hy h ⟨hh, hh₀⟩
  have hB0 : 0 ≤ C_M * (1 + L * h₀ * (1 + L * h₀)) := by
    have := hh.le.trans hh₀; positivity
  have hE := uniform_majorant hL hCN hB0 hh.le hh₀ (mul_nonneg hh.le hε) rk4a 4
    (β := fun _ => C_M * (1 + L * h₀ * (1 + L * h₀)) * (h * ε)) (fun _ _ => le_rfl)
  have hE0 : ∀ j, 0 ≤ L * C_N * (C_M * (1 + L * h₀ * (1 + L * h₀))) *
      (1 + L * (C_N + 1) * (∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l|) * h₀) ^ (j + 1) *
        (h * ε) := by
    intro j
    have := hh.le.trans hh₀
    have : 0 ≤ ∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have := mul_nonneg hh.le hε
    positivity
  have hδ' : Metric.infDist (A 0) (rk4S m n r 4) ≤ δ := by rw [hS4]; exact hδ
  refine (rrk_global (P := P) hL hF hΦ hΦ0 hA hR 4 hRS hCN hξ hind hq hqt hmom rk4a rk4b hh hh₀
    hδ' hβ hθ hρ hE0 hE hN).trans (ENNReal.ofReal_le_ofReal ?_)
  have hℓ := rk4_ell_le (ε := ε) hL hh.le hh₀ hCM hCN hC1 hε
  set Kc := rk4K L h₀ C_M C_N C_1 with hKc
  have hδ0 : 0 ≤ δ := distLR_nonneg.trans hδ
  have hK0 : 0 ≤ Kc := by
    rw [hKc, rk4K]
    have := hh.le.trans hh₀
    positivity
  have hW0 : 0 ≤ ε + h ^ 4 := by positivity
  have hNl : (N : ℝ) * (C_N * (C_M * h * ε) + (C_N + 1) * (∑ j ∈ range 4, |h * rk4b j| *
      (L * C_N * (C_M * (1 + L * h₀ * (1 + L * h₀))) *
        (1 + L * (C_N + 1) * (∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l|) * h₀) ^ (j + 1) *
          (h * ε)) + C_1 * h ^ 5)) ≤ T * Kc * (ε + h ^ 4) := by
    calc _ ≤ (N : ℝ) * (Kc * (h * ε + h ^ 5)) := mul_le_mul_of_nonneg_left hℓ (Nat.cast_nonneg N)
      _ = (N * h) * (Kc * (ε + h ^ 4)) := by ring
      _ ≤ T * (Kc * (ε + h ^ 4)) := mul_le_mul_of_nonneg_right hN (mul_nonneg hK0 hW0)
      _ = T * Kc * (ε + h ^ 4) := by ring
  have t1 := mul_le_mul_of_nonneg_right (le_max_left C_N (T * Kc)) hδ0
  have t2 := mul_le_mul_of_nonneg_right (le_max_right C_N (T * Kc)) hW0
  have hexp := (Real.exp_pos (L * T)).le
  calc Real.exp (L * T) * (C_N * δ + N * (C_N * (C_M * h * ε) + (C_N + 1) *
        (∑ j ∈ range 4, |h * rk4b j| * (L * C_N * (C_M * (1 + L * h₀ * (1 + L * h₀))) *
          (1 + L * (C_N + 1) * (∑ j ∈ range 4, ∑ l ∈ range j, |rk4a j l|) * h₀) ^ (j + 1) *
            (h * ε)) + C_1 * h ^ 5)))
      ≤ Real.exp (L * T) * (max C_N (T * Kc) * δ + max C_N (T * Kc) * (ε + h ^ 4)) :=
        mul_le_mul_of_nonneg_left (by linarith) hexp
    _ = _ := by ring

/-- **Theorem 10 of arXiv 2409.06384, tail bound**: with `C = e^{LT} max(C_N, T K)` and `C_N > 0`,
`P(‖Y_N - A(Nh)‖ ≥ C η (δ + ε + h⁴)) ≤ η^{-q}` for `η > 0` (Markov, as in Corollary 4). -/
theorem thm10_tail {F : Matrix m n ℝ → Matrix m n ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) {Φ : ℝ → Matrix m n ℝ → Matrix m n ℝ} {h₀ : ℝ}
    (hΦ : ∀ Y, ODESolution (fun _ => F) (fun t => Φ t Y) 0 h₀) (hΦ0 : ∀ Y, Φ 0 Y = Y)
    {r : ℕ} {C_M ε : ℝ} (hCM : 0 ≤ C_M) (hε : 0 ≤ ε)
    (h21 : ∀ k, r ≤ k → k ≤ 15 * r → ∀ Y : Matrix m n ℝ, Y.rank ≤ k → ∀ t ∈ Ioc 0 h₀,
      distLR k (Φ t Y) ≤ C_M * t * ε)
    {R15 Rr : K → Matrix m n ℝ → Matrix m n ℝ} (hR15 : Measurable (Function.uncurry R15))
    (hRr : Measurable (Function.uncurry Rr)) (hRr_rank : ∀ k z, (Rr k z).rank ≤ r)
    {C_N : ℝ} (hCN : 0 ≤ C_N) {ξ : ℕ × ℕ → Ω → K} (hξ : ∀ p, Measurable (ξ p))
    (hind : iIndepFun ξ P) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hmom15 : ∀ p z, eLpNorm (fun ω => R15 (ξ p ω) z - z) q P ≤
      ENNReal.ofReal (C_N * distLR (15 * r) z))
    (hmomr : ∀ p z, eLpNorm (fun ω => Rr (ξ p ω) z - z) q P ≤
      ENNReal.ofReal (C_N * distLR r z))
    {C_1 : ℝ} (hC1 : 0 ≤ C_1)
    (hRK4 : ∀ Y : Matrix m n ℝ, Y.rank ≤ r → ∀ t ∈ Ioc 0 h₀,
      ‖(Y + t • ∑ j ∈ range 4, rk4b j • rkK F (fun _ => id) rk4a t Y j) - Φ t Y‖ ≤ C_1 * t ^ 5)
    {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀) {T : ℝ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ => F) A 0 T) {δ : ℝ} (hδ : distLR r (A 0) ≤ δ) {N : ℕ}
    (hN : N * h ≤ T) (hCNpos : 0 < C_N) {η : ℝ} (hη : 0 < η) :
    P {ω | Real.exp (L * T) * max C_N (T * rk4K L h₀ C_M C_N C_1) * η * (δ + ε + h ^ 4) ≤
      ‖rrkIter F (rk4R R15 Rr) rk4a rk4b 4 h ξ (A 0) N ω - A (N * h)‖} ≤
      ENNReal.ofReal (η ^ (-q.toReal)) := by
  have h10 := thm10 hL hF hΦ hΦ0 hCM hε h21 hR15 hRr hRr_rank hCN hξ hind hq hqt hmom15 hmomr hC1
    hRK4 hh hh₀ hA hδ hN
  have hδ0 : 0 ≤ δ := distLR_nonneg.trans hδ
  have hpos : 0 < Real.exp (L * T) * max C_N (T * rk4K L h₀ C_M C_N C_1) * (δ + ε + h ^ 4) :=
    mul_pos (mul_pos (Real.exp_pos _) (lt_of_lt_of_le hCNpos (le_max_left _ _))) (by positivity)
  have := markov_tail (P := P) (zero_lt_one.trans_le hq).ne' hqt hpos h10 hη
  rw [show Real.exp (L * T) * max C_N (T * rk4K L h₀ C_M C_N C_1) * η * (δ + ε + h ^ 4) =
    η * (Real.exp (L * T) * max C_N (T * rk4K L h₀ C_M C_N C_1) * (δ + ε + h ^ 4)) by ring]
  exact this

end Thm10


section Instances

/-- Any family of random variables on the one-point probability space is independent (auxiliary;
arXiv 2409.06384, non-vacuity of the hypotheses). -/
theorem iIndepFun_unit {ι K : Type*} [MeasurableSpace K] (ξ : ι → Unit → K) :
    iIndepFun ξ (Measure.dirac ()) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  have h1 : ∀ A : Set Unit, (Measure.dirac ()) A = if () ∈ A then 1 else 0 := by
    intro A
    rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_apply]
    simp
  rw [h1, Finset.prod_congr rfl fun i _ => h1 _, Finset.prod_boole]
  simp

/-- Constant curves solve `ẏ = 0` (auxiliary; arXiv 2409.06384, non-vacuity of the hypotheses). -/
theorem odeSolution_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E)
    (a b : ℝ) : ODESolution (fun _ _ => (0 : E)) (fun _ => c) a b :=
  ⟨continuousOn_const, fun _ _ => hasDerivWithinAt_const _ _ _⟩

/-- arXiv 2409.06384: the hypotheses of `thm3` are consistent (trivial instance on the one-point
space). -/
example : eLpNorm (fun ω => idealIter (fun (_ : Unit) (z : ℝ) => z) ((fun _ Y => Y) 1)
      (fun _ _ => ()) ((fun _ => (1 : ℝ)) 0) 1 ω - (fun _ => (1 : ℝ)) ((1 : ℕ) * 1)) 2
      (Measure.dirac ()) ≤
    ENNReal.ofReal (1 * Real.exp (0 * 1) * max 1 (0 * 1) * (0 + 0)) :=
  thm3 (F := fun _ => (0 : ℝ)) le_rfl (fun _ _ => by simp) (Φ := fun _ Y => Y) (h₀ := 1)
    (fun Y => odeSolution_const Y 0 1) (fun _ => rfl) (S := Set.univ) le_rfl le_rfl
    (fun _ _ _ _ => by rw [Metric.infDist_zero_of_mem (Set.mem_univ _)]; simp)
    (odeSolution_const 1 0 1) (by rw [Metric.infDist_zero_of_mem (Set.mem_univ _)])
    measurable_snd
    (fun _ _ => Set.mem_univ _) zero_le_one (fun _ => measurable_const) (iIndepFun_unit _)
    one_le_two (by simp) (fun _ _ => by simp) one_pos le_rfl (by norm_num)

/-- arXiv 2409.06384: the hypotheses of `thm5` are consistent (trivial instance: `F = 0`, two
stages, one point). -/
example : ∃ C : ℝ, 0 < C ∧ eLpNorm (fun ω => rrkIter (fun _ : ℝ => (0 : ℝ))
      (fun _ (_ : Unit) z => z) (fun _ _ => 0) (fun _ => 1 / 2) 2 1 (fun _ _ => ())
      ((fun _ => (1 : ℝ)) 0) 1 ω - (fun _ => (1 : ℝ)) ((1 : ℕ) * 1)) 2 (Measure.dirac ()) ≤
      ENNReal.ofReal (C * (0 + 0 + 1 ^ min 1 ((fun _ => 1) 1 + 1))) := by
  obtain ⟨C, hC, hall⟩ := thm5 0 1 1 0 1 0 0 2 1 (fun _ => 1) (fun _ _ => 0) (fun _ => 1 / 2)
    le_rfl le_rfl zero_le_one le_rfl le_rfl le_rfl (by simp) (fun _ _ _ _ _ => le_rfl)
  refine ⟨C, hC, (hall (Measure.dirac ()) (fun _ => (0 : ℝ)) (fun _ Y => Y) Set.univ 0
    (fun _ => 1) 0 (fun (_ : Unit) z => z) (fun _ _ => ()) 2 1 1 (fun _ _ => by simp)
    (fun Y => odeSolution_const Y 0 1) (fun _ => rfl) le_rfl
    (fun _ _ _ _ => by rw [Metric.infDist_zero_of_mem (Set.mem_univ _)]; simp)
    (odeSolution_const 1 0 1) (by rw [Metric.infDist_zero_of_mem (Set.mem_univ _)])
    measurable_snd (fun _ _ => Set.mem_univ _) (fun _ => measurable_const) (iIndepFun_unit _)
    one_le_two (by simp) (fun _ _ => by simp) (fun _ _ _ _ _ _ _ => by simp [rkZ])
    (fun _ _ _ _ => by simp [rkK_eq]) one_pos le_rfl (by norm_num)).1⟩

open scoped LeanDLRA.Frobenius in
/-- arXiv 2409.06384: the hypotheses of `thm10` are consistent (trivial instance: `1 × 1` matrices,
`r = 1`). -/
example : eLpNorm (fun ω => rrkIter (fun _ : Matrix (Fin 1) (Fin 1) ℝ => 0)
      (rk4R (fun (_ : Unit) z => z) (fun _ z => z)) rk4a rk4b 4 1 (fun _ _ => ())
      ((fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0) 1 ω -
        (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) ((1 : ℕ) * 1)) 2 (Measure.dirac ()) ≤
      ENNReal.ofReal (Real.exp (0 * 1) * max 1 (1 * rk4K 0 1 0 1 0) * (0 + 0 + 1 ^ 4)) := by
  have hrk : ∀ Y : Matrix (Fin 1) (Fin 1) ℝ, Y.rank ≤ 1 := fun Y =>
    (Matrix.rank_le_card_width Y).trans (by simp)
  exact thm10 (F := fun _ => 0) le_rfl (fun _ _ => by simp) (Φ := fun _ Y => Y) (h₀ := 1)
    (fun Y => odeSolution_const Y 0 1) (fun _ => rfl) (r := 1) le_rfl le_rfl
    (fun _ _ _ Y hY _ _ => by rw [distLR_eq_zero_of_rank_le hY]; simp) measurable_snd
    measurable_snd (fun _ z => hrk z) zero_le_one (fun _ => measurable_const)
    (iIndepFun_unit _) one_le_two (by simp) (fun _ _ => by simp) (fun _ _ => by simp) le_rfl
    (fun _ _ _ _ => by simp [rkK_eq]) one_pos le_rfl (odeSolution_const 1 0 1)
    (by rw [distLR_eq_zero_of_rank_le (hrk _)]) (by norm_num)

end Instances


section CoreRK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Relation to the core (arXiv 2409.06384, scheme (16)): the stages `rkZ F id a h y` and the result
of the classical explicit Runge–Kutta step (all stage maps `= id`) form a full Runge–Kutta step in
the sense of `LeanDLRA.RungeKuttaBUG.IsGalerkinRKStep` (all projectors `= 1`), for the strictly
lower triangular part of the tableau `a` restricted to `s` stages. -/
theorem isGalerkinRKStep_rk (F : E → E) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (s : ℕ) (c : Fin s → ℝ)
    (t h : ℝ) (y : E) :
    RungeKuttaBUG.IsGalerkinRKStep (fun _ => F)
      (fun i j : Fin s => if (j : ℕ) < i then a i j else 0) (fun i => b i) c (fun _ => 1) 1 t h y
      (fun i => rkZ F (fun _ => id) a h y i)
      (y + h • ∑ j ∈ range s, b j • rkK F (fun _ => id) a h y j) := by
  have hK : ∀ l, rkK F (fun _ => id) a h y l = F (rkZ F (fun _ => id) a h y l) :=
    fun l => rkK_eq _ _ _ _ _ _
  constructor
  · intro i
    change rkZ F (fun _ => id) a h y i = y + h • ∑ j : Fin s,
      (if (j : ℕ) < i then a i j else 0) • F (rkZ F (fun _ => id) a h y j)
    conv_lhs => rw [rkZ]
    congr 2
    simp only [hK, ite_smul, zero_smul]
    rw [Fin.sum_univ_eq_sum_range (fun l => a i l • F (rkZ F (fun _ => id) a h y l)) i,
      Fin.sum_univ_eq_sum_range (fun j => if j < (i : ℕ) then
        a i j • F (rkZ F (fun _ => id) a h y j) else 0) s, ← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hj; exact ⟨hj.trans i.isLt, hj⟩
    · intro hj; exact hj.2
  · change y + h • ∑ j ∈ range s, b j • rkK F (fun _ => id) a h y j =
      y + h • ∑ i : Fin s, b i • F (rkZ F (fun _ => id) a h y i)
    congr 2
    rw [Fin.sum_univ_eq_sum_range (fun j => b j • F (rkZ F (fun _ => id) a h y j)) s]
    exact Finset.sum_congr rfl fun j _ => by rw [hK]

end CoreRK

end LeanDLRA.Literature.P2409_06384
