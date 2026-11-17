import LeanDLRA.OpenProblems.Stiff.Part1Defs
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Stability.Energy
import LeanDLRA.Integrators.BUG
import LeanDLRA.Stiff.ImplicitBUG
import LeanDLRA.Stiff.ImplicitSolvability

/-!
# Open problems OP-ST-02, OP-ST-03, OP-ST-04, OP-ST-05
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.OpenProblems.Stiff

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem eq_zero_of_inner_self_eq_zero_of_nonpos {C : E →L[ℝ] E}
    (hCsym : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫) (hCneg : ∀ x, ⟪C x, x⟫ ≤ 0) {x : E}
    (hx : ⟪C x, x⟫ = 0) : C x = 0 := by
  by_contra hne
  have ha : 0 < ‖C x‖ ^ 2 := by positivity
  have hb := hCneg (C x)
  obtain ⟨b, hbdef⟩ : ∃ b, b = ⟪C (C x), C x⟫ := ⟨_, rfl⟩
  rw [← hbdef] at hb
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖C x‖ ^ 2 / (|b| + 1) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  have h1 := hCneg (x + t • C x)
  have h3 : ⟪C x, C x⟫ = ‖C x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have e : ⟪C (x + t • C x), x + t • C x⟫ = 2 * t * ‖C x‖ ^ 2 + t ^ 2 * b := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, conj_trivial, hx]
    rw [hCsym (C x) x, h3, hbdef]
    ring
  rw [e] at h1
  have hbabs : -b ≤ |b| := neg_le_abs b
  have : t * |b| < ‖C x‖ ^ 2 := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg b]
  nlinarith

private theorem spectral_gap [FiniteDimensional ℝ E] {C : E →L[ℝ] E}
    (hCsym : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫) (hCneg : ∀ x, ⟪C x, x⟫ ≤ 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ (LinearMap.ker (C : E →ₗ[ℝ] E))ᗮ, ⟪C x, x⟫ ≤ -μ * ‖x‖ ^ 2 := by
  set M := (LinearMap.ker (C : E →ₗ[ℝ] E))ᗮ with hM
  by_cases hne : ((M : Set E) ∩ Metric.sphere 0 1).Nonempty
  · have hcomp : IsCompact ((M : Set E) ∩ Metric.sphere 0 1) :=
      (isCompact_sphere 0 1).inter_left (Submodule.closed_of_finiteDimensional M)
    obtain ⟨x₀, hx₀, hmin⟩ := hcomp.exists_isMinOn hne
      (f := fun x => -⟪C x, x⟫)
      (by fun_prop)
    have hx0M : x₀ ∈ M := hx₀.1
    have hx0n : ‖x₀‖ = 1 := by simpa using hx₀.2
    have hpos : 0 < -⟪C x₀, x₀⟫ := by
      by_contra hle
      have h0 : ⟪C x₀, x₀⟫ = 0 := le_antisymm (hCneg _) (by linarith)
      have hC0 := eq_zero_of_inner_self_eq_zero_of_nonpos hCsym hCneg h0
      have hK : x₀ ∈ LinearMap.ker (C : E →ₗ[ℝ] E) := by simpa using hC0
      have : x₀ = 0 := by
        exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hK hx0M)
      rw [this] at hx0n; simp at hx0n
    refine ⟨-⟪C x₀, x₀⟫, hpos, fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hxs : (‖x‖⁻¹ • x) ∈ (M : Set E) ∩ Metric.sphere 0 1 := by
        refine ⟨M.smul_mem _ hx, ?_⟩
        simp [norm_smul, hn.ne']
      have this : -⟪C x₀, x₀⟫ ≤ -⟪C (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫ := hmin hxs
      have e : ⟪C (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫ = ‖x‖⁻¹ ^ 2 * ⟪C x, x⟫ := by
        rw [map_smul, inner_smul_left, inner_smul_right]; simp; ring
      rw [e] at this
      have h2 : ⟪C x, x⟫ * ‖x‖⁻¹ ^ 2 ≤ ⟪C x₀, x₀⟫ := by nlinarith
      have h3 : ⟪C x, x⟫ ≤ ⟪C x₀, x₀⟫ * ‖x‖ ^ 2 := by
        calc ⟪C x, x⟫ = (⟪C x, x⟫ * ‖x‖⁻¹ ^ 2) * ‖x‖ ^ 2 := by field_simp
          _ ≤ ⟪C x₀, x₀⟫ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      linarith
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · simp [hx0]
    · exfalso
      apply hne
      refine ⟨‖x‖⁻¹ • x, M.smul_mem _ hx, ?_⟩
      simp [norm_smul, norm_ne_zero_iff.mpr hx0]

/-- OP-ST-02 (source: arXiv 1907.04247 Assumption 1, 2005.06571, 2601.11900; core (i)–(ii)).
If the Galerkin projector `Pg` fixes a family `g` spanning the equilibria `ker C` (no linear
independence of `g` required), the implicit relaxation step `v = Pg (w + s C v)` converges as
`s → ∞` (`s = h/ε` or `h/ε²`) to the *true* equilibrium projection of `w`: augmentation makes
the nondegeneracy assumptions of the formal AP proofs unnecessary. -/
theorem relaxation_tendsto_of_capture [FiniteDimensional ℝ E] {C Pg : E →L[ℝ] E}
    (hPg : IsOrthProj Pg) (hCsym : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫) (hCneg : ∀ x, ⟪C x, x⟫ ≤ 0)
    {ι : Type*} (g : ι → E)
    (hspan : Submodule.span ℝ (Set.range g) = LinearMap.ker (C : E →ₗ[ℝ] E))
    (hcap : ∀ i, Pg (g i) = g i) (w : E) {v : ℝ → E}
    (hv : ∀ s, 0 ≤ s → v s = Pg (w + s • C (v s))) :
    Tendsto v atTop (𝓝 ((LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w)) := by
  set K := LinearMap.ker (C : E →ₗ[ℝ] E) with hKdef
  obtain ⟨μ, hμ, hgap⟩ := spectral_gap hCsym hCneg
  have hfix : ∀ k ∈ K, Pg k = k := by
    intro k hk
    rw [← hspan] at hk
    have : Submodule.span ℝ (Set.range g) ≤ LinearMap.ker ((Pg : E →ₗ[ℝ] E) - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp [hcap]
    have := this hk
    simpa [sub_eq_zero] using this
  have hCK : ∀ k ∈ K, C k = 0 := fun k hk => by simpa [hKdef] using hk
  set p := K.starProjection w with hp
  have hpK : p ∈ K := Submodule.starProjection_apply_mem K w
  have hwp : w - p ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal w
  set c := ‖w - p‖ with hc
  have key : ∀ s, 0 ≤ s → ‖v s - p‖ ≤ c / (1 + μ * s) := by
    intro s hs
    have hvs := hv s hs
    have hPv : Pg (v s) = v s := by
      conv_lhs => rw [hvs]
      rw [hPg.idem, ← hvs]
    have hperp : ∀ k ∈ K, ⟪v s, k⟫ = ⟪w, k⟫ := by
      intro k hk
      rw [hvs, hPg.symm, hfix k hk, inner_add_left, inner_smul_left, hCsym, hCK k hk]
      simp
    set u := v s - p with hu
    have huK : u ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal']
      intro k hk
      rw [hu, inner_sub_left, hperp k hk]
      have := Submodule.inner_right_of_mem_orthogonal hk hwp
      rw [inner_sub_right] at this
      linarith [real_inner_comm k w, real_inner_comm k p]
    have hpu : ⟪p, u⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hpK huK
    have hup : ⟪u, p⟫ = 0 := by rw [real_inner_comm]; exact hpu
    have hvsu : v s = p + u := by rw [hu]; abel
    have hE : ⟪v s, v s⟫ = ⟪w, v s⟫ + s * ⟪C (v s), v s⟫ := by
      have h := hPg.symm (w + s • C (v s)) (v s)
      rw [← hvs, hPv] at h
      rw [h, inner_add_left, inner_smul_left]
      simp
    have hpp : ⟪p, w - p⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hpK hwp
    have hvv : ⟪v s, v s⟫ = ⟪p, p⟫ + ⟪u, u⟫ := by
      rw [hvsu, inner_add_left, inner_add_right, inner_add_right, hpu, hup]; ring
    have hwv : ⟪w, v s⟫ = ⟪p, p⟫ + ⟪w - p, u⟫ := by
      have : w = p + (w - p) := by abel
      conv_lhs => rw [this, hvsu]
      have h5 : ⟪w - p, p⟫ = 0 := by rw [real_inner_comm]; exact hpp
      simp only [inner_add_left, inner_add_right]
      linarith
    have hCv : ⟪C (v s), v s⟫ = ⟪C u, u⟫ := by
      have hCp : C p = 0 := hCK p hpK
      rw [hvsu, map_add, hCp, zero_add, inner_add_right, hCsym u p, hCp]
      simp
    have hg := hgap u huK
    have hcs : ⟪w - p, u⟫ ≤ c * ‖u‖ := by
      calc ⟪w - p, u⟫ ≤ ‖w - p‖ * ‖u‖ := real_inner_le_norm _ _
        _ = c * ‖u‖ := by rw [hc]
    rw [real_inner_self_eq_norm_sq u] at hvv
    have hineq : (1 + μ * s) * ‖u‖ ^ 2 ≤ c * ‖u‖ := by
      have := hE
      rw [hvv, hwv, hCv] at this
      have h4 : s * ⟪C u, u⟫ ≤ s * (-μ * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hg hs
      rw [real_inner_self_eq_norm_sq] at this
      nlinarith
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
    · have h5 : 0 ≤ c / (1 + μ * s) := div_nonneg (norm_nonneg _) (by positivity)
      calc ‖u‖ = 0 := h0.symm
        _ ≤ _ := h5
    · rw [le_div_iff₀ (by positivity)]
      nlinarith
  have hlim : Tendsto (fun s : ℝ => c / (1 + μ * s)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hμ)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with s hs using key s hs

/-- OP-ST-02 (iv) (source: arXiv 1907.04247, negative part).  The nondegeneracy assumption
`H = ∫ ∇ρ ∇ρᵀ` nonsingular fails for data independent of one coordinate: if `D_j k = 0`, the Gram
matrix `H_{ab} = ⟪D_a k, D_b k⟫` of the discrete derivatives is singular. -/
theorem gram_det_eq_zero_of_deriv_eq_zero {d : ℕ} (D : Fin d → E →L[ℝ] E) (k : E) {j : Fin d}
    (hj : D j k = 0) : (Matrix.of fun a b => ⟪D a k, D b k⟫).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro b
  simp [hj]

open scoped Convolution in
open MeasureTheory Metric in
private theorem mollify [FiniteDimensional ℝ E] {f : E → E} {ℓ : ℝ}
    (hosl : ∀ x y, ⟪f x - f y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → E, ContDiff ℝ 1 g ∧ (∀ x y, ⟪g x - g y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2) ∧
      ∀ a, ∀ δ, (∀ x ∈ ball a ε, dist (f x) (f a) ≤ δ) → dist (g a) (f a) ≤ δ := by
  borelize E
  set μ : Measure E := Measure.addHaar with hμ
  have hloc : LocallyIntegrable f μ := hf.locallyIntegrable
  set φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩ with hφ
  have hcs : HasCompactSupport (φ.normed μ) := φ.hasCompactSupport_normed
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := E) with hL
  refine ⟨(φ.normed μ) ⋆[L, μ] f, hcs.contDiff_convolution_left L φ.contDiff_normed hloc, ?_,
    fun a δ => φ.dist_normed_convolution_le hloc.aestronglyMeasurable⟩
  have hex : ConvolutionExists (φ.normed μ) f L μ :=
    hcs.convolutionExists_left L φ.continuous_normed hloc
  intro x y
  have hux : Integrable (fun t => L (φ.normed μ t) (f (x - t))) μ := hex x
  have huy : Integrable (fun t => L (φ.normed μ t) (f (y - t))) μ := hex y
  have e1 : (φ.normed μ ⋆[L, μ] f) x - (φ.normed μ ⋆[L, μ] f) y =
      ∫ t, (L (φ.normed μ t) (f (x - t)) - L (φ.normed μ t) (f (y - t))) ∂μ := by
    rw [convolution_def, convolution_def, integral_sub hux huy]
  have hdiff : Integrable
      (fun t => L (φ.normed μ t) (f (x - t)) - L (φ.normed μ t) (f (y - t))) μ :=
    hux.sub huy
  rw [e1, real_inner_comm, ← integral_inner hdiff]
  have hint2 : Integrable (fun t => φ.normed μ t * (ℓ * ‖x - y‖ ^ 2)) μ :=
    φ.integrable_normed.mul_const _
  calc ∫ t, ⟪x - y, L (φ.normed μ t) (f (x - t)) - L (φ.normed μ t) (f (y - t))⟫ ∂μ
      ≤ ∫ t, φ.normed μ t * (ℓ * ‖x - y‖ ^ 2) ∂μ := by
        refine integral_mono (hdiff.const_inner (x - y)) hint2 (fun t => ?_)
        have h1 := hosl (x - t) (y - t)
        rw [sub_sub_sub_cancel_right] at h1
        have h2 : ⟪x - y, L (φ.normed μ t) (f (x - t)) - L (φ.normed μ t) (f (y - t))⟫ =
            φ.normed μ t * ⟪f (x - t) - f (y - t), x - y⟫ := by
          rw [hL, ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.lsmul_apply, ← smul_sub,
            real_inner_smul_right, real_inner_comm]
        rw [h2]
        exact mul_le_mul_of_nonneg_left h1 (φ.nonneg_normed t)
    _ = ℓ * ‖x - y‖ ^ 2 := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- OP-ST-03 (source: survey; remaining part of arXiv 2402.05347 / TT kinetic future work).
Existence of the implicit Galerkin stage for a merely *continuous* field with a one-sided bound
(finite-dimensional Browder–Minty): `x₁ = P (x₀ + h f(x₁))` has exactly one solution whenever
`h ℓ < 1`.  LeanDLRA has this for Lipschitz and locally Lipschitz `f`
(`existsUnique_implicitGalerkin_of_locallyLipschitz`). -/
theorem existsUnique_implicitGalerkin_of_continuous [FiniteDimensional ℝ E] {f : E → E}
    {ℓ h : ℝ} (hosl : ∀ x y, ⟪f x - f y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2) (hf : Continuous f)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) (hh : 0 ≤ h) (hhℓ : h * ℓ < 1) (x₀ : E) :
    ∃! x₁, x₁ = P (x₀ + h • f x₁) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hc : 0 < 1 - h * ℓ := by linarith
  -- existence
  have hex : ∃ x₁, x₁ = P (x₀ + h • f x₁) := by
    set R₀ := (‖x₀‖ + h * (‖f 0‖ + 1)) / (1 - h * ℓ) with hR₀
    set K : Set E := Metric.closedBall 0 R₀ with hK
    have hKc : IsCompact K := isCompact_closedBall 0 R₀
    set Φ : E → ℝ := fun x => ‖x - P (x₀ + h • f x)‖ with hΦ
    have hΦc : Continuous Φ := by
      simp only [hΦ]
      fun_prop
    have hK0 : (0 : E) ∈ K := by
      rw [hK, Metric.mem_closedBall, dist_self, hR₀]
      exact div_nonneg (by positivity) hc.le
    have happrox : ∀ δ : ℝ, 0 < δ → ∃ z ∈ K, Φ z ≤ h * δ := by
      intro δ hδ
      set δ' := min δ 1 with hδ'
      have hδ'0 : 0 < δ' := lt_min hδ one_pos
      have hunif : UniformContinuousOn f (Metric.closedBall 0 (R₀ + 1)) :=
        (isCompact_closedBall 0 (R₀ + 1)).uniformContinuousOn_of_continuous hf.continuousOn
      obtain ⟨ε₁, hε₁, hfε⟩ := Metric.uniformContinuousOn_iff.mp hunif δ' hδ'0
      obtain ⟨g, hgd, hgos, hgapp⟩ := mollify hosl hf (lt_min hε₁ one_pos)
      have happ : ∀ a ∈ K, dist (g a) (f a) ≤ δ' := by
        intro a ha
        refine hgapp a δ' (fun x hx => ?_)
        rw [Metric.mem_ball, lt_min_iff] at hx
        have hxa : dist x a < 1 := hx.2
        have hxK : x ∈ Metric.closedBall (0 : E) (R₀ + 1) := by
          rw [Metric.mem_closedBall] at ha ⊢
          have := dist_triangle x a 0
          linarith
        exact (hfε x hxK a (by rw [Metric.mem_closedBall] at ha ⊢; linarith) hx.1).le
      obtain ⟨z, hz⟩ := (existsUnique_implicitGalerkin_of_locallyLipschitz hgos
        hgd.locallyLipschitz hP hh hhℓ x₀).exists
      -- a priori bound
      have hstab := proj_implicit_step_stability hP hh hz (y₀ := -(h • g 0)) (y₁ := 0)
        (g := g 0) (by simp) (by simpa using hgos z 0)
      rw [sub_zero, sub_neg_eq_add] at hstab
      have h0 : ‖g 0‖ ≤ ‖f 0‖ + 1 := by
        have := happ 0 hK0
        rw [dist_eq_norm] at this
        have := norm_sub_norm_le (g 0) (f 0)
        have := (min_le_right δ 1)
        linarith
      have hzR : ‖z‖ ≤ R₀ := by
        rw [hR₀, le_div_iff₀ hc]
        have : ‖x₀ + h • g 0‖ ≤ ‖x₀‖ + h * (‖f 0‖ + 1) :=
          (norm_add_le _ _).trans (by
            rw [norm_smul, Real.norm_of_nonneg hh]
            linarith [mul_le_mul_of_nonneg_left h0 hh])
        nlinarith
      have hzK : z ∈ K := by simpa [hK] using hzR
      refine ⟨z, hzK, ?_⟩
      simp only [hΦ]
      have hz' : z - P (x₀ + h • f z) = P (h • (g z - f z)) := by
        calc z - P (x₀ + h • f z) = P (x₀ + h • g z) - P (x₀ + h • f z) := by rw [← hz]
          _ = P (h • (g z - f z)) := by
            rw [← map_sub, smul_sub]
            congr 1
            abel
      rw [hz']
      refine (hP.norm_le _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hh]
      have := happ z hzK
      rw [dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_left (this.trans (min_le_left _ _)) hh
    obtain ⟨x, hxK, hxmin⟩ := hKc.exists_isMinOn ⟨0, hK0⟩ hΦc.continuousOn
    refine ⟨x, ?_⟩
    have hle : ∀ δ : ℝ, 0 < δ → Φ x ≤ h * δ := by
      intro δ hδ
      obtain ⟨z, hz, hzΦ⟩ := happrox δ hδ
      exact (hxmin hz).trans hzΦ
    have hΦx : Φ x = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra hcon
      replace hcon := not_le.mp hcon
      have := hle (Φ x / (2 * (h + 1))) (by positivity)
      have h2 : h * (Φ x / (2 * (h + 1))) < Φ x := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    simpa [hΦ, sub_eq_zero] using hΦx
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, hx, fun y hy => ?_⟩
  have h1 := proj_implicit_step_stability hP hh hy hx (hosl y x)
  rw [sub_self, norm_zero] at h1
  have h2 : ‖y - x‖ ≤ 0 := by nlinarith [norm_nonneg (y - x)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

/-- OP-ST-04 (source: arXiv 2402.05347; a-priori version).  Merged step-truncation/BUG implicit
Galerkin steps `Xₙ = Pₙ (Yₙ + h F(t_{n+1}, Xₙ))` followed by truncation (`‖Y_{n+1} - Xₙ‖ ≤ θ`),
with dissipative `F` (`ℓ ≤ 0`).  If the merged spaces capture the full backward-Euler solution
`Xsₙ` in the graph norm (`‖F(Pₙ Xsₙ) - F(Xsₙ)‖ ≤ η`, `‖(1 - Pₙ) F(Xsₙ)‖ ≤ η`), the global
error is `δ + n (2 h η + θ + M h²)`: no Lipschitz constant, no restriction `h ≤ 1/(2L)`. -/
theorem mergedImplicit_apriori_bconv {F : ℝ → E → E} {ℓ : ℝ}
    (hos : IsOneSidedLipschitzField F ℓ) (hℓ : ℓ ≤ 0) {t₀ h M η θ : ℝ} (hh : 0 ≤ h)
    (hM : 0 ≤ M) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    (hAM : ∀ n < N, ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (A t) - F (t₀ + (n + 1) * h) (A (t₀ + (n + 1) * h))‖ ≤
        M * (t₀ + (n + 1) * h - t))
    {Pg : ℕ → E →L[ℝ] E} (hPg : ∀ n, IsOrthProj (Pg n)) {Y X Xs : ℕ → E}
    (hfix : ∀ n < N, Pg n (Y n) = Y n)
    (hX : ∀ n < N, X n = Pg n (Y n + h • F (t₀ + (n + 1) * h) (X n)))
    (hXs : ∀ n < N, Xs n = Y n + h • F (t₀ + (n + 1) * h) (Xs n))
    (hgraph : ∀ n < N,
      ‖F (t₀ + (n + 1) * h) (Pg n (Xs n)) - F (t₀ + (n + 1) * h) (Xs n)‖ ≤ η)
    (hnormal : ∀ n < N, ‖(1 - Pg n) (F (t₀ + (n + 1) * h) (Xs n))‖ ≤ η)
    (htr : ∀ n < N, ‖Y (n + 1) - X n‖ ≤ θ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ ‖Y 0 - A t₀‖ + n * (2 * h * η + θ + M * h ^ 2) := by
  have step : ∀ n < N, ‖Y (n + 1) - A (t₀ + ((n + 1 : ℕ) : ℝ) * h)‖ ≤
      ‖Y n - A (t₀ + n * h)‖ + (2 * h * η + θ + M * h ^ 2) := by
    intro n hn
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
    have hNh : ((n : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hn' hh
    have hAn : ODESolution F A (t₀ + n * h) (t₀ + (n + 1) * h) :=
      hA.mono (by linarith) (by linarith)
    have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
    rw [hcast]
    obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₁ = t₀ + ((n : ℝ) + 1) * h := ⟨_, rfl⟩
    have hP := hPg n
    have hxs := hXs n hn
    have hx := hX n hn
    have hfx := hfix n hn
    have hgr := hgraph n hn
    have hno := hnormal n hn
    have hAM' := hAM n hn
    have htr' := htr n hn
    rw [← ht₁] at hxs hx hgr hno hAM' ⊢
    rw [← ht₁] at hAn
    have hη : 0 ≤ η := (norm_nonneg _).trans hno
    -- the full backward Euler step is B-stable
    have hres := residual_step_error hos (t₀ := t₀ + n * h) (t₁ := t₁) (by rw [ht₁]; ring) hh hAn
      hM (fun t ht => hAM' t ht) (Y n) (Xs n)
    have hres0 : Xs n - Y n - h • F t₁ (Xs n) = 0 := by
      rw [sub_eq_iff_eq_add'.mpr hxs, sub_self]
    rw [hres0, norm_zero] at hres
    have hxsA : ‖Xs n - A t₁‖ ≤ ‖Y n - A (t₀ + n * h)‖ + M * h ^ 2 := by
      nlinarith [norm_nonneg (Xs n - A t₁), mul_nonneg hh (neg_nonneg.mpr hℓ),
        mul_nonneg (mul_nonneg hh (neg_nonneg.mpr hℓ)) (norm_nonneg (Xs n - A t₁))]
    have hcea := implicitGalerkin_cea hP hh hfx hx hxs (hos t₁ (X n) (Xs n))
    have hPX : Pg n (X n) = X n := by rw [hx, hP.idem]
    have hPZ : Pg n (Pg n (Xs n)) = Pg n (Xs n) := hP.idem _
    have hXeq : X n = Y n + h • Pg n (F t₁ (X n)) := by
      conv_lhs => rw [hx]
      rw [map_add, map_smul, hfx]
    have hZeq : Pg n (Xs n) = Y n + h • Pg n (F t₁ (Xs n)) := by
      conv_lhs => rw [hxs]
      rw [map_add, map_smul, hfx]
    have hee : X n - Pg n (Xs n) = h • Pg n (F t₁ (X n) - F t₁ (Xs n)) := by
      calc X n - Pg n (Xs n) = (Y n + h • Pg n (F t₁ (X n))) - (Y n + h • Pg n (F t₁ (Xs n))) := by
            rw [← hXeq, ← hZeq]
        _ = _ := by rw [map_sub, smul_sub]; abel
    have hPe : Pg n (X n - Pg n (Xs n)) = X n - Pg n (Xs n) := by
      rw [map_sub, hPX, hPZ]
    set e := X n - Pg n (Xs n) with he
    have h1 : ‖e‖ ^ 2 = h * ⟪F t₁ (X n) - F t₁ (Xs n), e⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      calc ⟪e, e⟫ = ⟪h • Pg n (F t₁ (X n) - F t₁ (Xs n)), e⟫ := by rw [← hee]
        _ = h * ⟪Pg n (F t₁ (X n) - F t₁ (Xs n)), e⟫ := real_inner_smul_left _ _ _
        _ = h * ⟪F t₁ (X n) - F t₁ (Xs n), Pg n e⟫ := by rw [hP.symm]
        _ = _ := by rw [hPe]
    have h2 : ⟪F t₁ (X n) - F t₁ (Xs n), e⟫ ≤ η * ‖e‖ := by
      have hd : F t₁ (X n) - F t₁ (Xs n) =
          (F t₁ (X n) - F t₁ (Pg n (Xs n))) + (F t₁ (Pg n (Xs n)) - F t₁ (Xs n)) := by abel
      rw [hd, inner_add_left]
      have a1 := hos t₁ (X n) (Pg n (Xs n))
      have a2 : ⟪F t₁ (Pg n (Xs n)) - F t₁ (Xs n), e⟫ ≤ η * ‖e‖ :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hgr (norm_nonneg _))
      have a3 : ℓ * ‖e‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hℓ (sq_nonneg _)
      linarith
    have hZ : ‖e‖ ≤ h * η := by
      by_contra hcon
      replace hcon := not_le.mp hcon
      have hpos : 0 < ‖e‖ := lt_of_le_of_lt (mul_nonneg hh hη) hcon
      nlinarith [mul_le_mul_of_nonneg_left h2 hh]
    have hsq : ‖X n - Xs n‖ ^ 2 ≤ (2 * h * η) ^ 2 := by
      rw [hcea.1]
      have hb : h ^ 2 * ‖(1 - Pg n) (F t₁ (Xs n))‖ ^ 2 ≤ h ^ 2 * η ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hno 2) (sq_nonneg _)
      have ha : ‖e‖ ^ 2 ≤ (h * η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hZ 2
      nlinarith [sq_nonneg (h * η)]
    have hXX : ‖X n - Xs n‖ ≤ 2 * h * η := by
      by_contra hcon
      replace hcon := not_le.mp hcon
      nlinarith [mul_nonneg hh hη]
    have htri : ‖Y (n + 1) - A t₁‖ ≤ ‖Y (n + 1) - X n‖ + ‖X n - Xs n‖ + ‖Xs n - A t₁‖ := by
      have : Y (n + 1) - A t₁ = (Y (n + 1) - X n) + (X n - Xs n) + (Xs n - A t₁) := by abel
      rw [this]; exact norm_add₃_le
    linarith
  intro n hn
  induction n with
  | zero => simp
  | succ k ih =>
    have := step k (by omega)
    have := ih (by omega)
    push_cast at *
    linarith

/-- OP-ST-05, Lie part (source: arXiv 1803.10473, 1705.10175, 2602.07437; corrected
hypotheses).  `Y_{n+1} = S (Ψ_τ Yₙ)` where `S = e^{τ 𝒜}` is a contraction (`ω ≤ 0`) and `Ψ_τ`
is one BUG step for the non-stiff part `G` (`IsBUGStep`, normal-component hypothesis at the
substep points).  Given the exact Lie splitting error `ks τ²` at the exact solution, the global
error is first order with constants depending on `G` only (mesh- and singular-value-free). -/
theorem lieSplitting_bug_global {G : ℝ → E → E} {L B ε τ t₀ ks : ℝ}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B) (hτ : 0 ≤ τ)
    (hks : 0 ≤ ks) {S : E →L[ℝ] E} (hS : ∀ x, ‖S x‖ ≤ ‖x‖) {N : ℕ} {A : ℝ → E} {Y : ℕ → E}
    {P₀ Q₀ P₁ Q₁ : ℕ → E →L[ℝ] E} {YK YL YS Φ Ψ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsBUGStep G ε (P₀ n) (Q₀ n) (P₁ n) (Q₁ n) (t₀ + n * τ)
      (t₀ + (n + 1) * τ) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = S (YS n (t₀ + (n + 1) * τ)))
    (hΦ : ∀ n < N, ODESolution G (Φ n) (t₀ + n * τ) (t₀ + (n + 1) * τ))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * τ) = A (t₀ + n * τ))
    (hΨ : ∀ n < N, ODESolution G (Ψ n) (t₀ + n * τ) (t₀ + (n + 1) * τ))
    (hΨ₀ : ∀ n < N, Ψ n (t₀ + n * τ) = Y n)
    (hsplit : ∀ n < N, ‖S (Φ n (t₀ + (n + 1) * τ)) - A (t₀ + (n + 1) * τ)‖ ≤ ks * τ ^ 2) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * τ)‖ ≤ Real.exp (L * (n * τ)) * (‖Y 0 - A t₀‖ +
      n * (ks * τ ^ 2 + ((Real.exp (L * τ) - 1) * (B * τ + 2 * (τ * (4 * L * B * τ + ε))) +
        2 * (τ * (4 * L * B * τ + ε))))) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro n hn
    have : n = 0 := by omega
    subst this
    simp
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hε : 0 ≤ ε := (hstep 0 hN).eps_nonneg (by nlinarith)
  have hc : 0 ≤ ((Real.exp (L * τ) - 1) * (B * τ + 2 * (τ * (4 * L * B * τ + ε))) +
        2 * (τ * (4 * L * B * τ + ε))) := by
    have h1 : 0 ≤ Real.exp (L * τ) - 1 := by
      have := Real.one_le_exp (mul_nonneg hL hτ); linarith
    positivity
  have hrec : ∀ n < N, ‖Y (n + 1) - A (t₀ + ((n + 1 : ℕ) : ℝ) * τ)‖ ≤
      Real.exp (L * τ) * ‖Y n - A (t₀ + n * τ)‖ + (ks * τ ^ 2 + ((Real.exp (L * τ) - 1) *
        (B * τ + 2 * (τ * (4 * L * B * τ + ε))) + 2 * (τ * (4 * L * B * τ + ε)))) := by
    intro n hn
    have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
    rw [hcast]
    have hloc := (hstep n hn).local_error hG hL hB (h := τ) (by ring) hτ (hΨ n hn) (hΨ₀ n hn)
    have hstab := (hΨ n hn).norm_sub_le_exp hG hL (hΦ n hn) (t₀ + (n + 1) * τ)
      ⟨by nlinarith, le_rfl⟩
    rw [hΨ₀ n hn, hΦ₀ n hn, show t₀ + (n + 1) * τ - (t₀ + n * τ) = τ by ring] at hstab
    have h1 : ‖Y (n + 1) - S (Φ n (t₀ + (n + 1) * τ))‖ ≤
        ‖YS n (t₀ + (n + 1) * τ) - Φ n (t₀ + (n + 1) * τ)‖ := by
      rw [hY n hn, ← map_sub]
      exact hS _
    have h2 : ‖YS n (t₀ + (n + 1) * τ) - Φ n (t₀ + (n + 1) * τ)‖ ≤
        ‖YS n (t₀ + (n + 1) * τ) - Ψ n (t₀ + (n + 1) * τ)‖ +
          ‖Ψ n (t₀ + (n + 1) * τ) - Φ n (t₀ + (n + 1) * τ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h3 : ‖Y (n + 1) - A (t₀ + (n + 1) * τ)‖ ≤
        ‖Y (n + 1) - S (Φ n (t₀ + (n + 1) * τ))‖ +
          ‖S (Φ n (t₀ + (n + 1) * τ)) - A (t₀ + (n + 1) * τ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h4 := hsplit n hn
    linarith
  intro n hn
  have key := discrete_gronwall_exp_le (e := fun n => ‖Y n - A (t₀ + n * τ)‖) hL hτ
    (add_nonneg (mul_nonneg hks (sq_nonneg τ)) hc) hrec n hn
  simpa using key

private theorem pow_succ_apply (S : E →L[ℝ] E) (j : ℕ) (x : E) :
    (S ^ (j + 1)) x = S ((S ^ j) x) := by
  rw [pow_succ']; rfl

private theorem pow_contract {S : E →L[ℝ] E} (hS : ∀ x, ‖S x‖ ≤ ‖x‖) (j : ℕ) (x : E) :
    ‖(S ^ j) x‖ ≤ ‖x‖ := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ_apply]
    exact (hS _).trans (ih x)

private theorem gronwall_monotone {m a : ℕ → ℝ} {c : ℝ} {N : ℕ} (hc : 0 ≤ c)
    (ha : ∀ k n, k ≤ n → n ≤ N → a k ≤ a n)
    (h : ∀ n ≤ N, m n ≤ a n + c * ∑ k ∈ range n, m k) :
    ∀ n ≤ N, m n ≤ a n * (1 + c) ^ n := by
  have geom : ∀ n : ℕ, 1 + c * ∑ k ∈ range n, (1 + c) ^ k = (1 + c) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, mul_add, ← add_assoc, ih]; ring
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have h1 : ∑ k ∈ range n, m k ≤ ∑ k ∈ range n, a n * (1 + c) ^ k := by
      apply sum_le_sum
      intro k hk
      have hk' : k < n := mem_range.mp hk
      calc m k ≤ a k * (1 + c) ^ k := ih k hk' (by omega)
        _ ≤ a n * (1 + c) ^ k :=
          mul_le_mul_of_nonneg_right (ha k n hk'.le hn) (by positivity)
    calc m n ≤ a n + c * ∑ k ∈ range n, m k := h n hn
      _ ≤ a n + c * ∑ k ∈ range n, a n * (1 + c) ^ k := by gcongr
      _ = a n * (1 + c * ∑ k ∈ range n, (1 + c) ^ k) := by rw [← mul_sum]; ring
      _ = a n * (1 + c) ^ n := by rw [geom]

private theorem harmonic_aux (Cs : ℝ) (hCs : 0 ≤ Cs) (n : ℕ) :
    ∑ j ∈ range n, (if j = 0 then (1 : ℝ) else Cs / j) ≤ 1 + Cs * (1 + Real.log n) := by
  rcases n with _ | m
  · simp only [range_zero, sum_empty, Nat.cast_zero, Real.log_zero, add_zero, mul_one]
    linarith
  · rw [sum_range_succ']
    have e1 : ∑ j ∈ range m, (if j + 1 = 0 then (1 : ℝ) else Cs / ((j + 1 : ℕ) : ℝ)) =
        ∑ j ∈ range m, Cs / ((j + 1 : ℕ) : ℝ) :=
      sum_congr rfl (fun j _ => by simp)
    have hh : ∑ j ∈ range m, Cs / ((j + 1 : ℕ) : ℝ) = Cs * (harmonic m : ℝ) := by
      simp [harmonic, Rat.cast_sum, div_eq_mul_inv, Finset.mul_sum]
    rw [e1, hh]
    simp only [↓reduceIte]
    have h1 : (harmonic m : ℝ) ≤ 1 + Real.log m := harmonic_le_one_add_log m
    have h2 : Real.log m ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp
      · exact Real.log_le_log (by exact_mod_cast h0) (by push_cast; linarith)
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans (add_le_add_right h2 1)) hCs]

/-- OP-ST-05, Strang part (source: arXiv 2602.07437; core of the `τ² |log τ|` bound).  Error
recursion `e_{n+1} = S eₙ + gₙ + dₙ` with a contraction `S = e^{τ 𝒜}`, parabolic smoothing
`‖Sʲ (τ𝒜) x‖ ≤ C_s/j ‖x‖`, a Lipschitz propagation term `‖gₙ‖ ≤ L τ ‖eₙ‖` (the fix of the gap
in 2602.07437) and Strang defects in Peano form `dₙ = (τ𝒜) ρₙ`, `‖ρₙ‖, ‖dₙ‖ ≤ K τ²`.  Then
`‖eₙ‖ ≤ e^{L n τ} (‖e₀‖ + K τ² (1 + C_s (1 + log n)))`: order two up to a logarithm. -/
theorem strang_smoothing_global {S Aτ : E →L[ℝ] E} (hS : ∀ x, ‖S x‖ ≤ ‖x‖) {Cs : ℝ}
    (hCs : 0 ≤ Cs) (hsm : ∀ j : ℕ, 1 ≤ j → ∀ x, ‖(S ^ j) (Aτ x)‖ ≤ Cs / j * ‖x‖)
    {L K τ : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hτ : 0 ≤ τ) {N : ℕ} {e g d ρ : ℕ → E}
    (hrec : ∀ n < N, e (n + 1) = S (e n) + g n + d n)
    (hg : ∀ n < N, ‖g n‖ ≤ L * τ * ‖e n‖) (hd : ∀ n < N, d n = Aτ (ρ n))
    (hρ : ∀ n < N, ‖ρ n‖ ≤ K * τ ^ 2) (hdn : ∀ n < N, ‖d n‖ ≤ K * τ ^ 2) :
    ∀ n ≤ N, ‖e n‖ ≤
      Real.exp (L * (n * τ)) * (‖e 0‖ + K * τ ^ 2 * (1 + Cs * (1 + Real.log n))) := by
  have formula : ∀ n ≤ N, e n = (S ^ n) (e 0) +
      ∑ j ∈ range n, (S ^ j) (g (n - 1 - j) + d (n - 1 - j)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      rw [hrec n (by omega), h1, sum_range_succ' _ n]
      have : ∀ j ∈ range n, (S ^ (j + 1)) (g (n + 1 - 1 - (j + 1)) + d (n + 1 - 1 - (j + 1))) =
          S ((S ^ j) (g (n - 1 - j) + d (n - 1 - j))) := by
        intro j _
        rw [pow_succ_apply, show n + 1 - 1 - (j + 1) = n - 1 - j by omega]
      rw [sum_congr rfl this, map_add, map_sum, pow_succ_apply]
      have p0 : ∀ x : E, (S ^ 0) x = x := fun x => by simp
      simp only [Nat.add_sub_cancel, Nat.sub_zero, p0]
      abel
  have dbound : ∀ n ≤ N, ‖∑ j ∈ range n, (S ^ j) (d (n - 1 - j))‖ ≤
      K * τ ^ 2 * (1 + Cs * (1 + Real.log n)) := by
    intro n hn
    calc ‖∑ j ∈ range n, (S ^ j) (d (n - 1 - j))‖
        ≤ ∑ j ∈ range n, ‖(S ^ j) (d (n - 1 - j))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range n, K * τ ^ 2 * (if j = 0 then (1 : ℝ) else Cs / j) := by
          apply sum_le_sum
          intro j hj
          have hj' : n - 1 - j < N := by have := mem_range.mp hj; omega
          by_cases h0 : j = 0
          · subst h0
            simpa using hdn _ hj'
          · simp only [h0, ↓reduceIte]
            rw [hd _ hj']
            calc ‖(S ^ j) (Aτ (ρ (n - 1 - j)))‖ ≤ Cs / j * ‖ρ (n - 1 - j)‖ :=
                  hsm j (Nat.one_le_iff_ne_zero.mpr h0) _
              _ ≤ Cs / j * (K * τ ^ 2) :=
                  mul_le_mul_of_nonneg_left (hρ _ hj') (by positivity)
              _ = _ := by ring
      _ = K * τ ^ 2 * ∑ j ∈ range n, (if j = 0 then (1 : ℝ) else Cs / j) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_aux Cs hCs n) (by positivity)
  set c := L * τ with hc
  have hc0 : 0 ≤ c := mul_nonneg hL hτ
  set a : ℕ → ℝ := fun n => ‖e 0‖ + K * τ ^ 2 * (1 + Cs * (1 + Real.log n)) with ha
  have hmono : ∀ k n : ℕ, k ≤ n → n ≤ N → a k ≤ a n := by
    intro k n hkn _
    simp only [ha]
    have : Real.log k ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simpa using Real.log_natCast_nonneg n
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hkn)
    have := mul_le_mul_of_nonneg_left this hCs
    have := mul_le_mul_of_nonneg_left (add_le_add_right this 1) (by positivity : 0 ≤ K * τ ^ 2)
    nlinarith
  have hine : ∀ n ≤ N, ‖e n‖ ≤ a n + c * ∑ k ∈ range n, ‖e k‖ := by
    intro n hn
    have hgs : ‖∑ j ∈ range n, (S ^ j) (g (n - 1 - j))‖ ≤ c * ∑ k ∈ range n, ‖e k‖ := by
      calc ‖∑ j ∈ range n, (S ^ j) (g (n - 1 - j))‖
          ≤ ∑ j ∈ range n, ‖(S ^ j) (g (n - 1 - j))‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ range n, c * ‖e (n - 1 - j)‖ := by
            apply sum_le_sum
            intro j hj
            have hj' : n - 1 - j < N := by have := mem_range.mp hj; omega
            exact (pow_contract hS j _).trans (hg _ hj')
        _ = c * ∑ k ∈ range n, ‖e k‖ := by
            rw [← mul_sum, sum_range_reflect (fun k => ‖e k‖) n]
    have hd' := dbound n hn
    have h0 : ‖(S ^ n) (e 0)‖ ≤ ‖e 0‖ := pow_contract hS n _
    rw [formula n hn]
    simp only [map_add, sum_add_distrib]
    calc ‖(S ^ n) (e 0) + (∑ j ∈ range n, (S ^ j) (g (n - 1 - j)) +
          ∑ j ∈ range n, (S ^ j) (d (n - 1 - j)))‖
        ≤ ‖(S ^ n) (e 0)‖ + (‖∑ j ∈ range n, (S ^ j) (g (n - 1 - j))‖ +
          ‖∑ j ∈ range n, (S ^ j) (d (n - 1 - j))‖) :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ _ := by simp only [ha]; linarith
  have key := gronwall_monotone hc0 hmono hine
  intro n hn
  have hexp : (1 + c) ^ n ≤ Real.exp (L * (n * τ)) := by
    calc (1 + c) ^ n ≤ (Real.exp c) ^ n := by
          gcongr
          linarith [Real.add_one_le_exp c]
      _ = Real.exp (L * (n * τ)) := by rw [← Real.exp_nat_mul, hc]; ring_nf
  have ha0 : 0 ≤ a n := by
    simp only [ha]
    have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    positivity
  calc ‖e n‖ ≤ a n * (1 + c) ^ n := key n hn
    _ ≤ a n * Real.exp (L * (n * τ)) := mul_le_mul_of_nonneg_left hexp ha0
    _ = _ := by simp only [ha]; ring

attribute [-instance] ContinuousLinearMap.instNPowId in
/-- The statement of `strang_smoothing_global` as recorded on v4.36.0-rc2, where `S ^ j`
elaborated with `Monoid.toNPow`; Mathlib v4.36.0 elaborates `ContinuousLinearMap.instNPowId`.
Both forms are the same proposition: this one follows from the theorem by `exact`. -/
example {S Aτ : E →L[ℝ] E} (hS : ∀ x, ‖S x‖ ≤ ‖x‖) {Cs : ℝ}
    (hCs : 0 ≤ Cs) (hsm : ∀ j : ℕ, 1 ≤ j → ∀ x, ‖(S ^ j) (Aτ x)‖ ≤ Cs / j * ‖x‖)
    {L K τ : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hτ : 0 ≤ τ) {N : ℕ} {e g d ρ : ℕ → E}
    (hrec : ∀ n < N, e (n + 1) = S (e n) + g n + d n)
    (hg : ∀ n < N, ‖g n‖ ≤ L * τ * ‖e n‖) (hd : ∀ n < N, d n = Aτ (ρ n))
    (hρ : ∀ n < N, ‖ρ n‖ ≤ K * τ ^ 2) (hdn : ∀ n < N, ‖d n‖ ≤ K * τ ^ 2) :
    ∀ n ≤ N, ‖e n‖ ≤
      Real.exp (L * (n * τ)) * (‖e 0‖ + K * τ ^ 2 * (1 + Cs * (1 + Real.log n))) := by
  exact strang_smoothing_global hS hCs hsm hL hK hτ hrec hg hd hρ hdn

end LeanDLRA.OpenProblems.Stiff
