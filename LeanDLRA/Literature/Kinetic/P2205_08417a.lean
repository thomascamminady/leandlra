import LeanDLRA.Stability.Conservation
import LeanDLRA.Literature.Kinetic.P2510_05452a

/-!
# The CSD pseudo-time transformation and the `P_N` closure of KiT-RT (arXiv 2205.08417)

J. Kusch, S. Schotthöfer, P. Stammer, J. Wolters, T. Xiao, *KiT-RT: An extendable framework for
radiative transfer and therapy*, arXiv 2205.08417 (v1).  This is a software paper; it states no
theorems.  Its mathematical statements with a derivation are the transformation (6)-(9) of the
continuous slowing down (CSD) equation (3) into a transport equation in the pseudo-time `Ẽ`, and,
in Sec. 3.1, that the quadratic entropy `η(g) = g²` "recovers the `P_N` method" together with the
`P_N` moment flux `A_i = ∫ m mᵀ Ω_i dΩ`.  These are formalized here.

## Main results

* (6): `transformedEnergy`, `hasDerivAt_transformedEnergy` (`dẼ/dE = -1/S(E)`),
  `transformedEnergy_strictAntiOn` (so the inverse `E(Ẽ)` of (7) exists) and
  `transformedEnergy_self` (`E_max` is pseudo-time `0`, the initial time of (9)).
* (8): `isCSDAt_of_isTransformedAt` ((8) at `Ẽ(E)` implies (3) at `E`) and
  `isCSDAt_iff_isTransformedAt` (equivalence when `ψ̃` is differentiable in pseudo-time), with the
  helper `stream_scatter_transformed`.  (9) is (8) with the tilde dropped.
* Sec. 3.1: `quadratic_entropy_closure` (the `P_N` reconstruction `uᵀ m` is the unique minimiser of
  `∫ g²` under the moment constraints), `isOrthProj_pnProj` (the `P_N` closure map is the
  orthogonal projector onto the span of the basis, a core `IsOrthProj`, built from the core
  `rankOneProj`), `moments_pnRecon`, `pnRecon_minimizes_on`, and the flux identity
  `moments_map_pnRecon`.

## Setting and differences from the paper

* Positions and directions lie in a real inner product space `V` (the paper: `ℝ³` and `𝕊²`), the
  angular integral is over any measure `μ`, and the streaming term `Ω·∇ₓ` is `stream` of
  `LeanDLRA.Literature.P2510_05452` (the derivative of `ψ(E, ·, Ω)` at `x` in direction `Ω`).
  (3) and (8) are stated pointwise (`IsCSDAt`, `IsTransformedAt`) with the coefficients of (5);
  the stopping power is continuous and positive on `[0, E_max]` and `ρ` does not vanish.
* (7) defines `ψ̃` through the inverse `E(Ẽ)`; here `ψ̃` is any function with
  `ψ̃(Ẽ(E), x, Ω) = S(E) ρ(x) ψ(E, x, Ω)` for `E ∈ (0, E_max)`, which is the same thing.  The
  direction (3) ⇒ (8) assumes that `ψ̃` is differentiable in pseudo-time at `Ẽ(E)`; deriving this
  from the differentiability of `ψ` needs the inverse function theorem and is not done.
* For the closure, `H` is any real inner product space (`L²(𝕊²)`, where `∫ η(g) = ‖g‖²`) and
  `m` any orthonormal family (the paper: real spherical harmonics, which are orthonormal).  The
  set `F_m` of (14) also requires `g > 0`.  The remark holds without that constraint
  (`quadratic_entropy_closure`), and with it whenever the `P_N` reconstruction of the moments is
  positive (`pnRecon_minimizes_on`); the paper itself notes that `P_N` does not preserve
  positivity.
* Not formalised: the moment equations (10)-(11), which need the recursion and Funk-Hecke
  properties of the spherical harmonics; the properties of the `M_N` closure and of the
  regularised closure (18)-(19), which the paper cites from [4, 45] without proof; the `S_N`
  quadratures, finite volume, IMEX and Heun schemes and the limiters (20)-(49), which are
  definitions of the implemented methods; Secs. 5-7 (software, scaling, validation), which are
  empirical.

No claim of the paper was found to be false.
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2205_08417

open LeanDLRA LeanDLRA.Literature.P2510_05452

/-! ### The transformed energy, Eq. (6) -/

/-- The transformed energy of Eq. (6),
`Ẽ(E) = ∫₀^{E_max} 1/S(E') dE' - ∫₀^E 1/S(E') dE'`, for the stopping power `S` of water. -/
noncomputable def transformedEnergy (S : ℝ → ℝ) (Emax E : ℝ) : ℝ :=
  (∫ e in (0 : ℝ)..Emax, 1 / S e) - ∫ e in (0 : ℝ)..E, 1 / S e

/-- The maximal energy is pseudo-time zero, the initial time of (9). -/
theorem transformedEnergy_self (S : ℝ → ℝ) (Emax : ℝ) : transformedEnergy S Emax Emax = 0 :=
  sub_self _

/-- `dẼ/dE = -1/S(E)` (fundamental theorem of calculus for (6)), for a continuous positive
stopping power. -/
theorem hasDerivAt_transformedEnergy {S : ℝ → ℝ} {Emax E : ℝ}
    (hc : ContinuousOn S (Icc 0 Emax)) (hpos : ∀ e ∈ Icc 0 Emax, 0 < S e) (hE : E ∈ Ioo 0 Emax) :
    HasDerivAt (transformedEnergy S Emax) (-(1 / S E)) E := by
  have hf : ContinuousOn (fun e => 1 / S e) (Icc 0 Emax) :=
    continuousOn_const.div hc fun e he => (hpos e he).ne'
  have hint : IntervalIntegrable (fun e => 1 / S e) volume 0 E :=
    (hf.mono (Icc_subset_Icc le_rfl hE.2.le)).intervalIntegrable_of_Icc hE.1.le
  have hmeas : StronglyMeasurableAtFilter (fun e => 1 / S e) (𝓝 E) :=
    (hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo E hE
  have hcont : ContinuousAt (fun e => 1 / S e) E := hf.continuousAt (Icc_mem_nhds hE.1 hE.2)
  exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_sub _

/-- For a positive stopping power the transformed energy is strictly decreasing on `[0, E_max]`,
so the inverse `E(Ẽ)` used in (7) exists: high energies are early pseudo-times. -/
theorem transformedEnergy_strictAntiOn {S : ℝ → ℝ} {Emax : ℝ}
    (hc : ContinuousOn S (Icc 0 Emax)) (hpos : ∀ e ∈ Icc 0 Emax, 0 < S e) :
    StrictAntiOn (transformedEnergy S Emax) (Icc 0 Emax) := by
  have hf : ContinuousOn (fun e => 1 / S e) (Icc 0 Emax) :=
    continuousOn_const.div hc fun e he => (hpos e he).ne'
  intro a ha b hb hab
  have hia : IntervalIntegrable (fun e => 1 / S e) volume 0 a :=
    (hf.mono (Icc_subset_Icc le_rfl ha.2)).intervalIntegrable_of_Icc ha.1
  have hiab : IntervalIntegrable (fun e => 1 / S e) volume a b :=
    (hf.mono (Icc_subset_Icc ha.1 hb.2)).intervalIntegrable_of_Icc hab.le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hia hiab
  have hposab : 0 < ∫ e in a..b, 1 / S e :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hiab
      (fun e he => one_div_pos.2 (hpos e ⟨ha.1.trans he.1.le, he.2.le.trans hb.2⟩)) hab
  simp only [transformedEnergy]
  linarith

/-! ### The CSD equation in pseudo-time, Eqs. (3), (5), (7), (8) -/

section CSD

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

/-- The continuous slowing down equation (3) with the water-equivalent coefficients (5), at
energy `E`, position `x` and direction `Ω`:
`-∂_E(S(E) ρ(x) ψ) + Ω·∇ₓψ + Σₜ(E) ρ(x) ψ = ∫ Σₛ(E, Ω·Ω') ρ(x) ψ(E, x, Ω') dΩ'`.
`D` is the energy derivative; the streaming term is `stream` of
`LeanDLRA.Literature.P2510_05452` (the derivative of `ψ(E, ·, Ω)` at `x` in direction `Ω`). -/
def IsCSDAt (μ : Measure V) (S sigT : ℝ → ℝ) (sigS : ℝ → ℝ → ℝ) (ρ : V → ℝ)
    (ψ : ℝ → V → V → ℝ) (E : ℝ) (x Ω : V) : Prop :=
  ∃ D, HasDerivAt (fun e => S e * ρ x * ψ e x Ω) D E ∧
    -D + stream (ψ E) x Ω + sigT E * ρ x * ψ E x Ω = ∫ Ω', sigS E ⟪Ω, Ω'⟫ * ρ x * ψ E x Ω' ∂μ

/-- Eq. (8) at pseudo-time `Ẽ`, with coefficients `Σ̃ₜ(Ẽ) = σt` and `Σ̃ₛ(Ẽ, ·) = σs`:
`∂_Ẽ ψ̃ + Ω·∇ₓ(ψ̃/ρ) + Σ̃ₜ ψ̃ = ∫ Σ̃ₛ(Ω·Ω') ψ̃(Ẽ, x, Ω') dΩ'`. -/
def IsTransformedAt (μ : Measure V) (σt : ℝ) (σs : ℝ → ℝ) (ρ : V → ℝ) (ψt : ℝ → V → V → ℝ)
    (e : ℝ) (x Ω : V) : Prop :=
  ∃ D, HasDerivAt (fun e' => ψt e' x Ω) D e ∧
    D + stream (fun y Ω' => ψt e y Ω' / ρ y) x Ω + σt * ψt e x Ω =
      ∫ Ω', σs ⟪Ω, Ω'⟫ * ψt e x Ω' ∂μ

/-- The streaming and scattering terms of (8) are `S(E)` times those of (3), when
`ψ̃(Ẽ, ·, ·) = S(E) ρ ψ(E, ·, ·)` (Eq. (7)). -/
lemma stream_scatter_transformed {μ : Measure V} {S : ℝ → ℝ} {sigS : ℝ → ℝ → ℝ} {ρ : V → ℝ}
    {ψ ψt : ℝ → V → V → ℝ} {E e : ℝ} (hρ : ∀ y, ρ y ≠ 0)
    (hrel : ∀ y Ω', ψt e y Ω' = S E * ρ y * ψ E y Ω') (x Ω : V) :
    stream (fun y Ω' => ψt e y Ω' / ρ y) x Ω = S E * stream (ψ E) x Ω ∧
      ∫ Ω', sigS E ⟪Ω, Ω'⟫ * ψt e x Ω' ∂μ = S E * ∫ Ω', sigS E ⟪Ω, Ω'⟫ * ρ x * ψ E x Ω' ∂μ := by
  constructor
  · have hfun : (fun y => ψt e y Ω / ρ y) = S E • fun y => ψ E y Ω := by
      funext y
      rw [hrel y Ω, Pi.smul_apply, smul_eq_mul]
      field_simp [hρ y]
    simp only [stream]
    rw [hfun, fderiv_const_smul_field]
    rfl
  · simp_rw [hrel]
    rw [← integral_const_mul]
    congr 1
    funext Ω'
    ring

/-- arXiv 2205.08417, Eq. (8) implies (3): if the transformed density `ψ̃` of (7) solves (8) at
the pseudo-time `Ẽ(E)`, with `Σ̃ₜ(Ẽ(E)) = Σₜ(E)` and `Σ̃ₛ(Ẽ(E), ·) = Σₛ(E, ·)`, then `ψ` solves
the CSD equation (3) at `E`.  The stopping power is continuous and positive on `[0, E_max]` and
the density `ρ` does not vanish. -/
theorem isCSDAt_of_isTransformedAt {μ : Measure V} {S sigT : ℝ → ℝ} {sigS : ℝ → ℝ → ℝ}
    {ρ : V → ℝ} {ψ ψt : ℝ → V → V → ℝ} {Emax E : ℝ} {x Ω : V}
    (hc : ContinuousOn S (Icc 0 Emax)) (hpos : ∀ e ∈ Icc 0 Emax, 0 < S e) (hE : E ∈ Ioo 0 Emax)
    (hρ : ∀ y, ρ y ≠ 0)
    (hrel : ∀ e ∈ Ioo 0 Emax, ∀ y Ω', ψt (transformedEnergy S Emax e) y Ω' = S e * ρ y * ψ e y Ω')
    (h8 : IsTransformedAt μ (sigT E) (sigS E) ρ ψt (transformedEnergy S Emax E) x Ω) :
    IsCSDAt μ S sigT sigS ρ ψ E x Ω := by
  obtain ⟨Dt, hDt, heq⟩ := h8
  have hS : S E ≠ 0 := (hpos E (Ioo_subset_Icc_self hE)).ne'
  have hchain := hDt.comp E (hasDerivAt_transformedEnergy hc hpos hE)
  have hev : (fun e => S e * ρ x * ψ e x Ω) =ᶠ[𝓝 E]
      (fun e => ψt (transformedEnergy S Emax e) x Ω) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hE.1 hE.2) fun e he => (hrel e he x Ω).symm
  refine ⟨Dt * -(1 / S E), hchain.congr_of_eventuallyEq hev, ?_⟩
  obtain ⟨hst, hint⟩ := stream_scatter_transformed (μ := μ) (sigS := sigS) hρ
    (hrel E hE) x Ω
  rw [hst, hint, hrel E hE x Ω] at heq
  have hs' : S E * (S E)⁻¹ = 1 := mul_inv_cancel₀ hS
  linear_combination (S E)⁻¹ * heq - (stream (ψ E) x Ω + sigT E * ρ x * ψ E x Ω -
    ∫ Ω', sigS E ⟪Ω, Ω'⟫ * ρ x * ψ E x Ω' ∂μ) * hs'

/-- arXiv 2205.08417, Eqs. (3) and (8) are equivalent ("multiplying (3) with `S(E)` and plugging
in the defined transformation gives (8)"): for `ψ̃` defined by (7) and differentiable in the
pseudo-time at `Ẽ(E)`, `ψ` solves (3) at `E` if and only if `ψ̃` solves (8) at `Ẽ(E)` with
`Σ̃ₜ(Ẽ(E)) = Σₜ(E)` and `Σ̃ₛ(Ẽ(E), ·) = Σₛ(E, ·)`. -/
theorem isCSDAt_iff_isTransformedAt {μ : Measure V} {S sigT : ℝ → ℝ} {sigS : ℝ → ℝ → ℝ}
    {ρ : V → ℝ} {ψ ψt : ℝ → V → V → ℝ} {Emax E : ℝ} {x Ω : V}
    (hc : ContinuousOn S (Icc 0 Emax)) (hpos : ∀ e ∈ Icc 0 Emax, 0 < S e) (hE : E ∈ Ioo 0 Emax)
    (hρ : ∀ y, ρ y ≠ 0)
    (hrel : ∀ e ∈ Ioo 0 Emax, ∀ y Ω', ψt (transformedEnergy S Emax e) y Ω' = S e * ρ y * ψ e y Ω')
    (hD : DifferentiableAt ℝ (fun e => ψt e x Ω) (transformedEnergy S Emax E)) :
    IsCSDAt μ S sigT sigS ρ ψ E x Ω ↔
      IsTransformedAt μ (sigT E) (sigS E) ρ ψt (transformedEnergy S Emax E) x Ω := by
  refine ⟨fun h3 => ?_, isCSDAt_of_isTransformedAt hc hpos hE hρ hrel⟩
  obtain ⟨D, hD3, heq⟩ := h3
  have hS : S E ≠ 0 := (hpos E (Ioo_subset_Icc_self hE)).ne'
  set Dt := deriv (fun e => ψt e x Ω) (transformedEnergy S Emax E)
  have hchain := hD.hasDerivAt.comp E (hasDerivAt_transformedEnergy hc hpos hE)
  have hev : (fun e => S e * ρ x * ψ e x Ω) =ᶠ[𝓝 E]
      (fun e => ψt (transformedEnergy S Emax e) x Ω) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hE.1 hE.2) fun e he => (hrel e he x Ω).symm
  have hDeq : D = Dt * -(1 / S E) := hD3.unique (hchain.congr_of_eventuallyEq hev)
  refine ⟨Dt, hD.hasDerivAt, ?_⟩
  obtain ⟨hst, hint⟩ := stream_scatter_transformed (μ := μ) (sigS := sigS) hρ
    (hrel E hE) x Ω
  rw [hst, hint, hrel E hE x Ω]
  rw [hDeq] at heq
  have hs' : S E * (S E)⁻¹ = 1 := mul_inv_cancel₀ hS
  linear_combination S E * heq - Dt * hs'

end CSD

/-! ### The `P_N` closure as the quadratic-entropy closure (Sec. 3.1) -/

section Closure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι]

/-- The moments `u = ⟨m g⟩` of `g` with respect to the angular basis `m`, in an inner product
space `H` standing for `L²(𝕊²)`. -/
def moments (m : ι → H) (g : H) : ι → ℝ := fun i => ⟪m i, g⟫

/-- The `P_N` reconstruction (13), `ψ_{P_N} = uᵀ m`. -/
def pnRecon (m : ι → H) (u : ι → ℝ) : H := ∑ i, u i • m i

/-- The `P_N` closure map `g ↦ ψ_{P_N}(⟨m g⟩)`, the sum of the rank-one projectors of the basis
functions (the core `rankOneProj`). -/
noncomputable def pnProj (m : ι → H) : H →L[ℝ] H := ∑ i, rankOneProj (m i)

theorem pnProj_apply (m : ι → H) (g : H) : pnProj m g = pnRecon m (moments m g) := by
  simp [pnProj, pnRecon, moments]

/-- The `P_N` reconstruction reproduces its moments when the basis is orthonormal. -/
theorem moments_pnRecon {m : ι → H} (hm : Orthonormal ℝ m) (u : ι → ℝ) :
    moments m (pnRecon m u) = u := by
  classical
  funext i
  simp only [moments, pnRecon, inner_sum, real_inner_smul_right]
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq, hm.1 i]; ring
  · intro j _ hji; rw [hm.2 hji.symm, mul_zero]
  · simp

/-- For an orthonormal basis the `P_N` closure map is an orthogonal projector (core
`IsOrthProj`): the orthogonal projection onto the span of the basis functions. -/
theorem isOrthProj_pnProj {m : ι → H} (hm : Orthonormal ℝ m) : IsOrthProj (pnProj m) where
  idem x := by rw [pnProj_apply, pnProj_apply, moments_pnRecon hm]
  symm x y := by
    simp only [pnProj_apply, pnRecon, moments, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (m i) x]; ring

/-- arXiv 2205.08417, Sec. 3.1: the quadratic entropy `η(g) = g²` "recovers the `P_N` method".
Among all `g` with moments `⟨m g⟩ = u`, the `P_N` reconstruction `uᵀ m` has the least entropy
`∫ g² = ‖g‖²`, and it is the only minimiser.  Here `H` is any real inner product space
(`L²(𝕊²)` in the paper) and `m` an orthonormal family (the real spherical harmonics).  The set
`F_m` of (14) also asks `g > 0`; that constraint is dropped here, see `pnRecon_minimizes_on`. -/
theorem quadratic_entropy_closure {m : ι → H} (hm : Orthonormal ℝ m) (u : ι → ℝ) :
    moments m (pnRecon m u) = u ∧
      ∀ g, moments m g = u → ‖pnRecon m u‖ ^ 2 ≤ ‖g‖ ^ 2 ∧
        (‖g‖ ^ 2 = ‖pnRecon m u‖ ^ 2 → g = pnRecon m u) := by
  refine ⟨moments_pnRecon hm u, fun g hg => ?_⟩
  have hP := isOrthProj_pnProj hm
  have hPg : pnProj m g = pnRecon m u := by rw [pnProj_apply, hg]
  have hsum := hP.norm_sq_add g
  rw [hPg] at hsum
  refine ⟨by nlinarith [sq_nonneg ‖g - pnRecon m u‖], fun heq => ?_⟩
  have h0 : ‖g - pnRecon m u‖ ^ 2 = 0 := by linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))

/-- With a constraint set `F` such as the positive functions of (14): if the `P_N`
reconstruction belongs to `F`, it minimises the quadratic entropy over `F` with moments `u`.
So the remark of Sec. 3.1 holds with the positivity constraint exactly when `uᵀ m > 0`. -/
theorem pnRecon_minimizes_on {m : ι → H} (hm : Orthonormal ℝ m) (u : ι → ℝ) {F : Set H}
    (hF : pnRecon m u ∈ F) :
    pnRecon m u ∈ {g | g ∈ F ∧ moments m g = u} ∧
      ∀ g ∈ {g | g ∈ F ∧ moments m g = u}, ‖pnRecon m u‖ ^ 2 ≤ ‖g‖ ^ 2 :=
  ⟨⟨hF, moments_pnRecon hm u⟩, fun g hg => ((quadratic_entropy_closure hm u).2 g hg.2).1⟩

/-- The flux of the `P_N` closure (Sec. 3.1, the moment equations below (13)): for every linear
operator `K` (multiplication by `Ω_i` in the paper), `⟨m K(uᵀ m)⟩ = A u` with
`A_{jk} = ⟨m_j, K m_k⟩` (`A_i = ∫ m mᵀ Ω_i dΩ`). -/
theorem moments_map_pnRecon (m : ι → H) (K : H →L[ℝ] H) (u : ι → ℝ) :
    moments m (K (pnRecon m u)) = Matrix.of (fun j k => ⟪m j, K (m k)⟫) *ᵥ u := by
  funext j
  simp [moments, pnRecon, map_sum, inner_sum, real_inner_smul_right, Matrix.mulVec,
    dotProduct, mul_comm]

/-- Non-vacuity: the standard basis of `ℝⁿ` is orthonormal, so `isOrthProj_pnProj` and
`quadratic_entropy_closure` apply to it. -/
example (n : ℕ) : IsOrthProj (pnProj (EuclideanSpace.basisFun (Fin n) ℝ)) :=
  isOrthProj_pnProj (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal

end Closure

end LeanDLRA.Literature.P2205_08417
