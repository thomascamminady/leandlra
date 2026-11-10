import Mathlib
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Kinetic.LowRank

/-!
# A low-rank projector-splitting integrator for Vlasov–Poisson (arXiv 1801.01103)

Einkemmer, Lubich, *A low-rank projector-splitting integrator for the Vlasov–Poisson equation*.
The paper has no numbered theorems; its results are the derivations of Secs. 1–3.  This module
proves them for the actual objects: the exact free-streaming solution (1.2) and its rank; the
products `X_i V_j` in `L²(Ω_x) ⊗ L²(Ω_v) ⊂ L²(Ω_x × Ω_v)` with the gauge-fixed equations
(2.2)–(2.5), uniqueness of the factor derivatives, and the projector (2.7) as the orthogonal
projector onto the tangent space; the reduction of the three substeps (2.8)–(2.10) with the true
operator `v·∇ₓ - E(f)·∇ᵥ` to the `r` equations (2.13) in `x`, the `r²` ordinary differential
equations (2.14) and the `r` equations (2.15) in `v`; the decoupling of Sec. 2.2 by the symmetric
coefficient matrices; and from Sec. 3 Algorithm 2 run on core tensors, (3.13), (3.14), and the fact
that the Tucker step for the identity factor is void.

## Main results

* (1.2): `freeStream_solves`, `freeStream_unique`, `freeStream_eq`, `freeStream_hasRankLE_two`,
  `freeStream_not_hasRankLE_one`, `freeStream_hasRankLE_one_iff`.
* Sec. 2.2: `c1_isSymm`, `d1_isSymm`, `exists_orthogonal_diagonalisation`, `advection_scalar`,
  `advection_decouple`, `kAdvection_decouple`, `lAdvection_decouple`.
* (2.2)–(2.7): `hasDerivAt_ansatz`, `coreDeriv_eq`, `eq_2_4`, `eq_2_5`, `factorDeriv_unique`,
  `tangentP_apply`, `isOrthProj_tangentP`, `isTangent_iff`, and in `L²(μ × ν)`
  `l2_gauge_equations`, `l2_tangent_space`, with the integrals `partialX_coeFn`, `partialV_coeFn`,
  `projX_coeFn`, `projV_coeFn`.
* (2.8)–(2.15): `kStep_iff`, `sStep_iff`, `lStep_iff`, `field_lowRank_K`, `field_lowRank_S`,
  `field_lowRank_L`, `kStep_factor_fixed`, `lStep_factor_fixed`, `sStep_factors_fixed`,
  `IsLieStep.splitting`, with the instance `isLieStep_trivial`.
* Sec. 3: `inner_coreMap` (3.13), `coreMap_add_smul` (3.14), `mgs_spec`, `algorithm2_core`,
  `coreMap_eq_of_qr`, `a1_formula`, `a1_symm`, `tucker_square_factor_step`,
  `tucker_identity_factor_unchanged`, `leftProj_of_square`, `ksl_cancel_of_identity`.

## Statements that need a qualification

* **"Exactly rank two for all `t`" is false at `t = 0` and for `k = 0`**, where the rank is one
  (`freeStream_hasRankLE_one_iff`).  The paper only says that rank two suffices, which holds for all
  `k`, `t` (`freeStream_hasRankLE_two`); the rank is exactly two if and only if `k t ≠ 0`.
* Algorithm 2 divides by `S_jj`, so it needs independent `K_j`.  The paper does not say so
  (`mgs_spec`, `algorithm2_core`).
* "The first step leaves both `C` and `A` unchanged" holds for the decomposition
  `K(t₁) = 1 · K(t₁)`.  A QR decomposition with `U¹ ≠ 1` leaves the tensor unchanged, but changes
  `A` and `C` by `U¹` (`tucker_square_factor_step`, `tucker_identity_factor_unchanged`).  The
  cancellation uses that the right-hand side does not depend on `t` explicitly, as is the case here.
  With the Lipschitz hypothesis on `G`, which only holds after discretization, every solution of
  the S-step cancels; without it, `odeSolution_reverse` still says that the time-reversed K-step
  is a solution of the S-step.
* Misprint: the paper writes `ρ(t, x) = -∑_j K_j(t, x) ρ(V_j⁰)` with `ρ(V_j⁰) = ∫ V_j⁰ dv`, against
  its `ρ(f) = -∫ f dv`.  We use the integrals (`fieldK`, `fieldS`, `fieldL`).

## Modelling choices

* Sec. 2 up to (2.7) holds for any bilinear `τ` with `⟨a ⊗ b, c ⊗ d⟩ = ⟨a, c⟩ ⟨b, d⟩`
  (`IsTensorPairing`); the model is `tensL2` on `L²(μ) × L²(ν)` for arbitrary σ-finite measures,
  which covers any `Ω_x`, `Ω_v`.  `partialX`, `partialV` are defined as adjoints, and
  `partialX_coeFn`, `partialV_coeFn` show that they are the integrals of the paper.
* The substeps are stated pointwise, because `v·∇ₓ` is unbounded on `L²`.  `μ`, `ν` are arbitrary
  measures on `ℝ^d`, `∇` is `fderiv` on `ℝ^d`, so functions on a torus enter through their periodic
  extension.  `E(f) = 𝓔(ρ(f))` for an arbitrary `𝓔`, which includes the solution operator of the
  Poisson problem; the Poisson equation itself is never used.  `IsVelocityBasis`, `IsSpaceBasis`
  only ask that the printed integrals exist.  As in the paper, existence of solutions of
  (2.13)–(2.15) is not addressed.  The operator `F = -(v·∇ₓ - E·∇ᵥ)` is `vlasovF`; it, `PS`, `pd`,
  `lowRank`, `coreK`, `proj`, `IsOrthonormalL2` are the definitions of the module of arXiv
  1807.02338, repeated here to keep this module independent of it.
* Sec. 3 is stated for `d = 2`, with two factors `X¹`, `X²` and any `IsTensorPairing`, which
  includes `L²(Ω_{x₁}) ⊗ L²(Ω_{x₂})` by `tensL2`.  The first Tucker step is stated for the
  matricization `Mat₁(C)`, with `G` the map `K ↦ Mat₁(F(Ten₁(K Vᵀ))) V` of arXiv 1709.02594.
  `mgsState` is the in-place loop of Algorithm 2.

## Not formalized

Secs. 2.1, 2.3 (time stepping, frozen fields), the bound `‖∂ᵥᵐ f‖ ∝ (k t)ᵐ`, which is asymptotic,
the evolution equations (3.7)–(3.12) beyond `a¹`, the case `d = 3` of Sec. 3.2, and Sec. 4
(numerics).
The robust bound `ksl_global_error_le` of the library is not used: it needs a Lipschitz field, which
the transport operator is only after discretization.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace LeanDLRA.Literature.P1801_01103

/-! ### Eq. (1.2): free streaming has rank two -/

section FreeStreaming

/-- `f(x, v)` is a sum of at most `r` separated terms `A_i(x) B_i(v)`. -/
def HasRankLE {α β : Type*} (f : α → β → ℝ) (r : ℕ) : Prop :=
  ∃ (A : Fin r → α → ℝ) (B : Fin r → β → ℝ), ∀ x v, f x v = ∑ i, A i x * B i v

/-- The exact solution (1.2), `f(t, x, v) = cos(k (x - v t)) e^{-v²/2}`, written as a function of
`k, t, x, v`. -/
noncomputable def freeStream (k t x v : ℝ) : ℝ :=
  Real.cos (k * (x - v * t)) * Real.exp (-v ^ 2 / 2)

/-- **(1.2), initial value** (arXiv 1801.01103): `f(0, x, v) = cos(k x) e^{-v²/2}`. -/
theorem freeStream_zero (k x v : ℝ) :
    freeStream k 0 x v = Real.cos (k * x) * Real.exp (-v ^ 2 / 2) := by
  simp [freeStream]

/-- The `t`-derivative of `freeStream`, for (1.2) of arXiv 1801.01103. -/
theorem hasDerivAt_freeStream_t (k t x v : ℝ) :
    HasDerivAt (fun s => freeStream k s x v)
      (k * v * Real.sin (k * (x - v * t)) * Real.exp (-v ^ 2 / 2)) t := by
  have h : HasDerivAt (fun s : ℝ => k * (x - v * s)) (-(k * v)) t := by
    have := ((hasDerivAt_id t).const_mul v).const_sub x |>.const_mul k
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have := (h.cos).mul_const (Real.exp (-v ^ 2 / 2))
  exact this.congr_deriv (by ring)

/-- The `x`-derivative of `freeStream`, for (1.2) of arXiv 1801.01103. -/
theorem hasDerivAt_freeStream_x (k t x v : ℝ) :
    HasDerivAt (fun y => freeStream k t y v)
      (-(k * Real.sin (k * (x - v * t))) * Real.exp (-v ^ 2 / 2)) x := by
  have h : HasDerivAt (fun y : ℝ => k * (y - v * t)) k x := by
    simpa using ((hasDerivAt_id x).sub_const (v * t)).const_mul k
  have := (h.cos).mul_const (Real.exp (-v ^ 2 / 2))
  exact this.congr_deriv (by ring)

/-- **(1.2), the equation** (arXiv 1801.01103): `f = cos(k (x - v t)) e^{-v²/2}` solves the free
streaming equation `∂ₜf + v ∂ₓf = 0`, the Vlasov–Poisson equation without its nonlinear term. -/
theorem freeStream_solves (k t x v : ℝ) :
    deriv (fun s => freeStream k s x v) t + v * deriv (fun y => freeStream k t y v) x = 0 := by
  rw [(hasDerivAt_freeStream_t k t x v).deriv, (hasDerivAt_freeStream_x k t x v).deriv]
  ring

/-- **The displayed formula after (1.2)** (arXiv 1801.01103):
`f(t, x, v) = (cos(k x) cos(k v t) + sin(k x) sin(k v t)) e^{-v²/2}`. -/
theorem freeStream_eq (k t x v : ℝ) :
    freeStream k t x v =
      (Real.cos (k * x) * Real.cos (k * v * t) + Real.sin (k * x) * Real.sin (k * v * t)) *
        Real.exp (-v ^ 2 / 2) := by
  rw [freeStream, show k * (x - v * t) = k * x - k * v * t by ring, Real.cos_sub]

/-- **(1.2), rank at most two** (arXiv 1801.01103): "the linear part of the equation can be
represented exactly with rank two", for all `k` and `t`, although the `v`-wave number `k t` grows
without bound (filamentation). -/
theorem freeStream_hasRankLE_two (k t : ℝ) : HasRankLE (freeStream k t) 2 := by
  refine ⟨![fun x => Real.cos (k * x), fun x => Real.sin (k * x)],
    ![fun v => Real.cos (k * v * t) * Real.exp (-v ^ 2 / 2),
      fun v => Real.sin (k * v * t) * Real.exp (-v ^ 2 / 2)], fun x v => ?_⟩
  rw [freeStream_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **(1.2), the rank is exactly two as soon as `k t ≠ 0`** (arXiv 1801.01103): `f(t, ·, ·)` is not
a single product `A(x) B(v)`. -/
theorem freeStream_not_hasRankLE_one {k t : ℝ} (hk : k ≠ 0) (ht : t ≠ 0) :
    ¬ HasRankLE (freeStream k t) 1 := by
  rintro ⟨A, B, h⟩
  simp only [Fin.sum_univ_one] at h
  have hk' : (2 * k) ≠ 0 := mul_ne_zero two_ne_zero hk
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ = Real.pi / (2 * k) := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v₂, v₂ = Real.pi / (2 * k * t) := ⟨_, rfl⟩
  have e1 : k * (x₂ - v₂ * t) = 0 := by
    rw [hx₂, hv₂]; field_simp; ring
  have e2 : k * (0 - v₂ * t) = -(Real.pi / 2) := by
    rw [hv₂]; field_simp; ring
  have e3 : k * (x₂ - 0 * t) = Real.pi / 2 := by
    rw [hx₂]; field_simp; ring
  have h11 : freeStream k t 0 0 = 1 := by simp [freeStream]
  have h22 : freeStream k t x₂ v₂ = Real.exp (-v₂ ^ 2 / 2) := by
    simp [freeStream, e1]
  have h12 : freeStream k t 0 v₂ = 0 := by
    rw [freeStream, e2, Real.cos_neg, Real.cos_pi_div_two, zero_mul]
  have h21 : freeStream k t x₂ 0 = 0 := by
    rw [freeStream, e3, Real.cos_pi_div_two, zero_mul]
  have hdet : freeStream k t 0 0 * freeStream k t x₂ v₂ =
      freeStream k t 0 v₂ * freeStream k t x₂ 0 := by
    simp only [h]; ring
  rw [h11, h22, h12, h21] at hdet
  have := Real.exp_pos (-v₂ ^ 2 / 2)
  simp only [one_mul, zero_mul] at hdet
  linarith

/-- **(1.2), degenerate cases** (arXiv 1801.01103): at `t = 0` and for `k = 0` the solution has
rank one.  So "rank exactly two" holds if and only if `k t ≠ 0`, not for all `t`: the paper only
claims that rank two suffices. -/
theorem freeStream_hasRankLE_one_iff (k t : ℝ) :
    HasRankLE (freeStream k t) 1 ↔ k = 0 ∨ t = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    exact freeStream_not_hasRankLE_one hc.1 hc.2 h
  · rintro (rfl | rfl)
    · exact ⟨fun _ _ => 1, fun _ v => Real.exp (-v ^ 2 / 2), fun x v => by simp [freeStream]⟩
    · exact ⟨fun _ x => Real.cos (k * x), fun _ v => Real.exp (-v ^ 2 / 2),
        fun x v => by simp [freeStream]⟩

end FreeStreaming

/-! ### Sec. 2.2: symmetric coefficient matrices decouple the advections -/

section Advection

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- `M` is a differentiable solution of the coupled advection system `∂ₜM = -A ∂_e M`,
`∂ₜM_j(t, x) = -∑_l A_jl ∂_e M_l(t, x)`: the system of Sec. 2.2 for `M` with `e` the unit vector
of a coordinate direction. -/
structure IsAdvectionSol (A : Matrix ι ι ℝ) (e : W) (M : ℝ → W → ι → ℝ) : Prop where
  differentiable : ∀ j, Differentiable ℝ fun p : ℝ × W => M p.1 p.2 j
  eqn : ∀ t x j, deriv (fun s => M s x j) t = -∑ l, A j l * fderiv ℝ (fun y => M t y l) x e

private lemma diffAt_t {u : ℝ × W → ℝ} (hu : Differentiable ℝ u) (t : ℝ) (x : W) :
    DifferentiableAt ℝ (fun s => u (s, x)) t :=
  (hu _).comp t (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => (s, x)) t)

private lemma diffAt_x {u : ℝ × W → ℝ} (hu : Differentiable ℝ u) (t : ℝ) (x : W) :
    DifferentiableAt ℝ (fun y => u (t, y)) x :=
  (hu _).comp x (by fun_prop : DifferentiableAt ℝ (fun y : W => (t, y)) x)

/-- **Sec. 2.2** (arXiv 1801.01103), the change of variables `M̄ = T M`: `T` orthogonal turns
`∂ₜM = -A ∂_e M` into `∂ₜM̄ = -(T A Tᵀ) ∂_e M̄`. -/
theorem IsAdvectionSol.mulVec {A T : Matrix ι ι ℝ} {e : W} {M : ℝ → W → ι → ℝ}
    (hM : IsAdvectionSol A e M) (hT : Tᵀ * T = 1) :
    IsAdvectionSol (T * A * Tᵀ) e fun t x => T *ᵥ M t x := by
  have hd : ∀ j, Differentiable ℝ fun p : ℝ × W => (T *ᵥ M p.1 p.2) j := fun j => by
    simp only [Matrix.mulVec, dotProduct]
    exact Differentiable.fun_sum fun l _ => (differentiable_const _).mul (hM.differentiable l)
  refine ⟨hd, fun t x j => ?_⟩
  have ht : ∀ l, DifferentiableAt ℝ (fun s => M s x l) t := fun l =>
    diffAt_t (hM.differentiable l) t x
  have hx : ∀ (s : ℝ) l, DifferentiableAt ℝ (fun y => M s y l) x := fun s l =>
    diffAt_x (hM.differentiable l) s x
  have h1 : deriv (fun s => (T *ᵥ M s x) j) t = ∑ l, T j l * deriv (fun s => M s x l) t := by
    have : HasDerivAt (fun s => ∑ l, T j l * M s x l)
        (∑ l, T j l * deriv (fun s => M s x l) t) t :=
      HasDerivAt.fun_sum fun l _ => (ht l).hasDerivAt.const_mul _
    exact this.deriv
  have h2 : ∀ m, fderiv ℝ (fun y => (T *ᵥ M t y) m) x e =
      ∑ l, T m l * fderiv ℝ (fun y => M t y l) x e := fun m => by
    have : HasFDerivAt (fun y => ∑ l, T m l * M t y l)
        (∑ l, T m l • fderiv ℝ (fun y => M t y l) x) x :=
      HasFDerivAt.fun_sum fun l _ => (hx t l).hasFDerivAt.const_mul _
    simpa [Matrix.mulVec, dotProduct] using congrArg (· e) this.fderiv
  set G : ι → ℝ := fun l => fderiv ℝ (fun y => M t y l) x e with hG
  have h3 : ∑ m, (T * A * Tᵀ) j m * ∑ l, T m l * G l = ∑ l, (T * A) j l * G l := by
    have : (T * A * Tᵀ) *ᵥ (T *ᵥ G) = (T * A) *ᵥ G := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hT, Matrix.mul_one]
    simpa [Matrix.mulVec, dotProduct] using congrFun this j
  have h4 : ∑ l, T j l * ∑ m, A l m * G m = ∑ l, (T * A) j l * G l := by
    have : T *ᵥ (A *ᵥ G) = (T * A) *ᵥ G := Matrix.mulVec_mulVec _ _ _
    simpa [Matrix.mulVec, dotProduct] using congrFun this j
  have h5 : ∀ l, deriv (fun s => M s x l) t = -∑ m, A l m * G m := fun l => hM.eqn t x l
  rw [h1]
  simp only [h2, h5, mul_neg, Finset.sum_neg_distrib]
  rw [h3, h4]

/-- **Sec. 2.2** (arXiv 1801.01103): the scalar advection equation `∂ₜu = -a ∂_e u` has the
characteristic solution
`u(t, x) = u(0, x - t a e)`, the "one-dimensional advection equation with constant coefficients"
of Sec. 2.2. -/
theorem advection_scalar {u : ℝ → W → ℝ} {a : ℝ} {e : W}
    (hu : Differentiable ℝ fun p : ℝ × W => u p.1 p.2)
    (h : ∀ t x, deriv (fun s => u s x) t = -a * fderiv ℝ (fun y => u t y) x e) (t : ℝ) (x : W) :
    u t x = u 0 (x - (t * a) • e) := by
  set U : ℝ × W → ℝ := fun p => u p.1 p.2 with hU
  set x₀ : W := x - (t * a) • e with hx₀
  set φ : ℝ → ℝ := fun s => U (s, x₀ + (s * a) • e) with hφ
  have hd : ∀ s, HasDerivAt φ 0 s := fun s => by
    have hc : HasDerivAt (fun s : ℝ => (s, x₀ + (s * a) • e)) ((1 : ℝ), a • e) s := by
      refine (hasDerivAt_id s).prodMk ?_
      have := ((hasDerivAt_id s).mul_const a).smul_const e
      simpa using this.const_add x₀
    set y := x₀ + (s * a) • e with hy
    have hF := (hu (s, y)).hasFDerivAt
    have h1 := hF.comp_hasDerivAt s hc
    set D := fderiv ℝ U (s, y) with hD
    have ht : deriv (fun r => u r y) s = D ((1 : ℝ), (0 : W)) := by
      have hc' : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : W)) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
      exact (hF.comp_hasDerivAt s hc').deriv
    have hx : fderiv ℝ (fun w => u s w) y e = D ((0 : ℝ), e) := by
      have hc' : HasFDerivAt (fun w : W => (s, w))
          ((0 : W →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ W)) y :=
        (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
      have h' : HasFDerivAt (fun w => u s w)
          (D.comp ((0 : W →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ W))) y := hF.comp y hc'
      rw [h'.fderiv]
      simp
    have hsplit : D ((1 : ℝ), a • e) = D ((1 : ℝ), (0 : W)) + a * D ((0 : ℝ), e) := by
      have : ((1 : ℝ), a • e) = ((1 : ℝ), (0 : W)) + a • ((0 : ℝ), e) := by simp
      rw [this, map_add, map_smul, smul_eq_mul]
    have h0 : D ((1 : ℝ), a • e) = 0 := by
      rw [hsplit, ← ht, ← hx, h s y]; ring
    rw [← h0]
    exact h1
  have hconst : φ t = φ 0 := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [hφ, hU, hx₀] using hconst

/-- **Sec. 2.2** (arXiv 1801.01103): a diagonal system is a family of decoupled scalar advections,
solved along characteristics. -/
theorem IsAdvectionSol.diagonal_formula {D : ι → ℝ} {e : W} {N : ℝ → W → ι → ℝ}
    (hN : IsAdvectionSol (Matrix.diagonal D) e N) (t : ℝ) (x : W) (j : ι) :
    N t x j = N 0 (x - (t * D j) • e) j := by
  refine advection_scalar (u := fun t x => N t x j) (hN.differentiable j) (fun t x => ?_) t x
  rw [hN.eqn t x j, Finset.sum_eq_single j]
  · simp
  · intro l _ hl; simp [Matrix.diagonal_apply_ne _ hl.symm]
  · simp

/-- **Sec. 2.2** (arXiv 1801.01103): the travelling waves `N_j(t, x) = N⁰_j(x - t D_j e)` solve
the diagonal system. -/
theorem isAdvectionSol_diagonal {D : ι → ℝ} {e : W} {N₀ : W → ι → ℝ}
    (hN : ∀ j, Differentiable ℝ fun x => N₀ x j) :
    IsAdvectionSol (Matrix.diagonal D) e fun t x j => N₀ (x - (t * D j) • e) j := by
  refine ⟨fun j => (hN j).comp (by fun_prop), fun t x j => ?_⟩
  rw [Finset.sum_eq_single j (fun l _ hl => by simp [Matrix.diagonal_apply_ne _ hl.symm])
    (fun h => absurd (Finset.mem_univ j) h), Matrix.diagonal_apply_eq]
  set z := x - (t * D j) • e with hz
  have hc : HasDerivAt (fun s : ℝ => x - (s * D j) • e) (-(D j • e)) t := by
    have := (((hasDerivAt_id t).mul_const (D j)).smul_const e).const_sub x
    simpa using this
  have h1 := (hN j z).hasFDerivAt.comp_hasDerivAt t hc
  have h2 : HasFDerivAt (fun y : W => y - (t * D j) • e) (ContinuousLinearMap.id ℝ W) x :=
    (hasFDerivAt_id x).sub_const _
  have h3 : HasFDerivAt ((fun x => N₀ x j) ∘ fun y : W => y - (t * D j) • e)
      ((fderiv ℝ (fun x => N₀ x j) z).comp (ContinuousLinearMap.id ℝ W)) x :=
    (hN j z).hasFDerivAt.comp x h2
  have h4 : fderiv ℝ (fun y => N₀ (y - (t * D j) • e) j) x e = fderiv ℝ (fun x => N₀ x j) z e := by
    rw [show (fun y => N₀ (y - (t * D j) • e) j) =
      (fun x => N₀ x j) ∘ fun y : W => y - (t * D j) • e from rfl, h3.fderiv]
    simp
  rw [h4, show deriv (fun s => N₀ (x - (s * D j) • e) j) t = _ from h1.deriv]
  simp

/-- **Sec. 2.2, diagonalisation** (arXiv 1801.01103): a real symmetric matrix `A` is orthogonally
diagonalisable, `T A Tᵀ = D`.  Uses the spectral theorem for real symmetric matrices. -/
theorem exists_orthogonal_diagonalisation {A : Matrix ι ι ℝ} (hA : A.IsSymm) :
    ∃ (T : Matrix ι ι ℝ) (D : ι → ℝ), Tᵀ * T = 1 ∧ T * A * Tᵀ = Matrix.diagonal D := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  have hU1 : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hU2 : U * Uᵀ = 1 := mul_eq_one_comm.mp hU1
  have hs := hH.spectral_theorem
  have hA' : A = U * Matrix.diagonal hH.eigenvalues * Uᵀ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  refine ⟨Uᵀ, hH.eigenvalues, by simpa using hU2, ?_⟩
  rw [Matrix.transpose_transpose]
  calc Uᵀ * A * U = Uᵀ * (U * Matrix.diagonal hH.eigenvalues * Uᵀ) * U :=
        congrArg (fun B => Uᵀ * B * U) hA'
    _ = (Uᵀ * U) * Matrix.diagonal hH.eigenvalues * (Uᵀ * U) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal hH.eigenvalues := by rw [hU1, Matrix.one_mul, Matrix.mul_one]

/-- **Sec. 2.2, decoupling** (arXiv 1801.01103).  Let `T` be orthogonal with `T A Tᵀ = D`.  Then
`M` solves `∂ₜM = -A ∂_e M` if and only if `M̄ = T M` solves the decoupled scalar advections
`∂ₜM̄_j = -D_j ∂_e M̄_j`; every solution is recovered by undoing the transformation,
`M_j(t, x) = ∑_l T_lj M̄_l(0, x - t D_l e)`; and this formula produces a solution for all
differentiable initial data.  This is the computation of `M(t, x) = e^{-t c ∂ₓ} M(0, x)`. -/
theorem advection_decouple {A T : Matrix ι ι ℝ} {D : ι → ℝ} (e : W) (hT : Tᵀ * T = 1)
    (hD : T * A * Tᵀ = Matrix.diagonal D) :
    (∀ M : ℝ → W → ι → ℝ, IsAdvectionSol A e M ↔
      IsAdvectionSol (Matrix.diagonal D) e fun t x => T *ᵥ M t x) ∧
    (∀ M : ℝ → W → ι → ℝ, IsAdvectionSol A e M → ∀ t x j,
      M t x j = ∑ l, T l j * (T *ᵥ M 0 (x - (t * D l) • e)) l) ∧
    (∀ M₀ : W → ι → ℝ, (∀ j, Differentiable ℝ fun x => M₀ x j) →
      IsAdvectionSol A e fun t x j => ∑ l, T l j * (T *ᵥ M₀ (x - (t * D l) • e)) l) := by
  have hT' : T * Tᵀ = 1 := mul_eq_one_comm.mp hT
  have hA : Tᵀ * Matrix.diagonal D * T = A := by
    rw [← hD]
    calc Tᵀ * (T * A * Tᵀ) * T = (Tᵀ * T) * A * (Tᵀ * T) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hT, Matrix.one_mul, Matrix.mul_one]
  have hback : ∀ N : ℝ → W → ι → ℝ, IsAdvectionSol (Matrix.diagonal D) e N →
      IsAdvectionSol A e fun t x => Tᵀ *ᵥ N t x := fun N hN => by
    have := hN.mulVec (T := Tᵀ) (by simpa using hT')
    rwa [Matrix.transpose_transpose, hA] at this
  have hrec : ∀ (M : ℝ → W → ι → ℝ) t x, Tᵀ *ᵥ (T *ᵥ M t x) = M t x := fun M t x => by
    rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  refine ⟨fun M => ⟨fun hM => ?_, fun hN => ?_⟩, fun M hM t x j => ?_, fun M₀ hM₀ => ?_⟩
  · have := hM.mulVec hT
    rwa [hD] at this
  · have := hback _ hN
    simpa only [hrec] using this
  · have hN : IsAdvectionSol (Matrix.diagonal D) e fun t x => T *ᵥ M t x := by
      have := hM.mulVec hT
      rwa [hD] at this
    have h := congrFun (hrec M t x) j
    rw [← h]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hN.diagonal_formula t x l
    simp only [Matrix.mulVec, dotProduct] at this
    rw [this]
  · have hN := isAdvectionSol_diagonal (D := D) (e := e) (N₀ := fun x => T *ᵥ M₀ x) fun j => by
      simp only [Matrix.mulVec, dotProduct]
      exact Differentiable.fun_sum fun l _ => (differentiable_const _).mul (hM₀ l)
    have heq : (fun t x j => ∑ l, T l j * (T *ᵥ M₀ (x - (t * D l) • e)) l) =
        fun t x => Tᵀ *ᵥ fun j => (T *ᵥ M₀ (x - (t * D j) • e)) j := by
      funext t x j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [heq]
    exact hback _ hN

/-- **(1.2), "the exact solution"** (arXiv 1801.01103): `f` of (1.2) is the only differentiable
solution of `∂ₜf + v ∂ₓf = 0` with the initial value `cos(k x) e^{-v²/2}`, for each fixed `v`. -/
theorem freeStream_unique {k v : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : Differentiable ℝ fun p : ℝ × ℝ => u p.1 p.2)
    (h : ∀ t x, deriv (fun s => u s x) t + v * deriv (fun y => u t y) x = 0)
    (h0 : ∀ x, u 0 x = Real.cos (k * x) * Real.exp (-v ^ 2 / 2)) (t x : ℝ) :
    u t x = freeStream k t x v := by
  have h1 := advection_scalar (a := v) (e := (1 : ℝ)) hu (fun t x => by
    change deriv (fun s => u s x) t = -v * deriv (fun y => u t y) x
    linarith [h t x]) t x
  rw [h1, h0, freeStream, smul_eq_mul, mul_one, mul_comm t v]

end Advection

/-! ### The tensor pairing `L²(Ω_x) × L²(Ω_v) → L²(Ω)`, partial inner products, projectors -/

section Tensor

variable {ι Hx Hv H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup Hx] [InnerProductSpace ℝ Hx] [CompleteSpace Hx]
  [NormedAddCommGroup Hv] [InnerProductSpace ℝ Hv] [CompleteSpace Hv]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The bilinear map `(a, b) ↦ a ⊗ b`, `(a ⊗ b)(x, v) = a(x) b(v)`, with
`⟨a ⊗ b, c ⊗ d⟩ = ⟨a, c⟩ ⟨b, d⟩`.  The model is `tensL2` below. -/
structure IsTensorPairing (τ : Hx →L[ℝ] Hv →L[ℝ] H) : Prop where
  inner_eq : ∀ a b c d, ⟪τ a b, τ c d⟫ = ⟪a, c⟫ * ⟪b, d⟫

/-- The partial inner product `⟨a, g⟩ₓ`, a function of `v`, as the adjoint of `b ↦ a ⊗ b`;
pointwise formula: `partialX_coeFn`. -/
noncomputable def partialX (τ : Hx →L[ℝ] Hv →L[ℝ] H) (a : Hx) : H →L[ℝ] Hv :=
  ContinuousLinearMap.adjoint (τ a)

/-- The partial inner product `⟨b, g⟩ᵥ`, a function of `x`, as the adjoint of `a ↦ a ⊗ b`;
pointwise formula: `partialV_coeFn`. -/
noncomputable def partialV (τ : Hx →L[ℝ] Hv →L[ℝ] H) (b : Hv) : H →L[ℝ] Hx :=
  ContinuousLinearMap.adjoint (τ.flip b)

variable {τ : Hx →L[ℝ] Hv →L[ℝ] H}

lemma inner_partialX (a : Hx) (g : H) (b : Hv) : ⟪partialX τ a g, b⟫ = ⟪g, τ a b⟫ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

lemma inner_partialV (b : Hv) (g : H) (a : Hx) : ⟪partialV τ b g, a⟫ = ⟪g, τ a b⟫ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

lemma partialX_tensor (ht : IsTensorPairing τ) (a c : Hx) (b : Hv) :
    partialX τ a (τ c b) = ⟪a, c⟫ • b := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_partialX, ht.inner_eq, real_inner_smul_left, real_inner_comm a c]

lemma partialV_tensor (ht : IsTensorPairing τ) (b d : Hv) (a : Hx) :
    partialV τ b (τ a d) = ⟪b, d⟫ • a := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_partialV, ht.inner_eq, real_inner_smul_left, real_inner_comm b d, mul_comm]

/-- `P_X̄ g = ∑_i X_i ⟨X_i, g⟩ₓ`, the projector onto `span{X_i}` "which acts only on the
`x`-variable". -/
noncomputable def projX (τ : Hx →L[ℝ] Hv →L[ℝ] H) (X : ι → Hx) : H →L[ℝ] H :=
  ∑ i, (τ (X i)).comp (partialX τ (X i))

/-- `P_V̄ g = ∑_j ⟨V_j, g⟩ᵥ V_j`, the projector onto `span{V_j}` "which acts only on the
`v`-variable". -/
noncomputable def projV (τ : Hx →L[ℝ] Hv →L[ℝ] H) (V : ι → Hv) : H →L[ℝ] H :=
  ∑ j, (τ.flip (V j)).comp (partialV τ (V j))

lemma projX_apply (X : ι → Hx) (g : H) : projX τ X g = ∑ i, τ (X i) (partialX τ (X i) g) := by
  simp [projX]

lemma projV_apply (V : ι → Hv) (g : H) : projV τ V g = ∑ j, τ (partialV τ (V j) g) (V j) := by
  simp [projV]

/-- The ansatz (2.1), `f = ∑_ij X_i S_ij V_j`. -/
noncomputable def ansatz (τ : Hx →L[ℝ] Hv →L[ℝ] H) (X : ι → Hx) (S : Matrix ι ι ℝ) (V : ι → Hv) :
    H :=
  ∑ i, ∑ j, S i j • τ (X i) (V j)

/-- The right-hand side of (2.2), `ḟ = ∑_ij (X_i Ṡ_ij V_j + Ẋ_i S_ij V_j + X_i S_ij V̇_j)`. -/
noncomputable def tangentVec (τ : Hx →L[ℝ] Hv →L[ℝ] H) (X : ι → Hx) (S : Matrix ι ι ℝ) (V : ι → Hv)
    (X' : ι → Hx) (S' : Matrix ι ι ℝ) (V' : ι → Hv) : H :=
  ∑ i, ∑ j, (S' i j • τ (X i) (V j) + S i j • τ (X' i) (V j) + S i j • τ (X i) (V' j))

/-- **(2.2)** (arXiv 1801.01103): along a differentiable path of factors, the time derivative of
`f = ∑ X_i S_ij V_j` is `∑ (X_i Ṡ_ij V_j + Ẋ_i S_ij V_j + X_i S_ij V̇_j)`. -/
theorem hasDerivAt_ansatz {X : ℝ → ι → Hx} {V : ℝ → ι → Hv} {S : ℝ → Matrix ι ι ℝ} {t : ℝ}
    {X' : ι → Hx} {V' : ι → Hv} {S' : Matrix ι ι ℝ}
    (hX : ∀ i, HasDerivAt (fun s => X s i) (X' i) t)
    (hV : ∀ j, HasDerivAt (fun s => V s j) (V' j) t)
    (hS : ∀ i j, HasDerivAt (fun s => S s i j) (S' i j) t) :
    HasDerivAt (fun s => ansatz τ (X s) (S s) (V s))
      (tangentVec τ (X t) (S t) (V t) X' S' V') t := by
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have h1 : HasDerivAt (fun s => τ (X s i)) (τ (X' i)) t := τ.hasFDerivAt.comp_hasDerivAt t (hX i)
  have h2 := h1.clm_apply (hV j)
  have h3 := (hS i j).smul h2
  refine h3.congr_deriv ?_
  rw [smul_add, add_assoc]
  simp only [add_comm]
  abel

section Gauge

variable {X : ι → Hx} {V : ι → Hv} {S : Matrix ι ι ℝ} {X' : ι → Hx} {V' : ι → Hv}
  {S' : Matrix ι ι ℝ}

/-- **(2.3)** (arXiv 1801.01103): with orthonormal `X_i`, `V_j` and the gauge conditions
`⟨X_i, Ẋ_j⟩ₓ = 0`, `⟨V_i, V̇_j⟩ᵥ = 0`, "`Ṡ_ij` is uniquely determined by `ḟ`":
`Ṡ_ij = ⟨X_i V_j, ḟ⟩ₓᵥ`. -/
theorem coreDeriv_eq (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X) (hV : Orthonormal ℝ V)
    (hgX : ∀ i j, ⟪X i, X' j⟫ = 0) (hgV : ∀ i j, ⟪V i, V' j⟫ = 0) (i j : ι) :
    S' i j = ⟪τ (X i) (V j), tangentVec τ X S V X' S' V'⟫ := by
  have hXi : ∀ i k, ⟪X i, X k⟫ = if i = k then (1 : ℝ) else 0 := fun i k =>
    orthonormal_iff_ite.mp hX i k
  have hVi : ∀ i k, ⟪V i, V k⟫ = if i = k then (1 : ℝ) else 0 := fun i k =>
    orthonormal_iff_ite.mp hV i k
  simp only [tangentVec, inner_sum, inner_add_right, real_inner_smul_right, ht.inner_eq, hgX, hgV,
    hXi, hVi, mul_zero, zero_mul, add_zero]
  simp [mul_ite, Finset.sum_ite_eq]

/-- `⟨X_i, ḟ⟩ₓ = ∑_j (Ṡ_ij V_j + S_ij V̇_j)`. -/
lemma partialX_tangentVec (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X)
    (hgX : ∀ i j, ⟪X i, X' j⟫ = 0) (i : ι) :
    partialX τ (X i) (tangentVec τ X S V X' S' V') =
      ∑ j, S' i j • V j + ∑ j, S i j • V' j := by
  have hXi : ∀ i k, ⟪X i, X k⟫ = if i = k then (1 : ℝ) else 0 := fun i k =>
    orthonormal_iff_ite.mp hX i k
  simp only [tangentVec, map_sum, map_add, map_smul, partialX_tensor ht, hgX, hXi, zero_smul,
    smul_zero, Finset.sum_add_distrib, smul_ite, ite_smul, one_smul]
  simp [Finset.sum_ite_eq]

/-- `⟨V_j, ḟ⟩ᵥ = ∑_i (Ṡ_ij X_i + S_ij Ẋ_i)`. -/
lemma partialV_tangentVec (ht : IsTensorPairing τ) (hV : Orthonormal ℝ V)
    (hgV : ∀ i j, ⟪V i, V' j⟫ = 0) (j : ι) :
    partialV τ (V j) (tangentVec τ X S V X' S' V') =
      ∑ i, S' i j • X i + ∑ i, S i j • X' i := by
  have hVi : ∀ i k, ⟪V i, V k⟫ = if i = k then (1 : ℝ) else 0 := fun i k =>
    orthonormal_iff_ite.mp hV i k
  simp only [tangentVec, map_sum, map_add, map_smul, partialV_tensor ht, hgV, hVi, zero_smul,
    smul_zero, Finset.sum_add_distrib, smul_ite, ite_smul, one_smul]
  simp [Finset.sum_ite_eq]

/-- **(2.4)** (arXiv 1801.01103): `∑_j S_ij V̇_j = ⟨X_i, ḟ⟩ₓ - ∑_j Ṡ_ij V_j`. -/
theorem eq_2_4 (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X) (hgX : ∀ i j, ⟪X i, X' j⟫ = 0)
    (i : ι) :
    ∑ j, S i j • V' j =
      partialX τ (X i) (tangentVec τ X S V X' S' V') - ∑ j, S' i j • V j := by
  rw [partialX_tangentVec ht hX hgX i, add_sub_cancel_left]

/-- **(2.5)** (arXiv 1801.01103): `∑_i S_ij Ẋ_i = ⟨V_j, ḟ⟩ᵥ - ∑_i X_i Ṡ_ij`. -/
theorem eq_2_5 (ht : IsTensorPairing τ) (hV : Orthonormal ℝ V) (hgV : ∀ i j, ⟪V i, V' j⟫ = 0)
    (j : ι) :
    ∑ i, S i j • X' i =
      partialV τ (V j) (tangentVec τ X S V X' S' V') - ∑ i, S' i j • X i := by
  rw [partialV_tangentVec ht hV hgV j, add_sub_cancel_left]

/-- Solving `∑_j S_ij w_j = u_i` for invertible `S`. -/
private lemma solve_left {E : Type*} [AddCommGroup E] [Module ℝ E] {T : Matrix ι ι ℝ}
    (hT : T * S = 1) {w u : ι → E} (h : ∀ i, ∑ j, S i j • w j = u i) (l : ι) :
    w l = ∑ i, T l i • u i := by
  simp only [← h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have : ∀ j, ∑ i, T l i * S i j = (1 : Matrix ι ι ℝ) l j := fun j => by
    rw [← hT, Matrix.mul_apply]
  simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

/-- Solving `∑_i S_ij w_i = u_j` for invertible `S`. -/
private lemma solve_right {E : Type*} [AddCommGroup E] [Module ℝ E] {T : Matrix ι ι ℝ}
    (hT : S * T = 1) {w u : ι → E} (h : ∀ j, ∑ i, S i j • w i = u j) (l : ι) :
    w l = ∑ j, T j l • u j := by
  have h1 : ∀ i, ∑ j, S i j * T j l = (1 : Matrix ι ι ℝ) i l := fun i => by
    rw [← hT, Matrix.mul_apply]
  calc w l = ∑ i, (∑ j, S i j * T j l) • w i := by
        simp only [h1, Matrix.one_apply, ite_smul, one_smul, zero_smul]
        simp
    _ = ∑ j, T j l • ∑ i, S i j • w i := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    _ = ∑ j, T j l • u j := by simp only [h]

/-- **Sec. 2, uniqueness** (arXiv 1801.01103): "the `X_i` and `V_j` are uniquely defined if the
matrix `S` is invertible".  Two gauged triples `(Ẋ, Ṡ, V̇)` that give the same `ḟ` are equal. -/
theorem factorDeriv_unique (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X) (hV : Orthonormal ℝ V)
    (hS : IsUnit S) {X₂ : ι → Hx} {V₂ : ι → Hv} {S₂ : Matrix ι ι ℝ}
    (hgX : ∀ i j, ⟪X i, X' j⟫ = 0) (hgV : ∀ i j, ⟪V i, V' j⟫ = 0)
    (hgX₂ : ∀ i j, ⟪X i, X₂ j⟫ = 0) (hgV₂ : ∀ i j, ⟪V i, V₂ j⟫ = 0)
    (h : tangentVec τ X S V X' S' V' = tangentVec τ X S V X₂ S₂ V₂) :
    S' = S₂ ∧ X' = X₂ ∧ V' = V₂ := by
  obtain ⟨T, hT1, hT2⟩ : ∃ T : Matrix ι ι ℝ, T * S = 1 ∧ S * T = 1 := by
    obtain ⟨u, rfl⟩ := hS
    exact ⟨(↑u⁻¹ : Matrix ι ι ℝ), u.inv_mul, u.mul_inv⟩
  have hS' : S' = S₂ := by
    ext i j
    rw [coreDeriv_eq (S := S) (S' := S') ht hX hV hgX hgV i j, h,
      ← coreDeriv_eq (S := S) (S' := S₂) ht hX hV hgX₂ hgV₂ i j]
  subst hS'
  refine ⟨rfl, funext fun l => ?_, funext fun l => ?_⟩
  · rw [solve_right hT2 (w := X') (fun j => eq_2_5 (X := X) (S := S) (S' := S') ht hV hgV j) l,
      solve_right hT2 (w := X₂) (fun j => eq_2_5 (X := X) (S := S) (S' := S') ht hV hgV₂ j) l, h]
  · rw [solve_left hT1 (w := V') (fun i => eq_2_4 (V := V) (S := S) (S' := S') ht hX hgX i) l,
      solve_left hT1 (w := V₂) (fun i => eq_2_4 (V := V) (S := S) (S' := S') ht hX hgX₂ i) l, h]

end Gauge

section Projectors

variable {X : ι → Hx} {V : ι → Hv}

/-- `⟨X_k, P_X̄ g⟩ₓ = ⟨X_k, g⟩ₓ`. -/
lemma partialX_projX (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X) (k : ι) (g : H) :
    partialX τ (X k) (projX τ X g) = partialX τ (X k) g := by
  classical
  have hXi := orthonormal_iff_ite.mp hX
  simp only [projX_apply, map_sum, partialX_tensor ht, hXi]
  simp [ite_smul, Finset.sum_ite_eq]

/-- `⟨V_k, P_V̄ g⟩ᵥ = ⟨V_k, g⟩ᵥ`. -/
lemma partialV_projV (ht : IsTensorPairing τ) (hV : Orthonormal ℝ V) (k : ι) (g : H) :
    partialV τ (V k) (projV τ V g) = partialV τ (V k) g := by
  classical
  have hVi := orthonormal_iff_ite.mp hV
  simp only [projV_apply, map_sum, partialV_tensor ht, hVi]
  simp [ite_smul, Finset.sum_ite_eq]

/-- `P_X̄` fixes `X_i ⊗ b`. -/
lemma projX_tensor (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X) (i : ι) (b : Hv) :
    projX τ X (τ (X i) b) = τ (X i) b := by
  classical
  have hXi := orthonormal_iff_ite.mp hX
  rw [projX_apply, Finset.sum_eq_single i]
  · simp [partialX_tensor ht, hX.1 i]
  · intro k _ hk
    simp [partialX_tensor ht, hXi, hk]
  · simp

/-- `P_V̄` fixes `a ⊗ V_j`. -/
lemma projV_tensor (ht : IsTensorPairing τ) (hV : Orthonormal ℝ V) (j : ι) (a : Hx) :
    projV τ V (τ a (V j)) = τ a (V j) := by
  classical
  have hVi := orthonormal_iff_ite.mp hV
  rw [projV_apply, Finset.sum_eq_single j]
  · simp [partialV_tensor ht, hV.1 j]
  · intro k _ hk
    simp [partialV_tensor ht, hVi, hk]
  · simp

/-- **Sec. 2** (arXiv 1801.01103): `P_X̄` is an orthogonal projector. -/
theorem isOrthProj_projX (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X) :
    IsOrthProj (projX τ X) where
  idem g := by
    rw [projX_apply (g := projX τ X g)]
    simp only [partialX_projX ht hX]
    rw [← projX_apply]
  symm g h := by
    simp only [projX_apply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, ← inner_partialX, real_inner_comm, ← inner_partialX, real_inner_comm]

/-- **Sec. 2** (arXiv 1801.01103): `P_V̄` is an orthogonal projector. -/
theorem isOrthProj_projV (ht : IsTensorPairing τ) (hV : Orthonormal ℝ V) :
    IsOrthProj (projV τ V) where
  idem g := by
    rw [projV_apply (g := projV τ V g)]
    simp only [partialV_projV ht hV]
    rw [← projV_apply]
  symm g h := by
    simp only [projV_apply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, ← inner_partialV, real_inner_comm, ← inner_partialV, real_inner_comm]

/-- The double sum `P_V̄ P_X̄ g = ∑_ij X_i ⟨X_i V_j, g⟩ₓᵥ V_j` in the formula before (2.7) of
arXiv 1801.01103. -/
theorem projV_projX (ht : IsTensorPairing τ) (g : H) :
    projV τ V (projX τ X g) = ∑ i, ∑ j, ⟪τ (X i) (V j), g⟫ • τ (X i) (V j) := by
  have h1 : ∀ i j, partialV τ (V j) (τ (X i) (partialX τ (X i) g)) =
      ⟪τ (X i) (V j), g⟫ • X i := fun i j => by
    rw [partialV_tensor ht, real_inner_comm, inner_partialX, real_inner_comm]
  simp only [projV_apply, projX_apply, map_sum, h1, map_smul, _root_.smul_apply]

/-- The same double sum as `projV_projX`, in the other order (arXiv 1801.01103, Sec. 2). -/
theorem projX_projV (ht : IsTensorPairing τ) (g : H) :
    projX τ X (projV τ V g) = ∑ i, ∑ j, ⟪τ (X i) (V j), g⟫ • τ (X i) (V j) := by
  have h1 : ∀ i j, partialX τ (X i) (τ (partialV τ (V j) g) (V j)) =
      ⟪τ (X i) (V j), g⟫ • V j := fun i j => by
    rw [partialX_tensor ht, real_inner_comm, inner_partialV, real_inner_comm]
  simp only [projV_apply, projX_apply, map_sum, h1, map_smul]
  exact Finset.sum_comm

/-- **Sec. 2** (arXiv 1801.01103): `P_X̄` and `P_V̄` commute, since one acts on `x` and the other
on `v`. -/
theorem projX_projV_comm (ht : IsTensorPairing τ) (g : H) :
    projV τ V (projX τ X g) = projX τ X (projV τ V g) := by
  rw [projV_projX ht, projX_projV ht]

/-- The projector `P(f)` of (2.7), `P(f) g = P_V̄ g - P_V̄ P_X̄ g + P_X̄ g`, in the library's
notation `LeanDLRA.tangent L R = L + R - L R`.  It depends on `f` only through `span{X_i}` and
`span{V_j}`. -/
noncomputable def tangentP (τ : Hx →L[ℝ] Hv →L[ℝ] H) (X : ι → Hx) (V : ι → Hv) : H →L[ℝ] H :=
  tangent (projV τ V) (projX τ X)

/-- **(2.7)** (arXiv 1801.01103): `P(f) g = P_V̄ g - P_V̄ P_X̄ g + P_X̄ g`, and in terms of the
partial inner products,
`P(f) g = ∑_j ⟨V_j, g⟩ᵥ V_j - ∑_ij X_i ⟨X_i V_j, g⟩ₓᵥ V_j + ∑_i X_i ⟨X_i, g⟩ₓ`. -/
theorem tangentP_apply (ht : IsTensorPairing τ) (g : H) :
    tangentP τ X V g = projV τ V g - projV τ V (projX τ X g) + projX τ X g ∧
    tangentP τ X V g = ∑ j, τ (partialV τ (V j) g) (V j) -
      ∑ i, ∑ j, ⟪τ (X i) (V j), g⟫ • τ (X i) (V j) + ∑ i, τ (X i) (partialX τ (X i) g) := by
  have h : tangentP τ X V g = projV τ V g - projV τ V (projX τ X g) + projX τ X g := by
    simp only [tangentP, tangent_apply]
    abel
  refine ⟨h, ?_⟩
  rw [h, projV_projX ht, projV_apply, projX_apply]

/-- **(2.7)** (arXiv 1801.01103): `P(f)` is an orthogonal projector. -/
theorem isOrthProj_tangentP (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X)
    (hV : Orthonormal ℝ V) : IsOrthProj (tangentP τ X V) :=
  (isOrthProj_projV ht hV).tangent (isOrthProj_projX ht hX) (projX_projV_comm ht)

/-- `g` is in the tangent space `T_f M` at `f = ∑ X_i S_ij V_j`, as defined in Sec. 2: it has the
form (2.2) with gauged `Ẋ_i`, `V̇_j`. -/
def IsTangent (τ : Hx →L[ℝ] Hv →L[ℝ] H) (X : ι → Hx) (S : Matrix ι ι ℝ) (V : ι → Hv) (g : H) :
    Prop :=
  ∃ (X' : ι → Hx) (S' : Matrix ι ι ℝ) (V' : ι → Hv),
    (∀ i j, ⟪X i, X' j⟫ = 0) ∧ (∀ i j, ⟪V i, V' j⟫ = 0) ∧ g = tangentVec τ X S V X' S' V'

/-- **(2.6), (2.7)** (arXiv 1801.01103): for `f = ∑ X_i S_ij V_j ∈ M` (orthonormal factors,
invertible `S`) the operator `P(f)` of (2.7) has range exactly the tangent space `T_f M`; together
with `isOrthProj_tangentP` it is "the orthogonal projector onto the tangent space".  Its definition
does not involve `S`, so `T_f M` depends only on the spans of the factors. -/
theorem isTangent_iff (ht : IsTensorPairing τ) (hX : Orthonormal ℝ X) (hV : Orthonormal ℝ V)
    {S : Matrix ι ι ℝ} (hS : IsUnit S) (g : H) :
    IsTangent τ X S V g ↔ tangentP τ X V g = g := by
  classical
  have hXi := orthonormal_iff_ite.mp hX
  have hVi := orthonormal_iff_ite.mp hV
  have hP := isOrthProj_tangentP ht hX hV
  constructor
  · rintro ⟨X', S', V', hgX, hgV, rfl⟩
    have hA : ∀ i j, tangentP τ X V (τ (X i) (V j)) = τ (X i) (V j) := fun i j => by
      have h1 := projX_tensor ht hX i (V j)
      have h2 := projV_tensor ht hV j (X i)
      simp only [tangentP, tangent_apply, h1, h2]
      abel
    have hB : ∀ i j, tangentP τ X V (τ (X' i) (V j)) = τ (X' i) (V j) := fun i j => by
      have h1 : projX τ X (τ (X' i) (V j)) = 0 := by
        simp [projX_apply, partialX_tensor ht, hgX]
      have h2 := projV_tensor ht hV j (X' i)
      simp only [tangentP, tangent_apply, h1, h2, map_zero]
      abel
    have hC : ∀ i j, tangentP τ X V (τ (X i) (V' j)) = τ (X i) (V' j) := fun i j => by
      have h1 := projX_tensor ht hX i (V' j)
      have h2 : projV τ V (τ (X i) (V' j)) = 0 := by
        simp [projV_apply, partialV_tensor ht, hgV]
      simp only [tangentP, tangent_apply, h1, h2]
      abel
    simp only [tangentVec, map_sum, map_add, map_smul, hA, hB, hC]
  · intro hg
    obtain ⟨T, hT1, hT2⟩ : ∃ T : Matrix ι ι ℝ, T * S = 1 ∧ S * T = 1 := by
      obtain ⟨u, rfl⟩ := hS
      exact ⟨(↑u⁻¹ : Matrix ι ι ℝ), u.inv_mul, u.mul_inv⟩
    set S' : Matrix ι ι ℝ := Matrix.of fun i j => ⟪τ (X i) (V j), g⟫ with hS'
    set U : ι → Hv := fun i => partialX τ (X i) g - ∑ j, S' i j • V j with hU
    set W : ι → Hx := fun j => partialV τ (V j) g - ∑ i, S' i j • X i with hW
    set V' : ι → Hv := fun l => ∑ i, T l i • U i with hV'
    set X' : ι → Hx := fun l => ∑ j, T j l • W j with hX'
    have hU0 : ∀ m i, ⟪V m, U i⟫ = 0 := fun m i => by
      simp only [hU, inner_sub_right, inner_sum, real_inner_smul_right, hVi, hS', Matrix.of_apply]
      rw [real_inner_comm, inner_partialX]
      simp [mul_ite, Finset.sum_ite_eq, real_inner_comm]
    have hW0 : ∀ m j, ⟪X m, W j⟫ = 0 := fun m j => by
      simp only [hW, inner_sub_right, inner_sum, real_inner_smul_right, hXi, hS', Matrix.of_apply]
      rw [real_inner_comm, inner_partialV]
      simp [mul_ite, Finset.sum_ite_eq, real_inner_comm]
    have hSV : ∀ i, ∑ j, S i j • V' j = U i := fun i => by
      simp only [hV', Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      have : ∀ m, ∑ j, S i j * T j m = (1 : Matrix ι ι ℝ) i m := fun m => by
        rw [← hT2, Matrix.mul_apply]
      simp [this, Matrix.one_apply, ite_smul]
    have hSX : ∀ j, ∑ i, S i j • X' i = W j := fun j => by
      simp only [hX', Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      have : ∀ m, ∑ i, S i j * T m i = (1 : Matrix ι ι ℝ) m j := fun m => by
        rw [← hT1, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      simp [this, Matrix.one_apply, ite_smul]
    refine ⟨X', S', V', fun i j => ?_, fun i j => ?_, ?_⟩
    · simp [hX', inner_sum, real_inner_smul_right, hW0]
    · simp [hV', inner_sum, real_inner_smul_right, hU0]
    · have hsum1 : ∑ i, ∑ j, S i j • τ (X i) (V' j) =
          projX τ X g - ∑ i, ∑ j, S' i j • τ (X i) (V j) := by
        rw [projX_apply, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := congrArg (τ (X i)) (hSV i)
        simp only [map_sum, map_smul] at this
        rw [this, hU, map_sub, map_sum]
        simp
      have hsum2 : ∑ i, ∑ j, S i j • τ (X' i) (V j) =
          projV τ V g - ∑ i, ∑ j, S' i j • τ (X i) (V j) := by
        rw [Finset.sum_comm, projV_apply, Finset.sum_comm (f := fun i j => S' i j • τ (X i) (V j)),
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := congrArg (τ.flip (V j)) (hSX j)
        simp only [map_sum, map_smul, ContinuousLinearMap.flip_apply] at this
        rw [this, hW, map_sub, map_sum]
        simp
      have hS'sum : ∑ i, ∑ j, S' i j • τ (X i) (V j) = projV τ V (projX τ X g) := by
        rw [projV_projX ht]
        rfl
      calc g = tangentP τ X V g := hg.symm
        _ = projV τ V g - projV τ V (projX τ X g) + projX τ X g := (tangentP_apply ht g).1
        _ = _ := ?_
      simp only [tangentVec, Finset.sum_add_distrib]
      rw [hsum1, hsum2, hS'sum]
      abel

end Projectors

/-! The substeps fix the other factor. -/

section Fixed

variable {K K' : ι → Hx} {V V' : ι → Hv}

/-- **(2.12) ⇒ `V_j` fixed** (arXiv 1801.01103): "the solution of (2.12) is given by
`V_j(t, v) = V_j⁰(v)`".  Suppose that `f = ∑_j K_j V_j` has orthonormal `V_j`, independent `K_j`,
the gauge `⟨V_i, V̇_j⟩ᵥ = 0`, and that its derivative `∑_j (K̇_j V_j + K_j V̇_j)` equals `P_V̄ g`
for some `g`, as in (2.8).  Then `V̇_j = 0` and `K̇_j = ⟨V_j, g⟩ᵥ`. -/
theorem kStep_factor_fixed (ht : IsTensorPairing τ) (hV : Orthonormal ℝ V)
    (hgV : ∀ i j, ⟪V i, V' j⟫ = 0) (hK : LinearIndependent ℝ K) {g : H}
    (h : ∑ j, (τ (K' j) (V j) + τ (K j) (V' j)) = projV τ V g) :
    V' = 0 ∧ ∀ j, K' j = partialV τ (V j) g := by
  classical
  have hVi := orthonormal_iff_ite.mp hV
  have hK' : ∀ i, K' i = partialV τ (V i) g := fun i => by
    have := congrArg (partialV τ (V i)) h
    rw [partialV_projV ht hV] at this
    rw [← this]
    simp only [map_sum, map_add, partialV_tensor ht, hVi, hgV]
    simp [ite_smul, Finset.sum_ite_eq]
  refine ⟨?_, hK'⟩
  have h0 : ∑ j, τ (K j) (V' j) = 0 := by
    have h1 : ∑ j, τ (K' j) (V j) = projV τ V g := by
      rw [projV_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [hK' j]
    rw [Finset.sum_add_distrib, h1] at h
    simpa using h
  funext j
  refine ext_inner_right ℝ fun φ => ?_
  have h2 := congrArg (partialV τ φ) h0
  simp only [map_sum, partialV_tensor ht, map_zero] at h2
  have h3 := Fintype.linearIndependent_iff.mp hK _ h2 j
  simpa [real_inner_comm] using h3

/-- **(2.10) ⇒ `X_i` fixed** (arXiv 1801.01103): "the `X_i` remain constant during that step".  If
`f = ∑_i X_i L_i` has orthonormal `X_i`, independent `L_i`, the gauge `⟨X_i, Ẋ_j⟩ₓ = 0`, and its
derivative equals `P_X̄ g`, then `Ẋ_i = 0` and `L̇_i = ⟨X_i, g⟩ₓ`. -/
theorem lStep_factor_fixed {X X' : ι → Hx} {L L' : ι → Hv} (ht : IsTensorPairing τ)
    (hX : Orthonormal ℝ X) (hgX : ∀ i j, ⟪X i, X' j⟫ = 0) (hL : LinearIndependent ℝ L) {g : H}
    (h : ∑ i, (τ (X' i) (L i) + τ (X i) (L' i)) = projX τ X g) :
    X' = 0 ∧ ∀ i, L' i = partialX τ (X i) g := by
  classical
  have hXi := orthonormal_iff_ite.mp hX
  have hL' : ∀ i, L' i = partialX τ (X i) g := fun i => by
    have := congrArg (partialX τ (X i)) h
    rw [partialX_projX ht hX] at this
    rw [← this]
    simp only [map_sum, map_add, partialX_tensor ht, hXi, hgX]
    simp [ite_smul, Finset.sum_ite_eq]
  refine ⟨?_, hL'⟩
  have h0 : ∑ i, τ (X' i) (L i) = 0 := by
    have h1 : ∑ i, τ (X i) (L' i) = projX τ X g := by
      rw [projX_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hL' i]
    rw [Finset.sum_add_distrib, h1] at h
    simpa using h
  funext i
  refine ext_inner_right ℝ fun φ => ?_
  have h2 := congrArg (partialX τ φ) h0
  simp only [map_sum, partialX_tensor ht, map_zero] at h2
  have h3 := Fintype.linearIndependent_iff.mp hL _ h2 i
  simpa [real_inner_comm] using h3

/-- **(2.9) ⇒ both factors fixed** (arXiv 1801.01103): "both `V_j⁰` and `X_i¹` are unchanged and
only `S_ij` is updated".  If `f = ∑ X_i S_ij V_j` is gauged, `S` is invertible and
`ḟ = c P_V̄ P_X̄ g`, then `Ẋ_i = 0`, `V̇_j = 0` and `Ṡ_ij = c ⟨X_i V_j, g⟩ₓᵥ`. -/
theorem sStep_factors_fixed {X X' : ι → Hx} {S S' : Matrix ι ι ℝ} (ht : IsTensorPairing τ)
    (hX : Orthonormal ℝ X) (hV : Orthonormal ℝ V) (hS : IsUnit S)
    (hgX : ∀ i j, ⟪X i, X' j⟫ = 0) (hgV : ∀ i j, ⟪V i, V' j⟫ = 0) {g : H} {c : ℝ}
    (h : tangentVec τ X S V X' S' V' = c • projV τ V (projX τ X g)) :
    X' = 0 ∧ V' = 0 ∧ S' = Matrix.of fun i j => c * ⟪τ (X i) (V j), g⟫ := by
  have h' : tangentVec τ X S V X' S' V' = tangentVec τ X S V 0
      (Matrix.of fun i j => c * ⟪τ (X i) (V j), g⟫) 0 := by
    rw [h, projV_projX ht]
    simp [tangentVec, Finset.smul_sum, smul_smul]
  obtain ⟨h1, h2, h3⟩ := factorDeriv_unique ht hX hV hS hgX hgV (fun _ _ => by simp)
    (fun _ _ => by simp) h'
  exact ⟨h2, h3, h1⟩

end Fixed

end Tensor

/-! ### The model: `L²(Ω_x) ⊗ L²(Ω_v) ⊂ L²(Ω_x × Ω_v)` -/

section L2

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- A product of `L²` functions is `L²` on the product space. -/
lemma memLp_mul_prod [SFinite μ] [SFinite ν] {u : α → ℝ} {w : β → ℝ} (hu : MemLp u 2 μ)
    (hw : MemLp w 2 ν) : MemLp (fun p : α × β => u p.1 * w p.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × β => u p.1 * w p.2) (μ.prod ν) :=
    hu.aestronglyMeasurable.comp_fst.mul hw.aestronglyMeasurable.comp_snd
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have h := hu.integrable_sq.mul_prod hw.integrable_sq
  exact h.congr (ae_of_all _ fun p => by ring)

variable [SFinite μ] [SFinite ν]

/-- The function `(x, v) ↦ a(x) b(v)` as an element of `L²(μ × ν)`. -/
noncomputable def tensL2Fun (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (memLp_mul_prod (Lp.memLp a) (Lp.memLp b)).toLp _

lemma tensL2Fun_coeFn (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ν) :
    tensL2Fun a b =ᵐ[μ.prod ν] fun p => a p.1 * b p.2 :=
  MemLp.coeFn_toLp _

/-- `⟨a ⊗ b, c ⊗ d⟩ = ⟨a, c⟩ ⟨b, d⟩`, by Fubini. -/
lemma inner_tensL2Fun (a c : Lp ℝ 2 μ) (b d : Lp ℝ 2 ν) :
    ⟪tensL2Fun a b, tensL2Fun c d⟫ = ⟪a, c⟫ * ⟪b, d⟫ := by
  simp only [L2.inner_def]
  rw [← integral_prod_mul (μ := μ) (ν := ν)]
  refine integral_congr_ae ?_
  filter_upwards [tensL2Fun_coeFn a b, tensL2Fun_coeFn c d] with p h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The tensor pairing of `L²(μ)` and `L²(ν)` in `L²(μ × ν)`. -/
noncomputable def tensL2 (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 (μ.prod ν) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ tensL2Fun
      (fun a a' b => by
        rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
        simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
          inner_tensL2Fun]
        ring)
      (fun c a b => by
        rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          inner_tensL2Fun]
        ring)
      (fun a b b' => by
        rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
        simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
          inner_tensL2Fun]
        ring)
      (fun c a b => by
        rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          inner_tensL2Fun]
        ring))
    1 fun a b => by
      have h : ‖tensL2Fun a b‖ ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, inner_tensL2Fun, real_inner_self_eq_norm_sq,
          real_inner_self_eq_norm_sq]
        ring
      have h' : ‖tensL2Fun a b‖ = ‖a‖ * ‖b‖ :=
        (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h
      simp only [LinearMap.mk₂_apply]
      rw [h', one_mul]

/-- `(a ⊗ b)(x, v) = a(x) b(v)` almost everywhere: the products of (2.1) of arXiv 1801.01103. -/
theorem tensL2_coeFn (a : Lp ℝ 2 μ) (b : Lp ℝ 2 ν) :
    tensL2 μ ν a b =ᵐ[μ.prod ν] fun p => a p.1 * b p.2 :=
  tensL2Fun_coeFn a b

/-- The product functions of `L²(μ)` and `L²(ν)` form a tensor pairing in `L²(μ × ν)`, by Fubini:
the setting of Sec. 2 of arXiv 1801.01103. -/
theorem isTensorPairing_tensL2 : IsTensorPairing (tensL2 μ ν) :=
  ⟨fun a b c d => inner_tensL2Fun a c b d⟩

omit [SFinite μ] [SFinite ν] in
/-- `∫ₛ w = ∫ₛ w'` for all `s` of finite measure, from the weak form against indicators. -/
private lemma ae_eq_of_weak {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ} [SigmaFinite ρ]
    (G : Lp ℝ 2 ρ) (h : γ → ℝ)
    (key : ∀ (s : Set γ) (hs : MeasurableSet s) (hρ : ρ s < ⊤), IntegrableOn h s ρ ∧
      ∫ v in s, h v ∂ρ = ⟪G, indicatorConstLp 2 hs hρ.ne (1 : ℝ)⟫) :
    G =ᵐ[ρ] h := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hρ => integrableOn_Lp_of_measure_ne_top G (by norm_num) hρ.ne)
    (fun s hs hρ => (key s hs hρ).1) fun s hs hρ => ?_
  rw [(key s hs hρ).2, real_inner_comm, L2.inner_indicatorConstLp_one]

/-- **The partial inner product `⟨a, g⟩ₓ` of Sec. 2 (arXiv 1801.01103) is the integral**:
`⟨a, g⟩ₓ(v) = ∫ a(x) g(x, v) dx` for almost every `v`. -/
theorem partialX_coeFn [SigmaFinite ν] (a : Lp ℝ 2 μ) (g : Lp ℝ 2 (μ.prod ν)) :
    partialX (tensL2 μ ν) a g =ᵐ[ν] fun v => ∫ x, a x * g (x, v) ∂μ := by
  refine ae_eq_of_weak _ _ fun s hs hνs => ?_
  set h : β → ℝ := fun v => ∫ x, a x * g (x, v) ∂μ with hh
  set φ : Lp ℝ 2 ν := indicatorConstLp 2 hs hνs.ne (1 : ℝ) with hφ
  have hφc : φ =ᵐ[ν] s.indicator fun _ => (1 : ℝ) := indicatorConstLp_coeFn
  set F : α × β → ℝ := fun p => a p.1 * s.indicator (fun _ => (1 : ℝ)) p.2 * g p with hF
  have hT : tensL2 μ ν a φ =ᵐ[μ.prod ν] fun p => a p.1 * s.indicator (fun _ => (1 : ℝ)) p.2 := by
    filter_upwards [tensL2_coeFn a φ, Measure.quasiMeasurePreserving_snd.ae_eq_comp hφc]
      with p h1 h2
    rw [h1]
    simp only [Function.comp] at h2
    rw [h2]
  have hFint : Integrable F (μ.prod ν) := by
    have h0 : Integrable (fun p => tensL2 μ ν a φ p * g p) (μ.prod ν) :=
      (Lp.memLp _).integrable_mul (Lp.memLp g)
    refine h0.congr ?_
    filter_upwards [hT] with p hp
    rw [hp]
  have hin : ⟪g, tensL2 μ ν a φ⟫ = ∫ p, F p ∂(μ.prod ν) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT] with p hp
    rw [hp]
    simp only [RCLike.inner_apply, conj_trivial, hF]
  have hslice : ∀ v, ∫ x, F (x, v) ∂μ = s.indicator h v := fun v => by
    by_cases hv : v ∈ s <;> simp [hF, hv, hh]
  have hint : Integrable (s.indicator h) ν := by
    have := hFint.integral_prod_right
    simpa only [hslice] using this
  refine ⟨(integrable_indicator_iff hs).1 hint, ?_⟩
  rw [inner_partialX, hin, integral_prod_symm F hFint, ← integral_indicator hs]
  exact integral_congr_ae (ae_of_all _ fun v => (hslice v).symm)

/-- **The partial inner product `⟨b, g⟩ᵥ` of Sec. 2 (arXiv 1801.01103) is the integral**:
`⟨b, g⟩ᵥ(x) = ∫ b(v) g(x, v) dv` for almost every `x`. -/
theorem partialV_coeFn [SigmaFinite μ] (b : Lp ℝ 2 ν) (g : Lp ℝ 2 (μ.prod ν)) :
    partialV (tensL2 μ ν) b g =ᵐ[μ] fun x => ∫ v, b v * g (x, v) ∂ν := by
  refine ae_eq_of_weak _ _ fun s hs hμs => ?_
  set h : α → ℝ := fun x => ∫ v, b v * g (x, v) ∂ν with hh
  set φ : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ) with hφ
  have hφc : φ =ᵐ[μ] s.indicator fun _ => (1 : ℝ) := indicatorConstLp_coeFn
  set F : α × β → ℝ := fun p => s.indicator (fun _ => (1 : ℝ)) p.1 * b p.2 * g p with hF
  have hT : tensL2 μ ν φ b =ᵐ[μ.prod ν] fun p => s.indicator (fun _ => (1 : ℝ)) p.1 * b p.2 := by
    filter_upwards [tensL2_coeFn φ b, Measure.quasiMeasurePreserving_fst.ae_eq_comp hφc]
      with p h1 h2
    rw [h1]
    simp only [Function.comp] at h2
    rw [h2]
  have hFint : Integrable F (μ.prod ν) := by
    have h0 : Integrable (fun p => tensL2 μ ν φ b p * g p) (μ.prod ν) :=
      (Lp.memLp _).integrable_mul (Lp.memLp g)
    refine h0.congr ?_
    filter_upwards [hT] with p hp
    rw [hp]
  have hin : ⟪g, tensL2 μ ν φ b⟫ = ∫ p, F p ∂(μ.prod ν) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT] with p hp
    rw [hp]
    simp only [RCLike.inner_apply, conj_trivial, hF]
  have hslice : ∀ x, ∫ v, F (x, v) ∂ν = s.indicator h x := fun x => by
    by_cases hx : x ∈ s <;> simp [hF, hx, hh]
  have hint : Integrable (s.indicator h) μ := by
    have := hFint.integral_prod_left
    simpa only [hslice] using this
  refine ⟨(integrable_indicator_iff hs).1 hint, ?_⟩
  rw [inner_partialV, hin, integral_prod F hFint, ← integral_indicator hs]
  exact integral_congr_ae (ae_of_all _ fun x => (hslice x).symm)

/-- The almost everywhere value of a finite sum in `L²`. -/
private lemma coeFn_finset_sum {γ κ : Type*} [MeasurableSpace γ] {ρ : Measure γ} (s : Finset κ)
    (f : κ → Lp ℝ 2 ρ) : ⇑(∑ i ∈ s, f i) =ᵐ[ρ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact Lp.coeFn_zero ℝ 2 ρ
  | insert a s ha ih =>
    rw [sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, sum_insert ha]

/-- **`P_V̄` of Sec. 2 (arXiv 1801.01103) as a formula**:
`(P_V̄ g)(x, v) = ∑_j (∫ V_j(w) g(x, w) dw) V_j(v)` almost everywhere, so `projV` is the pointwise
`projVf` used for the substeps. -/
theorem projV_coeFn [SigmaFinite μ] {κ : Type*} [Fintype κ] (V : κ → Lp ℝ 2 ν)
    (g : Lp ℝ 2 (μ.prod ν)) :
    projV (tensL2 μ ν) V g =ᵐ[μ.prod ν]
      fun p => ∑ j, (∫ w, V j w * g (p.1, w) ∂ν) * V j p.2 := by
  classical
  have hj : ∀ j, ∀ᵐ p ∂(μ.prod ν), tensL2 μ ν (partialV (tensL2 μ ν) (V j) g) (V j) p =
      (∫ w, V j w * g (p.1, w) ∂ν) * V j p.2 := fun j => by
    filter_upwards [tensL2_coeFn (partialV (tensL2 μ ν) (V j) g) (V j),
      Measure.quasiMeasurePreserving_fst.ae (partialV_coeFn (V j) g)] with p h1 h2
    rw [h1, h2]
  filter_upwards [coeFn_finset_sum Finset.univ fun j =>
    tensL2 μ ν (partialV (tensL2 μ ν) (V j) g) (V j), ae_all_iff.2 hj] with p hp hq
  rw [projV_apply, hp]
  exact sum_congr rfl fun j _ => hq j

/-- **`P_X̄` of Sec. 2 (arXiv 1801.01103) as a formula**:
`(P_X̄ g)(x, v) = ∑_i (∫ X_i(y) g(y, v) dy) X_i(x)` almost everywhere, so `projX` is the pointwise
`projXf` used for the substeps. -/
theorem projX_coeFn [SigmaFinite ν] {κ : Type*} [Fintype κ] (X : κ → Lp ℝ 2 μ)
    (g : Lp ℝ 2 (μ.prod ν)) :
    projX (tensL2 μ ν) X g =ᵐ[μ.prod ν]
      fun p => ∑ i, (∫ y, X i y * g (y, p.2) ∂μ) * X i p.1 := by
  classical
  have hj : ∀ i, ∀ᵐ p ∂(μ.prod ν), tensL2 μ ν (X i) (partialX (tensL2 μ ν) (X i) g) p =
      (∫ y, X i y * g (y, p.2) ∂μ) * X i p.1 := fun i => by
    filter_upwards [tensL2_coeFn (X i) (partialX (tensL2 μ ν) (X i) g),
      Measure.quasiMeasurePreserving_snd.ae (partialX_coeFn (X i) g)] with p h1 h2
    rw [h1, h2, mul_comm]
  filter_upwards [coeFn_finset_sum Finset.univ fun i =>
    tensL2 μ ν (X i) (partialX (tensL2 μ ν) (X i) g), ae_all_iff.2 hj] with p hp hq
  rw [projX_apply, hp]
  exact sum_congr rfl fun i _ => hq i

/-- **(2.2)–(2.5) and the uniqueness of Sec. 2 in `L²(Ω_x) ⊗ L²(Ω_v) ⊂ L²(Ω)`** (arXiv 1801.01103).
Let `X_i ∈ L²(μ)`, `V_j ∈ L²(ν)`, `S_ij` be differentiable paths with `X_i`, `V_j` orthonormal at
time `t` and with the gauge conditions `⟨X_i, Ẋ_j⟩ₓ = ⟨V_i, V̇_j⟩ᵥ = 0`.  Then `f = ∑ X_i S_ij V_j`
has the derivative (2.2) in `L²(μ × ν)`, and (2.3), (2.4), (2.5) hold.  `μ`, `ν` are arbitrary
σ-finite measures, which covers any `Ω_x`, `Ω_v` and dimension `d`. -/
theorem l2_gauge_equations [SigmaFinite μ] [SigmaFinite ν] {ι : Type*} [Fintype ι]
    {X : ℝ → ι → Lp ℝ 2 μ} {V : ℝ → ι → Lp ℝ 2 ν} {S : ℝ → Matrix ι ι ℝ} {t : ℝ}
    {X' : ι → Lp ℝ 2 μ} {V' : ι → Lp ℝ 2 ν} {S' : Matrix ι ι ℝ}
    (hXd : ∀ i, HasDerivAt (fun s => X s i) (X' i) t)
    (hVd : ∀ j, HasDerivAt (fun s => V s j) (V' j) t)
    (hSd : ∀ i j, HasDerivAt (fun s => S s i j) (S' i j) t)
    (hX : Orthonormal ℝ (X t)) (hV : Orthonormal ℝ (V t))
    (hgX : ∀ i j, ⟪X t i, X' j⟫ = 0) (hgV : ∀ i j, ⟪V t i, V' j⟫ = 0) :
    ∃ f' : Lp ℝ 2 (μ.prod ν),
      HasDerivAt (fun s => ansatz (tensL2 μ ν) (X s) (S s) (V s)) f' t ∧
      f' = tangentVec (tensL2 μ ν) (X t) (S t) (V t) X' S' V' ∧
      (∀ i j, S' i j = ⟪tensL2 μ ν (X t i) (V t j), f'⟫) ∧
      (∀ i, ∑ j, S t i j • V' j = partialX (tensL2 μ ν) (X t i) f' - ∑ j, S' i j • V t j) ∧
      (∀ j, ∑ i, S t i j • X' i = partialV (tensL2 μ ν) (V t j) f' - ∑ i, S' i j • X t i) := by
  classical
  have ht := isTensorPairing_tensL2 (μ := μ) (ν := ν)
  exact ⟨_, hasDerivAt_ansatz hXd hVd hSd, rfl, coreDeriv_eq ht hX hV hgX hgV,
    eq_2_4 ht hX hgX, eq_2_5 ht hV hgV⟩

/-- **Uniqueness of the factor derivatives and the tangent space in `L²`** (arXiv 1801.01103,
Sec. 2).  For `f = ∑ X_i S_ij V_j` with orthonormal `X_i ∈ L²(μ)`, `V_j ∈ L²(ν)` and invertible `S`:
gauged `(Ẋ, Ṡ, V̇)` are determined by `ḟ`, the operator `P(f)` of (2.7) is an orthogonal projector
on `L²(μ × ν)`, and its range is the tangent space `T_f M`. -/
theorem l2_tangent_space [SigmaFinite μ] [SigmaFinite ν] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Lp ℝ 2 μ} {V : ι → Lp ℝ 2 ν} {S : Matrix ι ι ℝ} (hX : Orthonormal ℝ X)
    (hV : Orthonormal ℝ V) (hS : IsUnit S) :
    (∀ (X' X₂ : ι → Lp ℝ 2 μ) (V' V₂ : ι → Lp ℝ 2 ν) (S' S₂ : Matrix ι ι ℝ),
      (∀ i j, ⟪X i, X' j⟫ = 0) → (∀ i j, ⟪V i, V' j⟫ = 0) →
      (∀ i j, ⟪X i, X₂ j⟫ = 0) → (∀ i j, ⟪V i, V₂ j⟫ = 0) →
      tangentVec (tensL2 μ ν) X S V X' S' V' = tangentVec (tensL2 μ ν) X S V X₂ S₂ V₂ →
      S' = S₂ ∧ X' = X₂ ∧ V' = V₂) ∧
    IsOrthProj (tangentP (tensL2 μ ν) X V) ∧
    ∀ g, IsTangent (tensL2 μ ν) X S V g ↔ tangentP (tensL2 μ ν) X V g = g := by
  have ht := isTensorPairing_tensL2 (μ := μ) (ν := ν)
  exact ⟨fun _ _ _ _ _ _ h1 h2 h3 h4 h => factorDeriv_unique ht hX hV hS h1 h2 h3 h4 h,
    isOrthProj_tangentP ht hX hV, isTangent_iff ht hX hV hS⟩

end L2

/-! ### Eqs. (2.8)–(2.15): the three substeps as lower-dimensional equations -/

section Vlasov

/-- Physical space and velocity space `ℝ^d`. -/
abbrev PS (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d r : ℕ} {μ ν : Measure (PS d)}

/-- The partial derivative `∂_a g`. -/
noncomputable def pd (a : Fin d) (g : PS d → ℝ) (x : PS d) : ℝ :=
  fderiv ℝ g x (EuclideanSpace.single a 1)

/-- The Vlasov operator `F(f) = -v·∇ₓf + E·∇ᵥf` for a given field `E`, the negative of the
`v·∇ₓf - E·∇ᵥf` of (2.6). -/
noncomputable def vlasovF (E : PS d → PS d) (f : PS d → PS d → ℝ) (x v : PS d) : ℝ :=
  -fderiv ℝ (fun y => f y v) x v + fderiv ℝ (fun w => f x w) v (E x)

/-- A separated function `∑_j A_j(x) B_j(v)`: this is `f = ∑ K_j V_j` and `f = ∑ X_k L_k`. -/
def lowRank (A B : Fin r → PS d → ℝ) (x v : PS d) : ℝ := ∑ j, A j x * B j v

/-- `K_l = ∑_k X_k S_kl`, (2.11). -/
def coreK (X : Fin r → PS d → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (l : Fin r) (x : PS d) : ℝ :=
  ∑ k, X k x * S k l

/-- The orthogonal projection `g ↦ ∑_i ⟨X_i, g⟩ X_i` of a function of one variable. -/
noncomputable def proj {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : Fin r → α → ℝ)
    (g : α → ℝ) (x : α) : ℝ :=
  ∑ i, (∫ y, X i y * g y ∂μ) * X i x

/-- Orthonormality in `L²(μ)`. -/
structure IsOrthonormalL2 {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : Fin r → α → ℝ) :
    Prop where
  memLp : ∀ i, MemLp (X i) 2 μ
  inner_eq : ∀ i k, ∫ x, X i x * X k x ∂μ = if i = k then 1 else 0

/-- `∂_a` of a finite combination. -/
lemma pd_sum_mul {A : Fin r → PS d → ℝ} (a : Fin d) (c : Fin r → ℝ) {x : PS d}
    (hA : ∀ j, DifferentiableAt ℝ (A j) x) :
    pd a (fun y => ∑ j, A j y * c j) x = ∑ j, pd a (A j) x * c j := by
  have h : HasFDerivAt (fun y => ∑ j, A j y * c j)
      (∑ j, c j • fderiv ℝ (A j) x) x :=
    HasFDerivAt.fun_sum fun j _ => by
      simpa using (hA j).hasFDerivAt.mul_const (c j)
  simp [pd, h.fderiv, mul_comm]

/-- `w·∇g = ∑_a w_a ∂_a g`. -/
lemma fderiv_apply_eq_sum_pd (g : PS d → ℝ) (x w : PS d) :
    fderiv ℝ g x w = ∑ a, w a * pd a g x := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w]
  simp [pd, map_sum]

/-- The Vlasov operator on a separated function. -/
lemma vlasovF_lowRank (E : PS d → PS d) {A B : Fin r → PS d → ℝ} (x v : PS d)
    (hA : ∀ j, DifferentiableAt ℝ (A j) x) (hB : ∀ j, DifferentiableAt ℝ (B j) v) :
    vlasovF E (lowRank A B) x v =
      ∑ j, (-(∑ a, v a * pd a (A j) x) * B j v + A j x * ∑ b, E x b * pd b (B j) v) := by
  have h1 : HasFDerivAt (fun y => lowRank A B y v) (∑ j, B j v • fderiv ℝ (A j) x) x :=
    HasFDerivAt.fun_sum fun j _ => by
      simpa using (hA j).hasFDerivAt.mul_const (B j v)
  have h2 : HasFDerivAt (fun w => lowRank A B x w) (∑ j, A j x • fderiv ℝ (B j) v) v :=
    HasFDerivAt.fun_sum fun j _ => by
      simpa using (hB j).hasFDerivAt.const_mul (A j x)
  simp only [vlasovF, h1.fderiv, h2.fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, fderiv_apply_eq_sum_pd]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- The charge density `ρ(f)(x) = -∫ f(x, v) dv` of Sec. 2. -/
noncomputable def charge (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (x : PS d) : ℝ :=
  -∫ v, f x v ∂ν

/-- The self-consistent field `E(f) = 𝓔(ρ(f))`, where `𝓔` maps a charge density to its electric
field.  In the paper `𝓔` solves the Poisson problem `-Δφ = ρ + 1`, `E = -∇φ`.  Here `𝓔` is an
arbitrary map, so that every theorem below holds for that `𝓔` in particular: only the fact that
`E(f)` depends on `f` through `ρ(f)` is used. -/
noncomputable def field (𝓔 : (PS d → ℝ) → PS d → PS d) (ν : Measure (PS d))
    (f : PS d → PS d → ℝ) : PS d → PS d :=
  𝓔 (charge ν f)

/-- `P_V̄ g (x, v) = ∑_j ⟨V_j, g(x, ·)⟩ᵥ V_j(v)`, pointwise. -/
noncomputable def projVf (ν : Measure (PS d)) (V : Fin r → PS d → ℝ) (g : PS d → PS d → ℝ)
    (x v : PS d) : ℝ :=
  proj ν V (g x) v

/-- `P_X̄ g (x, v) = ∑_i ⟨X_i, g(·, v)⟩ₓ X_i(x)`, pointwise. -/
noncomputable def projXf (μ : Measure (PS d)) (X : Fin r → PS d → ℝ) (g : PS d → PS d → ℝ)
    (x v : PS d) : ℝ :=
  proj μ X (fun y => g y v) x

/-- The component `c^{1;x_a}` of `c¹_jl = ∫ v V_j V_l dv` in (2.13). -/
noncomputable def c1 (ν : Measure (PS d)) (V : Fin r → PS d → ℝ) (a : Fin d) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun j l => ∫ v, v a * V j v * V l v ∂ν

/-- The component `a` of `c²_jl = ∫ V_j ∇ᵥV_l dv` in (2.13). -/
noncomputable def c2 (ν : Measure (PS d)) (V : Fin r → PS d → ℝ) (a : Fin d) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun j l => ∫ v, V j v * pd a (V l) v ∂ν

/-- The component `a` of `d¹_ik[E] = ∫ X_i E X_k dx` in (2.14). -/
noncomputable def d1 (μ : Measure (PS d)) (X : Fin r → PS d → ℝ) (E : PS d → PS d) (a : Fin d) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i k => ∫ x, X i x * E x a * X k x ∂μ

/-- The component `a` of `d²_ik = ∫ X_i ∇ₓX_k dx` in (2.14). -/
noncomputable def d2 (μ : Measure (PS d)) (X : Fin r → PS d → ℝ) (a : Fin d) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i k => ∫ x, X i x * pd a (X k) x ∂μ

/-- `E(K)`: the field of the charge `ρ = -∑_j K_j ∫ V_j dv` of the K-step. -/
noncomputable def fieldK (𝓔 : (PS d → ℝ) → PS d → PS d) (ν : Measure (PS d))
    (V K : Fin r → PS d → ℝ) : PS d → PS d :=
  𝓔 fun x => -∑ j, K j x * ∫ v, V j v ∂ν

/-- `E(S)`: the field of the charge `ρ = -∑_ij X_i S_ij ∫ V_j dv` of the S-step. -/
noncomputable def fieldS (𝓔 : (PS d → ℝ) → PS d → PS d) (ν : Measure (PS d))
    (X V : Fin r → PS d → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) : PS d → PS d :=
  𝓔 fun x => -∑ i, ∑ j, X i x * S i j * ∫ v, V j v ∂ν

/-- `E(L)`: the field of the charge `ρ = -∑_i X_i ∫ L_i dv` of the L-step. -/
noncomputable def fieldL (𝓔 : (PS d → ℝ) → PS d → PS d) (ν : Measure (PS d))
    (X L : Fin r → PS d → ℝ) : PS d → PS d :=
  𝓔 fun x => -∑ i, X i x * ∫ v, L i v ∂ν

/-- The right-hand side of (2.13):
`-∑_l c¹_jl · ∇ₓK_l(x) + ∑_l c²_jl · E(K)(x) K_l(x)`. -/
noncomputable def kRhs (𝓔 : (PS d → ℝ) → PS d → PS d) (ν : Measure (PS d))
    (V K : Fin r → PS d → ℝ) (j : Fin r) (x : PS d) : ℝ :=
  -∑ l, ∑ a, c1 ν V a j l * pd a (K l) x +
    ∑ l, ∑ a, c2 ν V a j l * fieldK 𝓔 ν V K x a * K l x

/-- The right-hand side of (2.14): `∑_kl (c¹_jl · d²_ik - c²_jl · d¹_ik[E(S)]) S_kl`. -/
noncomputable def sRhs (𝓔 : (PS d → ℝ) → PS d → PS d) (μ ν : Measure (PS d))
    (X V : Fin r → PS d → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (i j : Fin r) : ℝ :=
  ∑ k, ∑ l, (∑ a, c1 ν V a j l * d2 μ X a i k -
    ∑ a, c2 ν V a j l * d1 μ X (fieldS 𝓔 ν X V S) a i k) * S k l

/-- The right-hand side of (2.15):
`∑_k d¹_ik[E(L)] · ∇ᵥL_k(v) - ∑_k (d²_ik · v) L_k(v)`. -/
noncomputable def lRhs (𝓔 : (PS d → ℝ) → PS d → PS d) (μ ν : Measure (PS d))
    (X L : Fin r → PS d → ℝ) (i : Fin r) (v : PS d) : ℝ :=
  ∑ k, ∑ a, d1 μ X (fieldL 𝓔 ν X L) a i k * pd a (L k) v -
    ∑ k, (∑ a, d2 μ X a i k * v a) * L k v

/-- Regularity of the velocity basis: orthonormal, differentiable, and such that the coefficients
`∫ V_j`, `c¹`, `c²` exist. -/
structure IsVelocityBasis (ν : Measure (PS d)) (V : Fin r → PS d → ℝ) : Prop where
  orth : IsOrthonormalL2 ν V
  diff : ∀ j, Differentiable ℝ (V j)
  mass : ∀ j, Integrable (V j) ν
  c1 : ∀ a j l, Integrable (fun v => v a * V j v * V l v) ν
  c2 : ∀ a j l, Integrable (fun v => V j v * pd a (V l) v) ν

/-- Regularity of the space basis: orthonormal, differentiable, and such that the coefficient
`d²` exists. -/
structure IsSpaceBasis (μ : Measure (PS d)) (X : Fin r → PS d → ℝ) : Prop where
  orth : IsOrthonormalL2 μ X
  diff : ∀ k, Differentiable ℝ (X k)
  d2 : ∀ a i k, Integrable (fun x => X i x * pd a (X k) x) μ

/-! Coefficient comparison in an orthonormal system. -/

/-- `⟨V_i, ∑_j c_j V_j⟩ = c_i`. -/
lemma integral_mul_sum_basis {V : Fin r → PS d → ℝ} (hV : IsOrthonormalL2 ν V) (c : Fin r → ℝ)
    (i : Fin r) : ∫ v, V i v * ∑ j, c j * V j v ∂ν = c i := by
  have h : ∀ v, V i v * ∑ j, c j * V j v = ∑ j, (V i v * V j v) * c j := fun v => by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have hint : ∀ j, Integrable (fun v => V i v * V j v) ν := fun j =>
    (hV.memLp i).integrable_mul (hV.memLp j)
  simp only [h]
  rw [integral_finsetSum _ fun j _ => (hint j).mul_const _]
  simp only [integral_mul_const, hV.inner_eq]
  simp

/-- Linear independence of an orthonormal system. -/
lemma coeff_eq_of_sum_eq {V : Fin r → PS d → ℝ} (hV : IsOrthonormalL2 ν V) {a b : Fin r → ℝ}
    (h : ∀ v, ∑ j, a j * V j v = ∑ j, b j * V j v) : a = b := by
  funext i
  rw [← integral_mul_sum_basis hV a i, ← integral_mul_sum_basis hV b i]
  simp only [h]

/-- An equation for `∑_j A_j V_j` in an orthonormal system is the same as the equations for the
coefficients: this is "equating coefficients in the basis expansion". -/
lemma hasDerivAt_coeff_iff {V : Fin r → PS d → ℝ} (hV : IsOrthonormalL2 ν V)
    {A : ℝ → Fin r → ℝ} {R : Fin r → ℝ} {t : ℝ}
    (hA : ∀ j, DifferentiableAt ℝ (fun s => A s j) t) :
    (∀ v, HasDerivAt (fun s => ∑ j, A s j * V j v) (∑ j, R j * V j v) t) ↔
      ∀ j, HasDerivAt (fun s => A s j) (R j) t := by
  constructor
  · intro h
    have h1 : ∀ v, HasDerivAt (fun s => ∑ j, A s j * V j v)
        (∑ j, deriv (fun s => A s j) t * V j v) t := fun v =>
      HasDerivAt.fun_sum fun j _ => (hA j).hasDerivAt.mul_const _
    have h2 := coeff_eq_of_sum_eq hV (a := fun j => deriv (fun s => A s j) t) (b := R)
      fun v => (h1 v).unique (h v)
    intro j
    rw [← congrFun h2 j]
    exact (hA j).hasDerivAt
  · intro h v
    exact HasDerivAt.fun_sum fun j _ => (h j).mul_const _

/-- Linearity of the integral for a double sum. -/
private lemma integral_double_sum {κ κ' : Type*} [Fintype κ] [Fintype κ'] {α : Type*}
    [MeasurableSpace α] {ρ : Measure α} (f : κ → κ' → α → ℝ) (c : κ → κ' → ℝ)
    (hf : ∀ l a, Integrable (f l a) ρ) :
    Integrable (fun v => ∑ l, ∑ a, f l a v * c l a) ρ ∧
      ∫ v, ∑ l, ∑ a, f l a v * c l a ∂ρ = ∑ l, ∑ a, (∫ v, f l a v ∂ρ) * c l a := by
  refine ⟨integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun a _ =>
    (hf l a).mul_const _, ?_⟩
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun a _ => (hf l a).mul_const _]
  refine sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun a _ => (hf l a).mul_const _]
  simp only [integral_mul_const]

/-- **(2.12) ⇒ (2.13), right-hand side** (arXiv 1801.01103): the coefficient of `V_j` in `F(f)` for
`f = ∑_l K_l V_l` and a given field `E`. -/
theorem integral_V_vlasovF {V K : Fin r → PS d → ℝ} (E : PS d → PS d) {x : PS d}
    (hV : IsVelocityBasis ν V) (hK : ∀ l, DifferentiableAt ℝ (K l) x) (j : Fin r) :
    ∫ v, V j v * vlasovF E (lowRank K V) x v ∂ν =
      -∑ l, ∑ a, c1 ν V a j l * pd a (K l) x + ∑ l, ∑ a, c2 ν V a j l * E x a * K l x := by
  have h : ∀ v, V j v * vlasovF E (lowRank K V) x v =
      ∑ l, ∑ a, (V j v * pd a (V l) v) * (E x a * K l x) -
        ∑ l, ∑ a, (v a * V j v * V l v) * pd a (K l) x := fun v => by
    rw [vlasovF_lowRank E x v hK fun l => hV.diff l v, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun l _ => ?_
    simp only [neg_mul, mul_add, mul_neg, Finset.mul_sum, Finset.sum_mul]
    rw [add_comm, sub_eq_add_neg]
    congr 1
    · exact sum_congr rfl fun a _ => by ring
    · congr 1
      exact sum_congr rfl fun a _ => by ring
  have h1 := integral_double_sum (fun l a v => v a * V j v * V l v) (fun l a => pd a (K l) x)
    (fun l a => hV.c1 a j l)
  have h2 := integral_double_sum (fun l a v => V j v * pd a (V l) v) (fun l a => E x a * K l x)
    (fun l a => hV.c2 a j l)
  simp only [h]
  rw [integral_sub h2.1 h1.1, h1.2, h2.2, sub_eq_neg_add]
  simp only [c1, c2, Matrix.of_apply, mul_assoc]

/-- **(2.15), right-hand side** (arXiv 1801.01103): the coefficient of `X_i` in `F(f)` for
`f = ∑_k X_k L_k` and a given field `E`. -/
theorem integral_X_vlasovF {X L : Fin r → PS d → ℝ} (E : PS d → PS d) {v : PS d}
    (hX : IsSpaceBasis μ X) (hL : ∀ k, DifferentiableAt ℝ (L k) v)
    (hd1 : ∀ a i k, Integrable (fun x => X i x * E x a * X k x) μ) (i : Fin r) :
    ∫ x, X i x * vlasovF E (lowRank X L) x v ∂μ =
      ∑ k, ∑ a, d1 μ X E a i k * pd a (L k) v - ∑ k, (∑ a, d2 μ X a i k * v a) * L k v := by
  have h : ∀ x, X i x * vlasovF E (lowRank X L) x v =
      ∑ k, ∑ a, (X i x * E x a * X k x) * pd a (L k) v -
        ∑ k, ∑ a, (X i x * pd a (X k) x) * (v a * L k v) := fun x => by
    rw [vlasovF_lowRank E x v (fun k => hX.diff k x) hL, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [neg_mul, mul_add, mul_neg, Finset.mul_sum, Finset.sum_mul]
    rw [add_comm, sub_eq_add_neg]
    congr 1
    · exact sum_congr rfl fun a _ => by ring
    · congr 1
      exact sum_congr rfl fun a _ => by ring
  have h1 := integral_double_sum (fun k a x => X i x * E x a * X k x) (fun k a => pd a (L k) v)
    (fun k a => hd1 a i k)
  have h2 := integral_double_sum (fun k a x => X i x * pd a (X k) x) (fun k a => v a * L k v)
    (fun k a => hX.d2 a i k)
  simp only [h]
  rw [integral_sub h1.1 h2.1, h1.2, h2.2]
  simp only [d1, d2, Matrix.of_apply, Finset.sum_mul, mul_assoc]

/-- **The field depends only on `K`** (arXiv 1801.01103, Sec. 2): for `f = ∑_j K_j V_j`,
`ρ(f) = -∑_j K_j ∫ V_j dv`, "which explains our notation `E(K)`". -/
theorem field_lowRank_K (𝓔 : (PS d → ℝ) → PS d → PS d) {V K : Fin r → PS d → ℝ}
    (hV : ∀ j, Integrable (V j) ν) : field 𝓔 ν (lowRank K V) = fieldK 𝓔 ν V K := by
  refine congrArg 𝓔 (funext fun x => ?_)
  simp only [charge, lowRank]
  rw [integral_finsetSum _ fun j _ => (hV j).const_mul _]
  simp only [integral_const_mul]

/-- **The field depends only on `L`** (arXiv 1801.01103, Sec. 2): for `f = ∑_i X_i L_i`,
`ρ(f) = -∑_i X_i ∫ L_i dv`. -/
theorem field_lowRank_L (𝓔 : (PS d → ℝ) → PS d → PS d) {X L : Fin r → PS d → ℝ}
    (hL : ∀ i, Integrable (L i) ν) : field 𝓔 ν (lowRank X L) = fieldL 𝓔 ν X L :=
  field_lowRank_K 𝓔 hL

/-- **The field depends only on `S`** (arXiv 1801.01103, Sec. 2): for `f = ∑_ij X_i S_ij V_j`,
`ρ(f) = -∑_ij X_i S_ij ∫ V_j dv`. -/
theorem field_lowRank_S (𝓔 : (PS d → ℝ) → PS d → PS d) {X V : Fin r → PS d → ℝ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hV : ∀ j, Integrable (V j) ν) :
    field 𝓔 ν (lowRank (coreK X S) V) = fieldS 𝓔 ν X V S := by
  rw [field_lowRank_K 𝓔 hV]
  refine congrArg 𝓔 (funext fun x => ?_)
  simp only [coreK, sum_mul]
  rw [sum_comm]

/-- **(2.8) ⇔ (2.13)** (arXiv 1801.01103).  For fixed orthonormal `V_j` and `f = ∑_j K_j V_j`, the
K-step equation `∂ₜf = -P_V̄ (v·∇ₓf - E(f)·∇ᵥf)` holds at time `t` and at every `(x, v)` if and only
if the `r` functions `K_j` satisfy the `r` advection equations (2.13) in `x` alone, with
coefficients that are integrals over `v` and with `E(K)` determined by `K`.

Here `F(f) = -(v·∇ₓf - E·∇ᵥf)` is `vlasovF` of arXiv 1807.02338.  `ν` is an arbitrary measure on
`ℝ^d`, which covers `Ω_v ⊂ ℝ^d`.  Functions on `Ω_x` enter through differentiable functions on
`ℝ^d`.  `IsVelocityBasis` only says that the printed integrals exist. -/
theorem kStep_iff (𝓔 : (PS d → ℝ) → PS d → PS d) {V : Fin r → PS d → ℝ}
    {K : ℝ → Fin r → PS d → ℝ} {t : ℝ} (hV : IsVelocityBasis ν V)
    (hKx : ∀ j, Differentiable ℝ (K t j))
    (hKt : ∀ j x, DifferentiableAt ℝ (fun s => K s j x) t) :
    (∀ x v, HasDerivAt (fun s => lowRank (K s) V x v)
      (projVf ν V (vlasovF (field 𝓔 ν (lowRank (K t) V)) (lowRank (K t) V)) x v) t) ↔
      ∀ j x, HasDerivAt (fun s => K s j x) (kRhs 𝓔 ν V (K t) j x) t := by
  have hR : ∀ x v, projVf ν V (vlasovF (field 𝓔 ν (lowRank (K t) V)) (lowRank (K t) V)) x v =
      ∑ j, kRhs 𝓔 ν V (K t) j x * V j v := fun x v => by
    simp only [projVf, proj]
    refine sum_congr rfl fun j _ => ?_
    rw [integral_V_vlasovF _ hV fun l => hKx l x, field_lowRank_K 𝓔 hV.mass, kRhs]
  simp only [hR]
  constructor
  · intro h j x
    exact (hasDerivAt_coeff_iff hV.orth fun j => hKt j x).1 (h x) j
  · intro h x
    exact (hasDerivAt_coeff_iff hV.orth fun j => hKt j x).2 fun j => h j x

/-- **(2.10) ⇔ (2.15)** (arXiv 1801.01103).  For fixed orthonormal `X_i` and `f = ∑_i X_i L_i`, the
L-step equation `∂ₜf = -P_X̄ (v·∇ₓf - E(f)·∇ᵥf)` holds at time `t` at every `(x, v)` if and only if
the `r` functions `L_i` satisfy the `r` advection equations (2.15) in `v` alone, with `E(L)`
determined by `L`.  `hd1` says that the integrals `d¹_ik[E(L)]` exist. -/
theorem lStep_iff (𝓔 : (PS d → ℝ) → PS d → PS d) {X : Fin r → PS d → ℝ}
    {L : ℝ → Fin r → PS d → ℝ} {t : ℝ} (hX : IsSpaceBasis μ X)
    (hLv : ∀ i, Differentiable ℝ (L t i)) (hLi : ∀ i, Integrable (L t i) ν)
    (hLt : ∀ i v, DifferentiableAt ℝ (fun s => L s i v) t)
    (hd1 : ∀ a i k, Integrable (fun x => X i x * fieldL 𝓔 ν X (L t) x a * X k x) μ) :
    (∀ x v, HasDerivAt (fun s => lowRank X (L s) x v)
      (projXf μ X (vlasovF (field 𝓔 ν (lowRank X (L t))) (lowRank X (L t))) x v) t) ↔
      ∀ i v, HasDerivAt (fun s => L s i v) (lRhs 𝓔 μ ν X (L t) i v) t := by
  have hR : ∀ x v, projXf μ X (vlasovF (field 𝓔 ν (lowRank X (L t))) (lowRank X (L t))) x v =
      ∑ i, lRhs 𝓔 μ ν X (L t) i v * X i x := fun x v => by
    simp only [projXf, proj]
    refine sum_congr rfl fun i _ => ?_
    rw [field_lowRank_L 𝓔 hLi, integral_X_vlasovF _ hX (fun k => hLv k v) hd1, lRhs]
  have hs : ∀ s x v, lowRank X (L s) x v = ∑ i, L s i v * X i x := fun s x v =>
    sum_congr rfl fun i _ => mul_comm _ _
  simp only [hR, hs]
  constructor
  · intro h i v
    exact (hasDerivAt_coeff_iff hX.orth fun i => hLt i v).1 (fun x => h x v) i
  · intro h x v
    exact (hasDerivAt_coeff_iff hX.orth fun i => hLt i v).2 (fun i => h i v) x

/-- `L_k = ∑_l S_kl V_l`. -/
def lOfS (S : Matrix (Fin r) (Fin r) ℝ) (V : Fin r → PS d → ℝ) (k : Fin r) (v : PS d) : ℝ :=
  ∑ l, S k l * V l v

/-- `∑_l (∑_k X_k S_kl) V_l = ∑_k X_k (∑_l S_kl V_l)`. -/
lemma lowRank_coreK (X V : Fin r → PS d → ℝ) (S : Matrix (Fin r) (Fin r) ℝ) :
    lowRank (coreK X S) V = lowRank X (lOfS S V) := by
  funext x v
  simp only [lowRank, coreK, lOfS, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring

/-- The partial derivatives of `L_k = ∑_l S_kl V_l`. -/
lemma pd_lOfS {V : Fin r → PS d → ℝ} (S : Matrix (Fin r) (Fin r) ℝ)
    (hV : ∀ j, Differentiable ℝ (V j)) (a : Fin d) (k : Fin r) (v : PS d) :
    pd a (lOfS S V k) v = ∑ l, S k l * pd a (V l) v := by
  have h : lOfS S V k = fun y => ∑ l, V l y * S k l := funext fun y =>
    sum_congr rfl fun l _ => mul_comm _ _
  rw [h, pd_sum_mul a _ fun l => hV l v]
  exact sum_congr rfl fun l _ => mul_comm _ _

/-- The coefficient of `X_i V_j` in `F(f)`, for `f = ∑ X_k S_kl V_l`: the integral over `v` of the
`X_i`-coefficient of `F(f)` is `-∑_kl (c¹_jl · d²_ik - c²_jl · d¹_ik[E]) S_kl`. -/
private lemma integral_V_lRhs {X V : Fin r → PS d → ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    (E : PS d → PS d) (hV : IsVelocityBasis ν V) (i j : Fin r) :
    Integrable (fun w => V j w * (∑ k, ∑ a, d1 μ X E a i k * pd a (lOfS S V k) w -
        ∑ k, (∑ a, d2 μ X a i k * w a) * lOfS S V k w)) ν ∧
    ∫ w, V j w * (∑ k, ∑ a, d1 μ X E a i k * pd a (lOfS S V k) w -
        ∑ k, (∑ a, d2 μ X a i k * w a) * lOfS S V k w) ∂ν =
      -∑ k, ∑ l, (∑ a, c1 ν V a j l * d2 μ X a i k -
        ∑ a, c2 ν V a j l * d1 μ X E a i k) * S k l := by
  set D1 := fun a k => d1 μ X E a i k with hD1
  set D2 := fun a k => d2 μ X a i k with hD2
  have h : ∀ w, V j w * (∑ k, ∑ a, d1 μ X E a i k * pd a (lOfS S V k) w -
      ∑ k, (∑ a, d2 μ X a i k * w a) * lOfS S V k w) =
      ∑ k, ∑ l, ∑ a, ((V j w * pd a (V l) w) * (D1 a k * S k l) -
        (w a * V j w * V l w) * (D2 a k * S k l)) := fun w => by
    simp only [pd_lOfS S hV.diff, sum_sub_distrib, mul_sub, lOfS]
    congr 1
    · simp only [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun l _ => sum_congr rfl fun a _ => by
        simp only [hD1]
        ring
    · simp only [mul_sum, sum_mul]
      refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => sum_congr rfl fun a _ => ?_
      simp only [hD2]
      ring
  have hI : ∀ k l a, Integrable (fun w => (V j w * pd a (V l) w) * (D1 a k * S k l) -
      (w a * V j w * V l w) * (D2 a k * S k l)) ν := fun k l a =>
    ((hV.c2 a j l).mul_const _).sub ((hV.c1 a j l).mul_const _)
  have hJ : ∀ k l a, ∫ w, ((V j w * pd a (V l) w) * (D1 a k * S k l) -
      (w a * V j w * V l w) * (D2 a k * S k l)) ∂ν =
      c2 ν V a j l * (D1 a k * S k l) - c1 ν V a j l * (D2 a k * S k l) := fun k l a => by
    rw [integral_sub ((hV.c2 a j l).mul_const _) ((hV.c1 a j l).mul_const _), integral_mul_const,
      integral_mul_const]
    rfl
  simp only [h]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun a _ => hI k l a, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun a _ => hI k l a, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun a _ => hI k l a,
    ← sum_neg_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun a _ => hI k l a]
  simp only [hJ]
  rw [sum_sub_distrib, sub_mul, sum_mul, sum_mul, neg_sub]
  simp only [hD1, hD2, mul_assoc]

/-- **(2.9) ⇔ (2.14)** (arXiv 1801.01103).  For fixed orthonormal `X_i`, `V_j` and
`f = ∑_ij X_i S_ij V_j`, the backward S-step equation `∂ₜf = P_V̄ P_X̄ (v·∇ₓf - E(f)·∇ᵥf)` holds at
time `t` at every `(x, v)` if and only if the matrix `S` satisfies the `r²` ordinary differential
equations (2.14), which depend neither on `x` nor on `v`, with `E(S)` determined by `S`.  `hd1` says
that the integrals `d¹_ik[E(S)]` exist. -/
theorem sStep_iff (𝓔 : (PS d → ℝ) → PS d → PS d) {X V : Fin r → PS d → ℝ}
    {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {t : ℝ} (hX : IsSpaceBasis μ X) (hV : IsVelocityBasis ν V)
    (hSt : ∀ i j, DifferentiableAt ℝ (fun s => S s i j) t)
    (hd1 : ∀ a i k, Integrable (fun x => X i x * fieldS 𝓔 ν X V (S t) x a * X k x) μ) :
    (∀ x v, HasDerivAt (fun s => lowRank (coreK X (S s)) V x v)
      (-projVf ν V (projXf μ X (vlasovF (field 𝓔 ν (lowRank (coreK X (S t)) V))
        (lowRank (coreK X (S t)) V))) x v) t) ↔
      ∀ i j, HasDerivAt (fun s => S s i j) (sRhs 𝓔 μ ν X V (S t) i j) t := by
  have hE : field 𝓔 ν (lowRank (coreK X (S t)) V) = fieldS 𝓔 ν X V (S t) :=
    field_lowRank_S 𝓔 hV.mass
  have hf := lowRank_coreK X V (S t)
  rw [hE, hf]
  set E := fieldS 𝓔 ν X V (S t) with hEdef
  set LL := lOfS (S t) V with hLL
  have hLd : ∀ k w, DifferentiableAt ℝ (LL k) w := fun k w =>
    DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul (hV.diff l w)
  have hPX : ∀ w x, projXf μ X (vlasovF E (lowRank X LL)) x w =
      ∑ i, (∑ k, ∑ a, d1 μ X E a i k * pd a (LL k) w -
        ∑ k, (∑ a, d2 μ X a i k * w a) * LL k w) * X i x := fun w x => by
    simp only [projXf, proj]
    exact sum_congr rfl fun i _ => by rw [integral_X_vlasovF E hX (fun k => hLd k w) hd1 i]
  have hG : ∀ x v, -projVf ν V (projXf μ X (vlasovF E (lowRank X LL))) x v =
      ∑ j, (∑ i, sRhs 𝓔 μ ν X V (S t) i j * X i x) * V j v := fun x v => by
    simp only [projVf, proj, hPX, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    have hI := fun i => (integral_V_lRhs (μ := μ) (X := X) (S := S t) E hV i j).1
    have hJ := fun i => (integral_V_lRhs (μ := μ) (X := X) (S := S t) E hV i j).2
    have h1 : ∀ w, V j w * ∑ i, (∑ k, ∑ a, d1 μ X E a i k * pd a (LL k) w -
        ∑ k, (∑ a, d2 μ X a i k * w a) * LL k w) * X i x =
        ∑ i, (V j w * (∑ k, ∑ a, d1 μ X E a i k * pd a (LL k) w -
          ∑ k, (∑ a, d2 μ X a i k * w a) * LL k w)) * X i x := fun w => by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    simp only [h1]
    rw [integral_finsetSum _ fun i _ => (hI i).mul_const _]
    simp only [integral_mul_const, hJ]
    rw [← neg_mul]
    congr 1
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← neg_mul, neg_neg]
    rfl
  have hs : ∀ s x v, lowRank (coreK X (S s)) V x v = ∑ j, (∑ k, S s k j * X k x) * V j v :=
    fun s x v => sum_congr rfl fun j _ => by
      simp only [coreK, mul_comm (X _ x)]
  simp only [hG, hs]
  have hA : ∀ x j, DifferentiableAt ℝ (fun s => ∑ k, S s k j * X k x) t := fun x j =>
    DifferentiableAt.fun_sum fun k _ => (hSt k j).mul_const _
  constructor
  · intro h i j
    have h1 := fun x => (hasDerivAt_coeff_iff hV.orth (hA x)).1 (h x)
    exact (hasDerivAt_coeff_iff hX.orth (A := fun s k => S s k j) fun k => hSt k j).1
      (fun x => h1 x j) i
  · intro h x
    refine (hasDerivAt_coeff_iff hV.orth (hA x)).2 fun j => ?_
    exact (hasDerivAt_coeff_iff hX.orth (A := fun s k => S s k j) fun k => hSt k j).2
      (fun k => h k j) x

/-- All data of one first-order Lie step of Sec. 2 on `[0, τ]`, the equations holding for `t ∈ I`:
the K-step (2.13) with initial value `K_j(0) = ∑_i X_i⁰ S⁰_ij`, the decomposition
`K_j(τ) = ∑_i X_i¹ Ŝ¹_ij`, the S-step (2.14) with `S(0) = Ŝ¹`, the L-step (2.15) with
`L_i(0) = ∑_j S_ij(τ) V_j⁰`, and the decomposition `L_i(τ) = ∑_j S¹_ij V_j¹`.  The remaining fields
are the regularity needed for the printed quantities to exist. -/
structure IsLieStep (𝓔 : (PS d → ℝ) → PS d → PS d) (μ ν : Measure (PS d)) (τ : ℝ) (I : Set ℝ)
    (X₀ X₁ V₀ V₁ : Fin r → PS d → ℝ) (S₀ Ŝ₁ S₁ : Matrix (Fin r) (Fin r) ℝ)
    (K : ℝ → Fin r → PS d → ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (L : ℝ → Fin r → PS d → ℝ) : Prop where
  basisV : IsVelocityBasis ν V₀
  basisX : IsSpaceBasis μ X₁
  kDiff : ∀ t ∈ I, ∀ j, Differentiable ℝ (K t j)
  kEq : ∀ t ∈ I, ∀ j x, HasDerivAt (fun s => K s j x) (kRhs 𝓔 ν V₀ (K t) j x) t
  kStart : K 0 = coreK X₀ S₀
  kEnd : K τ = coreK X₁ Ŝ₁
  sInt : ∀ t ∈ I, ∀ a i k,
    Integrable (fun x => X₁ i x * fieldS 𝓔 ν X₁ V₀ (S t) x a * X₁ k x) μ
  sEq : ∀ t ∈ I, ∀ i j, HasDerivAt (fun s => S s i j) (sRhs 𝓔 μ ν X₁ V₀ (S t) i j) t
  sStart : S 0 = Ŝ₁
  lDiff : ∀ t ∈ I, ∀ i, Differentiable ℝ (L t i)
  lIntegrable : ∀ t ∈ I, ∀ i, Integrable (L t i) ν
  lInt : ∀ t ∈ I, ∀ a i k,
    Integrable (fun x => X₁ i x * fieldL 𝓔 ν X₁ (L t) x a * X₁ k x) μ
  lEq : ∀ t ∈ I, ∀ i v, HasDerivAt (fun s => L s i v) (lRhs 𝓔 μ ν X₁ (L t) i v) t
  lStart : L 0 = lOfS (S τ) V₀
  lEnd : L τ = lOfS S₁ V₁

/-- **Sec. 2, the Lie–Trotter step** (arXiv 1801.01103).  The three lower-dimensional systems
(2.13), (2.14), (2.15), chained through the QR decompositions as in the paper, solve the splitting
(2.8), (2.9), (2.10) of the projected equation (2.6) "one after the other": each function starts
where the previous one ended, and the output is `∑ X_i¹ S_ij¹ V_j¹`. -/
theorem IsLieStep.splitting {𝓔 : (PS d → ℝ) → PS d → PS d} {τ : ℝ} {I : Set ℝ}
    {X₀ X₁ V₀ V₁ : Fin r → PS d → ℝ} {S₀ Ŝ₁ S₁ : Matrix (Fin r) (Fin r) ℝ}
    {K : ℝ → Fin r → PS d → ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {L : ℝ → Fin r → PS d → ℝ}
    (h : IsLieStep 𝓔 μ ν τ I X₀ X₁ V₀ V₁ S₀ Ŝ₁ S₁ K S L) :
    (∀ t ∈ I, ∀ x v, HasDerivAt (fun s => lowRank (K s) V₀ x v)
      (projVf ν V₀ (vlasovF (field 𝓔 ν (lowRank (K t) V₀)) (lowRank (K t) V₀)) x v) t) ∧
    (∀ t ∈ I, ∀ x v, HasDerivAt (fun s => lowRank (coreK X₁ (S s)) V₀ x v)
      (-projVf ν V₀ (projXf μ X₁ (vlasovF (field 𝓔 ν (lowRank (coreK X₁ (S t)) V₀))
        (lowRank (coreK X₁ (S t)) V₀))) x v) t) ∧
    (∀ t ∈ I, ∀ x v, HasDerivAt (fun s => lowRank X₁ (L s) x v)
      (projXf μ X₁ (vlasovF (field 𝓔 ν (lowRank X₁ (L t))) (lowRank X₁ (L t))) x v) t) ∧
    lowRank (K 0) V₀ = lowRank (coreK X₀ S₀) V₀ ∧
    lowRank (coreK X₁ (S 0)) V₀ = lowRank (K τ) V₀ ∧
    lowRank X₁ (L 0) = lowRank (coreK X₁ (S τ)) V₀ ∧
    lowRank X₁ (L τ) = lowRank (coreK X₁ S₁) V₁ := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, ?_, ?_, ?_⟩
  · exact (kStep_iff 𝓔 h.basisV (h.kDiff t ht) fun j x =>
      (h.kEq t ht j x).differentiableAt).2 (h.kEq t ht)
  · exact (sStep_iff 𝓔 h.basisX h.basisV (fun i j => (h.sEq t ht i j).differentiableAt)
      (h.sInt t ht)).2 (h.sEq t ht)
  · exact (lStep_iff 𝓔 h.basisX (h.lDiff t ht) (h.lIntegrable t ht)
      (fun i v => (h.lEq t ht i v).differentiableAt) (h.lInt t ht)).2 (h.lEq t ht)
  · rw [h.kStart]
  · rw [h.sStart, h.kEnd]
  · rw [h.lStart, lowRank_coreK]
  · rw [h.lEnd, lowRank_coreK]

/-! ### Sec. 2.2: the symmetric coefficient matrices -/

/-- **Sec. 2.2** (arXiv 1801.01103): every `c^{1;x_a}`, with entries `∫ v_a V_j V_l dv`, is
symmetric. -/
theorem c1_isSymm (ν : Measure (PS d)) (V : Fin r → PS d → ℝ) (a : Fin d) : (c1 ν V a).IsSymm := by
  ext j l
  simp only [c1, Matrix.transpose_apply, Matrix.of_apply]
  exact integral_congr_ae (ae_of_all _ fun v => by ring)

/-- **Sec. 2.2** (arXiv 1801.01103): every `d^{1;x_a}`, with entries `∫ X_i E_a X_k dx`, is
symmetric. -/
theorem d1_isSymm (μ : Measure (PS d)) (X : Fin r → PS d → ℝ) (E : PS d → PS d) (a : Fin d) :
    (d1 μ X E a).IsSymm := by
  ext i k
  simp only [d1, Matrix.transpose_apply, Matrix.of_apply]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- **Sec. 2.2, K-step** (arXiv 1801.01103): the advection `∂ₜM = -c^{1;x_a} ∂_a M` obtained by Lie
splitting of (2.17) decouples into scalar advections.  There are an orthogonal `T` and a diagonal
`D` with `T c^{1;x_a} Tᵀ = D`, and the conclusions of `advection_decouple` hold. -/
theorem kAdvection_decouple (ν : Measure (PS d)) (V : Fin r → PS d → ℝ) (a : Fin d) :
    ∃ (T : Matrix (Fin r) (Fin r) ℝ) (D : Fin r → ℝ), Tᵀ * T = 1 ∧
      T * c1 ν V a * Tᵀ = Matrix.diagonal D ∧
      ∀ M : ℝ → PS d → Fin r → ℝ,
        (IsAdvectionSol (c1 ν V a) (EuclideanSpace.single a 1) M ↔
          IsAdvectionSol (Matrix.diagonal D) (EuclideanSpace.single a 1) fun t x => T *ᵥ M t x) ∧
        (IsAdvectionSol (c1 ν V a) (EuclideanSpace.single a 1) M → ∀ t x j, M t x j =
          ∑ l, T l j * (T *ᵥ M 0 (x - (t * D l) • EuclideanSpace.single a 1)) l) := by
  obtain ⟨T, D, hT, hD⟩ := exists_orthogonal_diagonalisation (c1_isSymm ν V a)
  have h := advection_decouple (EuclideanSpace.single a (1 : ℝ) : PS d) hT hD
  exact ⟨T, D, hT, hD, fun M => ⟨h.1 M, h.2.1 M⟩⟩

/-- **Sec. 2.2, L-step** (arXiv 1801.01103): with the frozen field, the advection
`∂ₜM = d^{1;x_a} ∂_a M` obtained by Lie splitting of (2.15) decouples into scalar advections.
Written with `A = -d^{1;x_a}`, which is symmetric as well. -/
theorem lAdvection_decouple (μ : Measure (PS d)) (X : Fin r → PS d → ℝ) (E : PS d → PS d)
    (a : Fin d) :
    ∃ (T : Matrix (Fin r) (Fin r) ℝ) (D : Fin r → ℝ), Tᵀ * T = 1 ∧
      T * (-d1 μ X E a) * Tᵀ = Matrix.diagonal D ∧
      ∀ M : ℝ → PS d → Fin r → ℝ,
        (IsAdvectionSol (-d1 μ X E a) (EuclideanSpace.single a 1) M ↔
          IsAdvectionSol (Matrix.diagonal D) (EuclideanSpace.single a 1) fun t x => T *ᵥ M t x) ∧
        (IsAdvectionSol (-d1 μ X E a) (EuclideanSpace.single a 1) M → ∀ t x j, M t x j =
          ∑ l, T l j * (T *ᵥ M 0 (x - (t * D l) • EuclideanSpace.single a 1)) l) := by
  have hs : (-d1 μ X E a).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_neg, (d1_isSymm μ X E a).eq]
  obtain ⟨T, D, hT, hD⟩ := exists_orthogonal_diagonalisation hs
  have h := advection_decouple (EuclideanSpace.single a (1 : ℝ) : PS d) hT hD
  exact ⟨T, D, hT, hD, fun M => ⟨h.1 M, h.2.1 M⟩⟩

/-! ### Instances of the regularity hypotheses -/

/-- A constant basis function on a probability space `Ω_v` with finite first moments, for `r = 1`:
the hypotheses of `IsVelocityBasis` (Sec. 2 of arXiv 1801.01103) can hold. -/
theorem isVelocityBasis_one (hν : IsProbabilityMeasure ν)
    (hm : ∀ a : Fin d, Integrable (fun v : PS d => v a) ν) :
    IsVelocityBasis ν (fun (_ : Fin 1) (_ : PS d) => (1 : ℝ)) where
  orth := ⟨fun _ => memLp_const 1, fun i k => by simp [Subsingleton.elim i k]⟩
  diff _ := differentiable_const _
  mass _ := integrable_const _
  c1 a _ _ := by simpa using hm a
  c2 a _ _ := by simp [pd]

/-- A constant basis function on a probability space `Ω_x`, for `r = 1`: the hypotheses of
`IsSpaceBasis` (Sec. 2 of arXiv 1801.01103) can hold. -/
theorem isSpaceBasis_one (hμ : IsProbabilityMeasure μ) :
    IsSpaceBasis μ (fun (_ : Fin 1) (_ : PS d) => (1 : ℝ)) where
  orth := ⟨fun _ => memLp_const 1, fun i k => by simp [Subsingleton.elim i k]⟩
  diff _ := differentiable_const _
  d2 a _ _ := by simp [pd]

/-- The structure `IsLieStep` is inhabited, for all `𝓔`, `τ`, `I`: the hypotheses of
`IsLieStep.splitting` (Sec. 2 of arXiv 1801.01103) are jointly satisfiable.  This instance is
degenerate (one velocity, `r = 1`) and only serves that purpose. -/
theorem isLieStep_trivial (𝓔 : (PS d → ℝ) → PS d → PS d) (τ : ℝ) (I : Set ℝ) :
    IsLieStep 𝓔 (Measure.dirac 0) (Measure.dirac 0) τ I
      (fun (_ : Fin 1) (_ : PS d) => (1 : ℝ)) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) 1 1 1
      (fun _ _ _ => 1) (fun _ => 1) (fun _ _ _ => 1) := by
  have hpd : ∀ (a : Fin d) (c : ℝ), pd a (fun _ => c) = fun _ => 0 := fun a c => by
    funext x
    simp [pd]
  have hk : ∀ (j : Fin 1) (x : PS d),
      kRhs 𝓔 (Measure.dirac 0) (fun _ _ => 1) (fun _ _ => 1) j x = 0 := by
    intro j x
    simp [kRhs, c2, hpd]
  have hs : ∀ S : Matrix (Fin 1) (Fin 1) ℝ, ∀ i j,
      sRhs 𝓔 (Measure.dirac 0) (Measure.dirac 0) (fun _ _ => 1) (fun _ _ => 1) S i j = 0 := by
    intro S i j
    simp [sRhs, c2, d2, hpd]
  have hl : ∀ (i : Fin 1) (v : PS d), lRhs 𝓔 (Measure.dirac 0) (Measure.dirac 0) (fun _ _ => 1)
      (fun _ _ => 1) i v = 0 := by
    intro i v
    simp [lRhs, d2, hpd]
  have hc : ∀ (φ : PS d → ℝ), Integrable φ (Measure.dirac (0 : PS d)) := fun φ =>
    integrable_dirac (by simp)
  have h1 : ∀ i j : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 1 := fun i j => by
    rw [Subsingleton.elim i j]
    simp
  refine ⟨isVelocityBasis_one inferInstance fun a => hc _, isSpaceBasis_one inferInstance,
    fun _ _ _ => differentiable_const _, fun t _ j x => ?_, ?_, ?_, fun _ _ _ _ _ => hc _,
    fun t _ i j => ?_, rfl, fun _ _ _ => differentiable_const _, fun _ _ _ => hc _,
    fun _ _ _ _ _ => hc _, fun t _ i v => ?_, ?_, ?_⟩
  · rw [hk]
    exact hasDerivAt_const t _
  · funext j x
    simp [coreK, h1]
  · funext j x
    simp [coreK, h1]
  · rw [hs]
    exact hasDerivAt_const t _
  · rw [hl]
    exact hasDerivAt_const t _
  · funext j x
    simp [lOfS, h1]
  · funext j x
    simp [lOfS, h1]

end Vlasov

/-! ### Sec. 3: the hierarchical algorithm -/

section GramSchmidt

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The inner loop of Algorithm 2 (lines 3–8): starting from `c`, subtract one after the other the
components along `Q 0, …, Q (k - 1)`, each computed from the current vector. -/
noncomputable def mgsSweep (Q : ℕ → E) (c : E) : ℕ → E
  | 0 => c
  | k + 1 => mgsSweep Q c k - ⟪Q k, mgsSweep Q c k⟫ • Q k

/-- The array `C` of Algorithm 2 after the outer iterations `0, …, j - 1`: as in the paper the
algorithm works in place, and iteration `j` overwrites only entry `j`. -/
noncomputable def mgsState (C : ℕ → E) : ℕ → ℕ → E
  | 0 => C
  | j + 1 => Function.update (mgsState C j) j
      ((‖mgsSweep (mgsState C j) (mgsState C j j) j‖)⁻¹ •
        mgsSweep (mgsState C j) (mgsState C j j) j)

/-- The matrix `S` of Algorithm 2: line 4 for `k < j`, line 9 for `k = j`, line 1 otherwise. -/
noncomputable def mgsS (C : ℕ → E) (k j : ℕ) : ℝ :=
  if k < j then ⟪mgsState C j k, mgsSweep (mgsState C j) (mgsState C j j) k⟫
  else if k = j then ‖mgsSweep (mgsState C j) (mgsState C j j) j‖ else 0

lemma mgsState_of_le (C : ℕ → E) {j n : ℕ} (h : j ≤ n) : mgsState C j n = C n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [mgsState, Function.update_of_ne (by omega)]
    exact ih (by omega)

lemma mgsState_succ_of_lt (C : ℕ → E) {j n : ℕ} (h : n < j) :
    mgsState C (j + 1) n = mgsState C j n := by
  rw [mgsState, Function.update_of_ne (by omega)]

lemma mgsState_stable (C : ℕ → E) {j m n : ℕ} (hn : n < j) (hm : j ≤ m) :
    mgsState C m n = mgsState C j n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [mgsState_succ_of_lt C (by omega), ih]

/-- The sweep against an orthonormal family: the result is orthogonal to the family, and `c` is
the result plus the removed components. -/
lemma mgsSweep_spec {Q : ℕ → E} {m : ℕ}
    (hQ : ∀ i k, i < m → k < m → ⟪Q i, Q k⟫ = if i = k then (1 : ℝ) else 0) (c : E) (k : ℕ)
    (hk : k ≤ m) :
    (∀ i, i < k → ⟪Q i, mgsSweep Q c k⟫ = 0) ∧
      c = mgsSweep Q c k + ∑ i ∈ range k, ⟪Q i, mgsSweep Q c i⟫ • Q i := by
  induction k with
  | zero => simp [mgsSweep]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [mgsSweep, inner_sub_right, real_inner_smul_right]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [h1 i hi, hQ i k (by omega) (by omega)]
        simp [hi.ne]
      · rw [hQ i i (by omega) (by omega)]
        simp
    · rw [sum_range_succ, mgsSweep, ← add_assoc, add_right_comm, sub_add_cancel]
      exact h2

/-- The invariants of Algorithm 2 of arXiv 1801.01103, for independent input. -/
theorem mgs_invariant {C : ℕ → E} {r : ℕ} (hC : LinearIndependent ℝ fun i : Fin r => C i)
    (j : ℕ) (hj : j ≤ r) :
    (∀ i k, i < j → k < j →
      ⟪mgsState C j i, mgsState C j k⟫ = if i = k then (1 : ℝ) else 0) ∧
    (∀ i, i < j → mgsState C j i ∈
      Submodule.span ℝ ((fun i : Fin r => C i) '' {l | l.val < j})) ∧
    (∀ i, i < j → C i = ∑ k ∈ range (i + 1), mgsS C k i • mgsState C j k) ∧
    (∀ i, i < j → 0 < mgsS C i i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hO, hSp, hR, hP⟩ := ih (by omega)
    set Q := mgsState C j with hQ
    have hQj : Q j = C j := mgsState_of_le C le_rfl
    set w := mgsSweep Q (Q j) j with hw
    obtain ⟨hw0, hwc⟩ := mgsSweep_spec hO (Q j) j le_rfl
    rw [← hw] at hw0 hwc
    have hsum : ∑ i ∈ range j, ⟪Q i, mgsSweep Q (Q j) i⟫ • Q i ∈
        Submodule.span ℝ ((fun i : Fin r => C i) '' {l | l.val < j}) :=
      Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hSp i (mem_range.1 hi))
    have hne : w ≠ 0 := by
      intro h0
      have hmem : C j ∈ Submodule.span ℝ ((fun i : Fin r => C i) '' {l | l.val < j}) := by
        rw [← hQj, hwc, h0, zero_add]
        exact hsum
      exact hC.notMem_span_image (s := {l | l.val < j}) (x := ⟨j, by omega⟩) (by simp) hmem
    have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hne
    have hQ' : ∀ i, i < j → mgsState C (j + 1) i = Q i := fun i hi => mgsState_succ_of_lt C hi
    have hQ'j : mgsState C (j + 1) j = ‖w‖⁻¹ • w := by
      rw [mgsState, Function.update_self]
    have hSj : mgsS C j j = ‖w‖ := by simp [mgsS, hw, hQ]
    refine ⟨fun i k hi hk => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · rw [hQ' i hi, hQ' k hk]
          exact hO i k hi hk
        · rw [hQ' i hi, hQ'j, real_inner_smul_right, hw0 i hi]
          simp [hi.ne]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · rw [hQ' k hk, hQ'j, real_inner_smul_left, real_inner_comm, hw0 k hk]
          simp [hk.ne']
        · rw [hQ'j, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
          simp only [↓reduceIte]
          field_simp
    · have hmono : Submodule.span ℝ ((fun i : Fin r => C i) '' {l | l.val < j}) ≤
          Submodule.span ℝ ((fun i : Fin r => C i) '' {l | l.val < j + 1}) :=
        Submodule.span_mono (Set.image_mono fun l (hl : l.val < j) =>
          (by omega : l.val < j + 1))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hQ' i hi]
        exact hmono (hSp i hi)
      · rw [hQ'j]
        refine Submodule.smul_mem _ _ ?_
        have hw' : w = C i - ∑ k ∈ range i, ⟪Q k, mgsSweep Q (Q i) k⟫ • Q k := by
          rw [← hQj]
          exact eq_sub_of_add_eq hwc.symm
        rw [hw']
        refine Submodule.sub_mem _ (Submodule.subset_span ⟨⟨i, by omega⟩, ?_, rfl⟩) (hmono hsum)
        simp
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · conv_lhs => rw [hR i hi]
        refine sum_congr rfl fun k hk => ?_
        rw [hQ' k (by have := mem_range.1 hk; omega)]
      · rw [sum_range_succ, hSj, hQ'j, smul_smul, mul_inv_cancel₀ hnw, one_smul]
        have e1 : ∑ k ∈ range i, mgsS C k i • mgsState C (i + 1) k =
            ∑ k ∈ range i, ⟪Q k, mgsSweep Q (Q i) k⟫ • Q k := by
          refine sum_congr rfl fun k hk => ?_
          have hk' := mem_range.1 hk
          rw [hQ' k hk']
          simp [mgsS, hk', hQ]
        rw [e1, add_comm, ← hwc, hQj]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hP i hi
      · rw [hSj]
        exact norm_pos_iff.2 hne

/-- **Algorithm 2** (arXiv 1801.01103), in an inner product space: for independent input `C_j`,
`j < r`, the output `Q_j` is orthonormal and `C_j = ∑_i S_ij Q_i` with `S` upper triangular with
positive diagonal.  The independence hypothesis cannot be dropped, since line 11 divides by
`S_jj`; the paper does not state it. -/
theorem mgs_spec {C : ℕ → E} {r : ℕ} (hC : LinearIndependent ℝ fun i : Fin r => C i) :
    (∀ i k : Fin r, ⟪mgsState C r i, mgsState C r k⟫ = if i = k then (1 : ℝ) else 0) ∧
    (∀ j : Fin r, C j = ∑ i : Fin r, mgsS C i j • mgsState C r i) ∧
    (∀ i j : Fin r, j < i → mgsS C i j = 0) ∧ (∀ i : Fin r, 0 < mgsS C i i) := by
  obtain ⟨hO, -, hR, hP⟩ := mgs_invariant hC r le_rfl
  refine ⟨fun i k => ?_, fun j => ?_, fun i j hij => ?_, fun i => hP i i.2⟩
  · have := hO i k i.2 k.2
    simpa [Fin.ext_iff] using this
  · rw [hR j j.2, Fin.sum_univ_eq_sum_range (fun i => mgsS C i j • mgsState C r i) r]
    refine sum_subset (fun k hk => ?_) fun k _ hk => ?_
    · have := mem_range.1 hk
      have := j.2
      exact mem_range.2 (by omega)
    · have hk' : ¬ k < j.val + 1 := fun h => hk (mem_range.2 h)
      have h1 : ¬ k < j.val := by omega
      have h2 : k ≠ j.val := by omega
      simp [mgsS, h1, h2]
  · have h1 : ¬ i.val < j.val := by have := Fin.lt_def.1 hij; omega
    have h2 : i.val ≠ j.val := by have := Fin.lt_def.1 hij; omega
    simp [mgsS, h1, h2]

/-- A linear isometry commutes with the sweep. -/
lemma map_mgsSweep (Φ : E →ₗᵢ[ℝ] F) (Q : ℕ → E) (c : E) (k : ℕ) :
    Φ (mgsSweep Q c k) = mgsSweep (Φ ∘ Q) (Φ c) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mgsSweep, map_sub, map_smul, ← ih, Φ.inner_map_map, Function.comp]

/-- A linear isometry commutes with Algorithm 2. -/
lemma map_mgsState (Φ : E →ₗᵢ[ℝ] F) (C : ℕ → E) (j n : ℕ) :
    Φ (mgsState C j n) = mgsState (Φ ∘ C) j n := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    have hfun : Φ ∘ mgsState C j = mgsState (Φ ∘ C) j := funext fun n => ih n
    rcases eq_or_ne n j with rfl | hn
    · have hs : mgsSweep (mgsState (Φ ∘ C) n) (mgsState (Φ ∘ C) n n) n =
          Φ (mgsSweep (mgsState C n) (mgsState C n n) n) := by
        rw [map_mgsSweep, hfun, ih n]
      rw [mgsState, mgsState, Function.update_self, Function.update_self, hs, map_smul,
        Φ.norm_map]
    · rw [mgsState, mgsState, Function.update_of_ne hn, Function.update_of_ne hn, ih n]

/-- A linear isometry does not change the matrix `S` of Algorithm 2. -/
lemma mgsS_map (Φ : E →ₗᵢ[ℝ] F) (C : ℕ → E) (k j : ℕ) : mgsS (Φ ∘ C) k j = mgsS C k j := by
  have hfun : Φ ∘ mgsState C j = mgsState (Φ ∘ C) j := funext fun n => map_mgsState Φ C j n
  simp only [mgsS, ← hfun, Function.comp, ← map_mgsSweep Φ, Φ.inner_map_map, Φ.norm_map]

end GramSchmidt

section Core

open scoped LeanDLRA.Frobenius

variable {a b H₁ H₂ H : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The function `∑_αβ X¹_α(x₁) C_αβ X²_β(x₂)` of (3.2), with core `C`. -/
noncomputable def coreMap (τ : H₁ →L[ℝ] H₂ →L[ℝ] H) (X₁ : a → H₁) (X₂ : b → H₂)
    (C : Matrix a b ℝ) : H :=
  ∑ α, ∑ β, C α β • τ (X₁ α) (X₂ β)

/-- **(3.14)** (arXiv 1801.01103): `K_j + c K_k` has the core `C_j + c C_k`. -/
theorem coreMap_add_smul (τ : H₁ →L[ℝ] H₂ →L[ℝ] H) (X₁ : a → H₁) (X₂ : b → H₂)
    (C D : Matrix a b ℝ) (c : ℝ) :
    coreMap τ X₁ X₂ (C + c • D) = coreMap τ X₁ X₂ C + c • coreMap τ X₁ X₂ D := by
  simp only [coreMap, Finset.smul_sum, ← Finset.sum_add_distrib, Matrix.add_apply,
    Matrix.smul_apply, add_smul, smul_smul, smul_eq_mul]

/-- `⟨X¹_α X²_β, ∑ X¹ D X²⟩ = D_αβ`. -/
lemma inner_tensor_coreMap {τ : H₁ →L[ℝ] H₂ →L[ℝ] H} (ht : IsTensorPairing τ) {X₁ : a → H₁}
    {X₂ : b → H₂} (hX₁ : Orthonormal ℝ X₁) (hX₂ : Orthonormal ℝ X₂) (D : Matrix a b ℝ)
    (α : a) (β : b) : ⟪τ (X₁ α) (X₂ β), coreMap τ X₁ X₂ D⟫ = D α β := by
  have h1 := orthonormal_iff_ite.mp hX₁
  have h2 := orthonormal_iff_ite.mp hX₂
  simp only [coreMap, inner_sum, real_inner_smul_right, ht.inner_eq, h1, h2]
  simp [mul_ite, Finset.sum_ite_eq]

/-- **(3.13)** (arXiv 1801.01103): for orthonormal `X¹_α`, `X²_β`,
`⟨K_j, K_k⟩ₓ = ∑_αβ C_jαβ C_kαβ`, "without evaluating any integrals". -/
theorem inner_coreMap {τ : H₁ →L[ℝ] H₂ →L[ℝ] H} (ht : IsTensorPairing τ) {X₁ : a → H₁}
    {X₂ : b → H₂} (hX₁ : Orthonormal ℝ X₁) (hX₂ : Orthonormal ℝ X₂) (C D : Matrix a b ℝ) :
    ⟪coreMap τ X₁ X₂ C, coreMap τ X₁ X₂ D⟫ = ∑ α, ∑ β, C α β * D α β := by
  simp only [coreMap, sum_inner, real_inner_smul_left]
  refine sum_congr rfl fun α _ => sum_congr rfl fun β _ => ?_
  congr 1
  exact inner_tensor_coreMap ht hX₁ hX₂ D α β

/-- The map `C ↦ ∑ X¹_α C_αβ X²_β` as a linear isometry from the core tensors with the Frobenius
inner product. -/
noncomputable def coreIso {τ : H₁ →L[ℝ] H₂ →L[ℝ] H} (ht : IsTensorPairing τ) {X₁ : a → H₁}
    {X₂ : b → H₂} (hX₁ : Orthonormal ℝ X₁) (hX₂ : Orthonormal ℝ X₂) :
    Matrix a b ℝ →ₗᵢ[ℝ] H where
  toFun := coreMap τ X₁ X₂
  map_add' C D := by simpa using coreMap_add_smul τ X₁ X₂ C D 1
  map_smul' c C := by
    have h0 : coreMap τ X₁ X₂ 0 = 0 := by simp [coreMap]
    simpa [h0] using coreMap_add_smul τ X₁ X₂ 0 C c
  norm_map' C := by
    have h : ‖coreMap τ X₁ X₂ C‖ ^ 2 = ‖C‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_coreMap ht hX₁ hX₂, ← real_inner_self_eq_norm_sq,
        Frobenius.inner_def]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- Line 4 of Algorithm 2 (arXiv 1801.01103) for core tensors is the Frobenius product:
`S_kj = ∑_αβ C_kαβ C_jαβ`, with the current `C_k` and `C_j`. -/
theorem mgsS_of_lt (C : ℕ → Matrix a b ℝ) {k j : ℕ} (h : k < j) :
    mgsS C k j = ∑ α, ∑ β, mgsState C j k α β * mgsSweep (mgsState C j) (mgsState C j j) k α β := by
  simp [mgsS, h, Frobenius.inner_def]

/-- **Algorithm 2 and (3.13), (3.14)** (arXiv 1801.01103): "we can compute a QR decomposition
without modifying `X¹` or `X²` and without evaluating any integrals".  Let
`K_j = ∑ X¹_α C_jαβ X²_β`, `j < r`, with orthonormal `X¹`, `X²` and independent `K_j`, and run
Algorithm 2 on the core tensors `C_j` alone.  Then its output `C⁴`, `S` satisfies
`⟨X_i, X_k⟩ₓ = δ_ik` and `K_j = ∑_i X_i S_ij` for `X_i = ∑ X¹_α C⁴_iαβ X²_β`, with `S` upper
triangular.  Moreover the run is the modified Gram–Schmidt process on the functions `K_j`
themselves: `X_i` and `S` are what that process would produce.  Independence of the `K_j` is
needed and is not stated in the paper. -/
theorem algorithm2_core {τ : H₁ →L[ℝ] H₂ →L[ℝ] H} (ht : IsTensorPairing τ) {X₁ : a → H₁}
    {X₂ : b → H₂} (hX₁ : Orthonormal ℝ X₁) (hX₂ : Orthonormal ℝ X₂) {r : ℕ}
    (C : ℕ → Matrix a b ℝ)
    (hK : LinearIndependent ℝ fun j : Fin r => coreMap τ X₁ X₂ (C j)) :
    (∀ i k : Fin r, ⟪coreMap τ X₁ X₂ (mgsState C r i), coreMap τ X₁ X₂ (mgsState C r k)⟫ =
      if i = k then (1 : ℝ) else 0) ∧
    (∀ j : Fin r, coreMap τ X₁ X₂ (C j) =
      ∑ i : Fin r, mgsS C i j • coreMap τ X₁ X₂ (mgsState C r i)) ∧
    (∀ i j : Fin r, j < i → mgsS C i j = 0) ∧ (∀ i : Fin r, 0 < mgsS C i i) ∧
    (∀ j n, coreMap τ X₁ X₂ (mgsState C j n) =
      mgsState (fun l => coreMap τ X₁ X₂ (C l)) j n) ∧
    (∀ k j, mgsS (fun l => coreMap τ X₁ X₂ (C l)) k j = mgsS C k j) := by
  set Φ := coreIso ht hX₁ hX₂ with hΦ
  have hC : LinearIndependent ℝ fun i : Fin r => C i :=
    LinearIndependent.of_comp Φ.toLinearMap hK
  obtain ⟨h1, h2, h3, h4⟩ := mgs_spec hC
  refine ⟨fun i k => ?_, fun j => ?_, h3, h4, fun j n => map_mgsState Φ C j n,
    fun k j => mgsS_map Φ C k j⟩
  · have := Φ.inner_map_map (mgsState C r i) (mgsState C r k)
    rw [← h1 i k, ← this]
    rfl
  · have h5 := congrArg Φ (h2 j)
    rw [map_sum] at h5
    simp only [map_smul] at h5
    exact h5

/-- The functions `W_jξ = ∑_β Q_jξβ X²_β` of (3.6). -/
noncomputable def wFun {κ ξ : Type*} (X₂ : b → H₂) (Q : κ → ξ → b → ℝ) (j : κ) (x : ξ) : H₂ :=
  ∑ β, Q j x β • X₂ β

/-- **(3.6)** (arXiv 1801.01103): from the QR decomposition `C⁰_jαβ = ∑_ξ Q_jξβ R_αξ`,
`K_j = ∑_αξ X¹_α R_αξ W_jξ`. -/
theorem coreMap_eq_of_qr {κ ξ : Type*} [Fintype ξ] (τ : H₁ →L[ℝ] H₂ →L[ℝ] H) (X₁ : a → H₁)
    (X₂ : b → H₂) {C : Matrix a b ℝ} {R : a → ξ → ℝ} {Q : κ → ξ → b → ℝ} {j : κ}
    (hC : ∀ α β, C α β = ∑ x, Q j x β * R α x) :
    coreMap τ X₁ X₂ C = ∑ α, ∑ x, R α x • τ (X₁ α) (wFun X₂ Q j x) := by
  simp only [coreMap, wFun, hC, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  refine sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun β _ => by rw [mul_comm]

/-- **(3.7)** (arXiv 1801.01103): for orthonormal `X²_β`,
`⟨W_iα, W_kξ⟩ = ∑_β Q_iαβ Q_kξβ`, without any integral. -/
theorem inner_wFun {κ ξ : Type*} {X₂ : b → H₂} (hX₂ : Orthonormal ℝ X₂) (Q : κ → ξ → b → ℝ)
    (i k : κ) (x y : ξ) : ⟪wFun X₂ Q i x, wFun X₂ Q k y⟫ = ∑ β, Q i x β * Q k y β := by
  have h2 := orthonormal_iff_ite.mp hX₂
  simp only [wFun, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, h2]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- **(3.7)** (arXiv 1801.01103), the coefficient `a¹`: "the orthonormality relation of the
`X_{2β}` can be used to obtain a simpler formula that can be computed without performing any
integrals",
`a¹_αξ = ∑_ik c_ik ⟨W_iα, W_kξ⟩ = ∑_ikβ c_ik Q_iαβ Q_kξβ`. -/
theorem a1_formula {κ ξ : Type*} [Fintype κ] {X₂ : b → H₂} (hX₂ : Orthonormal ℝ X₂)
    (Q : κ → ξ → b → ℝ) (c : Matrix κ κ ℝ) (x y : ξ) :
    ∑ i, ∑ k, c i k * ⟪wFun X₂ Q i x, wFun X₂ Q k y⟫ =
      ∑ i, ∑ k, ∑ β, c i k * Q i x β * Q k y β := by
  simp only [inner_wFun hX₂, Finset.mul_sum, mul_assoc]

/-- **(3.7)** (arXiv 1801.01103): the coefficient `a¹` is symmetric when `c` is, as `c^{1;x₁}` is
by `c1_isSymm`, so the advection (3.7) can be decoupled as in Sec. 2.2. -/
theorem a1_symm {κ ξ : Type*} [Fintype κ] (X₂ : b → H₂) (Q : κ → ξ → b → ℝ) {c : Matrix κ κ ℝ}
    (hc : c.IsSymm) (x y : ξ) :
    ∑ i, ∑ k, c i k * ⟪wFun X₂ Q i x, wFun X₂ Q k y⟫ =
      ∑ i, ∑ k, c i k * ⟪wFun X₂ Q i y, wFun X₂ Q k x⟫ := by
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
  rw [real_inner_comm, ← hc.apply i k]

end Core

section TuckerStep

open scoped LeanDLRA.Frobenius

/-- The time reversal of a solution of `y' = G(y)` on `[a, b]` solves `z' = -G(z)`: the reason for
the cancellation in Sec. 3 of arXiv 1801.01103. -/
theorem odeSolution_reverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → E}
    {y : ℝ → E} {a b : ℝ} (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (G (y t)) (Icc a b) t) :
    ODESolution (fun _ z => -G z) (fun t => y (a + b - t)) a b := by
  have hρ : MapsTo (fun t => a + b - t) (Icc a b) (Icc a b) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hc : ContinuousOn y (Icc a b) := fun t ht => (hy t ht).continuousWithinAt
  refine ⟨hc.comp (by fun_prop) hρ, fun t ht => ?_⟩
  have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have h1 : HasDerivWithinAt (fun s => a + b - s) (-1 : ℝ) (Icc a b) t := by
    simpa using ((hasDerivAt_id t).const_sub (a + b)).hasDerivWithinAt
  have h2 := (hy _ (hρ ht')).scomp t h1 hρ
  have h3 : HasDerivWithinAt (fun t => y (a + b - t)) (-G (y (a + b - t))) (Icc a b) t := by
    simpa [Function.comp_def] using h2
  exact h3.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]

/-- **Sec. 3, first step of the Tucker splitting for a square orthogonal factor**
(arXiv 1801.01103, with arXiv 1709.02594, Algorithm 1, lines 3–11).  Let mode one have a square
factor, `r₁ = n₁ = r`, and `Mat₁(C⁰) = S⁰ Qᵀ`.  The K-step solves `K' = G(K)`, `K(t₀) = U⁰ S⁰`;
then `K(t₁) = U¹ Ŝ` with `U¹` orthogonal, and the S-step solves `S' = -U¹ᵀ G(U¹ S)`, `S(t₀) = Ŝ`.
Here `G(K) = Mat₁(F(Ten₁(K Vᵀ))) V` is any Lipschitz map, independent of time: the Vlasov–Poisson
right-hand side is autonomous.  Then the new core `C¹ = S(t₁) Qᵀ` and factor `U¹` represent the same
tensor as before: `U¹ Mat₁(C¹) = U⁰ Mat₁(C⁰)`.  The steps K and S cancel exactly. -/
theorem tucker_square_factor_step {G : Matrix ι ι ℝ → Matrix ι ι ℝ} {Lip : ℝ}
    (hG : ∀ A B, ‖G A - G B‖ ≤ Lip * ‖A - B‖) (hLip : 0 ≤ Lip)
    {K S : ℝ → Matrix ι ι ℝ} {U₀ U₁ S₀ Ŝ : Matrix ι ι ℝ} {C₀ : Matrix ι m ℝ} {Q : Matrix m ι ℝ}
    {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) (hC : C₀ = S₀ * Qᵀ) (hU₁ : U₁ᵀ * U₁ = 1)
    (hK : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt K (G (K t)) (Icc t₀ t₁) t)
    (hK0 : K t₀ = U₀ * S₀) (hK1 : K t₁ = U₁ * Ŝ)
    (hS : ODESolution (fun _ s => -(U₁ᵀ * G (U₁ * s))) S t₀ t₁) (hS0 : S t₀ = Ŝ) :
    U₁ * (S t₁ * Qᵀ) = U₀ * C₀ := by
  have hU₁' : U₁ * U₁ᵀ = 1 := mul_eq_one_comm.mp hU₁
  have h1 : ODESolution (fun _ z => -G z) (fun t => U₁ * S t) t₀ t₁ := by
    refine ⟨?_, fun t ht => ?_⟩
    · exact (Frobenius.leftMulCLM U₁).continuous.comp_continuousOn hS.cont
    · have := Frobenius.hasDerivWithinAt_const_mul U₁ (hS.deriv t ht)
      simpa [Matrix.mul_neg, ← Matrix.mul_assoc, hU₁'] using this
  have h2 := odeSolution_reverse hK
  have hlip : IsLipschitzField (fun (_ : ℝ) z => -G z) Lip := fun _ x y => by
    have h3 : -G x - -G y = -(G x - G y) := by abel
    simp only [h3, norm_neg]
    exact hG x y
  have heq := h1.eqOn h2 hlip hLip (by simp [hS0, hK1])
  have hend := heq (right_mem_Icc.2 h01)
  simp only [add_sub_cancel_right] at hend
  rw [← Matrix.mul_assoc, hend, hK0, hC, Matrix.mul_assoc]

/-- **Sec. 3: "the first step leaves both `C` and `A` (in this case the identity) unchanged"**
(arXiv 1801.01103).  For `A = U⁰ = 1`, `K(t₁) = 1 · K(t₁)` is an admissible decomposition, and with
it the new factor is `U¹ = 1` and the new core is `C¹ = C⁰`.  A QR decomposition with `U¹ ≠ 1` gives
the same tensor by `tucker_square_factor_step`, but then `A` and `C` change by `U¹`: the paper's
claim refers to the trivial decomposition. -/
theorem tucker_identity_factor_unchanged {G : Matrix ι ι ℝ → Matrix ι ι ℝ} {Lip : ℝ}
    (hG : ∀ A B, ‖G A - G B‖ ≤ Lip * ‖A - B‖) (hLip : 0 ≤ Lip)
    {K S : ℝ → Matrix ι ι ℝ} {S₀ : Matrix ι ι ℝ} {C₀ : Matrix ι m ℝ} {Q : Matrix m ι ℝ}
    {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) (hC : C₀ = S₀ * Qᵀ)
    (hK : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt K (G (K t)) (Icc t₀ t₁) t) (hK0 : K t₀ = S₀)
    (hS : ODESolution (fun _ s => -G s) S t₀ t₁) (hS0 : S t₀ = K t₁) :
    S t₁ * Qᵀ = C₀ := by
  have hS' : ODESolution (fun _ s => -((1 : Matrix ι ι ℝ)ᵀ * G (1 * s))) S t₀ t₁ := by
    simpa using hS
  have h := tucker_square_factor_step hG hLip (U₀ := 1) (U₁ := 1) (S₀ := S₀) (Ŝ := K t₁) h01 hC
    (by simp) hK (by simp [hK0]) (by simp) hS' hS0
  simpa using h

/-- **Sec. 3** (arXiv 1801.01103): for a square orthogonal factor `U`, the left projector is the
identity: the tangential projection in that mode is void, and the L-step that remains after the
K- and S-step of mode one is the original equation. -/
theorem leftProj_of_square {n : Type*} [Fintype n] {U : Matrix ι ι ℝ} (hU : Uᵀ * U = 1)
    (Y : Matrix ι n ℝ) : leftProj U Y = Y := by
  rw [leftProj_apply, mul_eq_one_comm.mp hU, Matrix.one_mul]

/-- **Sec. 3, projector form** (arXiv 1801.01103).  In a KSL step for an autonomous `F` with
`P₁ = 1` (square orthogonal factor) and Lipschitz `Q₀ F`, the K- and S-step cancel,
`YS(t₁) = Y₀`, and the L-step solves the unprojected equation `YL' = F(YL)` from `Y₀`: "we can
proceed with the algorithm and work directly in the representation (3.2)". -/
theorem ksl_cancel_of_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → E} {ε Lip : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YS YL : ℝ → E}
    (hs : IsKSLStep (fun _ => F) ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (hP : ∀ x, P₁ x = x) (h01 : t₀ ≤ t₁)
    (hLip : 0 ≤ Lip) (hL : ∀ x y, ‖Q₀ (F x) - Q₀ (F y)‖ ≤ Lip * ‖x - y‖)
    (hK : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt YK (Q₀ (F (YK t))) (Icc t₀ t₁) t) :
    YS t₁ = Y₀ ∧ ODESolution (fun _ => F) YL t₀ t₁ ∧ YL t₀ = Y₀ := by
  have hs1 : ODESolution (fun _ z => -Q₀ (F z)) YS t₀ t₁ := by
    have h := hs.sSol
    simpa only [hP] using h
  have h2 := odeSolution_reverse (G := fun z => Q₀ (F z)) hK
  have hlip : IsLipschitzField (fun (_ : ℝ) z => -Q₀ (F z)) Lip := fun _ x y => by
    have h3 : -Q₀ (F x) - -Q₀ (F y) = -(Q₀ (F x) - Q₀ (F y)) := by abel
    simp only [h3, norm_neg]
    exact hL x y
  have heq := hs1.eqOn h2 hlip hLip (by simp [hs.sStart])
  have hend := heq (right_mem_Icc.2 h01)
  simp only [add_sub_cancel_right, hs.kStart] at hend
  have hl : ODESolution (fun _ => F) YL t₀ t₁ := by
    have h := hs.lSol
    simpa only [hP] using h
  exact ⟨hend, hl, by rw [hs.lStart, hend]⟩

end TuckerStep

/-! ### The rank, the ansatz, the charge and orthonormality in the core vocabulary -/

section KineticCore

variable {d r : ℕ}

/-- **The separation rank through the core**: `HasRankLE f k` of this file is the core
`LeanDLRA.HasSepRankLE` over the ring `ℝ`. -/
theorem hasRankLE_iff_hasSepRankLE {α β : Type*} (f : α → β → ℝ) (k : ℕ) :
    HasRankLE f k ↔ HasSepRankLE ℝ f k := Iff.rfl

/-- **The ansatz through the core**: the separated function `∑_j A_j(x) B_j(v)` is the core
`Kinetic.lowRankAnsatz` with the weight `1` and the identity as coefficient matrix. -/
theorem lowRank_eq_lowRankAnsatz (A B : Fin r → PS d → ℝ) :
    lowRank A B = Kinetic.lowRankAnsatz 1 A 1 B := by
  funext x v
  exact (Kinetic.lowRankAnsatz_one_one A B x v).symm

/-- The separated function with `r` terms has rank at most `r`. -/
theorem hasRankLE_lowRank (A B : Fin r → PS d → ℝ) : HasRankLE (lowRank A B) r :=
  ⟨A, B, fun _ _ => rfl⟩

/-- **The charge through the core**: the charge density is minus the core
`Kinetic.velocityMoment` with the function `1`. -/
theorem charge_eq_neg_velocityMoment (ν : Measure (PS d)) (f : PS d → PS d → ℝ) (x : PS d) :
    charge ν f x = -Kinetic.velocityMoment ν 1 f x := by
  simp [charge, Kinetic.velocityMoment_apply]

/-- **Orthonormality through the core**: `IsOrthonormalL2` of this file is the core
`Kinetic.IsOrthonormalWrt` for families indexed by `Fin r`. -/
theorem isOrthonormalL2_iff_isOrthonormalWrt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X : Fin r → α → ℝ) : IsOrthonormalL2 μ X ↔ Kinetic.IsOrthonormalWrt μ X :=
  ⟨fun h => ⟨h.memLp, h.inner_eq⟩, fun h => ⟨h.memLp, h.inner_eq⟩⟩

/-- The bridges at nonzero data: one term with `A = 2`, `B = 3` has the value `6` and rank at most
`1`; for the Dirac mass at the origin the charge of `f = 2` is `-2`; the constant `1` is
orthonormal for the Dirac mass. -/
example :
    lowRank (d := 1) (fun (_ : Fin 1) _ => 2) (fun _ _ => 3) 0 0 = 6 ∧
      HasSepRankLE ℝ (lowRank (d := 1) (fun (_ : Fin 1) _ => 2) (fun _ _ => 3)) 1 ∧
      charge (d := 1) (Measure.dirac 0) (fun _ _ => 2) 0 = -2 ∧
      IsOrthonormalL2 (Measure.dirac (0 : ℝ)) (fun (_ : Fin 1) (_ : ℝ) => (1 : ℝ)) := by
  refine ⟨?_, (hasRankLE_iff_hasSepRankLE _ 1).1 (hasRankLE_lowRank _ _), ?_, ?_⟩
  · rw [lowRank_eq_lowRankAnsatz, Kinetic.lowRankAnsatz_one_one]
    norm_num
  · rw [charge_eq_neg_velocityMoment, Kinetic.velocityMoment_apply]
    simp
  · rw [isOrthonormalL2_iff_isOrthonormalWrt]
    exact ⟨fun _ => memLp_const 1, fun i j => by simp [Subsingleton.elim i j]⟩

end KineticCore

end LeanDLRA.Literature.P1801_01103
