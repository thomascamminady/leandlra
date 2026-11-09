import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2101.12571: Mass-, momentum- and energy-conservative DLRA for Vlasov

This module formalizes L. Einkemmer, I. Joseph, *A mass, momentum, and energy conservative dynamical
low-rank scheme for the Vlasov equation* (read in arXiv v2).  Vlasov-Poisson is discretized on
arbitrary finite nodes: `Model` holds the quadrature weights of `∫ dx`, `∫ dv`, the weight `f_{0v}`
(`f_{0x} = 1`, as in the paper), `d` velocity directions (the paper's derivations are in `1 + 1`
dimensions, with the extension to `d` announced), skew-adjoint commuting `∂_{x_α}` and arbitrary
linear `∂_{v_α}`, so it covers the fully discrete scheme of Sec. 6.1, and `vlasov` is `D[f]`,
`IsField` the Gauss law.  **Sec. 4, eq. (7)**: `eq7`, the exact defect `rhs7_sub`, the collapse
`rhs7_collapse` for `1 ∈ span V` and its converse `exists_rhs7_ne`; `one_not_memLp`,
`one_notMem_span` for `L²(ℝ^d)`; a state on which the classical scheme really loses mass:
`Ex.classic_not_conservative`.  **Sec. 4, eqs. (8)-(12)**: `petrovGalerkin_iff` says that the
Petrov-Galerkin condition (9) on the tangent space with fixed `U_a` is equivalent to (10), (11),
(12); `test_chi` is the fact `χ U_a ∈ 𝒯_f ℳ` behind conservation; `gramFree_isUnit` is the
invertibility of `T`; and the constraints are derived, not assumed: along (10)-(12) the factors stay
orthonormal and the gauge holds (`IsSolution.isFrame`, `IsSolution.gauge`, by Grönwall, as long as
`S` is invertible), so that (10)-(12) imply (9) with the true `∂ₜ f` (`IsSolution.hasDeriv_lowRank`,
`IsSolution.petrovGalerkin`).  **Sec. 5**: the local laws `IsSolution.rho_law`, `cur_law`,
`dens_law` and the conservation of mass, momentum, energy `IsSolution.mass_eq`, `momentum_eq`,
`energy_eq`, together in `IsSolution.conservation`, in `d` dimensions; on the discrete phase space
exact integration by parts in `v` against `1`, `v`, `v²` is the hypothesis `VelIBP`, on the state.
The same local laws hold in the continuum: in the namespace `Continuum` the phase space is `ℝ × ℝ`,
derivatives and integrals are the true ones, integration by parts is proved from integrability of
the moments of order `≤ 3` (`mom_vlasov`), and `Continuum.IsSolution.rho_law`, `cur_law`, `dens_law`
are `∂ₜ ρ + ∂ₓ j = 0`, `∂ₜ j + ∂ₓ σ = -E ρ`, `∂ₜ e + ∂ₓ Q = E (∂ₜ E - j)`, for `1, v, v² ∈ span U`
and `⟨V_j, U_a⟩_v = δ_ja`, which here is a hypothesis.  Global conservation in the continuum is not
treated.  **Sec. 6.1, eqs. (13)-(16)**: `IsEuler` is the scheme, `IsEuler.colK_eq` eq. (13) in
discrete time, `IsEuler.perp` keeps `⟨W_p, U_a⟩_v = 0`, needing neither orthonormality of `X` or of
the `W_p` among themselves (which the scheme does not keep) nor invertibility of `T`;
`MomStep.rho_eq`, `cur_eq`, `kin_eq`, `mass_eq`, `momentum_eq` are the discrete laws, and
`euler_run`, `euler_reorth_run` (with the re-orthonormalization `IsReorth` of the paper),
`euler_conservation` the statements over many steps.  **Sec. 6.1, eq. (17)**: `MomStep.eq17`, the
defect `MomStep.energy_defect`, its size `MomStep.field_sub_le`, `run_energy_le` (first order
globally: `≤ n τ² J / 2`), `MomStep.energy_eq_iff` (no defect iff `∇ ⋅ j^n = 0`), the midpoint field
`MomStep.energy_midpoint`, the abstract `quadratic_step`, `quadratic_step_defect`; the midpoint rule
for quadratics is `implicitMidpoint_quadratic_eq` in the library, and the abstract cores of the
linear invariants and of the energy defect are in `Stability/Conservation.lean` and
`vp_energy_defect`.  Differences from the paper.  (a) Eq. (15) as printed, with `(S^{n+1})⁻¹_{ik}`,
is a misprint: it gives `X^{n+1} S^{n+1} = K^{n+1}` for all data only for symmetric `S^{n+1}`
(`eq15_as_printed_iff`), so `IsEuler` uses `(S^{n+1})⁻¹_{ki}`.  (b) In the display before (17),
and again in the display for `E^{n+1/2}` on p. 12, `∇ ⋅ Q^n` carries the wrong sign (by
`kin_vlasov`, `½ ∫ v² D[f] dv = -∇ ⋅ Q - E ⋅ j`), which does not matter after integration.  (c) The
paper says that FFT or centered differences with the trapezoidal rule integrate by parts without
error.  On a
truncated velocity grid, against the non-periodic `v`, `v²`, this holds only up to boundary terms
(`not_velIBP_const`), which is why `VelIBP` is a hypothesis on `f` and not on the grid.  (d) With
`E^{n+1/2}` in the update, conservation of momentum is not covered: the field is not the field of
`f^n` there, and the paper does not claim it.  The hypotheses can hold: `exists_isField` solves the
discrete Poisson problem, `exists_isEuler` gives the step for small `τ`, `Ex.exists_energy_growth`
is a concrete instance with three fixed and one evolving function in which the energy strictly
grows, `Ex.isSolution₀` a stationary solution of (10)-(12), and
`Continuum.maxwellian_isSolution` the Maxwellian with the weight and the fixed functions of the
paper.  Not treated: solutions with transport of (10)-(12) (Picard-Lindelöf), Sec. 6.2 (another
slice), and the numerical results of Sec. 7.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace LeanDLRA.Literature.P2101_12571

noncomputable section

/-- A discretized phase space, for `arXiv 2101.12571`: finite nodes in `x` and `v`, with quadrature
weights, the weight `f_{0v}`, velocity coordinates in `d = |δ|` directions, and discrete
derivatives.  In `x` they satisfy exact summation by parts, kill constants and commute, as FFT and
centered differences on a periodic tensor grid do.  In `v` nothing is assumed here; see `VelIBP`. -/
structure Model (Ix Iv δ : Type*) [Fintype Ix] where
  /-- Quadrature weights of `∫ dx`. -/
  hx : Ix → ℝ
  /-- Quadrature weights of `∫ dv`. -/
  hv : Iv → ℝ
  /-- The weight `f_{0v}`. -/
  f0 : Iv → ℝ
  /-- The velocity coordinates. -/
  vel : δ → Iv → ℝ
  /-- The discrete derivatives `∂_{x_α}`. -/
  dx : δ → (Ix → ℝ) →ₗ[ℝ] Ix → ℝ
  /-- The discrete derivatives `∂_{v_α}`. -/
  dv : δ → (Iv → ℝ) →ₗ[ℝ] Iv → ℝ
  hx_pos : ∀ x, 0 < hx x
  hv_pos : ∀ v, 0 < hv v
  f0_pos : ∀ v, 0 < f0 v
  dx_skew : ∀ α (u w : Ix → ℝ), ∑ x, hx x * (u x * dx α w x) = -∑ x, hx x * (dx α u x * w x)
  dx_const : ∀ α, dx α (fun _ => 1) = 0
  dx_comm : ∀ α β (u : Ix → ℝ), dx α (dx β u) = dx β (dx α u)

namespace Model

variable {Ix Iv δ : Type*} [Fintype Ix] [Fintype Iv] [Fintype δ] (M : Model Ix Iv δ)

/-- `(φ, G)_v`, a function of `x`.  Unweighted, as in the paper. -/
def mom (φ : Iv → ℝ) (G : Ix → Iv → ℝ) (x : Ix) : ℝ := ∑ v, M.hv v * (φ v * G x v)

/-- `(u, G)_x`, a function of `v`. -/
def momX (u : Ix → ℝ) (G : Ix → Iv → ℝ) (v : Iv) : ℝ := ∑ x, M.hx x * (u x * G x v)

/-- `(u φ, G)_{xv}`. -/
def pair (u : Ix → ℝ) (φ : Iv → ℝ) (G : Ix → Iv → ℝ) : ℝ := ∑ x, M.hx x * (u x * M.mom φ G x)

/-- `⟨u, w⟩_x`. -/
def ipx (u w : Ix → ℝ) : ℝ := ∑ x, M.hx x * (u x * w x)

/-- The weighted `⟨g, h⟩_v = ∫ f_{0v} g h dv`. -/
def ipv (g h : Iv → ℝ) : ℝ := ∑ v, M.hv v * (M.f0 v * (g v * h v))

/-- `v²`. -/
def vsq (v : Iv) : ℝ := ∑ α, M.vel α v ^ 2

/-- `ρ = ∫ f dv`. -/
def rho (f : Ix → Iv → ℝ) : Ix → ℝ := M.mom (fun _ => 1) f

/-- `j = ∫ v f dv`. -/
def cur (f : Ix → Iv → ℝ) (α : δ) : Ix → ℝ := M.mom (M.vel α) f

/-- `σ = ∫ v ⊗ v f dv`. -/
def sig (f : Ix → Iv → ℝ) (α β : δ) : Ix → ℝ := M.mom (fun v => M.vel α v * M.vel β v) f

/-- The kinetic energy density `½ ∫ v² f dv`. -/
def kin (f : Ix → Iv → ℝ) : Ix → ℝ := fun x => (1 / 2) * M.mom M.vsq f x

/-- `Q = ½ ∫ v v² f dv`. -/
def heat (f : Ix → Iv → ℝ) (α : δ) : Ix → ℝ :=
  fun x => (1 / 2) * M.mom (fun v => M.vel α v * M.vsq v) f x

/-- `D[f] = -v ⋅ ∇ₓ f + E ⋅ ∇ᵥ f`. -/
def vlasov (E : δ → Ix → ℝ) (f : Ix → Iv → ℝ) : Ix → Iv → ℝ := fun x v =>
  -∑ α, M.vel α v * M.dx α (fun y => f y v) x + ∑ α, E α x * M.dv α (f x) v

/-- The energy density `e = ½ ∫ v² f dv + ½ E²`. -/
def dens (f : Ix → Iv → ℝ) (E : δ → Ix → ℝ) (x : Ix) : ℝ :=
  M.kin f x + (1 / 2) * ∑ α, E α x ^ 2

/-- The mass `M = ∫∫ f dv dx`. -/
def mass (f : Ix → Iv → ℝ) : ℝ := ∑ x, M.hx x * M.rho f x

/-- The momentum `J = ∫∫ v f dv dx`. -/
def momentum (f : Ix → Iv → ℝ) (α : δ) : ℝ := ∑ x, M.hx x * M.cur f α x

/-- The total energy `ℰ = ∫ e dx`. -/
def energy (f : Ix → Iv → ℝ) (E : δ → Ix → ℝ) : ℝ := ∑ x, M.hx x * M.dens f E x

/-- Exact integration by parts of `g` in `v` against `1`, `v`, `v²`.  In the paper this is the
statement that the discretization integrates by parts without error; the continuum case is
proved, `Continuum.mom_vlasov`.  It holds for all `g`, for instance, for the weak derivative of
`Ex.dv` (`Ex.velIBP`). -/
structure VelIBP [DecidableEq δ] (g : Iv → ℝ) : Prop where
  one : ∀ α, ∑ v, M.hv v * M.dv α g v = 0
  vel : ∀ α β, ∑ v, M.hv v * (M.vel β v * M.dv α g v) = -(if α = β then ∑ v, M.hv v * g v else 0)
  sq : ∀ α, ∑ v, M.hv v * (M.vsq v * M.dv α g v) = -2 * ∑ v, M.hv v * (M.vel α v * g v)

/-- The discrete Gauss law `∇ ⋅ E = 1 - ρ`, `E = -∇ φ`. -/
structure IsField (ρ : Ix → ℝ) (E : δ → Ix → ℝ) (φ : Ix → ℝ) : Prop where
  grad : ∀ α, E α = -M.dx α φ
  gauss : ∀ x, ∑ α, M.dx α (E α) x = 1 - ρ x

variable {M}

lemma dx_mom (α : δ) (ψ : Iv → ℝ) (f : Ix → Iv → ℝ) (x : Ix) :
    M.dx α (M.mom ψ f) x = ∑ v, M.hv v * (ψ v * M.dx α (fun y => f y v) x) := by
  have h : M.mom ψ f = ∑ v, (M.hv v * ψ v) • (fun y => f y v) := by
    ext y
    simp [mom, Finset.sum_apply, mul_assoc]
  rw [h, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

lemma mom_vlasov (φ : Iv → ℝ) (E : δ → Ix → ℝ) (f : Ix → Iv → ℝ) (x : Ix) :
    M.mom φ (M.vlasov E f) x = -∑ α, M.dx α (M.mom (fun v => M.vel α v * φ v) f) x
      + ∑ α, E α x * ∑ v, M.hv v * (φ v * M.dv α (f x) v) := by
  simp only [dx_mom]
  simp only [mom, vlasov]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun v _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun v _ => by ring

section Flux
variable [DecidableEq δ] {E : δ → Ix → ℝ} {f : Ix → Iv → ℝ} {x : Ix}

/-- `∫ D[f] dv = -∇ ⋅ j`. -/
lemma rho_vlasov (h : M.VelIBP (f x)) : M.rho (M.vlasov E f) x = -∑ α, M.dx α (M.cur f α) x := by
  have := mom_vlasov (M := M) (fun _ => 1) E f x
  simp only [one_mul, mul_one, h.one, mul_zero, Finset.sum_const_zero, add_zero] at this
  exact this

/-- `∫ v D[f] dv = -∇ ⋅ σ - E ρ`. -/
lemma cur_vlasov (h : M.VelIBP (f x)) (β : δ) :
    M.cur (M.vlasov E f) β x = -∑ α, M.dx α (M.sig f α β) x - E β x * M.rho f x := by
  have := mom_vlasov (M := M) (M.vel β) E f x
  simp only [h.vel] at this
  simp only [cur, sig, rho, mom] at this ⊢
  rw [this, sub_eq_add_neg]
  congr 1
  simp [mul_ite]

/-- `½ ∫ v² D[f] dv = -∇ ⋅ Q - E ⋅ j`. -/
lemma kin_vlasov (h : M.VelIBP (f x)) :
    M.kin (M.vlasov E f) x = -∑ α, M.dx α (M.heat f α) x - ∑ α, E α x * M.cur f α x := by
  have := mom_vlasov (M := M) M.vsq E f x
  simp only [h.sq] at this
  have e : ∀ α, M.dx α (M.heat f α) x
      = (1 / 2) * M.dx α (M.mom (fun v => M.vel α v * M.vsq v) f) x := by
    intro α
    have : M.heat f α = (1 / 2 : ℝ) • M.mom (fun v => M.vel α v * M.vsq v) f := by
      ext y; simp [heat]
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul]
  simp only [e]
  rw [kin, this, ← Finset.mul_sum]
  simp only [cur, mom]
  have e2 : ∑ α, E α x * (-2 * ∑ v, M.hv v * (M.vel α v * f x v))
      = -2 * ∑ α, E α x * ∑ v, M.hv v * (M.vel α v * f x v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => by ring
  rw [e2]
  ring

end Flux

/-- A discrete divergence integrates to zero. -/
lemma sum_dx (α : δ) (u : Ix → ℝ) : ∑ x, M.hx x * M.dx α u x = 0 := by
  have := M.dx_skew α (fun _ => 1) u
  simp only [one_mul, M.dx_const, Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
    neg_zero] at this
  exact this

/-- `∑ u ∂ u = 0`. -/
lemma sum_mul_dx_self (α : δ) (u : Ix → ℝ) : ∑ x, M.hx x * (u x * M.dx α u x) = 0 := by
  have := M.dx_skew α u u
  have e : ∑ x, M.hx x * (M.dx α u x * u x) = ∑ x, M.hx x * (u x * M.dx α u x) :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [e] at this
  linarith

/-- A gradient is orthogonal to a divergence-free field: `∫ ∇ψ ⋅ Y = -∫ ψ ∇ ⋅ Y`. -/
lemma sum_grad_mul (ψ : Ix → ℝ) (Y : δ → Ix → ℝ) :
    ∑ x, M.hx x * ∑ α, M.dx α ψ x * Y α x = -∑ x, M.hx x * (ψ x * ∑ α, M.dx α (Y α) x) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [M.dx_skew α ψ (Y α), neg_neg]

/-- The electric field has mean zero, `∫ E dx = 0`. -/
lemma IsField.sum_field {ρ : Ix → ℝ} {E : δ → Ix → ℝ} {φ : Ix → ℝ} (h : M.IsField ρ E φ) (β : δ) :
    ∑ x, M.hx x * E β x = 0 := by
  rw [h.grad β]
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sum_dx, neg_zero]

/-- The force on the plasma vanishes: `∫ E ρ dx = 0`. -/
lemma IsField.sum_force {ρ : Ix → ℝ} {E : δ → Ix → ℝ} {φ : Ix → ℝ} (h : M.IsField ρ E φ) (β : δ) :
    ∑ x, M.hx x * (E β x * ρ x) = 0 := by
  have hρ : ∀ x, ρ x = 1 - ∑ α, M.dx α (E α) x := fun x => by rw [h.gauss x]; ring
  have key : ∑ x, M.hx x * (E β x * ∑ α, M.dx α (E α) x) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α _ => ?_
    have h1 : ∀ x, E β x = -M.dx β φ x := fun x => by rw [h.grad β]; rfl
    have h2 := M.dx_skew α (M.dx β φ) (M.dx α φ)
    have h3 := sum_mul_dx_self (M := M) β (M.dx α φ)
    have h4 : M.dx α (M.dx β φ) = M.dx β (M.dx α φ) := M.dx_comm α β φ
    rw [h4] at h2
    have h5 : ∑ x, M.hx x * (M.dx β (M.dx α φ) x * M.dx α φ x)
        = ∑ x, M.hx x * (M.dx α φ x * M.dx β (M.dx α φ) x) :=
      Finset.sum_congr rfl fun x _ => by ring
    rw [h5, h3, neg_zero] at h2
    have h6 : ∑ x, M.hx x * (E β x * M.dx α (E α) x)
        = ∑ x, M.hx x * (M.dx β φ x * M.dx α (M.dx α φ) x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [h1 x, h.grad α, map_neg, Pi.neg_apply]
      ring
    rw [h6]
    exact h2
  have e : ∑ x, M.hx x * (E β x * ρ x)
      = ∑ x, M.hx x * E β x - ∑ x, M.hx x * (E β x * ∑ α, M.dx α (E α) x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hρ x]
    ring
  rw [e, h.sum_field β, key, sub_zero]

/-! ### The low-rank ansatz and the fixed basis functions -/

section Ansatz

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `K_j = ∑_i X_i S_ij`. -/
def colK {Ix : Type*} (X : ι → Ix → ℝ) (S : Matrix ι κ ℝ) (j : κ) (x : Ix) : ℝ :=
  ∑ i, X i x * S i j

variable (M) in
/-- The ansatz (8), `f = f_{0v} ∑_ij X_i S_ij V_j`. -/
def lowRank (X : ι → Ix → ℝ) (S : Matrix ι κ ℝ) (V : κ → Iv → ℝ) : Ix → Iv → ℝ :=
  fun x v => M.f0 v * ∑ i, ∑ j, X i x * S i j * V j v

lemma lowRank_eq (X : ι → Ix → ℝ) (S : Matrix ι κ ℝ) (V : κ → Iv → ℝ) (x : Ix) (v : Iv) :
    M.lowRank X S V x v = M.f0 v * ∑ j, colK X S j x * V j v := by
  simp only [lowRank, colK, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma mom_lowRank (φ : Iv → ℝ) (X : ι → Ix → ℝ) (S : Matrix ι κ ℝ) (V : κ → Iv → ℝ) (x : Ix) :
    M.mom φ (M.lowRank X S V) x = ∑ j, colK X S j x * M.ipv (V j) φ := by
  simp only [mom, lowRank_eq, ipv, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => by ring

end Ansatz

variable {A P : Type*} [Fintype A] [Fintype P] [DecidableEq A] [DecidableEq P]

/-- The basis `V = (U_a, W_p)`: fixed functions first, evolving functions second. -/
abbrev basis (U : A → Iv → ℝ) (W : P → Iv → ℝ) : A ⊕ P → Iv → ℝ := Sum.elim U W

variable (M) in
/-- The fixed functions are orthonormal in `⟨·, ·⟩_v`. -/
def FixedOrtho (U : A → Iv → ℝ) : Prop :=
  ∀ a b, M.ipv (U a) (U b) = if a = b then 1 else 0

/-- `φ` lies in `span {U_a}`. -/
def InSpan (U : A → Iv → ℝ) (φ : Iv → ℝ) : Prop := ∃ c : A → ℝ, ∀ v, φ v = ∑ a, c a * U a v

variable (M) in
/-- `1`, `v`, `v²` lie in `span {U_a}`: for `U_1 ∝ 1`, `U_2 ∝ v`, `U_3 ∝ v² - 1` in `1 + 1`
dimensions, and in `d` dimensions for one function per component of `v`. -/
structure Conserves (U : A → Iv → ℝ) : Prop where
  one : InSpan U (fun _ => 1)
  vel : ∀ α, InSpan U (M.vel α)
  sq : InSpan U M.vsq

lemma mom_inSpan {U : A → Iv → ℝ} {φ : Iv → ℝ} {c : A → ℝ} (hc : ∀ v, φ v = ∑ a, c a * U a v)
    (G : Ix → Iv → ℝ) (x : Ix) : M.mom φ G x = ∑ a, c a * M.mom (U a) G x := by
  simp only [mom, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ => by ring

/-- The moment against a fixed function is a column of `K`, which is why these are the conserved
quantities: `(U_a, f)_v = K_a`. -/
lemma mom_fixed {U : A → Iv → ℝ} {W : P → Iv → ℝ} (hU : M.FixedOrtho U)
    (hW : ∀ p a, M.ipv (W p) (U a) = 0) {ι : Type*} [Fintype ι] (X : ι → Ix → ℝ)
    (S : Matrix ι (A ⊕ P) ℝ) (a : A) (x : Ix) :
    M.mom (U a) (M.lowRank X S (basis U W)) x = colK X S (Sum.inl a) x := by
  have hU' : ∀ b, M.ipv (U b) (U a) = if b = a then 1 else 0 := fun b => hU b a
  rw [mom_lowRank, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hW, hU', mul_zero, Finset.sum_const_zero, add_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable (M) in
/-- A step that advances the moments against all fixed functions by `τ (U_a, G)_v`. -/
def MomStep (U : A → Iv → ℝ) (τ : ℝ) (G f f' : Ix → Iv → ℝ) : Prop :=
  ∀ a x, M.mom (U a) f' x = M.mom (U a) f x + τ * M.mom (U a) G x

variable (M) in
/-- A step of the factors which keeps `⟨W_p, U_a⟩_v = 0` and in which the columns `K_a` of the fixed
functions follow explicit Euler.  This is all that the conservation laws use of the scheme. -/
structure IsBalanced (U : A → Iv → ℝ) (τ : ℝ) (G : Ix → Iv → ℝ)
    (X X' : A ⊕ P → Ix → ℝ) (S S' : Matrix (A ⊕ P) (A ⊕ P) ℝ) (W' : P → Iv → ℝ) : Prop where
  perp : ∀ p a, M.ipv (W' p) (U a) = 0
  col : ∀ a x, colK X' S' (Sum.inl a) x = colK X S (Sum.inl a) x + τ * M.mom (U a) G x

lemma IsBalanced.momStep {U : A → Iv → ℝ} {τ : ℝ} {G : Ix → Iv → ℝ} {X X' : A ⊕ P → Ix → ℝ}
    {S S' : Matrix (A ⊕ P) (A ⊕ P) ℝ} {W W' : P → Iv → ℝ}
    (h : M.IsBalanced U τ G X X' S S' W') (hU : M.FixedOrtho U)
    (hW : ∀ p a, M.ipv (W p) (U a) = 0) :
    M.MomStep U τ G (M.lowRank X S (basis U W)) (M.lowRank X' S' (basis U W')) := by
  intro a x
  rw [mom_fixed hU h.perp, mom_fixed hU hW, h.col]

/-! ### The conservative Euler scheme -/

/-- The block `T_qp = ∑_i S_iq S_ip`, `p, q` free indices, of eqs. (11) and (16). -/
def gramFree (S : Matrix (A ⊕ P) (A ⊕ P) ℝ) : Matrix P P ℝ :=
  fun q p => ∑ i, S i (Sum.inr q) * S i (Sum.inr p)

variable (M) in
/-- The bracket of eq. (16),
`(X_i, G)_x / f_{0v} - ∑_l (X_i V_l, G)_{xv} V_l`. -/
def freeRhs (X : A ⊕ P → Ix → ℝ) (V : A ⊕ P → Iv → ℝ) (G : Ix → Iv → ℝ) (i : A ⊕ P) (v : Iv) : ℝ :=
  M.momX (X i) G v / M.f0 v - ∑ l, M.pair (X i) (V l) G * V l v

variable (M) in
/-- One step of the scheme (14)-(16), with right-hand side `G`.  In (15) the inverse carries the
indices `(S⁻¹)_{ki}`: the paper prints `(S⁻¹)_{ik}`, see `eq15_as_printed_iff`. -/
structure IsEuler (U : A → Iv → ℝ) (τ : ℝ) (G : Ix → Iv → ℝ)
    (X X' : A ⊕ P → Ix → ℝ) (S S' : Matrix (A ⊕ P) (A ⊕ P) ℝ) (W W' : P → Iv → ℝ) : Prop where
  s_step : ∀ k l, S' k l = S k l + τ * M.pair (X k) (basis U W l) G
  x_step : ∀ i x, X' i x = ∑ k, S'⁻¹ k i * (colK X S k x + τ * M.mom (basis U W k) G x)
  w_step : ∀ p v, W' p v = W p v
    + τ * ∑ q, ∑ i, (gramFree S)⁻¹ p q * S i (Sum.inr q) * M.freeRhs X (basis U W) G i v

lemma pair_eq_sum (u : Ix → ℝ) (φ : Iv → ℝ) (G : Ix → Iv → ℝ) :
    M.pair u φ G = ∑ v, M.hv v * (φ v * M.momX u G v) := by
  simp only [pair, mom, momX, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun x _ => by ring

lemma ipv_comm (g h : Iv → ℝ) : M.ipv g h = M.ipv h g :=
  Finset.sum_congr rfl fun v _ => by ring

/-- `⟨(u, G)_x / f_{0v}, φ⟩_v = (u φ, G)_{xv}`. -/
lemma ipv_momX (u : Ix → ℝ) (φ : Iv → ℝ) (G : Ix → Iv → ℝ) :
    M.ipv (fun v => M.momX u G v / M.f0 v) φ = M.pair u φ G := by
  rw [pair_eq_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have := (M.f0_pos v).ne'
  field_simp

/-- The bracket of (16) is orthogonal to the basis, if the basis is. -/
lemma ipv_freeRhs {V : A ⊕ P → Iv → ℝ} {φ : Iv → ℝ} {k : A ⊕ P}
    (hφ : ∀ l, M.ipv (V l) φ = if l = k then 1 else 0) (hk : φ = V k)
    (X : A ⊕ P → Ix → ℝ) (G : Ix → Iv → ℝ) (i : A ⊕ P) :
    M.ipv (M.freeRhs X V G i) φ = 0 := by
  have e : ∀ v, M.hv v * (M.f0 v * (M.freeRhs X V G i v * φ v))
      = M.hv v * (M.f0 v * (M.momX (X i) G v / M.f0 v * φ v))
        - ∑ l, M.pair (X i) (V l) G * (M.hv v * (M.f0 v * (V l v * φ v))) := by
    intro v
    simp only [freeRhs, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => by ring
  have e2 : M.ipv (M.freeRhs X V G i) φ = M.ipv (fun v => M.momX (X i) G v / M.f0 v) φ
      - ∑ l, M.pair (X i) (V l) G * M.ipv (V l) φ := by
    simp only [ipv, e, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [e2, ipv_momX]
  simp only [hφ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hk]
  exact sub_self _

lemma ipv_update (W₀ : Iv → ℝ) (τ : ℝ) {Q R : Type*} [Fintype Q] [Fintype R] (c : Q → R → ℝ)
    (B : R → Iv → ℝ) (φ W₁ : Iv → ℝ) (hW₁ : ∀ v, W₁ v = W₀ v + τ * ∑ q, ∑ i, c q i * B i v) :
    M.ipv W₁ φ = M.ipv W₀ φ + τ * ∑ q, ∑ i, c q i * M.ipv (B i) φ := by
  have e : ∀ v, M.hv v * (M.f0 v * (W₁ v * φ v)) = M.hv v * (M.f0 v * (W₀ v * φ v))
      + τ * ∑ q, ∑ i, c q i * (M.hv v * (M.f0 v * (B i v * φ v))) := by
    intro v
    have e1 : ∑ q, ∑ i, c q i * (M.hv v * (M.f0 v * (B i v * φ v)))
        = M.hv v * M.f0 v * φ v * ∑ q, ∑ i, c q i * B i v := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hW₁ v]
    ring
  simp only [ipv, e, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

section Euler

variable {U : A → Iv → ℝ} {τ : ℝ} {G : Ix → Iv → ℝ} {X X' : A ⊕ P → Ix → ℝ}
  {S S' : Matrix (A ⊕ P) (A ⊕ P) ℝ} {W W' : P → Iv → ℝ}

/-- Eq. (15) says `∑_i X_i^{n+1} S_ik^{n+1} = K_k^n + τ (V_k, G)_v`, the conservative form (13) in
discrete time. -/
lemma IsEuler.colK_eq (h : M.IsEuler U τ G X X' S S' W W') (hS' : IsUnit S'.det) (k : A ⊕ P)
    (x : Ix) : colK X' S' k x = colK X S k x + τ * M.mom (basis U W k) G x := by
  have hinv : S'⁻¹ * S' = 1 := Matrix.nonsing_inv_mul _ hS'
  obtain ⟨R, hR⟩ : ∃ R : A ⊕ P → ℝ, R = fun k => colK X S k x + τ * M.mom (basis U W k) G x :=
    ⟨_, rfl⟩
  have e : ∀ i, X' i x = ∑ m, S'⁻¹ m i * R m := fun i => by rw [h.x_step i x, hR]
  have e2 : colK X' S' k x = ∑ m, R m * (S'⁻¹ * S') m k := by
    simp only [colK, e, Finset.sum_mul, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
  rw [e2, hinv]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, hR]

/-- `⟨W_p, U_a⟩_v = 0` is kept exactly by eq. (16): no invertibility, no orthonormality of `X` or
of the `W_p` among themselves is needed. -/
lemma IsEuler.perp (h : M.IsEuler U τ G X X' S S' W W') (hU : M.FixedOrtho U)
    (hW : ∀ p a, M.ipv (W p) (U a) = 0) (p : P) (a : A) : M.ipv (W' p) (U a) = 0 := by
  have hφ : ∀ l, M.ipv (basis U W l) (U a) = if l = Sum.inl a then 1 else 0 := by
    rintro (b | q)
    · simpa using hU b a
    · simpa using hW q a
  have e := ipv_update (M := M) (W p) τ (fun q i => (gramFree S)⁻¹ p q * S i (Sum.inr q))
    (M.freeRhs X (basis U W) G) (U a) (W' p) (fun v => h.w_step p v)
  rw [e, hW]
  simp [ipv_freeRhs (k := Sum.inl a) hφ rfl]

/-- The scheme is balanced. -/
lemma IsEuler.isBalanced (h : M.IsEuler U τ G X X' S S' W W') (hS' : IsUnit S'.det)
    (hU : M.FixedOrtho U) (hW : ∀ p a, M.ipv (W p) (U a) = 0) :
    M.IsBalanced U τ G X X' S S' W' :=
  ⟨h.perp hU hW, fun a x => by simpa using h.colK_eq hS' (Sum.inl a) x⟩

end Euler

/-- The re-orthonormalization that the paper applies at the end of a step: `W = W' R` with `R`
invertible, compensated in the free columns of `S`. -/
structure IsReorth (R : Matrix P P ℝ) (S S' : Matrix (A ⊕ P) (A ⊕ P) ℝ) (W W' : P → Iv → ℝ) :
    Prop where
  unit : IsUnit R.det
  w : ∀ p v, W p v = ∑ q, W' q v * R q p
  s_fixed : ∀ i a, S' i (Sum.inl a) = S i (Sum.inl a)
  s_free : ∀ i q, S' i (Sum.inr q) = ∑ p, S i (Sum.inr p) * R q p

section Reorth

variable {U : A → Iv → ℝ} {R : Matrix P P ℝ} {S S' : Matrix (A ⊕ P) (A ⊕ P) ℝ}
  {W W' : P → Iv → ℝ}

/-- Re-orthonormalization does not change `f`. -/
lemma IsReorth.lowRank_eq (h : IsReorth R S S' W W') (X : A ⊕ P → Ix → ℝ) :
    M.lowRank X S' (basis U W') = M.lowRank X S (basis U W) := by
  have key : ∀ x v i,
      ∑ j, X i x * S' i j * basis U W' j v = ∑ j, X i x * S i j * basis U W j v := by
    intro x v i
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, h.s_fixed, h.s_free, h.w]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  ext x v
  simp only [lowRank, key]

/-- Re-orthonormalization keeps a balanced step balanced: the new `W'` stay orthogonal to `U`. -/
lemma IsBalanced.reorth {τ : ℝ} {G : Ix → Iv → ℝ} {X X' : A ⊕ P → Ix → ℝ}
    {S₀ : Matrix (A ⊕ P) (A ⊕ P) ℝ} (hb : M.IsBalanced U τ G X X' S₀ S W)
    (h : IsReorth R S S' W W') : M.IsBalanced U τ G X X' S₀ S' W' := by
  refine ⟨fun m a => ?_, fun a x => ?_⟩
  · have hinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ h.unit
    have e : ∀ v, W' m v = ∑ p, W p v * R⁻¹ p m := by
      intro v
      have e1 : ∑ p, W p v * R⁻¹ p m = ∑ q, W' q v * (R * R⁻¹) q m := by
        simp only [h.w, Finset.sum_mul, Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
      rw [e1, hinv]
      simp [Matrix.one_apply]
    have e2 := ipv_update (M := M) 0 1 (fun (_ : Unit) p => R⁻¹ p m) W (U a) (W' m)
      (fun v => by simp [e v, mul_comm])
    have e3 : M.ipv 0 (U a) = 0 := by simp [ipv]
    rw [e2, e3]
    simp [hb.perp]
  · have : colK X' S' (Sum.inl a) x = colK X' S (Sum.inl a) x := by simp [colK, h.s_fixed]
    rw [this, hb.col]

end Reorth

/-! ### The discrete conservation laws -/

section Laws

variable {U : A → Iv → ℝ} {τ : ℝ} {Em E E' : δ → Ix → ℝ} {f f' : Ix → Iv → ℝ} {G : Ix → Iv → ℝ}

lemma MomStep.mom_eq (h : M.MomStep U τ G f f') {φ : Iv → ℝ} (hφ : InSpan U φ) (x : Ix) :
    M.mom φ f' x = M.mom φ f x + τ * M.mom φ G x := by
  obtain ⟨c, hc⟩ := hφ
  simp only [mom_inSpan hc, h _ _, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => by ring

variable [DecidableEq δ]

/-- The discrete continuity equation, `(ρ^{n+1} - ρ^n)/τ + ∇ ⋅ j^n = 0`. -/
lemma MomStep.rho_eq (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (x : Ix) :
    M.rho f' x = M.rho f x - τ * ∑ α, M.dx α (M.cur f α) x := by
  have e : M.rho f' x = M.rho f x + τ * M.rho (M.vlasov Em f) x := h.mom_eq hc.one x
  rw [e, rho_vlasov (hI x)]
  ring

/-- The discrete momentum equation, `(j^{n+1} - j^n)/τ + ∇ ⋅ σ^n = -E ρ^n`. -/
lemma MomStep.cur_eq (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (β : δ) (x : Ix) :
    M.cur f' β x = M.cur f β x - τ * (∑ α, M.dx α (M.sig f α β) x + Em β x * M.rho f x) := by
  have e : M.cur f' β x = M.cur f β x + τ * M.cur (M.vlasov Em f) β x := h.mom_eq (hc.vel β) x
  rw [e, cur_vlasov (hI x)]
  ring

/-- The discrete kinetic energy equation,
`(κ^{n+1} - κ^n)/τ + ∇ ⋅ Q^n = -E ⋅ j^n`. -/
lemma MomStep.kin_eq (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (x : Ix) :
    M.kin f' x = M.kin f x
      - τ * (∑ α, M.dx α (M.heat f α) x + ∑ α, Em α x * M.cur f α x) := by
  have e : M.kin f' x = M.kin f x + τ * M.kin (M.vlasov Em f) x := by
    simp only [kin, h.mom_eq hc.sq x]
    ring
  rw [e, kin_vlasov (hI x)]
  ring

/-- Conservation of mass. -/
lemma MomStep.mass_eq (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) : M.mass f' = M.mass f := by
  simp only [mass, h.rho_eq hc hI, mul_sub, Finset.sum_sub_distrib]
  have : ∑ x, M.hx x * (τ * ∑ α, M.dx α (M.cur f α) x) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α _ => ?_
    have := sum_dx (M := M) α (M.cur f α)
    calc _ = τ * ∑ x, M.hx x * M.dx α (M.cur f α) x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [this, mul_zero]
  rw [this, sub_zero]

/-- Conservation of momentum, if the field of the kinetic update is the field of `f`. -/
lemma MomStep.momentum_eq (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) {φ : Ix → ℝ} (hF : M.IsField (M.rho f) Em φ) (β : δ) :
    M.momentum f' β = M.momentum f β := by
  simp only [momentum, h.cur_eq hc hI]
  have e : ∑ x, M.hx x * (τ * (∑ α, M.dx α (M.sig f α β) x + Em β x * M.rho f x)) = 0 := by
    have e1 : ∀ x, M.hx x * (τ * (∑ α, M.dx α (M.sig f α β) x + Em β x * M.rho f x))
        = τ * ∑ α, M.hx x * M.dx α (M.sig f α β) x + τ * (M.hx x * (Em β x * M.rho f x)) := by
      intro x
      rw [← Finset.mul_sum]
      ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, hF.sum_force β, mul_zero, add_zero]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, sum_dx]
  simp only [mul_sub, Finset.sum_sub_distrib, e, sub_zero]

/-- The energy balance of one step: the fluxes integrate to zero, so
`ℰ' - ℰ = ∫ (½ (E'² - E²) - τ Em ⋅ j) dx`. -/
lemma MomStep.energy_sub (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) :
    M.energy f' E' - M.energy f E
      = ∑ x, M.hx x * ∑ α, ((1 / 2) * (E' α x ^ 2 - E α x ^ 2) - τ * (Em α x * M.cur f α x)) := by
  have e0 : ∑ x, M.hx x * (τ * ∑ α, M.dx α (M.heat f α) x) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α _ => ?_
    have := sum_dx (M := M) α (M.heat f α)
    calc _ = τ * ∑ x, M.hx x * M.dx α (M.heat f α) x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have e1 : ∀ x, M.hx x * M.dens f' E' x - M.hx x * M.dens f E x
      = M.hx x * ∑ α, ((1 / 2) * (E' α x ^ 2 - E α x ^ 2) - τ * (Em α x * M.cur f α x))
        - M.hx x * (τ * ∑ α, M.dx α (M.heat f α) x) := by
    intro x
    simp only [dens, h.kin_eq hc hI x, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  simp only [energy]
  rw [← Finset.sum_sub_distrib]
  simp only [e1, Finset.sum_sub_distrib, e0, sub_zero]

end Laws

section Energy

variable [DecidableEq δ] {U : A → Iv → ℝ} {τ : ℝ} {Em E E' Eg : δ → Ix → ℝ} {f f' : Ix → Iv → ℝ}
  {φ φ' ψ : Ix → ℝ}

/-- The discrete Ampère law: for fields `E`, `E'` of `f`, `f'` the field `E' - E - τ j` is
divergence free, hence orthogonal to every gradient.  This is the discrete Gauss law step that makes
the first term of eq. (17) vanish. -/
lemma MomStep.work_eq_zero (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (hF : M.IsField (M.rho f) E φ) (hF' : M.IsField (M.rho f') E' φ')
    (hψ : ∀ α, Eg α = -M.dx α ψ) :
    ∑ x, M.hx x * ∑ α, Eg α x * (E' α x - E α x - τ * M.cur f α x) = 0 := by
  obtain ⟨Y, hY⟩ : ∃ Y : δ → Ix → ℝ, Y = fun α => E' α - E α - τ • M.cur f α := ⟨_, rfl⟩
  have hdiv : ∀ x, ∑ α, M.dx α (Y α) x = 0 := by
    intro x
    simp only [hY, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hF'.gauss x, hF.gauss x, h.rho_eq hc hI x]
    ring
  have e := sum_grad_mul (M := M) ψ Y
  simp only [hdiv, mul_zero, Finset.sum_const_zero, neg_zero] at e
  have e2 : ∑ x, M.hx x * ∑ α, Eg α x * (E' α x - E α x - τ * M.cur f α x)
      = -∑ x, M.hx x * ∑ α, M.dx α ψ x * Y α x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    simp [hψ α, hY]
  rw [e2, e, neg_zero]

/-- **Sec. 6.1, eq. (17)** (arXiv 2101.12571), on the discrete phase space: for the explicit Euler
step with field `E`, `ℰ^{n+1} - ℰ^n = τ ∫ E^n ⋅ ((E^{n+1} - E^n)/τ - j^n) dx + ½ ∫ (E^{n+1} - E^n)²
dx`.  The only thing used of `E^{n+1}` is that it is a function. -/
theorem MomStep.eq17 (h : M.MomStep U τ (M.vlasov E f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (hτ : τ ≠ 0) :
    M.energy f' E' - M.energy f E
      = τ * ∑ x, M.hx x * ∑ α, E α x * ((E' α x - E α x) / τ - M.cur f α x)
        + (1 / 2) * ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2 := by
  rw [h.energy_sub (E := E) (E' := E') hc hI]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  field_simp
  ring

/-- **Sec. 6.1, energy defect** (arXiv 2101.12571), on the discrete phase space: by the discrete
Gauss law the first term of (17) vanishes, so the total energy changes per step by exactly
`½ ∫ (E^{n+1} - E^n)² dx ≥ 0`. -/
theorem MomStep.energy_defect (h : M.MomStep U τ (M.vlasov E f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (hF : M.IsField (M.rho f) E φ) (hF' : M.IsField (M.rho f') E' φ') :
    M.energy f' E' - M.energy f E = (1 / 2) * ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2 := by
  have w := h.work_eq_zero (Eg := E) hc hI hF hF' hF.grad
  rw [h.energy_sub (E := E) (E' := E') hc hI]
  rw [← add_zero ((1 / 2) * ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2), ← w]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

lemma sum_sq_eq_zero_iff (g : δ → Ix → ℝ) :
    ∑ x, M.hx x * ∑ α, g α x ^ 2 = 0 ↔ ∀ α x, g α x = 0 := by
  constructor
  · intro h α x
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (M.hx_pos x).le
      (Finset.sum_nonneg fun α _ => sq_nonneg (g α x)))).1 h x (Finset.mem_univ x)
    have h2 := (mul_eq_zero.1 h1).resolve_left (M.hx_pos x).ne'
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun α _ => sq_nonneg (g α x))).1 h2 α (Finset.mem_univ α)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h3
  · intro h
    simp [h]

/-- **Sec. 6.1** (arXiv 2101.12571), on the discrete phase space.  The paper says that the defect
is `O(τ²)` per step.  Explicitly `∫ (E^{n+1} - E^n)² dx ≤ τ² ∫ (j^n)² dx`, as `E^{n+1} - E^n` is the
gradient part of `τ j^n` (a Pythagoras identity). -/
theorem MomStep.field_sub_le (h : M.MomStep U τ (M.vlasov Em f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (hF : M.IsField (M.rho f) E φ) (hF' : M.IsField (M.rho f') E' φ') :
    ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2 ≤ τ ^ 2 * ∑ x, M.hx x * ∑ α, M.cur f α x ^ 2 := by
  have hψ : ∀ α, (E' α - E α) = -M.dx α (φ' - φ) := by
    intro α
    rw [hF.grad α, hF'.grad α, map_sub]
    abel
  have w := h.work_eq_zero (Eg := fun α => E' α - E α) (ψ := φ' - φ) hc hI hF hF' hψ
  have hsq : 0 ≤ ∑ x, M.hx x * ∑ α, (E' α x - E α x - τ * M.cur f α x) ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (M.hx_pos x).le
      (Finset.sum_nonneg fun α _ => sq_nonneg _)
  have w' : ∑ x, M.hx x * ∑ α, (E' α x - E α x) * (E' α x - E α x - τ * M.cur f α x) = 0 := w
  have key : ∑ x, M.hx x * ∑ α, (E' α x - E α x - τ * M.cur f α x) ^ 2
      = τ ^ 2 * ∑ x, M.hx x * ∑ α, M.cur f α x ^ 2 - ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2
        + 2 * ∑ x, M.hx x * ∑ α, (E' α x - E α x) * (E' α x - E α x - τ * M.cur f α x) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  rw [w', mul_zero, add_zero] at key
  linarith

/-- **Sec. 6.1** (arXiv 2101.12571), on the discrete phase space, sharper than the paper: the
defect vanishes exactly if the density does not move, `ℰ^{n+1} = ℰ^n` iff `∇ ⋅ j^n = 0`.  So exact
conservation of energy by explicit Euler is the exception. -/
theorem MomStep.energy_eq_iff (h : M.MomStep U τ (M.vlasov E f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (hF : M.IsField (M.rho f) E φ) (hF' : M.IsField (M.rho f') E' φ')
    (hτ : τ ≠ 0) :
    M.energy f' E' = M.energy f E ↔ ∀ x, ∑ α, M.dx α (M.cur f α) x = 0 := by
  have hd := h.energy_defect hc hI hF hF'
  constructor
  · intro e x
    rw [e, sub_self] at hd
    have h0 : ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2 = 0 := by linarith
    have h1 := (sum_sq_eq_zero_iff (fun α x => E' α x - E α x)).1 h0
    have h2 : E' = E := by
      ext α x
      linarith [h1 α x]
    have h3 := h.rho_eq hc hI x
    have h4 := hF.gauss x
    have h5 := hF'.gauss x
    rw [h2, h4] at h5
    have h6 : τ * ∑ α, M.dx α (M.cur f α) x = 0 := by linarith
    exact (mul_eq_zero.1 h6).resolve_left hτ
  · intro hdiv
    have hρ : ∀ x, M.rho f' x = M.rho f x := fun x => by
      rw [h.rho_eq hc hI x, hdiv x]
      ring
    have hY : ∀ x, ∑ α, M.dx α (E' α - E α) x = 0 := by
      intro x
      simp only [map_sub, Pi.sub_apply, Finset.sum_sub_distrib]
      rw [hF'.gauss x, hF.gauss x, hρ x]
      ring
    have e := sum_grad_mul (M := M) (φ' - φ) (fun α => E' α - E α)
    simp only [hY, mul_zero, Finset.sum_const_zero, neg_zero] at e
    have e2 : ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2 = 0 := by
      rw [← neg_eq_zero, ← e, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun α _ => ?_
      have : M.dx α (φ' - φ) x = -(E' α x - E α x) := by
        rw [hF.grad α, hF'.grad α, map_sub]
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring
      rw [this, Pi.sub_apply]
      ring
    rw [e2, mul_zero] at hd
    linarith

/-- **Sec. 6.1, the implicit remedy** (arXiv 2101.12571): with `E^{n+1/2} = (E^n + E^{n+1})/2` in
the kinetic update, the discrete energy is conserved exactly. -/
theorem MomStep.energy_midpoint
    (h : M.MomStep U τ (M.vlasov (fun α x => (E α x + E' α x) / 2) f) f f') (hc : M.Conserves U)
    (hI : ∀ x, M.VelIBP (f x)) (hF : M.IsField (M.rho f) E φ) (hF' : M.IsField (M.rho f') E' φ') :
    M.energy f' E' = M.energy f E := by
  have hψ : ∀ α, (fun x => (E α x + E' α x) / 2) = -M.dx α ((1 / 2 : ℝ) • (φ + φ')) := by
    intro α
    ext x
    rw [map_smul, map_add, hF.grad α, hF'.grad α]
    simp
    ring
  have w := h.work_eq_zero (Eg := fun α x => (E α x + E' α x) / 2) hc hI hF hF' hψ
  have e := h.energy_sub (E := E) (E' := E') hc hI
  rw [← sub_eq_zero, e, ← w]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

end Energy

/-! ### The Petrov-Galerkin condition (9) and the equations of motion (10)-(12) -/

section PetrovGalerkin

variable (M) in
/-- An element of the tangent space `𝒯_f ℳ`, in factor form:
`f_{0v} ∑_ij (Ẋ_i S_ij V_j + X_i Ṡ_ij V_j) + f_{0v} ∑_ip X_i S_ip Ẇ_p`. -/
def tangent (X : A ⊕ P → Ix → ℝ) (S : Matrix (A ⊕ P) (A ⊕ P) ℝ) (V : A ⊕ P → Iv → ℝ)
    (Xd : A ⊕ P → Ix → ℝ) (Sd : Matrix (A ⊕ P) (A ⊕ P) ℝ) (Wd : P → Iv → ℝ) : Ix → Iv → ℝ :=
  fun x v => M.f0 v * (∑ i, ∑ j, (Xd i x * S i j * V j v + X i x * Sd i j * V j v)
    + ∑ i, ∑ p, X i x * S i (Sum.inr p) * Wd p v)

variable (M) in
/-- The gauge conditions `⟨Ẋ_i, X_j⟩_x = 0`, `⟨Ẇ_p, V_k⟩_v = 0`. -/
structure Gauge (X : A ⊕ P → Ix → ℝ) (V : A ⊕ P → Iv → ℝ) (Xd : A ⊕ P → Ix → ℝ)
    (Wd : P → Iv → ℝ) : Prop where
  x : ∀ i j, M.ipx (Xd i) (X j) = 0
  v : ∀ p k, M.ipv (Wd p) (V k) = 0

variable (M) in
/-- The tangent space `𝒯_f ℳ`, for `f = f_{0v} ∑ X_i S_ij V_j`, with the gauge conditions of the
paper.  The `U_a` do not move: there is a derivative `Ẇ_p` for the free functions only. -/
def tangentSpace (X : A ⊕ P → Ix → ℝ) (S : Matrix (A ⊕ P) (A ⊕ P) ℝ) (V : A ⊕ P → Iv → ℝ) :
    Set (Ix → Iv → ℝ) :=
  {ν | ∃ Xd Sd Wd, M.Gauge X V Xd Wd ∧ ν = M.tangent X S V Xd Sd Wd}

variable (M) in
/-- The Petrov-Galerkin condition (9), `(ν / f_{0v}, ∂ₜ f - G)_{xv} = 0` on the tangent space. -/
def PetrovGalerkin (X : A ⊕ P → Ix → ℝ) (S : Matrix (A ⊕ P) (A ⊕ P) ℝ) (V : A ⊕ P → Iv → ℝ)
    (fd G : Ix → Iv → ℝ) : Prop :=
  ∀ ν ∈ M.tangentSpace X S V,
    ∑ x, M.hx x * ∑ v, M.hv v * (ν x v / M.f0 v * (fd x v - G x v)) = 0

variable (M) in
/-- `X` and `V` are orthonormal in `⟨·, ·⟩_x` and `⟨·, ·⟩_v`. -/
structure IsFrame (X : A ⊕ P → Ix → ℝ) (V : A ⊕ P → Iv → ℝ) : Prop where
  x : ∀ i j, M.ipx (X i) (X j) = if i = j then 1 else 0
  v : ∀ k l, M.ipv (V k) (V l) = if k = l then 1 else 0

lemma ipx_comm (u w : Ix → ℝ) : M.ipx u w = M.ipx w u :=
  Finset.sum_congr rfl fun x _ => by ring

variable {X Xd : A ⊕ P → Ix → ℝ} {S Sd : Matrix (A ⊕ P) (A ⊕ P) ℝ} {V : A ⊕ P → Iv → ℝ}
  {Wd : P → Iv → ℝ}

lemma tangent_eq (x : Ix) (v : Iv) : M.tangent X S V Xd Sd Wd x v = M.f0 v *
    (∑ j, (∑ i, (Xd i x * S i j + X i x * Sd i j)) * V j v
      + ∑ p, colK X S (Sum.inr p) x * Wd p v) := by
  simp only [tangent, colK, Finset.sum_mul]
  congr 2
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]

lemma tangent_eq' (x : Ix) (v : Iv) : M.tangent X S V Xd Sd Wd x v = M.f0 v *
    ∑ i, (X i x * (∑ j, Sd i j * V j v + ∑ p, S i (Sum.inr p) * Wd p v)
      + Xd i x * ∑ j, S i j * V j v) := by
  simp only [tangent]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_assoc]
  ring

/-- `(V_k, ∂ₜ f)_v = ∑_i (Ẋ_i S_ik + X_i Ṡ_ik)`. -/
lemma mom_tangent (hV : ∀ k l, M.ipv (V k) (V l) = if k = l then 1 else 0)
    (hg : ∀ p k, M.ipv (Wd p) (V k) = 0) (k : A ⊕ P) (x : Ix) :
    M.mom (V k) (M.tangent X S V Xd Sd Wd) x = ∑ i, (Xd i x * S i k + X i x * Sd i k) := by
  obtain ⟨c, hc⟩ : ∃ c : A ⊕ P → ℝ, c = fun j => ∑ i, (Xd i x * S i j + X i x * Sd i j) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : P → ℝ, d = fun p => colK X S (Sum.inr p) x := ⟨_, rfl⟩
  have e : ∀ v, M.hv v * (V k v * M.tangent X S V Xd Sd Wd x v)
      = ∑ j, c j * (M.hv v * (M.f0 v * (V j v * V k v)))
        + ∑ p, d p * (M.hv v * (M.f0 v * (Wd p v * V k v))) := by
    intro v
    rw [tangent_eq]
    have : ∑ j, (∑ i, (Xd i x * S i j + X i x * Sd i j)) * V j v = ∑ j, c j * V j v := by
      rw [hc]
    rw [this]
    have : ∑ p, colK X S (Sum.inr p) x * Wd p v = ∑ p, d p * Wd p v := by rw [hd]
    rw [this]
    simp only [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => by ring
    · refine Finset.sum_congr rfl fun p _ => by ring
  calc M.mom (V k) (M.tangent X S V Xd Sd Wd) x
      = ∑ v, ∑ j, c j * (M.hv v * (M.f0 v * (V j v * V k v)))
        + ∑ v, ∑ p, d p * (M.hv v * (M.f0 v * (Wd p v * V k v))) := by
        simp only [mom]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => e v
    _ = ∑ j, c j * M.ipv (V j) (V k) + ∑ p, d p * M.ipv (Wd p) (V k) := by
        congr 1 <;>
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
    _ = c k := by
        simp only [hV, hg, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, Finset.sum_const_zero, add_zero]
    _ = _ := by rw [hc]

/-- `(X_m, ∂ₜ f)_x / f_{0v} = ∑_j Ṡ_mj V_j + ∑_p S_mp Ẇ_p`. -/
lemma momX_tangent (hX : ∀ i j, M.ipx (X i) (X j) = if i = j then 1 else 0)
    (hg : ∀ i j, M.ipx (Xd i) (X j) = 0) (m : A ⊕ P) (v : Iv) :
    M.momX (X m) (M.tangent X S V Xd Sd Wd) v
      = M.f0 v * (∑ j, Sd m j * V j v + ∑ p, S m (Sum.inr p) * Wd p v) := by
  obtain ⟨L, hL⟩ : ∃ L : A ⊕ P → ℝ,
      L = fun i => ∑ j, Sd i j * V j v + ∑ p, S i (Sum.inr p) * Wd p v := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : A ⊕ P → ℝ, N = fun i => ∑ j, S i j * V j v := ⟨_, rfl⟩
  have e : ∀ x, M.hx x * (X m x * M.tangent X S V Xd Sd Wd x v)
      = M.f0 v * ∑ i, (L i * (M.hx x * (X i x * X m x)) + N i * (M.hx x * (Xd i x * X m x))) := by
    intro x
    rw [tangent_eq']
    have : ∀ i, X i x * (∑ j, Sd i j * V j v + ∑ p, S i (Sum.inr p) * Wd p v)
        + Xd i x * ∑ j, S i j * V j v = X i x * L i + Xd i x * N i := fun i => by rw [hL, hN]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have e0 : ∑ x, ∑ i, (L i * (M.hx x * (X i x * X m x)) + N i * (M.hx x * (Xd i x * X m x)))
      = ∑ i, (L i * M.ipx (X i) (X m) + N i * M.ipx (Xd i) (X m)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib, ipx, ipx, Finset.mul_sum, Finset.mul_sum]
  have e1 : M.momX (X m) (M.tangent X S V Xd Sd Wd) v = M.f0 v * L m := by
    simp only [momX, e, ← Finset.mul_sum]
    rw [e0]
    simp only [hX, hg, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, add_zero]
  rw [e1, hL]

lemma momX_colK (q : A ⊕ P) (g : Ix → Iv → ℝ) (v : Iv) :
    M.momX (colK X S q) g v = ∑ i, S i q * M.momX (X i) g v := by
  simp only [momX, colK, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

/-- `(K_q, ∂ₜ f)_x / f_{0v} = ∑_p T_qp Ẇ_p + ∑_il S_iq Ṡ_il V_l`, for a free index `q`. -/
lemma momX_colK_tangent (hX : ∀ i j, M.ipx (X i) (X j) = if i = j then 1 else 0)
    (hg : ∀ i j, M.ipx (Xd i) (X j) = 0) (q : P) (v : Iv) :
    M.momX (colK X S (Sum.inr q)) (M.tangent X S V Xd Sd Wd) v
      = M.f0 v * (∑ p, gramFree S q p * Wd p v
        + ∑ i, S i (Sum.inr q) * ∑ l, Sd i l * V l v) := by
  have e1 : ∑ p, gramFree S q p * Wd p v
      = ∑ i, S i (Sum.inr q) * ∑ p, S i (Sum.inr p) * Wd p v := by
    simp only [gramFree, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
  simp only [momX_colK, momX_tangent hX hg]
  rw [e1, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma ipx_sub_sum {ι : Type*} [Fintype ι] (g h : Ix → ℝ) (c : ι → ℝ) (B : ι → Ix → ℝ) :
    M.ipx (fun x => g x - ∑ i, c i * B i x) h = M.ipx g h - ∑ i, c i * M.ipx (B i) h := by
  have e : ∀ x, M.hx x * ((g x - ∑ i, c i * B i x) * h x)
      = M.hx x * (g x * h x) - ∑ i, c i * (M.hx x * (B i x * h x)) := by
    intro x
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [ipx]
  rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

lemma ipv_sub_sum {ι : Type*} [Fintype ι] (g h : Iv → ℝ) (c : ι → ℝ) (B : ι → Iv → ℝ) :
    M.ipv (fun v => g v - ∑ i, c i * B i v) h = M.ipv g h - ∑ i, c i * M.ipv (B i) h := by
  have e : ∀ v, M.hv v * (M.f0 v * ((g v - ∑ i, c i * B i v) * h v))
      = M.hv v * (M.f0 v * (g v * h v)) - ∑ i, c i * (M.hv v * (M.f0 v * (B i v * h v))) := by
    intro v
    rw [sub_mul, mul_sub, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [ipv]
  rw [Finset.sum_congr rfl (fun v _ => e v), Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- `χ(x) V_k`, and in particular `χ(x) U_a`, is a test function of the Petrov-Galerkin condition:
`f_{0v} χ V_k` is tangent.  This is what makes the scheme conservative. -/
lemma test_chi (hX : ∀ i j, M.ipx (X i) (X j) = if i = j then 1 else 0) (hS : IsUnit S.det)
    (χ : Ix → ℝ) (k : A ⊕ P) :
    (fun x v => M.f0 v * (χ x * V k v)) ∈ M.tangentSpace X S V := by
  have hinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hS
  obtain ⟨χp, hχp⟩ : ∃ χp : Ix → ℝ, χp = fun x => χ x - ∑ i, M.ipx (X i) χ * X i x := ⟨_, rfl⟩
  have horth : ∀ j, M.ipx χp (X j) = 0 := by
    intro j
    rw [hχp, ipx_sub_sum]
    simp only [hX, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [ipx_comm, sub_self]
  refine ⟨fun i x => S⁻¹ k i * χp x, Matrix.of fun i j => if j = k then M.ipx (X i) χ else 0, 0,
    ⟨fun i j => ?_, fun p l => ?_⟩, ?_⟩
  · have : M.ipx (fun x => S⁻¹ k i * χp x) (X j) = S⁻¹ k i * M.ipx χp (X j) := by
      simp only [ipx, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, horth, mul_zero]
  · simp [ipv]
  · ext x v
    have coef : ∀ j, ∑ i, (S⁻¹ k i * χp x * S i j
        + X i x * (Matrix.of fun i j => if j = k then M.ipx (X i) χ else 0) i j)
        = if j = k then χ x else 0 := by
      intro j
      rw [Finset.sum_add_distrib]
      have e1 : ∑ i, S⁻¹ k i * χp x * S i j = χp x * (S⁻¹ * S) k j := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, hinv, Matrix.one_apply]
      by_cases hj : j = k
      · subst hj
        simp only [ite_true, mul_one, hχp, Matrix.of_apply]
        rw [sub_add_eq_add_sub]
        have : ∑ i, X i x * M.ipx (X i) χ = ∑ i, M.ipx (X i) χ * X i x :=
          Finset.sum_congr rfl fun i _ => by ring
        rw [this]
        ring
      · simp [hj, Ne.symm hj]
    refine Eq.symm ((tangent_eq x v).trans ?_)
    simp only [coef, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp

/-- `K_q(x) ζ(v)`, for a free index `q`, is a test function of the Petrov-Galerkin condition. -/
lemma test_zeta (hV : ∀ k l, M.ipv (V k) (V l) = if k = l then 1 else 0) (ζ : Iv → ℝ) (q : P) :
    (fun x v => M.f0 v * (colK X S (Sum.inr q) x * ζ v)) ∈ M.tangentSpace X S V := by
  obtain ⟨ζp, hζp⟩ : ∃ ζp : Iv → ℝ, ζp = fun v => ζ v - ∑ l, M.ipv (V l) ζ * V l v := ⟨_, rfl⟩
  have horth : ∀ k, M.ipv ζp (V k) = 0 := by
    intro k
    rw [hζp, ipv_sub_sum]
    simp only [hV, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [ipv_comm, sub_self]
  refine ⟨0, Matrix.of fun i l => S i (Sum.inr q) * M.ipv (V l) ζ,
    fun p v => if p = q then ζp v else 0, ⟨fun i j => ?_, fun p k => ?_⟩, ?_⟩
  · simp [ipx]
  · by_cases hp : p = q
    · simp only [hp, ite_true]
      exact horth k
    · simp [hp, ipv]
  · ext x v
    refine Eq.symm ((tangent_eq' x v).trans ?_)
    congr 1
    simp only [colK, Pi.zero_apply, zero_mul, add_zero, Matrix.of_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, S i (Sum.inr q) * M.ipv (V j) ζ * V j v
        = S i (Sum.inr q) * ∑ j, M.ipv (V j) ζ * V j v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hζp]
    ring

lemma mom_sub (φ : Iv → ℝ) (a b : Ix → Iv → ℝ) (x : Ix) :
    M.mom φ (fun x v => a x v - b x v) x = M.mom φ a x - M.mom φ b x := by
  simp only [mom, mul_sub, Finset.sum_sub_distrib]

lemma momX_sub (u : Ix → ℝ) (a b : Ix → Iv → ℝ) (v : Iv) :
    M.momX u (fun x v => a x v - b x v) v = M.momX u a v - M.momX u b v := by
  simp only [momX, mul_sub, Finset.sum_sub_distrib]

/-- The pairing of a tangent vector with a residual. -/
lemma pairing_tangent (R : Ix → Iv → ℝ) :
    ∑ x, M.hx x * ∑ v, M.hv v * (M.tangent X S V Xd Sd Wd x v / M.f0 v * R x v)
      = ∑ x, M.hx x * ∑ j, (∑ i, (Xd i x * S i j + X i x * Sd i j)) * M.mom (V j) R x
        + ∑ p, ∑ v, M.hv v * (Wd p v * M.momX (colK X S (Sum.inr p)) R v) := by
  have e : ∀ x v, M.hv v * (M.tangent X S V Xd Sd Wd x v / M.f0 v * R x v)
      = ∑ j, (∑ i, (Xd i x * S i j + X i x * Sd i j)) * (M.hv v * (V j v * R x v))
        + ∑ p, M.hv v * (Wd p v * (colK X S (Sum.inr p) x * R x v)) := by
    intro x v
    rw [tangent_eq, mul_div_cancel_left₀ _ (M.f0_pos v).ne', add_mul, mul_add, Finset.sum_mul,
      Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun p _ => by ring
  have e1 : ∀ x, M.hx x * ∑ v, M.hv v * (M.tangent X S V Xd Sd Wd x v / M.f0 v * R x v)
      = M.hx x * ∑ j, (∑ i, (Xd i x * S i j + X i x * Sd i j)) * M.mom (V j) R x
        + ∑ p, ∑ v, M.hx x * (M.hv v * (Wd p v * (colK X S (Sum.inr p) x * R x v))) := by
    intro x
    rw [Finset.sum_congr rfl (fun v _ => e x v), Finset.sum_add_distrib, mul_add]
    congr 1
    · congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mom, Finset.mul_sum]
    · rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [momX, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma pair_test_chi (χ : Ix → ℝ) (φ : Iv → ℝ) (R : Ix → Iv → ℝ) :
    ∑ x, M.hx x * ∑ v, M.hv v * ((M.f0 v * (χ x * φ v)) / M.f0 v * R x v)
      = ∑ x, M.hx x * (χ x * M.mom φ R x) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [mom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_div_cancel_left₀ _ (M.f0_pos v).ne']
  ring

lemma pair_test_zeta (u : Ix → ℝ) (ζ : Iv → ℝ) (R : Ix → Iv → ℝ) :
    ∑ x, M.hx x * ∑ v, M.hv v * ((M.f0 v * (u x * ζ v)) / M.f0 v * R x v)
      = ∑ v, M.hv v * (ζ v * M.momX u R v) := by
  simp only [momX, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun x _ => ?_
  rw [mul_div_cancel_left₀ _ (M.f0_pos v).ne']
  ring

/-- **Sec. 4, eqs. (9)-(12)** (arXiv 2101.12571), on the discrete phase space.  At a point with
orthonormal `X`, `V`, invertible `S`, and for `∂ₜ f` tangent in the gauge of the paper, the
Petrov-Galerkin condition (9) holds with right-hand side `G` iff the equations of motion (10), (11),
(12) hold.  No property of `G` is used; (12) is `Ṡ_kl = (X_k V_l, G)_{xv}`. -/
theorem petrovGalerkin_iff (hF : M.IsFrame X V) (hS : IsUnit S.det) (hg : M.Gauge X V Xd Wd)
    (G : Ix → Iv → ℝ) :
    M.PetrovGalerkin X S V (M.tangent X S V Xd Sd Wd) G ↔
      (∀ k x, ∑ i, Xd i x * S i k = M.mom (V k) G x - ∑ i, X i x * Sd i k) ∧
      (∀ q v, ∑ p, gramFree S q p * Wd p v = ∑ i, S i (Sum.inr q) *
        (M.momX (X i) G v / M.f0 v - ∑ l, Sd i l * V l v)) ∧
      (∀ k l, Sd k l = M.pair (X k) (V l) G) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : Ix → Iv → ℝ, R = fun x v => M.tangent X S V Xd Sd Wd x v - G x v :=
    ⟨_, rfl⟩
  have h10 : ∀ k x, M.mom (V k) R x = 0
      ↔ ∑ i, Xd i x * S i k = M.mom (V k) G x - ∑ i, X i x * Sd i k := by
    intro k x
    rw [hR, mom_sub, mom_tangent hF.v hg.v, Finset.sum_add_distrib]
    constructor <;> intro h <;> linarith
  have h11 : ∀ q v, M.momX (colK X S (Sum.inr q)) R v = 0
      ↔ ∑ p, gramFree S q p * Wd p v = ∑ i, S i (Sum.inr q) *
        (M.momX (X i) G v / M.f0 v - ∑ l, Sd i l * V l v) := by
    intro q v
    have hf := (M.f0_pos v).ne'
    have e : M.momX (colK X S (Sum.inr q)) G v = M.f0 v * ∑ i, S i (Sum.inr q) *
        (M.momX (X i) G v / M.f0 v) := by
      rw [momX_colK, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have e2 : ∑ i, S i (Sum.inr q) * (M.momX (X i) G v / M.f0 v - ∑ l, Sd i l * V l v)
        = ∑ i, S i (Sum.inr q) * (M.momX (X i) G v / M.f0 v)
          - ∑ i, S i (Sum.inr q) * ∑ l, Sd i l * V l v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hR, momX_sub, momX_colK_tangent hF.x hg.x, e, e2, ← mul_sub, mul_eq_zero, or_iff_right hf]
    constructor <;> intro h <;> linarith
  have h12 : (∀ k x, M.mom (V k) R x = 0) → ∀ k l, Sd k l = M.pair (X k) (V l) G := by
    intro h k l
    have e : ∀ x, M.mom (V l) G x = ∑ i, (Xd i x * S i l + X i x * Sd i l) := by
      intro x
      have := (h10 l x).1 (h l x)
      rw [Finset.sum_add_distrib, this]
      ring
    have e2 : M.pair (X k) (V l) G
        = ∑ i, (M.ipx (Xd i) (X k) * S i l + M.ipx (X i) (X k) * Sd i l) := by
      have e3 : ∀ x, M.hx x * (X k x * ∑ i, (Xd i x * S i l + X i x * Sd i l))
          = ∑ i, (M.hx x * (Xd i x * X k x) * S i l + M.hx x * (X i x * X k x) * Sd i l) := by
        intro x
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [pair, e]
      rw [Finset.sum_congr rfl (fun x _ => e3 x), Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_add_distrib, ipx, ipx, Finset.sum_mul, Finset.sum_mul]
    rw [e2]
    simp only [hg.x, hF.x, zero_mul, zero_add, ite_mul, one_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hRa : ∀ x v, M.tangent X S V Xd Sd Wd x v - G x v = R x v := fun x v => by rw [hR]
  constructor
  · intro h
    have hm : ∀ k x, M.mom (V k) R x = 0 := by
      intro k x₀
      have e := h _ (test_chi (V := V) hF.x hS (fun x => if x = x₀ then 1 else 0) k)
      have e2 := pair_test_chi (M := M) (fun x => if x = x₀ then (1 : ℝ) else 0) (V k) R
      simp only [hRa] at e
      have e3 := e2.symm.trans e
      simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true] at e3
      exact (mul_eq_zero.1 e3).resolve_left (M.hx_pos x₀).ne'
    have hmx : ∀ q v, M.momX (colK X S (Sum.inr q)) R v = 0 := by
      intro q v₀
      have e := h _ (test_zeta (S := S) (X := X) hF.v (fun v => if v = v₀ then 1 else 0) q)
      have e2 := pair_test_zeta (M := M) (colK X S (Sum.inr q))
        (fun v => if v = v₀ then (1 : ℝ) else 0) R
      simp only [hRa] at e
      have e3 := e2.symm.trans e
      simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true] at e3
      exact (mul_eq_zero.1 e3).resolve_left (M.hv_pos v₀).ne'
    exact ⟨fun k x => (h10 k x).1 (hm k x), fun q v => (h11 q v).1 (hmx q v), h12 hm⟩
  · rintro ⟨h1, h2, -⟩ ν ⟨ξ, σ, ω, -, rfl⟩
    have hm := fun k x => (h10 k x).2 (h1 k x)
    have hmx := fun q v => (h11 q v).2 (h2 q v)
    simp only [hRa]
    rw [pairing_tangent]
    simp [hm, hmx]

/-- Since `S` has full rank the same is true for `T`, as the paper says after eq. (11). -/
lemma gramFree_isUnit {S : Matrix (A ⊕ P) (A ⊕ P) ℝ} (hS : IsUnit S.det) :
    IsUnit (gramFree S).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨y, hy, hT⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hy
  have e0 : ∑ i, (∑ p, S i (Sum.inr p) * y p) ^ 2 = 0 := by
    have e1 : ∑ i, (∑ p, S i (Sum.inr p) * y p) ^ 2
        = ∑ q, y q * (gramFree S).mulVec y q := by
      have e : ∀ q, y q * (gramFree S).mulVec y q
          = ∑ i, (S i (Sum.inr q) * y q) * ∑ p, S i (Sum.inr p) * y p := by
        intro q
        simp only [Matrix.mulVec, dotProduct, gramFree, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
      simp only [e]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sq, Finset.sum_mul]
    rw [e1, hT]
    simp
  have e2 : ∀ i, ∑ p, S i (Sum.inr p) * y p = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 e0 i (Finset.mem_univ i)
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have e3 : S.mulVec (Sum.elim 0 y) = 0 := by
    ext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, e2]
  have e4 := Matrix.eq_zero_of_mulVec_eq_zero (isUnit_iff_ne_zero.1 hS) e3
  ext p
  simpa using congrFun e4 (Sum.inr p)

end PetrovGalerkin

/-! ### Continuous time: the constraints are preserved -/

section Continuous

variable {J : Set ℝ} {t : ℝ}

lemma hasDeriv_ipv {a b : ℝ → Iv → ℝ} {a' b' : Iv → ℝ}
    (ha : ∀ v, HasDerivWithinAt (fun s => a s v) (a' v) J t)
    (hb : ∀ v, HasDerivWithinAt (fun s => b s v) (b' v) J t) :
    HasDerivWithinAt (fun s => M.ipv (a s) (b s)) (M.ipv a' (b t) + M.ipv (a t) b') J t := by
  have h : HasDerivWithinAt (fun s => ∑ v, M.hv v * (M.f0 v * (a s v * b s v)))
      (∑ v, M.hv v * (M.f0 v * (a' v * b t v + a t v * b' v))) J t :=
    HasDerivWithinAt.fun_sum fun v _ => (((ha v).mul (hb v)).const_mul _).const_mul _
  have e : M.ipv a' (b t) + M.ipv (a t) b'
      = ∑ v, M.hv v * (M.f0 v * (a' v * b t v + a t v * b' v)) := by
    rw [ipv, ipv, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e]
  exact h

lemma hasDeriv_ipx {a b : ℝ → Ix → ℝ} {a' b' : Ix → ℝ}
    (ha : ∀ x, HasDerivWithinAt (fun s => a s x) (a' x) J t)
    (hb : ∀ x, HasDerivWithinAt (fun s => b s x) (b' x) J t) :
    HasDerivWithinAt (fun s => M.ipx (a s) (b s)) (M.ipx a' (b t) + M.ipx (a t) b') J t := by
  have h : HasDerivWithinAt (fun s => ∑ x, M.hx x * (a s x * b s x))
      (∑ x, M.hx x * (a' x * b t x + a t x * b' x)) J t :=
    HasDerivWithinAt.fun_sum fun x _ => ((ha x).mul (hb x)).const_mul _
  have e : M.ipx a' (b t) + M.ipx (a t) b' = ∑ x, M.hx x * (a' x * b t x + a t x * b' x) := by
    rw [ipx, ipx, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e]
  exact h

/-- A linear homogeneous law for a symmetric Gram defect keeps it at zero (Grönwall). -/
lemma gram_eq_zero {κ : Type*} [Fintype κ] {t₀ t₁ : ℝ} {C Cd A : ℝ → κ → κ → ℝ}
    (hC : ∀ t ∈ Icc t₀ t₁, ∀ m n, HasDerivWithinAt (fun s => C s m n) (Cd t m n) (Icc t₀ t₁) t)
    (hA : ∀ m n, ContinuousOn (fun t => A t m n) (Icc t₀ t₁))
    (hlin : ∀ t ∈ Icc t₀ t₁, ∀ m n, Cd t m n = ∑ l, (A t m l * C t l n + A t n l * C t m l))
    (h0 : ∀ m n, C t₀ m n = 0) : ∀ t ∈ Icc t₀ t₁, ∀ m n, C t m n = 0 := by
  have hbd : ∀ m n, ∃ B, ∀ t ∈ Icc t₀ t₁, ‖A t m n‖ ≤ B := fun m n =>
    isCompact_Icc.exists_bound_of_continuousOn (hA m n)
  choose B hB using hbd
  obtain ⟨K, hK⟩ : ∃ K, K = ∑ m, ∑ n, |B m n| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hAK : ∀ t ∈ Icc t₀ t₁, ∀ m n, |A t m n| ≤ K := by
    intro t ht m n
    calc |A t m n| ≤ B m n := hB m n t ht
      _ ≤ |B m n| := le_abs_self _
      _ ≤ ∑ n, |B m n| := Finset.single_le_sum (f := fun n => |B m n|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ n)
      _ ≤ K := by
        rw [hK]
        exact Finset.single_le_sum (f := fun m => ∑ n, |B m n|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt C (Cd t) (Icc t₀ t₁) t := fun t ht =>
    hasDerivWithinAt_pi.2 fun m => hasDerivWithinAt_pi.2 fun n => hC t ht m n
  have hc : ContinuousOn C (Icc t₀ t₁) := fun t ht => (hd t ht).continuousWithinAt
  have hd' : ∀ x ∈ Ico t₀ t₁, HasDerivWithinAt C (Cd x) (Ici x) x := fun x hx =>
    (hd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  have hb : ∀ x ∈ Ico t₀ t₁, ‖Cd x‖ ≤ (2 * Fintype.card κ * K) * ‖C x‖ + 0 := by
    intro x hx
    have hx' := Ico_subset_Icc_self hx
    rw [add_zero]
    have hentry : ∀ m n, |C x m n| ≤ ‖C x‖ := fun m n => by
      have h1 := norm_le_pi_norm (C x m) n
      have h2 := norm_le_pi_norm (C x) m
      rw [Real.norm_eq_abs] at h1
      exact h1.trans h2
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m =>
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun n => ?_
    rw [Real.norm_eq_abs, hlin x hx' m n]
    calc |∑ l, (A x m l * C x l n + A x n l * C x m l)|
        ≤ ∑ l, |A x m l * C x l n + A x n l * C x m l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : κ, (2 * K * ‖C x‖) := by
        refine Finset.sum_le_sum fun l _ => ?_
        have h1 := hAK x hx' m l
        have h2 := hAK x hx' n l
        have h3 := hentry l n
        have h4 := hentry m l
        calc _ ≤ |A x m l * C x l n| + |A x n l * C x m l| := abs_add_le _ _
          _ = |A x m l| * |C x l n| + |A x n l| * |C x m l| := by rw [abs_mul, abs_mul]
          _ ≤ K * ‖C x‖ + K * ‖C x‖ := by gcongr
          _ = _ := by ring
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have h00 : ‖C t₀‖ ≤ 0 := by
    have : C t₀ = 0 := by
      ext m n
      exact h0 m n
    simp [this]
  intro t ht m n
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hc hd' h00 hb t ht
  rw [gronwallBound_ε0_δ0] at hg
  have h1 : C t = 0 := norm_le_zero_iff.1 hg
  rw [h1]
  rfl

lemma continuousOn_matrix_inv {Q : Type*} [Fintype Q] [DecidableEq Q] {J : Set ℝ}
    {B : ℝ → Matrix Q Q ℝ} (hB : ∀ p q, ContinuousOn (fun t => B t p q) J)
    (hu : ∀ t ∈ J, IsUnit (B t).det) (p q : Q) : ContinuousOn (fun t => (B t)⁻¹ p q) J := by
  have hB' : ContinuousOn B J := continuousOn_pi.2 fun p => continuousOn_pi.2 fun q => hB p q
  have hdet : ContinuousOn (fun t => (B t).det) J :=
    (continuous_id.matrix_det).comp_continuousOn hB'
  have hadj : ContinuousOn (fun t => (B t).adjugate) J :=
    (continuous_id.matrix_adjugate).comp_continuousOn hB'
  have e : ∀ t, (B t)⁻¹ p q = ((B t).det)⁻¹ * (B t).adjugate p q := by
    intro t
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  simp only [e]
  refine (hdet.inv₀ fun t ht => (hu t ht).ne_zero).mul ?_
  exact (continuous_apply_apply p q).comp_continuousOn hadj

variable (M) in
/-- The right-hand side `D[f(t)]` along a curve of factors. -/
def rhs (U : A → Iv → ℝ) (X : ℝ → A ⊕ P → Ix → ℝ) (S : ℝ → Matrix (A ⊕ P) (A ⊕ P) ℝ)
    (W : ℝ → P → Iv → ℝ) (E : ℝ → δ → Ix → ℝ) (t : ℝ) : Ix → Iv → ℝ :=
  M.vlasov (E t) (M.lowRank (X t) (S t) (basis U (W t)))

variable (M) in
/-- A classical solution on `[t₀, t₁]` of the equations of motion (10), (11), (12) of the
conservative scheme.  `E` is any differentiable curve of fields here. -/
structure IsSolution (U : A → Iv → ℝ) (t₀ t₁ : ℝ) (X X' : ℝ → A ⊕ P → Ix → ℝ)
    (S S' : ℝ → Matrix (A ⊕ P) (A ⊕ P) ℝ) (W W' : ℝ → P → Iv → ℝ) (E E' : ℝ → δ → Ix → ℝ) :
    Prop where
  hX : ∀ t ∈ Icc t₀ t₁, ∀ i x, HasDerivWithinAt (fun s => X s i x) (X' t i x) (Icc t₀ t₁) t
  hS : ∀ t ∈ Icc t₀ t₁, ∀ i j, HasDerivWithinAt (fun s => S s i j) (S' t i j) (Icc t₀ t₁) t
  hW : ∀ t ∈ Icc t₀ t₁, ∀ p v, HasDerivWithinAt (fun s => W s p v) (W' t p v) (Icc t₀ t₁) t
  hE : ∀ t ∈ Icc t₀ t₁, ∀ α x, HasDerivWithinAt (fun s => E s α x) (E' t α x) (Icc t₀ t₁) t
  eq10 : ∀ t ∈ Icc t₀ t₁, ∀ k x, ∑ i, X' t i x * S t i k
    = M.mom (basis U (W t) k) (M.rhs U X S W E t) x - ∑ i, X t i x * S' t i k
  eq11 : ∀ t ∈ Icc t₀ t₁, ∀ q v, ∑ p, gramFree (S t) q p * W' t p v
    = ∑ i, S t i (Sum.inr q) * (M.momX (X t i) (M.rhs U X S W E t) v / M.f0 v
        - ∑ l, S' t i l * basis U (W t) l v)
  eq12 : ∀ t ∈ Icc t₀ t₁, ∀ k l, S' t k l
    = M.pair (X t k) (basis U (W t) l) (M.rhs U X S W E t)

section Solution

variable {U : A → Iv → ℝ} {t₀ t₁ : ℝ} {X X' : ℝ → A ⊕ P → Ix → ℝ}
  {S S' : ℝ → Matrix (A ⊕ P) (A ⊕ P) ℝ} {W W' : ℝ → P → Iv → ℝ} {E E' : ℝ → δ → Ix → ℝ}

lemma IsSolution.contX (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') (i : A ⊕ P) (x : Ix) :
    ContinuousOn (fun s => X s i x) (Icc t₀ t₁) :=
  fun t ht => (h.hX t ht i x).continuousWithinAt

lemma IsSolution.contS (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') (i j : A ⊕ P) :
    ContinuousOn (fun s => S s i j) (Icc t₀ t₁) :=
  fun t ht => (h.hS t ht i j).continuousWithinAt

lemma IsSolution.contV (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') (k : A ⊕ P) (v : Iv) :
    ContinuousOn (fun s => basis U (W s) k v) (Icc t₀ t₁) := by
  rcases k with a | p
  · exact continuousOn_const
  · exact fun t ht => (h.hW t ht p v).continuousWithinAt

lemma IsSolution.contE (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') (α : δ) (x : Ix) :
    ContinuousOn (fun s => E s α x) (Icc t₀ t₁) :=
  fun t ht => (h.hE t ht α x).continuousWithinAt

lemma IsSolution.contF (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') (x : Ix) (v : Iv) :
    ContinuousOn (fun s => M.lowRank (X s) (S s) (basis U (W s)) x v) (Icc t₀ t₁) := by
  simp only [lowRank]
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => ((h.contX i x).mul (h.contS i j)).mul (h.contV j v))

lemma IsSolution.contG (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') (x : Ix) (v : Iv) :
    ContinuousOn (fun s => M.rhs U X S W E s x v) (Icc t₀ t₁) := by
  simp only [rhs, vlasov]
  refine (continuousOn_finsetSum _ fun α _ => continuousOn_const.mul ?_).neg.add
    (continuousOn_finsetSum _ fun α _ => (h.contE α x).mul ?_)
  · have hc : Continuous (M.dx α) := (M.dx α).continuous_of_finiteDimensional
    have h1 : ContinuousOn (fun s => fun y => M.lowRank (X s) (S s) (basis U (W s)) y v)
        (Icc t₀ t₁) := continuousOn_pi.2 fun y => h.contF y v
    exact (continuous_apply x).comp_continuousOn (hc.comp_continuousOn h1)
  · have hc : Continuous (M.dv α) := (M.dv α).continuous_of_finiteDimensional
    have h1 : ContinuousOn (fun s => fun w => M.lowRank (X s) (S s) (basis U (W s)) x w)
        (Icc t₀ t₁) := continuousOn_pi.2 fun w => h.contF x w
    exact (continuous_apply v).comp_continuousOn (hc.comp_continuousOn h1)

lemma IsSolution.contS' (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') (i j : A ⊕ P) :
    ContinuousOn (fun s => S' s i j) (Icc t₀ t₁) := by
  refine ContinuousOn.congr (f := fun s => M.pair (X s i) (basis U (W s) j) (M.rhs U X S W E s)) ?_
    fun s hs => h.eq12 s hs i j
  simp only [pair, mom]
  exact continuousOn_finsetSum _ fun x _ => continuousOn_const.mul ((h.contX i x).mul
    (continuousOn_finsetSum _ fun v _ => continuousOn_const.mul
      ((h.contV j v).mul (h.contG x v))))

lemma sum_aux {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → ℝ) (a : ι → κ → ℝ) (b : κ → ℝ) :
    ∑ k, (-∑ i, c i * a i k) * b k = ∑ l, (-∑ k, a l k * b k) * c l := by
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring)

/-- `⟨Ẋ_i, X_j⟩_x` is linear in the defect of `⟨X_i, X_j⟩_x`. -/
lemma IsSolution.ipx_deriv (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (hS : IsUnit (S t).det) (m j : A ⊕ P) :
    M.ipx (X' t m) (X t j) = ∑ l, (-∑ k, S' t l k * (S t)⁻¹ k m)
      * (M.ipx (X t l) (X t j) - if l = j then 1 else 0) := by
  have hinv : S t * (S t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
  obtain ⟨G, hG⟩ : ∃ G, G = M.rhs U X S W E t := ⟨_, rfl⟩
  have key : ∀ k, ∑ i, M.ipx (X' t i) (X t j) * S t i k
      = -∑ i, (M.ipx (X t i) (X t j) - if i = j then 1 else 0) * S' t i k := by
    intro k
    have e : ∀ x, ∑ i, M.hx x * (X' t i x * X t j x) * S t i k
        = M.hx x * (X t j x * M.mom (basis U (W t) k) G x)
          - ∑ i, M.hx x * (X t i x * X t j x) * S' t i k := by
      intro x
      have e1 := h.eq10 t ht k x
      rw [← hG] at e1
      have e2 : ∑ i, M.hx x * (X' t i x * X t j x) * S t i k
          = M.hx x * X t j x * ∑ i, X' t i x * S t i k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e3 : ∑ i, M.hx x * (X t i x * X t j x) * S' t i k
          = M.hx x * X t j x * ∑ i, X t i x * S' t i k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e2, e3, e1]
      ring
    have e4 : ∑ i, M.ipx (X' t i) (X t j) * S t i k
        = M.pair (X t j) (basis U (W t) k) G - ∑ i, M.ipx (X t i) (X t j) * S' t i k := by
      simp only [ipx, Finset.sum_mul, pair]
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_comm]
    have e5 : S' t j k = M.pair (X t j) (basis U (W t) k) G := by
      rw [hG]
      exact h.eq12 t ht j k
    rw [e4, ← e5]
    simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, neg_sub]
  have e : M.ipx (X' t m) (X t j) = ∑ i, M.ipx (X' t i) (X t j) * (S t * (S t)⁻¹) i m := by
    rw [hinv]
    simp [Matrix.one_apply]
  have e2 : ∑ i, M.ipx (X' t i) (X t j) * (S t * (S t)⁻¹) i m
      = ∑ k, (∑ i, M.ipx (X' t i) (X t j) * S t i k) * (S t)⁻¹ k m := by
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [e, e2]
  simp only [key]
  exact sum_aux _ _ _

lemma ipv_sum_left {ι : Type*} [Fintype ι] (c : ι → ℝ) (B : ι → Iv → ℝ) (h : Iv → ℝ) :
    M.ipv (fun v => ∑ i, c i * B i v) h = ∑ i, c i * M.ipv (B i) h := by
  have e := ipv_sub_sum (M := M) 0 h (fun i => -c i) B
  have e0 : M.ipv 0 h = 0 := by simp [ipv]
  simp only [e0, Pi.zero_apply, zero_sub, neg_mul, Finset.sum_neg_distrib, neg_neg] at e
  exact e

lemma sum_aux2 {Q ι κ : Type*} [Fintype Q] [Fintype ι] [Fintype κ] (b : Q → ℝ) (s : ι → Q → ℝ)
    (a : ι → κ → ℝ) (c : κ → ℝ) :
    ∑ q, b q * (-∑ i, s i q * ∑ l, a i l * c l)
      = ∑ l, (-∑ q, b q * ∑ i, s i q * a i l) * c l := by
  have e : ∀ q, b q * (-∑ i, s i q * ∑ l, a i l * c l)
      = -∑ l, (b q * ∑ i, s i q * a i l) * c l := by
    intro q
    rw [mul_neg, neg_inj]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
  simp only [e, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `⟨Ẇ_p, V_n⟩_v` is linear in the defect of `⟨V_l, V_n⟩_v`. -/
lemma IsSolution.ipv_deriv (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (hS : IsUnit (S t).det) (p : P) (n : A ⊕ P) :
    M.ipv (W' t p) (basis U (W t) n)
      = ∑ l, (-∑ q, (gramFree (S t))⁻¹ p q * ∑ i, S t i (Sum.inr q) * S' t i l)
        * (M.ipv (basis U (W t) l) (basis U (W t) n) - if l = n then 1 else 0) := by
  have hinv : (gramFree (S t))⁻¹ * gramFree (S t) = 1 :=
    Matrix.nonsing_inv_mul _ (gramFree_isUnit hS)
  obtain ⟨G, hG⟩ : ∃ G, G = M.rhs U X S W E t := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = basis U (W t) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : A ⊕ P → ℝ, c = fun l => M.ipv (V l) (V n) - if l = n then 1 else 0 :=
    ⟨_, rfl⟩
  have key : ∀ q, ∑ m, gramFree (S t) q m * M.ipv (W' t m) (V n)
      = -∑ i, S t i (Sum.inr q) * ∑ l, S' t i l * c l := by
    intro q
    have e : (fun v => ∑ m, gramFree (S t) q m * W' t m v)
        = fun v => ∑ i, S t i (Sum.inr q) * (M.momX (X t i) G v / M.f0 v
          - ∑ l, S' t i l * V l v) := by
      ext v
      have := h.eq11 t ht q v
      rw [← hG, ← hV] at this
      exact this
    have e1 := ipv_sum_left (M := M) (fun m => gramFree (S t) q m) (W' t) (V n)
    have e2 := ipv_sum_left (M := M) (fun i => S t i (Sum.inr q))
      (fun i v => M.momX (X t i) G v / M.f0 v - ∑ l, S' t i l * V l v) (V n)
    rw [← e1, e, e2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ipv_sub_sum, ipv_momX, ← mul_neg]
    congr 1
    have e3 : S' t i n = M.pair (X t i) (V n) G := by
      rw [hG, hV]
      exact h.eq12 t ht i n
    rw [← e3, hc]
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have e : M.ipv (W' t p) (V n)
      = ∑ m, ((gramFree (S t))⁻¹ * gramFree (S t)) p m * M.ipv (W' t m) (V n) := by
    rw [hinv]
    simp [Matrix.one_apply]
  have e2 : ∑ m, ((gramFree (S t))⁻¹ * gramFree (S t)) p m * M.ipv (W' t m) (V n)
      = ∑ q, (gramFree (S t))⁻¹ p q * ∑ m, gramFree (S t) q m * M.ipv (W' t m) (V n) := by
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun m _ => by ring
  rw [← hV, e, e2]
  simp only [key]
  have := sum_aux2 (fun q => (gramFree (S t))⁻¹ p q) (fun i q => S t i (Sum.inr q))
    (fun i l => S' t i l) c
  rw [this, hc]

/-- **Sec. 4, the constraints of the manifold** (arXiv 2101.12571), on the discrete phase space.
The equations of motion (10)-(12) keep `X` and `V = (U, W)` orthonormal, as long as `S` stays
invertible.  In particular `⟨W_p, U_a⟩_v = 0` is a consequence of the initial data; it is not
assumed. -/
theorem IsSolution.isFrame (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hS : ∀ t ∈ Icc t₀ t₁, IsUnit (S t).det) (h0 : M.IsFrame (X t₀) (basis U (W t₀))) :
    ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t)) := by
  have hX := gram_eq_zero (t₀ := t₀) (t₁ := t₁) (κ := A ⊕ P)
    (C := fun s i j => M.ipx (X s i) (X s j) - if i = j then 1 else 0)
    (Cd := fun t i j => M.ipx (X' t i) (X t j) + M.ipx (X t i) (X' t j))
    (A := fun t m l => -∑ k, S' t l k * (S t)⁻¹ k m)
    (fun t ht i j => (hasDeriv_ipx (h.hX t ht i) (h.hX t ht j)).sub_const _)
    (fun m l => (continuousOn_finsetSum _ fun k _ => (h.contS' l k).mul
      (continuousOn_matrix_inv (fun p q => h.contS p q) hS k m)).neg)
    (fun t ht m n => by
      rw [ipx_comm (X t m) (X' t n), h.ipx_deriv ht (hS t ht) m n, h.ipx_deriv ht (hS t ht) n m,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e1 : M.ipx (X t l) (X t m) = M.ipx (X t m) (X t l) := ipx_comm _ _
      have e2 : (if l = m then (1 : ℝ) else 0) = if m = l then 1 else 0 := by
        simp only [eq_comm]
      rw [e1, e2])
    (fun m n => by simp [h0.x])
  have hV := gram_eq_zero (t₀ := t₀) (t₁ := t₁) (κ := A ⊕ P)
    (C := fun s m n => M.ipv (basis U (W s) m) (basis U (W s) n) - if m = n then 1 else 0)
    (Cd := fun t m n => M.ipv (Sum.elim 0 (W' t) m) (basis U (W t) n)
      + M.ipv (basis U (W t) m) (Sum.elim 0 (W' t) n))
    (A := fun t m l => Sum.elim (fun _ => 0)
      (fun p => -∑ q, (gramFree (S t))⁻¹ p q * ∑ i, S t i (Sum.inr q) * S' t i l) m)
    (fun t ht m n => by
      have hb : ∀ k v, HasDerivWithinAt (fun s => basis U (W s) k v)
          (Sum.elim (0 : A → Iv → ℝ) (W' t) k v) (Icc t₀ t₁) t := by
        rintro (a | p) v
        · exact hasDerivWithinAt_const _ _ _
        · exact h.hW t ht p v
      exact (hasDeriv_ipv (hb m) (hb n)).sub_const _)
    (fun m l => by
      rcases m with a | p
      · exact continuousOn_const
      · refine (continuousOn_finsetSum _ fun q _ => ContinuousOn.mul ?_ ?_).neg
        · refine continuousOn_matrix_inv (B := fun t => gramFree (S t)) (fun p q => ?_)
            (fun t ht => gramFree_isUnit (hS t ht)) p q
          exact continuousOn_finsetSum _ fun i _ => (h.contS _ _).mul (h.contS _ _)
        · exact continuousOn_finsetSum _ fun i _ => (h.contS _ _).mul (h.contS' _ _))
    (fun t ht m n => by
      have hY : ∀ m n, M.ipv (Sum.elim (0 : A → Iv → ℝ) (W' t) m) (basis U (W t) n)
          = ∑ l, Sum.elim (fun _ => (0 : ℝ))
            (fun p => -∑ q, (gramFree (S t))⁻¹ p q * ∑ i, S t i (Sum.inr q) * S' t i l) m
            * (M.ipv (basis U (W t) l) (basis U (W t) n) - if l = n then 1 else 0) := by
        rintro (a | p) n
        · simp [ipv]
        · exact h.ipv_deriv ht (hS t ht) p n
      rw [ipv_comm (basis U (W t) m), hY m n, hY n m, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e1 : M.ipv (basis U (W t) l) (basis U (W t) m)
          = M.ipv (basis U (W t) m) (basis U (W t) l) := ipv_comm _ _
      have e2 : (if l = m then (1 : ℝ) else 0) = if m = l then 1 else 0 := by
        simp only [eq_comm]
      rw [e1, e2])
    (fun m n => by simp [h0.v])
  refine fun t ht => ⟨fun i j => ?_, fun m n => ?_⟩
  · exact sub_eq_zero.1 (hX t ht i j)
  · exact sub_eq_zero.1 (hV t ht m n)

/-- **Sec. 4** (arXiv 2101.12571), on the discrete phase space: along a solution of (10)-(12), the
gauge conditions of the paper hold.  They are not assumed. -/
theorem IsSolution.gauge (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hS : ∀ t ∈ Icc t₀ t₁, IsUnit (S t).det) (h0 : M.IsFrame (X t₀) (basis U (W t₀)))
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    M.Gauge (X t) (basis U (W t)) (X' t) (W' t) := by
  have hF := h.isFrame hS h0 t ht
  refine ⟨fun m j => ?_, fun p n => ?_⟩
  · rw [h.ipx_deriv ht (hS t ht) m j]
    simp [hF.x]
  · rw [h.ipv_deriv ht (hS t ht) p n]
    simp [hF.v]

/-- The derivative of the ansatz is the tangent vector of the factors' derivatives. -/
lemma IsSolution.hasDeriv_lowRank (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (x : Ix) (v : Iv) :
    HasDerivWithinAt (fun s => M.lowRank (X s) (S s) (basis U (W s)) x v)
      (M.tangent (X t) (S t) (basis U (W t)) (X' t) (S' t) (W' t) x v) (Icc t₀ t₁) t := by
  have hb : ∀ k, HasDerivWithinAt (fun s => basis U (W s) k v)
      (Sum.elim (0 : A → Iv → ℝ) (W' t) k v) (Icc t₀ t₁) t := by
    rintro (a | p)
    · exact hasDerivWithinAt_const _ _ _
    · exact h.hW t ht p v
  have h1 : HasDerivWithinAt
      (fun s => M.f0 v * ∑ i, ∑ j, X s i x * S s i j * basis U (W s) j v)
      (M.f0 v * ∑ i, ∑ j, (X' t i x * S t i j * basis U (W t) j v
        + X t i x * S' t i j * basis U (W t) j v
        + X t i x * S t i j * Sum.elim (0 : A → Iv → ℝ) (W' t) j v)) (Icc t₀ t₁) t := by
    refine HasDerivWithinAt.const_mul _ (HasDerivWithinAt.fun_sum fun i _ =>
      HasDerivWithinAt.fun_sum fun j _ => ?_)
    have := ((h.hX t ht i x).mul (h.hS t ht i j)).mul (hb j)
    convert this using 1
    simp only [Pi.mul_apply]
    ring
  have e : M.tangent (X t) (S t) (basis U (W t)) (X' t) (S' t) (W' t) x v
      = M.f0 v * ∑ i, ∑ j, (X' t i x * S t i j * basis U (W t) j v
        + X t i x * S' t i j * basis U (W t) j v
        + X t i x * S t i j * Sum.elim (0 : A → Iv → ℝ) (W' t) j v) := by
    simp only [tangent]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_add_distrib]
    congr 1
    rw [Fintype.sum_sum_type]
    simp
  rw [e]
  exact h1

/-- **Sec. 4** (arXiv 2101.12571): a solution of the equations of motion (10)-(12) satisfies the
Petrov-Galerkin condition (9), with the true time derivative of `f`. -/
theorem IsSolution.petrovGalerkin (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hS : ∀ t ∈ Icc t₀ t₁, IsUnit (S t).det) (h0 : M.IsFrame (X t₀) (basis U (W t₀)))
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    M.PetrovGalerkin (X t) (S t) (basis U (W t))
      (M.tangent (X t) (S t) (basis U (W t)) (X' t) (S' t) (W' t)) (M.rhs U X S W E t) :=
  (petrovGalerkin_iff (h.isFrame hS h0 t ht) (hS t ht) (h.gauge hS h0 ht) _).2
    ⟨h.eq10 t ht, h.eq11 t ht, h.eq12 t ht⟩

lemma IsSolution.hasDeriv_colK (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E') {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (k : A ⊕ P) (x : Ix) :
    HasDerivWithinAt (fun s => colK (X s) (S s) k x)
      (M.mom (basis U (W t) k) (M.rhs U X S W E t) x) (Icc t₀ t₁) t := by
  have h1 : HasDerivWithinAt (fun s => ∑ i, X s i x * S s i k)
      (∑ i, (X' t i x * S t i k + X t i x * S' t i k)) (Icc t₀ t₁) t :=
    HasDerivWithinAt.fun_sum fun i _ => (h.hX t ht i x).mul (h.hS t ht i k)
  have e : M.mom (basis U (W t) k) (M.rhs U X S W E t) x
      = ∑ i, (X' t i x * S t i k + X t i x * S' t i k) := by
    rw [Finset.sum_add_distrib, h.eq10 t ht k x]
    ring
  rw [e]
  exact h1

/-- **Sec. 5, the core** (arXiv 2101.12571), on the discrete phase space: since `U_a` is fixed,
`∂ₜ (φ, f)_v = (φ, D[f])_v` for every `φ ∈ span U`. -/
theorem IsSolution.hasDeriv_mom (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hF : ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t))) {φ : Iv → ℝ} (hφ : InSpan U φ) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (x : Ix) :
    HasDerivWithinAt (fun s => M.mom φ (M.lowRank (X s) (S s) (basis U (W s))) x)
      (M.mom φ (M.rhs U X S W E t) x) (Icc t₀ t₁) t := by
  obtain ⟨c, hc⟩ := hφ
  have hU : M.FixedOrtho U := fun a b => by simpa using (hF t ht).v (Sum.inl a) (Sum.inl b)
  have hW : ∀ s ∈ Icc t₀ t₁, ∀ p a, M.ipv (W s p) (U a) = 0 := fun s hs p a => by
    simpa using (hF s hs).v (Sum.inr p) (Sum.inl a)
  have e : ∀ s ∈ Icc t₀ t₁, M.mom φ (M.lowRank (X s) (S s) (basis U (W s))) x
      = ∑ a, c a * colK (X s) (S s) (Sum.inl a) x := by
    intro s hs
    rw [mom_inSpan hc]
    exact Finset.sum_congr rfl fun a _ => by rw [mom_fixed hU (hW s hs)]
  have h1 : HasDerivWithinAt (fun s => ∑ a, c a * colK (X s) (S s) (Sum.inl a) x)
      (∑ a, c a * M.mom (basis U (W t) (Sum.inl a)) (M.rhs U X S W E t) x) (Icc t₀ t₁) t :=
    HasDerivWithinAt.fun_sum fun a _ => (h.hasDeriv_colK ht _ x).const_mul _
  rw [mom_inSpan hc]
  exact h1.congr e (e t ht)

lemma const_of_deriv {g g' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt g (g' t) (Icc t₀ t₁) t)
    (h0 : ∀ t ∈ Ico t₀ t₁, g' t = 0) : ∀ t ∈ Icc t₀ t₁, g t = g t₀ := by
  refine constant_of_has_deriv_right_zero (fun t ht => (hg t ht).continuousWithinAt) fun t ht => ?_
  rw [← h0 t ht]
  exact (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

lemma hasDeriv_dx {J : Set ℝ} {t : ℝ} {u : ℝ → Ix → ℝ} {u' : Ix → ℝ}
    (hu : ∀ y, HasDerivWithinAt (fun s => u s y) (u' y) J t) (α : δ) (x : Ix) :
    HasDerivWithinAt (fun s => M.dx α (u s) x) (M.dx α u' x) J t := by
  have h1 : HasDerivWithinAt u u' J t := hasDerivWithinAt_pi.2 hu
  have h2 := (LinearMap.toContinuousLinearMap (M.dx α)).hasFDerivAt.comp_hasDerivWithinAt t h1
  exact hasDerivWithinAt_pi.1 h2 x

section Laws

variable [DecidableEq δ]

/-- **Sec. 5, the continuity equation** (arXiv 2101.12571), on the discrete phase space:
`∂ₜ ρ + ∇ ⋅ j = 0`. -/
theorem IsSolution.rho_law (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hF : ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t))) (hc : M.Conserves U) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (hI : ∀ x, M.VelIBP (M.lowRank (X t) (S t) (basis U (W t)) x)) (x : Ix) :
    HasDerivWithinAt (fun s => M.rho (M.lowRank (X s) (S s) (basis U (W s))) x)
      (-∑ α, M.dx α (M.cur (M.lowRank (X t) (S t) (basis U (W t))) α) x) (Icc t₀ t₁) t := by
  have h1 := h.hasDeriv_mom hF hc.one ht x
  have e : M.mom (fun _ => 1) (M.rhs U X S W E t) x
      = -∑ α, M.dx α (M.cur (M.lowRank (X t) (S t) (basis U (W t))) α) x := rho_vlasov (hI x)
  rw [e] at h1
  exact h1

/-- **Sec. 5, the momentum equation** (arXiv 2101.12571), on the discrete phase space:
`∂ₜ j + ∇ ⋅ σ = -E ρ`, for any curve `E`. -/
theorem IsSolution.cur_law (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hF : ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t))) (hc : M.Conserves U) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (hI : ∀ x, M.VelIBP (M.lowRank (X t) (S t) (basis U (W t)) x)) (β : δ)
    (x : Ix) :
    HasDerivWithinAt (fun s => M.cur (M.lowRank (X s) (S s) (basis U (W s))) β x)
      (-∑ α, M.dx α (M.sig (M.lowRank (X t) (S t) (basis U (W t))) α β) x
        - E t β x * M.rho (M.lowRank (X t) (S t) (basis U (W t))) x) (Icc t₀ t₁) t := by
  have h1 := h.hasDeriv_mom hF (hc.vel β) ht x
  have e : M.mom (M.vel β) (M.rhs U X S W E t) x
      = -∑ α, M.dx α (M.sig (M.lowRank (X t) (S t) (basis U (W t))) α β) x
        - E t β x * M.rho (M.lowRank (X t) (S t) (basis U (W t))) x := cur_vlasov (hI x) β
  rw [e] at h1
  exact h1

/-- **Sec. 5, the energy equation** (arXiv 2101.12571), on the discrete phase space:
`∂ₜ e + ∇ ⋅ Q = E ⋅ (∂ₜ E - j)`, for any differentiable curve `E`. -/
theorem IsSolution.dens_law (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hF : ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t))) (hc : M.Conserves U) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (hI : ∀ x, M.VelIBP (M.lowRank (X t) (S t) (basis U (W t)) x)) (x : Ix) :
    HasDerivWithinAt (fun s => M.dens (M.lowRank (X s) (S s) (basis U (W s))) (E s) x)
      (-∑ α, M.dx α (M.heat (M.lowRank (X t) (S t) (basis U (W t))) α) x
        + ∑ α, E t α x * (E' t α x - M.cur (M.lowRank (X t) (S t) (basis U (W t))) α x))
      (Icc t₀ t₁) t := by
  have h1 := (h.hasDeriv_mom hF hc.sq ht x).const_mul (1 / 2 : ℝ)
  have h2 : HasDerivWithinAt (fun s => (1 / 2 : ℝ) * ∑ α, E s α x ^ 2)
      ((1 / 2 : ℝ) * ∑ α, 2 * E t α x * E' t α x) (Icc t₀ t₁) t := by
    refine HasDerivWithinAt.const_mul _ (HasDerivWithinAt.fun_sum fun α _ => ?_)
    have := (h.hE t ht α x).pow 2
    convert this using 1
    simp
  have e : (1 / 2 : ℝ) * M.mom M.vsq (M.rhs U X S W E t) x
      = -∑ α, M.dx α (M.heat (M.lowRank (X t) (S t) (basis U (W t))) α) x
        - ∑ α, E t α x * M.cur (M.lowRank (X t) (S t) (basis U (W t))) α x := kin_vlasov (hI x)
  rw [e] at h1
  have h3 : HasDerivWithinAt (fun s => M.dens (M.lowRank (X s) (S s) (basis U (W s))) (E s) x) _
      (Icc t₀ t₁) t := h1.add h2
  refine h3.congr_deriv ?_
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have : ∑ α, (1 / 2 : ℝ) * (2 * E t α x * E' t α x) = ∑ α, E t α x * E' t α x :=
    Finset.sum_congr rfl fun α _ => by ring
  rw [this]
  ring

lemma sum_div (u : δ → Ix → ℝ) : ∑ x, M.hx x * ∑ α, M.dx α (u α) x = 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [sum_dx]

/-- **Sec. 5, conservation of mass** (arXiv 2101.12571), on the discrete phase space. -/
theorem IsSolution.mass_eq (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hF : ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t))) (hc : M.Conserves U)
    (hI : ∀ t ∈ Icc t₀ t₁, ∀ x, M.VelIBP (M.lowRank (X t) (S t) (basis U (W t)) x)) :
    ∀ t ∈ Icc t₀ t₁, M.mass (M.lowRank (X t) (S t) (basis U (W t)))
      = M.mass (M.lowRank (X t₀) (S t₀) (basis U (W t₀))) := by
  refine const_of_deriv (g := fun t => M.mass (M.lowRank (X t) (S t) (basis U (W t)))) (fun t ht =>
    HasDerivWithinAt.fun_sum fun x _ => (h.rho_law hF hc ht (hI t ht) x).const_mul _) fun t _ => ?_
  simp only [mul_neg, Finset.sum_neg_distrib, sum_div, neg_zero]

/-- **Sec. 5, conservation of momentum** (arXiv 2101.12571), on the discrete phase space: here the
field `E` must be the field of `f`. -/
theorem IsSolution.momentum_eq (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hF : ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t))) (hc : M.Conserves U)
    (hI : ∀ t ∈ Icc t₀ t₁, ∀ x, M.VelIBP (M.lowRank (X t) (S t) (basis U (W t)) x))
    (hE : ∀ t ∈ Icc t₀ t₁, ∃ φ, M.IsField (M.rho (M.lowRank (X t) (S t) (basis U (W t)))) (E t) φ)
    (β : δ) : ∀ t ∈ Icc t₀ t₁, M.momentum (M.lowRank (X t) (S t) (basis U (W t))) β
      = M.momentum (M.lowRank (X t₀) (S t₀) (basis U (W t₀))) β := by
  refine const_of_deriv (g := fun t => M.momentum (M.lowRank (X t) (S t) (basis U (W t))) β)
    (fun t ht => HasDerivWithinAt.fun_sum fun x _ =>
      (h.cur_law hF hc ht (hI t ht) β x).const_mul _) fun t ht => ?_
  obtain ⟨φ, hφ⟩ := hE t (Ico_subset_Icc_self ht)
  simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib, sum_div, neg_zero,
    hφ.sum_force β, sub_zero]

/-- **Sec. 5, conservation of energy** (arXiv 2101.12571), on the discrete phase space.  The term
`E ⋅ (∂ₜ E - j)` integrates to zero, which is the paper's `∂ₜ E = j`: the time derivative of the
Gauss law says `∇ ⋅ (∂ₜ E - j) = 0`, and `E` is a gradient. -/
theorem IsSolution.energy_eq (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hF : ∀ t ∈ Icc t₀ t₁, M.IsFrame (X t) (basis U (W t))) (hc : M.Conserves U)
    (hI : ∀ t ∈ Icc t₀ t₁, ∀ x, M.VelIBP (M.lowRank (X t) (S t) (basis U (W t)) x))
    (hE : ∀ t ∈ Icc t₀ t₁, ∃ φ, M.IsField (M.rho (M.lowRank (X t) (S t) (basis U (W t)))) (E t) φ) :
    ∀ t ∈ Icc t₀ t₁, M.energy (M.lowRank (X t) (S t) (basis U (W t))) (E t)
      = M.energy (M.lowRank (X t₀) (S t₀) (basis U (W t₀))) (E t₀) := by
  refine const_of_deriv (g := fun t => M.energy (M.lowRank (X t) (S t) (basis U (W t))) (E t))
    (fun t ht => HasDerivWithinAt.fun_sum fun x _ =>
      (h.dens_law hF hc ht (hI t ht) x).const_mul _) fun t ht => ?_
  have ht' := Ico_subset_Icc_self ht
  have hlt : t₀ < t₁ := ht.1.trans_lt ht.2
  obtain ⟨φ, hφ⟩ := hE t ht'
  obtain ⟨Y, hY⟩ : ∃ Y : δ → Ix → ℝ, Y = fun α =>
    E' t α - M.cur (M.lowRank (X t) (S t) (basis U (W t))) α := ⟨_, rfl⟩
  have hdiv : ∀ x, ∑ α, M.dx α (Y α) x = 0 := by
    intro x
    have h1 : HasDerivWithinAt (fun s => ∑ α, M.dx α (E s α) x) (∑ α, M.dx α (E' t α) x)
        (Icc t₀ t₁) t :=
      HasDerivWithinAt.fun_sum fun α _ => hasDeriv_dx (fun y => h.hE t ht' α y) α x
    have h2 : HasDerivWithinAt (fun s => 1 - M.rho (M.lowRank (X s) (S s) (basis U (W s))) x)
        (-(-∑ α, M.dx α (M.cur (M.lowRank (X t) (S t) (basis U (W t))) α) x)) (Icc t₀ t₁) t :=
      (h.rho_law hF hc ht' (hI t ht') x).const_sub 1
    have h3 := h1.congr (f := fun s => ∑ α, M.dx α (E s α) x) (fun _ _ => rfl) rfl
    have h4 : HasDerivWithinAt (fun s => ∑ α, M.dx α (E s α) x) _ (Icc t₀ t₁) t :=
      h2.congr (fun s hs => by
        obtain ⟨ψ, hψ⟩ := hE s hs
        exact hψ.gauss x) (by exact hφ.gauss x)
    have e := (uniqueDiffOn_Icc hlt t ht').eq_deriv _ h3 h4
    simp only [hY, map_sub, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [e]
    ring
  have e := sum_grad_mul (M := M) φ Y
  simp only [hdiv, mul_zero, Finset.sum_const_zero, neg_zero] at e
  have e2 : ∀ x, M.hx x * (-∑ α, M.dx α (M.heat (M.lowRank (X t) (S t) (basis U (W t))) α) x
      + ∑ α, E t α x * (E' t α x - M.cur (M.lowRank (X t) (S t) (basis U (W t))) α x))
      = -(M.hx x * ∑ α, M.dx α (M.heat (M.lowRank (X t) (S t) (basis U (W t))) α) x)
        - M.hx x * ∑ α, M.dx α φ x * Y α x := by
    intro x
    have : ∑ α, E t α x * (E' t α x - M.cur (M.lowRank (X t) (S t) (basis U (W t))) α x)
        = -∑ α, M.dx α φ x * Y α x := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hφ.grad α, hY]
      simp
    rw [this]
    ring
  simp only [e2, Finset.sum_sub_distrib, Finset.sum_neg_distrib, sum_div, e, neg_zero, sub_zero]

/-- **Sec. 5** (arXiv 2101.12571), on the discrete phase space, in one statement.  From orthonormal
initial factors, as long as `S` is invertible: if the Vlasov moments integrate by parts exactly, and
`E` is the field of `f`, then mass, momentum and energy are conserved exactly. -/
theorem IsSolution.conservation (h : M.IsSolution U t₀ t₁ X X' S S' W W' E E')
    (hS : ∀ t ∈ Icc t₀ t₁, IsUnit (S t).det) (h0 : M.IsFrame (X t₀) (basis U (W t₀)))
    (hc : M.Conserves U)
    (hI : ∀ t ∈ Icc t₀ t₁, ∀ x, M.VelIBP (M.lowRank (X t) (S t) (basis U (W t)) x))
    (hE : ∀ t ∈ Icc t₀ t₁, ∃ φ, M.IsField (M.rho (M.lowRank (X t) (S t) (basis U (W t)))) (E t) φ) :
    ∀ t ∈ Icc t₀ t₁, M.mass (M.lowRank (X t) (S t) (basis U (W t)))
        = M.mass (M.lowRank (X t₀) (S t₀) (basis U (W t₀))) ∧
      (∀ β, M.momentum (M.lowRank (X t) (S t) (basis U (W t))) β
        = M.momentum (M.lowRank (X t₀) (S t₀) (basis U (W t₀))) β) ∧
      M.energy (M.lowRank (X t) (S t) (basis U (W t))) (E t)
        = M.energy (M.lowRank (X t₀) (S t₀) (basis U (W t₀))) (E t₀) := by
  have hF := h.isFrame hS h0
  exact fun t ht => ⟨h.mass_eq hF hc hI t ht, fun β => h.momentum_eq hF hc hI hE β t ht,
    h.energy_eq hF hc hI hE t ht⟩

end Laws

end Solution

end Continuous

/-! ### Many steps of the scheme -/

section Run

variable [DecidableEq δ] {U : A → Iv → ℝ} {τ : ℝ} {N : ℕ} {f : ℕ → Ix → Iv → ℝ}
  {E : ℕ → δ → Ix → ℝ} {φ : ℕ → Ix → ℝ}

/-- **Sec. 6.1, conservation over many steps** (arXiv 2101.12571), on the discrete phase space, for
every scheme that advances the moments by explicit Euler: mass and momentum are conserved exactly
and the energy grows by the sum of the defects of eq. (17). -/
theorem run_conservation (hstep : ∀ n < N, M.MomStep U τ (M.vlasov (E n) (f n)) (f n) (f (n + 1)))
    (hc : M.Conserves U) (hI : ∀ n < N, ∀ x, M.VelIBP (f n x))
    (hF : ∀ n ≤ N, M.IsField (M.rho (f n)) (E n) (φ n)) :
    ∀ n ≤ N, M.mass (f n) = M.mass (f 0) ∧ (∀ β, M.momentum (f n) β = M.momentum (f 0) β) ∧
      M.energy (f n) (E n) = M.energy (f 0) (E 0)
        + ∑ k ∈ Finset.range n, (1 / 2) * ∑ x, M.hx x * ∑ α, (E (k + 1) α x - E k α x) ^ 2 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hlt : n < N := hn
    obtain ⟨h1, h2, h3⟩ := ih hlt.le
    refine ⟨?_, fun β => ?_, ?_⟩
    · rw [(hstep n hlt).mass_eq hc (hI n hlt), h1]
    · rw [(hstep n hlt).momentum_eq hc (hI n hlt) (hF n hlt.le) β, h2]
    · have e := (hstep n hlt).energy_defect hc (hI n hlt) (hF n hlt.le) (hF (n + 1) hn)
      rw [Finset.sum_range_succ, ← add_assoc, ← h3, ← e]
      ring

/-- **Sec. 6.1** (arXiv 2101.12571), on the discrete phase space: the energy error of the scheme is
first order and one-sided.  After `n` steps it is at most `n τ² J / 2`, so at most `T τ J / 2` at
time `T = n τ`, where `J` bounds `∫ j² dx`. -/
theorem run_energy_le {J : ℝ}
    (hstep : ∀ n < N, M.MomStep U τ (M.vlasov (E n) (f n)) (f n) (f (n + 1)))
    (hc : M.Conserves U) (hI : ∀ n < N, ∀ x, M.VelIBP (f n x))
    (hF : ∀ n ≤ N, M.IsField (M.rho (f n)) (E n) (φ n))
    (hJ : ∀ n < N, ∑ x, M.hx x * ∑ α, M.cur (f n) α x ^ 2 ≤ J) :
    ∀ n ≤ N, 0 ≤ M.energy (f n) (E n) - M.energy (f 0) (E 0) ∧
      M.energy (f n) (E n) - M.energy (f 0) (E 0) ≤ n * τ ^ 2 * J / 2 := by
  intro n hn
  have e := (run_conservation hstep hc hI hF n hn).2.2
  have e2 : M.energy (f n) (E n) - M.energy (f 0) (E 0)
      = ∑ k ∈ Finset.range n, (1 / 2) * ∑ x, M.hx x * ∑ α, (E (k + 1) α x - E k α x) ^ 2 := by
    rw [e]
    ring
  rw [e2]
  constructor
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
      mul_nonneg (M.hx_pos x).le (Finset.sum_nonneg fun α _ => sq_nonneg _))
  · have hb : ∀ k ∈ Finset.range n, (1 / 2) * ∑ x, M.hx x * ∑ α, (E (k + 1) α x - E k α x) ^ 2
        ≤ τ ^ 2 * J / 2 := by
      intro k hk
      have hk' : k < N := (Finset.mem_range.1 hk).trans_le hn
      have h1 := (hstep k hk').field_sub_le hc (hI k hk') (hF k hk'.le) (hF (k + 1) hk')
      have h2 := mul_le_mul_of_nonneg_left (hJ k hk') (sq_nonneg τ)
      linarith
    have := Finset.sum_le_card_nsmul _ _ _ hb
    simp only [Finset.card_range, nsmul_eq_mul] at this
    linarith

end Run

section FactorRun

variable {U : A → Iv → ℝ} {τ : ℝ} {N : ℕ} {E : ℕ → δ → Ix → ℝ} {X : ℕ → A ⊕ P → Ix → ℝ}
  {S St : ℕ → Matrix (A ⊕ P) (A ⊕ P) ℝ} {W Wt : ℕ → P → Iv → ℝ}

/-- **Sec. 6.1, eqs. (13)-(16)** (arXiv 2101.12571), on the discrete phase space: along the scheme
(14), (15), (16) followed by a re-orthonormalization of the `W_p`, the orthogonality
`⟨W_p, U_a⟩_v = 0` is kept exactly and every step advances the moments against the `U_a` by explicit
Euler.  With `run_conservation` this gives the conservation laws of the scheme. -/
theorem euler_reorth_run {R : ℕ → Matrix P P ℝ}
    (hstep : ∀ n < N, M.IsEuler U τ (M.vlasov (E n) (M.lowRank (X n) (S n) (basis U (W n))))
      (X n) (X (n + 1)) (S n) (St n) (W n) (Wt n))
    (hR : ∀ n < N, IsReorth (R n) (St n) (S (n + 1)) (Wt n) (W (n + 1)))
    (hS : ∀ n < N, IsUnit (St n).det) (hU : M.FixedOrtho U)
    (hW : ∀ p a, M.ipv (W 0 p) (U a) = 0) :
    (∀ n ≤ N, ∀ p a, M.ipv (W n p) (U a) = 0) ∧
      ∀ n < N, M.MomStep U τ (M.vlasov (E n) (M.lowRank (X n) (S n) (basis U (W n))))
        (M.lowRank (X n) (S n) (basis U (W n)))
        (M.lowRank (X (n + 1)) (S (n + 1)) (basis U (W (n + 1)))) := by
  have hb : ∀ n, n < N → (∀ p a, M.ipv (W n p) (U a) = 0) → M.IsBalanced U τ
      (M.vlasov (E n) (M.lowRank (X n) (S n) (basis U (W n)))) (X n) (X (n + 1)) (S n) (S (n + 1))
      (W (n + 1)) := fun n hn hp =>
    ((hstep n hn).isBalanced (hS n hn) hU hp).reorth (hR n hn)
  have hperp : ∀ n ≤ N, ∀ p a, M.ipv (W n p) (U a) = 0 := by
    intro n
    induction n with
    | zero => intro _; exact hW
    | succ n ih =>
      intro hn
      exact (hb n hn (ih (Nat.le_of_succ_le hn))).perp
  exact ⟨hperp, fun n hn => (hb n hn (hperp n hn.le)).momStep hU (hperp n hn.le)⟩

/-- `R = 1`: no re-orthonormalization. -/
lemma IsReorth.refl (S : Matrix (A ⊕ P) (A ⊕ P) ℝ) (W : P → Iv → ℝ) : IsReorth 1 S S W W where
  unit := by simp
  w := by simp [Matrix.one_apply]
  s_fixed := by simp
  s_free := by simp [Matrix.one_apply]

/-- **Sec. 6.1, eqs. (13)-(16)** (arXiv 2101.12571), on the discrete phase space: the scheme (14),
(15), (16) itself, without re-orthonormalization. -/
theorem euler_run
    (hstep : ∀ n < N, M.IsEuler U τ (M.vlasov (E n) (M.lowRank (X n) (S n) (basis U (W n))))
      (X n) (X (n + 1)) (S n) (S (n + 1)) (W n) (W (n + 1)))
    (hS : ∀ n < N, IsUnit (S (n + 1)).det) (hU : M.FixedOrtho U)
    (hW : ∀ p a, M.ipv (W 0 p) (U a) = 0) :
    (∀ n ≤ N, ∀ p a, M.ipv (W n p) (U a) = 0) ∧
      ∀ n < N, M.MomStep U τ (M.vlasov (E n) (M.lowRank (X n) (S n) (basis U (W n))))
        (M.lowRank (X n) (S n) (basis U (W n)))
        (M.lowRank (X (n + 1)) (S (n + 1)) (basis U (W (n + 1)))) :=
  euler_reorth_run (St := fun n => S (n + 1)) (Wt := fun n => W (n + 1)) (R := fun _ => 1) hstep
    (fun _ _ => IsReorth.refl _ _) hS hU hW

/-- **Sec. 6.1** (arXiv 2101.12571), on the discrete phase space, in one statement.  Along the
scheme (14), (15), (16): `⟨W_p, U_a⟩_v = 0`, mass and momentum are exact, and the energy is exact up
to the sum of the defects `½ ∫ (E^{n+1} - E^n)² dx` of eq. (17). -/
theorem euler_conservation [DecidableEq δ] {φ : ℕ → Ix → ℝ}
    (hstep : ∀ n < N, M.IsEuler U τ (M.vlasov (E n) (M.lowRank (X n) (S n) (basis U (W n))))
      (X n) (X (n + 1)) (S n) (S (n + 1)) (W n) (W (n + 1)))
    (hS : ∀ n < N, IsUnit (S (n + 1)).det) (hU : M.FixedOrtho U) (hc : M.Conserves U)
    (hW : ∀ p a, M.ipv (W 0 p) (U a) = 0)
    (hI : ∀ n < N, ∀ x, M.VelIBP (M.lowRank (X n) (S n) (basis U (W n)) x))
    (hF : ∀ n ≤ N, M.IsField (M.rho (M.lowRank (X n) (S n) (basis U (W n)))) (E n) (φ n)) :
    ∀ n ≤ N, (∀ p a, M.ipv (W n p) (U a) = 0) ∧
      M.mass (M.lowRank (X n) (S n) (basis U (W n)))
        = M.mass (M.lowRank (X 0) (S 0) (basis U (W 0))) ∧
      (∀ β, M.momentum (M.lowRank (X n) (S n) (basis U (W n))) β
        = M.momentum (M.lowRank (X 0) (S 0) (basis U (W 0))) β) ∧
      M.energy (M.lowRank (X n) (S n) (basis U (W n))) (E n)
        = M.energy (M.lowRank (X 0) (S 0) (basis U (W 0))) (E 0)
          + ∑ k ∈ Finset.range n, (1 / 2) * ∑ x, M.hx x * ∑ α, (E (k + 1) α x - E k α x) ^ 2 := by
  obtain ⟨h1, h2⟩ := euler_run hstep hS hU hW
  have h3 := run_conservation (f := fun n => M.lowRank (X n) (S n) (basis U (W n))) h2 hc hI hF
  exact fun n hn => ⟨h1 n hn, h3 n hn⟩

end FactorRun

/-- **Sec. 6.1, eq. (15) as printed** (arXiv 2101.12571).  The paper prints `(S^{n+1})⁻¹_{ik}` in
(15).  With this index order `∑_i X_i^{n+1} S_ij^{n+1} = K_j^{n+1}`, for all `K^{n+1}`, holds only
if `S^{n+1}` is symmetric.  So (15) is a misprint for `(S^{n+1})⁻¹_{ki}`, which is what `IsEuler`
uses (`IsEuler.colK_eq`). -/
theorem eq15_as_printed_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Matrix ι ι ℝ}
    (hT : IsUnit T.det) :
    (∀ K : ι → ℝ, ∀ j, ∑ i, (∑ k, T⁻¹ i k * K k) * T i j = K j) ↔ Tᵀ = T := by
  have hinv1 : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hT
  have hinv2 : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hT
  have key : ∀ (K : ι → ℝ) j, ∑ i, (∑ k, T⁻¹ i k * K k) * T i j
      = ∑ k, K k * ((T⁻¹)ᵀ * T) k j := by
    intro K j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  constructor
  · intro h
    have e : (T⁻¹)ᵀ * T = 1 := by
      ext m j
      have := h (fun k => if k = m then 1 else 0) j
      rw [key] at this
      simpa [Matrix.one_apply, eq_comm] using this
    calc Tᵀ = Tᵀ * ((T⁻¹)ᵀ * T) := by rw [e, mul_one]
      _ = (T⁻¹ * T)ᵀ * T := by rw [← mul_assoc, Matrix.transpose_mul]
      _ = T := by rw [hinv1]; simp
  · intro h K j
    have e : (T⁻¹)ᵀ * T = 1 := by
      calc (T⁻¹)ᵀ * T = (T⁻¹)ᵀ * Tᵀ := by rw [h]
        _ = (T * T⁻¹)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = 1 := by rw [hinv2, Matrix.transpose_one]
    rw [key, e]
    simp [Matrix.one_apply]

/-! ### The classical scheme: eq. (7) -/

section Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The time derivative of the classical ansatz (3) `f = ∑_ij X_i S_ij V_j`. -/
def classicD (X Xd : ι → Ix → ℝ) (S Sd : Matrix ι κ ℝ) (V Vd : κ → Iv → ℝ) : Ix → Iv → ℝ :=
  fun x v => ∑ i, ∑ j, (Xd i x * S i j * V j v + X i x * Sd i j * V j v + X i x * S i j * Vd j v)

variable (M) in
/-- The classical equations of motion (4), (5), (6), at one instant, with right-hand side `G`.
Unweighted: the classical scheme works in `L²`. -/
structure IsClassical (X Xd : ι → Ix → ℝ) (S Sd : Matrix ι κ ℝ) (V Vd : κ → Iv → ℝ)
    (G : Ix → Iv → ℝ) : Prop where
  eq4 : ∀ j x, ∑ i, (Xd i x * S i j + X i x * Sd i j) = M.mom (V j) G x
  eq5 : ∀ i j, Sd i j = M.pair (X i) (V j) G
  eq6 : ∀ i v, ∑ j, (Sd i j * V j v + S i j * Vd j v) = M.momX (X i) G v

variable (M) in
/-- The right-hand side of eq. (7). -/
def rhs7 (X : ι → Ix → ℝ) (V : κ → Iv → ℝ) (G : Ix → Iv → ℝ) (x : Ix) : ℝ :=
  ∑ j, M.mom (V j) G x * ∑ v, M.hv v * V j v
    - ∑ i, ∑ j, X i x * M.pair (X i) (V j) G * ∑ v, M.hv v * V j v
    + ∑ i, X i x * M.pair (X i) (fun _ => 1) G

variable (M) in
/-- The residual `1 - ∑_j (1, V_j)_v V_j` of the constant function. -/
def oneRes (V : κ → Iv → ℝ) (v : Iv) : ℝ := 1 - ∑ j, (∑ w, M.hv w * V j w) * V j v

/-- **Sec. 4, eq. (7)** (arXiv 2101.12571), on the discrete phase space, with `G = D[f]` or any
other right-hand side.  Along the classical equations of motion (4), (5), (6),
`∂ₜ ρ = ∑_j (V_j, G)_v (1, V_j)_v - ∑_ij X_i (X_i V_j, G)_{xv} (1, V_j)_v
+ ∑_i X_i (X_i, G)_{xv}`. -/
theorem eq7 {X Xd : ι → Ix → ℝ} {S Sd : Matrix ι κ ℝ} {V Vd : κ → Iv → ℝ} {G : Ix → Iv → ℝ}
    (h : M.IsClassical X Xd S Sd V Vd G) (x : Ix) :
    ∑ v, M.hv v * classicD X Xd S Sd V Vd x v = M.rhs7 X V G x := by
  have e : ∀ v, classicD X Xd S Sd V Vd x v = ∑ j, M.mom (V j) G x * V j v
      - ∑ i, ∑ j, X i x * M.pair (X i) (V j) G * V j v + ∑ i, X i x * M.momX (X i) G v := by
    intro v
    have e1 : ∑ j, M.mom (V j) G x * V j v
        = ∑ i, ∑ j, (Xd i x * S i j * V j v + X i x * Sd i j * V j v) := by
      simp only [← h.eq4, Finset.sum_mul, add_mul]
      rw [Finset.sum_comm]
    have e2 : ∑ i, X i x * M.momX (X i) G v
        = ∑ i, ∑ j, (X i x * Sd i j * V j v + X i x * S i j * Vd j v) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h.eq6, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e3 : ∑ i, ∑ j, X i x * M.pair (X i) (V j) G * V j v
        = ∑ i, ∑ j, X i x * Sd i j * V j v := by
      simp only [h.eq5]
    rw [e1, e2, e3]
    simp only [classicD, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [e, rhs7, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  · congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pair_eq_sum, one_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring

/-- **Sec. 4, eq. (7)** (arXiv 2101.12571), on the discrete phase space: the right-hand side of (7)
differs from `(1, G)_v` exactly by the part of the moment against the residual of `1` that lies
outside of `span X`.  This is the exact form of the paper's argument. -/
theorem rhs7_sub (X : ι → Ix → ℝ) (V : κ → Iv → ℝ) (G : Ix → Iv → ℝ) (x : Ix) :
    M.rhs7 X V G x - M.mom (fun _ => 1) G x
      = -M.mom (M.oneRes V) G x + ∑ i, X i x * M.pair (X i) (M.oneRes V) G := by
  have e1 : ∀ y, M.mom (M.oneRes V) G y
      = M.mom (fun _ => 1) G y - ∑ j, (∑ w, M.hv w * V j w) * M.mom (V j) G y := by
    intro y
    have : ∀ v, M.hv v * (M.oneRes V v * G y v) = M.hv v * (1 * G y v)
        - ∑ j, (∑ w, M.hv w * V j w) * (M.hv v * (V j v * G y v)) := by
      intro v
      simp only [oneRes, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => by ring
    simp only [mom]
    rw [Finset.sum_congr rfl (fun v _ => this v), Finset.sum_sub_distrib, Finset.sum_comm]
    simp only [← Finset.mul_sum]
  have e2 : ∀ i, M.pair (X i) (M.oneRes V) G = M.pair (X i) (fun _ => 1) G
      - ∑ j, (∑ w, M.hv w * V j w) * M.pair (X i) (V j) G := by
    intro i
    simp only [pair, e1, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring
  simp only [e2, rhs7, mul_sub, Finset.sum_sub_distrib, e1]
  have e3 : ∑ i, X i x * ∑ j, (∑ w, M.hv w * V j w) * M.pair (X i) (V j) G
      = ∑ i, ∑ j, X i x * M.pair (X i) (V j) G * ∑ v, M.hv v * V j v := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ j, (∑ w, M.hv w * V j w) * M.mom (V j) G x
      = ∑ j, M.mom (V j) G x * ∑ v, M.hv v * V j v :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [e3, e4]
  ring

/-- **Sec. 4** (arXiv 2101.12571), on the discrete phase space: if `1 = ∑_j c_j V_j`, with `V`
orthonormal in the unweighted `L²`, the right-hand side of (7) collapses to `(1, G)_v`. -/
theorem rhs7_collapse [DecidableEq κ] {V : κ → Iv → ℝ}
    (hV : ∀ k l, ∑ v, M.hv v * (V k v * V l v) = if k = l then 1 else 0) {c : κ → ℝ}
    (hc : ∀ v, ∑ j, c j * V j v = 1) (X : ι → Ix → ℝ) (G : Ix → Iv → ℝ) (x : Ix) :
    M.rhs7 X V G x = M.mom (fun _ => 1) G x := by
  have hres : M.oneRes V = 0 := by
    have e : ∀ j, ∑ w, M.hv w * V j w = c j := by
      intro j
      have : ∑ w, M.hv w * V j w = ∑ w, M.hv w * (V j w * ∑ l, c l * V l w) :=
        Finset.sum_congr rfl fun w _ => by rw [hc, mul_one]
      rw [this]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ l, ∑ w, M.hv w * (V j w * (c l * V l w))
          = c l * ∑ w, M.hv w * (V j w * V l w) := fun l => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring
      simp only [this, hV, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]
    ext v
    simp only [oneRes, e, hc, sub_self, Pi.zero_apply]
  have := rhs7_sub (M := M) X V G x
  have e0 : ∀ y, M.mom (fun _ => 0) G y = 0 := fun y => by simp [mom]
  simp only [hres] at this
  have e1 : M.mom 0 G x = 0 := e0 x
  have e2 : ∀ i, M.pair (X i) 0 G = 0 := fun i => by
    have : ∀ y, M.mom 0 G y = 0 := e0
    simp [pair, this]
  simp only [e1, e2, mul_zero, Finset.sum_const_zero, neg_zero, add_zero] at this
  linarith

/-- **Sec. 4** (arXiv 2101.12571), on the discrete phase space.  The converse of the collapse.  If
`X` does not span all functions of `x`, then `1 ∈ span V` is also necessary: otherwise (7) differs
from `(1, G)_v` for some right-hand side. -/
theorem exists_rhs7_ne {X : ι → Ix → ℝ} {V : κ → Iv → ℝ} {u : Ix → ℝ} (hu : u ≠ 0)
    (hX : ∀ i, M.ipx (X i) u = 0) (hres : M.oneRes V ≠ 0) :
    ∃ (G : Ix → Iv → ℝ) (x : Ix), M.rhs7 X V G x ≠ M.mom (fun _ => 1) G x := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hu
  obtain ⟨c, hc⟩ : ∃ c, c = ∑ v, M.hv v * M.oneRes V v ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    obtain ⟨v₀, hv₀⟩ := Function.ne_iff.1 hres
    have hv₁ : M.oneRes V v₀ ≠ 0 := hv₀
    rw [hc]
    exact Finset.sum_pos' (fun v _ => mul_nonneg (M.hv_pos v).le (sq_nonneg _))
      ⟨v₀, Finset.mem_univ _, mul_pos (M.hv_pos v₀)
        (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hv₁).symm)⟩
  have e1 : ∀ y, M.mom (M.oneRes V) (fun y v => u y * M.oneRes V v) y = u y * c := by
    intro y
    rw [hc, mom, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e2 : ∀ i, M.pair (X i) (M.oneRes V) (fun y v => u y * M.oneRes V v) = 0 := by
    intro i
    have : M.pair (X i) (M.oneRes V) (fun y v => u y * M.oneRes V v) = M.ipx (X i) u * c := by
      simp only [pair, e1, ipx, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, hX, zero_mul]
  refine ⟨fun y v => u y * M.oneRes V v, x, fun h => ?_⟩
  have := rhs7_sub (M := M) X V (fun y v => u y * M.oneRes V v) x
  rw [h, sub_self, e1] at this
  simp only [e2, mul_zero, Finset.sum_const_zero, add_zero] at this
  have h0 : u x * c = 0 := by linarith
  exact hx ((mul_eq_zero.1 h0).resolve_right hc0.ne')

/-- **Sec. 4** (arXiv 2101.12571): "constant functions do not lie in `L²(ℝ^d)`", for `d ≥ 1`. -/
theorem one_not_memLp {d : ℕ} [NeZero d] :
    ¬ MeasureTheory.MemLp (fun _ : Fin d → ℝ => (1 : ℝ)) 2 MeasureTheory.volume := by
  have hne : Nonempty (Fin d) := ⟨0⟩
  have h : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) Set.univ = ⊤ :=
    MeasureTheory.measure_univ_of_isAddLeftInvariant MeasureTheory.volume
  intro hm
  have h2 := (MeasureTheory.memLp_const_iff (μ := (MeasureTheory.volume :
    MeasureTheory.Measure (Fin d → ℝ))) (c := (1 : ℝ)) (p := 2) (by norm_num) (by norm_num)).1 hm
  rcases h2 with h1 | h1
  · exact one_ne_zero h1
  · rw [h] at h1
    exact lt_irrefl _ h1

/-- **Sec. 4** (arXiv 2101.12571): hence `1 ∉ span {V_j}`, for all `V_j ∈ L²(ℝ^d)`, `d ≥ 1`. -/
theorem one_notMem_span {d : ℕ} [NeZero d] {V : κ → (Fin d → ℝ) → ℝ}
    (hV : ∀ j, MeasureTheory.MemLp (V j) 2 MeasureTheory.volume) (c : κ → ℝ) :
    ¬ (fun _ => (1 : ℝ)) =ᵐ[MeasureTheory.volume] fun v => ∑ j, c j * V j v := by
  intro h
  have h1 : MeasureTheory.MemLp (fun v => ∑ j, c j * V j v) 2 MeasureTheory.volume :=
    MeasureTheory.memLp_finsetSum _ fun j _ => (hV j).const_mul _
  exact one_not_memLp (h1.ae_eq h.symm)

end Classical

/-! ### The hypotheses can hold -/

/-- **Sec. 6.1, exact integration by parts** (arXiv 2101.12571), a caveat.  `VelIBP` is a hypothesis
on the state, not on the grid: a discrete derivative that annihilates constants, as FFT or periodic
centered differences do, does not integrate by parts against `v` on the constant function.  On such
a grid `VelIBP g` needs that `g` vanishes at the velocity boundary, which the paper's
`f = f_{0v} ∑ X_i S_ij V_j` does only approximately. -/
theorem not_velIBP_const [DecidableEq δ] [Nonempty Iv] (α : δ) (h : M.dv α (fun _ => 1) = 0) :
    ¬ M.VelIBP (fun _ => 1) := by
  intro hI
  have e := hI.vel α α
  simp only [h, Pi.zero_apply, mul_zero, Finset.sum_const_zero, ite_true, mul_one] at e
  have hpos : 0 < ∑ v, M.hv v := Finset.sum_pos (fun v _ => M.hv_pos v) Finset.univ_nonempty
  linarith

section Solvability

/-- Non-vacuity for arXiv 2101.12571, eq. (2): the discrete Poisson problem is solvable, if the
`∂_{x_α}` see all nonconstant functions and the plasma is neutral.  So the `IsField` hypotheses are
no restriction, by conservation of mass. -/
theorem exists_isField (hker : ∀ u : Ix → ℝ, (∀ α, M.dx α u = 0) → ∃ c : ℝ, u = fun _ => c)
    {ρ : Ix → ℝ} (hρ : ∑ x, M.hx x * (1 - ρ x) = 0) : ∃ E φ, M.IsField ρ E φ := by
  classical
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (Ix → ℝ) →ₗ[ℝ] ℝ, ∀ u, ℓ u = ∑ x, M.hx x * u x :=
    ⟨∑ x, M.hx x • LinearMap.proj x, fun u => by simp [LinearMap.sum_apply]⟩
  obtain ⟨L, hL⟩ : ∃ L : (Ix → ℝ) →ₗ[ℝ] (Ix → ℝ), ∀ u x, L u x = -∑ α, M.dx α (M.dx α u) x :=
    ⟨-∑ α, (M.dx α) ∘ₗ (M.dx α), fun u x => by
      simp [LinearMap.sum_apply, Finset.sum_apply]⟩
  have hLH : ∀ u ∈ LinearMap.ker ℓ, L u ∈ LinearMap.ker ℓ := by
    intro u _
    rw [LinearMap.mem_ker, hℓ]
    simp only [hL, mul_neg, Finset.sum_neg_distrib, sum_div, neg_zero]
  have hinj : Function.Injective (L.restrict hLH) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, hu⟩ h0
    have hu0 : L u = 0 := congrArg Subtype.val h0
    have e : ∑ α, ∑ x, M.hx x * M.dx α u x ^ 2 = 0 := by
      have e1 : ∑ x, M.hx x * (u x * L u x) = ∑ α, ∑ x, M.hx x * M.dx α u x ^ 2 := by
        simp only [hL, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [M.dx_skew α u (M.dx α u), neg_neg]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [← e1, hu0]
      simp
    have hdx : ∀ α, M.dx α u = 0 := by
      intro α
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => Finset.sum_nonneg fun x _ =>
        mul_nonneg (M.hx_pos x).le (sq_nonneg _))).1 e α (Finset.mem_univ α)
      ext x
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        mul_nonneg (M.hx_pos x).le (sq_nonneg _))).1 h1 x (Finset.mem_univ x)
      have h3 := (mul_eq_zero.1 h2).resolve_left (M.hx_pos x).ne'
      exact pow_eq_zero_iff two_ne_zero |>.1 h3
    obtain ⟨c, hc⟩ := hker u hdx
    have h4 : ℓ u = 0 := hu
    rw [hℓ, hc] at h4
    ext x
    have h5 : c * ∑ y, M.hx y = 0 := by
      rw [Finset.mul_sum]
      rw [← h4]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hpos : 0 < ∑ y, M.hx y :=
      Finset.sum_pos (fun y _ => M.hx_pos y) ⟨x, Finset.mem_univ x⟩
    have h6 : c = 0 := (mul_eq_zero.1 h5).resolve_right hpos.ne'
    simp [hc, h6]
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨⟨φ, hφ⟩, hφ2⟩ := hsurj ⟨fun x => 1 - ρ x, by rw [LinearMap.mem_ker, hℓ]; exact hρ⟩
  have hφ3 : L φ = fun x => 1 - ρ x := congrArg Subtype.val hφ2
  refine ⟨fun α => -M.dx α φ, φ, ⟨fun _ => rfl, fun x => ?_⟩⟩
  have := congrFun hφ3 x
  rw [hL] at this
  simp only [map_neg, Pi.neg_apply, Finset.sum_neg_distrib]
  exact this

/-- Non-vacuity for arXiv 2101.12571, Sec. 6.1: for small `τ`, the matrix `S^{n+1}` of (14) is
invertible, so that the scheme is well defined: the step exists. -/
theorem exists_isEuler (U : A → Iv → ℝ) (X : A ⊕ P → Ix → ℝ) {S : Matrix (A ⊕ P) (A ⊕ P) ℝ}
    (W : P → Iv → ℝ) (G : Ix → Iv → ℝ) (hS : IsUnit S.det) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), ∃ X' S' W', IsUnit (S' : Matrix (A ⊕ P) (A ⊕ P) ℝ).det ∧
      M.IsEuler U τ G X X' S S' W W' := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (A ⊕ P) (A ⊕ P) ℝ,
      B = Matrix.of fun k l => M.pair (X k) (basis U W l) G := ⟨_, rfl⟩
  have hc : ContinuousAt (fun τ : ℝ => (S + τ • B).det) 0 := by
    have : Continuous (fun τ : ℝ => S + τ • B) := by fun_prop
    exact (this.matrix_det).continuousAt
  have h0 : (fun τ : ℝ => (S + τ • B).det) 0 ≠ 0 := by
    simpa using hS.ne_zero
  filter_upwards [hc.eventually_ne h0] with τ hτ
  refine ⟨fun i x => ∑ k, (S + τ • B)⁻¹ k i * (colK X S k x + τ * M.mom (basis U W k) G x),
    S + τ • B, fun p v => W p v + τ * ∑ q, ∑ i, (gramFree S)⁻¹ p q * S i (Sum.inr q)
      * M.freeRhs X (basis U W) G i v, isUnit_iff_ne_zero.2 hτ, ⟨fun k l => ?_, fun i x => rfl,
      fun p v => rfl⟩⟩
  simp [hB]

end Solvability

end Model

/-! ### An instance: five periodic nodes in `x`, four nodes in `v` -/

namespace Ex

open Model

/-- Centered differences on five periodic nodes. -/
def dx : (Fin 5 → ℝ) →ₗ[ℝ] Fin 5 → ℝ where
  toFun u i := (u (i + 1) - u (i - 1)) / 2
  map_add' u w := by
    ext i
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The weak derivative on the nodes `-7, -1, 1, 7`: minus the transpose of the matrix that
differentiates the cubic interpolant. -/
def dv : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ :=
  Matrix.mulVecLin !![61 / 168, 1 / 42, -1 / 56, 1 / 14; -7 / 6, 11 / 24, 1 / 2, -7 / 8;
    7 / 8, -1 / 2, -11 / 24, 7 / 6; -1 / 14, 1 / 56, -1 / 42, -61 / 168]

/-- The velocity nodes. -/
def vel : Fin 4 → ℝ := ![-7, -1, 1, 7]

/-- The instance of the model. -/
def M : Model (Fin 5) (Fin 4) Unit where
  hx _ := 1
  hv _ := 1
  f0 _ := 1 / 4
  vel _ := vel
  dx _ := dx
  dv _ := dv
  hx_pos _ := one_pos
  hv_pos _ := one_pos
  f0_pos _ := by norm_num
  dx_skew _ u w := by
    have h : (-1 : Fin 5) = 4 := rfl
    simp [dx, Fin.sum_univ_five, h]
    ring
  dx_const _ := by
    ext i
    simp [dx]
  dx_comm _ _ _ := rfl

lemma dv_apply (g : Fin 4 → ℝ) :
    dv g = ![61 / 168 * g 0 + 1 / 42 * g 1 - 1 / 56 * g 2 + 1 / 14 * g 3,
      -7 / 6 * g 0 + 11 / 24 * g 1 + 1 / 2 * g 2 - 7 / 8 * g 3,
      7 / 8 * g 0 - 1 / 2 * g 1 - 11 / 24 * g 2 + 7 / 6 * g 3,
      -1 / 14 * g 0 + 1 / 56 * g 1 - 1 / 42 * g 2 - 61 / 168 * g 3] := by
  ext i
  fin_cases i <;> simp [dv, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- Integration by parts is exact against `1`, `v`, `v²`, on all functions. -/
lemma velIBP (g : Fin 4 → ℝ) : M.VelIBP g where
  one _ := by
    simp [M, dv_apply, Fin.sum_univ_four]
    ring
  vel _ _ := by
    simp [M, dv_apply, Fin.sum_univ_four, vel]
    ring
  sq _ := by
    simp [M, dv_apply, Fin.sum_univ_four, vel, vsq]
    ring

/-- The fixed functions `1`, `v / 5`, `(v² - 25) / 24`. -/
def U : Fin 3 → Fin 4 → ℝ := ![![1, 1, 1, 1], ![-7 / 5, -1 / 5, 1 / 5, 7 / 5], ![1, -1, -1, 1]]

/-- The evolving function. -/
def W : Unit → Fin 4 → ℝ := fun _ => ![1 / 5, -7 / 5, 7 / 5, -1 / 5]

/-- An orthonormal family in `x`. -/
def X : Fin 3 ⊕ Unit → Fin 5 → ℝ :=
  Sum.elim ![![1 / 3, 2 / 3, 2 / 3, 0, 0], ![2 / 3, 1 / 3, -2 / 3, 0, 0],
    ![2 / 3, -2 / 3, 1 / 3, 0, 0]] fun _ => ![0, 0, 0, 1, 0]

/-- The coefficient matrix. -/
def S : Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℝ := Matrix.diagonal (Sum.elim ![3, 1, 1] fun _ => 1)

lemma fixedOrtho : M.FixedOrtho U := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [ipv, M, U, Fin.sum_univ_four] <;> norm_num

lemma conserves : M.Conserves U where
  one := ⟨![1, 0, 0], fun v => by fin_cases v <;> simp [U, Fin.sum_univ_three]⟩
  vel _ := ⟨![0, 5, 0], fun v => by
    fin_cases v <;> simp [U, M, vel, Fin.sum_univ_three] <;> norm_num⟩
  sq := ⟨![25, 0, 24], fun v => by
    fin_cases v <;> simp [U, M, vel, vsq, Fin.sum_univ_three] <;> norm_num⟩

lemma isFrame : M.IsFrame X (basis U W) := by
  refine ⟨fun i j => ?_, fun k l => ?_⟩
  · rcases i with a | p <;> rcases j with b | q
    · fin_cases a <;> fin_cases b <;> simp [ipx, M, X, Fin.sum_univ_five] <;> norm_num
    · fin_cases a <;> simp [ipx, M, X, Fin.sum_univ_five]
    · fin_cases b <;> simp [ipx, M, X, Fin.sum_univ_five]
    · simp [ipx, M, X, Fin.sum_univ_five]
  · rcases k with a | p <;> rcases l with b | q
    · fin_cases a <;> fin_cases b <;> simp [ipv, M, U, Fin.sum_univ_four] <;> norm_num
    · fin_cases a <;> simp [ipv, M, U, W, Fin.sum_univ_four] <;> norm_num
    · fin_cases b <;> simp [ipv, M, U, W, Fin.sum_univ_four] <;> norm_num
    · simp [ipv, M, W, Fin.sum_univ_four]
      norm_num

lemma isUnit_S : IsUnit S.det := by
  simp [S, Matrix.det_diagonal, Fintype.prod_sum_type, Fin.prod_univ_three]

lemma perp (p : Unit) (a : Fin 3) : M.ipv (W p) (U a) = 0 := by
  simpa using isFrame.v (Sum.inr p) (Sum.inl a)

/-- The potential of `f`. -/
def φ : Fin 5 → ℝ := ![0, -4 / 5, -8 / 5, 8 / 5, 4 / 5]

/-- The electric field of `f`. -/
def E : Unit → Fin 5 → ℝ := fun _ => ![4 / 5, 4 / 5, -6 / 5, -6 / 5, 4 / 5]

/-- The distribution function of the instance. -/
def f : Fin 5 → Fin 4 → ℝ := M.lowRank X S (basis U W)

lemma colK_eq (j : Fin 3 ⊕ Unit) (x : Fin 5) :
    colK X S j x = X j x * Sum.elim ![3, 1, 1] (fun _ => 1) j := by
  simp [colK, S, Matrix.diagonal_apply]

lemma rho_f (x : Fin 5) : M.rho f x = 3 * X (Sum.inl 0) x := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℝ, c = ![1, 0, 0] := ⟨_, rfl⟩
  have h1 : ∀ v, (fun _ => (1 : ℝ)) v = ∑ a, c a * U a v := fun v => by
    fin_cases v <;> simp [U, hc, Fin.sum_univ_three]
  have e : M.rho f x = ∑ a, c a * M.mom (U a) f x := mom_inSpan h1 f x
  have e2 : ∀ a, M.mom (U a) f x = colK X S (Sum.inl a) x :=
    fun a => mom_fixed fixedOrtho perp X S a x
  rw [e]
  simp only [e2, colK_eq, hc, Fin.sum_univ_three]
  simp
  ring

lemma cur_f (α : Unit) (x : Fin 5) : M.cur f α x = 5 * X (Sum.inl 1) x := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℝ, c = ![0, 5, 0] := ⟨_, rfl⟩
  have h1 : ∀ v, M.vel α v = ∑ a, c a * U a v := fun v => by
    fin_cases v <;> simp [U, M, vel, hc, Fin.sum_univ_three] <;> norm_num
  have e : M.cur f α x = ∑ a, c a * M.mom (U a) f x := mom_inSpan h1 f x
  have e2 : ∀ a, M.mom (U a) f x = colK X S (Sum.inl a) x :=
    fun a => mom_fixed fixedOrtho perp X S a x
  rw [e]
  simp only [e2, colK_eq, hc, Fin.sum_univ_three]
  simp

lemma isField : M.IsField (M.rho f) E φ := by
  have h : (-1 : Fin 5) = 4 := rfl
  refine ⟨fun α => ?_, fun x => ?_⟩
  · ext x
    fin_cases x <;> simp [E, φ, M, dx, h] <;> norm_num
  · rw [rho_f]
    fin_cases x <;> simp [E, M, dx, X, h] <;> norm_num

lemma hker (u : Fin 5 → ℝ) (h : ∀ α, M.dx α u = 0) : ∃ c : ℝ, u = fun _ => c := by
  have h1 : ∀ i, u (i + 1) = u (i - 1) := by
    intro i
    have := congrFun (h ()) i
    simp only [M, dx, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    linarith
  have e0 := h1 0
  have e1 := h1 1
  have e2 := h1 2
  have e3 := h1 3
  have e4 := h1 4
  simp only [zero_add, zero_sub] at e0
  have a1 : (1 : Fin 5) + 1 = 2 := rfl
  have a2 : (2 : Fin 5) + 1 = 3 := rfl
  have a3 : (3 : Fin 5) + 1 = 4 := rfl
  have a4 : (4 : Fin 5) + 1 = 0 := rfl
  have b0 : (-1 : Fin 5) = 4 := rfl
  have b1 : (1 : Fin 5) - 1 = 0 := rfl
  have b2 : (2 : Fin 5) - 1 = 1 := rfl
  have b3 : (3 : Fin 5) - 1 = 2 := rfl
  have b4 : (4 : Fin 5) - 1 = 3 := rfl
  rw [b0] at e0
  rw [a1, b1] at e1
  rw [a2, b2] at e2
  rw [a3, b3] at e3
  rw [a4, b4] at e4
  refine ⟨u 0, ?_⟩
  ext i
  fin_cases i
  · rfl
  · exact e0.trans (e3.trans e1)
  · exact e1
  · exact e4.symm
  · exact e3.trans e1

/-- **Non-vacuity of arXiv 2101.12571, Sec. 6.1, and the sign of the defect.**  On the phase space
`M`, with exact integration by parts (`velIBP`), three fixed functions with `1, v, v² ∈ span U`
(`fixedOrtho`, `conserves`) and one evolving function `W`, orthonormal factors (`isFrame`), an
invertible `S` (`isUnit_S`) and the field of `f` (`isField`): for all small `τ > 0` the scheme makes
a step, the new `f` has a field, and the total energy strictly increases. -/
theorem exists_energy_growth : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∃ X' S' W' E' φ',
    IsUnit (S' : Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℝ).det ∧
    M.IsEuler U τ (M.vlasov E f) X X' S S' W W' ∧
    M.IsField (M.rho (M.lowRank X' S' (basis U W'))) E' φ' ∧
    M.energy f E < M.energy (M.lowRank X' S' (basis U W')) E' := by
  have h1 := (exists_isEuler (M := M) U X W (M.vlasov E f) isUnit_S).filter_mono
    (nhdsWithin_le_nhds (s := Ioi 0))
  filter_upwards [h1, self_mem_nhdsWithin] with τ hτ hpos
  obtain ⟨X', S', W', hS', hstep⟩ := hτ
  have hb := (hstep.isBalanced hS' fixedOrtho perp).momStep fixedOrtho perp
  have hI : ∀ x, M.VelIBP (f x) := fun x => velIBP _
  have hmass := Model.MomStep.mass_eq hb conserves hI
  obtain ⟨E', φ', hF'⟩ := exists_isField (M := M) hker
    (ρ := M.rho (M.lowRank X' S' (basis U W'))) (by
      have e0 : ∀ g : Fin 5 → Fin 4 → ℝ, ∑ x, M.hx x * (1 - M.rho g x)
          = ∑ x, M.hx x - M.mass g := fun g => by
        simp only [mass, mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [e0, hmass, ← e0]
      simp only [rho_f]
      simp [Fin.sum_univ_five, M, X]
      norm_num)
  refine ⟨X', S', W', E', φ', hS', hstep, hF', ?_⟩
  have hd := Model.MomStep.energy_defect hb conserves hI isField hF'
  have hne := Model.MomStep.energy_eq_iff hb conserves hI isField hF' hpos.ne'
  have hnz : M.energy (M.lowRank X' S' (basis U W')) E' ≠ M.energy f E := by
    intro h
    have h0 := (hne.1 h) 0
    have hj : ∀ α, M.cur f α = fun x => 5 * X (Sum.inl 1) x := fun α => funext (cur_f α)
    have h4 : (-1 : Fin 5) = 4 := rfl
    simp only [hj] at h0
    simp [M, dx, X, h4] at h0
  have hnn : 0 ≤ (1 / 2) * ∑ x, M.hx x * ∑ α, (E' α x - E α x) ^ 2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => mul_nonneg (M.hx_pos x).le
      (Finset.sum_nonneg fun α _ => sq_nonneg _))
  exact lt_of_le_of_ne (by linarith) hnz.symm

/-- The spatial factor of a rank-one classical state. -/
def Xc : Unit → Fin 5 → ℝ := fun _ => ![1 / 3, 2 / 3, 2 / 3, 0, 0]

/-- The velocity factor of a rank-one classical state; it is orthonormal in the unweighted `L²`. -/
def Vc : Unit → Fin 4 → ℝ := fun _ => ![1, 0, 0, 0]

/-- The coefficient of a rank-one classical state. -/
def Sc : Matrix Unit Unit ℝ := Matrix.of fun _ _ => 3

/-- A rank-one classical state with the same density as `f`. -/
def fc : Fin 5 → Fin 4 → ℝ := fun x v => ∑ i, ∑ j, Xc i x * Sc i j * Vc j v

lemma isField_fc : M.IsField (M.rho fc) E φ := by
  have h : (-1 : Fin 5) = 4 := rfl
  refine ⟨isField.grad, fun x => ?_⟩
  fin_cases x <;>
    simp [E, M, dx, Xc, Vc, Sc, fc, rho, mom, h, Fin.sum_univ_four] <;> norm_num

lemma vlasov_fc : M.vlasov E fc = fun x v => (![![1531 / 210, -14 / 15, 7 / 10, -2 / 35],
    ![857 / 210, -28 / 15, 7 / 5, -4 / 35], ![-551 / 70, 14 / 5, -21 / 10, 6 / 35],
    ![-7, 0, 0, 0], ![7 / 2, 0, 0, 0]] : Fin 5 → Fin 4 → ℝ) x v := by
  have h : (-1 : Fin 5) = 4 := rfl
  ext x v
  fin_cases x <;> fin_cases v <;>
    simp [vlasov, M, dx, fc, Xc, Sc, Vc, E, h, dv_apply, vel] <;> norm_num

/-- **Sec. 4** (arXiv 2101.12571): *the classical scheme does not conserve mass*.  At a rank-one
state, orthonormal in the unweighted `L²`, with `E` the field of the state and exact integration by
parts in `v` (`velIBP`), so that `(1, D[f])_v = -∇ ⋅ j` integrates to zero, the equations of motion
(4), (5), (6) are solvable and the mass changes at rate `61/378`. -/
theorem classic_not_conservative : M.IsField (M.rho fc) E φ ∧ M.ipx (Xc ()) (Xc ()) = 1 ∧
    ∑ v, M.hv v * (Vc () v * Vc () v) = 1 ∧ IsUnit Sc.det ∧
    ∃ Xd Sd Vd, M.IsClassical Xc Xd Sc Sd Vc Vd (M.vlasov E fc) ∧
      ∑ x, M.hx x * ∑ v, M.hv v * classicD Xc Xd Sc Sd Vc Vd x v = 61 / 378 := by
  refine ⟨isField_fc, ?_, ?_, ?_, ?_⟩
  · simp [ipx, M, Xc, Fin.sum_univ_five]
    norm_num
  · simp [M, Vc, Fin.sum_univ_four]
  · simp [Sc, Matrix.det_unique]
  obtain ⟨G, hG⟩ : ∃ G, G = M.vlasov E fc := ⟨_, rfl⟩
  obtain ⟨sd, hsd⟩ : ∃ sd, sd = M.pair (Xc ()) (Vc ()) G := ⟨_, rfl⟩
  obtain ⟨Xd, hXd⟩ : ∃ Xd : Unit → Fin 5 → ℝ,
    Xd = fun _ x => (M.mom (Vc ()) G x - Xc () x * sd) / 3 := ⟨_, rfl⟩
  obtain ⟨Vd, hVd⟩ : ∃ Vd : Unit → Fin 4 → ℝ,
    Vd = fun _ v => (M.momX (Xc ()) G v - sd * Vc () v) / 3 := ⟨_, rfl⟩
  have hc : M.IsClassical Xc Xd Sc (Matrix.of fun _ _ => sd) Vc Vd G := by
    refine ⟨fun j x => ?_, fun i j => ?_, fun i v => ?_⟩
    · simp only [Fintype.sum_unique, Sc, Matrix.of_apply, PUnit.default_eq_unit, hXd]
      ring
    · simp only [Matrix.of_apply, hsd]
    · simp only [Fintype.sum_unique, Sc, Matrix.of_apply, PUnit.default_eq_unit, hVd]
      ring
  refine ⟨Xd, Matrix.of fun _ _ => sd, Vd, hG ▸ hc, ?_⟩
  have e := eq7 hc
  have e2 : ∑ x, M.hx x * M.rhs7 Xc Vc G x = 61 / 378 := by
    rw [hG, vlasov_fc]
    simp [rhs7, mom, pair, M, Xc, Vc, Fin.sum_univ_five, Fin.sum_univ_four]
    norm_num
  rw [← e2]
  exact Finset.sum_congr rfl fun x _ => by rw [e x]

/-- The discrete phase space of a homogeneous plasma: four nodes in `x`, no transport. -/
def M₀ : Model (Fin 4) (Fin 4) Unit where
  hx _ := 1 / 4
  hv _ := 1
  f0 _ := 1 / 4
  vel _ := vel
  dx _ := 0
  dv _ := dv
  hx_pos _ := by norm_num
  hv_pos _ := one_pos
  f0_pos _ := by norm_num
  dx_skew _ _ _ := by simp
  dx_const _ := rfl
  dx_comm _ _ _ := rfl

/-- The Walsh functions, orthonormal in `⟨·, ·⟩_x` of `M₀`. -/
def X₀ : Fin 3 ⊕ Unit → Fin 4 → ℝ :=
  Sum.elim ![![1, 1, 1, 1], ![1, 1, -1, -1], ![1, -1, 1, -1]] fun _ => ![1, -1, -1, 1]

lemma isFrame₀ : M₀.IsFrame X₀ (basis U W) := by
  refine ⟨fun i j => ?_, fun k l => ?_⟩
  · rcases i with a | p <;> rcases j with b | q
    · fin_cases a <;> fin_cases b <;> simp [ipx, M₀, X₀, Fin.sum_univ_four] <;> norm_num
    · fin_cases a <;> simp [ipx, M₀, X₀, Fin.sum_univ_four]
    · fin_cases b <;> simp [ipx, M₀, X₀, Fin.sum_univ_four]
    · simp [ipx, M₀, X₀, Fin.sum_univ_four]
      norm_num
  · have h := isFrame.v k l
    simpa [ipv, M₀, M] using h

/-- **Non-vacuity of arXiv 2101.12571, Sec. 5.**  A stationary solution of the equations of motion
on a homogeneous phase space, with three fixed and one evolving function and an orthonormal frame
`isFrame₀`.  (Solutions with transport are not constructed here.) -/
theorem isSolution₀ : M₀.IsSolution U 0 1 (fun _ => X₀) 0 (fun _ => 1) 0 (fun _ => W) 0 0 0 := by
  have hG : ∀ t, M₀.rhs U (fun _ => X₀) (fun _ => 1) (fun _ => W) 0 t = 0 := by
    intro t
    ext x v
    simp [rhs, vlasov, M₀]
  refine ⟨fun t _ i x => hasDerivWithinAt_const _ _ _, fun t _ i j => hasDerivWithinAt_const _ _ _,
    fun t _ p v => hasDerivWithinAt_const _ _ _, fun t _ α x => hasDerivWithinAt_const _ _ _,
    fun t _ k x => ?_, fun t _ q v => ?_, fun t _ k l => ?_⟩ <;>
  simp [hG, mom, momX, pair]

end Ex

/-! ### The continuum: Sec. 5 on `ℝ × ℝ` -/

namespace Continuum

open MeasureTheory
open scoped Real

section Moments

variable {κ : Type*} [Fintype κ] {K K' g g' : κ → ℝ → ℝ} {E : ℝ → ℝ}

/-- `f = ∑_j K_j(x) g_j(v)`. -/
def phase (K g : κ → ℝ → ℝ) (x v : ℝ) : ℝ := ∑ j, K j x * g j v

/-- `D[f] = -v ∂ₓ f + E ∂ᵥ f`, with true derivatives. -/
def vlasov (E : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (x v : ℝ) : ℝ :=
  -(v * deriv (fun y => f y v) x) + E x * deriv (f x) v

/-- The velocity moment `∫ vᵏ f dv`. -/
def mom (k : ℕ) (f : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := ∫ v, v ^ k * f x v

/-- Differentiable in `x` and `v`, with the moments of the paper. -/
structure IsRegular (K K' g g' : κ → ℝ → ℝ) : Prop where
  hK : ∀ j y, HasDerivAt (K j) (K' j y) y
  hg : ∀ j v, HasDerivAt (g j) (g' j v) v
  int : ∀ j k, k ≤ 3 → Integrable (fun v => v ^ k * g j v)
  int' : ∀ j k, k ≤ 2 → Integrable (fun v => v ^ k * g' j v)

lemma vlasov_phase (h : IsRegular K K' g g') (x v : ℝ) :
    vlasov E (phase K g) x v = -(v * ∑ j, K' j x * g j v) + E x * ∑ j, K j x * g' j v := by
  have h1 : HasDerivAt (fun y => phase K g y v) (∑ j, K' j x * g j v) x :=
    HasDerivAt.fun_sum fun j _ => (h.hK j x).mul_const _
  have h2 : HasDerivAt (phase K g x) (∑ j, K j x * g' j v) v :=
    HasDerivAt.fun_sum fun j _ => (h.hg j v).const_mul _
  rw [vlasov, h1.deriv, h2.deriv]

lemma mom_phase (h : IsRegular K K' g g') {k : ℕ} (hk : k ≤ 3) (x : ℝ) :
    mom k (phase K g) x = ∑ j, K j x * ∫ v, v ^ k * g j v := by
  have e : ∀ v, v ^ k * phase K g x v = ∑ j, K j x * (v ^ k * g j v) := by
    intro v
    rw [phase, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [mom, e]
  rw [integral_finsetSum _ fun j _ => (h.int j k hk).const_mul _]
  simp only [integral_const_mul]

/-- Integration by parts in `v`: the velocity flux has no moment. -/
lemma integral_pow_mul_deriv (h : IsRegular K K' g g') (j : κ) {k : ℕ} (hk : k ≤ 2) :
    ∫ v, v ^ k * g' j v = -(k * ∫ v, v ^ (k - 1) * g j v) := by
  have h1 : Integrable (fun v => (k : ℝ) * v ^ (k - 1) * g j v) := by
    have := (h.int j (k - 1) (by omega)).const_mul (k : ℝ)
    simpa [mul_assoc] using this
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun v : ℝ => v ^ k)
    (u' := fun v => (k : ℝ) * v ^ (k - 1)) (v := g j) (v' := g' j)
    (fun v _ => hasDerivAt_pow k v) (fun v _ => h.hg j v) (h.int' j k hk) h1
    (h.int j k (by omega))
  rw [this, ← integral_const_mul]
  simp only [mul_assoc]

lemma integrable_vlasov (h : IsRegular K K' g g') {k : ℕ} (hk : k ≤ 2) (x : ℝ) :
    Integrable (fun v => v ^ k * vlasov E (phase K g) x v) := by
  have e : ∀ v, v ^ k * vlasov E (phase K g) x v
      = -∑ j, K' j x * (v ^ (k + 1) * g j v) + E x * ∑ j, K j x * (v ^ k * g' j v) := by
    intro v
    rw [vlasov_phase h, mul_add, mul_neg, mul_left_comm (v ^ k) (E x)]
    simp only [Finset.mul_sum]
    exact congrArg₂ (· + ·) (congrArg Neg.neg (Finset.sum_congr rfl fun j _ => by ring))
      (Finset.sum_congr rfl fun j _ => by ring)
  simp only [e]
  refine ((integrable_finsetSum _ fun j _ => (h.int j (k + 1) (by omega)).const_mul _).neg).add
    ((integrable_finsetSum _ fun j _ => (h.int' j k hk).const_mul _).const_mul _)

lemma hasDerivAt_mom (h : IsRegular K K' g g') {k : ℕ} (hk : k ≤ 3) (x : ℝ) :
    HasDerivAt (mom k (phase K g)) (∑ j, K' j x * ∫ v, v ^ k * g j v) x := by
  rw [show mom k (phase K g) = fun y => ∑ j, K j y * ∫ v, v ^ k * g j v from
    funext fun y => mom_phase h hk y]
  exact HasDerivAt.fun_sum fun j _ => (h.hK j x).mul_const _

/-- **Sec. 5** (arXiv 2101.12571), on `ℝ × ℝ`, the step that the paper leaves to the reader: for
`k ≤ 2`, `∫ vᵏ D[f] dv = -∂ₓ ∫ vᵏ⁺¹ f dv - k E ∫ vᵏ⁻¹ f dv`, with true derivatives and integrals. -/
theorem mom_vlasov (h : IsRegular K K' g g') {k : ℕ} (hk : k ≤ 2) (x : ℝ) :
    mom k (vlasov E (phase K g)) x
      = -deriv (mom (k + 1) (phase K g)) x - k * E x * mom (k - 1) (phase K g) x := by
  have e : ∀ v, v ^ k * vlasov E (phase K g) x v
      = -∑ j, K' j x * (v ^ (k + 1) * g j v) + E x * ∑ j, K j x * (v ^ k * g' j v) := by
    intro v
    rw [vlasov_phase h, mul_add, mul_neg, mul_left_comm (v ^ k) (E x)]
    simp only [Finset.mul_sum]
    exact congrArg₂ (· + ·) (congrArg Neg.neg (Finset.sum_congr rfl fun j _ => by ring))
      (Finset.sum_congr rfl fun j _ => by ring)
  have i1 : Integrable (fun v => -∑ j, K' j x * (v ^ (k + 1) * g j v)) :=
    (integrable_finsetSum _ fun j _ => (h.int j (k + 1) (by omega)).const_mul _).neg
  have i2 : Integrable (fun v => E x * ∑ j, K j x * (v ^ k * g' j v)) :=
    (integrable_finsetSum _ fun j _ => (h.int' j k hk).const_mul _).const_mul _
  rw [(hasDerivAt_mom h (by omega) x).deriv, mom_phase h (by omega) x]
  simp only [mom, e]
  rw [integral_add i1 i2, integral_neg, integral_const_mul,
    integral_finsetSum _ fun j _ => (h.int j (k + 1) (by omega)).const_mul _,
    integral_finsetSum _ fun j _ => (h.int' j k hk).const_mul _]
  simp only [integral_const_mul, integral_pow_mul_deriv h _ hk, mul_neg, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [sub_eq_add_neg]
  congr 1
  exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ => by ring)

end Moments

section Time

variable {ι κ P : Type*} [Fintype ι] [Fintype κ] [Fintype P] [DecidableEq P]

/-- The fixed functions: polynomials of degree at most two. -/
def polyU (L : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3) (v : ℝ) : ℝ :=
  ∑ k : Fin 3, L a k * v ^ (k : ℕ)

/-- The ansatz (8), `f = f_{0v} ∑_ij X_i S_ij V_j`, on `ℝ × ℝ`. -/
def ansatz (f0 : ℝ → ℝ) (X : ι → ℝ → ℝ) (S : Matrix ι κ ℝ) (V : κ → ℝ → ℝ) (x v : ℝ) : ℝ :=
  f0 v * ∑ i, ∑ j, X i x * S i j * V j v

lemma ansatz_eq (f0 : ℝ → ℝ) (X : ι → ℝ → ℝ) (S : Matrix ι κ ℝ) (V : κ → ℝ → ℝ) :
    ansatz f0 X S V = phase (Model.colK X S) (fun j v => f0 v * V j v) := by
  ext x v
  simp only [ansatz, phase, Model.colK, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma integral_polyU (L : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ → ℝ}
    (hh : ∀ k, k ≤ 2 → Integrable fun v => v ^ k * h v) (a : Fin 3) :
    ∫ v, polyU L a v * h v = ∑ k : Fin 3, L a k * ∫ v, v ^ (k : ℕ) * h v := by
  have e : ∀ v, polyU L a v * h v = ∑ k : Fin 3, L a k * (v ^ (k : ℕ) * h v) := by
    intro v
    rw [polyU, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e]
  rw [integral_finsetSum (f := fun (k : Fin 3) v => L a k * (v ^ (k : ℕ) * h v)) _
    fun k _ => (hh k (Nat.le_of_lt_succ k.2)).const_mul _]
  simp only [integral_const_mul]

lemma integrable_polyU (L : Matrix (Fin 3) (Fin 3) ℝ) {h : ℝ → ℝ}
    (hh : ∀ k, k ≤ 2 → Integrable fun v => v ^ k * h v) (a : Fin 3) :
    Integrable fun v => polyU L a v * h v := by
  have e : ∀ v, polyU L a v * h v = ∑ k : Fin 3, L a k * (v ^ (k : ℕ) * h v) := by
    intro v
    rw [polyU, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e]
  exact integrable_finsetSum _ fun k _ => (hh k (Nat.le_of_lt_succ k.2)).const_mul _

/-- A classical solution, on the open set `I` of times, of the part of the equations of motion that
Sec. 5 uses.  `L` is the matrix of the fixed functions in terms of `1, v, v²`; for instance
`U_1 ∝ 1`, `U_2 ∝ v`, `U_3 ∝ v² - 1`.  Eq. (10) is needed only for the fixed columns, and (11), (12)
only through the constraint `orth`, which they imply in the discrete setting (`IsSolution.isFrame`)
and which is part of the manifold `ℳ` here. -/
structure IsSolution (f0 : ℝ → ℝ) (L : Matrix (Fin 3) (Fin 3) ℝ) (I : Set ℝ)
    (X X' Xx : ℝ → ι → ℝ → ℝ) (S S' : ℝ → Matrix ι (Fin 3 ⊕ P) ℝ) (W : ℝ → P → ℝ → ℝ)
    (g' : ℝ → Fin 3 ⊕ P → ℝ → ℝ) (E : ℝ → ℝ → ℝ) : Prop where
  reg : ∀ t ∈ I, IsRegular (Model.colK (X t) (S t)) (fun j y => ∑ i, Xx t i y * S t i j)
    (fun j v => f0 v * Sum.elim (polyU L) (W t) j v) (g' t)
  orth : ∀ t ∈ I, ∀ j a, ∫ v, polyU L a v * (f0 v * Sum.elim (polyU L) (W t) j v)
    = if j = Sum.inl a then 1 else 0
  hXt : ∀ t ∈ I, ∀ i x, HasDerivAt (fun s => X s i x) (X' t i x) t
  hSt : ∀ t ∈ I, ∀ i j, HasDerivAt (fun s => S s i j) (S' t i j) t
  eq10 : ∀ t ∈ I, ∀ a x, ∑ i, X' t i x * S t i (Sum.inl a)
    = (∫ v, polyU L a v * vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t))) x v)
      - ∑ i, X t i x * S' t i (Sum.inl a)

variable {f0 : ℝ → ℝ} {L : Matrix (Fin 3) (Fin 3) ℝ} {I : Set ℝ} {X X' Xx : ℝ → ι → ℝ → ℝ}
  {S S' : ℝ → Matrix ι (Fin 3 ⊕ P) ℝ} {W : ℝ → P → ℝ → ℝ} {g' : ℝ → Fin 3 ⊕ P → ℝ → ℝ}
  {E : ℝ → ℝ → ℝ}

/-- `(U_a, f)_v = K_a`. -/
lemma IsSolution.mom_eq (h : IsSolution f0 L I X X' Xx S S' W g' E) {t : ℝ} (ht : t ∈ I) (a : Fin 3)
    (x : ℝ) : ∑ k : Fin 3, L a k * mom k (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t))) x
      = Model.colK (X t) (S t) (Sum.inl a) x := by
  have hr := h.reg t ht
  have hint : ∀ j, ∀ k, k ≤ 2 → Integrable fun v =>
      v ^ k * (f0 v * Sum.elim (polyU L) (W t) j v) := fun j k hk => hr.int j k (by omega)
  have e1 : ∀ v, polyU L a v * ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) x v
      = ∑ j, Model.colK (X t) (S t) j x
        * (polyU L a v * (f0 v * Sum.elim (polyU L) (W t) j v)) := by
    intro v
    rw [ansatz_eq, phase, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∫ v, polyU L a v * ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) x v
      = Model.colK (X t) (S t) (Sum.inl a) x := by
    simp only [e1]
    rw [integral_finsetSum _ fun j _ => (integrable_polyU L (hint j) a).const_mul _]
    simp only [integral_const_mul, h.orth t ht, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hint2 : ∀ k, k ≤ 2 → Integrable fun v =>
      v ^ k * ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) x v := by
    intro k hk
    have e : ∀ v, v ^ k * ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) x v
        = ∑ j, Model.colK (X t) (S t) j x * (v ^ k * (f0 v * Sum.elim (polyU L) (W t) j v)) := by
      intro v
      rw [ansatz_eq, phase, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e]
    exact integrable_finsetSum _ fun j _ => (hint j k hk).const_mul _
  rw [← e2, integral_polyU L hint2 a]
  rfl

/-- **Sec. 5, the core** (arXiv 2101.12571), on `ℝ × ℝ`: `∂ₜ ∫ vᵏ f dv = ∫ vᵏ D[f] dv`, for
`k ≤ 2`. -/
theorem IsSolution.hasDeriv_mom (h : IsSolution f0 L I X X' Xx S S' W g' E) (hL : IsUnit L.det)
    (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) (k : Fin 3) (x : ℝ) :
    HasDerivAt (fun s => mom k (ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s))) x)
      (mom k (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x) t := by
  have hinv : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hL
  have hK : ∀ a, HasDerivAt (fun s => Model.colK (X s) (S s) (Sum.inl a) x)
      (∑ m : Fin 3, L a m
        * mom m (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x) t := by
    intro a
    have h1 : HasDerivAt (fun s => ∑ i, X s i x * S s i (Sum.inl a))
        (∑ i, (X' t i x * S t i (Sum.inl a) + X t i x * S' t i (Sum.inl a))) t :=
      HasDerivAt.fun_sum fun i _ => (h.hXt t ht i x).mul (h.hSt t ht i _)
    have e : ∑ i, (X' t i x * S t i (Sum.inl a) + X t i x * S' t i (Sum.inl a))
        = ∑ m : Fin 3, L a m
          * mom m (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x := by
      have e0 : ∑ i, (X' t i x * S t i (Sum.inl a) + X t i x * S' t i (Sum.inl a))
          = ∫ v, polyU L a v * vlasov (E t)
            (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t))) x v := by
        have aux : ∀ A B C : ℝ, A = B - C → A + C = B := fun _ _ _ h => by linarith
        rw [Finset.sum_add_distrib]
        exact aux _ _ _ (h.eq10 t ht a x)
      rw [e0, ansatz_eq]
      exact integral_polyU L (fun m hm => integrable_vlasov (h.reg t ht) hm x) a
    rw [e] at h1
    exact h1
  have e : ∀ s ∈ I, mom k (ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s))) x
      = ∑ a, L⁻¹ k a * Model.colK (X s) (S s) (Sum.inl a) x := by
    intro s hs
    simp only [← h.mom_eq hs]
    have : ∑ a, L⁻¹ k a * ∑ m : Fin 3, L a m
          * mom m (ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s))) x
        = ∑ m : Fin 3, (L⁻¹ * L) k m
          * mom m (ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s))) x := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun a _ => by ring
    rw [this, hinv]
    simp [Matrix.one_apply]
  have h2 : HasDerivAt (fun s => ∑ a, L⁻¹ k a * Model.colK (X s) (S s) (Sum.inl a) x)
      (∑ a, L⁻¹ k a * ∑ m : Fin 3, L a m
        * mom m (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x) t :=
    HasDerivAt.fun_sum fun a _ => (hK a).const_mul _
  have e2 : ∑ a, L⁻¹ k a * ∑ m : Fin 3, L a m
        * mom m (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x
      = mom k (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x := by
    have : ∑ a, L⁻¹ k a * ∑ m : Fin 3, L a m
          * mom m (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x
        = ∑ m : Fin 3, (L⁻¹ * L) k m
          * mom m (vlasov (E t) (ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)))) x := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun a _ => by ring
    rw [this, hinv]
    simp [Matrix.one_apply]
  rw [e2] at h2
  exact h2.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hI.mem_nhds ht) e)

/-- **Sec. 5, the local continuity equation** (arXiv 2101.12571), on `ℝ × ℝ`, with true
derivatives and integrals: `∂ₜ ρ + ∂ₓ j = 0`. -/
theorem IsSolution.rho_law (h : IsSolution f0 L I X X' Xx S S' W g' E) (hL : IsUnit L.det)
    (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    HasDerivAt (fun s => ∫ v, ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s)) x v)
      (-deriv (fun y => ∫ v, v * ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) y v) x) t := by
  obtain ⟨F, hF⟩ : ∃ F, F = ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) := ⟨_, rfl⟩
  have h1 := h.hasDeriv_mom hL hI ht 0 x
  have e := mom_vlasov (E := E t) (h.reg t ht) (k := 0) (by norm_num) x
  rw [← ansatz_eq, ← hF] at e
  rw [← hF] at h1 ⊢
  have e1 : mom 1 F = fun y => ∫ v, v * F y v := by
    ext y
    simp [mom]
  simp only [Fin.val_zero, zero_add, Nat.cast_zero, zero_mul, sub_zero, e1] at h1 e
  rw [e] at h1
  simpa only [mom, pow_zero, one_mul] using h1

/-- **Sec. 5, the local momentum equation** (arXiv 2101.12571), on `ℝ × ℝ`, with true derivatives
and integrals: `∂ₜ j + ∂ₓ σ = -E ρ`. -/
theorem IsSolution.cur_law (h : IsSolution f0 L I X X' Xx S S' W g' E) (hL : IsUnit L.det)
    (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    HasDerivAt (fun s => ∫ v, v * ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s)) x v)
      (-deriv (fun y => ∫ v, v ^ 2 * ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) y v) x
        - E t x * ∫ v, ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) x v) t := by
  obtain ⟨F, hF⟩ : ∃ F, F = ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) := ⟨_, rfl⟩
  have h1 := h.hasDeriv_mom hL hI ht 1 x
  have e := mom_vlasov (E := E t) (h.reg t ht) (k := 1) (by norm_num) x
  rw [← ansatz_eq, ← hF] at e
  rw [← hF] at h1 ⊢
  have e1 : mom 2 F = fun y => ∫ v, v ^ 2 * F y v := rfl
  have e2 : mom 0 F x = ∫ v, F x v := by simp [mom]
  simp only [Fin.val_one, Nat.cast_one, one_mul, Nat.sub_self] at h1 e
  rw [show (1 + 1 : ℕ) = 2 from rfl, e1, e2] at e
  rw [e] at h1
  simpa only [mom, pow_one] using h1

/-- **Sec. 5, the local energy equation** (arXiv 2101.12571), on `ℝ × ℝ`, with true derivatives and
integrals: `∂ₜ e + ∂ₓ Q = E (∂ₜ E - j)`, for `e = ½ ∫ v² f dv + ½ E²`, `Q = ½ ∫ v³ f dv`. -/
theorem IsSolution.dens_law (h : IsSolution f0 L I X X' Xx S S' W g' E) (hL : IsUnit L.det)
    (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) (x : ℝ) {E' : ℝ} (hE : HasDerivAt (fun s => E s x) E' t) :
    HasDerivAt (fun s => (1 / 2) * (∫ v, v ^ 2 *
          ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s)) x v) + (1 / 2) * E s x ^ 2)
      (-deriv (fun y => (1 / 2) * ∫ v, v ^ 3 *
          ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) y v) x
        + E t x * (E' - ∫ v, v * ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) x v)) t := by
  obtain ⟨F, hF⟩ : ∃ F, F = ansatz f0 (X t) (S t) (Sum.elim (polyU L) (W t)) := ⟨_, rfl⟩
  have h1 := (h.hasDeriv_mom hL hI ht 2 x).const_mul (1 / 2 : ℝ)
  have h2 := (hE.pow 2).const_mul (1 / 2 : ℝ)
  have e := mom_vlasov (E := E t) (h.reg t ht) (k := 2) (by norm_num) x
  have hd := hasDerivAt_mom (h.reg t ht) (k := 3) le_rfl x
  rw [← ansatz_eq, ← hF] at e hd
  rw [← hF] at h1 ⊢
  have e1 : mom 3 F = fun y => ∫ v, v ^ 3 * F y v := rfl
  have e2 : mom 1 F x = ∫ v, v * F x v := by simp [mom]
  have e3 : deriv (fun y => (1 / 2 : ℝ) * ∫ v, v ^ 3 * F y v) x = (1 / 2) * deriv (mom 3 F) x := by
    have e8 : (fun y => (1 / 2 : ℝ) * ∫ v, v ^ 3 * F y v) = fun y => (1 / 2) * mom 3 F y := rfl
    rw [e8]
    exact deriv_const_mul _ hd.differentiableAt
  rw [e3]
  have e4 : mom 2 (vlasov (E t) F) x
      = -deriv (mom 3 F) x - ((2 : ℕ) : ℝ) * E t x * mom 1 F x := e
  have h1' : HasDerivAt
      (fun s => (1 / 2 : ℝ) * mom 2 (ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s))) x)
      ((1 / 2) * mom 2 (vlasov (E t) F) x) t := h1
  rw [e4] at h1'
  have h3 : HasDerivAt (fun s => (1 / 2) * (∫ v, v ^ 2 *
      ansatz f0 (X s) (S s) (Sum.elim (polyU L) (W s)) x v) + (1 / 2) * E s x ^ 2) _ t :=
    h1'.add h2
  refine h3.congr_deriv ?_
  rw [e2]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

end Time

/-- The Maxwellian `exp(-v²/2) / √(2π)`. -/
def gauss (v : ℝ) : ℝ := (√(2 * π))⁻¹ * Real.exp (-(1 / 2) * v ^ 2)

lemma integrable_pow_gauss (k : ℕ) : Integrable fun v : ℝ => v ^ k * gauss v := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := k)
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith)).const_mul (√(2 * π))⁻¹
  refine h.congr (ae_of_all _ fun v => ?_)
  simp only [gauss, Real.rpow_natCast]
  ring

lemma hasDerivAt_gauss (v : ℝ) : HasDerivAt gauss (-(v * gauss v)) v := by
  have h1 : HasDerivAt (fun v : ℝ => -(1 / 2) * v ^ 2) (-(1 / 2) * (2 * v)) v := by
    simpa using (hasDerivAt_pow 2 v).const_mul (-(1 / 2) : ℝ)
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  refine h2.congr_deriv ?_
  rw [gauss]
  ring

lemma integral_gauss : ∫ v, gauss v = 1 := by
  simp only [gauss]
  rw [integral_const_mul]
  rw [integral_gaussian (1 / 2)]
  have h : π / (1 / 2) = 2 * π := by ring
  rw [h]
  exact inv_mul_cancel₀ (by positivity)

/-- `∫ vᵏ⁺² M dv = (k + 1) ∫ vᵏ M dv`. -/
lemma gauss_rec (k : ℕ) :
    ∫ v, v ^ (k + 2) * gauss v = (k + 1) * ∫ v, v ^ k * gauss v := by
  have h1 : Integrable (fun v : ℝ => v ^ (k + 1) * -(v * gauss v)) := by
    have := (integrable_pow_gauss (k + 2)).neg
    refine this.congr (ae_of_all _ fun v => ?_)
    simp only [Pi.neg_apply]
    ring
  have h2 : Integrable (fun v : ℝ => ((k + 1 : ℕ) : ℝ) * v ^ k * gauss v) := by
    have := (integrable_pow_gauss k).const_mul ((k + 1 : ℕ) : ℝ)
    simpa [mul_assoc] using this
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun v : ℝ => v ^ (k + 1))
    (u' := fun v => ((k + 1 : ℕ) : ℝ) * v ^ k) (v := gauss) (v' := fun v => -(v * gauss v))
    (fun v _ => by simpa using hasDerivAt_pow (k + 1) v) (fun v _ => hasDerivAt_gauss v) h1 h2
    (integrable_pow_gauss (k + 1))
  have e1 : ∫ v, v ^ (k + 1) * -(v * gauss v) = -∫ v, v ^ (k + 2) * gauss v := by
    rw [← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun v => by ring)
  have e2 : ∫ v, ((k + 1 : ℕ) : ℝ) * v ^ k * gauss v = (k + 1) * ∫ v, v ^ k * gauss v := by
    rw [← integral_const_mul]
    simp [mul_assoc]
  rw [e1, e2] at this
  linarith

lemma integral_id_gauss : ∫ v, v * gauss v = 0 := by
  have h1 : Integrable (fun v : ℝ => (1 : ℝ) * -(v * gauss v)) := by
    have := (integrable_pow_gauss 1).neg
    refine this.congr (ae_of_all _ fun v => ?_)
    simp
  have h2 : Integrable (fun v : ℝ => (0 : ℝ) * gauss v) := by simp
  have h3 : Integrable (fun v : ℝ => (1 : ℝ) * gauss v) := by
    simpa using integrable_pow_gauss 0
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun _ : ℝ => (1 : ℝ))
    (u' := fun _ => 0) (v := gauss) (v' := fun v => -(v * gauss v))
    (fun v _ => hasDerivAt_const v 1) (fun v _ => hasDerivAt_gauss v) h1 h2 h3
  simp only [one_mul, zero_mul, integral_zero, neg_zero, integral_neg] at this
  linarith

lemma integral_sq_gauss : ∫ v, v ^ 2 * gauss v = 1 := by
  have := gauss_rec 0
  have h0 : (∫ v, v ^ 0 * gauss v) = 1 := by simpa using integral_gauss
  rw [h0] at this
  simpa using this

lemma integral_cube_gauss : ∫ v, v ^ 3 * gauss v = 0 := by
  have := gauss_rec 1
  have h1 : (∫ v, v ^ 1 * gauss v) = 0 := by simpa using integral_id_gauss
  rw [h1] at this
  simpa using this

lemma integral_four_gauss : ∫ v, v ^ 4 * gauss v = 3 := by
  have := gauss_rec 2
  rw [integral_sq_gauss] at this
  norm_num at this
  exact this

/-- The matrix of the fixed functions `U_1 = 1`, `U_2 = v`, `U_3 = (v² - 1) / √2` of the paper, for
the Maxwellian weight. -/
def maxL : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; -(√2)⁻¹, 0, (√2)⁻¹]

lemma isUnit_maxL : IsUnit maxL.det := by
  rw [isUnit_iff_ne_zero, maxL, Matrix.det_fin_three]
  simp

lemma pow_mul_gauss_polyU (L : Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) (b : Fin 3) (v : ℝ) :
    v ^ k * (gauss v * polyU L b v) = ∑ m : Fin 3, L b m * (v ^ (k + (m : ℕ)) * gauss v) := by
  rw [polyU, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [pow_add]
    ring

lemma integrable_gauss_polyU (L : Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) (b : Fin 3) :
    Integrable fun v => v ^ k * (gauss v * polyU L b v) := by
  simp only [pow_mul_gauss_polyU]
  exact integrable_finsetSum _ fun m _ => (integrable_pow_gauss _).const_mul _

lemma integral_gauss_polyU (L : Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) (b : Fin 3) :
    ∫ v, v ^ k * (gauss v * polyU L b v)
      = ∑ m : Fin 3, L b m * ∫ v, v ^ (k + (m : ℕ)) * gauss v := by
  simp only [pow_mul_gauss_polyU]
  rw [integral_finsetSum (f := fun (m : Fin 3) v => L b m * (v ^ (k + (m : ℕ)) * gauss v)) _
    fun m _ => (integrable_pow_gauss _).const_mul _]
  simp only [integral_const_mul]

/-- `U_1 = 1`, `U_2 = v`, `U_3 = (v² - 1) / √2` are orthonormal for the Maxwellian weight. -/
lemma orth_max (a b : Fin 3) :
    ∫ v, polyU maxL a v * (gauss v * polyU maxL b v) = if a = b then 1 else 0 := by
  have h2 : (√2 : ℝ)⁻¹ * (√2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [integral_polyU maxL (fun k _ => integrable_gauss_polyU maxL k b) a]
  simp only [integral_gauss_polyU, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;>
    simp [maxL, integral_gauss, integral_id_gauss, integral_sq_gauss, integral_cube_gauss,
      integral_four_gauss]
  linarith

lemma hasDerivAt_polyU (L : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3) (v : ℝ) :
    HasDerivAt (polyU L a) (L a 1 + 2 * L a 2 * v) v := by
  have e : polyU L a = fun v => L a 0 + L a 1 * v + L a 2 * v ^ 2 := by
    ext w
    simp [polyU, Fin.sum_univ_three]
  rw [e]
  have h := ((hasDerivAt_const v (L a 0)).add ((hasDerivAt_id' v).const_mul (L a 1))).add
    ((hasDerivAt_pow 2 v).const_mul (L a 2))
  refine h.congr_deriv ?_
  simp
  ring

/-- The velocity derivative of `M U_a`. -/
def maxG (a : Fin 3) (v : ℝ) : ℝ :=
  -(v * gauss v) * polyU maxL a v + gauss v * (maxL a 1 + 2 * maxL a 2 * v)

/-- **Non-vacuity of arXiv 2101.12571, Sec. 5, in the continuum.**  The Maxwellian `f = M`, with
`E = 0`, is a solution in the sense of `IsSolution`, for the weight `f_{0v} = M` and the fixed
functions of the paper. -/
theorem maxwellian_isSolution : IsSolution (ι := Unit) (P := Empty) gauss maxL univ (fun _ _ _ => 1)
    0 0 (fun _ => Matrix.of fun _ j => if j = Sum.inl 0 then 1 else 0) 0 (fun _ p => p.elim)
    (fun _ j v => Sum.elim (fun a => maxG a v) (fun p => p.elim) j) 0 := by
  refine ⟨fun t _ => ⟨fun j y => ?_, fun j v => ?_, fun j k hk => ?_, fun j k hk => ?_⟩,
    fun t _ j a => ?_, fun t _ i x => ?_, fun t _ i j => ?_, fun t _ a x => ?_⟩
  · simp only [Fin.isValue, Finset.univ_unique, PUnit.default_eq_unit, Pi.zero_apply,
      Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_self, sum_const_zero]
    exact hasDerivAt_const y _
  · rcases j with a | p
    · exact ((hasDerivAt_gauss v).mul (hasDerivAt_polyU maxL a v)).congr_deriv rfl
    · exact p.elim
  · rcases j with a | p
    · exact integrable_gauss_polyU maxL k a
    · exact p.elim
  · rcases j with a | p
    · have e : ∀ v, v ^ k * maxG a v = -(v ^ (k + 1) * (gauss v * polyU maxL a v))
          + maxL a 1 * (v ^ k * gauss v) + 2 * maxL a 2 * (v ^ (k + 1) * gauss v) := fun v => by
        rw [maxG, pow_succ]
        ring
      simp only [Sum.elim_inl, e]
      exact (((integrable_gauss_polyU maxL (k + 1) a).neg).add
        ((integrable_pow_gauss k).const_mul _)).add ((integrable_pow_gauss (k + 1)).const_mul _)
    · exact p.elim
  · rcases j with b | p
    · simp only [Sum.elim_inl, orth_max a b, Sum.inl.injEq, eq_comm]
    · exact p.elim
  · exact hasDerivAt_const t _
  · exact hasDerivAt_const t _
  · have e : ∀ v, vlasov (0 : ℝ → ℝ) (ansatz (ι := Unit) (κ := Fin 3 ⊕ Empty) gauss
        (fun _ _ => 1) (Matrix.of fun _ j => if j = Sum.inl 0 then 1 else 0)
        (Sum.elim (polyU maxL) fun p : Empty => p.elim)) x v = 0 := by
      intro v
      simp [vlasov, ansatz]
    simp [e]

end Continuum

section Quadratic

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- **Sec. 6.1, abstract form of eq. (17)** (arXiv 2101.12571).  For a quadratic functional
`I(Y) = ⟪c, Y⟫ + ½ ‖L Y‖²` on an inner product space and any step `Y₀ ↦ Y₁`, in particular explicit
Euler `Y₁ = Y₀ + τ Π F(Y₀)`, `I(Y₁) - I(Y₀) = ⟪∇I(Y₀), Y₁ - Y₀⟫ + ½ ‖L (Y₁ - Y₀)‖²`. -/
theorem quadratic_step (c : H) (L : H →L[ℝ] K) (Y₀ Y₁ : H) :
    (⟪c, Y₁⟫ + ‖L Y₁‖ ^ 2 / 2) - (⟪c, Y₀⟫ + ‖L Y₀‖ ^ 2 / 2)
      = ⟪c + ContinuousLinearMap.adjoint L (L Y₀), Y₁ - Y₀⟫ + ‖L (Y₁ - Y₀)‖ ^ 2 / 2 := by
  have e : L Y₁ = L Y₀ + L (Y₁ - Y₀) := by
    rw [← map_add]
    congr 1
    abel
  rw [e, norm_add_sq_real, inner_add_left, ContinuousLinearMap.adjoint_inner_left, inner_sub_right]
  ring

/-- **Sec. 6.1, abstract form of the energy defect** (arXiv 2101.12571).  If the step is orthogonal
to `∇I(Y₀)`, only the nonnegative term of `quadratic_step` remains.  This is the defect of explicit
Euler; for the midpoint rule, which conserves quadratic invariants, see
`implicitMidpoint_quadratic_eq` in `OpenProblems/Conservation/Part1d.lean`. -/
theorem quadratic_step_defect (c : H) (L : H →L[ℝ] K) {Y₀ Y₁ : H}
    (h : ⟪c + ContinuousLinearMap.adjoint L (L Y₀), Y₁ - Y₀⟫ = 0) :
    (⟪c, Y₁⟫ + ‖L Y₁‖ ^ 2 / 2) - (⟪c, Y₀⟫ + ‖L Y₀‖ ^ 2 / 2) = ‖L (Y₁ - Y₀)‖ ^ 2 / 2 ∧
      0 ≤ ‖L (Y₁ - Y₀)‖ ^ 2 / 2 := by
  rw [quadratic_step, h, zero_add]
  exact ⟨rfl, by positivity⟩

end Quadratic

end

end LeanDLRA.Literature.P2101_12571
