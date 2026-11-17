import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stability.Energy

/-!
# Energy stability of DLRA for nonlinear kinetic models: Stefan–Boltzmann emission and
entropy (OP-SB-52)

Open problem OP-SB-52 of `docs/catalogue/survey/open-problems.json` (research-level).

## The nonlinear Stefan–Boltzmann coupling (arXiv 2402.16746 only treats the linearised model)

Thermal radiative transfer couples the radiation intensity `ψ(x, Ω)` with the material
temperature `T(x)`:

  `∂ₜ ψ = 𝒢 ψ - σ (ψ - ι B(T))`,   `c_v ∂ₜ T = σ (ι† ψ - B(T))`,

where `ι` embeds a material field isotropically into phase space (`(ι T)(x, Ω) = T(x)`), `ι†`
is the angular average, `𝒢` collects streaming (and isotropic scattering) and `B(T) = a c T⁴`
is the Planck emission.  arXiv 2402.16746 proves energy stability of the full and the DLRA
scheme only for the *linearised* emission (`B(T) = T`, the Su–Olson model), where the energy
`‖ψ‖² + ‖T‖²` is quadratic; for `T⁴` only numerical energy decay is reported.

The point of this module: the natural energy of the nonlinear model is not quadratic but
`𝓔(ψ, T) = ½ ‖ψ‖² + Φ(T)`, with `Φ' = c_v B`, i.e. `Φ(T) = c_v a c T⁵/5`.  Because `B` is
increasing on `T ≥ 0`, `Φ` is convex there, and testing the material equation with the *new*
emission `B(Tⁿ⁺¹)` gives `Φ(Tⁿ⁺¹) - Φ(Tⁿ) ≤ c_v ⟪B(Tⁿ⁺¹), Tⁿ⁺¹ - Tⁿ⟫` for free.  Combined with
the Galerkin energy identity `galerkin_step_energy_identity` this yields, for the DLRA step with
implicit emission–absorption and explicit streaming,

  `𝓔ⁿ⁺¹ + ½ ‖ψⁿ⁺¹ - P ψⁿ‖² + Δt σ ‖ψⁿ⁺¹ - ι B(Tⁿ⁺¹)‖² ≤ 𝓔ⁿ + Δt ⟪𝒢, ψⁿ⁺¹⟫`

for *any* orthogonal projector `P` (any bases), *any* step size for the coupling, and *any*
`σ ≥ 0`.  The nonlinearity costs nothing: no positivity bound, no two-sided temperature bound
and no frozen coefficient `4 (Tⁿ)³` is needed, only the convexity of `Φ` at the two iterates.
The streaming part contributes exactly the term absorbed by the CFL condition of the full
scheme, as in `dlra_imex_energy_stable`.

* `trt_galerkin_energy_step`: the energy inequality above.
* `trt_galerkin_energy_le`: under the full-scheme CFL estimate `2 Δt ⟪𝒢, ψⁿ⁺¹⟫ ≤ ‖ψⁿ⁺¹ - P ψⁿ‖²`,
  `𝓔ⁿ⁺¹ ≤ 𝓔ⁿ`; with `𝒢 = 0` (pure emission–absorption) unconditionally.
* `trt_galerkin_total_energy`: total energy `⟪ψ, ι c⟫ + c_v ⟪T, c⟫` is conserved if `ι c` lies in
  the range of `P` (basis augmentation) and the streaming is conservative.
* `stefanBoltzmann_convex`: the convexity inequality for `B(T) = κ T⁴`, `Φ(T) = c_v κ T⁵/5` on
  nonnegative temperatures (cellwise), with the exact remainder
  `c_v κ (y - x)² (y³ + 2 x y² + 3 x² y + 4 x³)/5`.
* `TRTExample`: a rank-one instance on `ℝ²` with `P ≠ ι ι†`, `B(T) = T⁴`, exact rational data
  solving the implicit equations, for which the energy drops from `69/20` to `6/5`.

## Entropy: the log-DLRA mechanism for BGK

For the Boltzmann–BGK collision operator `F = M[f] - f` the Lyapunov functional is the entropy
`Σ f log f`, whose gradient `log f + 1` is not low-rank.  The entropy production of the
`L²`-orthogonal DLRA `ḟ = P F` is `⟪F, P (log f + 1)⟫`, so the Galerkin trick above fails unless
`log f + 1 ∈ range P`.  Scratch numerics show that the sign is really lost:
even with the collision invariants `1, v, |v|²` in the velocity basis (conservative DLRA) there
are positive rank-`3` states arbitrarily close to a rank-`3` Maxwellian matrix at which the
entropy *increases* along `ḟ = P (M[f] - f)`.  Near a rank-`r` Maxwellian matrix `M` one has
`d/dt Σ f log f = -ε² ⟪P χ⊥, χ⊥/M⟫ + O(ε³)` for `f = M + ε χ`, `χ` tangent, `χ⊥` the part of
`χ` outside the moment space, and this quadratic form is indefinite for some `M` (`5 × 12` grid,
`r = 3`), whereas the full model gives `-ε² ⟪χ⊥, χ⊥/M⟫ < 0`.  (For rank one the collision term
is exactly tangent, `M[a ⊗ b] = a ⊗ M[b]`, and the DLRA inherits the H-theorem trivially.)
This counterexample is numerical and is not formalised here.

The mechanism that restores the H-theorem for every rank is to evolve `g = log f` on the
low-rank manifold with the tangent projector orthogonal in the entropy-Hessian metric
`⟪a, b⟫_f = Σ f a b`, which is the one metric in which `d/dt Σ f log f` is the pairing of `ġ`
with `g + 1`.

* `discrete_H_theorem`: `Σ (M - f)(log f + 1) ≤ 0` whenever `M > 0` has the same mass as `f` and
  `log M` is orthogonal to `M - f` (as it is when `log M` is a combination of collision
  invariants whose moments `M` matches).
* `weighted_galerkin_entropy_production`: if `P` is idempotent and self-adjoint for the
  `f`-weighted inner product, and `P (g + 1) = g + 1` (bases containing the constants), then the
  entropy production of `ġ = P (F / f)` equals `Σ F (g + 1)`, the full one;
  `weighted_galerkin_mass` is the corresponding mass conservation.
* `logDLRA_entropy_antitone`, `logDLRA_BGK_entropy_antitone`: along any solution of the
  log-DLRA with such projectors the entropy `Σ f log f` is nonincreasing whenever the full model
  is entropy dissipative, in particular for BGK.
* `isWOrthProj_wProj`: the weighted projectors exist with `P ≠ 1` (rank-one instance).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Novel.OpSB52

section TRT

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The convexity inequality used for the material energy, at one pair of states: `B e'` is a
(sub)gradient of `Φ` at `e'`, scaled by `c_v`. -/
def ConvexAt (Φ : F → ℝ) (B : F → F) (cv : ℝ) (e e' : F) : Prop :=
  Φ e' + cv * ⟪B e', e - e'⟫ ≤ Φ e

/-- **Energy inequality of one DLRA step for the nonlinear thermal radiative transfer system**
(arXiv 2402.16746 treats `B(T) = T`).  Let `P` be any orthogonal projector
(the Galerkin/S-step projector `X¹ X¹ᵀ (·) V¹ V¹ᵀ`), `ι` an isometry with adjoint `ι†`
(isotropic embedding and angular average), `σ ≥ 0` the opacity, `h ≥ 0` the step size and `𝒢`
the explicit part (streaming, evaluated at `P ψ`).  If `(ψ', e')` solve the implicit coupled step

  `ψ' = P (P ψ + h (𝒢 - σ (ψ' - ι B(e'))))`,   `c_v (e' - e) = h σ (ι† ψ' - B(e'))`

and `Φ` satisfies the convexity inequality `Φ(e) ≥ Φ(e') + c_v ⟪B(e'), e - e'⟫`, then

  `½ ‖ψ'‖² + Φ(e') + ½ ‖ψ' - P ψ‖² + h σ ‖ψ' - ι B(e')‖² ≤ ½ ‖P ψ‖² + Φ(e) + h ⟪𝒢, ψ'⟫`.

The nonlinear emission–absorption coupling is dissipative in the energy `½ ‖ψ‖² + Φ(e)` for
every projector and every step size; only the explicit part needs a CFL condition. -/
theorem trt_galerkin_energy_step {P : E →L[ℝ] E} (hP : IsOrthProj P) {ι : F →L[ℝ] E}
    {ιT : E →L[ℝ] F} (hadj : ∀ x ψ, ⟪ι x, ψ⟫ = ⟪x, ιT ψ⟫) (hiso : ∀ x y, ⟪ι x, ι y⟫ = ⟪x, y⟫)
    {Φ : F → ℝ} {B : F → F} {cv h σ : ℝ} {ψ ψ' G : E} {e e' : F}
    (hconv : ConvexAt Φ B cv e e')
    (hψ : ψ' = P (P ψ + h • (G - σ • (ψ' - ι (B e')))))
    (he : cv • (e' - e) = (h * σ) • (ιT ψ' - B e')) :
    1 / 2 * ‖ψ'‖ ^ 2 + Φ e' + 1 / 2 * ‖ψ' - P ψ‖ ^ 2 + h * σ * ‖ψ' - ι (B e')‖ ^ 2
      ≤ 1 / 2 * ‖P ψ‖ ^ 2 + Φ e + h * ⟪G, ψ'⟫ := by
  have hid := galerkin_step_energy_identity hP (hP.idem ψ) hψ
  -- the material energy, tested with the new emission
  have hmat : Φ e' - Φ e ≤ h * σ * (⟪ι (B e'), ψ'⟫ - ‖ι (B e')‖ ^ 2) := by
    have h1 : cv * ⟪B e', e' - e⟫ = h * σ * ⟪B e', ιT ψ' - B e'⟫ := by
      rw [← real_inner_smul_right, he, real_inner_smul_right]
    have h2 : ⟪B e', ιT ψ' - B e'⟫ = ⟪ι (B e'), ψ'⟫ - ‖ι (B e')‖ ^ 2 := by
      rw [inner_sub_right, ← hadj, ← hiso, real_inner_self_eq_norm_sq]
    have h3 : cv * ⟪B e', e - e'⟫ = -(cv * ⟪B e', e' - e⟫) := by
      rw [← neg_sub e' e, inner_neg_right]; ring
    unfold ConvexAt at hconv
    rw [h2] at h1
    linarith
  have hexp : ‖ψ' - ι (B e')‖ ^ 2 = ‖ψ'‖ ^ 2 - 2 * ⟪ι (B e'), ψ'⟫ + ‖ι (B e')‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hG : ⟪G - σ • (ψ' - ι (B e')), ψ'⟫
      = ⟪G, ψ'⟫ - σ * (‖ψ'‖ ^ 2 - ⟪ι (B e'), ψ'⟫) := by
    rw [inner_sub_left, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
  rw [hG] at hid
  rw [hexp]
  linarith [hid, hmat]

/-- **Energy stability of the DLRA step under the full-scheme CFL condition.**  If the explicit
part satisfies the estimate `2 h ⟪𝒢, ψ'⟫ ≤ ‖ψ' - P ψ‖²` (what the CFL condition of the full
scheme provides, cf. `dlra_imex_energy_stable`), then the energy `½ ‖ψ‖² + Φ(e)` does not
increase: `½ ‖ψ'‖² + Φ(e') ≤ ½ ‖ψ‖² + Φ(e)`.  For `𝒢 = 0` the hypothesis is trivial, so pure
emission–absorption with the nonlinear Planck function is unconditionally energy stable. -/
theorem trt_galerkin_energy_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {ι : F →L[ℝ] E}
    {ιT : E →L[ℝ] F} (hadj : ∀ x ψ, ⟪ι x, ψ⟫ = ⟪x, ιT ψ⟫) (hiso : ∀ x y, ⟪ι x, ι y⟫ = ⟪x, y⟫)
    {Φ : F → ℝ} {B : F → F} {cv h σ : ℝ} (hh : 0 ≤ h) (hσ : 0 ≤ σ) {ψ ψ' G : E} {e e' : F}
    (hconv : ConvexAt Φ B cv e e')
    (hψ : ψ' = P (P ψ + h • (G - σ • (ψ' - ι (B e')))))
    (he : cv • (e' - e) = (h * σ) • (ιT ψ' - B e'))
    (hcfl : 2 * h * ⟪G, ψ'⟫ ≤ ‖ψ' - P ψ‖ ^ 2) :
    1 / 2 * ‖ψ'‖ ^ 2 + Φ e' ≤ 1 / 2 * ‖ψ‖ ^ 2 + Φ e := by
  have h1 := trt_galerkin_energy_step hP hadj hiso hconv hψ he
  have h2 : ‖P ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hP.norm_le ψ) 2
  have h3 : 0 ≤ h * σ * ‖ψ' - ι (B e')‖ ^ 2 :=
    mul_nonneg (mul_nonneg hh hσ) (sq_nonneg _)
  linarith

/-- **Conservation of total energy.**  If the constant direction `ι c` lies in the range of `P`
(basis augmentation, arXiv 2402.16746 Thm 5) and the explicit part is conservative,
`⟪𝒢, ι c⟫ = 0`, then `⟪ψ', ι c⟫ + c_v ⟪e', c⟫ = ⟪ψ, ι c⟫ + c_v ⟪e, c⟫`: the implicit nonlinear
coupling exchanges energy between radiation and material exactly. -/
theorem trt_galerkin_total_energy {P : E →L[ℝ] E} (hP : IsOrthProj P) {ι : F →L[ℝ] E}
    {ιT : E →L[ℝ] F} (hadj : ∀ x ψ, ⟪ι x, ψ⟫ = ⟪x, ιT ψ⟫) (hiso : ∀ x y, ⟪ι x, ι y⟫ = ⟪x, y⟫)
    {B : F → F} {cv h σ : ℝ} {ψ ψ' G : E} {e e' c : F} (hc : P (ι c) = ι c)
    (hG : ⟪G, ι c⟫ = 0)
    (hψ : ψ' = P (P ψ + h • (G - σ • (ψ' - ι (B e')))))
    (he : cv • (e' - e) = (h * σ) • (ιT ψ' - B e')) :
    ⟪ψ', ι c⟫ + cv * ⟪e', c⟫ = ⟪ψ, ι c⟫ + cv * ⟪e, c⟫ := by
  have h1 : ⟪ψ', ι c⟫ = ⟪P ψ + h • (G - σ • (ψ' - ι (B e'))), ι c⟫ := by
    have := congrArg (fun z => ⟪z, ι c⟫) hψ
    rw [this, hP.symm, hc]
  have h2 : ⟪P ψ, ι c⟫ = ⟪ψ, ι c⟫ := by rw [hP.symm, hc]
  have h3 : ⟪ψ' - ι (B e'), ι c⟫ = ⟪ιT ψ' - B e', c⟫ := by
    rw [inner_sub_left, inner_sub_left, real_inner_comm (ι c) ψ', hadj, real_inner_comm c,
      hiso]
  have h4 : cv * ⟪e' - e, c⟫ = h * σ * ⟪ιT ψ' - B e', c⟫ := by
    rw [← real_inner_smul_left, he, real_inner_smul_left]
  rw [inner_add_left, real_inner_smul_left, inner_sub_left, real_inner_smul_left, h3, h2, hG]
    at h1
  rw [inner_sub_left] at h4
  linarith

/-- The remainder in the convexity inequality of `t ↦ t⁵/5`: for all `x y`,
`y⁵/5 - x⁵/5 - x⁴ (y - x) = (y - x)² (y³ + 2 x y² + 3 x² y + 4 x³)/5`. -/
lemma pow_five_convex_remainder (x y : ℝ) :
    y ^ 5 / 5 - x ^ 5 / 5 - x ^ 4 * (y - x)
      = (y - x) ^ 2 * (y ^ 3 + 2 * x * y ^ 2 + 3 * x ^ 2 * y + 4 * x ^ 3) / 5 := by ring

/-- Convexity of `t ↦ t⁵/5` on `[0, ∞)`: `x⁴ (y - x) ≤ y⁵/5 - x⁵/5` for `0 ≤ x`, `0 ≤ y`. -/
lemma pow_five_convex {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 4 * (y - x) ≤ y ^ 5 / 5 - x ^ 5 / 5 := by
  have h := pow_five_convex_remainder x y
  have hr : 0 ≤ (y - x) ^ 2 * (y ^ 3 + 2 * x * y ^ 2 + 3 * x ^ 2 * y + 4 * x ^ 3) / 5 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (sq_nonneg _)
    positivity
  linarith

variable {N : Type*} [Fintype N]

/-- The Stefan–Boltzmann emission `B(T)ᵢ = κ Tᵢ⁴` on a grid of material cells. -/
noncomputable def stefanBoltzmann (κ : ℝ) (T : EuclideanSpace ℝ N) : EuclideanSpace ℝ N :=
  WithLp.toLp 2 fun i => κ * T i ^ 4

/-- The material energy `Φ(T) = Σᵢ c_v κ Tᵢ⁵/5`, whose gradient is `c_v B(T)`. -/
noncomputable def planckEnergy (cv κ : ℝ) (T : EuclideanSpace ℝ N) : ℝ :=
  ∑ i, cv * κ * T i ^ 5 / 5

/-- **The Stefan–Boltzmann law satisfies the convexity inequality** on nonnegative temperatures:
`Φ(T) ≥ Φ(T') + c_v ⟪B(T'), T - T'⟫` for `κ, c_v ≥ 0` and `T, T' ≥ 0` cellwise.  This is the only
property of `B(T) = κ T⁴` used by `trt_galerkin_energy_step`; the exact remainder is
`Σᵢ c_v κ (Tᵢ - Tᵢ')² (Tᵢ³ + 2 Tᵢ' Tᵢ² + 3 Tᵢ'² Tᵢ + 4 Tᵢ'³)/5 ≥ 0`. -/
theorem stefanBoltzmann_convex {cv κ : ℝ} (hcv : 0 ≤ cv) (hκ : 0 ≤ κ)
    {T T' : EuclideanSpace ℝ N} (hT : ∀ i, 0 ≤ T i) (hT' : ∀ i, 0 ≤ T' i) :
    ConvexAt (planckEnergy cv κ) (stefanBoltzmann κ) cv T T' := by
  unfold ConvexAt planckEnergy
  rw [PiLp.inner_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [stefanBoltzmann, PiLp.toLp_apply, PiLp.sub_apply, RCLike.inner_apply, conj_trivial]
  have h := pow_five_convex (hT' i) (hT i)
  have hc : 0 ≤ cv * κ := mul_nonneg hcv hκ
  nlinarith [mul_le_mul_of_nonneg_left h hc]

/-! ### A rank-one instance on `ℝ²` with exact rational data -/

namespace TRTExample

/-- The Euclidean plane `ℝ²`: two angular directions `μ = ±1` in one spatial cell. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The standard basis vectors `e₀, e₁` of `ℝ²`. -/
noncomputable def e (i : Fin 2) : E2 := EuclideanSpace.single i 1

lemma inner_e_self (i : Fin 2) : ⟪e i, e i⟫ = (1 : ℝ) := by simp [e]

lemma inner_e01 : ⟪e 0, e 1⟫ = (0 : ℝ) := by simp [e, EuclideanSpace.inner_single_left]

lemma inner_e10 : ⟪e 1, e 0⟫ = (0 : ℝ) := by simp [e, EuclideanSpace.inner_single_left]

/-- The diagonal direction `d = e₀ + e₁`. -/
noncomputable def d : E2 := e 0 + e 1

lemma inner_d_d : ⟪d, d⟫ = (2 : ℝ) := by
  simp only [d, inner_add_left, inner_add_right, inner_e_self, inner_e01, inner_e10]; norm_num

lemma inner_d_e0 : ⟪d, e 0⟫ = (1 : ℝ) := by
  simp only [d, inner_add_left, inner_e_self, inner_e10]; norm_num

lemma inner_e0_d : ⟪e 0, d⟫ = (1 : ℝ) := by
  simp only [d, inner_add_right, inner_e_self, inner_e01]; norm_num

lemma inner_d_e1 : ⟪d, e 1⟫ = (1 : ℝ) := by
  simp only [d, inner_add_left, inner_e_self, inner_e01]; norm_num

/-- The rank-one orthogonal projector onto the line spanned by `d`: `x ↦ ½ ⟪d, x⟫ d`.  This is
*not* the isotropic projector `ι ι†` (which projects onto `e₀`). -/
noncomputable def Pd : E2 →L[ℝ] E2 := ((1 / 2 : ℝ) • innerSL ℝ d).smulRight d

lemma Pd_apply (x : E2) : Pd x = (1 / 2 * ⟪d, x⟫) • d := rfl

lemma isOrthProj_Pd : IsOrthProj Pd where
  idem x := by
    rw [Pd_apply, Pd_apply, real_inner_smul_right, inner_d_d]; congr 1; ring
  symm x y := by
    rw [Pd_apply, Pd_apply, real_inner_smul_left, real_inner_smul_right, real_inner_comm d x]
    ring

/-- The isotropic embedding `ι : ℝ → ℝ²`, `t ↦ t e₀`, and its adjoint `ι† = ⟪e₀, ·⟫`. -/
noncomputable def ι : ℝ →L[ℝ] E2 := (1 : ℝ →L[ℝ] ℝ).smulRight (e 0)

noncomputable def ιT : E2 →L[ℝ] ℝ := innerSL ℝ (e 0)

lemma ι_apply (t : ℝ) : ι t = t • e 0 := by simp [ι]

lemma ιT_apply (ψ : E2) : ιT ψ = ⟪e 0, ψ⟫ := rfl

lemma ι_adjoint (t : ℝ) (ψ : E2) : ⟪ι t, ψ⟫ = ⟪t, ιT ψ⟫ := by
  rw [ι_apply, ιT_apply, real_inner_smul_left, RCLike.inner_apply', conj_trivial]

lemma ι_isometry (s t : ℝ) : ⟪ι s, ι t⟫ = ⟪s, t⟫ := by
  rw [ι_apply, ι_apply, real_inner_smul_left, real_inner_smul_right, inner_e_self,
    RCLike.inner_apply', conj_trivial]; ring

/-- Planck emission `B(T) = T⁴` and material energy `Φ(T) = T⁵/5` for a single cell. -/
noncomputable def B (T : ℝ) : ℝ := T ^ 4

noncomputable def Φ (T : ℝ) : ℝ := T ^ 5 / 5

/-- **The hypotheses of `trt_galerkin_energy_le` are jointly satisfiable in a genuinely
low-rank, genuinely nonlinear situation**: `P = Pd ≠ 1`, `P ≠ ι ι†`, `h = σ = c_v = 1`,
`𝒢 = 0`, `B(T) = T⁴`.  The data `ψ = (7/2, 3/2)`, `T = 1/2` and `ψ' = (3/2, 3/2)`, `T' = 1`
solve the implicit coupled equations exactly, and the energy drops from
`½ ‖ψ‖² + Φ(T) = 1161/160` to `½ ‖ψ'‖² + Φ(T') = 49/20`. -/
lemma Pd_ψ : Pd ((7 / 2 : ℝ) • e 0 + (3 / 2 : ℝ) • e 1) = (5 / 2 : ℝ) • d := by
  rw [Pd_apply]
  simp only [inner_add_right, real_inner_smul_right, inner_d_e0, inner_d_e1]
  congr 1; ring

/-- The radiation equation of the instance, `ψ' = P (P ψ + h (𝒢 - σ (ψ' - ι B(T'))))`. -/
lemma radiation_eq :
    (3 / 2 : ℝ) • d = Pd (Pd ((7 / 2 : ℝ) • e 0 + (3 / 2 : ℝ) • e 1)
      + (1 : ℝ) • ((0 : E2) - (1 : ℝ) • ((3 / 2 : ℝ) • d - ι (B 1)))) := by
  rw [Pd_ψ]
  have h2 : (5 / 2 : ℝ) • d + (1 : ℝ) • ((0 : E2) - (1 : ℝ) • ((3 / 2 : ℝ) • d - ι (B 1)))
      = (2 : ℝ) • e 0 + e 1 := by
    simp only [B, ι_apply, one_pow, one_smul, zero_sub, d]; module
  rw [h2, Pd_apply, inner_add_right, real_inner_smul_right, inner_d_e0, inner_d_e1]
  simp only [d]; module

/-- The material equation of the instance, `c_v (T' - T) = h σ (ι† ψ' - B(T'))`. -/
lemma material_eq :
    (1 : ℝ) • ((1 : ℝ) - 1 / 2) = ((1 : ℝ) * 1) • (ιT ((3 / 2 : ℝ) • d) - B 1) := by
  rw [ιT_apply, real_inner_smul_right, inner_e0_d]
  simp only [B, smul_eq_mul]; norm_num

/-- **The hypotheses of `trt_galerkin_energy_le` are jointly satisfiable in a genuinely
low-rank, genuinely nonlinear situation**: `P = Pd ≠ 1`, `P ≠ ι ι†`, `h = σ = c_v = 1`,
`𝒢 = 0`, `B(T) = T⁴`.  The data `ψ = (7/2, 3/2)`, `T = 1/2` and `ψ' = (3/2, 3/2)`, `T' = 1`
solve the implicit coupled equations exactly (`radiation_eq`, `material_eq`), and the energy
drops from `½ ‖ψ‖² + Φ(T) = 1161/160` to `½ ‖ψ'‖² + Φ(T') = 49/20`. -/
theorem instance_energy_le :
    1 / 2 * ‖(3 / 2 : ℝ) • d‖ ^ 2 + Φ 1
      ≤ 1 / 2 * ‖(7 / 2 : ℝ) • e 0 + (3 / 2 : ℝ) • e 1‖ ^ 2 + Φ (1 / 2) := by
  refine trt_galerkin_energy_le (ι := ι) (ιT := ιT) isOrthProj_Pd ι_adjoint ι_isometry
    (Φ := Φ) (B := B) (cv := 1) (h := 1) (σ := 1) zero_le_one zero_le_one (G := 0)
    (e := 1 / 2) (e' := 1) ?_ radiation_eq material_eq ?_
  · simp only [ConvexAt, Φ, B, RCLike.inner_apply', conj_trivial]; norm_num
  · simp

/-- The projector of the instance is neither the identity nor the isotropic projector `ι ι†`:
`Pd e₀ = d/2 ≠ e₀`. -/
theorem Pd_ne_isotropic : Pd (e 0) ≠ ι (ιT (e 0)) := by
  intro h
  rw [Pd_apply, inner_d_e0, ι_apply, ιT_apply, inner_e_self, one_smul] at h
  have := congrArg (fun x => ⟪e 1, x⟫) h
  simp only [real_inner_smul_right, d, inner_add_right, inner_e10, inner_e_self] at this
  norm_num at this

end TRTExample

end TRT

/-! ### Entropy: the log-DLRA mechanism for BGK -/

section Entropy

variable {ι : Type*} [Fintype ι]

/-- The inner product weighted by `w`: `⟪a, b⟫_w = Σᵢ wᵢ aᵢ bᵢ`.  With `w = f` this is the
Hessian metric of the entropy `Σ f log f` at `f`. -/
def winner (w a b : ι → ℝ) : ℝ := ∑ i, w i * a i * b i

lemma winner_comm (w a b : ι → ℝ) : winner w a b = winner w b a := by
  unfold winner; exact Finset.sum_congr rfl fun i _ => by ring

lemma winner_add_left (w a b c : ι → ℝ) : winner w (a + b) c = winner w a c + winner w b c := by
  unfold winner; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring

lemma winner_smul_left (w : ι → ℝ) (r : ℝ) (a c : ι → ℝ) :
    winner w (r • a) c = r * winner w a c := by
  unfold winner; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma winner_smul_right (w : ι → ℝ) (r : ℝ) (a c : ι → ℝ) :
    winner w a (r • c) = r * winner w a c := by
  rw [winner_comm, winner_smul_left, winner_comm]

lemma winner_self_pos {w : ι → ℝ} (hw : ∀ i, 0 < w i) {c : ι → ℝ} (hc : c ≠ 0) :
    0 < winner w c c := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hc
  unfold winner
  apply Finset.sum_pos'
  · intro i _; rw [mul_assoc]; exact mul_nonneg (hw i).le (mul_self_nonneg _)
  · exact ⟨j, Finset.mem_univ j, by rw [mul_assoc]; exact mul_pos (hw j) (mul_self_pos.2 hj)⟩

/-- `P` is an orthogonal projector for the `w`-weighted inner product: idempotent and
`w`-self-adjoint.  For `w = f` this is the tangent projector of the low-rank manifold in the
entropy-Hessian metric. -/
structure IsWOrthProj (w : ι → ℝ) (P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop where
  idem : ∀ a, P (P a) = P a
  symm : ∀ a b, winner w (P a) b = winner w a (P b)

/-- The rank-one `w`-orthogonal projector onto the line spanned by `c`. -/
noncomputable def wProj (w c : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun a := (winner w a c / winner w c c) • c
  map_add' a b := by rw [winner_add_left, add_div, add_smul]
  map_smul' r a := by
    simp only [RingHom.id_apply]; rw [winner_smul_left, mul_div_assoc, smul_smul]

lemma wProj_apply (w c a : ι → ℝ) : wProj w c a = (winner w a c / winner w c c) • c := rfl

/-- The rank-one weighted projector is a `w`-orthogonal projector (an instance showing that the
hypotheses of `weighted_galerkin_entropy_production` are satisfiable with `P ≠ 1`). -/
theorem isWOrthProj_wProj {w : ι → ℝ} (hw : ∀ i, 0 < w i) {c : ι → ℝ} (hc : c ≠ 0) :
    IsWOrthProj w (wProj w c) where
  idem a := by
    have h := (winner_self_pos hw hc).ne'
    rw [wProj_apply, wProj_apply, winner_smul_left]
    congr 1; field_simp
  symm a b := by
    rw [wProj_apply, wProj_apply, winner_smul_left, winner_smul_right, winner_comm w c b]
    ring

lemma wProj_self {w : ι → ℝ} (hw : ∀ i, 0 < w i) {c : ι → ℝ} (hc : c ≠ 0) : wProj w c c = c := by
  rw [wProj_apply, div_self (winner_self_pos hw hc).ne', one_smul]

/-- **Discrete H-theorem for a BGK-type relaxation.**  If `M > 0` has the same mass as `f > 0`
and `log M` is orthogonal to `M - f` (as it is for a Maxwellian: `log M` is a combination of the
collision invariants, whose moments `M` matches), then `Σ (M - f)(log f + 1) ≤ 0`, i.e. the
entropy `Σ f log f` does not increase along `ḟ = M - f`. -/
theorem discrete_H_theorem {f M : ι → ℝ} (hf : ∀ i, 0 < f i) (hM : ∀ i, 0 < M i)
    (hmass : ∑ i, (M i - f i) = 0) (hlog : ∑ i, (M i - f i) * Real.log (M i) = 0) :
    ∑ i, (M i - f i) * (Real.log (f i) + 1) ≤ 0 := by
  have h : ∑ i, (M i - f i) * (Real.log (f i) + 1)
      = ∑ i, (M i - f i) * (Real.log (f i) - Real.log (M i)) := by
    have e : ∀ i, (M i - f i) * (Real.log (f i) + 1)
        = (M i - f i) * (Real.log (f i) - Real.log (M i)) + (M i - f i) * Real.log (M i)
          + (M i - f i) := fun i => by ring
    simp only [e, Finset.sum_add_distrib, hlog, hmass, add_zero]
  rw [h]
  apply Finset.sum_nonpos
  intro i _
  rcases le_total (f i) (M i) with hle | hle
  · have := Real.log_le_log (hf i) hle
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  · have := Real.log_le_log (hM i) hle
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- **Entropy production of the log-DLRA equals that of the full model.**  Evolve `g = log f` by
`ġ = P (F / f)`, `f = exp g`, where `P` is an orthogonal projector for the `f`-weighted (entropy
Hessian) metric with `g + 1` in its range (bases containing the constants).  Then
`d/dt Σ f log f = Σ f ġ (g + 1) = Σ F (g + 1)`, exactly the entropy production of `ḟ = F`.  The
`L²`-orthogonal DLRA of `f` instead gives `⟪F, P (log f + 1)⟫`, which has no sign because
`log f + 1` is not low-rank (see the module docstring). -/
theorem weighted_galerkin_entropy_production {g F : ι → ℝ} {P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hP : IsWOrthProj (fun i => Real.exp (g i)) P) (hg : P (g + 1) = g + 1) :
    ∑ i, Real.exp (g i) * P (fun i => F i / Real.exp (g i)) i * (g i + 1)
      = ∑ i, F i * (g i + 1) := by
  have h1 : ∑ i, Real.exp (g i) * P (fun i => F i / Real.exp (g i)) i * (g i + 1)
      = winner (fun i => Real.exp (g i)) (P (fun i => F i / Real.exp (g i))) (g + 1) := by
    simp only [winner, Pi.add_apply, Pi.one_apply]
  rw [h1, hP.symm, hg]
  simp only [winner, Pi.add_apply, Pi.one_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [mul_div_cancel₀ _ (Real.exp_ne_zero _)]

/-- **Mass conservation of the log-DLRA**: if the constants are in the range of `P`, then
`d/dt Σ f = Σ f ġ = Σ F`. -/
theorem weighted_galerkin_mass {g F : ι → ℝ} {P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hP : IsWOrthProj (fun i => Real.exp (g i)) P) (h1 : P 1 = 1) :
    ∑ i, Real.exp (g i) * P (fun i => F i / Real.exp (g i)) i = ∑ i, F i := by
  have h : ∑ i, Real.exp (g i) * P (fun i => F i / Real.exp (g i)) i
      = winner (fun i => Real.exp (g i)) (P (fun i => F i / Real.exp (g i))) 1 := by
    simp only [winner, Pi.one_apply, mul_one]
  rw [h, hP.symm, h1]
  simp only [winner, Pi.one_apply, mul_one]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_div_cancel₀ _ (Real.exp_ne_zero _)]

/-- The entropy `Σ f log f` written in the variable `g = log f`. -/
noncomputable def entropy (g : ι → ℝ) : ℝ := ∑ i, Real.exp (g i) * g i

/-- Chain rule: `d/dt Σ exp(g) g = Σ exp(g) ġ (g + 1)`. -/
theorem hasDerivAt_entropy {g : ℝ → ι → ℝ} {g' : ι → ℝ} {t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun t => entropy (g t)) (∑ i, Real.exp (g t i) * g' i * (g t i + 1)) t := by
  unfold entropy
  apply HasDerivAt.fun_sum
  intro i _
  have hi : HasDerivAt (fun t => g t i) (g' i) t := hasDerivAt_pi.1 hg i
  have := hi.exp.mul hi
  convert this using 1; ring

/-- **The log-DLRA is entropy-nonincreasing whenever the full model is.**  Let `g(t) = log f(t)`
solve `ġ = P(t) (F(t) / exp g)`, where `P(t)` is an orthogonal projector for the
`exp g(t)`-weighted metric with `g(t) + 1` in its range, and let the full model be entropy
dissipative, `Σ F(t) (g(t) + 1) ≤ 0`.  Then `t ↦ Σ f log f` is nonincreasing. -/
theorem logDLRA_entropy_antitone {g : ℝ → ι → ℝ} {P : ℝ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    {F : ℝ → ι → ℝ}
    (hg : ∀ t, HasDerivAt g (P t fun i => F t i / Real.exp (g t i)) t)
    (hP : ∀ t, IsWOrthProj (fun i => Real.exp (g t i)) (P t))
    (h1 : ∀ t, P t (g t + 1) = g t + 1)
    (hF : ∀ t, ∑ i, F t i * (g t i + 1) ≤ 0) :
    Antitone fun t => entropy (g t) := by
  apply antitone_of_deriv_nonpos
  · intro t; exact (hasDerivAt_entropy (hg t)).differentiableAt
  · intro t
    rw [(hasDerivAt_entropy (hg t)).deriv, weighted_galerkin_entropy_production (hP t) (h1 t)]
    exact hF t

/-- **H-theorem for the log-DLRA of BGK** (OP-SB-52 asks for entropy stability
of DLRA for Boltzmann–BGK).  With `F(t) = M(t) - exp g(t)` for Maxwellians `M(t) > 0` of the same
mass as `f(t) = exp g(t)` and with `log M(t) ⊥ (M(t) - f(t))`, the entropy `Σ f log f` of the
log-DLRA solution with Hessian-metric projectors containing the constants is nonincreasing. -/
theorem logDLRA_BGK_entropy_antitone {g : ℝ → ι → ℝ} {P : ℝ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    {M : ℝ → ι → ℝ} (hM : ∀ t i, 0 < M t i)
    (hg : ∀ t, HasDerivAt g (P t fun i => (M t i - Real.exp (g t i)) / Real.exp (g t i)) t)
    (hP : ∀ t, IsWOrthProj (fun i => Real.exp (g t i)) (P t))
    (h1 : ∀ t, P t (g t + 1) = g t + 1)
    (hmass : ∀ t, ∑ i, (M t i - Real.exp (g t i)) = 0)
    (hlog : ∀ t, ∑ i, (M t i - Real.exp (g t i)) * Real.log (M t i) = 0) :
    Antitone fun t => entropy (g t) := by
  refine logDLRA_entropy_antitone (F := fun t i => M t i - Real.exp (g t i)) hg hP h1 fun t => ?_
  have := discrete_H_theorem (fun i => Real.exp_pos (g t i)) (hM t) (hmass t) (hlog t)
  simpa only [Real.log_exp] using this

end Entropy

end LeanDLRA.Novel.OpSB52
