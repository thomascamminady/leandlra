import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Analysis.Defs

/-!
# `L²`-stability and energy stability of robust dynamical low-rank integrators

For hyperbolic and parabolic (kinetic) problems the relevant notion of stability of a
time-stepping scheme is `L²`-stability, `‖uⁿ⁺¹‖ ≤ ‖uⁿ‖`, typically guaranteed for the full
(full-rank) scheme by a CFL condition.  The question studied by Kusch–Einkemmer–Ceruti
(arXiv 2107.07282), Einkemmer–Hu–Kusch (arXiv 2212.12012) and Zhang–Hu (arXiv 2507.15192) is
whether dynamical low-rank integrators *inherit* this stability.  The answer depends on the
integrator:

* the **basis-update & Galerkin (BUG)** integrator only uses forward Galerkin steps, which are
  orthogonal projections of forward steps of the full problem; hence it inherits `L²`-stability
  under exactly the CFL condition of the full scheme, for *any* choice of bases;
* the **projector-splitting (KSL) integrator** contains the backward S-step
  `Ṡ = -U₁ᵀ F(U₁ S V₀ᵀ) V₀`, which runs the dynamics backward in time: for dissipative problems it
  is *anti-dissipative*.  How much stability is lost depends on the discretisation.  With the
  classical Lax–Friedrichs scheme, whose numerical diffusion `∼ Δx²/Δt` scales like `1/h`, the
  discretise-first KSL integrator is unstable for every step size (arXiv 2107.07282, Theorem 1).
  With the Lax–Friedrichs field `F_LF` of Zhang–Hu, whose numerical diffusion `λ_max M₂/(2Δx)`
  does not depend on `h` (a Rusanov-type flux), Zhang–Hu prove `L²`-stability under the stricter
  CFL condition `ν ≤ 1/3` (arXiv 2507.15192, Theorems 3.3 and 3.6).  They state explicitly that
  their conclusions differ from those of arXiv 2107.07282, Theorems 1–2.  The abstract
  counterpart is `kslEulerStep_smul`: an `h`-independent field gives a stricter CFL condition,
  while the `h`-dependent field `-(2/h)·id` gives the factor `3` for every `h`.  Stability can
  also be recovered by suitable implicit/explicit combinations of the substeps
  (arXiv 2507.15192, Theorem 4.3).

Following the abstract framework of the library, all substeps are written as full-space maps on
a real inner product space `E` with orthogonal projectors standing for the basis projectors:
`P₀, P₁` (left, `X ↦ U Uᵀ X`) and `Q₀, Q₁` (right, `X ↦ X V Vᵀ`).

## Main results

Explicit Euler (BUG).
* `galerkinEulerStep_norm_le`, `bug_euler_norm_le`, `galerkinEulerIter_norm_le`,
  `augmentedBug_euler_norm_le`: if the full explicit Euler step `x ↦ x + h F(x)` has
  amplification factor `γ` (`γ = 1`: the CFL condition of the full scheme), so has the explicit
  Euler BUG step `u₁ = P₁ Q₁ (ū + h F(ū))`, `ū = P₁ Q₁ u₀` (arXiv 2107.07282, Theorem 4), for
  arbitrary bases, over any number of steps, and for the augmented (rank-adaptive) BUG integrator
  with a norm-nonincreasing truncation.
* `eulerStep_norm_le_of_inner_le`: an abstract CFL condition: `⟪F x, x⟫ ≤ -β ‖F x‖²` and
  `0 ≤ h ≤ 2 β` imply `‖x + h F(x)‖ ≤ ‖x‖`.

Continuous substeps (BUG, dissipative fields).
* `dissipative_iff_adjoint`: for linear `𝒜`, `𝒜 + 𝒜* ≤ 0` iff `⟪𝒜 x, x⟫ ≤ 0`.
* `galerkin_substep_norm_le_of_dissipative`, `bug_norm_le_of_dissipative`,
  `bug_norm_le_of_dissipative_linear`, `augmentedBug_norm_le_of_dissipative`: the K-, L- and
  Galerkin S-steps are norm-nonincreasing for dissipative `F` (`⟪F(t, x), x⟫ ≤ 0`), hence the BUG
  step is `L²`-stable without any step-size restriction.

Projector-splitting integrator (KSL).
* `hasDerivWithinAt_norm_sq_backward`, `ksl_sStep_hasDerivWithinAt_norm_sq`: along the backward
  S-step `YS' = -P₁ Q₀ F(t, YS)`, `d/dt ‖YS‖² = -2 ⟪P₁ Q₀ F(t, YS), YS⟫ = -2 ⟪F(t, YS), YS⟫`.
* `ksl_sStep_norm_ge_of_dissipative`: for dissipative `F` the backward S-step does not decrease
  the norm (the instability mechanism of arXiv 2107.07282, Theorem 1 and Remark 1).
* `norm_le_exp_of_inner_deriv_le`, `ksl_sStep_norm_le_exp`, `ksl_sStep_norm_le_exp_linear`:
  `‖YS(t₁)‖ ≤ exp(‖𝒜‖ h) ‖YS(t₀)‖`, attained by `ksl_sStep_growth_example`.
* `kslSplitStep_norm_le`, `kslEulerStep_norm_le`: generic composition lemmas.  The substeps may
  use different discretisations `FK, FS, FL`, and the substep amplification bounds are needed only
  on the inputs that occur (`range Q₀`, resp. `range P₁ ∩ range Q₀`).  This is the structure of
  the proofs of arXiv 2107.07282, Theorems 2–3, for the schemes (31) and (35), whose S-step is
  discretised differently from the K- and L-steps.  The Fourier-analytic substep factors are not
  formalised.
* `kslSplitStep_energy_le`: the same composition with energy functionals in place of norms.  This
  is the structure of the proof of arXiv 2507.15192, Theorem 3.3, which carries the mixed `L²–H¹`
  energy `‖·‖² + ν(1 - ν)|·|²_{1,x}` from the K-step (eq. (3.12)) through the S- and L-steps
  (Lemma 3.4, eq. (3.18)), because the S-step is not stable on its own.
* `kslS_norm_ge_of_dissipative`: discrete anti-dissipativity of the S-step.
* `kslEulerStep_smul`, `ksl_scalar_amplification_le_one_iff`: for `F = -c·id` and a state in
  both bases, the KSL step multiplies by `(1 - hc)² (1 + hc)`.  This is `≤ 1` iff
  `hc ≤ (1 + √5)/2`, whereas the full explicit Euler step only needs `hc ≤ 2`.  An
  `h`-independent dissipative field therefore gives a stricter CFL condition, not unconditional
  instability.
* `kslEulerStep_unstable`: for the `h`-dependent field `-(2/h)·id` (`hc = 2`, the classical
  Lax–Friedrichs mode with `cos(ᾱπΔx) = -1`), the KSL step amplifies by `3` although the full
  explicit Euler step is norm-preserving (arXiv 2107.07282, Theorem 1, abstract form).
* `implicitGalerkin_norm_le` (backward Euler Galerkin steps are contractive for dissipative
  fields, arXiv 2507.15192, Theorem 4.1), `hybridKSL_norm_le`: the hybrid KSL integrator with
  backward Euler K- and L-steps and a forward Euler S-step is unconditionally `L²`-stable
  (arXiv 2507.15192, Theorems 4.3–4.4); `allBackwardKSL_unstable`: the all-backward variant is not
  (arXiv 2507.15192, Proposition 4.2 with `θ = 1`).

Energy stability (arXiv 2212.12012).
* `galerkin_norm_sq_add_integral_le`: if `⟪F(t, x), x⟫ ≤ -D(x)` on the Galerkin space, then
  `‖y(t)‖² + 2 ∫ₐᵗ D(y) ≤ ‖y(a)‖²`.  This is the integrated abstract form of Theorem 5.1, where
  `D` is the scattering dissipation `(σ₀/ε²)‖gˢ‖²` of the microscopic part.
* `galerkin_norm_le_exp`: Galerkin solutions with `⟪F(t, x), x⟫ ≤ ℓ ‖x‖²` on the Galerkin space
  satisfy `‖y(t)‖ ≤ exp(ℓ (t - a)) ‖y(a)‖`.  The micro–macro system of the paper only has `ℓ = 0`,
  because scattering does not damp the macroscopic part `ρ`.
* `galerkin_step_energy_identity`, `galerkin_imex_norm_le`, `dlra_imex_energy_stable`: the
  discrete energy identity `‖v‖² - ‖u‖² + ‖v - u‖² = 2 h ⟪G, v⟫` holds verbatim for Galerkin steps
  `v = Π(u + h G)`, so any energy estimate of the full IMEX scheme proved by testing with the new
  iterate is inherited by the DLRA scheme under the same CFL condition (Theorem 5.2).

Examples.  The section `EnergyExamples` instantiates `bug_euler_norm_le`, `kslEulerStep_norm_le`,
`kslEulerStep_unstable` and `hybridKSL_norm_le` on `ℝ²`.  These examples use rank-one orthogonal
projectors (`P ≠ 1`) and a dissipative field that couples the two coordinates.

## Conventions

Discrete steps use an autonomous (frozen-time) field `F : E → E`; time dependence is covered by
the iterated versions with step-dependent fields `F n`.  Implicit steps are stated for given
solutions of the implicit equations (existence is a separate matter and is not needed for
stability).  The energy `eⁿ = ‖ρ‖² + ε²‖g‖²` of the micro–macro scheme of arXiv 2212.12012 is the
squared norm of a weighted inner product on the product space `(ρ, g)`, with the Galerkin
projector acting as the identity on the macroscopic component; this is covered by working with
an arbitrary inner product space.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Explicit Euler steps and the BUG integrator -/

section ExplicitEuler

/-- The explicit-Euler Galerkin step `x ↦ P (P x + h F(P x))`.  For `P = P₁ Q₁` this is the
explicit Euler BUG step: the S-step starts from `ū = P₁ Q₁ u₀ = U₁ (U₁ᵀ U₀ S₀ V₀ᵀ V₁) V₁ᵀ` and
`u₁ = U₁ S₁ V₁ᵀ = P₁ Q₁ (ū + h F(ū))` (arXiv 2107.07282, eq. (38)). -/
def galerkinEulerStep (P : E →L[ℝ] E) (F : E → E) (h : ℝ) (x : E) : E :=
  P (eulerStep F h (P x))

/-- **Stability inheritance of Galerkin explicit Euler steps.**  If the full explicit Euler step
has amplification factor `γ ≥ 0` on `range P`, so has the Galerkin step (on all of `E`). -/
theorem galerkinEulerStep_norm_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {F : E → E} {h γ : ℝ}
    (hγ : 0 ≤ γ) (hF : ∀ x, P x = x → ‖eulerStep F h x‖ ≤ γ * ‖x‖) (x : E) :
    ‖galerkinEulerStep P F h x‖ ≤ γ * ‖x‖ :=
  (hP.norm_le _).trans
    ((hF _ (hP.idem x)).trans (mul_le_mul_of_nonneg_left (hP.norm_le x) hγ))

/-- **`L²`-stability of the explicit Euler BUG step** (Kusch–Einkemmer–Ceruti, arXiv 2107.07282,
Theorem 4, abstract form).  Let `P₁, Q₁` be commuting orthogonal projectors (the new left and
right bases).  If the full explicit Euler step is norm-nonincreasing up to the factor `γ` on
`range (P₁ Q₁)` (for `γ = 1`: the CFL condition of the full scheme), then the BUG step
`u₁ = P₁ Q₁ (ū + h F(ū))`, `ū = P₁ Q₁ u₀`, satisfies `‖u₁‖ ≤ γ ‖u₀‖`.  The paper proves this for
the Lax–Friedrichs discretisation of linear advection via Fourier analysis; here it holds for any
field and any choice of the bases. -/
theorem bug_euler_norm_le {P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) {F : E → E} {h γ : ℝ} (hγ : 0 ≤ γ)
    (hF : ∀ x, P₁ (Q₁ x) = x → ‖eulerStep F h x‖ ≤ γ * ‖x‖) (u₀ : E) :
    ‖P₁ (Q₁ (eulerStep F h (P₁ (Q₁ u₀))))‖ ≤ γ * ‖u₀‖ :=
  galerkinEulerStep_norm_le (hP₁.mul hQ₁ hc) hγ hF u₀

/-- Iterates of explicit-Euler Galerkin steps with step-dependent Galerkin projectors `P n`
(the bases chosen by the K- and L-steps in step `n`) and step-dependent fields `F n` (e.g.
`F n = F(tₙ, ·)`). -/
def galerkinEulerIter (P : ℕ → E →L[ℝ] E) (F : ℕ → E → E) (h : ℝ) (u₀ : E) : ℕ → E
  | 0 => u₀
  | n + 1 => galerkinEulerStep (P n) (F n) h (galerkinEulerIter P F h u₀ n)

/-- **Discrete `L²`-stability of the explicit Euler BUG integrator over many steps**, uniformly
in the choice of the bases: `‖uₙ‖ ≤ γⁿ ‖u₀‖`. -/
theorem galerkinEulerIter_norm_le {P : ℕ → E →L[ℝ] E} (hP : ∀ n, IsOrthProj (P n))
    {F : ℕ → E → E} {h γ : ℝ} (hγ : 0 ≤ γ)
    (hF : ∀ n x, P n x = x → ‖eulerStep (F n) h x‖ ≤ γ * ‖x‖) (u₀ : E) (n : ℕ) :
    ‖galerkinEulerIter P F h u₀ n‖ ≤ γ ^ n * ‖u₀‖ := by
  induction n with
  | zero => simp [galerkinEulerIter]
  | succ n ih =>
    calc ‖galerkinEulerIter P F h u₀ (n + 1)‖ ≤ γ * ‖galerkinEulerIter P F h u₀ n‖ :=
          galerkinEulerStep_norm_le (hP n) hγ (hF n) _
      _ ≤ γ * (γ ^ n * ‖u₀‖) := mul_le_mul_of_nonneg_left ih hγ
      _ = γ ^ (n + 1) * ‖u₀‖ := by ring

/-- **`L²`-stability of the explicit Euler augmented (rank-adaptive) BUG step.**  The augmented
basis contains the old one, so `P u₀ = u₀` (with `P = P̂₁ Q̂₁`) and the Galerkin step
`P (P u₀ + h F(P u₀))` equals `Ŷ₁ = P (u₀ + h F(u₀))`; it is followed by any norm-nonincreasing
truncation `u₁` (e.g. a truncated SVD, which is an orthogonal projection of `Ŷ₁`).  The
inequality itself holds for any `u₀`, but only for `P u₀ = u₀` does `P (u₀ + h F(u₀))` describe
the Galerkin step; the general case `P (P u₀ + h F(P u₀))` is `galerkinEulerStep_norm_le`. -/
theorem augmentedBug_euler_norm_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {F : E → E}
    {h γ : ℝ} {u₀ u₁ : E} (hF : ‖eulerStep F h u₀‖ ≤ γ * ‖u₀‖)
    (htr : ‖u₁‖ ≤ ‖P (eulerStep F h u₀)‖) : ‖u₁‖ ≤ γ * ‖u₀‖ :=
  htr.trans ((hP.norm_le _).trans hF)

/-- Expansion of the explicit Euler step: `‖x + h F x‖² = ‖x‖² + 2 h ⟪F x, x⟫ + h² ‖F x‖²`. -/
lemma norm_eulerStep_sq (F : E → E) (h : ℝ) (x : E) :
    ‖eulerStep F h x‖ ^ 2 = ‖x‖ ^ 2 + 2 * h * ⟪F x, x⟫ + h ^ 2 * ‖F x‖ ^ 2 := by
  rw [eulerStep, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, real_inner_comm]
  ring

/-- **An abstract CFL condition.**  If `⟪F x, x⟫ ≤ -β ‖F x‖²` (e.g. `F = 𝒜` symmetric negative
semidefinite with `β = 1 / ‖𝒜‖`) and `0 ≤ h ≤ 2 β`, the explicit Euler step is
norm-nonincreasing at `x`.  Combined with `bug_euler_norm_le`, the BUG step is stable under the
same step-size restriction. -/
theorem eulerStep_norm_le_of_inner_le {F : E → E} {β h : ℝ} (hh : 0 ≤ h) (hhβ : h ≤ 2 * β)
    {x : E} (hF : ⟪F x, x⟫ ≤ -β * ‖F x‖ ^ 2) : ‖eulerStep F h x‖ ≤ ‖x‖ := by
  have h1 := norm_eulerStep_sq F h x
  have h2 : 0 ≤ ‖F x‖ ^ 2 := sq_nonneg _
  have h3 : h * ‖F x‖ ^ 2 * (h - 2 * β) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hh h2) (by linarith)
  have h4 : 2 * h * ⟪F x, x⟫ ≤ 2 * h * (-β * ‖F x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have h5 : ‖eulerStep F h x‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [h1]; nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h5

end ExplicitEuler

/-! ### Continuous BUG substeps for dissipative fields -/

section Dissipative

/-- For a linear operator, `𝒜 + 𝒜* ≤ 0` (the dissipativity assumption `𝒜 + 𝒜ᵀ ≤ 0` of the
papers) is equivalent to `⟪𝒜 x, x⟫ ≤ 0` for all `x`. -/
lemma dissipative_iff_adjoint [CompleteSpace E] (A : E →L[ℝ] E) :
    (∀ x, ⟪(A + ContinuousLinearMap.adjoint A) x, x⟫ ≤ 0) ↔ ∀ x, ⟪A x, x⟫ ≤ 0 := by
  have key : ∀ x, ⟪(A + ContinuousLinearMap.adjoint A) x, x⟫ = 2 * ⟪A x, x⟫ := fun x => by
    rw [add_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm x]
    ring
  constructor
  · intro h x
    have := h x
    rw [key] at this
    linarith
  · intro h x
    rw [key]
    linarith [h x]

variable {F : ℝ → E → E}

/-- **Every BUG substep is norm-nonincreasing for dissipative fields.**  The K-step
(`P = Q₀`), the L-step (`P = P₀`) and the Galerkin S-step (`P = P₁ Q₁`) are Galerkin ODEs
`y' = P F(t, y)` started in `range P`; if `⟪F(t, x), x⟫ ≤ 0` on `range P` then
`‖y(t)‖ ≤ ‖y(a)‖`.  This is a restatement of `ODESolution.galerkin_norm_le'` under the name
used for the BUG substeps. -/
theorem galerkin_substep_norm_le_of_dissipative {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {y : ℝ → E} {a b : ℝ} (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) (hF : ∀ t x, P x = x → ⟪F t x, x⟫ ≤ 0) :
    ∀ t ∈ Icc a b, ‖y t‖ ≤ ‖y a‖ :=
  hy.galerkin_norm_le' hP h0 hF

/-- **`L²`-stability of the BUG integrator for dissipative problems** (no step-size
restriction).  If the Galerkin S-step `YS' = P₁ Q₁ F(t, YS)` starts at `YS(t₀) = P₁ Q₁ Y₀` and
`⟪F(t, x), x⟫ ≤ 0` on `range (P₁ Q₁)`, then the BUG approximation satisfies
`‖YS(t₁)‖ ≤ ‖Y₀‖`, for any bases `P₁, Q₁` (in particular those computed by the K- and L-steps,
which are themselves norm-nonincreasing by `galerkin_substep_norm_le_of_dissipative`). -/
theorem bug_norm_le_of_dissipative {P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₁ : IsOrthProj Q₁) (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) {YS : ℝ → E} {t₀ t₁ : ℝ}
    (ht : t₀ ≤ t₁) (hYS : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁) {Y₀ : E}
    (h0 : YS t₀ = P₁ (Q₁ Y₀)) (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ ≤ 0) :
    ‖YS t₁‖ ≤ ‖Y₀‖ := by
  have hP := hP₁.mul hQ₁ hc
  have hYS' : ODESolution (fun t x => (P₁ * Q₁) (F t x)) YS t₀ t₁ := hYS
  have hr : (P₁ * Q₁) (YS t₀) = YS t₀ := by rw [h0]; exact hP.idem Y₀
  calc ‖YS t₁‖ ≤ ‖YS t₀‖ := hYS'.galerkin_norm_le' hP hr hF t₁ ⟨ht, le_rfl⟩
    _ = ‖(P₁ * Q₁) Y₀‖ := by rw [h0]; rfl
    _ ≤ ‖Y₀‖ := hP.norm_le Y₀

/-- `L²`-stability of the BUG integrator for a linear dissipative operator `𝒜`
(`⟪𝒜 x, x⟫ ≤ 0`, equivalently `𝒜 + 𝒜ᵀ ≤ 0` by `dissipative_iff_adjoint`). -/
theorem bug_norm_le_of_dissipative_linear {A : E →L[ℝ] E} (hA : ∀ x, ⟪A x, x⟫ ≤ 0)
    {P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) {YS : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hYS : ODESolution (fun _ x => P₁ (Q₁ (A x))) YS t₀ t₁) {Y₀ : E}
    (h0 : YS t₀ = P₁ (Q₁ Y₀)) : ‖YS t₁‖ ≤ ‖Y₀‖ :=
  bug_norm_le_of_dissipative (F := fun _ x => A x) hP₁ hQ₁ hc ht hYS h0 fun _ x _ => hA x

/-- **`L²`-stability of the augmented (rank-adaptive) BUG integrator for dissipative problems**
(cf. Ceruti–Kusch–Lubich, arXiv 2104.05247, Thm 4, dissipative version): the Galerkin step starts
at `Y₀ ∈ range P` (the augmented basis contains the old one) and is followed by a
norm-nonincreasing truncation `‖Y₁‖ ≤ ‖YS(t₁)‖`. -/
theorem augmentedBug_norm_le_of_dissipative {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {YS : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hYS : ODESolution (fun t x => P (F t x)) YS t₀ t₁)
    (h0 : P (YS t₀) = YS t₀) (hF : ∀ t x, P x = x → ⟪F t x, x⟫ ≤ 0) {Y₁ : E}
    (htr : ‖Y₁‖ ≤ ‖YS t₁‖) : ‖Y₁‖ ≤ ‖YS t₀‖ :=
  htr.trans (hYS.galerkin_norm_le' hP h0 hF t₁ ⟨ht, le_rfl⟩)

end Dissipative

/-! ### Energy estimates and exponential bounds -/

section Exponential

/-- **Energy estimate ⇒ norm bound.**  If `y' = v` on `[a, b]` and `⟪v(t), y(t)⟫ ≤ ℓ ‖y(t)‖²`
(for any real `ℓ`), then `‖y(t)‖ ≤ exp(ℓ (t - a)) ‖y(a)‖`. -/
theorem norm_le_exp_of_inner_deriv_le {y v : ℝ → E} {a b ℓ : ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (v t) (Ici t) t)
    (hv : ∀ t ∈ Ico a b, ⟪v t, y t⟫ ≤ ℓ * ‖y t‖ ^ 2) :
    ∀ t ∈ Icc a b, ‖y t‖ ≤ Real.exp (ℓ * (t - a)) * ‖y a‖ := by
  set g : ℝ → ℝ := fun s => Real.exp (-(2 * ℓ) * (s - a)) * ‖y s‖ ^ 2 with hg
  have hgc : ContinuousOn g (Icc a b) :=
    (Continuous.continuousOn (by fun_prop)).mul (hyc.norm.pow 2)
  have hgd : ∀ t ∈ Ico a b, HasDerivWithinAt g
      (Real.exp (-(2 * ℓ) * (t - a)) * (-(2 * ℓ)) * ‖y t‖ ^ 2 +
        Real.exp (-(2 * ℓ) * (t - a)) * (2 * ⟪y t, v t⟫)) (Ici t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => -(2 * ℓ) * (s - a)) (-(2 * ℓ)) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (-(2 * ℓ))
    exact h1.exp.hasDerivWithinAt.mul (hy t ht).norm_sq
  have hle := image_le_of_deriv_right_le_deriv_boundary hgc hgd (B := fun _ => g a)
    (B' := fun _ => 0) le_rfl continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _)
    fun t ht => by
      have hexp := Real.exp_pos (-(2 * ℓ) * (t - a))
      have hi : ⟪y t, v t⟫ ≤ ℓ * ‖y t‖ ^ 2 := by rw [real_inner_comm]; exact hv t ht
      nlinarith [mul_le_mul_of_nonneg_left hi hexp.le]
  intro t ht
  have h1 : g t ≤ ‖y a‖ ^ 2 := by simpa [hg] using hle ht
  have h2 : ‖y t‖ ^ 2 = Real.exp (2 * ℓ * (t - a)) * g t := by
    simp only [hg, ← mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  have h3 : Real.exp (2 * ℓ * (t - a)) = Real.exp (ℓ * (t - a)) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h4 : ‖y t‖ ^ 2 ≤ (Real.exp (ℓ * (t - a)) * ‖y a‖) ^ 2 := by
    rw [h2, mul_pow, ← h3]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h4

/-- **Exponential norm bound for Galerkin solutions.**  If `⟪F(t, x), x⟫ ≤ ℓ ‖x‖²` on `range P`
and `y(a) ∈ range P`, the Galerkin solution of `y' = P F(t, y)` satisfies
`‖y(t)‖ ≤ exp(ℓ (t - a)) ‖y(a)‖`.

For `ℓ = 0` this is the norm-nonincreasing consequence of the continuous energy stability of the
DLRA micro–macro scheme (Einkemmer–Hu–Kusch, arXiv 2212.12012, Theorem 5.1, abstract form, with
`‖·‖²` the energy `‖ρ‖² + ε²‖g‖²`).  This consequence drops the dissipation term
`-(σ₀/ε²)‖gˢ‖²` of Theorem 5.1, which `galerkin_norm_sq_add_integral_le` keeps.  For the
micro–macro system no bound with `ℓ < 0` holds.  Scattering damps only the microscopic part `g`,
and `⟪F x, x⟫ = 0` for `x = (ρ, 0)`; for instance, a constant `ρ` with periodic boundary
conditions is a steady state.  The case `ℓ < 0` applies to problems damped in every component,
and `ℓ > 0` gives the usual exponential growth bound. -/
theorem galerkin_norm_le_exp {P : E →L[ℝ] E} (hP : IsOrthProj P) {F : ℝ → E → E}
    {y : ℝ → E} {a b ℓ : ℝ} (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) (hF : ∀ t x, P x = x → ⟪F t x, x⟫ ≤ ℓ * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b, ‖y t‖ ≤ Real.exp (ℓ * (t - a)) * ‖y a‖ := by
  refine norm_le_exp_of_inner_deriv_le hy.cont hy.deriv fun t ht => ?_
  have hr := hy.galerkin_mem_range hP h0 t (Ico_subset_Icc_self ht)
  change ⟪P (F t (y t)), y t⟫ ≤ _
  rw [hP.inner_apply_left_of_mem _ hr]
  exact hF t _ hr

/-- **Energy dissipation of Galerkin solutions** (Einkemmer–Hu–Kusch, arXiv 2212.12012,
Theorem 5.1, abstract integrated form).  Suppose that `⟪F(t, x), x⟫ ≤ -D(x)` for all `x` in the
Galerkin space `range P`, where `D` is a continuous dissipation functional, and that
`y(a) ∈ range P`.  Then the Galerkin solution of `y' = P F(t, y)` satisfies
`‖y(t)‖² + 2 ∫ₐᵗ D(y(s)) ds ≤ ‖y(a)‖²`.

Theorem 5.1 states the differential form `½ d/dt (‖ρ‖² + ε²‖gˢ‖²) ≤ -(σ₀/ε²)‖gˢ‖²`.
Integrating it gives this statement in the following special case: `E` carries the weighted inner
product with squared norm `‖ρ‖² + ε²‖g‖²`, `P` acts as the identity on `ρ` and as the Galerkin
projector on `g`, and `D(ρ, g) = (σ₀/ε²)‖g‖²` acts on the microscopic part only (compare
`galerkin_norm_le_exp`, which cannot see this dissipation).  The example
`EnergyExamples.fmm_dissipation` shows that a toy micro–macro field satisfies the hypothesis. -/
theorem galerkin_norm_sq_add_integral_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {F : ℝ → E → E}
    {y : ℝ → E} {a b : ℝ} (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) {D : E → ℝ} (hD : Continuous D)
    (hF : ∀ t x, P x = x → ⟪F t x, x⟫ ≤ -D x) :
    ∀ t ∈ Icc a b, ‖y t‖ ^ 2 + 2 * ∫ s in a..t, D (y s) ≤ ‖y a‖ ^ 2 := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  -- extend `D ∘ y` continuously from `[a, b]` to `ℝ`
  set φ : ℝ → ℝ := fun s => D (y (projIcc a b hab s)) with hφ
  have hφc : Continuous φ :=
    hD.comp (hy.cont.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun s => (projIcc a b hab s).2)
  have hφeq : ∀ s ∈ Icc a b, φ s = D (y s) := fun s hs => by
    simp only [hφ, projIcc_of_mem hab hs]
  have hI : ∀ s, HasDerivAt (fun u => ∫ v in a..u, φ v) (φ s) s := fun s =>
    (hφc.integral_hasStrictDerivAt a s).hasDerivAt
  set G : ℝ → ℝ := fun s => ‖y s‖ ^ 2 + 2 * ∫ v in a..s, φ v with hG
  have hGc : ContinuousOn G (Icc a b) :=
    (hy.cont.norm.pow 2).add (continuousOn_const.mul
      (continuous_iff_continuousAt.2 fun s => (hI s).continuousAt).continuousOn)
  have hGd : ∀ s ∈ Ico a b,
      HasDerivWithinAt G (2 * ⟪y s, P (F s (y s))⟫ + 2 * φ s) (Ici s) s := fun s hs =>
    (hy.deriv s hs).norm_sq.add ((hI s).hasDerivWithinAt.const_mul 2)
  have hle := image_le_of_deriv_right_le_deriv_boundary hGc hGd (B := fun _ => ‖y a‖ ^ 2)
    (B' := fun _ => 0) (by simp [hG]) continuousOn_const
    (fun s _ => hasDerivWithinAt_const _ _ _) fun s hs => by
      have hr := hy.galerkin_mem_range hP h0 s (Ico_subset_Icc_self hs)
      have h1 : ⟪y s, P (F s (y s))⟫ = ⟪F s (y s), y s⟫ := by
        rw [real_inner_comm, hP.inner_apply_left_of_mem _ hr]
      rw [h1, hφeq s (Ico_subset_Icc_self hs)]
      linarith [hF s _ hr]
  have hint : ∫ v in a..t, φ v = ∫ v in a..t, D (y v) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact hφeq s ⟨hs.1, hs.2.trans ht.2⟩
  have h := hle ht
  simp only [hG] at h
  rwa [hint] at h

end Exponential

/-! ### The backward S-step of the projector-splitting integrator -/

section BackwardSStep

variable {F : ℝ → E → E}

/-- Along a solution of a backward step `y' = -P F(t, y)` (for the KSL S-step `P = P₁ Q₀`):
`d/dt ‖y‖² = -2 ⟪P F(t, y), y⟫`. -/
theorem hasDerivWithinAt_norm_sq_backward {P : E →L[ℝ] E} {y : ℝ → E} {a b t : ℝ}
    (hy : ODESolution (fun t x => -P (F t x)) y a b) (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun s => ‖y s‖ ^ 2) (-2 * ⟪P (F t (y t)), y t⟫) (Ici t) t := by
  refine (hy.deriv t ht).norm_sq.congr_deriv ?_
  show 2 * ⟪y t, -P (F t (y t))⟫ = _
  rw [inner_neg_right, real_inner_comm]
  ring

/-- A backward step `y' = -P F(t, y)` started in `range P` stays in `range P`. -/
theorem backward_mem_range {P : E →L[ℝ] E} (hP : IsOrthProj P) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun t x => -P (F t x)) y a b) (h0 : P (y a) = y a) :
    ∀ t ∈ Icc a b, P (y t) = y t :=
  range_invariant_of_deriv_mem_range (G := fun t => -F t (y t)) hP hy.cont
    (fun t ht => by rw [map_neg]; exact hy.deriv t ht) h0

/-- **Energy identity for the KSL backward S-step** `YS' = -P₁ Q₀ F(t, YS)`: if `P₁, Q₀`
commute and `YS(t₀) ∈ range (P₁ Q₀)` (as `YS(t₀) = P₁ YK(t₁)` is), then
`d/dt ‖YS‖² = -2 ⟪P₁ Q₀ F(t, YS), YS⟫ = -2 ⟪F(t, YS), YS⟫`.  For a dissipative field this is
nonnegative: the S-step *gains* energy. -/
theorem ksl_sStep_hasDerivWithinAt_norm_sq {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₀ : IsOrthProj Q₀) (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) {YS : ℝ → E} {a b t : ℝ}
    (hYS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS a b) (h0 : P₁ (Q₀ (YS a)) = YS a)
    (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun s => ‖YS s‖ ^ 2) (-2 * ⟪P₁ (Q₀ (F t (YS t))), YS t⟫) (Ici t) t ∧
      ⟪P₁ (Q₀ (F t (YS t))), YS t⟫ = ⟪F t (YS t), YS t⟫ := by
  have hP := hP₁.mul hQ₀ hc
  have hYS' : ODESolution (fun t x => -(P₁ * Q₀) (F t x)) YS a b := hYS
  refine ⟨hasDerivWithinAt_norm_sq_backward hYS' ht, ?_⟩
  have hr := backward_mem_range hP hYS' h0 t (Ico_subset_Icc_self ht)
  exact hP.inner_apply_left_of_mem _ hr

/-- **The backward S-step is anti-dissipative** (the instability mechanism of the
projector-splitting integrator, Kusch–Einkemmer–Ceruti, arXiv 2107.07282, Theorem 1 and
Remark 1): if `⟪F(t, x), x⟫ ≤ 0` on `range P` and `y(a) ∈ range P`, the solution of
`y' = -P F(t, y)` satisfies `‖y(a)‖ ≤ ‖y(t)‖`. -/
theorem ksl_sStep_norm_ge_of_dissipative {P : E →L[ℝ] E} (hP : IsOrthProj P) {y : ℝ → E}
    {a b : ℝ} (hy : ODESolution (fun t x => -P (F t x)) y a b) (h0 : P (y a) = y a)
    (hF : ∀ t x, P x = x → ⟪F t x, x⟫ ≤ 0) : ∀ t ∈ Icc a b, ‖y a‖ ≤ ‖y t‖ := by
  have hle := image_le_of_deriv_right_le_deriv_boundary (f := fun _ => ‖y a‖ ^ 2)
    (f' := fun _ => 0) continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _)
    (B := fun s => ‖y s‖ ^ 2) (B' := fun t => -2 * ⟪P (F t (y t)), y t⟫) le_rfl
    (hy.cont.norm.pow 2) (fun t ht => hasDerivWithinAt_norm_sq_backward hy ht)
    fun t ht => by
      have hr := backward_mem_range hP hy h0 t (Ico_subset_Icc_self ht)
      rw [hP.inner_apply_left_of_mem _ hr]
      linarith [hF t _ hr]
  intro t ht
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hle ht)

/-- **Growth bound for backward steps.**  If `‖F(t, x)‖ ≤ L ‖x‖` and `P` is a contraction, the
solution of `y' = -P F(t, y)` satisfies `‖y(t)‖ ≤ exp(L (t - a)) ‖y(a)‖`. -/
theorem ksl_sStep_norm_le_exp {P : E →L[ℝ] E} (hP : ∀ z, ‖P z‖ ≤ ‖z‖) {L : ℝ}
    (hF : ∀ t x, ‖F t x‖ ≤ L * ‖x‖) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun t x => -P (F t x)) y a b) :
    ∀ t ∈ Icc a b, ‖y t‖ ≤ Real.exp (L * (t - a)) * ‖y a‖ := by
  refine norm_le_exp_of_inner_deriv_le hy.cont hy.deriv fun t _ => ?_
  calc ⟪-P (F t (y t)), y t⟫ ≤ ‖-P (F t (y t))‖ * ‖y t‖ := real_inner_le_norm _ _
    _ ≤ (L * ‖y t‖) * ‖y t‖ := by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_right ((hP _).trans (hF t _)) (norm_nonneg _)
    _ = L * ‖y t‖ ^ 2 := by ring

/-- **Growth bound for the KSL backward S-step of a linear problem**:
`YS' = -P₁ Q₀ 𝒜 YS` gives `‖YS(t)‖ ≤ exp(‖𝒜‖ (t - t₀)) ‖YS(t₀)‖`, i.e.
`‖YS(t₁)‖ ≤ exp(‖𝒜‖ h) ‖YS(t₀)‖`.  This is sharp (`ksl_sStep_growth_example`). -/
theorem ksl_sStep_norm_le_exp_linear {P₁ Q₀ A : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₀ : IsOrthProj Q₀) {YS : ℝ → E} {t₀ t₁ : ℝ}
    (hYS : ODESolution (fun _ x => -P₁ (Q₀ (A x))) YS t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ‖YS t‖ ≤ Real.exp (‖A‖ * (t - t₀)) * ‖YS t₀‖ := by
  have hYS' : ODESolution (fun _ x => -(P₁ * Q₀) (A x)) YS t₀ t₁ := hYS
  exact ksl_sStep_norm_le_exp (F := fun _ x => A x)
    (fun z => (hP₁.norm_le (Q₀ z)).trans (hQ₀.norm_le z)) (fun _ x => A.le_opNorm x) hYS'

/-- **Sharpness of the growth bound** `ksl_sStep_norm_le_exp_linear`.  On `ℝ`, take the
dissipative operator `𝒜 = -1` (`⟪𝒜 x, x⟫ ≤ 0` and `‖𝒜‖ = 1`) and `P₁ = Q₀ = 1`.  Then
`YS(t) = exp(t - a)` solves the backward S-step `YS' = -P₁ Q₀ 𝒜 YS`, in exactly the form required
by `ksl_sStep_norm_le_exp_linear`, and attains its bound:
`‖YS(t)‖ = exp(‖𝒜‖ (t - a)) ‖YS(a)‖`. -/
theorem ksl_sStep_growth_example (a b : ℝ) :
    (∀ x : ℝ, ⟪(-1 : ℝ →L[ℝ] ℝ) x, x⟫ ≤ 0) ∧ ‖(-1 : ℝ →L[ℝ] ℝ)‖ = 1 ∧
      ODESolution (fun _ x => -(1 : ℝ →L[ℝ] ℝ) ((1 : ℝ →L[ℝ] ℝ) ((-1 : ℝ →L[ℝ] ℝ) x)))
        (fun t => Real.exp (t - a)) a b ∧
      ∀ t, ‖Real.exp (t - a)‖ = Real.exp (‖(-1 : ℝ →L[ℝ] ℝ)‖ * (t - a)) * ‖Real.exp (a - a)‖ := by
  have hA : ‖(-1 : ℝ →L[ℝ] ℝ)‖ = 1 := by rw [norm_neg, norm_one]
  refine ⟨fun x => ?_, hA, ⟨fun t _ => ?_, fun t _ => ?_⟩, fun t => ?_⟩
  · simp only [neg_apply, one_apply_eq_self, inner_neg_left,
      real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖x‖]
  · exact (Real.continuous_exp.comp (continuous_id.sub continuous_const)).continuousAt
      |>.continuousWithinAt
  · have h1 : HasDerivAt (fun s => s - a) 1 t := by simpa using (hasDerivAt_id t).sub_const a
    have h2 := h1.exp.hasDerivWithinAt (s := Ici t)
    simpa using h2
  · rw [hA]
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

end BackwardSStep

/-! ### Discrete projector-splitting steps -/

section DiscreteKSL

/-- Explicit Euler K-step of the projector-splitting integrator, `YK' = Q₀ F(YK)`:
`x ↦ x + h Q₀ F(x)`. -/
def kslK (Q₀ : E →L[ℝ] E) (F : E → E) (h : ℝ) (x : E) : E := x + h • Q₀ (F x)

/-- Explicit Euler backward S-step, `YS' = -P₁ Q₀ F(YS)`, started from the projection `P₁ z`
of the K-step result onto the new basis: `z ↦ P₁ z - h P₁ Q₀ F(P₁ z)`. -/
def kslS (P₁ Q₀ : E →L[ℝ] E) (F : E → E) (h : ℝ) (z : E) : E :=
  P₁ z - h • P₁ (Q₀ (F (P₁ z)))

/-- Explicit Euler L-step, `YL' = P₁ F(YL)`: `w ↦ w + h P₁ F(w)`. -/
def kslL (P₁ : E →L[ℝ] E) (F : E → E) (h : ℝ) (w : E) : E := w + h • P₁ (F w)

/-- One explicit Euler step of the projector-splitting (KSL) integrator with the same field `F`
in all three substeps, in full-space form.  For `F` the classical Lax–Friedrichs discretisation
this is arXiv 2107.07282, eq. (28).  For the field `F_LF`, whose numerical diffusion does not
depend on `h`, it is the DtP scheme (3.4)–(3.6) of arXiv 2507.15192.

The definition agrees with the integrator under two preconditions:
* `Q₀ x = x`: the input `x = X⁰ S⁰ W⁰ᵀ` lies in the old co-range;
* `P₁ (kslK Q₀ F h x) = kslK Q₀ F h x`: the new basis `X¹` spans the K-step result, as it does
  when `X¹` comes from a QR factorisation of `K¹`.

These conditions are not built into the definition; the theorems below assume them where they
are needed.  For other inputs the component `(1 - Q₀) x` passes through the K-step unprojected,
and the S-step starts from the projection `P₁` of the K-step result. -/
def kslEulerStep (P₁ Q₀ : E →L[ℝ] E) (F : E → E) (h : ℝ) (x : E) : E :=
  kslL P₁ F h (kslS P₁ Q₀ F h (kslK Q₀ F h x))

/-- One explicit Euler step of the projector-splitting integrator whose K-, S- and L-substeps
use the possibly different (frozen-time) discretisations `FK`, `FS`, `FL`.  Examples are the
schemes (31) and (35) of arXiv 2107.07282, whose S-step uses central differences, resp. a
Lax–Friedrichs stabilisation with the sign flipped, while the K- and L-steps use
Lax–Friedrichs fluxes.  The same preconditions as for `kslEulerStep` apply. -/
def kslSplitStep (P₁ Q₀ : E →L[ℝ] E) (FK FS FL : E → E) (h : ℝ) (x : E) : E :=
  kslL P₁ FL h (kslS P₁ Q₀ FS h (kslK Q₀ FK h x))

/-- `kslEulerStep` is the special case of `kslSplitStep` with one field in all substeps. -/
lemma kslEulerStep_eq_kslSplitStep (P₁ Q₀ : E →L[ℝ] E) (F : E → E) (h : ℝ) (x : E) :
    kslEulerStep P₁ Q₀ F h x = kslSplitStep P₁ Q₀ F F F h x := rfl

/-- The K-step maps `range Q₀` into itself. -/
lemma kslK_mem_range {Q₀ : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀) (F : E → E) (h : ℝ) {x : E}
    (hx : Q₀ x = x) : Q₀ (kslK Q₀ F h x) = kslK Q₀ F h x := by
  rw [kslK, map_add, map_smul, hx, hQ₀.idem]

/-- The S-step lands in `range P₁`. -/
lemma kslS_mem_range_left {P₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (Q₀ : E →L[ℝ] E) (F : E → E)
    (h : ℝ) (z : E) : P₁ (kslS P₁ Q₀ F h z) = kslS P₁ Q₀ F h z := by
  rw [kslS, map_sub, map_smul, hP₁.idem, hP₁.idem]

/-- For commuting `P₁, Q₀`, the S-step maps `range Q₀` into itself. -/
lemma kslS_mem_range_right {P₁ Q₀ : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (F : E → E) (h : ℝ) {z : E} (hz : Q₀ z = z) :
    Q₀ (kslS P₁ Q₀ F h z) = kslS P₁ Q₀ F h z := by
  rw [kslS, map_sub, map_smul, ← hc z, hz, ← hc, hQ₀.idem]

/-- The S-step only sees the projection `P₁ z` of its input. -/
lemma kslS_proj {P₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (Q₀ : E →L[ℝ] E) (F : E → E) (h : ℝ)
    (z : E) : kslS P₁ Q₀ F h (P₁ z) = kslS P₁ Q₀ F h z := by
  simp only [kslS, hP₁.idem]

/-- **Stability of a KSL step from substep amplification factors** (generic composition lemma).
Let `P₁, Q₀` be commuting orthogonal projectors.  Let the K-, S- and L-substeps, discretised
with the possibly different fields `FK, FS, FL`, amplify the norm by at most `γK, γS, γL`
(`γS, γL ≥ 0`) on the inputs that actually occur: `x ∈ range Q₀` for the K-step and
`range P₁ ∩ range Q₀` for the S- and L-steps.  Then for `x ∈ range Q₀` the KSL step amplifies
by at most `γK γS γL`.  No precondition `P₁ (kslK x) = kslK x` is needed, because the S-step
starts from the contraction `P₁ z` of its input.

The proofs of arXiv 2107.07282, Theorems 2–3, have this structure for the schemes (31) and
(35).  Those schemes are instances of `kslSplitStep` and not of `kslEulerStep`, because their
S-step is discretised differently from the K- and L-steps.  In the paper, Fourier analysis
bounds the substeps on inputs of the form `Ex ũ Wᵀ`, and the product `G` of the factors is
`≤ 1` under the respective CFL condition; that analysis is not formalised here.

Restricting the substep bounds to these ranges is essential.  Suppose the bounds were required
on all of `E`.  Then `Q₀ ≠ 1` forces `γK ≥ 1` for every field, because on `ker Q₀` the K-step
only adds an orthogonal increment.  Likewise `P₁ ≠ 1` forces `γL ≥ 1`, and for dissipative
fields `γS ≥ 1` as soon as `range P₁ ∩ range Q₀ ≠ 0` (`kslS_norm_ge_of_dissipative`).  In the
strictly dissipative example `EnergyExamples.ksl_rankOne_unrestricted` no such factors with
`γK γS γL ≤ 1` exist, while `EnergyExamples.ksl_rankOne_stable` certifies stability with the
restricted bounds. -/
theorem kslSplitStep_norm_le {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) {FK FS FL : E → E} {h γK γS γL : ℝ}
    (hγS : 0 ≤ γS) (hγL : 0 ≤ γL)
    (hK : ∀ x, Q₀ x = x → ‖kslK Q₀ FK h x‖ ≤ γK * ‖x‖)
    (hS : ∀ z, P₁ z = z → Q₀ z = z → ‖kslS P₁ Q₀ FS h z‖ ≤ γS * ‖z‖)
    (hL : ∀ w, P₁ w = w → Q₀ w = w → ‖kslL P₁ FL h w‖ ≤ γL * ‖w‖)
    {x : E} (hx : Q₀ x = x) :
    ‖kslSplitStep P₁ Q₀ FK FS FL h x‖ ≤ γK * γS * γL * ‖x‖ := by
  have hz : Q₀ (kslK Q₀ FK h x) = kslK Q₀ FK h x := kslK_mem_range hQ₀ FK h hx
  have hQPz : Q₀ (P₁ (kslK Q₀ FK h x)) = P₁ (kslK Q₀ FK h x) := by rw [← hc, hz]
  have hSb : ‖kslS P₁ Q₀ FS h (kslK Q₀ FK h x)‖ ≤ γS * ‖kslK Q₀ FK h x‖ := by
    rw [← kslS_proj hP₁]
    exact (hS _ (hP₁.idem _) hQPz).trans (mul_le_mul_of_nonneg_left (hP₁.norm_le _) hγS)
  calc ‖kslSplitStep P₁ Q₀ FK FS FL h x‖
        ≤ γL * ‖kslS P₁ Q₀ FS h (kslK Q₀ FK h x)‖ :=
        hL _ (kslS_mem_range_left hP₁ Q₀ FS h _) (kslS_mem_range_right hQ₀ hc FS h hz)
    _ ≤ γL * (γS * ‖kslK Q₀ FK h x‖) := mul_le_mul_of_nonneg_left hSb hγL
    _ ≤ γL * (γS * (γK * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK x hx) hγS) hγL
    _ = γK * γS * γL * ‖x‖ := by ring

/-- `kslSplitStep_norm_le` for the KSL step `kslEulerStep` with one field `F` in all three
substeps (e.g. the discretise-first scheme (28) of arXiv 2107.07282). -/
theorem kslEulerStep_norm_le {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) {F : E → E} {h γK γS γL : ℝ}
    (hγS : 0 ≤ γS) (hγL : 0 ≤ γL)
    (hK : ∀ x, Q₀ x = x → ‖kslK Q₀ F h x‖ ≤ γK * ‖x‖)
    (hS : ∀ z, P₁ z = z → Q₀ z = z → ‖kslS P₁ Q₀ F h z‖ ≤ γS * ‖z‖)
    (hL : ∀ w, P₁ w = w → Q₀ w = w → ‖kslL P₁ F h w‖ ≤ γL * ‖w‖)
    {x : E} (hx : Q₀ x = x) :
    ‖kslEulerStep P₁ Q₀ F h x‖ ≤ γK * γS * γL * ‖x‖ :=
  kslSplitStep_norm_le hP₁ hQ₀ hc hγS hγL hK hS hL hx

/-- **Energy chain through a KSL step** (generic composition lemma with energy functionals).
Suppose that, on the inputs that occur, the K-step maps the energy `𝓔₀` to `𝓔₁`, the S-step
maps `𝓔₁` to `𝓔₂`, and the L-step maps `𝓔₂` to `𝓔₃`.  Then `𝓔₃(step x) ≤ 𝓔₀(x)` for every
`x ∈ range Q₀` whose K-step result lies in the new basis.

This is the structure of the proof of Zhang–Hu, arXiv 2507.15192, Theorem 3.3, for the DtP
scheme (an instance of `kslEulerStep`).  There the S-step is not stable on its own, and the
proof uses the following energies:
* `𝓔₀ = 𝓔₃ = ‖·‖²`;
* `𝓔₁ = ‖·‖² + ν(1 - ν)|·|²_{1,x}`, the mixed `L²–H¹` energy after the K-step (eq. (3.12));
* `𝓔₂ = ‖·‖² - ν(1 - ν)|·|²_{1,x}`, the energy before the L-step (eq. (3.18)).

The S-step estimate `𝓔₂(S z) ≤ 𝓔₁(z)` is the content of Lemma 3.4.  The analytic estimates
for the Lax–Friedrichs discretisation under `ν ≤ 1/3` are not formalised here.  Unlike in the
norm version, the precondition `P₁ (kslK x) = kslK x` is needed, because `𝓔₁` need not
decrease under `P₁`. -/
theorem kslSplitStep_energy_le {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) {FK FS FL : E → E} {h : ℝ} {𝓔₀ 𝓔₁ 𝓔₂ 𝓔₃ : E → ℝ}
    (hK : ∀ x, Q₀ x = x → 𝓔₁ (kslK Q₀ FK h x) ≤ 𝓔₀ x)
    (hS : ∀ z, P₁ z = z → Q₀ z = z → 𝓔₂ (kslS P₁ Q₀ FS h z) ≤ 𝓔₁ z)
    (hL : ∀ w, P₁ w = w → Q₀ w = w → 𝓔₃ (kslL P₁ FL h w) ≤ 𝓔₂ w)
    {x : E} (hx : Q₀ x = x) (hx₁ : P₁ (kslK Q₀ FK h x) = kslK Q₀ FK h x) :
    𝓔₃ (kslSplitStep P₁ Q₀ FK FS FL h x) ≤ 𝓔₀ x := by
  have hz : Q₀ (kslK Q₀ FK h x) = kslK Q₀ FK h x := kslK_mem_range hQ₀ FK h hx
  exact (hL _ (kslS_mem_range_left hP₁ Q₀ FS h _) (kslS_mem_range_right hQ₀ hc FS h hz)).trans
    ((hS _ hx₁ hz).trans (hK x hx))

/-- **Discrete anti-dissipativity of the backward S-step**: for `z` in the range of both `P₁`
and `Q₀` and a field with `⟪F z, z⟫ ≤ 0`, the explicit Euler S-step does not decrease the norm,
`‖z‖ ≤ ‖z - h P₁ Q₀ F(z)‖`, for every `h ≥ 0`.  When discretising first, the S-step inherits the
numerical diffusion of the full scheme with the wrong sign.  Whether this destroys stability
for all step sizes depends on how that diffusion scales with `h`; see `kslEulerStep_smul` and
`kslEulerStep_unstable`. -/
theorem kslS_norm_ge_of_dissipative {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₀ : IsOrthProj Q₀) {F : E → E} {h : ℝ} (hh : 0 ≤ h) {z : E} (hz₁ : P₁ z = z)
    (hz₀ : Q₀ z = z) (hF : ⟪F z, z⟫ ≤ 0) : ‖z‖ ≤ ‖kslS P₁ Q₀ F h z‖ := by
  have hi : ⟪P₁ (Q₀ (F z)), z⟫ = ⟪F z, z⟫ := by
    rw [hP₁.inner_apply_left_of_mem _ hz₁, hQ₀.inner_apply_left_of_mem _ hz₀]
  have h1 : ‖kslS P₁ Q₀ F h z‖ ^ 2 =
      ‖z‖ ^ 2 - 2 * h * ⟪F z, z⟫ + h ^ 2 * ‖P₁ (Q₀ (F z))‖ ^ 2 := by
    rw [kslS, hz₁, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm, hi]
    ring
  have h2 : ‖z‖ ^ 2 ≤ ‖kslS P₁ Q₀ F h z‖ ^ 2 := by
    rw [h1]
    nlinarith [mul_nonneg hh (neg_nonneg.2 hF), sq_nonneg (h * ‖P₁ (Q₀ (F z))‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- **The KSL step for a scalar linear field.**  Let `F = -c·id` and let `x` lie in both the old
and the new basis (`P₁ x = x`, `Q₀ x = x`).  The full explicit Euler step multiplies `x` by
`1 - hc`.  The explicit Euler KSL step multiplies it by `(1 - hc)² (1 + hc)`: the K-step by
`1 - hc`, the backward S-step by `1 + hc`, and the L-step by `1 - hc`.  For `c > 0` and `h ≥ 0`
the full step is stable iff `hc ≤ 2`, while the KSL step is stable iff `hc ≤ (1 + √5)/2`
(`ksl_scalar_amplification_le_one_iff`).  For an `h`-independent dissipative field the
anti-dissipative S-step therefore costs a stricter CFL condition, not stability altogether. -/
theorem kslEulerStep_smul {P₁ Q₀ : E →L[ℝ] E} (c h : ℝ) {x : E} (h₁ : P₁ x = x)
    (h₀ : Q₀ x = x) :
    eulerStep (fun y => -c • y) h x = (1 - h * c) • x ∧
      kslEulerStep P₁ Q₀ (fun y => -c • y) h x = ((1 - h * c) ^ 2 * (1 + h * c)) • x := by
  have hK : kslK Q₀ (fun y => -c • y) h x = (1 - h * c) • x := by
    simp only [kslK, map_smul, h₀]
    module
  have hS : kslS P₁ Q₀ (fun y => -c • y) h ((1 - h * c) • x) =
      ((1 - h * c) * (1 + h * c)) • x := by
    simp only [kslS, map_smul, h₁, h₀]
    module
  have hL : kslL P₁ (fun y => -c • y) h (((1 - h * c) * (1 + h * c)) • x) =
      ((1 - h * c) ^ 2 * (1 + h * c)) • x := by
    simp only [kslL, map_smul, h₁]
    module
  refine ⟨?_, ?_⟩
  · simp only [eulerStep]
    module
  · rw [kslEulerStep, hK, hS, hL]

/-- **CFL condition of the scalar KSL amplification factor**: for `s = hc ≥ 0`,
`(1 - s)² (1 + s) ≤ 1` iff `s ≤ (1 + √5)/2` (the golden ratio).  The full explicit Euler factor
`|1 - s|` is `≤ 1` iff `s ≤ 2`, so the KSL step is unstable exactly for `s ∈ ((1 + √5)/2, 2]`
within the stability region of the full scheme. -/
theorem ksl_scalar_amplification_le_one_iff {s : ℝ} (hs : 0 ≤ s) :
    (1 - s) ^ 2 * (1 + s) ≤ 1 ↔ s ≤ (1 + √5) / 2 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 1 < √5 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have key : (1 - s) ^ 2 * (1 + s) - 1 =
      s * ((s - (1 + √5) / 2) * (s - (1 - √5) / 2)) := by
    linear_combination (s / 4) * h5
  have hpos : 0 < s - (1 - √5) / 2 := by linarith
  constructor
  · intro h
    by_contra hlt
    replace hlt := not_le.1 hlt
    have : 0 < s * ((s - (1 + √5) / 2) * (s - (1 - √5) / 2)) :=
      mul_pos (by linarith) (mul_pos (by linarith) hpos)
    linarith
  · intro h
    have : s * ((s - (1 + √5) / 2) * (s - (1 - √5) / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le)
    linarith

/-- **Instability of the explicit Euler projector-splitting integrator** (abstract form of
Kusch–Einkemmer–Ceruti, arXiv 2107.07282, Theorem 1).  Consider the field `F(y) = -(2/h) y`,
which is dissipative for `h > 0` (the statement holds for every `h ≠ 0`).  Its full explicit
Euler step `x ↦ -x` is norm-preserving; this is the Lax–Friedrichs mode with `cos(ᾱπΔx) = -1`.
For every `x` lying in both the old and the new basis (`P₁ x = x`, `Q₀ x = x`, i.e. the basis
does not change), one KSL step gives `3 x`: the K-step gives `-x`, the backward S-step `-3x`,
and the L-step `3x`.  This is `kslEulerStep_smul` with `hc = 2`.

The field scales like `1/h`, as does the numerical diffusion `∼ Δx²/Δt` of the classical
Lax–Friedrichs scheme.  This is what makes the instability unconditional.  For an
`h`-independent field the same mechanism only gives a stricter CFL condition
(`ksl_scalar_amplification_le_one_iff`).  Correspondingly, Zhang–Hu (arXiv 2507.15192,
Theorem 3.3) prove stability under `ν ≤ 1/3` for a Lax–Friedrichs field whose diffusion does not
depend on `h`, and note that their conclusions differ from arXiv 2107.07282, Theorems 1–2. -/
theorem kslEulerStep_unstable {P₁ Q₀ : E →L[ℝ] E} {h : ℝ} (hh : h ≠ 0) {x : E}
    (h₁ : P₁ x = x) (h₀ : Q₀ x = x) :
    eulerStep (fun y => -(2 / h) • y) h x = -x ∧
      kslEulerStep P₁ Q₀ (fun y => -(2 / h) • y) h x = (3 : ℝ) • x := by
  obtain ⟨hE, hK⟩ := kslEulerStep_smul (P₁ := P₁) (Q₀ := Q₀) (2 / h) h h₁ h₀
  have hc : h * (2 / h) = 2 := by field_simp
  rw [hc] at hE hK
  refine ⟨?_, ?_⟩
  · rw [hE]
    module
  · rw [hK]
    norm_num

/-- The full-norm statement of `kslEulerStep_unstable`: the KSL step multiplies the norm by
`3`, while the full explicit Euler step preserves it. -/
theorem kslEulerStep_unstable_norm {P₁ Q₀ : E →L[ℝ] E} {h : ℝ} (hh : h ≠ 0) {x : E}
    (h₁ : P₁ x = x) (h₀ : Q₀ x = x) :
    ‖eulerStep (fun y => -(2 / h) • y) h x‖ = ‖x‖ ∧
      ‖kslEulerStep P₁ Q₀ (fun y => -(2 / h) • y) h x‖ = 3 * ‖x‖ := by
  obtain ⟨h1, h2⟩ := kslEulerStep_unstable hh h₁ h₀
  rw [h1, h2, norm_neg, norm_smul]
  norm_num

end DiscreteKSL

/-! ### Implicit and hybrid projector-splitting steps -/

section Hybrid

/-- **Backward Euler Galerkin steps are contractive for dissipative fields** (the full-space
statement is arXiv 2507.15192, Theorem 4.1; the Galerkin version is used for the L-step of
Theorem 4.3).  If `v = w + h P F(v)` with `P w = w`, `h ≥ 0` and `⟪F v, v⟫ ≤ 0`, then
`P v = v` and `‖v‖ ≤ ‖w‖`. -/
theorem implicitGalerkin_norm_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {F : E → E} {h : ℝ}
    (hh : 0 ≤ h) {v w : E} (hw : P w = w) (hv : v = w + h • P (F v)) (hF : ⟪F v, v⟫ ≤ 0) :
    P v = v ∧ ‖v‖ ≤ ‖w‖ := by
  have hPv : P v = v := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, hw, hP.idem, ← hv]
  refine ⟨hPv, ?_⟩
  have hw' : w = v - h • P (F v) := by rw [eq_sub_iff_add_eq]; exact hv.symm
  have hi : ⟪w, v⟫ = ‖v‖ ^ 2 - h * ⟪F v, v⟫ := by
    rw [hw', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hP.inner_apply_left_of_mem _ hPv]
  have h1 : ‖v‖ ^ 2 ≤ ‖w‖ * ‖v‖ := by
    have := real_inner_le_norm w v
    nlinarith [mul_nonneg hh (neg_nonneg.2 hF)]
  by_contra hlt
  nlinarith [norm_nonneg w, norm_nonneg v, not_le.1 hlt]

/-- **Unconditional `L²`-stability of the hybrid projector-splitting integrator**
(Zhang–Hu, arXiv 2507.15192, Theorems 4.3–4.4, for an arbitrary dissipative field and arbitrary
bases).  Backward Euler K-step `uK = u + h Q₀ F(uK)`, new basis with `P₁ uK = uK`, forward Euler
(backward-in-time) S-step `uS = uK - h P₁ Q₀ F(uK)`, backward Euler L-step
`uL = uS + h P₁ F(uL)`.  Then the K- and S-steps cancel exactly, `uS = P₁ u`, and
`‖uL‖ ≤ ‖uS‖ ≤ ‖u‖` for every `h ≥ 0`, as soon as `⟪F(uL), uL⟫ ≤ 0`.  The hypotheses are
jointly satisfiable with rank-one projectors `P₁ ≠ Q₀` and a coupling field
(`EnergyExamples.hybridKSL_rankOne`). -/
theorem hybridKSL_norm_le {P₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (Q₀ : E →L[ℝ] E)
    {F : E → E} {h : ℝ} (hh : 0 ≤ h) {u uK uS uL : E} (hK : uK = u + h • Q₀ (F uK))
    (hP₁K : P₁ uK = uK) (hS : uS = uK - h • P₁ (Q₀ (F uK))) (hL : uL = uS + h • P₁ (F uL))
    (hF : ⟪F uL, uL⟫ ≤ 0) : uS = P₁ u ∧ ‖uL‖ ≤ ‖uS‖ ∧ ‖uL‖ ≤ ‖u‖ := by
  have hSu : uS = P₁ u := by
    have hu : u = uK - h • Q₀ (F uK) := by rw [eq_sub_iff_add_eq]; exact hK.symm
    rw [hS, hu, map_sub, map_smul, hP₁K]
  have hPS : P₁ uS = uS := by rw [hSu, hP₁.idem]
  have hLS := (implicitGalerkin_norm_le hP₁ hh hPS hL hF).2
  refine ⟨hSu, hLS, hLS.trans ?_⟩
  rw [hSu]
  exact hP₁.norm_le u

/-- **The all-backward projector-splitting integrator is not unconditionally stable**
(arXiv 2507.15192, Proposition 4.2 with `θ = 1`: amplification `1 / ((1 + ψ)² (1 - ψ))`).  On
`ℝ` with the dissipative field `F(x) = -(9/10) x`, `h = 1` and trivial projectors, backward Euler
in all three substeps (`uK = u + F(uK)`, `uS = uK - F(uS)`, `uL = uS + F(uL)`) maps `u = 1` to
`uL = 1000/361 > 2`, although each full backward Euler step is contractive
(`implicitGalerkin_norm_le` with `P = 1`). -/
theorem allBackwardKSL_unstable :
    let F : ℝ → ℝ := fun x => -(9 / 10) * x
    let u : ℝ := 1
    let uK : ℝ := 10 / 19
    let uS : ℝ := 100 / 19
    let uL : ℝ := 1000 / 361
    uK = u + F uK ∧ uS = uK - F uS ∧ uL = uS + F uL ∧ (∀ x, F x * x ≤ 0) ∧ 2 * |u| < |uL| := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun x => by nlinarith [sq_nonneg x], ?_⟩
  norm_num [abs_of_pos]

end Hybrid

/-! ### Energy stability of IMEX Galerkin steps (arXiv 2212.12012) -/

section IMEX

variable {P : E →L[ℝ] E}

/-- **Discrete energy identity for Galerkin steps.**  If `u ∈ range P` and `v = P (u + h G)`,
then `‖v‖² - ‖u‖² + ‖v - u‖² = 2 h ⟪G, v⟫` — exactly the identity obtained for the full scheme
(`P = 1`) by testing with the new iterate (arXiv 2212.12012, eqs. (3.12)–(3.13) and (5.6)–(5.7):
"this equation is equal to (3.13) when replacing `gⁿ` with `g̃ⁿ`"). -/
theorem galerkin_step_energy_identity (hP : IsOrthProj P) {u v G : E} {h : ℝ}
    (hu : P u = u) (hv : v = P (u + h • G)) :
    ‖v‖ ^ 2 - ‖u‖ ^ 2 + ‖v - u‖ ^ 2 = 2 * h * ⟪G, v⟫ := by
  have hPv : P v = v := by rw [hv, hP.idem]
  have hvu : v - u = h • P G := by rw [hv, map_add, map_smul, hu]; abel
  have h1 : ⟪v - u, v⟫ = h * ⟪G, v⟫ := by
    rw [hvu, real_inner_smul_left, hP.inner_apply_left_of_mem _ hPv]
  have h2 : ⟪v - u, v⟫ = ‖v‖ ^ 2 - ⟪u, v⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, real_inner_comm u v] at *
  nlinarith [h1, h2]

/-- **Energy stability of a Galerkin (IMEX) step under the full-scheme CFL condition.**  If the
energy estimate of the full scheme, `2 h ⟪G, v⟫ ≤ ‖v - u‖²`, holds for the pair `(u, v)`, then the
Galerkin step `v = P (u + h G)` from `u ∈ range P` is norm-nonincreasing. -/
theorem galerkin_imex_norm_le (hP : IsOrthProj P) {u v G : E} {h : ℝ} (hu : P u = u)
    (hv : v = P (u + h • G)) (hcfl : 2 * h * ⟪G, v⟫ ≤ ‖v - u‖ ^ 2) : ‖v‖ ≤ ‖u‖ := by
  have h1 := galerkin_step_energy_identity hP hu hv
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- **Energy stability of the DLRA IMEX scheme** (Einkemmer–Hu–Kusch, arXiv 2212.12012,
Theorem 5.2, abstract form).  Let `Fex` (explicit: streaming, coupling) and `Fim` (implicit:
scattering) be such that the full IMEX scheme satisfies the energy estimate obtained by testing
with the new iterate, `2 h ⟪Fex u + Fim v, v⟫ ≤ ‖v - u‖²` for all `u, v` in the Galerkin space
(this is what the CFL condition `Δt ≤ C (ε Δx + σ₀ Δx²)` guarantees in the paper).  Then the
S-step `v = P (ũ + h (Fex ũ + Fim v))` from `ũ = P u₀` (`S̃ⁿ = X¹ᵀ Xⁿ Sⁿ Vⁿᵀ V¹`) satisfies
`‖v‖ ≤ ‖u₀‖`, under the same CFL condition as the full scheme, for any bases.  The case `P = 1`
is the full-scheme Theorem 3.2. -/
theorem dlra_imex_energy_stable (hP : IsOrthProj P) {Fex Fim : E → E} {h : ℝ}
    (hcfl : ∀ u v, P u = u → P v = v → 2 * h * ⟪Fex u + Fim v, v⟫ ≤ ‖v - u‖ ^ 2)
    {u₀ v : E} (hv : v = P (P u₀ + h • (Fex (P u₀) + Fim v))) : ‖v‖ ≤ ‖u₀‖ := by
  have hu : P (P u₀) = P u₀ := hP.idem u₀
  have hPv : P v = v := by rw [hv, hP.idem]
  exact (galerkin_imex_norm_le hP hu hv (hcfl _ _ hu hPv)).trans (hP.norm_le u₀)

end IMEX

/-! ### Rank-one examples in `ℝ²`

The hypotheses of the main theorems are jointly satisfiable in a genuinely low-rank situation.
The space is `E = ℝ²`, the projectors are rank-one orthogonal projectors `x ↦ ⟪eᵢ, x⟫ eᵢ`
(`≠ 1`), and the field is the dissipative linear field `F(x) = A x` with
`A = [[-1, 1], [-1, -1]]`.  This field couples the two coordinates, so it does not leave the
ranges of the projectors invariant. -/

namespace EnergyExamples

/-- The Euclidean plane `ℝ²`. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The standard basis vectors `e₀, e₁` of `ℝ²`. -/
noncomputable def e (i : Fin 2) : E2 := EuclideanSpace.single i 1

lemma inner_e_self (i : Fin 2) : ⟪e i, e i⟫ = (1 : ℝ) := by
  simp [e]

lemma inner_e01 : ⟪e 0, e 1⟫ = (0 : ℝ) := by
  simp [e, EuclideanSpace.inner_single_left]

lemma inner_e10 : ⟪e 1, e 0⟫ = (0 : ℝ) := by
  simp [e, EuclideanSpace.inner_single_left]

lemma norm_e (i : Fin 2) : ‖e i‖ = 1 := by simp [e]

/-- The rank-one orthogonal projector `x ↦ ⟪eᵢ, x⟫ eᵢ` onto the line spanned by `eᵢ`. -/
noncomputable def lineProj (i : Fin 2) : E2 →L[ℝ] E2 := (innerSL ℝ (e i)).smulRight (e i)

lemma lineProj_apply (i : Fin 2) (x : E2) : lineProj i x = ⟪e i, x⟫ • e i := rfl

lemma isOrthProj_lineProj (i : Fin 2) : IsOrthProj (lineProj i) where
  idem x := by rw [lineProj_apply, lineProj_apply, real_inner_smul_right, inner_e_self, mul_one]
  symm x y := by
    rw [lineProj_apply, lineProj_apply, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (e i) x]
    ring

lemma lineProj_self (i : Fin 2) : lineProj i (e i) = e i := by
  rw [lineProj_apply, inner_e_self, one_smul]

/-- The rank-one projector is not the identity. -/
lemma lineProj_zero_ne_one : lineProj 0 ≠ 1 := by
  intro h
  have h1 : lineProj 0 (e 1) = 0 := by rw [lineProj_apply, inner_e01, zero_smul]
  rw [h, one_apply_eq_self] at h1
  simpa [norm_e] using congrArg norm h1

/-- The coupling dissipative field `F(x) = A x`, `A = [[-1, 1], [-1, -1]]`. -/
noncomputable def Fc (x : E2) : E2 := (⟪e 1, x⟫ - ⟪e 0, x⟫) • e 0 + (-⟪e 0, x⟫ - ⟪e 1, x⟫) • e 1

lemma norm_comb_sq (a b : ℝ) : ‖a • e 0 + b • e 1‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_e_self, inner_e01, inner_e10]
  ring

lemma inner_Fc (x : E2) : ⟪Fc x, x⟫ = -(⟪e 0, x⟫ ^ 2 + ⟪e 1, x⟫ ^ 2) := by
  simp only [Fc, inner_add_left, real_inner_smul_left]
  ring

/-- `F` is dissipative. -/
lemma Fc_dissipative (x : E2) : ⟪Fc x, x⟫ ≤ 0 := by
  rw [inner_Fc]
  nlinarith [sq_nonneg ⟪e 0, x⟫, sq_nonneg ⟪e 1, x⟫]

/-- The abstract CFL condition of `eulerStep_norm_le_of_inner_le` with `β = 1/2`. -/
lemma Fc_cfl (x : E2) : ⟪Fc x, x⟫ ≤ -(1 / 2) * ‖Fc x‖ ^ 2 := by
  rw [inner_Fc, Fc, norm_comb_sq]
  nlinarith [sq_nonneg ⟪e 0, x⟫, sq_nonneg ⟪e 1, x⟫]

lemma eq_smul_e0 {x : E2} (hx : lineProj 0 x = x) : x = ⟪e 0, x⟫ • e 0 := by
  rw [← lineProj_apply, hx]

/-- On the line spanned by `e₀`, the projected field `P₀ F` acts as `-id`. -/
lemma lineProj0_Fc {x : E2} (hx : lineProj 0 x = x) : lineProj 0 (Fc x) = -x := by
  rw [eq_smul_e0 hx]
  simp only [lineProj_apply, Fc, inner_add_right, real_inner_smul_right, inner_e_self,
    inner_e01, inner_e10]
  module

lemma lineProj0_Fc_e1 : lineProj 0 (Fc (e 1)) = e 0 := by
  simp only [lineProj_apply, Fc, inner_add_right, real_inner_smul_right, inner_e_self,
    inner_e01]
  module

/-- `bug_euler_norm_le` with the rank-one left projector `P₁ = P_{e₀}` and the coupling field:
the explicit Euler BUG step is `L²`-stable for `0 ≤ h ≤ 1`. -/
example {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (u₀ : E2) :
    ‖lineProj 0 ((1 : E2 →L[ℝ] E2) (eulerStep Fc h (lineProj 0 ((1 : E2 →L[ℝ] E2) u₀))))‖ ≤
      1 * ‖u₀‖ :=
  bug_euler_norm_le (isOrthProj_lineProj 0) IsOrthProj.one (fun x => by simp) zero_le_one
    (fun x _ => by
      rw [one_mul]
      exact eulerStep_norm_le_of_inner_le hh (by linarith) (Fc_cfl x)) u₀

/-- **`kslEulerStep_norm_le` certifies stability in a rank-one case.**  Take `P₁ = Q₀ = P_{e₀}`,
the coupling field and `h = 1/2`.  On the relevant ranges the substep factors are
`γK = 1/2`, `γS = 3/2` and `γL = 1/2`, so the KSL step is contractive with factor `3/8`.
Without the range restrictions this could not be certified (`ksl_rankOne_unrestricted`). -/
theorem ksl_rankOne_stable {x : E2} (hx : lineProj 0 x = x) :
    ‖kslEulerStep (lineProj 0) (lineProj 0) Fc (1 / 2) x‖ ≤ 1 / 2 * (3 / 2) * (1 / 2) * ‖x‖ := by
  refine kslEulerStep_norm_le (isOrthProj_lineProj 0) (isOrthProj_lineProj 0) (fun _ => rfl)
    (by norm_num) (by norm_num) ?_ ?_ ?_ hx
  · intro y hy
    rw [kslK, lineProj0_Fc hy, show y + (1 / 2 : ℝ) • -y = (1 / 2 : ℝ) • y by module, norm_smul]
    norm_num
  · intro z hz _
    rw [kslS, hz, lineProj0_Fc hz, map_neg, hz,
      show z - (1 / 2 : ℝ) • -z = (3 / 2 : ℝ) • z by module, norm_smul]
    norm_num
  · intro w hw _
    rw [kslL, lineProj0_Fc hw, show w + (1 / 2 : ℝ) • -w = (1 / 2 : ℝ) • w by module, norm_smul]
    norm_num

/-- **The range restrictions in `kslSplitStep_norm_le` are essential.**  In the setting of
`ksl_rankOne_stable`, substep bounds required on all of `E` force `γK ≥ 1` (the K-step maps `e₁`
to `e₁ + e₀/2`), `γS ≥ 3/2` and `γL ≥ 1`.  So they never give a product `γK γS γL ≤ 1`, although
the KSL step is contractive on `range Q₀`. -/
theorem ksl_rankOne_unrestricted :
    ¬ ∃ γK γS γL : ℝ, 0 ≤ γS ∧ 0 ≤ γL ∧ γK * γS * γL ≤ 1 ∧
      (∀ x, ‖kslK (lineProj 0) Fc (1 / 2) x‖ ≤ γK * ‖x‖) ∧
      (∀ z, ‖kslS (lineProj 0) (lineProj 0) Fc (1 / 2) z‖ ≤ γS * ‖z‖) ∧
      (∀ w, ‖kslL (lineProj 0) Fc (1 / 2) w‖ ≤ γL * ‖w‖) := by
  rintro ⟨γK, γS, γL, hS0, hL0, hprod, hK, hS, hL⟩
  have hv : ‖e 1 + (1 / 2 : ℝ) • e 0‖ = √5 / 2 := by
    have h := norm_comb_sq (1 / 2) 1
    rw [show (1 / 2 : ℝ) • e 0 + (1 : ℝ) • e 1 = e 1 + (1 / 2 : ℝ) • e 0 by module] at h
    rw [← Real.sqrt_sq (norm_nonneg _), h, show (1 / 2 : ℝ) ^ 2 + 1 ^ 2 = 5 / 2 ^ 2 by norm_num,
      Real.sqrt_div' _ (by norm_num), Real.sqrt_sq (by norm_num)]
  have h5 : 1 ≤ √5 / 2 := by
    rw [le_div_iff₀ (by norm_num), show (1 : ℝ) * 2 = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have k := hK (e 1)
  rw [kslK, lineProj0_Fc_e1, hv, norm_e, mul_one] at k
  have l := hL (e 1)
  rw [kslL, lineProj0_Fc_e1, hv, norm_e, mul_one] at l
  have s := hS (e 0)
  rw [kslS, lineProj_self, lineProj0_Fc (lineProj_self 0), map_neg, lineProj_self,
    show e 0 - (1 / 2 : ℝ) • -e 0 = (3 / 2 : ℝ) • e 0 by module, norm_smul, norm_e] at s
  norm_num at s
  have hK1 : 1 ≤ γK := h5.trans k
  have hL1 : 1 ≤ γL := h5.trans l
  have h1 : 3 / 2 ≤ γK * γS := by nlinarith
  nlinarith

/-- `kslEulerStep_unstable` with the rank-one projectors `P₁ = Q₀ = P_{e₀} ≠ 1`: the KSL step
triples `e₀`. -/
example {h : ℝ} (hh : h ≠ 0) :
    ‖kslEulerStep (lineProj 0) (lineProj 0) (fun y => -(2 / h) • y) h (e 0)‖ = 3 * ‖e 0‖ ∧
      lineProj 0 ≠ 1 :=
  ⟨(kslEulerStep_unstable_norm hh (lineProj_self 0) (lineProj_self 0)).2, lineProj_zero_ne_one⟩

/-- **`hybridKSL_norm_le` in a rank-one case with a basis change.**  Take
`Q₀ = P_{e₀}` (old co-range), `P₁ = P_{e₁}` (new basis), the coupling field and `h = 1`.
Then `u = e₁ - e₀` gives `uK = e₁`, `uS = e₁` and `uL = e₁/2`. -/
theorem hybridKSL_rankOne :
    e 1 = lineProj 1 (e 1 - e 0) ∧ ‖(1 / 2 : ℝ) • e 1‖ ≤ ‖e 1‖ ∧
      ‖(1 / 2 : ℝ) • e 1‖ ≤ ‖e 1 - e 0‖ := by
  have hF1 := lineProj0_Fc_e1
  have h10 : lineProj 1 (e 0) = 0 := by rw [lineProj_apply, inner_e10, zero_smul]
  refine hybridKSL_norm_le (isOrthProj_lineProj 1) (lineProj 0) (F := Fc) (h := 1) zero_le_one
    ?_ (lineProj_self 1) ?_ ?_ (Fc_dissipative _)
  · rw [hF1]
    module
  · rw [hF1, h10]
    module
  · simp only [lineProj_apply, Fc, inner_add_right, real_inner_smul_right, inner_e_self,
      inner_e01, inner_e10]
    module

/-- Toy micro–macro field `(ρ, g) ↦ (-g, ρ - g)` (transport coupling plus scattering acting on
`g` only). -/
noncomputable def Fmm (x : E2) : E2 := (-⟪e 1, x⟫) • e 0 + (⟪e 0, x⟫ - ⟪e 1, x⟫) • e 1

/-- The toy micro–macro field satisfies the hypotheses of `galerkin_norm_sq_add_integral_le` with
the continuous dissipation `D(ρ, g) = g²`.  It satisfies no bound `⟪F x, x⟫ ≤ ℓ ‖x‖²` with
`ℓ < 0`: take `x = (1, 0)`. -/
theorem fmm_dissipation :
    Continuous (fun x : E2 => ⟪e 1, x⟫ ^ 2) ∧ (∀ x, ⟪Fmm x, x⟫ ≤ -(⟪e 1, x⟫ ^ 2)) ∧
      ∀ ℓ : ℝ, ℓ < 0 → ¬ ⟪Fmm (e 0), e 0⟫ ≤ ℓ * ‖e 0‖ ^ 2 := by
  refine ⟨by fun_prop, fun x => le_of_eq ?_, fun ℓ hℓ hle => ?_⟩
  · simp only [Fmm, inner_add_left, real_inner_smul_left]
    ring
  · have h : ⟪Fmm (e 0), e 0⟫ = 0 := by
      simp only [Fmm, inner_add_left, real_inner_smul_left, inner_e_self, inner_e10]
      ring
    rw [h, norm_e] at hle
    linarith

end EnergyExamples

end LeanDLRA
