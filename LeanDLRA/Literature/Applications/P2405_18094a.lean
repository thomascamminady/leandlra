import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import LeanDLRA.Foundations.ODE

/-!
# Results of arXiv 2405.18094 (Dupuy, Ehrlacher, Guillot): space-time least squares

The paper writes the Schrödinger evolution `(i∂_t − H − B(t)) u* = f`, `u*(0) = u₀` (1.1) on a
Hilbert space `H`, with `H = H₀ + A`, as the minimisation of a least-squares functional on
`H¹(I, H)` (the interaction picture `v = e^{itH₀} u`), and proves that the functional is
equivalent to the squared `H¹` distance to the solution with constants polynomial in `T`. This
module formalizes these results for a **bounded self-adjoint perturbation** `A` (a special case of
the paper's assumption (A), see its Remark 3.6 (i)), on a complex Hilbert space `E`.

## Setting and deviations from the paper

* `E` is any complex Hilbert space (the paper: separable). `A` and `B(t)` are bounded and
  self-adjoint; `B` is strongly continuous on `[0, T]` with `‖B t‖ ≤ M` (`IsBoundedPotential`;
  the paper: strongly continuous on `(0, T)`, and its proofs use `M = sup ‖B(t)‖`).
* `H₀`: in Theorem 3.7 and Proposition 3.20, `H₀` is bounded self-adjoint, but all constants
  depend only on `‖A‖` and `M`, never on `H₀` or `T`. In Corollary 3.8, `H₀` enters only through
  its propagator, and `e^{−itH₀}` is replaced by an arbitrary strongly continuous unitary family
  `U` (`IsUnitaryPropagator`), which covers unbounded `H₀` via Stone's theorem; for bounded `H₀`
  the propagator is `freeProp H₀ t = exp(t • (−i H₀))`.
* Function spaces: Mathlib has no Bochner–Sobolev spaces. Curves are `C¹` functions `ℝ → E`
  (only `[0, T]` matters), and the norms are the paper's: `xNorm` (2.5)/(3.5), `h1Norm`,
  `yNorm` (3.27)/(3.29), and the functional `leastSquaresF` (1.8). `C¹` curves form a dense
  subspace of `X_H` and `H¹(I, H)` (Proposition 2.7), on which the stated inequalities between
  continuous norms are equivalent to the paper's; formally, they are stated for `C¹` curves.
* Proof route: Proposition 3.13 (Kato smoothing) is replaced by the operator-norm bound
  `‖K − G‖ ≤ L`, and the continuity estimate by the energy estimate
  `sq_norm_le_of_selfAdjoint`. One perturbation lemma (`xNorm_equiv_of_norm_sub_le`) gives
  Theorem 3.7, Proposition 3.20 and Corollary 3.8, with `C = √(2 + 8 L²)`, `α = 1/C`,
  `L = ‖A‖ + M`. In this bounded case the lower bounds hold with `(1 + T)⁻¹` also for `B ≠ 0`
  (the paper: `(1 + T)⁻²`); the theorems are stated for every exponent `γ ≥ 1`.

## Main results

* `xNorm_add_equiv`, `xNorm_add_timeDep_equiv`, `eqOn_zero_of_xNorm_add_timeDep_eq_zero`:
  Theorem 3.7 (i) and (ii), (3.4) and (3.6), and definiteness of `N`.
* `leastSquaresF_eq_xNormSq`, `leastSquaresF_normEquiv`, `leastSquaresF_isUniqueMin`:
  Corollary 3.8 (`F` is quadratic, estimate (3.7), `v*` is the unique minimiser), for any unitary
  propagator; `leastSquaresF_normEquiv_of_solution` and `leastSquaresF_freeProp_eq` state it in
  the paper's form for bounded `H₀`, with `u*` a solution of (1.1).
* `remark311_ceaType_h1`: Remark 3.11 (Céa-type quasi-optimality of constrained minimisers),
  unconditional. `remark311_ceaType` and `ceaType_of_normEquiv` are the abstract versions that
  take (3.7) as a hypothesis; `ceaType_of_equiv` is the common core.
* `yNorm_add_timeDep_equiv`, `eqOn_zero_of_yNorm_eq_zero`: Proposition 3.20.
* `h1Norm_star_freeProp_apply`, `norm_le_sqrt_two_mul_xNorm`, `eqOn_of_classical_solution`:
  Proposition 2.4 for bounded `H` and `C¹` curves (the isometry `u ↦ e^{itH} u` of (2.6)/(2.9),
  the estimate (2.7) with the paper's constant `√2`, uniqueness of solutions).
* `integral_inner_resid_eq`: the integration by parts formula (2.14) of Proposition 2.7.
* `dualLeastSquares_printed_pos`, `dualLeastSquares_upper_bound_fails`: Corollary 3.23 as printed
  fails for `B ≠ 0` ((3.36) omits `B(t)`).
* `weaklyClosed_timeSlice`: abstract core of Proposition 4.1.

## Core definitions used

`LeanDLRA.ODESolution` (`odeSolution_of_classical`: a classical solution of (1.1) is a core ODE
solution). The local definitions (`xNorm`, `h1Norm`, `yNorm`, `leastSquaresF`, `freeProp`,
`IsUnitaryPropagator`, `IsBoundedPotential`) are the paper's space-time norms and operator
families, which have no counterpart in the core.

## Not formalized

* The paper's unbounded perturbations (`A` closed symmetric and `H₀`-bounded with (3.3), e.g.
  Coulomb potentials): Kato smoothing (Lemma 3.1, Propositions 3.2, 3.13), Kato–Rellich
  (Lemma 3.5), Theorem 3.12 and Section 3.4.
* Proposition 2.4 beyond the parts above (Hilbert structure of `X_H`, existence of the solution,
  the Duhamel formula (2.8)), the density part of Proposition 2.7, Remark 3.10 (3.8).
* Lemma 3.21, Proposition 3.22 and Corollary 3.23 (dual formulation on `L²(I, H)`). As printed,
  (3.36) contains `A` but not `B(t)`, while `u*` solves (1.1) with `B`; for `B ≠ 0` the upper bound
  of (3.37) then fails at `u = u*` (`dualLeastSquares_printed_pos`,
  `dualLeastSquares_upper_bound_fails`). The corrected statement, with `A + B(s)` in (3.36), is
  not formalized.
* Existence of a minimiser of `F` over `H¹(I, Σ)` (after Proposition 4.1): it needs weak
  compactness in `H¹(I, H)`, which the `C¹` setting does not provide.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace LeanDLRA.Literature.P2405_18094

/-! ### Abstract Céa-type estimates and Proposition 4.1 -/

/-- **Céa-type quasi-optimality from a two-sided bound (abstract core of Remark 3.11 of
arXiv 2405.18094).**

Let `F, d : V → ℝ` on an arbitrary type `V` (`d v` plays the role of the error `‖v − v*‖`). If
`c₁ d v ≤ √(F v) ≤ c₂ d v` on `S`, with `c₁ > 0`, `c₂ ≥ 0`, and `vt ∈ S` minimises `F` over `S`,
then `d vt ≤ (c₂ / c₁) d v` for all `v ∈ S`, and `d vt ≤ (c₂ / c₁) inf_{v ∈ S} d v`. No norm is
needed, so this applies both to normed spaces (`ceaType_of_normEquiv`) and to the `H¹` error
of `C¹` curves (`remark311_ceaType_h1`). -/
theorem ceaType_of_equiv {V : Type*} (F d : V → ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    {S : Set V} (hlow : ∀ v ∈ S, c₁ * d v ≤ Real.sqrt (F v))
    (hup : ∀ v ∈ S, Real.sqrt (F v) ≤ c₂ * d v) {vt : V} (hvt : vt ∈ S)
    (hmin : ∀ v ∈ S, F vt ≤ F v) :
    (∀ v ∈ S, d vt ≤ c₂ / c₁ * d v) ∧ d vt ≤ c₂ / c₁ * sInf (d '' S) := by
  have hpt : ∀ v ∈ S, c₁ * d vt ≤ c₂ * d v := fun v hv =>
    (hlow vt hvt).trans ((Real.sqrt_le_sqrt (hmin v hv)).trans (hup v hv))
  have hpt' : ∀ v ∈ S, d vt ≤ c₂ / c₁ * d v := by
    intro v hv
    have h := hpt v hv
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
    linarith [mul_comm (d vt) c₁]
  refine ⟨hpt', ?_⟩
  have hk : 0 ≤ c₂ / c₁ := div_nonneg hc₂ hc₁.le
  rcases hk.eq_or_lt with h0 | hpos
  · have h := hpt' vt hvt
    rw [← h0, zero_mul] at h
    rw [← h0, zero_mul]
    exact h
  · have hs : d vt / (c₂ / c₁) ≤ sInf (d '' S) := by
      apply le_csInf (Set.Nonempty.image _ ⟨vt, hvt⟩)
      rintro _ ⟨v, hv, rfl⟩
      rw [div_le_iff₀ hpos, mul_comm]
      exact hpt' v hv
    have h := (div_le_iff₀ hpos).1 hs
    rw [mul_comm]
    exact h

/-- **Abstract core of Remark 3.11 (arXiv 2405.18094), Céa-type quasi-optimality.**

Let `F : V → ℝ` and `v*` be a reference point in a normed space `V`. Assume the two-sided
bounds `c₁ ‖v − v*‖ ≤ √(F v) ≤ c₂ ‖v − v*‖` for all `v`, with `c₁ > 0` and `c₂ ≥ 0`. Let
`ṽ ∈ S` minimise `F` over `S`. Then for every `v ∈ S`,
`‖ṽ − v*‖ ≤ (c₂ / c₁) ‖v − v*‖`, and `‖ṽ − v*‖ ≤ (c₂ / c₁) inf_{v ∈ S} ‖v − v*‖`.

This is the abstract argument behind the paper's remark that a constrained minimiser of
`F` over `H¹(I, Σ)` is quasi-optimal in `H¹(I, Σ)`. The paper's norm equivalence (3.7) for the
least-squares functional is an input here, not a consequence of this theorem; it is proved in
`leastSquaresF_normEquiv` (bounded perturbations). -/
theorem ceaType_of_normEquiv {V : Type*} [NormedAddCommGroup V] (F : V → ℝ)
    (vStar : V) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hlow : ∀ v : V, c₁ * ‖v - vStar‖ ≤ Real.sqrt (F v))
    (hup : ∀ v : V, Real.sqrt (F v) ≤ c₂ * ‖v - vStar‖)
    {S : Set V} {vt : V} (hvt : vt ∈ S) (hmin : ∀ v ∈ S, F vt ≤ F v) :
    (∀ v ∈ S, ‖vt - vStar‖ ≤ c₂ / c₁ * ‖v - vStar‖) ∧
      ‖vt - vStar‖ ≤ c₂ / c₁ * sInf ((fun v => ‖v - vStar‖) '' S) :=
  ceaType_of_equiv F (fun v => ‖v - vStar‖) hc₁ hc₂ (fun v _ => hlow v) (fun v _ => hup v) hvt
    hmin

/-- **Remark 3.11 of arXiv 2405.18094 with the paper's constants.**

Assume the paper's two-sided bound (3.7) for `F` (with `γ ∈ ℕ`, `α > 0`, `C ≥ 0`, `T ≥ 0`):
`α/(1+T)^γ ‖v − v*‖ ≤ √(F v) ≤ C(1+T) ‖v − v*‖`. Then a minimiser `ṽ` of `F` over `S` satisfies
`‖ṽ − v*‖ ≤ (C(1+T)^(γ+1)/α) ‖v − v*‖` for all `v ∈ S`, i.e. the constant `C(1+T)^(γ+1)/α`
of Remark 3.11.

Caveat: the bound (3.7) is a hypothesis here, so this abstract version is conditional on
(3.7). In the bounded-perturbation setting (3.7) is proved (`leastSquaresF_normEquiv`, Corollary
3.8), and `remark311_ceaType_h1` is the corresponding unconditional statement. -/
theorem remark311_ceaType {V : Type*} [NormedAddCommGroup V] (F : V → ℝ) (vStar : V)
    {α C T : ℝ} {γ : ℕ} (hα : 0 < α) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hlow : ∀ v : V, α / (1 + T) ^ γ * ‖v - vStar‖ ≤ Real.sqrt (F v))
    (hup : ∀ v : V, Real.sqrt (F v) ≤ C * (1 + T) * ‖v - vStar‖)
    {S : Set V} {vt : V} (hvt : vt ∈ S) (hmin : ∀ v ∈ S, F vt ≤ F v) :
    ∀ v ∈ S, ‖vt - vStar‖ ≤ C * (1 + T) ^ (γ + 1) / α * ‖v - vStar‖ := by
  have h1T : (0 : ℝ) < 1 + T := by linarith
  have hc₁ : 0 < α / (1 + T) ^ γ := div_pos hα (pow_pos h1T _)
  have hc₂ : 0 ≤ C * (1 + T) := mul_nonneg hC h1T.le
  intro v hv
  have h := (ceaType_of_normEquiv F vStar hc₁ hc₂ hlow hup hvt hmin).1 v hv
  have e : C * (1 + T) / (α / (1 + T) ^ γ) = C * (1 + T) ^ (γ + 1) / α := by
    field_simp
    ring
  rw [e] at h
  exact h

/-- A concrete instance of the hypotheses of `ceaType_of_normEquiv`: on `ℝ` with
`F v = (v − 1)²`, `v* = 1` and `c₁ = c₂ = 1`, the square root of `F` is `|v − 1|`. -/
example : ∀ v : ℝ, 1 * ‖v - 1‖ ≤ Real.sqrt ((v - 1) ^ 2) := by
  intro v
  rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, one_mul]

/-- **Proposition 4.1 of arXiv 2405.18094 (abstract core): weak closedness of time slices.**

Let `W` be a normed space over `𝕜` (the paper takes `W = H¹(I, H)`, not in Mathlib), and let
`ev t : W →L[𝕜] H` be continuous linear maps (the paper's evaluations `v ↦ v(t)`, for
`t ∈ I`). If `K ⊂ H` (the paper's `Σ`) is weakly closed, then
`{v ∈ W : v(t) ∈ K for all t ∈ I}` is closed in the
weak topology of `W`. The statement and the proof use only `IsClosed` in the weak topologies
`WeakSpace 𝕜 W` and `WeakSpace 𝕜 H`, so the Hilbert structure of the paper is not needed. -/
theorem weaklyClosed_timeSlice {𝕜 W H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (ev : ℝ → W →L[𝕜] H) (I : Set ℝ) {K : Set (WeakSpace 𝕜 H)} (hK : IsClosed K) :
    IsClosed {v : WeakSpace 𝕜 W | ∀ t ∈ I, WeakSpace.map (ev t) v ∈ K} := by
  have e : {v : WeakSpace 𝕜 W | ∀ t ∈ I, WeakSpace.map (ev t) v ∈ K} =
      ⋂ t ∈ I, (WeakSpace.map (ev t)) ⁻¹' K := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [e]
  exact isClosed_biInter fun t _ => hK.preimage (WeakSpace.map (ev t)).continuous

section SpaceTime

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ### Definitions -/

/-- Square of the norm (2.5) of arXiv 2405.18094 on the space `X_G`, for a possibly
time-dependent Hamiltonian `G`: `‖u 0‖² + T ∫₀ᵀ ‖i u'(t) − G(t) u(t)‖² dt`. For `G = H` constant
this is `‖u‖²_{X_H}` (2.5); for `G(t) = H + B(t)` it is the paper's `N(u)²` (2.10)/(3.5); for
`G = 0` it is the `H¹(I, H)` norm used in Corollary 3.8 (`h1Norm_eq_xNorm_zero`). Curves are
functions `ℝ → E` and only their values on `[0, T]` enter. -/
noncomputable def xNormSq (T : ℝ) (G : ℝ → E →L[ℂ] E) (u : ℝ → E) : ℝ :=
  ‖u 0‖ ^ 2 + T * ∫ t in (0 : ℝ)..T, ‖Complex.I • deriv u t - G t (u t)‖ ^ 2

/-- The norm (2.5) of arXiv 2405.18094, `‖u‖_{X_G} = √(xNormSq T G u)`. -/
noncomputable def xNorm (T : ℝ) (G : ℝ → E →L[ℂ] E) (u : ℝ → E) : ℝ :=
  Real.sqrt (xNormSq T G u)

/-- The `H¹(I, H)` norm of arXiv 2405.18094, `‖v‖_{H¹} = (‖v 0‖² + T ∫₀ᵀ ‖v'‖²)^{1/2}`. The
paper does not print it; it is the norm for which `‖u − u*‖_{X_{H₀}} = ‖v − v*‖_{H¹}` with
`v = e^{itH₀} u` (proof of Corollary 3.8, and `h1Norm_star_freeProp_apply` here). -/
noncomputable def h1Norm (T : ℝ) (v : ℝ → E) : ℝ :=
  Real.sqrt (‖v 0‖ ^ 2 + T * ∫ t in (0 : ℝ)..T, ‖deriv v t‖ ^ 2)

/-- The norm (3.27) of arXiv 2405.18094 on `Y_G = {u ∈ X_G : u(T) = 0}`:
`‖u‖_{Y_G} = (∫₀ᵀ ‖i u' − G u‖²)^{1/2}`; for `G(t) = H + B(t)` it is the map `L` of (3.29). -/
noncomputable def yNorm (T : ℝ) (G : ℝ → E →L[ℂ] E) (u : ℝ → E) : ℝ :=
  Real.sqrt (∫ t in (0 : ℝ)..T, ‖Complex.I • deriv u t - G t (u t)‖ ^ 2)

/-- `U` is a strongly continuous family of unitaries: the abstract stand-in for the free
propagator `U(t) = e^{−itH₀}` of an arbitrary (possibly unbounded) self-adjoint `H₀` in
arXiv 2405.18094, (1.8). Mathlib has no unbounded self-adjoint operators, so `H₀` enters only
through its propagator; `freeProp` provides it for bounded `H₀`
(`isUnitaryPropagator_freeProp`). The group law is not needed. -/
structure IsUnitaryPropagator (U : ℝ → E →L[ℂ] E) : Prop where
  /-- Every `U t` is unitary. -/
  mem_unitary : ∀ t, U t ∈ unitary (E →L[ℂ] E)
  /-- `U` is strongly continuous. -/
  continuous_apply : ∀ x, Continuous fun t => U t x
  /-- `U*` is strongly continuous. -/
  continuous_star_apply : ∀ x, Continuous fun t => star (U t) x

/-- `B` is a strongly continuous family of bounded self-adjoint operators on `[0, T]` with
`‖B t‖ ≤ M`: the time-dependent potential `B(t)` of arXiv 2405.18094, (1.1). The paper asks for
strong continuity on the open interval `I = (0, T)` and uses `M = sup ‖B(t)‖ < ∞`; here
continuity on the closed interval is assumed. (The core `IsBoundedField` bounds a vector field
uniformly in the state, which no nonzero linear map satisfies, so it does not fit.) -/
structure IsBoundedPotential (B : ℝ → E →L[ℂ] E) (T M : ℝ) : Prop where
  /-- Every `B t`, `t ∈ [0, T]`, is self-adjoint. -/
  selfAdjoint : ∀ t ∈ Icc 0 T, IsSelfAdjoint (B t)
  /-- `B` is strongly continuous on `[0, T]`. -/
  continuousOn_apply : ∀ x, ContinuousOn (fun t => B t x) (Icc 0 T)
  /-- `‖B t‖ ≤ M` on `[0, T]` (the paper's `M = sup ‖B(t)‖`). -/
  norm_le : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ M

/-- The least-squares functional (1.8) of arXiv 2405.18094,
`F(v) = ‖v(0) − u₀‖² + T ‖(i∂_t − e^{itH₀}(A + B(t))e^{−itH₀}) v − e^{itH₀} f‖²_{L²(I, H)}`,
with `U t` in place of `e^{−itH₀}` (so `e^{itH₀} = (U t)*`). -/
noncomputable def leastSquaresF (T : ℝ) (U : ℝ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (B : ℝ → E →L[ℂ] E) (u₀ : E) (f : ℝ → E) (v : ℝ → E) : ℝ :=
  ‖v 0 - u₀‖ ^ 2 + T * ∫ t in (0 : ℝ)..T,
    ‖Complex.I • deriv v t - star (U t) ((A + B t) (U t (v t))) - star (U t) (f t)‖ ^ 2

/-- The free propagator `e^{−itH₀} = exp(t • (−i H₀))` of a bounded operator `H₀`. -/
noncomputable def freeProp (H₀ : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  NormedSpace.exp (t • -(Complex.I • H₀))

/-! ### Energy estimate and elementary facts -/

omit [CompleteSpace E] in
/-- A strongly continuous, uniformly bounded family of operators applied to a continuous curve
gives a continuous curve. -/
theorem continuousOn_apply_of_strong {G : ℝ → E →L[ℂ] E} {w : ℝ → E} {s : Set ℝ} {M : ℝ}
    (hG : ∀ x, ContinuousOn (fun t => G t x) s) (hGb : ∀ t ∈ s, ‖G t‖ ≤ M)
    (hw : ContinuousOn w s) : ContinuousOn (fun t => G t (w t)) s := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hM'pos : 0 < max M 0 + 1 := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ :=
    Metric.continuousWithinAt_iff.1 (hw t ht) (ε / (2 * (max M 0 + 1))) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1 (hG (w t) t ht) (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {t'} ht' hd => ?_⟩
  have e : G t' (w t') - G t (w t) = G t' (w t' - w t) + (G t' (w t) - G t (w t)) := by
    rw [map_sub]; abel
  rw [dist_eq_norm, e]
  have a1 : ‖G t' (w t' - w t)‖ ≤ (max M 0 + 1) * ‖w t' - w t‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      ((hGb t' ht').trans ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one)))
      (norm_nonneg _))
  have a2 : ‖w t' - w t‖ < ε / (2 * (max M 0 + 1)) := by
    rw [← dist_eq_norm]; exact h₁ ht' (hd.trans_le (min_le_left _ _))
  have a3 : ‖G t' (w t) - G t (w t)‖ < ε / 2 := by
    rw [← dist_eq_norm]; exact h₂ ht' (hd.trans_le (min_le_right _ _))
  have a4 : (max M 0 + 1) * ‖w t' - w t‖ < ε / 2 := by
    calc (max M 0 + 1) * ‖w t' - w t‖ < (max M 0 + 1) * (ε / (2 * (max M 0 + 1))) :=
          mul_lt_mul_of_pos_left a2 hM'pos
      _ = ε / 2 := by field_simp
  calc ‖G t' (w t' - w t) + (G t' (w t) - G t (w t))‖
      ≤ ‖G t' (w t' - w t)‖ + ‖G t' (w t) - G t (w t)‖ := norm_add_le _ _
    _ < ε := by linarith

/-- Energy identity behind (B.3) of arXiv 2405.18094: if `G` is self-adjoint, then
`2 Re ⟪x, x'⟫ = 2 Im ⟪x, i x' − G x⟫`, so `|2 Re ⟪x, x'⟫| ≤ 2 ‖x‖ ‖i x' − G x‖`. -/
theorem abs_re_inner_le_of_selfAdjoint {G : E →L[ℂ] E} (hG : IsSelfAdjoint G) (x x' : E) :
    |2 * Complex.re ⟪x, x'⟫_ℂ| ≤ 2 * ‖x‖ * ‖Complex.I • x' - G x‖ := by
  have him : Complex.im ⟪x, G x⟫_ℂ = 0 := hG.isSymmetric.im_inner_self_apply x
  have hre : Complex.re ⟪x, x'⟫_ℂ = Complex.im ⟪x, Complex.I • x' - G x⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right, Complex.sub_im, Complex.mul_im, him]
    simp
  rw [hre, abs_mul, abs_two, mul_assoc]
  gcongr
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)

omit [CompleteSpace E] in
/-- `d/dt ‖w t‖² = 2 Re ⟪w t, w'⟫` in a complex inner product space. -/
theorem hasDerivAt_norm_sq_complex {w : ℝ → E} {w' : E} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => ‖w s‖ ^ 2) (2 * Complex.re ⟪w t, w'⟫_ℂ) t := by
  have h := (Complex.reCLM.hasFDerivAt (x := ⟪w t, w t⟫_ℂ)).comp_hasDerivAt t
    (hw.inner ℂ hw)
  have e : (fun s => ‖w s‖ ^ 2) = Complex.reCLM ∘ fun s => ⟪w s, w s⟫_ℂ := by
    funext s
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (w s)).symm
  rw [e]
  convert h using 1
  simp only [Complex.reCLM_apply, Complex.add_re]
  rw [← inner_conj_symm (w t) w', Complex.conj_re]
  ring

/-- **Energy estimate (the role of (2.7) and (B.3) of arXiv 2405.18094).** Let `G(t)` be
self-adjoint on `[0, T]` and `w` a `C¹` curve. For every base point `t₀ ∈ [0, T]` and every
`t ∈ [0, T]`, `‖w t‖² ≤ 2 ‖w t₀‖² + 4 T ∫₀ᵀ ‖i w' − G w‖²`. Self-adjointness makes the bound
independent of `‖G‖`; the constant is `4` (for `t₀ = 0`, `‖w‖_{C⁰} ≤ 2 N(w)`) instead of the
paper's `2`, which does not affect the theorems below. The base point `t₀ = T` gives the
backward estimate needed for Proposition 3.20. -/
theorem sq_norm_le_of_selfAdjoint {T t₀ : ℝ} {G : ℝ → E →L[ℂ] E} {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hG : ∀ t ∈ Icc 0 T, IsSelfAdjoint (G t))
    (hGw : ContinuousOn (fun t => G t (w t)) (Icc 0 T)) (ht₀ : t₀ ∈ Icc 0 T) :
    ∀ t ∈ Icc 0 T, ‖w t‖ ^ 2 ≤
      2 * ‖w t₀‖ ^ 2 + 4 * T * ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2 := by
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  have hdc : Continuous (deriv w) := hw.continuous_deriv le_rfl
  have hwc : Continuous w := hw.continuous
  have hfc : ContinuousOn (fun s => ‖Complex.I • deriv w s - G s (w s)‖ ^ 2) (Icc 0 T) :=
    ((hdc.const_smul Complex.I).continuousOn.sub hGw).norm.pow 2
  set I0 := ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2 with hI0_def
  have hI0 : 0 ≤ I0 := intervalIntegral.integral_nonneg hT (fun s _ => by positivity)
  rcases hT.eq_or_lt with h0 | hTpos
  · intro t ht
    subst h0
    have e1 : t = 0 := le_antisymm ht.2 ht.1
    have e2 : t₀ = 0 := le_antisymm ht₀.2 ht₀.1
    subst e1 e2
    nlinarith [sq_nonneg ‖w 0‖]
  · have hφ : ∀ s, HasDerivAt (fun s => ‖w s‖ ^ 2) (2 * Complex.re ⟪w s, deriv w s⟫_ℂ) s :=
      fun s => hasDerivAt_norm_sq_complex ((hw.differentiable one_ne_zero) s).hasDerivAt
    have hφ'c : Continuous fun s => 2 * Complex.re ⟪w s, deriv w s⟫_ℂ :=
      continuous_const.mul (Complex.continuous_re.comp (hwc.inner hdc))
    obtain ⟨t₁, ht₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT)
      (hwc.norm.pow 2).continuousOn
    set S := ‖w t₁‖ ^ 2 with hS_def
    have hbound : ∀ s ∈ Icc 0 T, ‖2 * Complex.re ⟪w s, deriv w s⟫_ℂ‖ ≤
        S / (2 * T) + 2 * T * ‖Complex.I • deriv w s - G s (w s)‖ ^ 2 := by
      intro s hs
      rw [Real.norm_eq_abs]
      have h1 := abs_re_inner_le_of_selfAdjoint (hG s hs) (w s) (deriv w s)
      have h2 : ‖w s‖ ^ 2 ≤ S := hmax hs
      set a := ‖w s‖
      set b := ‖Complex.I • deriv w s - G s (w s)‖
      have h3 : 2 * a * b ≤ a ^ 2 / (2 * T) + 2 * T * b ^ 2 := by
        rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (a - 2 * T * b)]
      have h4 : a ^ 2 / (2 * T) ≤ S / (2 * T) := div_le_div_of_nonneg_right h2 (by positivity)
      linarith
    have hftc : ‖w t₁‖ ^ 2 - ‖w t₀‖ ^ 2 =
        ∫ s in t₀..t₁, 2 * Complex.re ⟪w s, deriv w s⟫_ℂ :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ s)
        (hφ'c.intervalIntegrable _ _)).symm
    have hsub : uIoc t₀ t₁ ⊆ Ioc 0 T :=
      Ioc_subset_Ioc (le_min ht₀.1 ht₁.1) (max_le ht₀.2 ht₁.2)
    have hint : ∫ s in t₀..t₁, 2 * Complex.re ⟪w s, deriv w s⟫_ℂ ≤ S / 2 + 2 * T * I0 := by
      calc ∫ s in t₀..t₁, 2 * Complex.re ⟪w s, deriv w s⟫_ℂ
          ≤ ‖∫ s in t₀..t₁, 2 * Complex.re ⟪w s, deriv w s⟫_ℂ‖ := Real.le_norm_self _
        _ ≤ ∫ s in uIoc t₀ t₁, ‖2 * Complex.re ⟪w s, deriv w s⟫_ℂ‖ :=
            intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ s in Ioc 0 T, ‖2 * Complex.re ⟪w s, deriv w s⟫_ℂ‖ :=
            setIntegral_mono_set (hφ'c.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              (ae_of_all _ fun _ => norm_nonneg _) hsub.eventuallyLE
        _ ≤ ∫ s in Ioc 0 T, (S / (2 * T) +
              2 * T * ‖Complex.I • deriv w s - G s (w s)‖ ^ 2) :=
            setIntegral_mono_on (hφ'c.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              ((continuousOn_const.add (continuousOn_const.mul hfc)).integrableOn_Icc.mono_set
                Ioc_subset_Icc_self) measurableSet_Ioc
              (fun s hs => hbound s (Ioc_subset_Icc_self hs))
        _ = S / 2 + 2 * T * I0 := by
            rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_add
              intervalIntegrable_const, intervalIntegral.integral_const,
              intervalIntegral.integral_const_mul]
            · rw [smul_eq_mul]; field_simp; ring
            · exact (continuousOn_const.mul hfc).intervalIntegrable_of_Icc hT
    have hS : S ≤ 2 * ‖w t₀‖ ^ 2 + 4 * T * I0 := by linarith
    intro t ht
    exact (hmax ht).trans hS

omit [CompleteSpace E] in
/-- `xNormSq` is nonnegative for `T ≥ 0`. -/
theorem xNormSq_nonneg {T : ℝ} (hT : 0 ≤ T) (G : ℝ → E →L[ℂ] E) (u : ℝ → E) :
    0 ≤ xNormSq T G u := by
  unfold xNormSq
  have : 0 ≤ ∫ t in (0 : ℝ)..T, ‖Complex.I • deriv u t - G t (u t)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun s _ => sq_nonneg _)
  positivity

omit [CompleteSpace E] in
/-- The `H¹` norm is the `X_G` norm for `G = 0`. -/
theorem h1Norm_eq_xNorm_zero (T : ℝ) (v : ℝ → E) : h1Norm T v = xNorm T 0 v := by
  simp [h1Norm, xNorm, xNormSq, norm_smul]

/-- `2 + 8 L² T² ≤ (2 + 8 L²)(1 + T)²` for `T ≥ 0`. -/
theorem two_add_mul_sq_le (L : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    2 + 8 * L ^ 2 * T ^ 2 ≤ (2 + 8 * L ^ 2) * (1 + T) ^ 2 := by
  nlinarith [sq_nonneg L, sq_nonneg T, mul_nonneg (sq_nonneg L) hT]

/-- `α / (1 + T)^γ * x ≤ α / (1 + T) * x` for `γ ≥ 1`: a lower bound with exponent `1` gives
the same bound with every exponent `γ ≥ 1`. -/
theorem div_one_add_pow_mul_le {α T x : ℝ} (hα : 0 ≤ α) (hT : 0 ≤ T) (hx : 0 ≤ x) {γ : ℕ}
    (hγ : 1 ≤ γ) : α / (1 + T) ^ γ * x ≤ α / (1 + T) * x :=
  mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hα (by linarith) (le_self_pow₀ (by linarith) (by omega))) hx

/-- `t ↦ (H + B t)(u t)` is continuous on `[0, T]` for a continuous curve `u`. -/
theorem IsBoundedPotential.continuousOn_add_apply {B : ℝ → E →L[ℂ] E} {T M : ℝ}
    (hB : IsBoundedPotential B T M) (H : E →L[ℂ] E) {u : ℝ → E} (hu : Continuous u) :
    ContinuousOn (fun t => (H + B t) (u t)) (Icc 0 T) := by
  simp only [add_apply]
  exact (H.continuous.comp hu).continuousOn.add
    (continuousOn_apply_of_strong hB.continuousOn_apply hB.norm_le hu.continuousOn)

/-- `‖(H₀ + A + B t) − H₀‖ ≤ ‖A‖ + M` on `[0, T]`. -/
theorem IsBoundedPotential.norm_add_sub_le {B : ℝ → E →L[ℂ] E} {T M : ℝ}
    (hB : IsBoundedPotential B T M) (H₀ A : E →L[ℂ] E) :
    ∀ t ∈ Icc 0 T, ‖H₀ + A + B t - H₀‖ ≤ ‖A‖ + M := fun t ht => by
  rw [add_assoc, add_sub_cancel_left]
  exact (norm_add_le _ _).trans (by linarith [hB.norm_le t ht])

/-! ### Perturbation of the residual norm -/

/-- **Perturbation estimate.** If `G` is self-adjoint and `‖K t − G t‖ ≤ L` on `[0, T]`, then
for a `C¹` curve `w` and `t₀ ∈ [0, T]`,
`∫‖i w' − K w‖² ≤ 2 ∫‖i w' − G w‖² + 2 L² T (2 ‖w t₀‖² + 4 T ∫‖i w' − G w‖²)`. This is the
argument of the proof of Theorem 3.7 of arXiv 2405.18094 with Proposition 3.13 replaced by the
operator-norm bound `‖K − G‖ ≤ L` (bounded perturbation, Remark 3.6 (i)). -/
theorem integral_resid_sq_le {T t₀ L : ℝ} {G K : ℝ → E →L[ℂ] E} {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hG : ∀ t ∈ Icc 0 T, IsSelfAdjoint (G t))
    (hGw : ContinuousOn (fun t => G t (w t)) (Icc 0 T))
    (hKw : ContinuousOn (fun t => K t (w t)) (Icc 0 T))
    (hKG : ∀ t ∈ Icc 0 T, ‖K t - G t‖ ≤ L) (ht₀ : t₀ ∈ Icc 0 T) :
    ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - K s (w s)‖ ^ 2 ≤
      2 * (∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2) + 2 * L ^ 2 * T *
        (2 * ‖w t₀‖ ^ 2 + 4 * T * ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2) := by
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  have hE := sq_norm_le_of_selfAdjoint hw hG hGw ht₀
  set IG := ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2
  set R := 2 * ‖w t₀‖ ^ 2 + 4 * T * IG
  have hdc := hw.continuous_deriv le_rfl
  have hfG : ContinuousOn (fun s => ‖Complex.I • deriv w s - G s (w s)‖ ^ 2) (Icc 0 T) :=
    ((hdc.const_smul Complex.I).continuousOn.sub hGw).norm.pow 2
  have hfK : ContinuousOn (fun s => ‖Complex.I • deriv w s - K s (w s)‖ ^ 2) (Icc 0 T) :=
    ((hdc.const_smul Complex.I).continuousOn.sub hKw).norm.pow 2
  have hpt : ∀ s ∈ Icc 0 T, ‖Complex.I • deriv w s - K s (w s)‖ ^ 2 ≤
      2 * ‖Complex.I • deriv w s - G s (w s)‖ ^ 2 + 2 * L ^ 2 * R := by
    intro s hs
    have e : Complex.I • deriv w s - K s (w s) =
        (Complex.I • deriv w s - G s (w s)) - (K s - G s) (w s) := by
      rw [sub_apply]; abel
    have hL : 0 ≤ L := (norm_nonneg _).trans (hKG s hs)
    have h1 : ‖(K s - G s) (w s)‖ ≤ L * ‖w s‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hKG s hs) (norm_nonneg _))
    have h2 : ‖w s‖ ^ 2 ≤ R := hE s hs
    rw [e]
    set a := ‖Complex.I • deriv w s - G s (w s)‖
    have h3 := norm_sub_le (Complex.I • deriv w s - G s (w s)) ((K s - G s) (w s))
    have h4 : ‖(K s - G s) (w s)‖ ^ 2 ≤ L ^ 2 * R := by
      calc ‖(K s - G s) (w s)‖ ^ 2 ≤ (L * ‖w s‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = L ^ 2 * ‖w s‖ ^ 2 := by ring
        _ ≤ L ^ 2 * R := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : ‖Complex.I • deriv w s - G s (w s) - (K s - G s) (w s)‖ ^ 2 ≤
        (a + ‖(K s - G s) (w s)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [sq_nonneg (a - ‖(K s - G s) (w s)‖)]
  have hiK : IntervalIntegrable (fun s => ‖Complex.I • deriv w s - K s (w s)‖ ^ 2) volume 0 T :=
    hfK.intervalIntegrable_of_Icc hT
  have hiG : IntervalIntegrable
      (fun s => 2 * ‖Complex.I • deriv w s - G s (w s)‖ ^ 2 + 2 * L ^ 2 * R) volume 0 T :=
    ((continuousOn_const.mul hfG).add continuousOn_const).intervalIntegrable_of_Icc hT
  calc ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - K s (w s)‖ ^ 2
      ≤ ∫ s in (0 : ℝ)..T, (2 * ‖Complex.I • deriv w s - G s (w s)‖ ^ 2 + 2 * L ^ 2 * R) :=
        intervalIntegral.integral_mono_on hT hiK hiG hpt
    _ = 2 * IG + 2 * L ^ 2 * T * R := by
        rw [intervalIntegral.integral_add _ intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
        · ring
        · exact (continuousOn_const.mul hfG).intervalIntegrable_of_Icc hT

/-- `‖w‖²_{X_K} ≤ (2 + 8 L²)(1 + T)² ‖w‖²_{X_G}` if `G` is self-adjoint and `‖K − G‖ ≤ L`. -/
theorem xNormSq_le_of_norm_sub_le {T L : ℝ} (hT : 0 ≤ T) {G K : ℝ → E →L[ℂ] E} {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hG : ∀ t ∈ Icc 0 T, IsSelfAdjoint (G t))
    (hGw : ContinuousOn (fun t => G t (w t)) (Icc 0 T))
    (hKw : ContinuousOn (fun t => K t (w t)) (Icc 0 T))
    (hKG : ∀ t ∈ Icc 0 T, ‖K t - G t‖ ≤ L) :
    xNormSq T K w ≤ (2 + 8 * L ^ 2) * (1 + T) ^ 2 * xNormSq T G w := by
  have h := integral_resid_sq_le hw hG hGw hKw hKG ⟨le_rfl, hT⟩
  unfold xNormSq
  set IG := ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2
  set IK := ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - K s (w s)‖ ^ 2
  set a := ‖w 0‖ ^ 2
  have hIG : 0 ≤ IG := intervalIntegral.integral_nonneg hT (fun s _ => by positivity)
  have ha : 0 ≤ a := by positivity
  have h1 : T * IK ≤ T * (2 * IG + 2 * L ^ 2 * T * (2 * a + 4 * T * IG)) :=
    mul_le_mul_of_nonneg_left h hT
  have h2 : a + T * IK ≤ (2 + 8 * L ^ 2 * T ^ 2) * (a + T * IG) := by
    have e : (2 + 8 * L ^ 2 * T ^ 2) * (a + T * IG) =
        (a + 4 * L ^ 2 * T ^ 2 * a) +
          (a + T * (2 * IG + 2 * L ^ 2 * T * (2 * a + 4 * T * IG))) := by ring
    rw [e]
    nlinarith [sq_nonneg (L * T)]
  have h4 : 0 ≤ a + T * IG := by positivity
  calc a + T * IK ≤ (2 + 8 * L ^ 2 * T ^ 2) * (a + T * IG) := h2
    _ ≤ (2 + 8 * L ^ 2) * (1 + T) ^ 2 * (a + T * IG) := 
        mul_le_mul_of_nonneg_right (two_add_mul_sq_le L hT) h4

/-- `‖w‖_{X_K} ≤ √(2 + 8 L²) (1 + T) ‖w‖_{X_G}` if `G` is self-adjoint and `‖K − G‖ ≤ L`. -/
theorem xNorm_le_of_norm_sub_le {T L : ℝ} (hT : 0 ≤ T) {G K : ℝ → E →L[ℂ] E} {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hG : ∀ t ∈ Icc 0 T, IsSelfAdjoint (G t))
    (hGw : ContinuousOn (fun t => G t (w t)) (Icc 0 T))
    (hKw : ContinuousOn (fun t => K t (w t)) (Icc 0 T))
    (hKG : ∀ t ∈ Icc 0 T, ‖K t - G t‖ ≤ L) :
    xNorm T K w ≤ Real.sqrt (2 + 8 * L ^ 2) * (1 + T) * xNorm T G w := by
  unfold xNorm
  calc Real.sqrt (xNormSq T K w)
      ≤ Real.sqrt ((2 + 8 * L ^ 2) * (1 + T) ^ 2 * xNormSq T G w) :=
        Real.sqrt_le_sqrt (xNormSq_le_of_norm_sub_le hT hw hG hGw hKw hKG)
    _ = Real.sqrt (2 + 8 * L ^ 2) * (1 + T) * Real.sqrt (xNormSq T G w) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by linarith)]

/-- **Two-sided norm equivalence under a bounded self-adjoint perturbation.** If `G` and `K`
are self-adjoint on `[0, T]` with `‖K t − G t‖ ≤ L`, then for every `C¹` curve `w`,
`(1/C)/(1 + T) ‖w‖_{X_G} ≤ ‖w‖_{X_K} ≤ C (1 + T) ‖w‖_{X_G}` with `C = √(2 + 8 L²)`. This is
the common core of Theorem 3.7 and Corollary 3.8 of arXiv 2405.18094; the constants depend on
`L` only, not on `T`, `G` or `K`. -/
theorem xNorm_equiv_of_norm_sub_le {T L : ℝ} (hT : 0 ≤ T) {G K : ℝ → E →L[ℂ] E} {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hG : ∀ t ∈ Icc 0 T, IsSelfAdjoint (G t))
    (hK : ∀ t ∈ Icc 0 T, IsSelfAdjoint (K t))
    (hGw : ContinuousOn (fun t => G t (w t)) (Icc 0 T))
    (hKw : ContinuousOn (fun t => K t (w t)) (Icc 0 T))
    (hKG : ∀ t ∈ Icc 0 T, ‖K t - G t‖ ≤ L) :
    1 / Real.sqrt (2 + 8 * L ^ 2) / (1 + T) * xNorm T G w ≤ xNorm T K w ∧
      xNorm T K w ≤ Real.sqrt (2 + 8 * L ^ 2) * (1 + T) * xNorm T G w := by
  refine ⟨?_, xNorm_le_of_norm_sub_le hT hw hG hGw hKw hKG⟩
  have h := xNorm_le_of_norm_sub_le hT hw hK hKw hGw
    (fun t ht => by rw [norm_sub_rev]; exact hKG t ht)
  have hc : 0 < Real.sqrt (2 + 8 * L ^ 2) * (1 + T) := by positivity
  rw [div_div, one_div_mul_eq_div, div_le_iff₀ hc, mul_comm]
  exact h

/-- Definiteness: if `G` is self-adjoint and `‖w‖_{X_G} = 0`, then `w = 0` on `[0, T]`. -/
theorem eqOn_zero_of_xNormSq_eq_zero {T : ℝ} {G : ℝ → E →L[ℂ] E} {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hG : ∀ t ∈ Icc 0 T, IsSelfAdjoint (G t))
    (hGw : ContinuousOn (fun t => G t (w t)) (Icc 0 T)) (h : xNormSq T G w = 0) :
    ∀ t ∈ Icc 0 T, w t = 0 := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hE := sq_norm_le_of_selfAdjoint hw hG hGw ⟨le_rfl, hT⟩ t ht
  unfold xNormSq at h
  set IG := ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2
  have hIG : 0 ≤ IG := intervalIntegral.integral_nonneg hT (fun s _ => by positivity)
  have h0 : ‖w 0‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w 0‖, mul_nonneg hT hIG]
  have h1 : T * IG = 0 := by nlinarith [sq_nonneg ‖w 0‖, mul_nonneg hT hIG]
  have : ‖w t‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖w t‖ = 0 := by nlinarith [norm_nonneg (w t)]
  exact norm_eq_zero.1 this

/-- Backward version of `xNorm_le_of_norm_sub_le` for curves with `w T = 0`:
`‖w‖_{Y_K} ≤ √(2 + 8 L²) (1 + T) ‖w‖_{Y_G}` if `G` is self-adjoint and `‖K − G‖ ≤ L`. -/
theorem yNorm_le_of_norm_sub_le {T L : ℝ} (hT : 0 ≤ T) {G K : ℝ → E →L[ℂ] E} {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hwT : w T = 0) (hG : ∀ t ∈ Icc 0 T, IsSelfAdjoint (G t))
    (hGw : ContinuousOn (fun t => G t (w t)) (Icc 0 T))
    (hKw : ContinuousOn (fun t => K t (w t)) (Icc 0 T))
    (hKG : ∀ t ∈ Icc 0 T, ‖K t - G t‖ ≤ L) :
    yNorm T K w ≤ Real.sqrt (2 + 8 * L ^ 2) * (1 + T) * yNorm T G w := by
  have h := integral_resid_sq_le hw hG hGw hKw hKG ⟨hT, le_rfl⟩
  rw [hwT, norm_zero] at h
  set IG := ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - G s (w s)‖ ^ 2
  set IK := ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv w s - K s (w s)‖ ^ 2
  have hIG : 0 ≤ IG := intervalIntegral.integral_nonneg hT (fun s _ => by positivity)
  have h2 : IK ≤ (2 + 8 * L ^ 2) * (1 + T) ^ 2 * IG :=
    calc IK ≤ 2 * IG + 2 * L ^ 2 * T * (2 * 0 ^ 2 + 4 * T * IG) := h
      _ = (2 + 8 * L ^ 2 * T ^ 2) * IG := by ring
      _ ≤ (2 + 8 * L ^ 2) * (1 + T) ^ 2 * IG :=
          mul_le_mul_of_nonneg_right (two_add_mul_sq_le L hT) hIG
  unfold yNorm
  calc Real.sqrt IK ≤ Real.sqrt ((2 + 8 * L ^ 2) * (1 + T) ^ 2 * IG) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (2 + 8 * L ^ 2) * (1 + T) * Real.sqrt IG := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by linarith)]

/-! ### Theorem 3.7 and Proposition 3.20 -/

/-- **Theorem 3.7 (i) of arXiv 2405.18094, bounded-perturbation case.** Let `A` be bounded and
self-adjoint. There are `α, C > 0`, depending only on `‖A‖`, such that for every bounded
self-adjoint `H₀`, every `T ≥ 0` and every `C¹` curve `u`, with `H = H₀ + A`,
`α/(1 + T) ‖u‖_{X_{H₀}} ≤ ‖u‖_{X_H} ≤ C (1 + T) ‖u‖_{X_{H₀}}` (3.4).

Deviations from the printed theorem: `A` is bounded (a special case of assumption (A), see
Remark 3.6 (i)); `H₀` is bounded too, but the constants do not depend on `H₀`; the inequality is
stated for `C¹` curves, which are dense in `X_{H₀}` (Proposition 2.7), and both sides are
continuous norms. With bounded operators `X_H = X_{H₀}` holds trivially, so the content is the
norm equivalence. Explicitly `C = √(2 + 8 ‖A‖²)` and `α = 1/C`. -/
theorem xNorm_add_equiv (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ H₀ : E →L[ℂ] E, IsSelfAdjoint H₀ → ∀ T : ℝ, 0 ≤ T →
      ∀ u : ℝ → E, ContDiff ℝ 1 u →
        α / (1 + T) * xNorm T (fun _ => H₀) u ≤ xNorm T (fun _ => H₀ + A) u ∧
          xNorm T (fun _ => H₀ + A) u ≤ C * (1 + T) * xNorm T (fun _ => H₀) u := by
  refine ⟨1 / Real.sqrt (2 + 8 * ‖A‖ ^ 2), Real.sqrt (2 + 8 * ‖A‖ ^ 2), by positivity,
    by positivity, fun H₀ hH₀ T hT u hu => ?_⟩
  have hc := hu.continuous
  refine xNorm_equiv_of_norm_sub_le hT hu (fun _ _ => hH₀) (fun _ _ => hH₀.add hA)
    (H₀.continuous.comp hc).continuousOn ((H₀ + A).continuous.comp hc).continuousOn
    (fun t _ => ?_)
  simp

/-- **Theorem 3.7 (ii) of arXiv 2405.18094, bounded-perturbation case.** Let `A` be bounded and
self-adjoint and `M ≥ sup ‖B(t)‖`. There are `α, C > 0`, depending only on `‖A‖` and `M`, such
that for every bounded self-adjoint `H₀`, `T ≥ 0`, every potential `B` (`IsBoundedPotential`),
every `C¹` curve `u` and every `γ ≥ 1`,
`α/(1 + T)^γ ‖u‖_{X_{H₀}} ≤ N(u) ≤ C (1 + T) ‖u‖_{X_{H₀}}` with `N(u) = ‖u‖_{X_{H₀+A+B}}` (3.5).
The paper states `γ = 2` (3.6); in the bounded case the proof gives `γ = 1`, which implies it.
That `N` is definite is `eqOn_zero_of_xNorm_add_timeDep_eq_zero`. Deviations as in
`xNorm_add_equiv`, and `B` strongly continuous on `[0, T]` rather than on `(0, T)`. -/
theorem xNorm_add_timeDep_equiv (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (M : ℝ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ H₀ : E →L[ℂ] E, IsSelfAdjoint H₀ → ∀ T : ℝ, 0 ≤ T →
      ∀ B : ℝ → E →L[ℂ] E, IsBoundedPotential B T M →
      ∀ u : ℝ → E, ContDiff ℝ 1 u → ∀ γ : ℕ, 1 ≤ γ →
        α / (1 + T) ^ γ * xNorm T (fun _ => H₀) u ≤ xNorm T (fun t => H₀ + A + B t) u ∧
          xNorm T (fun t => H₀ + A + B t) u ≤ C * (1 + T) * xNorm T (fun _ => H₀) u := by
  refine ⟨1 / Real.sqrt (2 + 8 * (‖A‖ + M) ^ 2), Real.sqrt (2 + 8 * (‖A‖ + M) ^ 2),
    by positivity, by positivity, fun H₀ hH₀ T hT B hB u hu γ hγ => ?_⟩
  have hc := hu.continuous
  have key := xNorm_equiv_of_norm_sub_le hT hu (fun _ _ => hH₀)
    (fun t ht => (hH₀.add hA).add (hB.selfAdjoint t ht)) (H₀.continuous.comp hc).continuousOn
    (hB.continuousOn_add_apply (H₀ + A) hc) (hB.norm_add_sub_le H₀ A)
  exact ⟨(div_one_add_pow_mul_le (by positivity) hT (Real.sqrt_nonneg _) hγ).trans key.1, key.2⟩

/-- `N` of (3.5) in arXiv 2405.18094 is definite: `N(u) = 0` forces `u = 0` on `[0, T]` (the
nontrivial part of "N defines a norm" in Theorem 3.7 (ii)). -/
theorem eqOn_zero_of_xNorm_add_timeDep_eq_zero {T M : ℝ} {H₀ A : E →L[ℂ] E}
    (hH₀ : IsSelfAdjoint H₀) (hA : IsSelfAdjoint A) {B : ℝ → E →L[ℂ] E}
    (hB : IsBoundedPotential B T M) {u : ℝ → E} (hu : ContDiff ℝ 1 u)
    (h : xNorm T (fun t => H₀ + A + B t) u = 0) : ∀ t ∈ Icc 0 T, u t = 0 := by
  intro t ht
  exact eqOn_zero_of_xNormSq_eq_zero hu (fun t ht => (hH₀.add hA).add (hB.selfAdjoint t ht))
    (hB.continuousOn_add_apply (H₀ + A) hu.continuous)
    ((Real.sqrt_eq_zero (xNormSq_nonneg (ht.1.trans ht.2) _ _)).1 h) t ht

/-- **Proposition 3.20 of arXiv 2405.18094, bounded-perturbation case.** With `A`, `B`, `M` as
in `xNorm_add_timeDep_equiv`, there are `α, C > 0` (depending on `‖A‖`, `M`) such that for every
bounded self-adjoint `H₀`, `T ≥ 0`, every `C¹` curve `u` with `u T = 0` and `γ ≥ 1`,
`α/(1 + T)^γ ‖u‖_{Y_{H₀}} ≤ L(u) ≤ C (1 + T) ‖u‖_{Y_{H₀}}` with `L(u) = ‖u‖_{Y_{H₀+A+B}}`
(3.29)–(3.30); the paper has `γ = 2`. As in the paper, the proof is that of Theorem 3.7 with the
energy estimate based at `T`. Definiteness of `L` is `eqOn_zero_of_yNorm_eq_zero`. Deviations as
in `xNorm_add_timeDep_equiv`. -/
theorem yNorm_add_timeDep_equiv (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (M : ℝ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ H₀ : E →L[ℂ] E, IsSelfAdjoint H₀ → ∀ T : ℝ, 0 ≤ T →
      ∀ B : ℝ → E →L[ℂ] E, IsBoundedPotential B T M →
      ∀ u : ℝ → E, ContDiff ℝ 1 u → u T = 0 → ∀ γ : ℕ, 1 ≤ γ →
        α / (1 + T) ^ γ * yNorm T (fun _ => H₀) u ≤ yNorm T (fun t => H₀ + A + B t) u ∧
          yNorm T (fun t => H₀ + A + B t) u ≤ C * (1 + T) * yNorm T (fun _ => H₀) u := by
  refine ⟨1 / Real.sqrt (2 + 8 * (‖A‖ + M) ^ 2), Real.sqrt (2 + 8 * (‖A‖ + M) ^ 2),
    by positivity, by positivity, fun H₀ hH₀ T hT B hB u hu huT γ hγ => ?_⟩
  have hc := hu.continuous
  have hKu := hB.continuousOn_add_apply (H₀ + A) hc
  have hKG := hB.norm_add_sub_le H₀ A
  have hup := yNorm_le_of_norm_sub_le hT hu huT (fun _ _ => hH₀)
    (H₀.continuous.comp hc).continuousOn hKu hKG
  have hlow := yNorm_le_of_norm_sub_le hT hu huT
    (fun t ht => (hH₀.add hA).add (hB.selfAdjoint t ht)) hKu (H₀.continuous.comp hc).continuousOn
    (fun t ht => by rw [norm_sub_rev]; exact hKG t ht)
  refine ⟨(div_one_add_pow_mul_le (by positivity) hT (Real.sqrt_nonneg _) hγ).trans ?_, hup⟩
  have hcpos : 0 < Real.sqrt (2 + 8 * (‖A‖ + M) ^ 2) * (1 + T) := by positivity
  rw [div_div, one_div_mul_eq_div, div_le_iff₀ hcpos, mul_comm]
  exact hlow

/-- `L` of (3.29) in arXiv 2405.18094 is definite on `Y`: if `u T = 0` and `L(u) = 0`, then
`u = 0` on `[0, T]`. -/
theorem eqOn_zero_of_yNorm_eq_zero {T M : ℝ} {G : ℝ → E →L[ℂ] E}
    (hG : IsBoundedPotential G T M)
    {u : ℝ → E} (hu : ContDiff ℝ 1 u) (huT : u T = 0) (h : yNorm T G u = 0) :
    ∀ t ∈ Icc 0 T, u t = 0 := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hI : 0 ≤ ∫ s in (0 : ℝ)..T, ‖Complex.I • deriv u s - G s (u s)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun s _ => by positivity)
  have hI0 := (Real.sqrt_eq_zero hI).1 h
  have hE := sq_norm_le_of_selfAdjoint hu hG.selfAdjoint
    (continuousOn_apply_of_strong hG.continuousOn_apply hG.norm_le hu.continuous.continuousOn)
    ⟨hT, le_rfl⟩ t ht
  rw [huT, hI0, norm_zero] at hE
  have : ‖u t‖ ^ 2 ≤ 0 := by linarith
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg (u t)])

/-! ### Corollary 3.8 and Remark 3.11 (interaction picture) -/

/-- A unitary operator has norm at most `1`. -/
theorem IsUnitaryPropagator.norm_le_one {U : ℝ → E →L[ℂ] E} (hU : IsUnitaryPropagator U)
    (t : ℝ) : ‖U t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (hU.mem_unitary t), one_mul]

/-- The adjoint of a unitary operator has norm at most `1`. -/
theorem IsUnitaryPropagator.norm_star_le_one {U : ℝ → E →L[ℂ] E} (hU : IsUnitaryPropagator U)
    (t : ℝ) : ‖star (U t)‖ ≤ 1 := by
  rw [norm_star]; exact hU.norm_le_one t

/-- The interaction-picture operator `e^{itH₀}(A + B(t))e^{−itH₀}` of (1.8) is self-adjoint. -/
theorem interaction_selfAdjoint {U : ℝ → E →L[ℂ] E} {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {B : ℝ → E →L[ℂ] E} {T M : ℝ} (hB : IsBoundedPotential B T M) :
    ∀ t ∈ Icc 0 T, IsSelfAdjoint (star (U t) * (A + B t) * U t) :=
  fun t ht => (hA.add (hB.selfAdjoint t ht)).conjugate' (U t)

/-- `‖e^{itH₀}(A + B(t))e^{−itH₀}‖ ≤ ‖A‖ + M`. -/
theorem interaction_norm_le {U : ℝ → E →L[ℂ] E} (hU : IsUnitaryPropagator U) {A : E →L[ℂ] E}
    {B : ℝ → E →L[ℂ] E} {T M : ℝ} (hB : IsBoundedPotential B T M) :
    ∀ t ∈ Icc 0 T, ‖star (U t) * (A + B t) * U t‖ ≤ ‖A‖ + M := by
  intro t ht
  have h2 : ‖A + B t‖ ≤ ‖A‖ + M := (norm_add_le _ _).trans (by linarith [hB.norm_le t ht])
  calc ‖star (U t) * (A + B t) * U t‖ ≤ ‖star (U t)‖ * ‖A + B t‖ * ‖U t‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖A + B t‖ * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hU.norm_star_le_one t) (norm_nonneg _))
          (hU.norm_le_one t) (norm_nonneg _) (by positivity)
    _ ≤ ‖A‖ + M := by linarith

/-- The interaction-picture operator applied to a continuous curve is continuous on `[0, T]`. -/
theorem interaction_continuousOn {U : ℝ → E →L[ℂ] E} (hU : IsUnitaryPropagator U)
    {A : E →L[ℂ] E} {B : ℝ → E →L[ℂ] E} {T M : ℝ} (hB : IsBoundedPotential B T M)
    {w : ℝ → E} (hw : Continuous w) :
    ContinuousOn (fun t => (star (U t) * (A + B t) * U t) (w t)) (Icc 0 T) := by
  have h1 : ContinuousOn (fun t => U t (w t)) (Icc 0 T) :=
    continuousOn_apply_of_strong (fun x => (hU.continuous_apply x).continuousOn)
      (fun t _ => hU.norm_le_one t) hw.continuousOn
  have h2 : ContinuousOn (fun t => (A + B t) (U t (w t))) (Icc 0 T) := by
    simp only [add_apply]
    exact (A.continuous.comp_continuousOn h1).add
      (continuousOn_apply_of_strong hB.continuousOn_apply hB.norm_le h1)
  have h3 : ContinuousOn (fun t => star (U t) ((A + B t) (U t (w t)))) (Icc 0 T) :=
    continuousOn_apply_of_strong (fun x => (hU.continuous_star_apply x).continuousOn)
      (fun t _ => hU.norm_star_le_one t) h2
  exact h3

/-- **The functional `F` of (1.8) is quadratic** (Corollary 3.8 of arXiv 2405.18094): if `vs`
solves the interaction-picture equation `i vs' − U*(A + B)U vs = U* f` on `[0, T]` with
`vs 0 = u₀`, then `F(v) = ‖v − vs‖²_{X_K}` with `K(t) = U(t)*(A + B(t))U(t)` for every `C¹`
curve `v`. -/
theorem leastSquaresF_eq_xNormSq {T : ℝ} (hT : 0 ≤ T) {U : ℝ → E →L[ℂ] E} {A : E →L[ℂ] E}
    {B : ℝ → E →L[ℂ] E} {u₀ : E} {f vs v : ℝ → E} (hv : ContDiff ℝ 1 v)
    (hvs : ContDiff ℝ 1 vs) (hvs0 : vs 0 = u₀)
    (hsol : ∀ t ∈ Icc 0 T, Complex.I • deriv vs t - star (U t) ((A + B t) (U t (vs t))) =
      star (U t) (f t)) :
    leastSquaresF T U A B u₀ f v =
      xNormSq T (fun t => star (U t) * (A + B t) * U t) (v - vs) := by
  unfold leastSquaresF xNormSq
  rw [Pi.sub_apply, hvs0]
  congr 2
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  simp only
  rw [← hsol t ht, deriv_sub ((hv.differentiable one_ne_zero) t)
    ((hvs.differentiable one_ne_zero) t)]
  congr 2
  simp only [mul_apply_eq_comp, Pi.sub_apply, map_sub, smul_sub]
  abel

/-- **Corollary 3.8 of arXiv 2405.18094, estimate (3.7), bounded-perturbation case.** Let `A` be
bounded self-adjoint and `M ≥ sup ‖B‖`. There are `α, C > 0`, depending only on `‖A‖` and `M`,
such that for every strongly continuous unitary family `U` (standing for `e^{−itH₀}` with an
arbitrary, possibly unbounded, self-adjoint `H₀`), every `T ≥ 0`, potential `B`, data `u₀, f`,
every `C¹` solution `vs` of the interaction-picture equation
`i vs' − U*(A + B)U vs = U* f`, `vs 0 = u₀`, every `C¹` curve `v` and every `γ ≥ 1`:
`α/(1 + T)^γ ‖v − vs‖_{H¹} ≤ √F(v) ≤ C (1 + T) ‖v − vs‖_{H¹}`.

The paper has `γ = 1` for `B = 0` and `γ = 2` otherwise; both are covered. Deviations: `A` is
bounded (Remark 3.6 (i)); `vs` is given as a solution in the interaction picture, which for
`vs = e^{itH₀} u*` is equivalent to `u*` solving (1.1) (Proposition B.2 and the computation in
the proof of Corollary 3.8; for bounded `H₀` this is `interactionPicture_of_solution`, and
`leastSquaresF_normEquiv_of_solution` states the corollary in the paper's form); `v` ranges over
`C¹` curves, a dense subspace of `H¹(I, H)`. Explicitly `C = √(2 + 8 (‖A‖ + M)²)`, `α = 1/C`. -/
theorem leastSquaresF_normEquiv (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (M : ℝ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ U : ℝ → E →L[ℂ] E, IsUnitaryPropagator U →
      ∀ T : ℝ, 0 ≤ T → ∀ B : ℝ → E →L[ℂ] E, IsBoundedPotential B T M →
      ∀ (u₀ : E) (f vs : ℝ → E), ContDiff ℝ 1 vs → vs 0 = u₀ →
      (∀ t ∈ Icc 0 T, Complex.I • deriv vs t - star (U t) ((A + B t) (U t (vs t))) =
        star (U t) (f t)) →
      ∀ v : ℝ → E, ContDiff ℝ 1 v → ∀ γ : ℕ, 1 ≤ γ →
        α / (1 + T) ^ γ * h1Norm T (v - vs) ≤ Real.sqrt (leastSquaresF T U A B u₀ f v) ∧
          Real.sqrt (leastSquaresF T U A B u₀ f v) ≤ C * (1 + T) * h1Norm T (v - vs) := by
  refine ⟨1 / Real.sqrt (2 + 8 * (‖A‖ + M) ^ 2), Real.sqrt (2 + 8 * (‖A‖ + M) ^ 2),
    by positivity, by positivity,
    fun U hU T hT B hB u₀ f vs hvs hvs0 hsol v hv γ hγ => ?_⟩
  have hw : ContDiff ℝ 1 (v - vs) := hv.sub hvs
  rw [leastSquaresF_eq_xNormSq hT hv hvs hvs0 hsol, h1Norm_eq_xNorm_zero]
  have key := xNorm_equiv_of_norm_sub_le (L := ‖A‖ + M) hT hw
    (fun _ _ => IsSelfAdjoint.zero _) (interaction_selfAdjoint hA hB) continuousOn_const
    (interaction_continuousOn hU hB hw.continuous)
    (fun t ht => by rw [sub_zero]; exact interaction_norm_le hU hB t ht)
  exact ⟨(div_one_add_pow_mul_le (by positivity) hT (Real.sqrt_nonneg _) hγ).trans key.1, key.2⟩

/-- **Corollary 3.8 of arXiv 2405.18094, last claim:** `vs` is the unique minimiser of `F`
(among `C¹` curves, on `[0, T]`): `F(vs) = 0 ≤ F(v)`, and `F(v) ≤ F(vs)` forces `v = vs` on
`[0, T]`. Same setting as `leastSquaresF_normEquiv`. -/
theorem leastSquaresF_isUniqueMin {T : ℝ} (hT : 0 ≤ T) {U : ℝ → E →L[ℂ] E}
    (hU : IsUnitaryPropagator U) {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {B : ℝ → E →L[ℂ] E}
    {M : ℝ} (hB : IsBoundedPotential B T M) {u₀ : E} {f vs : ℝ → E} (hvs : ContDiff ℝ 1 vs)
    (hvs0 : vs 0 = u₀)
    (hsol : ∀ t ∈ Icc 0 T, Complex.I • deriv vs t - star (U t) ((A + B t) (U t (vs t))) =
      star (U t) (f t)) :
    leastSquaresF T U A B u₀ f vs = 0 ∧
      (∀ v : ℝ → E, ContDiff ℝ 1 v → 0 ≤ leastSquaresF T U A B u₀ f v) ∧
      ∀ v : ℝ → E, ContDiff ℝ 1 v →
        leastSquaresF T U A B u₀ f v ≤ leastSquaresF T U A B u₀ f vs →
          ∀ t ∈ Icc 0 T, v t = vs t := by
  have h0 : leastSquaresF T U A B u₀ f vs = 0 := by
    rw [leastSquaresF_eq_xNormSq hT hvs hvs hvs0 hsol, sub_self]
    simp [xNormSq]
  refine ⟨h0, fun v hv => ?_, fun v hv hle t ht => ?_⟩
  · rw [leastSquaresF_eq_xNormSq hT hv hvs hvs0 hsol]
    exact xNormSq_nonneg hT _ _
  · have hw : ContDiff ℝ 1 (v - vs) := hv.sub hvs
    rw [h0, leastSquaresF_eq_xNormSq hT hv hvs hvs0 hsol] at hle
    have hz := eqOn_zero_of_xNormSq_eq_zero hw (interaction_selfAdjoint hA hB)
      (interaction_continuousOn hU hB hw.continuous) (le_antisymm hle (xNormSq_nonneg hT _ _)) t
      ht
    exact sub_eq_zero.1 hz

/-- **Remark 3.11 of arXiv 2405.18094, unconditional (bounded-perturbation case).** With `α, C`
the constants of Corollary 3.8 (`leastSquaresF_normEquiv`): for every set `S` of `C¹` curves
(for instance `C¹(I, Σ)` for a low-rank set `Σ ⊂ H`) and every minimiser `vt` of `F` over `S`,
`‖vt − v*‖_{H¹} ≤ C (1 + T)^(γ+1)/α ‖v − v*‖_{H¹}` for all `v ∈ S`, and the same against the
infimum over `S`. Unlike `remark311_ceaType`, the two-sided bound (3.7) is proved here, not
assumed. Deviations: those of `leastSquaresF_normEquiv`; in particular `S` consists of `C¹`
curves instead of a subset of `H¹(I, Σ)`, and the existence of a minimiser is not claimed. -/
theorem remark311_ceaType_h1 (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (M : ℝ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ U : ℝ → E →L[ℂ] E, IsUnitaryPropagator U →
      ∀ T : ℝ, 0 ≤ T → ∀ B : ℝ → E →L[ℂ] E, IsBoundedPotential B T M →
      ∀ (u₀ : E) (f vs : ℝ → E), ContDiff ℝ 1 vs → vs 0 = u₀ →
      (∀ t ∈ Icc 0 T, Complex.I • deriv vs t - star (U t) ((A + B t) (U t (vs t))) =
        star (U t) (f t)) →
      ∀ S : Set (ℝ → E), (∀ v ∈ S, ContDiff ℝ 1 v) → ∀ vt ∈ S,
      (∀ v ∈ S, leastSquaresF T U A B u₀ f vt ≤ leastSquaresF T U A B u₀ f v) →
      ∀ γ : ℕ, 1 ≤ γ →
        (∀ v ∈ S, h1Norm T (vt - vs) ≤ C * (1 + T) ^ (γ + 1) / α * h1Norm T (v - vs)) ∧
        h1Norm T (vt - vs) ≤
          C * (1 + T) ^ (γ + 1) / α * sInf ((fun v => h1Norm T (v - vs)) '' S) := by
  obtain ⟨α, C, hα, hC, h⟩ := leastSquaresF_normEquiv A hA M
  refine ⟨α, C, hα, hC, fun U hU T hT B hB u₀ f vs hvs hvs0 hsol S hS vt hvt hmin γ hγ => ?_⟩
  have h1T : 0 < 1 + T := by linarith
  have e : C * (1 + T) / (α / (1 + T) ^ γ) = C * (1 + T) ^ (γ + 1) / α := by
    field_simp
    ring
  rw [← e]
  exact ceaType_of_equiv (leastSquaresF T U A B u₀ f) (fun v => h1Norm T (v - vs))
    (by positivity) (by positivity)
    (fun v hv => (h U hU T hT B hB u₀ f vs hvs hvs0 hsol v (hS v hv) γ hγ).1)
    (fun v hv => (h U hU T hT B hB u₀ f vs hvs hvs0 hsol v (hS v hv) γ hγ).2) hvt hmin

/-! ### Bounded free Hamiltonian: the propagator `e^{−itH₀}` -/

/-- `(e^{−itH₀})* = e^{itH₀}` for self-adjoint `H₀`. -/
theorem star_freeProp {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) (t : ℝ) :
    star (freeProp H₀ t) = NormedSpace.exp (t • (Complex.I • H₀)) := by
  rw [freeProp, NormedSpace.star_exp]
  simp [star_smul, hH₀.star_eq]

/-- `e^{−itH₀}` is unitary for self-adjoint `H₀`. -/
theorem freeProp_mem_unitary {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) (t : ℝ) :
    freeProp H₀ t ∈ unitary (E →L[ℂ] E) := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [star_smul, hH₀.star_eq]

/-- `t ↦ e^{−itH₀}` is norm continuous for bounded `H₀`. -/
theorem continuous_freeProp (H₀ : E →L[ℂ] E) : Continuous (freeProp H₀) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const _ t).continuousAt

/-- For bounded self-adjoint `H₀`, `t ↦ e^{−itH₀}` is a unitary propagator; in particular the
hypothesis `IsUnitaryPropagator` is satisfiable. -/
theorem isUnitaryPropagator_freeProp {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) :
    IsUnitaryPropagator (freeProp H₀) where
  mem_unitary := freeProp_mem_unitary hH₀
  continuous_apply _ := (continuous_freeProp H₀).clm_apply continuous_const
  continuous_star_apply _ :=
    (continuous_star.comp (continuous_freeProp H₀)).clm_apply continuous_const

/-- `d/dt (e^{itH₀} u(t)) = e^{itH₀} (i H₀ u(t) + u'(t))`. -/
theorem hasDerivAt_star_freeProp_apply {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀)
    {u : ℝ → E} {u' : E} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => star (freeProp H₀ s) (u s))
      (star (freeProp H₀ t) (Complex.I • H₀ (u t) + u')) t := by
  simp_rw [star_freeProp hH₀]
  let R := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hV : HasDerivAt (fun s : ℝ => R (NormedSpace.exp (s • (Complex.I • H₀))))
      (R (NormedSpace.exp (t • (Complex.I • H₀)) * (Complex.I • H₀))) t :=
    R.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (Complex.I • H₀) t)
  have h := hV.clm_apply hu
  refine h.congr_deriv ?_
  change (NormedSpace.exp (t • (Complex.I • H₀)) * (Complex.I • H₀)) (u t) +
    NormedSpace.exp (t • (Complex.I • H₀)) u' = _
  rw [mul_apply_eq_comp, map_add]
  rfl

/-- `t ↦ e^{itH₀} u(t)` is `C¹` when `u` is. -/
theorem contDiff_star_freeProp_apply {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) {u : ℝ → E}
    (hu : ContDiff ℝ 1 u) : ContDiff ℝ 1 fun s => star (freeProp H₀ s) (u s) := by
  have hd : ∀ t, HasDerivAt (fun s => star (freeProp H₀ s) (u s))
      (star (freeProp H₀ t) (Complex.I • H₀ (u t) + deriv u t)) t := fun t =>
    hasDerivAt_star_freeProp_apply hH₀ ((hu.differentiable one_ne_zero) t).hasDerivAt
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  rw [show deriv (fun s => star (freeProp H₀ s) (u s)) =
      fun t => star (freeProp H₀ t) (Complex.I • H₀ (u t) + deriv u t) from
    funext fun t => (hd t).deriv]
  exact (continuous_star.comp (continuous_freeProp H₀)).clm_apply
    ((continuous_const.smul (H₀.continuous.comp hu.continuous)).add
      (hu.continuous_deriv le_rfl))

/-- `i ∂_t (e^{itH₀} u) = e^{itH₀} (i ∂_t − H₀) u` (Proposition B.2 of arXiv 2405.18094,
bounded case). -/
theorem smul_deriv_star_freeProp_apply {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) {u : ℝ → E}
    (hu : ContDiff ℝ 1 u) (t : ℝ) :
    Complex.I • deriv (fun s => star (freeProp H₀ s) (u s)) t =
      star (freeProp H₀ t) (Complex.I • deriv u t - H₀ (u t)) := by
  rw [(hasDerivAt_star_freeProp_apply hH₀
    ((hu.differentiable one_ne_zero) t).hasDerivAt).deriv]
  rw [← map_smul, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, sub_eq_neg_add]

/-- `e^{−itH₀} e^{itH₀} x = x`. -/
theorem freeProp_star_freeProp_apply {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) (t : ℝ)
    (x : E) : freeProp H₀ t (star (freeProp H₀ t) x) = x := by
  rw [← mul_apply_eq_comp, Unitary.mul_star_self_of_mem (freeProp_mem_unitary hH₀ t),
    one_apply_eq_self]

/-- `e^{i0H₀} = 1`. -/
theorem star_freeProp_zero {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) :
    star (freeProp H₀ 0) = 1 := by
  simp [star_freeProp hH₀]

/-- **Interaction picture is an isometry** (bounded `H₀`): for `v = e^{itH₀} u`,
`‖v‖_{X_K} = ‖u‖_{X_{H₀+A+B}}` with `K(t) = e^{itH₀}(A + B(t))e^{−itH₀}`. This is the
computation in the proof of Corollary 3.8 of arXiv 2405.18094. -/
theorem xNormSq_interaction_eq {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) (A : E →L[ℂ] E)
    (B : ℝ → E →L[ℂ] E) {u : ℝ → E} (hu : ContDiff ℝ 1 u) (T : ℝ) :
    xNormSq T (fun t => star (freeProp H₀ t) * (A + B t) * freeProp H₀ t)
        (fun s => star (freeProp H₀ s) (u s)) =
      xNormSq T (fun t => H₀ + A + B t) u := by
  unfold xNormSq
  congr 1
  · simp [star_freeProp hH₀]
  · congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only
    rw [smul_deriv_star_freeProp_apply hH₀ hu, mul_apply_eq_comp, mul_apply_eq_comp,
      freeProp_star_freeProp_apply hH₀, ← map_sub,
      ContinuousLinearMap.norm_map_of_mem_unitary
        (Unitary.star_mem (freeProp_mem_unitary hH₀ t))]
    congr 1
    simp only [add_apply]
    abel_nf

/-- **Proposition 2.4 of arXiv 2405.18094, isomorphism part (2.6)/(2.9), bounded case:**
`u ↦ e^{itH₀} u` is an isometry from `X_{H₀}` to `H¹(I, H)`, `‖e^{itH₀} u‖_{H¹} = ‖u‖_{X_{H₀}}`,
for `C¹` curves and bounded self-adjoint `H₀`. -/
theorem h1Norm_star_freeProp_apply {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) {u : ℝ → E}
    (hu : ContDiff ℝ 1 u) (T : ℝ) :
    h1Norm T (fun s => star (freeProp H₀ s) (u s)) = xNorm T (fun _ => H₀) u := by
  have h := xNormSq_interaction_eq hH₀ 0 0 hu T
  simp only [Pi.zero_apply, add_zero, mul_zero, zero_mul] at h
  rw [h1Norm_eq_xNorm_zero, xNorm, xNorm]
  convert congrArg Real.sqrt h using 2

omit [CompleteSpace E] in
/-- A `C¹` classical solution of `i u' − H(t) u = f` on `[0, T]` (the paper's (1.1) with
`H(t) = H + B(t)`) is a solution of the ODE `u' = −i (H(t) u + f)` in the sense of the core
`LeanDLRA.ODESolution`. -/
theorem odeSolution_of_classical {T : ℝ} {H : ℝ → E →L[ℂ] E} {f u : ℝ → E}
    (hu : ContDiff ℝ 1 u) (hsol : ∀ t ∈ Icc 0 T, Complex.I • deriv u t - H t (u t) = f t) :
    LeanDLRA.ODESolution (fun t x => -Complex.I • (H t x + f t)) u 0 T where
  cont := hu.continuous.continuousOn
  deriv t ht := by
    have h := ((hu.differentiable one_ne_zero) t).hasDerivAt.hasDerivWithinAt (s := Ici t)
    convert h using 1
    rw [← hsol t (Ico_subset_Icc_self ht), add_sub_cancel, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul]

/-- If `u*` is a `C¹` solution of (1.1), `i u*' − (H₀ + A + B) u* = f` on `[0, T]` (bounded
`H₀`), then `v* = e^{itH₀} u*` solves the interaction-picture equation
`i v*' − e^{itH₀}(A + B)e^{−itH₀} v* = e^{itH₀} f`; this is the hypothesis of
`leastSquaresF_normEquiv`. -/
theorem interactionPicture_of_solution {T : ℝ} {H₀ A : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀)
    {B : ℝ → E →L[ℂ] E} {f us : ℝ → E} (hus : ContDiff ℝ 1 us)
    (hsol : ∀ t ∈ Icc 0 T, Complex.I • deriv us t - (H₀ + A + B t) (us t) = f t) :
    ∀ t ∈ Icc 0 T, Complex.I • deriv (fun s => star (freeProp H₀ s) (us s)) t -
        star (freeProp H₀ t) ((A + B t) (freeProp H₀ t (star (freeProp H₀ t) (us t)))) =
      star (freeProp H₀ t) (f t) := by
  intro t ht
  rw [smul_deriv_star_freeProp_apply hH₀ hus, freeProp_star_freeProp_apply hH₀, ← map_sub,
    ← hsol t ht]
  congr 1
  simp only [add_apply]
  abel_nf

/-- **The identity in the proof of Corollary 3.8 of arXiv 2405.18094** (bounded `H₀`):
`F(e^{itH₀} u) = N(u − u*)²`, with `N` the norm (3.5) and `u*` the solution of (1.1). -/
theorem leastSquaresF_freeProp_eq {T : ℝ} (hT : 0 ≤ T) {H₀ A : E →L[ℂ] E}
    (hH₀ : IsSelfAdjoint H₀) {B : ℝ → E →L[ℂ] E} {u₀ : E} {f us u : ℝ → E}
    (hus : ContDiff ℝ 1 us) (hus0 : us 0 = u₀)
    (hsol : ∀ t ∈ Icc 0 T, Complex.I • deriv us t - (H₀ + A + B t) (us t) = f t)
    (hu : ContDiff ℝ 1 u) :
    leastSquaresF T (freeProp H₀) A B u₀ f (fun s => star (freeProp H₀ s) (u s)) =
      xNormSq T (fun t => H₀ + A + B t) (u - us) := by
  rw [leastSquaresF_eq_xNormSq hT (contDiff_star_freeProp_apply hH₀ hu)
    (contDiff_star_freeProp_apply hH₀ hus) (by simp [star_freeProp_zero hH₀, hus0])
    (interactionPicture_of_solution hH₀ hus hsol),
    ← xNormSq_interaction_eq hH₀ A B (u := u - us) (hu.sub hus) T]
  congr 1
  funext s
  simp [map_sub]

/-- **Corollary 3.8 of arXiv 2405.18094 in the paper's form, bounded case.** For bounded
self-adjoint `H₀`, `U(t) = e^{−itH₀}`, `u*` a `C¹` solution of (1.1) and `v* = e^{itH₀} u*`:
`α/(1 + T)^γ ‖v − v*‖_{H¹} ≤ √F(v) ≤ C (1 + T) ‖v − v*‖_{H¹}` for all `C¹` curves `v`, with
`α, C` depending only on `‖A‖` and `M` (not on `H₀`, `T`, `u₀`, `f`). -/
theorem leastSquaresF_normEquiv_of_solution (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (M : ℝ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ H₀ : E →L[ℂ] E, IsSelfAdjoint H₀ →
      ∀ T : ℝ, 0 ≤ T → ∀ B : ℝ → E →L[ℂ] E, IsBoundedPotential B T M →
      ∀ (u₀ : E) (f us : ℝ → E), ContDiff ℝ 1 us → us 0 = u₀ →
      (∀ t ∈ Icc 0 T, Complex.I • deriv us t - (H₀ + A + B t) (us t) = f t) →
      ∀ v : ℝ → E, ContDiff ℝ 1 v → ∀ γ : ℕ, 1 ≤ γ →
        α / (1 + T) ^ γ * h1Norm T (v - fun t => star (freeProp H₀ t) (us t)) ≤
            Real.sqrt (leastSquaresF T (freeProp H₀) A B u₀ f v) ∧
          Real.sqrt (leastSquaresF T (freeProp H₀) A B u₀ f v) ≤
            C * (1 + T) * h1Norm T (v - fun t => star (freeProp H₀ t) (us t)) := by
  obtain ⟨α, C, hα, hC, h⟩ := leastSquaresF_normEquiv A hA M
  refine ⟨α, C, hα, hC, fun H₀ hH₀ T hT B hB u₀ f us hus hus0 hsol v hv γ hγ => ?_⟩
  exact h (freeProp H₀) (isUnitaryPropagator_freeProp hH₀) T hT B hB u₀ f _
    (contDiff_star_freeProp_apply hH₀ hus) (by simp [star_freeProp_zero hH₀, hus0])
    (interactionPicture_of_solution hH₀ hus hsol) v hv γ hγ

/-- **Uniqueness of solutions of (1.1)** (Proposition 2.4 / B.4 of arXiv 2405.18094, for `C¹`
solutions and a bounded potential family `G(t) = H + B(t)`): two solutions with the same initial
value agree on `[0, T]`. -/
theorem eqOn_of_classical_solution {T M : ℝ} {G : ℝ → E →L[ℂ] E}
    (hG : IsBoundedPotential G T M)
    {f u₁ u₂ : ℝ → E} (hu₁ : ContDiff ℝ 1 u₁) (hu₂ : ContDiff ℝ 1 u₂) (h0 : u₁ 0 = u₂ 0)
    (hs₁ : ∀ t ∈ Icc 0 T, Complex.I • deriv u₁ t - G t (u₁ t) = f t)
    (hs₂ : ∀ t ∈ Icc 0 T, Complex.I • deriv u₂ t - G t (u₂ t) = f t) :
    ∀ t ∈ Icc 0 T, u₁ t = u₂ t := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hw : ContDiff ℝ 1 (u₁ - u₂) := hu₁.sub hu₂
  have hz : xNormSq T G (u₁ - u₂) = 0 := by
    unfold xNormSq
    have hcongr : EqOn (fun s => ‖Complex.I • deriv (u₁ - u₂) s - G s ((u₁ - u₂) s)‖ ^ 2)
        (fun _ => (0 : ℝ)) (uIcc 0 T) := by
      intro s hs
      rw [uIcc_of_le hT] at hs
      simp only
      rw [deriv_sub ((hu₁.differentiable one_ne_zero) s) ((hu₂.differentiable one_ne_zero) s),
        Pi.sub_apply, map_sub, smul_sub,
        show Complex.I • deriv u₁ s - Complex.I • deriv u₂ s - (G s (u₁ s) - G s (u₂ s)) =
          (Complex.I • deriv u₁ s - G s (u₁ s)) - (Complex.I • deriv u₂ s - G s (u₂ s)) by abel,
        hs₁ s hs, hs₂ s hs, sub_self, norm_zero]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_zero, Pi.sub_apply, h0,
      sub_self, norm_zero]
    ring
  exact sub_eq_zero.1 (eqOn_zero_of_xNormSq_eq_zero hw hG.selfAdjoint
    (continuousOn_apply_of_strong hG.continuousOn_apply hG.norm_le hw.continuous.continuousOn)
    hz t ht)

/-! ### Continuity estimate (2.7) and integration by parts (2.14) -/

/-- Cauchy–Schwarz on `[0, T]`: `(∫₀ᵀ g)² ≤ T ∫₀ᵀ g²` for continuous `g`. -/
theorem sq_integral_le_mul_integral_sq {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) :
    (∫ s in (0 : ℝ)..T, g s) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, g s ^ 2 := by
  rcases hT.eq_or_lt with h0 | hTpos
  · subst h0; simp
  set m := ∫ s in (0 : ℝ)..T, g s
  set q := ∫ s in (0 : ℝ)..T, g s ^ 2
  set c := m / T
  have hgi : IntervalIntegrable g volume 0 T := hg.intervalIntegrable_of_Icc hT
  have hg2 : IntervalIntegrable (fun s => g s ^ 2) volume 0 T :=
    (hg.pow 2).intervalIntegrable_of_Icc hT
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..T, (g s - c) ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun _ _ => sq_nonneg _)
  have e : ∫ s in (0 : ℝ)..T, (g s - c) ^ 2 = q - 2 * c * m + c ^ 2 * T := by
    have : (fun s => (g s - c) ^ 2) = fun s => g s ^ 2 - 2 * c * g s + c ^ 2 := by
      funext s; ring
    rw [this, intervalIntegral.integral_add (hg2.sub (hgi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hg2 (hgi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have hc : c * T = m := by simp only [c]; field_simp
  have h3 : c ^ 2 * T = c * m := by rw [← hc]; ring
  have h2 : c * m ≤ q := by linarith
  calc m ^ 2 = T * (c * m) := by rw [← hc]; ring
    _ ≤ T * q := mul_le_mul_of_nonneg_left h2 hT

/-- `‖v‖_{C⁰([0,T], H)} ≤ √2 ‖v‖_{H¹}` for `C¹` curves (the "naive" estimate in Remark 3.10
of arXiv 2405.18094). -/
theorem norm_le_sqrt_two_mul_h1Norm {T : ℝ} {v : ℝ → E} (hv : ContDiff ℝ 1 v) :
    ∀ t ∈ Icc 0 T, ‖v t‖ ≤ Real.sqrt 2 * h1Norm T v := by
  intro t ht
  have hT := ht.1.trans ht.2
  have hdc := hv.continuous_deriv le_rfl
  have hftc : v t - v 0 = ∫ s in (0 : ℝ)..t, deriv v s :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => ((hv.differentiable one_ne_zero) s).hasDerivAt)
      (hdc.intervalIntegrable _ _)).symm
  set m := ∫ s in (0 : ℝ)..T, ‖deriv v s‖
  set q := ∫ s in (0 : ℝ)..T, ‖deriv v s‖ ^ 2
  have h1 : ‖v t - v 0‖ ≤ m := by
    rw [hftc]
    exact (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
      (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (ae_of_all _ fun _ => norm_nonneg _) (hdc.norm.intervalIntegrable _ _))
  have h2 : m ^ 2 ≤ T * q := sq_integral_le_mul_integral_sq hT hdc.norm.continuousOn
  have h3 : ‖v t‖ ≤ ‖v 0‖ + m := by
    have := norm_sub_norm_le (v t) (v 0)
    linarith
  have h4 : ‖v t‖ ^ 2 ≤ (‖v 0‖ + m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  have h5 : ‖v t‖ ^ 2 ≤ 2 * (‖v 0‖ ^ 2 + T * q) := by
    nlinarith [sq_nonneg (‖v 0‖ - m)]
  unfold h1Norm
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h5)

/-- **Estimate (2.7) of arXiv 2405.18094** (Proposition 2.4), for bounded self-adjoint `H` and
`C¹` curves: `‖u‖_{C⁰([0,T], H)} ≤ √2 ‖u‖_{X_H}`. As in the paper, the proof goes through the
isometry `u ↦ e^{itH} u` onto `H¹`. -/
theorem norm_le_sqrt_two_mul_xNorm {T : ℝ} {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) {u : ℝ → E}
    (hu : ContDiff ℝ 1 u) : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.sqrt 2 * xNorm T (fun _ => H) u := by
  intro t ht
  have h := norm_le_sqrt_two_mul_h1Norm (contDiff_star_freeProp_apply hH hu) t ht
  rwa [h1Norm_star_freeProp_apply hH hu, ContinuousLinearMap.norm_map_of_mem_unitary
    (Unitary.star_mem (freeProp_mem_unitary hH t))] at h

/-- **Integration by parts (2.14) of arXiv 2405.18094** (Proposition 2.7), for bounded
self-adjoint `H` and `C¹` curves `u, v`:
`∫₀ᵀ ⟪(i∂_t − H) u, v⟫ = −i (⟪u T, v T⟫ − ⟪u 0, v 0⟫) + ∫₀ᵀ ⟪u, (i∂_t − H) v⟫`.
The density part of Proposition 2.7 is not formalized (the curves here are `C¹` already). -/
theorem integral_inner_resid_eq {T : ℝ} {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) {u v : ℝ → E}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    ∫ t in (0 : ℝ)..T, ⟪Complex.I • deriv u t - H (u t), v t⟫_ℂ =
      -Complex.I * (⟪u T, v T⟫_ℂ - ⟪u 0, v 0⟫_ℂ) +
        ∫ t in (0 : ℝ)..T, ⟪u t, Complex.I • deriv v t - H (v t)⟫_ℂ := by
  have hdu := hu.continuous_deriv le_rfl
  have hdv := hv.continuous_deriv le_rfl
  have hg : ∀ t, HasDerivAt (fun s => ⟪u s, v s⟫_ℂ)
      (⟪u t, deriv v t⟫_ℂ + ⟪deriv u t, v t⟫_ℂ) t := fun t =>
    ((hu.differentiable one_ne_zero) t).hasDerivAt.inner ℂ
      ((hv.differentiable one_ne_zero) t).hasDerivAt
  have hgc : Continuous fun t => ⟪u t, deriv v t⟫_ℂ + ⟪deriv u t, v t⟫_ℂ :=
    (hu.continuous.inner hdv).add (hdu.inner hv.continuous)
  have hftc : ∫ t in (0 : ℝ)..T, (⟪u t, deriv v t⟫_ℂ + ⟪deriv u t, v t⟫_ℂ) =
      ⟪u T, v T⟫_ℂ - ⟪u 0, v 0⟫_ℂ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t) (hgc.intervalIntegrable _ _)
  have hpt : ∀ t, ⟪Complex.I • deriv u t - H (u t), v t⟫_ℂ =
      -Complex.I * (⟪u t, deriv v t⟫_ℂ + ⟪deriv u t, v t⟫_ℂ) +
        ⟪u t, Complex.I • deriv v t - H (v t)⟫_ℂ := by
    intro t
    have hs : ⟪H (u t), v t⟫_ℂ = ⟪u t, H (v t)⟫_ℂ := hH.isSymmetric (u t) (v t)
    rw [inner_sub_left, inner_smul_left, inner_sub_right, inner_smul_right, Complex.conj_I, hs]
    ring
  have hRc : Continuous fun t => ⟪u t, Complex.I • deriv v t - H (v t)⟫_ℂ :=
    hu.continuous.inner ((hdv.const_smul _).sub (H.continuous.comp hv.continuous))
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hgc.const_mul _).intervalIntegrable _ _)
    (hRc.intervalIntegrable _ _), intervalIntegral.integral_const_mul, hftc]

/-- Non-vacuity of Corollary 3.8: for any bounded self-adjoint `H₀`, `U = e^{−itH₀}`, `A = 0`,
`B = 0`, `f = 0` and the constant curve `vs = u₀` satisfy all hypotheses of
`leastSquaresF_normEquiv`. -/
example {H₀ : E →L[ℂ] E} (hH₀ : IsSelfAdjoint H₀) (T : ℝ) (u₀ : E) :
    IsUnitaryPropagator (freeProp H₀) ∧ IsBoundedPotential (fun _ => (0 : E →L[ℂ] E)) T 0 ∧
      ∀ t ∈ Icc 0 T, Complex.I • deriv (fun _ => u₀) t -
          star (freeProp H₀ t) (((0 : E →L[ℂ] E) + 0) (freeProp H₀ t u₀)) =
        star (freeProp H₀ t) ((fun _ => (0 : E)) t) :=
  ⟨isUnitaryPropagator_freeProp hH₀,
    ⟨fun _ _ => IsSelfAdjoint.zero _, fun _ => continuousOn_const, fun _ _ => by simp⟩,
    fun _ _ => by simp⟩

/-! ### Corollary 3.23 as printed -/

/-- The functional (3.36) of arXiv 2405.18094 as printed, for bounded `H₀`:
`E*(u) = ‖u(t) + i ∫₀ᵗ e^{−i(t−s)H₀} A u(s) ds − (e^{−itH₀} u₀ − i ∫₀ᵗ e^{−i(t−s)H₀} f(s) ds)‖²`
in `L²(0, T)`. It contains `A` but not the potential `B(t)`. -/
noncomputable def dualLeastSquares (T : ℝ) (H₀ A : E →L[ℂ] E) (u₀ : E) (f u : ℝ → E) : ℝ :=
  ∫ t in (0 : ℝ)..T, ‖u t + Complex.I • (∫ s in (0 : ℝ)..t, freeProp H₀ (t - s) (A (u s))) -
    (freeProp H₀ t u₀ - Complex.I • ∫ s in (0 : ℝ)..t, freeProp H₀ (t - s) (f s))‖ ^ 2

/-- **Corollary 3.23 of arXiv 2405.18094 fails as printed when `B ≠ 0`.** Take `H = ℂ`,
`H₀ = A = 0`, the bounded potential `B(t) = 1` (`IsBoundedPotential` with `M = 1`), `u₀ = 1`,
`f = 0`, `T = 1`. Then `u*(t) = e^{−it}` is a `C¹` solution of (1.1), but the printed functional
(3.36) does not vanish at it: `E*(u*) > 0`. So the upper bound of (3.37),
`√E*(u) ≤ C (1 + T) ‖u − u*‖_{L²}`, fails at `u = u*` for every `C`
(`dualLeastSquares_upper_bound_fails`). The paper's Section 3.6 assumes such a `B`, and its proof
of Corollary 3.23 also drops `B`; the statement appears to need `A + B(s)` in place of `A` in
(3.36). With `B = 0` this example does not apply. Checked against the printed PDF, p. 17. -/
theorem dualLeastSquares_printed_pos :
    ContDiff ℝ 1 (fun t : ℝ => Complex.exp (-(t * Complex.I))) ∧
      IsBoundedPotential (fun _ => (1 : ℂ →L[ℂ] ℂ)) 1 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.I • deriv (fun t : ℝ => Complex.exp (-(t * Complex.I))) t -
          ((0 : ℂ →L[ℂ] ℂ) + 0 + 1) (Complex.exp (-(t * Complex.I))) = 0) ∧
      0 < dualLeastSquares 1 (0 : ℂ →L[ℂ] ℂ) 0 1 0
        fun t : ℝ => Complex.exp (-(t * Complex.I)) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(t * Complex.I)))
      (Complex.exp (-(t * Complex.I)) * -(1 * Complex.I)) t := fun t =>
    (((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).neg).cexp
  have hc : Continuous fun t : ℝ => Complex.exp (-(t * Complex.I)) := by fun_prop
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun t => (hd t).differentiableAt, by
      rw [funext fun t => (hd t).deriv]; exact hc.mul continuous_const⟩,
    ⟨fun _ _ => IsSelfAdjoint.one _, fun _ => continuousOn_const,
      fun _ _ => ContinuousLinearMap.norm_id_le⟩, fun t _ => ?_, ?_⟩
  · rw [(hd t).deriv]
    simp only [smul_eq_mul, zero_add, one_apply_eq_self]
    have e : Complex.I * (Complex.exp (-(t * Complex.I)) * -(1 * Complex.I)) =
        Complex.exp (-(t * Complex.I)) := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [e, sub_self]
  · have e : dualLeastSquares 1 (0 : ℂ →L[ℂ] ℂ) 0 1 0
        (fun t : ℝ => Complex.exp (-(t * Complex.I))) =
        ∫ t in (0 : ℝ)..1, ‖Complex.exp (-(t * Complex.I)) - 1‖ ^ 2 := by
      simp [dualLeastSquares, freeProp]
    rw [e]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) one_pos
    · exact ((hc.sub continuous_const).norm.pow 2).intervalIntegrable _ _
    · have hne : Complex.exp (-(x * Complex.I)) ≠ 1 := by
        intro h
        obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
        have him := congrArg Complex.im hn
        simp at him
        have hpi := Real.pi_gt_three
        rcases le_or_gt 0 n with h0 | h0
        · have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h0
          nlinarith [hx.1]
        · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h0
          nlinarith [hx.2]
      have : 0 < ‖Complex.exp (-(x * Complex.I)) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      positivity

/-- The upper bound of (3.37) in arXiv 2405.18094, `√E*(u) ≤ C (1 + T) ‖u − u*‖_{L²(0,T)}`, fails
at `u = u*` for every `C` in the example of `dualLeastSquares_printed_pos` (`T = 1`). -/
theorem dualLeastSquares_upper_bound_fails (C : ℝ) :
    ¬ Real.sqrt (dualLeastSquares 1 (0 : ℂ →L[ℂ] ℂ) 0 1 0
        fun t : ℝ => Complex.exp (-(t * Complex.I))) ≤
      C * (1 + 1) * Real.sqrt (∫ t in (0 : ℝ)..1,
        ‖Complex.exp (-(t * Complex.I)) - Complex.exp (-(t * Complex.I))‖ ^ 2) := by
  have h := Real.sqrt_pos.2 dualLeastSquares_printed_pos.2.2.2
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    intervalIntegral.integral_zero, Real.sqrt_zero, mul_zero]
  exact not_le.2 h

end SpaceTime

end LeanDLRA.Literature.P2405_18094
