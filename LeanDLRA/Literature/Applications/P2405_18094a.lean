import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Results of arXiv 2405.18094 (Dupuy, Ehrlacher, Guillot): abstract cores

This module formalizes two abstract cores of the space-time variational formulation of the
Schrödinger equation in arXiv 2405.18094. It uses no LeanDLRA definitions: the statements
concern a generic normed space and its weak topology, and do not use the LeanDLRA integrators.

* `ceaType_of_normEquiv` is the abstract core of **Remark 3.11** (Céa-type quasi-optimality of
  constrained minimisers of a least-squares functional `F`). Assume `F` is bounded above and
  below by multiples of the distance to a reference point `v*` (the square root of `F` is
  two-sided norm-equivalent to `‖· − v*‖`). Then every minimiser `ṽ` of `F` over any subset `S`
  satisfies `‖ṽ − v*‖ ≤ (c₂/c₁) ‖v − v*‖` for all `v ∈ S`, and hence the same bound against the
  infimum over `S`.
* `remark311_ceaType` specializes this to the constants of the paper, `c₁ = α/(1+T)^γ` and
  `c₂ = C(1+T)`, which gives the ratio `C(1+T)^(γ+1)/α` stated in Remark 3.11. The two-sided bound
  (3.7) is taken as a hypothesis here. It is the conclusion of Corollary 3.8, which is NOT
  formalized in this file (see below).
* `weaklyClosed_timeSlice` is the abstract core of **Proposition 4.1** (weak closedness of
  `H¹(I, Σ) = {u : u(t) ∈ Σ for all t ∈ I}` in the weak topology). Mathlib does not contain the
  Bochner–Sobolev space `H¹(I, H)`, so the space is replaced by a generic normed space `W` with
  a family of continuous linear evaluation maps `ev t : W →L H`. The paper's continuity of
  `u ↦ u(t)` on `H¹(I, H)` (via `H¹(I,H) ↪ C⁰(I,H)`) is the hypothesis that these maps exist.
  The statement uses the weak topology of `WeakSpace 𝕜 W`; `Σ` is weakly closed when `IsClosed K`
  in `WeakSpace 𝕜 H`.

Not formalized (left out and not proven):

* **Corollary 3.8** and **Theorem 3.7** (norm equivalence (3.7) for `F`, and the identification
  `X_H = X_{H₀}`). The proofs rest on Kato smoothing (Proposition 3.13), Plancherel (Lemma 3.1)
  and Kato–Rellich, none of which is in Mathlib. The bound (3.7) therefore enters
  `remark311_ceaType` only as a hypothesis.
* **Existence of a minimiser** over `H¹(I, Σ)` (stated in the text after Proposition 4.1 as a
  consequence). It needs weak sequential compactness of bounded sets and weak lower semicontinuity
  of `F`, which are not assembled here; only the closedness part is proven.
* **Proposition 2.4, Proposition 2.7, Proposition 3.20, Corollary 3.23** (Hilbert structure of
  `X_H`, density of smooth functions, the dual least-squares functional `E*` and its strong
  convexity). They need Bochner spaces `L²(I, H)` with the graph-type inner product (2.5) and
  Duhamel formulas, which are not formalized here.

The abstract statements are general: the paper's Hilbert space `H` is a normed space over
`𝕜` with `RCLike 𝕜`, and no separability or self-adjointness is used.
-/

namespace LeanDLRA.Literature.P2405_18094

/-- **Abstract core of Remark 3.11 (arXiv 2405.18094), Céa-type quasi-optimality.**

Let `F : V → ℝ` and `v*` be a reference point in a normed space `V`. Assume the two-sided
bounds `c₁ ‖v − v*‖ ≤ √(F v) ≤ c₂ ‖v − v*‖` for all `v`, with `c₁ > 0` and `c₂ ≥ 0`. Let
`ṽ ∈ S` minimise `F` over `S`. Then for every `v ∈ S`,
`‖ṽ − v*‖ ≤ (c₂ / c₁) ‖v − v*‖`, and `‖ṽ − v*‖ ≤ (c₂ / c₁) inf_{v ∈ S} ‖v − v*‖`.

This is the abstract argument behind the paper's remark that a constrained minimiser of
`F` over `H¹(I, Σ)` is quasi-optimal in `H¹(I, Σ)`. The paper's norm equivalence (3.7) for the
least-squares functional is an input here, not a consequence of this theorem. -/
theorem ceaType_of_normEquiv {V : Type*} [NormedAddCommGroup V] (F : V → ℝ)
    (vStar : V) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hlow : ∀ v : V, c₁ * ‖v - vStar‖ ≤ Real.sqrt (F v))
    (hup : ∀ v : V, Real.sqrt (F v) ≤ c₂ * ‖v - vStar‖)
    {S : Set V} {vt : V} (hvt : vt ∈ S) (hmin : ∀ v ∈ S, F vt ≤ F v) :
    (∀ v ∈ S, ‖vt - vStar‖ ≤ c₂ / c₁ * ‖v - vStar‖) ∧
      ‖vt - vStar‖ ≤ c₂ / c₁ * sInf ((fun v => ‖v - vStar‖) '' S) := by
  have hpt : ∀ v ∈ S, c₁ * ‖vt - vStar‖ ≤ c₂ * ‖v - vStar‖ := fun v hv =>
    (hlow vt).trans ((Real.sqrt_le_sqrt (hmin v hv)).trans (hup v))
  have hpt' : ∀ v ∈ S, ‖vt - vStar‖ ≤ c₂ / c₁ * ‖v - vStar‖ := by
    intro v hv
    have h := hpt v hv
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
    linarith [mul_comm (‖vt - vStar‖) c₁]
  refine ⟨hpt', ?_⟩
  have hk : 0 ≤ c₂ / c₁ := div_nonneg hc₂ hc₁.le
  rcases hk.eq_or_lt with h0 | hpos
  · have h := hpt' vt hvt
    rw [← h0, zero_mul] at h
    rw [← h0, zero_mul]
    exact h
  · have hs : ‖vt - vStar‖ / (c₂ / c₁) ≤ sInf ((fun v => ‖v - vStar‖) '' S) := by
      apply le_csInf (Set.Nonempty.image _ ⟨vt, hvt⟩)
      rintro _ ⟨v, hv, rfl⟩
      change ‖vt - vStar‖ / (c₂ / c₁) ≤ ‖v - vStar‖
      rw [div_le_iff₀ hpos, mul_comm]
      exact hpt' v hv
    have h := (div_le_iff₀ hpos).1 hs
    rw [mul_comm]
    exact h

/-- **Remark 3.11 of arXiv 2405.18094 with the paper's constants.**

Assume the paper's two-sided bound (3.7) for `F` (with `γ ∈ ℕ`, `α > 0`, `C ≥ 0`, `T ≥ 0`):
`α/(1+T)^γ ‖v − v*‖ ≤ √(F v) ≤ C(1+T) ‖v − v*‖`. Then a minimiser `ṽ` of `F` over `S` satisfies
`‖ṽ − v*‖ ≤ (C(1+T)^(γ+1)/α) ‖v − v*‖` for all `v ∈ S`, i.e. the constant `C(1+T)^(γ+1)/α`
of Remark 3.11.

Caveat: the bound (3.7) is the conclusion of Corollary 3.8 in the paper, which is not formalized
in this file. It is a hypothesis here, so this theorem is conditional on (3.7). -/
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

end LeanDLRA.Literature.P2405_18094
