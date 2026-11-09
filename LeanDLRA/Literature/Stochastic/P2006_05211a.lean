import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2006.05211: Stability of projector-splitting DLR for random parabolic PDEs

This module formalizes one stability estimate of Kazashi, Nobile and Vidličková, arXiv 2006.05211
(v4), **Theorem 5.4, part 3** (implicit Euler DLR, `f = 0`, `H`-norm), in its abstract core, as a
result **conditional on** the discrete variational formulation (62) (Theorem 4.9 with the implicit
operator evaluation) and on `u^{n+1}` lying in the test space (Lemma 4.6), which the paper proves
and which are taken here as the hypotheses `hvar` and `hu₁`.
The theorem is `implicit_dlr_norm_le`: on a real inner product space `E`, let `T` be a subspace
(the test space of (62)), let `L` be a bounded operator with `⟪L x, x⟫ ≥ 0` (the paper's
coercivity (4) with constant `C_L ≥ 0`), and let `h ≥ 0` be the step size. If `u₁ ∈ T` satisfies
the implicit variational identity `⟪u₁ - u₀, v⟫ + h ⟪L u₁, v⟫ = 0` for every test vector `v ∈ T`,
then `‖u₁‖ ≤ ‖u₀‖`. The proof is the paper's: test with `v = u₁`.

What is and is not in the statement, relative to the paper:
* The paper's `𝓛` acts on a Gelfand triple `(V, H, V')` of random fields with the Bochner
  integral and the discrete measure `ρ̂`. Here `E` is an abstract inner product space; the paper's
  `H`-norm `‖·‖_{H,L²_ρ̂}` is the norm of `E`. The fully discrete space `V_h ⊗ L²_ρ̂` of the paper
  is finite-dimensional, so its form `⟨·,·⟩_{𝓛,ρ̂}` is `⟪L ·, ·⟫` for a bounded `L`.
* `T` is an arbitrary subspace. The paper's test space in (62) is `V_h ⊕ 𝒯_{Ũ^{n+1} Yⁿ} 𝓜_R`
  (mean part plus tangent part), a subspace; taking `T` to be it, `hvar` is (62) with `f = 0`
  and `hu₁` is Lemma 4.6, and the conclusion is Theorem 5.4(3). Neither (62) nor Lemma 4.6 is
  proved here.
* The coercivity constant `C_L > 0` of (4) is replaced by mere nonnegativity of `⟪L x, x⟫`.
* Not formalized: Theorem 5.4 part 1 (energy estimate with `C_L Δt Σ‖u^{n+1}‖²_V`), part 2 (the
  symmetric `𝓛`-norm estimate), part 4 (the symmetric `𝓛`-norm decrease), the `f ≠ 0` estimates,
  and the Gelfand-triple setting. Also not formalized: Lemmas 4.2, 4.6, 4.8, 4.12, 4.16 (Lemma 5.3
  is in `P2006_05211b`), the discrete variational formulation of Theorems 4.9 and 4.14 (taken as
  the hypothesis `hvar`), Theorem 5.5 (explicit Euler CFL, which needs the inverse inequality
  (22)), the semi-implicit scheme, and the existence of discrete solutions.
* Relation to the library: `LeanDLRA.galerkin_implicitEuler_norm_le` (Foundations/OneSided.lean)
  already gives norm decay for the projected implicit Galerkin step `x₁ = P (x₀ + h F(t, x₁))` with
  a dissipative field. The theorem here is stated in the variational form with a subspace test
  space, which is the form the paper uses, and needs no projector equation. It does not use the
  library's projector theory.

The core definitions used are none from `LeanDLRA` (only Mathlib's inner product space and
continuous linear maps). The imports are those already in the file header.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2006_05211

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Theorem 5.4, part 3 (f = 0, implicit Euler DLR), abstract core, arXiv 2006.05211**,
conditional on the discrete variational formulation (62) (`hvar`, Theorem 4.9) and on Lemma 4.6
(`hu₁`), which the paper proves and which are assumed here.
Let `T` be a subspace of `E` (the test space of (62)), `L` a bounded operator with
`⟪L x, x⟫ ≥ 0`, and `h ≥ 0`. If `u₁ ∈ T` and `⟪u₁ - u₀, v⟫ + h ⟪L u₁, v⟫ = 0` for all `v ∈ T`,
then `‖u₁‖ ≤ ‖u₀‖`. Unconditional in `h`: no CFL restriction appears. -/
theorem implicit_dlr_norm_le {T : Submodule ℝ E} {L : E →L[ℝ] E} (hL : ∀ x, 0 ≤ ⟪L x, x⟫)
    {h : ℝ} (hh : 0 ≤ h) {u₀ u₁ : E} (hu₁ : u₁ ∈ T)
    (hvar : ∀ v ∈ T, ⟪u₁ - u₀, v⟫ + h * ⟪L u₁, v⟫ = 0) :
    ‖u₁‖ ≤ ‖u₀‖ := by
  have h1 := hvar u₁ hu₁
  rw [inner_sub_left] at h1
  have hs : ⟪u₁, u₁⟫ = ‖u₁‖ ^ 2 := real_inner_self_eq_norm_sq u₁
  have h2 : 0 ≤ h * ⟪L u₁, u₁⟫ := mul_nonneg hh (hL u₁)
  have h3 : ‖u₁‖ ^ 2 ≤ ⟪u₀, u₁⟫ := by linarith
  have h4 : ⟪u₀, u₁⟫ ≤ ‖u₀‖ * ‖u₁‖ := real_inner_le_norm u₀ u₁
  nlinarith [norm_nonneg u₁, norm_nonneg u₀]

/-- Non-vacuity: on `E = ℝ` with `T = ℝ`, `L = id`, `h = 1`, `u₀ = 1`, `u₁ = 1/2` the
hypotheses of `implicit_dlr_norm_le` hold (`(1/2 - 1) v + (1/2) v = 0`), and the conclusion
`1/2 ≤ 1` follows. -/
example : ‖(1 / 2 : ℝ)‖ ≤ ‖(1 : ℝ)‖ := by
  apply implicit_dlr_norm_le (T := ⊤) (L := ContinuousLinearMap.id ℝ ℝ) (h := 1)
    (u₀ := 1) (u₁ := 1 / 2)
  · intro x
    simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    positivity
  · norm_num
  · exact Submodule.mem_top
  · intro v _
    simp only [ContinuousLinearMap.id_apply, one_mul]
    rw [← inner_add_left]
    norm_num

end LeanDLRA.Literature.P2006_05211
