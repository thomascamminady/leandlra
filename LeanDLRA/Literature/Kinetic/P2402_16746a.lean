import LeanDLRA.Classical.SVD
import LeanDLRA.Integrators.BUG
import LeanDLRA.Literature.Kinetic.P1906_09940a
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2402.16746: AP energy-stable DLRA for thermal radiative transfer

This module formalizes Patwardhan, Frank and Kusch for the fully discrete schemes themselves, not
for an abstract core: the staggered periodic grid (`Dp`, `Dm`), the `P_N` closure with
Gauss-Legendre data (`IsGaussLegendre`, `gaussT`, `gaussT_flux`, `Params.Apl`, `Params.Ami`, `bvec`,
`betaN`), the macro-micro scheme (3.1), (3.3) (`Params.IsFullStep`), the fixed-rank BUG integrator
(4.2)-(4.6) (`Params.IsFixedRankStep`) and the rank-adaptive integrator of Section 4.2
(`Params.IsAdaptiveStep`).

## Main results

* Theorem 1: `Params.theorem_1` at `ε = 0`, and `Params.theorem_1_tendsto` as a genuine limit.
* Theorem 2: `Params.theorem_2`, with the paper's quantifiers and constants;
  `Params.theorem_2_sharp` with the better constant `1/(4 c)` in place of `1/(5 c β_N)`, for any
  factorization of the flux matrix; `Params.theorem_2_zero_boundary` for zero boundary values. The
  estimate itself is `Params.energy_le_of_tested`, which only tests the micro equation with the new
  iterate.
* Theorem 3: `Params.theorem_3` at `ε = 0`, and `Params.theorem_3_tendsto` as a genuine limit.
* Theorem 4: `Params.theorem_4`, through the Galerkin identity `Params.IsSStep.tested`.
* Theorem 5: `Params.theorem_5`, `Params.theorem_5_adaptive`, and
  `mass_conservation_of_boundary_flux` for zero or periodic boundary values.
* Lemma 1: `Params.lemma_1`.
* Theorem 6: `Params.theorem_6` at `ε = 0`, and `Params.theorem_6_tendsto` as a genuine limit, from
  `Params.IsAdaptiveStep.norm_sub_le`, an `O(ε)` bound uniform in the bases and the ranks.
* Lemmas 2 and 3: `lemma_2_minus`, `lemma_2_plus`, `lemma_3`, for scalar sequences on the
  periodic grid (the paper's vector-valued forms follow componentwise).

## False as printed, with a formal counterexample

* Lemma 4, `gᵀ A² g = v̂ᵀ M² v̂`: false (`lemma_4_false`), for `P₁` with the two-point rule.
* Lemma 6, `∑ |(A⁺D⁺ + A⁻D⁻) g|² ≤ 2 β_N ∑ (D⁺g)ᵀ A² D⁺g`: false (`lemma_6_false`), for the same
  data on three cells.

Both are used in the paper's proof of Theorem 2. They are quoted from Lemmas 3.4 and 3.6 of
arXiv 2212.12012, whose printed forms (Lemma 3.6 there is stated for `ℒ = A⁺D⁻ + A⁻D⁺` with the
constant `2`) are refuted in `P2212_12012a` (`lemma_3_4_printed_false`,
`lemma_3_6_printed_false`). Theorems 2, 4 survive: what is true is the mode-wise
estimate `mode_bound` together with `first_moment_le`, and it gives more than (3.4) asks for.

## Gaps in the paper's proofs, with what is proved instead

* Theorem 3: the assumption "`S_Lᵀ ∑ σ X Xᵀ` is invertible" cannot hold at `ε = 0` for rank `r ≥ 2`
  (`Params.theorem_3_invertible_rank_le_one`). `Params.theorem_3` assumes `bᵀ Vⁿ ≠ 0` and
  `Xⁿᵀ Ψδ⁰(acT) ≠ 0` instead, the first of which the paper leaves implicit.
* Theorem 6: the proof applies Lemma 1, which needs `Ŝ^rem` invertible, but at `ε = 0` one has
  `Ŝ^rem = 0` (`Params.IsAdaptiveStep.Sr_eq_zero`). The theorem is true, and needs no invertibility
  at all, because the truncation only touches `K̂^rem`, which vanishes in the limit.
* Both proofs set `ε = 0` in the scheme, while the bases depend on `ε`. The `tendsto` theorems prove
  the actual limit, in which the bases need not converge.

## Differences from the paper

* The PDE (2.1) and the derivation of the modal system (2.6) are not formalized: the schemes are the
  starting point. "Consistent discretization" in Theorems 1, 3 is proved as in the paper, by
  exhibiting the explicit Euler, centred difference scheme (`Params.diffOp`). A Taylor expansion of
  that stencil is not formalized, and neither does the paper give one.
* Grid: `ZMod Nx`, with `Δx > 0` arbitrary. Theorems 3, 4, 6 are for the periodic grid only.
  Theorems 2, 4 hold for `ε ≥ 0`, which includes the limit scheme.
* Indices: `Fin N` carries the moments `1, …, N`, so `g₁` has index `0`. Row `j` of `g` is
  `g_{j+1/2}`. The flux multiplies rows from the right, and `A^±` are symmetric.
* `Ψ` is a parameter: `Ψ = 4 (Tⁿ)³` is (3.1), `Ψ = 1` is (3.3). The printed `δ⁰(a c Ψ T + ε² h)` of
  (3.1b) is read as `a c Ψ_{j+1/2} δ⁰T + ε² δ⁰h`, as the proof of Theorem 1 does (`Params.source`).
* `theorem_1_tendsto`, `theorem_3_tendsto` and `theorem_6_tendsto` assume `Ψ ≥ 0`, so that
  `1 + 2 a Ψ/cν ≠ 0`, which the paper uses silently.
* Misprints: Theorem 3 lacks the factor `Ψ` of Theorem 1 and of (4.8), and the version with `Ψ` is
  proved. Theorem 5 has "`n ∈ {0, 1}`". Lemma 5's last term has the sign opposite to (A.13), and
  `mode_bound` uses the sign of (A.13). In Section 4.2, `S̃ⁿ` is `M̂ Sⁿ N̂ᵀ`, `V̂^ap` is `b/γ₁`, and
  `K̂^ap` is the first column of `X̂ Ŝ`, which is proportional to `(σ^a)⁻¹Ψδ⁰(acT)` at `ε = 0` only.
* Theorem 5 is for linear emission, as its proof says.
* Orthonormal bases may have any number of columns, which covers rank deficiency. The truncation may
  keep any selection of singular triples. Lemma 1 also assumes `S^ap`, `R₂` and `S^rem` invertible.
* `theorem_6_tendsto` has index types independent of `ε`. `IsAdaptiveStep.norm_sub_le` has no such
  restriction.

## Non-vacuity

`isGaussLegendre_two_point` is the rule for `N = 1`. Existence of the Gauss-Legendre rule for every
`N` is classical but not reproved here; `exists_isFluxFactorization` gives, for every `N`, data for
`Params.theorem_2_sharp`. Steps exist: `Params.exists_isFullStep`, `Params.exists_isFixedRankStep`,
`Params.exists_isAdaptiveStep`.

## Related

Theorem 7 is the sibling module, `P2402_16746b`. Its `APEnergy.energy_le_core`, which appeared while
this module was written and which the checker snapshot could not see, is the same estimate as
`Params.energy_le_of_tested`, for `ε > 0`. It could replace the latter, and with it `mode_bound`.
The bound `β_N ≤ π` behind the paper's closing remark in Appendix A is
`LeanDLRA.OpenProblems.Stability.gaussQuadrature_weight_le`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2402_16746

open Matrix

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### The staggered periodic grid -/

section Grid

variable {Nx : ℕ} [NeZero Nx]

/-- The forward difference on `ZMod Nx`. On interface values it is `D⁺` of arXiv 2402.16746,
`(D⁺φ)_{j+1/2} = (φ_{j+3/2} - φ_{j+1/2})/Δx`, and on cell values it is `δ⁰`,
`(δ⁰T)_{j+1/2} = (T_{j+1} - T_j)/Δx`. Interface `j + 1/2` carries the index `j`. -/
noncomputable def Dp (Δx : ℝ) (φ : ZMod Nx → ℝ) (j : ZMod Nx) : ℝ := (φ (j + 1) - φ j) / Δx

/-- The backward difference on `ZMod Nx`. On interface values it is both `D⁻` and `D⁰` of
arXiv 2402.16746, `(D⁰φ)_j = (D⁻φ)_{j+1/2} = (φ_{j+1/2} - φ_{j-1/2})/Δx`. -/
noncomputable def Dm (Δx : ℝ) (φ : ZMod Nx → ℝ) (j : ZMod Nx) : ℝ := (φ j - φ (j - 1)) / Δx

/-- `D⁺` applied to every column of `Y`. -/
noncomputable def DpM {ι : Type*} (Δx : ℝ) (Y : Matrix (ZMod Nx) ι ℝ) : Matrix (ZMod Nx) ι ℝ :=
  Matrix.of fun j k => Dp Δx (fun i => Y i k) j

/-- `D⁻` applied to every column of `Y`. -/
noncomputable def DmM {ι : Type*} (Δx : ℝ) (Y : Matrix (ZMod Nx) ι ℝ) : Matrix (ZMod Nx) ι ℝ :=
  Matrix.of fun j k => Dm Δx (fun i => Y i k) j

omit [NeZero Nx] in
lemma DpM_mul {ι κ : Type*} [Fintype κ] (Δx : ℝ) (Y : Matrix (ZMod Nx) κ ℝ) (B : Matrix κ ι ℝ) :
    DpM Δx (Y * B) = DpM Δx Y * B := by
  ext j k
  simp only [DpM, Dp, Matrix.of_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [NeZero Nx] in
lemma DmM_mul {ι κ : Type*} [Fintype κ] (Δx : ℝ) (Y : Matrix (ZMod Nx) κ ℝ) (B : Matrix κ ι ℝ) :
    DmM Δx (Y * B) = DmM Δx Y * B := by
  ext j k
  simp only [DmM, Dm, Matrix.of_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sum_add_one (f : ZMod Nx → ℝ) : ∑ j, f (j + 1) = ∑ j, f j :=
  Equiv.sum_comp (Equiv.addRight 1) f

lemma sum_sub_one (f : ZMod Nx → ℝ) : ∑ j, f (j - 1) = ∑ j, f j :=
  Equiv.sum_comp (Equiv.subRight 1) f

/-- arXiv 2402.16746, Lemma 2 (summation by parts), the periodic case with `D⁻` on the right, for
scalar sequences (the paper's `ℝ^N`-valued form follows componentwise; zero boundary values, which
the paper also allows, are not treated). -/
theorem lemma_2_minus (Δx : ℝ) (ζ φ : ZMod Nx → ℝ) :
    ∑ j, ζ j * Dm Δx φ j = - ∑ j, Dp Δx ζ j * φ j := by
  have h : ∑ j, ζ j * φ (j - 1) = ∑ j, ζ (j + 1) * φ j := by
    rw [← sum_add_one (fun j => ζ j * φ (j - 1))]
    simp
  have e1 : ∑ j, ζ j * Dm Δx φ j = (∑ j, ζ j * φ j - ∑ j, ζ j * φ (j - 1)) / Δx := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by simp only [Dm]; ring
  have e2 : ∑ j, Dp Δx ζ j * φ j = (∑ j, ζ (j + 1) * φ j - ∑ j, ζ j * φ j) / Δx := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by simp only [Dp]; ring
  rw [e1, e2, h]
  ring

/-- arXiv 2402.16746, Lemma 2 (summation by parts), the periodic case with `D⁺` on the right, for
scalar sequences (the paper's `ℝ^N`-valued form follows componentwise). -/
theorem lemma_2_plus (Δx : ℝ) (ζ φ : ZMod Nx → ℝ) :
    ∑ j, ζ j * Dp Δx φ j = - ∑ j, Dm Δx ζ j * φ j := by
  have h := lemma_2_minus Δx φ ζ
  have e1 : ∑ j, ζ j * Dp Δx φ j = ∑ j, Dp Δx φ j * ζ j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : ∑ j, Dm Δx ζ j * φ j = ∑ j, φ j * Dm Δx ζ j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, e2, h, neg_neg]

lemma sum_Dm_sq (Δx : ℝ) (φ : ZMod Nx → ℝ) : ∑ j, Dm Δx φ j ^ 2 = ∑ j, Dp Δx φ j ^ 2 := by
  rw [← sum_sub_one (fun j => Dp Δx φ j ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Dm, Dp]

lemma sum_mul_Dm_self {Δx : ℝ} (hΔx : Δx ≠ 0) (φ : ZMod Nx → ℝ) :
    ∑ j, φ j * Dm Δx φ j = Δx / 2 * ∑ j, Dp Δx φ j ^ 2 := by
  have h1 : ∑ j, φ (j + 1) ^ 2 = ∑ j, φ j ^ 2 := sum_add_one fun j => φ j ^ 2
  have h2 : ∑ j, φ j * φ (j - 1) = ∑ j, φ (j + 1) * φ j := by
    rw [← sum_add_one (fun j => φ j * φ (j - 1))]
    simp
  have e1 : ∑ j, φ j * Dm Δx φ j = (∑ j, φ j ^ 2 - ∑ j, φ (j + 1) * φ j) / Δx := by
    rw [← h2, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by simp only [Dm]; ring
  have e2 : ∑ j, Dp Δx φ j ^ 2 = (2 * ∑ j, φ j ^ 2 - 2 * ∑ j, φ (j + 1) * φ j) / Δx ^ 2 := by
    have e (j : ZMod Nx) : Dp Δx φ j ^ 2 =
        (φ (j + 1) ^ 2 + φ j ^ 2 - 2 * (φ (j + 1) * φ j)) / Δx ^ 2 := by
      simp only [Dp, div_pow]
      ring
    simp only [e, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, h1]
    ring
  rw [e1, e2]
  field_simp

lemma sum_mul_Dp_self {Δx : ℝ} (hΔx : Δx ≠ 0) (φ : ZMod Nx → ℝ) :
    ∑ j, φ j * Dp Δx φ j = - (Δx / 2 * ∑ j, Dp Δx φ j ^ 2) := by
  rw [lemma_2_plus, ← sum_mul_Dm_self hΔx]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- arXiv 2402.16746, Lemma 3: `∑ (D⁺φ)² ≤ 4/Δx² ∑ φ²`, for scalar sequences on the periodic grid
(the paper's `ℝ^{N+1}`-valued form follows by summing over the components). -/
theorem lemma_3 {Δx : ℝ} (hΔx : Δx ≠ 0) (φ : ZMod Nx → ℝ) :
    ∑ j, Dp Δx φ j ^ 2 ≤ 4 / Δx ^ 2 * ∑ j, φ j ^ 2 := by
  have hb (j : ZMod Nx) : Dp Δx φ j ^ 2 ≤ (2 * φ (j + 1) ^ 2 + 2 * φ j ^ 2) / Δx ^ 2 := by
    simp only [Dp, div_pow]
    gcongr
    nlinarith [sq_nonneg (φ (j + 1) + φ j)]
  calc ∑ j, Dp Δx φ j ^ 2
      ≤ ∑ j, (2 * φ (j + 1) ^ 2 + 2 * φ j ^ 2) / Δx ^ 2 := Finset.sum_le_sum fun j _ => hb j
    _ = 4 / Δx ^ 2 * ∑ j, φ j ^ 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_add_one (fun j => φ j ^ 2)]
      ring

/-- The positive part `(m + |m|)/2`, an entry of `(M + |M|)/2`. -/
noncomputable def upos (m : ℝ) : ℝ := (m + |m|) / 2

/-- The negative part `(m - |m|)/2`, an entry of `(M - |M|)/2`. -/
noncomputable def uneg (m : ℝ) : ℝ := (m - |m|) / 2

lemma upos_mul_uneg (m : ℝ) : upos m * uneg m = 0 := by
  have : |m| ^ 2 = m ^ 2 := sq_abs m
  simp only [upos, uneg]
  nlinarith

lemma upos_sq_add_uneg_sq (m : ℝ) : upos m ^ 2 + uneg m ^ 2 = m ^ 2 := by
  have : |m| ^ 2 = m ^ 2 := sq_abs m
  simp only [upos, uneg]
  nlinarith

lemma upos_sub_uneg (m : ℝ) : upos m - uneg m = |m| := by
  simp only [upos, uneg]
  ring

/-- The energy estimate of one quadrature mode: the transport term of the upwind flux, the Young
inequality for the time difference and the CFL condition, in the sharp form
`Δt ≤ (2 ε Δx / |m| + σ₀ Δx² / m²) / (4 c)`. -/
lemma mode_bound {ε c Δt Δx σ₀ m : ℝ} (hc : 0 < c) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hσ₀ : 0 ≤ σ₀)
    (hcfl : m ≠ 0 → Δt ≤ 1 / (4 * c) * (2 * ε * Δx / |m| + σ₀ * Δx ^ 2 / m ^ 2))
    (φ ξ : ZMod Nx → ℝ) :
    Δt / 4 * m ^ 2 * ∑ j, Dp Δx φ j ^ 2 ≤
      ε ^ 2 / (4 * c ^ 2 * Δt) * ∑ j, (φ j - ξ j) ^ 2 +
      ε / (2 * c) * (upos m * ∑ j, φ j * Dm Δx ξ j + uneg m * ∑ j, φ j * Dp Δx ξ j) +
      σ₀ / (2 * c) * ∑ j, φ j ^ 2 := by
  have hΔx' : Δx ≠ 0 := hΔx.ne'
  set S := ∑ j, Dp Δx φ j ^ 2 with hS
  set Φ := ∑ j, φ j ^ 2 with hΦ
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΦ0 : 0 ≤ Φ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSΦ : S ≤ 4 / Δx ^ 2 * Φ := lemma_3 hΔx' φ
  set ψ : ZMod Nx → ℝ := fun j => φ j - ξ j with hψ
  set r : ZMod Nx → ℝ := fun j => upos m * Dp Δx φ j + uneg m * Dm Δx φ j with hr
  -- the transport term
  have hDm : ∑ j, φ j * Dm Δx ξ j = Δx / 2 * S + ∑ j, Dp Δx φ j * ψ j := by
    have e : ∑ j, φ j * Dm Δx ξ j = ∑ j, φ j * Dm Δx φ j - ∑ j, φ j * Dm Δx ψ j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hψ, Dm]
      ring
    rw [e, sum_mul_Dm_self hΔx', lemma_2_minus Δx φ ψ]
    ring
  have hDp : ∑ j, φ j * Dp Δx ξ j = - (Δx / 2 * S) + ∑ j, Dm Δx φ j * ψ j := by
    have e : ∑ j, φ j * Dp Δx ξ j = ∑ j, φ j * Dp Δx φ j - ∑ j, φ j * Dp Δx ψ j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hψ, Dp]
      ring
    rw [e, sum_mul_Dp_self hΔx', lemma_2_plus Δx φ ψ]
    ring
  have hU : upos m * ∑ j, φ j * Dm Δx ξ j + uneg m * ∑ j, φ j * Dp Δx ξ j =
      |m| * (Δx / 2 * S) + ∑ j, r j * ψ j := by
    have e : ∑ j, r j * ψ j =
        upos m * ∑ j, Dp Δx φ j * ψ j + uneg m * ∑ j, Dm Δx φ j * ψ j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [hr]; ring
    rw [hDm, hDp, e, ← upos_sub_uneg]
    ring
  -- the size of `r`
  have hrr : ∑ j, r j ^ 2 = m ^ 2 * S := by
    have e (j : ZMod Nx) : r j ^ 2 = upos m ^ 2 * Dp Δx φ j ^ 2 + uneg m ^ 2 * Dm Δx φ j ^ 2 +
        2 * (upos m * uneg m) * (Dp Δx φ j * Dm Δx φ j) := by
      simp only [hr]
      ring
    simp only [e, upos_mul_uneg, mul_zero, zero_mul, add_zero]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_Dm_sq, ← hS,
      ← upos_sq_add_uneg_sq m]
    ring
  -- Young's inequality for the time difference
  have hY : 0 ≤ ε ^ 2 / (4 * c ^ 2 * Δt) * ∑ j, ψ j ^ 2 + ε / (2 * c) * ∑ j, r j * ψ j +
      Δt / 4 * ∑ j, r j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun j _ => ?_
    have e : ε ^ 2 / (4 * c ^ 2 * Δt) * ψ j ^ 2 + ε / (2 * c) * (r j * ψ j) +
        Δt / 4 * r j ^ 2 = Δt / 4 * (r j + ε / (c * Δt) * ψ j) ^ 2 := by
      field_simp
      ring
    rw [e]
    positivity
  -- the CFL condition
  have hmain : 0 ≤ (ε * |m| * Δx / (4 * c) - Δt / 2 * m ^ 2) * S + σ₀ / (2 * c) * Φ := by
    by_cases hm : m = 0
    · subst hm
      simp only [abs_zero, mul_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div, zero_add]
      positivity
    · have habs : 0 < |m| := abs_pos.2 hm
      have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
      have hB : Δt / 2 * m ^ 2 - ε * |m| * Δx / (4 * c) ≤ σ₀ * Δx ^ 2 / (8 * c) := by
        have h := hcfl hm
        have hm2pos : 0 < m ^ 2 := by positivity
        have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ m ^ 2 / 2)
        have e : 1 / (4 * c) * (2 * ε * Δx / |m| + σ₀ * Δx ^ 2 / m ^ 2) * (m ^ 2 / 2) =
            ε * |m| * Δx / (4 * c) + σ₀ * Δx ^ 2 / (8 * c) := by
          rw [hm2]
          field_simp
          ring
        rw [e] at h'
        linarith
      by_cases hsign : Δt / 2 * m ^ 2 - ε * |m| * Δx / (4 * c) ≤ 0
      · have h1 : 0 ≤ (ε * |m| * Δx / (4 * c) - Δt / 2 * m ^ 2) * S :=
          mul_nonneg (by linarith) hS0
        have h2 : 0 ≤ σ₀ / (2 * c) * Φ := by positivity
        linarith
      · replace hsign := not_le.1 hsign
        have h1 : (Δt / 2 * m ^ 2 - ε * |m| * Δx / (4 * c)) * S ≤
            (Δt / 2 * m ^ 2 - ε * |m| * Δx / (4 * c)) * (4 / Δx ^ 2 * Φ) :=
          mul_le_mul_of_nonneg_left hSΦ hsign.le
        have h2 : (Δt / 2 * m ^ 2 - ε * |m| * Δx / (4 * c)) * (4 / Δx ^ 2 * Φ) ≤
            σ₀ * Δx ^ 2 / (8 * c) * (4 / Δx ^ 2 * Φ) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
        have h3 : σ₀ * Δx ^ 2 / (8 * c) * (4 / Δx ^ 2 * Φ) = σ₀ / (2 * c) * Φ := by
          field_simp
          ring
        nlinarith
  have hsum : ∑ j, (φ j - ξ j) ^ 2 = ∑ j, ψ j ^ 2 := rfl
  rw [hU, hsum]
  rw [hrr] at hY
  have e : ε / (2 * c) * (|m| * (Δx / 2 * S) + ∑ j, r j * ψ j) =
      ε * |m| * Δx / (4 * c) * S + ε / (2 * c) * ∑ j, r j * ψ j := by
    field_simp
    ring
  rw [e]
  nlinarith

end Grid

/-! ### The modal macro-micro scheme -/

/-- `γ₀ = √2`, the `L²(-1, 1)` norm of the Legendre polynomial of degree zero. -/
noncomputable def γ₀ : ℝ := √2

/-- `γ₁ = √(2/3)`, the `L²(-1, 1)` norm of the Legendre polynomial of degree one. -/
noncomputable def γ₁ : ℝ := √(2 / 3)

lemma γ₀_pos : 0 < γ₀ := Real.sqrt_pos.2 (by norm_num)

lemma γ₁_pos : 0 < γ₁ := Real.sqrt_pos.2 (by norm_num)

lemma γ₀_sq : γ₀ ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma γ₁_sq : γ₁ ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)

/-- The physical and discretization parameters of arXiv 2402.16746: the radiation constant `a`, the
speed of light `c`, the specific heat `cν`, the steps `Δt`, `Δx`, the absorption cross-section at
cell centres `σc i = σ^a_i` and at interfaces `σf j = σ^a_{j+1/2}`, the quadrature nodes `μ` and the
matrix `Tm` (the paper's `T ∈ ℝ^{N × (N+1)}`). The scaling `ε` is not a field, since Theorems 1,
3 and 6 vary it. -/
structure Params (Nx N : ℕ) where
  /-- the radiation constant -/
  a : ℝ
  /-- the speed of light -/
  c : ℝ
  /-- the specific heat -/
  cν : ℝ
  /-- the time step -/
  Δt : ℝ
  /-- the mesh width -/
  Δx : ℝ
  /-- `σ^a_i` -/
  σc : ZMod Nx → ℝ
  /-- `σ^a_{j+1/2}` -/
  σf : ZMod Nx → ℝ
  /-- the quadrature nodes `μ₁, …, μ_{N+1}` -/
  μ : Fin (N + 1) → ℝ
  /-- the matrix `T`, with `T_{ik} = √w_k P_i(μ_k)` for Gauss-Legendre data -/
  Tm : Matrix (Fin N) (Fin (N + 1)) ℝ

/-- The vector `b = (γ₁, 0, …, 0)ᵀ ∈ ℝ^N`. The first moment `g₁` of the paper has index `0`. -/
noncomputable def bvec (N : ℕ) [NeZero N] : Fin N → ℝ := fun k => if k = 0 then γ₁ else 0

namespace Params

variable {Nx N : ℕ} (P : Params Nx N)

/-- `κ = 2 / cν`. -/
noncomputable def κ : ℝ := 2 / P.cν

/-- `A⁺ = ½ T (M + |M|) Tᵀ`. -/
noncomputable def Apl : Matrix (Fin N) (Fin N) ℝ :=
  P.Tm * diagonal (fun k => upos (P.μ k)) * P.Tmᵀ

/-- `A⁻ = ½ T (M - |M|) Tᵀ`. -/
noncomputable def Ami : Matrix (Fin N) (Fin N) ℝ :=
  P.Tm * diagonal (fun k => uneg (P.μ k)) * P.Tmᵀ

/-- The flux `𝓛 g_{j+1/2} = (A⁺ D⁻ + A⁻ D⁺) g_{j+1/2}`. Row `j` of `g` is `g_{j+1/2}`, so this is a
right multiplication, and `A^±` are symmetric. -/
noncomputable def flux (Y : Matrix (ZMod Nx) (Fin N) ℝ) : Matrix (ZMod Nx) (Fin N) ℝ :=
  DmM P.Δx Y * P.Apl + DpM P.Δx Y * P.Ami

/-- The term `a c Ψ_{j+1/2} δ⁰T_{j+1/2} + ε² δ⁰h_{j+1/2}` of (3.1b), with
`Ψ_{j+1/2} = (Ψ_{j+1} + Ψ_j)/2`. The paper prints `δ⁰(a c Ψ T + ε² h)`, and its proof of Theorem 1
(eq. (3.2)) shows that `Ψ_{j+1/2}` stands in front of the difference. For `Ψ = 1` both agree. -/
noncomputable def source (ε : ℝ) (Ψ T h : ZMod Nx → ℝ) (j : ZMod Nx) : ℝ :=
  P.a * P.c * ((Ψ (j + 1) + Ψ j) / 2) * Dp P.Δx T j + ε ^ 2 * Dp P.Δx h j

/-- The update `Tⁿ, hⁿ, gⁿ ↦ Tⁿ⁺¹, hⁿ⁺¹, gⁿ⁺¹` of arXiv 2402.16746, scheme (3.1) with
`Ψ i = 4 (Tⁿ_i)³`, and scheme (3.3) with `Ψ = 1`. -/
structure IsFullStep [NeZero N] (ε : ℝ) (Ψ T h : ZMod Nx → ℝ) (g : Matrix (ZMod Nx) (Fin N) ℝ)
    (T' h' : ZMod Nx → ℝ) (g' : Matrix (ZMod Nx) (Fin N) ℝ) : Prop where
  /-- (3.1a) -/
  macro_eq : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * Ψ i * h' i +
    γ₁ / 2 * Dm P.Δx (fun j => g' j 0) i = - P.σc i * h' i
  /-- (3.1b) -/
  micro_eq : ∀ j k, ε ^ 2 / P.c * ((g' j k - g j k) / P.Δt) + ε * P.flux g j k +
    bvec N k * P.source ε Ψ T h j = - P.σf j * g' j k
  /-- (3.1c) -/
  temp_eq : ∀ i, (T' i - T i) / P.Δt = P.κ * P.σc i * h' i

/-- The energy `eⁿ = ‖a Tⁿ + ε²/c hⁿ‖² + ‖ε/(γ₀ c) gⁿ‖² + ‖√(a cν/2) Tⁿ‖²` of arXiv 2402.16746,
Theorem 2, where `‖u‖² = ∑ u_i² Δx`. -/
noncomputable def energy [NeZero Nx] (ε : ℝ) (T h : ZMod Nx → ℝ)
    (g : Matrix (ZMod Nx) (Fin N) ℝ) : ℝ :=
  ∑ i, (P.a * T i + ε ^ 2 / P.c * h i) ^ 2 * P.Δx +
    ∑ j, ∑ k, (ε / (γ₀ * P.c) * g j k) ^ 2 * P.Δx +
    ∑ i, (√(P.a * P.cν / 2) * T i) ^ 2 * P.Δx

/-- The standing assumptions of arXiv 2402.16746: positive constants and steps, and
`σ^a ≥ σ₀ > 0`. -/
structure Admissible (σ₀ : ℝ) : Prop where
  a_pos : 0 < P.a
  c_pos : 0 < P.c
  cν_pos : 0 < P.cν
  Δt_pos : 0 < P.Δt
  Δx_pos : 0 < P.Δx
  σ₀_pos : 0 < σ₀
  σc_ge : ∀ i, σ₀ ≤ P.σc i
  σf_ge : ∀ j, σ₀ ≤ P.σf j

/-- The residual of the micro equation (3.3b), written with old value `gold`. The equation is
`microRes = 0`, and the Galerkin steps only annihilate its projection. -/
noncomputable def microRes [NeZero Nx] [NeZero N] (ε : ℝ) (Ψ T h : ZMod Nx → ℝ)
    (gold g' : Matrix (ZMod Nx) (Fin N) ℝ) : Matrix (ZMod Nx) (Fin N) ℝ :=
  (ε ^ 2 / (P.c * P.Δt)) • (g' - gold) + ε • P.flux gold +
    vecMulVec (P.source ε Ψ T h) (bvec N) + diagonal P.σf * g'

end Params

/-- What the energy analysis uses of the angular discretization: `T Tᵀ = 1` and the first column of
the full flux matrix, `(A_f)_{i,0} = a₀ δ_{i,1}` with `a₀ = 1/√3`. Here `t₀` is the row of the full
matrix `T_f` that belongs to `P₀`. Gauss-Legendre data satisfy this (`isFluxFactorization_gauss`),
and so does any orthogonal diagonalization of `A_f` (`exists_isFluxFactorization`). -/
structure IsFluxFactorization {N : ℕ} [NeZero N] (μ : Fin (N + 1) → ℝ)
    (Tm : Matrix (Fin N) (Fin (N + 1)) ℝ) (t₀ : Fin (N + 1) → ℝ) : Prop where
  orth : Tm * Tmᵀ = 1
  t₀_norm : ∑ k, t₀ k ^ 2 = 1
  first_col : ∀ i, ∑ k, Tm i k * μ k * t₀ k = if i = 0 then 1 / √3 else 0

section Lift

variable {J : Type*} [Fintype J] {N : ℕ}

lemma sum_sq_mul_transpose {Tm : Matrix (Fin N) (Fin (N + 1)) ℝ} (hT : Tm * Tmᵀ = 1)
    (Y : Matrix J (Fin N) ℝ) : ∑ j, ∑ k, (Y * Tm) j k ^ 2 = ∑ j, ∑ k, Y j k ^ 2 := by
  have h := Frobenius.norm_mul_transpose_of_orthonormal (V := Tmᵀ)
    (by simpa using hT) Y
  rw [Matrix.transpose_transpose] at h
  rw [← Frobenius.norm_sq_eq_sum, ← Frobenius.norm_sq_eq_sum, h]

lemma sum_mul_sandwich (Tm : Matrix (Fin N) (Fin (N + 1)) ℝ) (d : Fin (N + 1) → ℝ)
    (g Y : Matrix J (Fin N) ℝ) :
    ∑ j, ∑ m, g j m * (Y * (Tm * diagonal d * Tmᵀ)) j m =
      ∑ k, d k * ∑ j, (g * Tm) j k * (Y * Tm) j k := by
  have e : Y * (Tm * diagonal d * Tmᵀ) = (Y * Tm * diagonal d) * Tmᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e, ← Frobenius.inner_def, Frobenius.inner_mul_right', Matrix.transpose_transpose,
    Frobenius.inner_def]
  simp only [Matrix.mul_diagonal, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

lemma first_moment_le [NeZero N] {μ : Fin (N + 1) → ℝ} {Tm : Matrix (Fin N) (Fin (N + 1)) ℝ}
    {t₀ : Fin (N + 1) → ℝ} (hF : IsFluxFactorization μ Tm t₀) (y : Fin N → ℝ) :
    y 0 ^ 2 ≤ 3 * ∑ k, μ k ^ 2 * (y ᵥ* Tm) k ^ 2 := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h30 : (√3 : ℝ) ≠ 0 := by positivity
  have e : y 0 / √3 = ∑ k, ((y ᵥ* Tm) k * μ k) * t₀ k := by
    have e1 : y 0 / √3 = ∑ i, y i * ∑ k, Tm i k * μ k * t₀ k := by
      simp only [hF.first_col, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    rw [e1]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => (y ᵥ* Tm) k * μ k) t₀
  rw [← e, hF.t₀_norm, mul_one, div_pow, h3] at hcs
  have e2 : ∑ k, ((y ᵥ* Tm) k * μ k) ^ 2 = ∑ k, μ k ^ 2 * (y ᵥ* Tm) k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [e2] at hcs
  have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).1 hcs
  linarith

end Lift

section Energy

variable {Nx N : ℕ} [NeZero Nx] [NeZero N]

namespace Params

variable (P : Params Nx N)

omit [NeZero N] in
lemma energy_eq (hP : 0 ≤ P.a * P.cν) (ε : ℝ) (T h : ZMod Nx → ℝ)
    (g : Matrix (ZMod Nx) (Fin N) ℝ) :
    P.energy ε T h g = P.Δx * (∑ i, (P.a * T i + ε ^ 2 / P.c * h i) ^ 2 +
      ε ^ 2 / (2 * P.c ^ 2) * ∑ j, ∑ k, g j k ^ 2 + P.a * P.cν / 2 * ∑ i, T i ^ 2) := by
  have hs : √(P.a * P.cν / 2) ^ 2 = P.a * P.cν / 2 := Real.sq_sqrt (by positivity)
  have hg : ∀ j k, (ε / (γ₀ * P.c) * g j k) ^ 2 = ε ^ 2 / (2 * P.c ^ 2) * g j k ^ 2 := by
    intro j k
    rw [mul_pow, div_pow, mul_pow, γ₀_sq]
  have e1 : ∑ i, (P.a * T i + ε ^ 2 / P.c * h i) ^ 2 * P.Δx =
      P.Δx * ∑ i, (P.a * T i + ε ^ 2 / P.c * h i) ^ 2 := by
    rw [← Finset.sum_mul, mul_comm]
  have e2 : ∑ j, ∑ k, (ε / (γ₀ * P.c) * g j k) ^ 2 * P.Δx =
      P.Δx * (ε ^ 2 / (2 * P.c ^ 2) * ∑ j, ∑ k, g j k ^ 2) := by
    simp only [hg, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have e3 : ∑ i, (√(P.a * P.cν / 2) * T i) ^ 2 * P.Δx =
      P.Δx * (P.a * P.cν / 2 * ∑ i, T i ^ 2) := by
    simp only [mul_pow, hs, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [energy, e1, e2, e3]
  ring

omit [NeZero N] in
/-- The flux term in the diagonalizing variables. -/
lemma sum_mul_flux (g gold : Matrix (ZMod Nx) (Fin N) ℝ) :
    ∑ j, ∑ m, g j m * P.flux gold j m =
      ∑ k, (upos (P.μ k) * ∑ j, (g * P.Tm) j k * Dm P.Δx (fun i => (gold * P.Tm) i k) j +
        uneg (P.μ k) * ∑ j, (g * P.Tm) j k * Dp P.Δx (fun i => (gold * P.Tm) i k) j) := by
  have e (j : ZMod Nx) (m : Fin N) : g j m * P.flux gold j m =
      g j m * (DmM P.Δx gold * P.Apl) j m + g j m * (DpM P.Δx gold * P.Ami) j m := by
    simp only [flux, Matrix.add_apply, mul_add]
  simp only [e, Finset.sum_add_distrib]
  rw [Apl, Ami, sum_mul_sandwich, sum_mul_sandwich, ← DmM_mul, ← DpM_mul]
  rfl

/-- **The energy estimate of arXiv 2402.16746, Appendix A**, in the form that covers both the full
scheme and its Galerkin variants: the micro equation is only tested with the new iterate, and the
old value `gold` is arbitrary. The CFL condition is the sharp `Δt ≤ (…) / (4 c)`. -/
theorem energy_le_of_tested {σ₀ : ℝ} (hP : P.Admissible σ₀) {t₀ : Fin (N + 1) → ℝ}
    (hF : IsFluxFactorization P.μ P.Tm t₀) {ε : ℝ}
    (hCFL : ∀ k, P.μ k ≠ 0 →
      P.Δt ≤ 1 / (4 * P.c) * (2 * ε * P.Δx / |P.μ k| + σ₀ * P.Δx ^ 2 / P.μ k ^ 2))
    {T h T' h' : ZMod Nx → ℝ} {gold g' : Matrix (ZMod Nx) (Fin N) ℝ}
    (hmacro : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * h' i +
      γ₁ / 2 * Dm P.Δx (fun j => g' j 0) i = -P.σc i * h' i)
    (htest : ∑ j, ∑ k, g' j k * P.microRes ε 1 T h gold g' j k = 0)
    (htemp : ∀ i, (T' i - T i) / P.Δt = P.κ * P.σc i * h' i) :
    P.energy ε T' h' g' ≤ P.energy ε T h gold := by
  obtain ⟨ha, hc, hcν, hΔt, hΔx, hσ₀, hσc, hσf⟩ := hP
  have hac : 0 ≤ P.a * P.cν := by positivity
  rw [energy_eq P hac, energy_eq P hac]
  refine mul_le_mul_of_nonneg_left ?_ hΔx.le
  set u : ZMod Nx → ℝ := fun i => P.a * T i + ε ^ 2 / P.c * h i with hu
  set u' : ZMod Nx → ℝ := fun i => P.a * T' i + ε ^ 2 / P.c * h' i with hu'
  set d₁ : ZMod Nx → ℝ := Dm P.Δx (fun j => g' j 0) with hd₁
  set Su' := ∑ i, u' i ^ 2 with hSu'
  set Su := ∑ i, u i ^ 2 with hSu
  set Sy := ∑ i, (u' i - u i) ^ 2 with hSy
  set ST' := ∑ i, T' i ^ 2 with hST'
  set ST := ∑ i, T i ^ 2 with hST
  set Sτ := ∑ i, (T' i - T i) ^ 2 with hSτ
  set Sg' := ∑ j, ∑ k, g' j k ^ 2 with hSg'
  set Sgold := ∑ j, ∑ k, gold j k ^ 2 with hSgold
  set Sd := ∑ j, ∑ k, (g' j k - gold j k) ^ 2 with hSd
  set U := ∑ j, ∑ k, g' j k * P.flux gold j k with hU
  set Sσg := ∑ j, P.σf j * ∑ k, g' j k ^ 2 with hSσg
  set Sσh := ∑ i, P.σc i * h' i ^ 2 with hSσh
  set Cross := ∑ i, (u' i - u i) * d₁ i with hCross
  set S₁ := ∑ i, d₁ i ^ 2 with hS₁
  set Sμ := ∑ k, P.μ k ^ 2 * ∑ j, Dp P.Δx (fun i => (g' * P.Tm) i k) j ^ 2 with hSμ
  have hκ : P.a * P.cν / 2 * P.κ = P.a := by
    simp only [κ]
    field_simp
  -- the macro equation, tested with `u'`
  have hA (i : ZMod Nx) : (u' i - u i) / P.Δt + γ₁ / 2 * d₁ i = - P.σc i * h' i := by
    simp only [hu, hu', hd₁]
    linear_combination hmacro i + P.a * htemp i
  have hEA : (Su' - Su + Sy) / (2 * P.Δt) + γ₁ / 2 * ∑ i, u' i * d₁ i =
      - (P.a * ∑ i, P.σc i * (T' i * h' i)) - ε ^ 2 / P.c * Sσh := by
    have e : ∀ i, (u' i ^ 2 - u i ^ 2 + (u' i - u i) ^ 2) / (2 * P.Δt) +
        γ₁ / 2 * (u' i * d₁ i) =
        - (P.a * (P.σc i * (T' i * h' i))) - ε ^ 2 / P.c * (P.σc i * h' i ^ 2) := by
      intro i
      have := hA i
      have e' : (u' i ^ 2 - u i ^ 2 + (u' i - u i) ^ 2) / (2 * P.Δt) =
          u' i * ((u' i - u i) / P.Δt) := by
        field_simp
        ring
      rw [e']
      calc u' i * ((u' i - u i) / P.Δt) + γ₁ / 2 * (u' i * d₁ i)
          = u' i * ((u' i - u i) / P.Δt + γ₁ / 2 * d₁ i) := by ring
        _ = u' i * (- P.σc i * h' i) := by rw [this]
        _ = _ := by simp only [hu']; ring
    have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => e i
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, ← Finset.sum_div] at hsum
    exact hsum
  -- the temperature equation, tested with `a cν / 2 T'`
  have hET : P.a * P.cν / 2 * (ST' - ST + Sτ) / (2 * P.Δt) =
      P.a * ∑ i, P.σc i * (T' i * h' i) := by
    have e : ∀ i, P.a * P.cν / 2 * (T' i ^ 2 - T i ^ 2 + (T' i - T i) ^ 2) / (2 * P.Δt) =
        P.a * (P.σc i * (T' i * h' i)) := by
      intro i
      have e' : P.a * P.cν / 2 * (T' i ^ 2 - T i ^ 2 + (T' i - T i) ^ 2) / (2 * P.Δt) =
          P.a * P.cν / 2 * T' i * ((T' i - T i) / P.Δt) := by
        field_simp
        ring
      rw [e', htemp i]
      linear_combination (T' i * P.σc i * h' i) * hκ
    have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => e i
    simp only [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] at hsum
    exact hsum
  -- the micro equation, tested with `g'`
  have hsrc (j : ZMod Nx) : P.source ε 1 T h j = P.c * Dp P.Δx u j := by
    simp only [source, Dp, hu, Pi.one_apply]
    field_simp
    ring
  have hres (j : ZMod Nx) (k : Fin N) : P.microRes ε 1 T h gold g' j k =
      ε ^ 2 / (P.c * P.Δt) * (g' j k - gold j k) + ε * P.flux gold j k +
        P.c * Dp P.Δx u j * bvec N k + P.σf j * g' j k := by
    simp only [microRes, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Matrix.diagonal_mul, hsrc]
  have hb : ∑ j, ∑ k, g' j k * (P.c * Dp P.Δx u j * bvec N k) =
      - (γ₁ * P.c * ∑ i, d₁ i * u i) := by
    have e (j : ZMod Nx) : ∑ k, g' j k * (P.c * Dp P.Δx u j * bvec N k) =
        γ₁ * P.c * (g' j 0 * Dp P.Δx u j) := by
      simp only [bvec, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    simp only [e]
    rw [← Finset.mul_sum, lemma_2_plus]
    ring
  have hEB : ε ^ 2 / (P.c * P.Δt) * ((Sg' - Sgold + Sd) / 2) + ε * U -
      γ₁ * P.c * ∑ i, d₁ i * u i + Sσg = 0 := by
    have e (j : ZMod Nx) (k : Fin N) : g' j k * P.microRes ε 1 T h gold g' j k =
        ε ^ 2 / (P.c * P.Δt) * ((g' j k ^ 2 - gold j k ^ 2 + (g' j k - gold j k) ^ 2) / 2) +
          ε * (g' j k * P.flux gold j k) + g' j k * (P.c * Dp P.Δx u j * bvec N k) +
          P.σf j * g' j k ^ 2 := by
      rw [hres]
      ring
    simp only [e, Finset.sum_add_distrib] at htest
    rw [hb] at htest
    have e1 : ∑ j, ∑ k, ε ^ 2 / (P.c * P.Δt) *
        ((g' j k ^ 2 - gold j k ^ 2 + (g' j k - gold j k) ^ 2) / 2) =
        ε ^ 2 / (P.c * P.Δt) * ((Sg' - Sgold + Sd) / 2) := by
      simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rfl
    have e2 : ∑ j, ∑ k, ε * (g' j k * P.flux gold j k) = ε * U := by
      simp only [← Finset.mul_sum]
      rfl
    have e3 : ∑ j, ∑ k, P.σf j * g' j k ^ 2 = Sσg := by
      simp only [← Finset.mul_sum]
      rfl
    rw [e1, e2, e3] at htest
    linarith
  -- the energy identity
  have hCross' : Cross = ∑ i, u' i * d₁ i - ∑ i, d₁ i * u i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hI : (Su' - Su + Sy) / (2 * P.Δt) + P.a * P.cν / 2 * (ST' - ST + Sτ) / (2 * P.Δt) +
      ε ^ 2 / (4 * P.c ^ 2 * P.Δt) * (Sg' - Sgold + Sd) + γ₁ / 2 * Cross + ε / (2 * P.c) * U +
      Sσg / (2 * P.c) + ε ^ 2 / P.c * Sσh = 0 := by
    rw [hCross']
    have hc0 : P.c ≠ 0 := hc.ne'
    have e : ε ^ 2 / (4 * P.c ^ 2 * P.Δt) * (Sg' - Sgold + Sd) + ε / (2 * P.c) * U +
        Sσg / (2 * P.c) - γ₁ / 2 * ∑ i, d₁ i * u i = 1 / (2 * P.c) * 0 := by
      rw [← hEB]
      field_simp
      ring
    linear_combination hEA + hET + e
  -- Young's inequality for the macro part
  have hB1 : - (Sy / (2 * P.Δt) + γ₁ / 2 * Cross) ≤ P.Δt / 12 * S₁ := by
    have hnn : 0 ≤ ∑ i, 1 / (2 * P.Δt) * ((u' i - u i) + P.Δt * (γ₁ / 2) * d₁ i) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    have e : ∑ i, 1 / (2 * P.Δt) * ((u' i - u i) + P.Δt * (γ₁ / 2) * d₁ i) ^ 2 =
        Sy / (2 * P.Δt) + γ₁ / 2 * Cross + P.Δt / 12 * S₁ := by
      have e' (i : ZMod Nx) : 1 / (2 * P.Δt) * ((u' i - u i) + P.Δt * (γ₁ / 2) * d₁ i) ^ 2 =
          (u' i - u i) ^ 2 / (2 * P.Δt) + γ₁ / 2 * ((u' i - u i) * d₁ i) +
            P.Δt / 12 * d₁ i ^ 2 := by
        have h12 : P.Δt / 2 * (γ₁ ^ 2 / 4) = P.Δt / 12 := by
          rw [γ₁_sq]
          ring
        rw [← h12]
        field_simp
        ring
      simp only [e', Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      rfl
    rw [e] at hnn
    linarith
  -- the modes
  have hB2 : P.Δt / 4 * Sμ ≤ ε ^ 2 / (4 * P.c ^ 2 * P.Δt) * Sd + ε / (2 * P.c) * U +
      σ₀ / (2 * P.c) * Sg' := by
    have hm := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      mode_bound hc hΔt hΔx hσ₀.le (hCFL k) (fun j => (g' * P.Tm) j k)
        (fun j => (gold * P.Tm) j k)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hm
    have e0 : ∑ k, P.Δt / 4 * P.μ k ^ 2 * ∑ j, Dp P.Δx (fun i => (g' * P.Tm) i k) j ^ 2 =
        P.Δt / 4 * Sμ := by
      rw [hSμ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e1 : ∑ k, ∑ j, ((g' * P.Tm) j k - (gold * P.Tm) j k) ^ 2 = Sd := by
      have h := sum_sq_mul_transpose hF.orth (g' - gold)
      simp only [Matrix.sub_apply, Matrix.sub_mul] at h
      rw [Finset.sum_comm, hSd, h]
    have e2 : ∑ k, ∑ j, (g' * P.Tm) j k ^ 2 = Sg' := by
      rw [Finset.sum_comm, hSg', sum_sq_mul_transpose hF.orth g']
    have e3 := sum_mul_flux P g' gold
    rw [← hU, Finset.sum_add_distrib] at e3
    rw [e0, e1, e2, ← e3] at hm
    exact hm
  -- the first moment
  have hB3 : S₁ ≤ 3 * Sμ := by
    have e1 : S₁ = ∑ j, Dp P.Δx (fun i => g' i 0) j ^ 2 := sum_Dm_sq _ _
    have hj (j : ZMod Nx) : Dp P.Δx (fun i => g' i 0) j ^ 2 ≤
        3 * ∑ k, P.μ k ^ 2 * Dp P.Δx (fun i => (g' * P.Tm) i k) j ^ 2 := by
      have h := first_moment_le hF (DpM P.Δx g' j)
      have e (k : Fin (N + 1)) : (DpM P.Δx g' j ᵥ* P.Tm) k =
          Dp P.Δx (fun i => (g' * P.Tm) i k) j := by
        have : DpM P.Δx (g' * P.Tm) j k = (DpM P.Δx g' * P.Tm) j k := by rw [DpM_mul]
        rw [show Dp P.Δx (fun i => (g' * P.Tm) i k) j = DpM P.Δx (g' * P.Tm) j k from rfl, this]
        rfl
      simp only [e] at h
      exact h
    rw [e1, hSμ]
    calc ∑ j, Dp P.Δx (fun i => g' i 0) j ^ 2
        ≤ ∑ j, 3 * ∑ k, P.μ k ^ 2 * Dp P.Δx (fun i => (g' * P.Tm) i k) j ^ 2 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]
  -- the collision terms
  have hB4 : σ₀ * Sg' ≤ Sσg := by
    rw [hSg', Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hσf j)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hSτ0 : 0 ≤ Sτ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSσh0 : 0 ≤ Sσh := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hσ₀.le.trans (hσc i)) (sq_nonneg _)
  have hτ : 0 ≤ P.a * P.cν / 2 * Sτ / (2 * P.Δt) := by positivity
  have hh : 0 ≤ ε ^ 2 / P.c * Sσh := by positivity
  have hS4 : σ₀ / (2 * P.c) * Sg' ≤ Sσg / (2 * P.c) := by
    have := div_le_div_of_nonneg_right hB4 (by positivity : 0 ≤ 2 * P.c)
    calc σ₀ / (2 * P.c) * Sg' = σ₀ * Sg' / (2 * P.c) := by ring
      _ ≤ _ := this
  have hS13 : P.Δt / 12 * S₁ ≤ P.Δt / 4 * Sμ := by nlinarith
  have hfinal : ((Su' + ε ^ 2 / (2 * P.c ^ 2) * Sg' + P.a * P.cν / 2 * ST') -
      (Su + ε ^ 2 / (2 * P.c ^ 2) * Sgold + P.a * P.cν / 2 * ST)) / (2 * P.Δt) ≤ 0 := by
    have e : ((Su' + ε ^ 2 / (2 * P.c ^ 2) * Sg' + P.a * P.cν / 2 * ST') -
        (Su + ε ^ 2 / (2 * P.c ^ 2) * Sgold + P.a * P.cν / 2 * ST)) / (2 * P.Δt) =
        - (Sy / (2 * P.Δt) + γ₁ / 2 * Cross) - P.a * P.cν / 2 * Sτ / (2 * P.Δt) -
          (ε ^ 2 / (4 * P.c ^ 2 * P.Δt) * Sd + ε / (2 * P.c) * U) - Sσg / (2 * P.c) -
          ε ^ 2 / P.c * Sσh := by
      linear_combination hI
    rw [e]
    linarith
  have := (div_le_iff₀ (by positivity : 0 < 2 * P.Δt)).1 hfinal
  linarith

end Params

end Energy

/-! ### Gauss-Legendre data -/

section Gauss

open Polynomial LeanDLRA.Literature.P1906_09940

variable {N : ℕ}

/-- The Gauss-Legendre rule with `N + 1` nodes: exact for polynomials of degree `≤ 2 N + 1`. This
is the form of `LeanDLRA.OpenProblems.Stability.gaussQuadrature_weight_le`. Positivity of the
weights follows (`IsGaussLegendre.weight_pos`). -/
def IsGaussLegendre (μ w : Fin (N + 1) → ℝ) : Prop :=
  ∀ p : ℝ[X], p.natDegree ≤ 2 * N + 1 →
    ∑ k, w k * p.eval (μ k) = ∫ t in (-1 : ℝ)..1, p.eval t

lemma natDegree_legendre_le : ∀ n, (legendre n).natDegree ≤ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [legendre]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_mul_le.trans ?_
      have h1 := natDegree_legendre_le (n + 1)
      have h2 : (C ((2 * (n : ℝ) + 3) / (n + 2)) * X : ℝ[X]).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans natDegree_X_le
      omega
    · refine (natDegree_C_mul_le _ _).trans ?_
      have := natDegree_legendre_le n
      omega

/-- `P_l` as a polynomial. -/
noncomputable def nLegPoly (l : ℕ) : ℝ[X] := C √((2 * (l : ℝ) + 1) / 2) * legendre l

lemma eval_nLegPoly (l : ℕ) (x : ℝ) : (nLegPoly l).eval x = nLeg l x := by
  simp [nLegPoly, nLeg]

lemma natDegree_nLegPoly_le (l : ℕ) : (nLegPoly l).natDegree ≤ l :=
  (natDegree_C_mul_le _ _).trans (natDegree_legendre_le l)

/-- **Gauss-Legendre weights are positive**, from exactness alone. -/
theorem IsGaussLegendre.weight_pos {μ w : Fin (N + 1) → ℝ} (h : IsGaussLegendre μ w)
    (k : Fin (N + 1)) : 0 < w k := by
  classical
  set q : ℝ[X] := ∏ j ∈ Finset.univ.erase k, (X - C (μ j)) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hdeg : q.natDegree ≤ N := by
    rw [hq, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have hsq := h (q * q) (natDegree_mul_le.trans (by omega))
  have hl : ∑ j, w j * (q * q).eval (μ j) = w k * q.eval (μ k) ^ 2 := by
    rw [Finset.sum_eq_single k]
    · simp only [eval_mul]
      ring
    · intro j _ hj
      have : q.eval (μ j) = 0 := by
        rw [hq, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) (by simp)
      simp [this]
    · simp
  have hne : ∃ x ∈ Set.Icc (-1 : ℝ) 1, 0 < (q * q).eval x := by
    by_contra hc
    have hroot : ∀ x ∈ Set.Icc (-1 : ℝ) 1, q.IsRoot x := by
      intro x hx
      by_contra hr
      refine hc ⟨x, hx, ?_⟩
      rw [eval_mul]
      exact mul_self_pos.2 hr
    have hinf : Set.Infinite {x | q.IsRoot x} :=
      (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono hroot
    exact hqm.ne_zero (eq_zero_of_infinite_isRoot q hinf)
  have hpos : 0 < ∫ t in (-1 : ℝ)..1, (q * q).eval t :=
    intervalIntegral.integral_pos (by norm_num) (q * q).continuous.continuousOn
      (fun x _ => by rw [eval_mul]; exact mul_self_nonneg _) hne
  rw [← hsq, hl] at hpos
  by_contra hw
  have : w k * q.eval (μ k) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hw) (sq_nonneg _)
  linarith

lemma IsGaussLegendre.quad_nLeg {μ w : Fin (N + 1) → ℝ} (h : IsGaussLegendre μ w) {i j : ℕ}
    (hij : i + j ≤ 2 * N) :
    ∑ k, w k * (nLeg i (μ k) * nLeg j (μ k)) = if i = j then 1 else 0 := by
  have hd : (nLegPoly i * nLegPoly j).natDegree ≤ 2 * N + 1 :=
    natDegree_mul_le.trans (by
      have := natDegree_nLegPoly_le i
      have := natDegree_nLegPoly_le j
      omega)
  have := h _ hd
  simp only [eval_mul, eval_nLegPoly] at this
  rw [this, integral_nLeg_mul]

lemma IsGaussLegendre.quad_mu_nLeg {μ w : Fin (N + 1) → ℝ} (h : IsGaussLegendre μ w) {i j : ℕ}
    (hij : i + j ≤ 2 * N) :
    ∑ k, w k * (μ k * nLeg i (μ k) * nLeg j (μ k)) =
      if j = i + 1 then muOff i else if i = j + 1 then muOff j else 0 := by
  have hd : (X * nLegPoly i * nLegPoly j).natDegree ≤ 2 * N + 1 := by
    refine natDegree_mul_le.trans ?_
    have h1 : (X * nLegPoly i).natDegree ≤ i + 1 := by
      refine natDegree_mul_le.trans ?_
      have := natDegree_nLegPoly_le i
      simp only [natDegree_X]
      omega
    have := natDegree_nLegPoly_le j
    omega
  have := h _ hd
  simp only [eval_mul, eval_nLegPoly, eval_X] at this
  rw [this, integral_mu_nLeg]

lemma IsGaussLegendre.sum_weight {μ w : Fin (N + 1) → ℝ} (h : IsGaussLegendre μ w) :
    ∑ k, w k = 2 := by
  have := h 1 (by simp)
  simp only [eval_one, mul_one] at this
  rw [this]
  norm_num

/-- The matrix `T ∈ ℝ^{N × (N+1)}` of arXiv 2402.16746, `T_{ik} = √w_k P_i(μ_k)`, `1 ≤ i ≤ N`. -/
noncomputable def gaussT (μ w : Fin (N + 1) → ℝ) : Matrix (Fin N) (Fin (N + 1)) ℝ :=
  Matrix.of fun i k => √(w k) * nLeg ((i : ℕ) + 1) (μ k)

/-- The row of `T_f` that belongs to `P₀`. -/
noncomputable def gaussT₀ (μ w : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : ℝ :=
  √(w k) * nLeg 0 (μ k)

/-- `A = T M Tᵀ`: the flux matrix of the paper, `A_{ij} = ⟨μ P_i P_j⟩_μ` for `1 ≤ i, j ≤ N`, is
reproduced by Gauss-Legendre data. -/
theorem gaussT_flux {μ w : Fin (N + 1) → ℝ} (h : IsGaussLegendre μ w) :
    gaussT μ w * diagonal μ * (gaussT μ w)ᵀ = (muMatrix (N + 1)).submatrix Fin.succ Fin.succ := by
  ext i j
  have hw (k : Fin (N + 1)) : √(w k) * √(w k) = w k := Real.mul_self_sqrt (h.weight_pos k).le
  have hij : ((i : ℕ) + 1) + ((j : ℕ) + 1) ≤ 2 * N := by omega
  have e : (gaussT μ w * diagonal μ * (gaussT μ w)ᵀ) i j =
      ∑ k, w k * (μ k * nLeg ((i : ℕ) + 1) (μ k) * nLeg ((j : ℕ) + 1) (μ k)) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, gaussT, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    linear_combination (μ k * nLeg ((i : ℕ) + 1) (μ k) * nLeg ((j : ℕ) + 1) (μ k)) * hw k
  rw [e, h.quad_mu_nLeg hij, Matrix.submatrix_apply, muMatrix_apply]
  simp

theorem isFluxFactorization_gauss [NeZero N] {μ w : Fin (N + 1) → ℝ} (h : IsGaussLegendre μ w) :
    IsFluxFactorization μ (gaussT μ w) (gaussT₀ μ w) := by
  have hw (k : Fin (N + 1)) : √(w k) * √(w k) = w k := Real.mul_self_sqrt (h.weight_pos k).le
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have hij : ((i : ℕ) + 1) + ((j : ℕ) + 1) ≤ 2 * N := by omega
    have e : (gaussT μ w * (gaussT μ w)ᵀ) i j =
        ∑ k, w k * (nLeg ((i : ℕ) + 1) (μ k) * nLeg ((j : ℕ) + 1) (μ k)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, gaussT, Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      linear_combination (nLeg ((i : ℕ) + 1) (μ k) * nLeg ((j : ℕ) + 1) (μ k)) * hw k
    rw [e, h.quad_nLeg hij, Matrix.one_apply]
    simp [Fin.ext_iff]
  · have e (k : Fin (N + 1)) : gaussT₀ μ w k ^ 2 = w k * (nLeg 0 (μ k) * nLeg 0 (μ k)) := by
      simp only [gaussT₀]
      linear_combination (nLeg 0 (μ k) * nLeg 0 (μ k)) * hw k
    simp only [e]
    rw [h.quad_nLeg (by omega)]
    simp
  · intro i
    have hi : ((i : ℕ) + 1) + 0 ≤ 2 * N := by omega
    have e : ∑ k, gaussT μ w i k * μ k * gaussT₀ μ w k =
        ∑ k, w k * (μ k * nLeg ((i : ℕ) + 1) (μ k) * nLeg 0 (μ k)) := by
      simp only [gaussT, gaussT₀, Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      linear_combination (μ k * nLeg ((i : ℕ) + 1) (μ k) * nLeg 0 (μ k)) * hw k
    rw [e, h.quad_mu_nLeg hi]
    by_cases hi0 : i = 0
    · subst hi0
      simp [muOff]
    · have : (i : ℕ) ≠ 0 := fun e => hi0 (Fin.ext (by simpa using e))
      simp [hi0, this]

/-- `β_N = max_k w_k (N + 1)`. -/
noncomputable def betaN (w : Fin (N + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w * ((N : ℝ) + 1)

lemma IsGaussLegendre.two_le_betaN {μ w : Fin (N + 1) → ℝ} (h : IsGaussLegendre μ w) :
    2 ≤ betaN w := by
  have hsum : ∑ k, w k ≤ ∑ _k : Fin (N + 1), Finset.univ.sup' Finset.univ_nonempty w :=
    Finset.sum_le_sum fun k hk => Finset.le_sup' w hk
  rw [h.sum_weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [betaN, mul_comm]
  push_cast at hsum
  exact hsum

end Gauss

/-! ### Theorem 2 -/

section Theorem2

variable {Nx N : ℕ} [NeZero Nx] [NeZero N] (P : Params Nx N)

namespace Params

/-- The micro equation (3.1b) says that the residual vanishes. -/
lemma IsFullStep.microRes_eq_zero {ε : ℝ} {Ψ T h T' h' : ZMod Nx → ℝ}
    {g g' : Matrix (ZMod Nx) (Fin N) ℝ} (hs : P.IsFullStep ε Ψ T h g T' h' g') :
    P.microRes ε Ψ T h g g' = 0 := by
  ext j k
  simp only [microRes, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Matrix.diagonal_mul, Matrix.zero_apply]
  linear_combination hs.micro_eq j k

/-- The CFL condition (3.4) implies the sharp one, since `β_N ≥ 2`. -/
lemma cfl_of_cfl {c ε Δx σ₀ Δt β m : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) (hΔx : 0 < Δx) (hσ₀ : 0 < σ₀)
    (hβ : 2 ≤ β)
    (h : Δt ≤ 1 / (5 * c * β) * (2 * ε * Δx / |m| + σ₀ * Δx ^ 2 / m ^ 2)) :
    Δt ≤ 1 / (4 * c) * (2 * ε * Δx / |m| + σ₀ * Δx ^ 2 / m ^ 2) := by
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- **arXiv 2402.16746, Theorem 2** (energy stability of the full macro-micro scheme (3.3) with
linear emission `Ψ = 1`), for `(N+1)`-point Gauss-Legendre data, on the periodic grid: under the
CFL condition (3.4), `eⁿ⁺¹ ≤ eⁿ`. Quantifiers and constants are the paper's. The zero boundary
case is `theorem_2_zero_boundary`. The paper's proof goes through its Lemmas 4 and 6, which are
false (`lemma_4_false`, `lemma_6_false`); the theorem itself holds, with room to spare, by
`theorem_2_sharp`. -/
theorem theorem_2 {σ₀ ε : ℝ} (hP : P.Admissible σ₀) {w : Fin (N + 1) → ℝ}
    (hGL : IsGaussLegendre P.μ w) (hTm : P.Tm = gaussT P.μ w) (hε : 0 ≤ ε)
    (hCFL : ∀ k, P.μ k ≠ 0 → P.Δt ≤ 1 / (5 * P.c * betaN w) *
      (2 * ε * P.Δx / |P.μ k| + σ₀ * P.Δx ^ 2 / P.μ k ^ 2))
    {T h T' h' : ZMod Nx → ℝ} {g g' : Matrix (ZMod Nx) (Fin N) ℝ}
    (hs : P.IsFullStep ε 1 T h g T' h' g') :
    P.energy ε T' h' g' ≤ P.energy ε T h g := by
  have hF := isFluxFactorization_gauss hGL
  rw [← hTm] at hF
  refine P.energy_le_of_tested hP hF
    (fun k hk => cfl_of_cfl hP.c_pos hε hP.Δx_pos hP.σ₀_pos hGL.two_le_betaN (hCFL k hk))
    (fun i => ?_) ?_ hs.temp_eq
  · simpa using hs.macro_eq i
  · simp [hs.microRes_eq_zero]

end Params

end Theorem2

/-! ### The fixed-rank modal macro-micro BUG integrator -/

section LowRank

variable {Nx N : ℕ} [NeZero Nx] [NeZero N] (P : Params Nx N)

namespace Params

variable {ρ ι ι' : Type*} [Fintype ρ] [Fintype ι] [Fintype ι']

/-- The K-step (4.2) of arXiv 2402.16746, with `K = X S` and rows `K_{j+1/2}`. The collision term
is implicit. Rows are multiplied from the right, and `Vᵀ A^± V` are symmetric. -/
def IsKStep (ε : ℝ) (Ψ T h : ZMod Nx → ℝ) (X : Matrix (ZMod Nx) ρ ℝ) (S : Matrix ρ ρ ℝ)
    (V : Matrix (Fin N) ρ ℝ) (K' : Matrix (ZMod Nx) ρ ℝ) : Prop :=
  (ε ^ 2 / (P.c * P.Δt)) • (K' - X * S) =
    -(ε • (DmM P.Δx (X * S) * (Vᵀ * P.Apl * V) + DpM P.Δx (X * S) * (Vᵀ * P.Ami * V))) -
      vecMulVec (P.source ε Ψ T h) (bvec N ᵥ* V) - diagonal P.σf * K'

/-- The L-step (4.3) of arXiv 2402.16746, with `L = V Sᵀ`. -/
def IsLStep (ε : ℝ) (Ψ T h : ZMod Nx → ℝ) (X : Matrix (ZMod Nx) ρ ℝ) (S : Matrix ρ ρ ℝ)
    (V : Matrix (Fin N) ρ ℝ) (L' : Matrix (Fin N) ρ ℝ) : Prop :=
  (ε ^ 2 / (P.c * P.Δt)) • (L' - V * Sᵀ) =
    -(ε • (P.Apl * (V * Sᵀ) * ((DmM P.Δx X)ᵀ * X) + P.Ami * (V * Sᵀ) * ((DpM P.Δx X)ᵀ * X))) -
      vecMulVec (bvec N) (Xᵀ *ᵥ P.source ε Ψ T h) - L' * (Xᵀ * diagonal P.σf * X)

/-- The S-step (4.4) of arXiv 2402.16746 in the bases `X'`, `V'`, from the initial value `St`,
which is `S̃ⁿ`. The same equation is the Galerkin step of Section 4.2, in the augmented bases. -/
def IsSStep (ε : ℝ) (Ψ T h : ZMod Nx → ℝ) (St : Matrix ι ι' ℝ) (X' : Matrix (ZMod Nx) ι ℝ)
    (V' : Matrix (Fin N) ι' ℝ) (S' : Matrix ι ι' ℝ) : Prop :=
  (ε ^ 2 / (P.c * P.Δt)) • (S' - St) =
    -(ε • (X'ᵀ * DmM P.Δx X' * St * (V'ᵀ * P.Apl * V') +
        X'ᵀ * DpM P.Δx X' * St * (V'ᵀ * P.Ami * V'))) -
      vecMulVec (X'ᵀ *ᵥ P.source ε Ψ T h) (bvec N ᵥ* V') - (X'ᵀ * diagonal P.σf * X') * S'

/-- One step (4.2)-(4.6) of the fixed-rank modal macro-micro BUG integrator of arXiv 2402.16746:
`Xⁿ, Sⁿ, Vⁿ, Tⁿ, hⁿ ↦ Xⁿ⁺¹, Sⁿ⁺¹, Vⁿ⁺¹, Tⁿ⁺¹, hⁿ⁺¹`. `Xⁿ⁺¹` and `Vⁿ⁺¹` are orthonormal bases
of `Kⁿ⁺¹`, `Lⁿ⁺¹`, as `K' = X' SK` and `L' = V' SLᵀ`. -/
structure IsFixedRankStep {r : ℕ} (ε : ℝ) (Ψ T h : ZMod Nx → ℝ)
    (X : Matrix (ZMod Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin N) (Fin r) ℝ)
    (K' : Matrix (ZMod Nx) (Fin r) ℝ) (L' : Matrix (Fin N) (Fin r) ℝ)
    (X' : Matrix (ZMod Nx) (Fin r) ℝ) (SK : Matrix (Fin r) (Fin r) ℝ)
    (V' : Matrix (Fin N) (Fin r) ℝ) (SL : Matrix (Fin r) (Fin r) ℝ)
    (S' : Matrix (Fin r) (Fin r) ℝ) (T' h' : ZMod Nx → ℝ) : Prop where
  K_eq : P.IsKStep ε Ψ T h X S V K'
  X'_orth : X'ᵀ * X' = 1
  K_qr : K' = X' * SK
  L_eq : P.IsLStep ε Ψ T h X S V L'
  V'_orth : V'ᵀ * V' = 1
  L_qr : L' = V' * SLᵀ
  S_eq : P.IsSStep ε Ψ T h ((X'ᵀ * X) * S * (Vᵀ * V')) X' V' S'
  macro_eq : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * Ψ i * h' i +
    γ₁ / 2 * Dm P.Δx (fun j => (X' * S' * V'ᵀ) j 0) i = -P.σc i * h' i
  temp_eq : ∀ i, (T' i - T i) / P.Δt = P.κ * P.σc i * h' i

variable [DecidableEq ι] [DecidableEq ι']

/-- The S-step annihilates the projection of the residual of the micro equation. -/
theorem IsSStep.res_eq_zero {ε : ℝ} {Ψ T h : ZMod Nx → ℝ} {St S' : Matrix ι ι' ℝ}
    {X' : Matrix (ZMod Nx) ι ℝ} {V' : Matrix (Fin N) ι' ℝ} (hX' : X'ᵀ * X' = 1)
    (hV' : V'ᵀ * V' = 1) (hS : P.IsSStep ε Ψ T h St X' V' S') :
    X'ᵀ * P.microRes ε Ψ T h (X' * St * V'ᵀ) (X' * S' * V'ᵀ) * V' = 0 := by
  set R := P.microRes ε Ψ T h (X' * St * V'ᵀ) (X' * S' * V'ᵀ) with hR
  have h1 (B : Matrix ι ι' ℝ) : X'ᵀ * (X' * B * V'ᵀ) * V' = B := by
    calc X'ᵀ * (X' * B * V'ᵀ) * V' = (X'ᵀ * X') * B * (V'ᵀ * V') := by
          simp only [Matrix.mul_assoc]
      _ = B := by rw [hX', hV', Matrix.one_mul, Matrix.mul_one]
  have h2 : X'ᵀ * P.flux (X' * St * V'ᵀ) * V' =
      X'ᵀ * DmM P.Δx X' * St * (V'ᵀ * P.Apl * V') +
        X'ᵀ * DpM P.Δx X' * St * (V'ᵀ * P.Ami * V') := by
    have hm : DmM P.Δx (X' * St * V'ᵀ) = DmM P.Δx X' * St * V'ᵀ := by rw [DmM_mul, DmM_mul]
    have hp : DpM P.Δx (X' * St * V'ᵀ) = DpM P.Δx X' * St * V'ᵀ := by rw [DpM_mul, DpM_mul]
    rw [flux, hm, hp]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have h3 : X'ᵀ * vecMulVec (P.source ε Ψ T h) (bvec N) * V' =
      vecMulVec (X'ᵀ *ᵥ P.source ε Ψ T h) (bvec N ᵥ* V') := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have h4 : X'ᵀ * (diagonal P.σf * (X' * S' * V'ᵀ)) * V' = (X'ᵀ * diagonal P.σf * X') * S' := by
    calc X'ᵀ * (diagonal P.σf * (X' * S' * V'ᵀ)) * V' =
        (X'ᵀ * diagonal P.σf * X') * S' * (V'ᵀ * V') := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV', Matrix.mul_one]
  have e : X'ᵀ * R * V' = (ε ^ 2 / (P.c * P.Δt)) • (S' - St) +
      ε • (X'ᵀ * P.flux (X' * St * V'ᵀ) * V') +
      X'ᵀ * vecMulVec (P.source ε Ψ T h) (bvec N) * V' +
      X'ᵀ * (diagonal P.σf * (X' * S' * V'ᵀ)) * V' := by
    rw [hR, microRes]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, h1]
  rw [e, h2, h3, h4, hS]
  abel

/-- The Galerkin identity behind Theorems 4 and 7: the residual vanishes when tested with the new
iterate. -/
theorem IsSStep.tested {ε : ℝ} {Ψ T h : ZMod Nx → ℝ} {St S' : Matrix ι ι' ℝ}
    {X' : Matrix (ZMod Nx) ι ℝ} {V' : Matrix (Fin N) ι' ℝ} (hX' : X'ᵀ * X' = 1)
    (hV' : V'ᵀ * V' = 1) (hS : P.IsSStep ε Ψ T h St X' V' S') :
    ∑ j, ∑ k, (X' * S' * V'ᵀ) j k *
      P.microRes ε Ψ T h (X' * St * V'ᵀ) (X' * S' * V'ᵀ) j k = 0 := by
  have e : (⟪X' * S' * V'ᵀ, P.microRes ε Ψ T h (X' * St * V'ᵀ) (X' * S' * V'ᵀ)⟫ : ℝ) =
      ⟪S', X'ᵀ * P.microRes ε Ψ T h (X' * St * V'ᵀ) (X' * S' * V'ᵀ) * V'⟫ := by
    rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, Matrix.transpose_transpose,
      Matrix.mul_assoc X'ᵀ _ V']
  rw [← Frobenius.inner_def, e, hS.res_eq_zero P hX' hV', inner_zero_right]

omit [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] [NeZero N] in
lemma energy_le_energy {σ₀ : ℝ} (hP : P.Admissible σ₀) (ε : ℝ) (T h : ZMod Nx → ℝ)
    {gold g : Matrix (ZMod Nx) (Fin N) ℝ}
    (hg : ∑ j, ∑ k, gold j k ^ 2 ≤ ∑ j, ∑ k, g j k ^ 2) :
    P.energy ε T h gold ≤ P.energy ε T h g := by
  have hac : 0 ≤ P.a * P.cν := mul_nonneg hP.a_pos.le hP.cν_pos.le
  have hc := hP.c_pos
  rw [energy_eq P hac, energy_eq P hac]
  refine mul_le_mul_of_nonneg_left ?_ hP.Δx_pos.le
  have := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ ε ^ 2 / (2 * P.c ^ 2))
  linarith

omit [NeZero Nx] [NeZero N] [Fintype ι] [Fintype ι'] in
/-- The Galerkin projection does not increase the norm: `S̃ⁿ` is `Xⁿ⁺¹ᵀ gⁿ Vⁿ⁺¹`. -/
lemma sum_sq_galerkin_le [NeZero Nx] [Fintype ι] [Fintype ι'] {X' : Matrix (ZMod Nx) ι ℝ}
    {V' : Matrix (Fin N) ι' ℝ} (hX' : X'ᵀ * X' = 1) (hV' : V'ᵀ * V' = 1)
    (g : Matrix (ZMod Nx) (Fin N) ℝ) :
    ∑ j, ∑ k, (X' * (X'ᵀ * g * V') * V'ᵀ) j k ^ 2 ≤ ∑ j, ∑ k, g j k ^ 2 := by
  rw [← Frobenius.norm_sq_eq_sum, ← Frobenius.norm_sq_eq_sum]
  rw [Frobenius.norm_mul_transpose_of_orthonormal hV', Frobenius.norm_mul_of_orthonormal hX']
  have h1 : ‖X'ᵀ * g * V'‖ ≤ ‖X'ᵀ * g‖ := norm_mul_le_of_orthonormal hV' _
  have h2 : ‖X'ᵀ * g‖ ≤ ‖g‖ := norm_transpose_mul_le hX' _
  exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2

/-- **arXiv 2402.16746, Theorem 4** (energy stability of the fixed-rank modal macro-micro BUG
integrator (4.2)-(4.6) for linear emission `Ψ = 1`), for Gauss-Legendre data on the periodic grid:
under the CFL condition (3.4) of Theorem 2, `eⁿ⁺¹ ≤ eⁿ` with
`eⁿ = ‖a Tⁿ + ε²/c hⁿ‖² + ‖ε/(γ₀ c) Xⁿ Sⁿ Vⁿᵀ‖² + ‖√(a cν/2) Tⁿ‖²`. Only the orthonormality of the
new bases is used, not the K- and L-steps. -/
theorem theorem_4 {σ₀ ε : ℝ} (hP : P.Admissible σ₀) {w : Fin (N + 1) → ℝ}
    (hGL : IsGaussLegendre P.μ w) (hTm : P.Tm = gaussT P.μ w) (hε : 0 ≤ ε)
    (hCFL : ∀ k, P.μ k ≠ 0 → P.Δt ≤ 1 / (5 * P.c * betaN w) *
      (2 * ε * P.Δx / |P.μ k| + σ₀ * P.Δx ^ 2 / P.μ k ^ 2))
    {r : ℕ} {T h T' h' : ZMod Nx → ℝ} {X X' : Matrix (ZMod Nx) (Fin r) ℝ}
    {K' : Matrix (ZMod Nx) (Fin r) ℝ} {L' V V' : Matrix (Fin N) (Fin r) ℝ}
    {S SK SL S' : Matrix (Fin r) (Fin r) ℝ}
    (hs : P.IsFixedRankStep ε 1 T h X S V K' L' X' SK V' SL S' T' h') :
    P.energy ε T' h' (X' * S' * V'ᵀ) ≤ P.energy ε T h (X * S * Vᵀ) := by
  have hF := isFluxFactorization_gauss hGL
  rw [← hTm] at hF
  have hst : P.energy ε T' h' (X' * S' * V'ᵀ) ≤
      P.energy ε T h (X' * ((X'ᵀ * X) * S * (Vᵀ * V')) * V'ᵀ) :=
    P.energy_le_of_tested hP hF
      (fun k hk => cfl_of_cfl hP.c_pos hε hP.Δx_pos hP.σ₀_pos hGL.two_le_betaN (hCFL k hk))
      (fun i => by simpa using hs.macro_eq i) (hs.S_eq.tested P hs.X'_orth hs.V'_orth) hs.temp_eq
  refine hst.trans (P.energy_le_energy hP ε T h ?_)
  have e : (X'ᵀ * X) * S * (Vᵀ * V') = X'ᵀ * (X * S * Vᵀ) * V' := by
    simp only [Matrix.mul_assoc]
  rw [e]
  exact sum_sq_galerkin_le hs.X'_orth hs.V'_orth _

/-! ### Theorem 5 -/

omit [NeZero Nx] [NeZero N] in
/-- The local conservation law (4.16a), (4.16b) for any scheme with the macro update (4.5), (4.6):
`Φ = a c T + ε² h`, for linear emission. Division by `c` and `cν` needs `c, cν ≠ 0`. -/
theorem local_conservation {ε : ℝ} (hc : P.c ≠ 0) (hcν : P.cν ≠ 0) {T h T' h' g₁ : ZMod Nx → ℝ}
    (hmacro : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * h' i +
      γ₁ / 2 * g₁ i = -P.σc i * h' i)
    (htemp : ∀ i, (T' i - T i) / P.Δt = P.κ * P.σc i * h' i) (i : ZMod Nx) :
    ((P.a * P.c * T' i + ε ^ 2 * h' i) - (P.a * P.c * T i + ε ^ 2 * h i)) / P.Δt +
        P.c * (γ₁ / 2) * g₁ i = -P.c * P.σc i * h' i ∧
      P.cν / 2 * ((T' i - T i) / P.Δt) = P.σc i * h' i := by
  constructor
  · have e : ((P.a * P.c * T' i + ε ^ 2 * h' i) - (P.a * P.c * T i + ε ^ 2 * h i)) / P.Δt =
        P.c * (P.a * ((T' i - T i) / P.Δt) + ε ^ 2 / P.c * ((h' i - h i) / P.Δt)) := by
      field_simp
      ring
    rw [e]
    linear_combination P.c * hmacro i + P.c * P.a * htemp i
  · rw [htemp i, κ]
    field_simp

omit [NeZero N] in
/-- The total mass `∑ (Φ_i / c + cν/2 T_i)` is conserved by any scheme with the macro update
(4.5), (4.6) and linear emission, on the periodic grid. -/
theorem global_conservation {ε : ℝ} (hc : P.c ≠ 0) (hcν : P.cν ≠ 0) (hΔt : P.Δt ≠ 0)
    {T h T' h' g₁ : ZMod Nx → ℝ}
    (hmacro : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * h' i +
      γ₁ / 2 * Dm P.Δx g₁ i = -P.σc i * h' i)
    (htemp : ∀ i, (T' i - T i) / P.Δt = P.κ * P.σc i * h' i) :
    ∑ i, ((P.a * P.c * T' i + ε ^ 2 * h' i) / P.c + P.cν / 2 * T' i) =
      ∑ i, ((P.a * P.c * T i + ε ^ 2 * h i) / P.c + P.cν / 2 * T i) := by
  have hD : ∑ i, Dm P.Δx g₁ i = 0 := by
    simp only [Dm, ← Finset.sum_div, Finset.sum_sub_distrib, sum_sub_one, sub_self, zero_div]
  have hi (i : ZMod Nx) : ((P.a * P.c * T' i + ε ^ 2 * h' i) / P.c + P.cν / 2 * T' i) =
      ((P.a * P.c * T i + ε ^ 2 * h i) / P.c + P.cν / 2 * T i) -
        P.Δt * (γ₁ / 2) * Dm P.Δx g₁ i := by
    have hT : T' i - T i = P.Δt * (P.κ * P.σc i * h' i) := by
      rw [← htemp i]
      field_simp
    have hh : ε ^ 2 / P.c * (h' i - h i) + P.Δt * (P.a * P.κ * P.σc i * h' i) +
        P.Δt * (γ₁ / 2 * Dm P.Δx g₁ i) = -P.Δt * P.σc i * h' i := by
      have e : P.Δt * (ε ^ 2 / P.c * ((h' i - h i) / P.Δt)) = ε ^ 2 / P.c * (h' i - h i) := by
        field_simp
      linear_combination P.Δt * hmacro i - e
    have hκ : P.cν / 2 * P.κ = 1 := by
      simp only [κ]
      field_simp
    have e1 : (P.a * P.c * T' i + ε ^ 2 * h' i) / P.c = P.a * T' i + ε ^ 2 / P.c * h' i := by
      field_simp
    have e2 : (P.a * P.c * T i + ε ^ 2 * h i) / P.c = P.a * T i + ε ^ 2 / P.c * h i := by
      field_simp
    rw [e1, e2]
    linear_combination (P.a + P.cν / 2) * hT + hh + P.Δt * P.σc i * h' i * hκ
  simp only [hi, Finset.sum_sub_distrib, ← Finset.mul_sum, hD]
  ring

/-- **arXiv 2402.16746, Theorem 5** (local mass conservation of the fixed-rank BUG integrator) for
linear emission on the periodic grid, with `Φⁿ_i = a c Tⁿ_i + ε² hⁿ_i`: the conservation laws
(4.16a), (4.16b), and the conservation of the total mass `∑ (Φ_i / c + cν/2 T_i)`. The paper's
"`n ∈ {0, 1}`" is a misprint for all `n`. The nonperiodic case is
`mass_conservation_of_boundary_flux`. -/
theorem theorem_5 {ε : ℝ} (hc : P.c ≠ 0) (hcν : P.cν ≠ 0) (hΔt : P.Δt ≠ 0) {r : ℕ}
    {T h T' h' : ZMod Nx → ℝ} {X X' : Matrix (ZMod Nx) (Fin r) ℝ}
    {K' : Matrix (ZMod Nx) (Fin r) ℝ} {L' V V' : Matrix (Fin N) (Fin r) ℝ}
    {S SK SL S' : Matrix (Fin r) (Fin r) ℝ}
    (hs : P.IsFixedRankStep ε 1 T h X S V K' L' X' SK V' SL S' T' h') :
    (∀ i, ((P.a * P.c * T' i + ε ^ 2 * h' i) - (P.a * P.c * T i + ε ^ 2 * h i)) / P.Δt +
        P.c * (γ₁ / 2) * Dm P.Δx (fun j => (X' * S' * V'ᵀ) j 0) i = -P.c * P.σc i * h' i ∧
      P.cν / 2 * ((T' i - T i) / P.Δt) = P.σc i * h' i) ∧
    ∑ i, ((P.a * P.c * T' i + ε ^ 2 * h' i) / P.c + P.cν / 2 * T' i) =
      ∑ i, ((P.a * P.c * T i + ε ^ 2 * h i) / P.c + P.cν / 2 * T i) := by
  have hm : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * h' i +
      γ₁ / 2 * Dm P.Δx (fun j => (X' * S' * V'ᵀ) j 0) i = -P.σc i * h' i :=
    fun i => by simpa using hs.macro_eq i
  exact ⟨P.local_conservation hc hcν hm hs.temp_eq, P.global_conservation hc hcν hΔt hm hs.temp_eq⟩

/-! ### The limit `ε → 0`: Theorems 1 and 3 -/

/-- The limiting flux `w_{j+1/2} = (Ψ_{j+1/2} / σ_{j+1/2}) δ⁰(a c T)_{j+1/2}`, the paper's
`(σ^a)⁻¹ Ψ δ⁰(a c T)`. -/
noncomputable def limitFlux (Ψ T : ZMod Nx → ℝ) (j : ZMod Nx) : ℝ :=
  P.a * P.c * ((Ψ (j + 1) + Ψ j) / 2) * Dp P.Δx T j / P.σf j

/-- The discrete diffusion operator on the right of the limit scheme,
`2 a c / (3 cν) [Ψ_{i+1/2}/σ_{i+1/2} (T_{i+1} - T_i) - Ψ_{i-1/2}/σ_{i-1/2} (T_i - T_{i-1})] / Δx²`,
with `Ψ_{i+1/2} = (Ψ_{i+1} + Ψ_i)/2`. -/
noncomputable def diffOp (Ψ T : ZMod Nx → ℝ) (i : ZMod Nx) : ℝ :=
  2 * P.a * P.c / (3 * P.cν) *
    ((((Ψ (i + 1) + Ψ i) / 2) / P.σf i * (T (i + 1) - T i) -
      ((Ψ i + Ψ (i - 1)) / 2) / P.σf (i - 1) * (T i - T (i - 1))) / P.Δx ^ 2)

omit [NeZero Nx] [NeZero N] in
lemma source_zero {σ₀ : ℝ} (hP : P.Admissible σ₀) (Ψ T h : ZMod Nx → ℝ) (j : ZMod Nx) :
    P.source 0 Ψ T h j = P.σf j * P.limitFlux Ψ T j := by
  have hσ : P.σf j ≠ 0 := (hP.σ₀_pos.trans_le (hP.σf_ge j)).ne'
  simp only [source, limitFlux, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    add_zero]
  field_simp

omit [NeZero Nx] [NeZero N] in
/-- The computation at the end of the proof of Theorem 1, from `g₁ = -γ₁ w`. -/
lemma diffusion_of_limit {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ T T' h' g₁ : ZMod Nx → ℝ}
    (hg : ∀ j, g₁ j = -(γ₁ * P.limitFlux Ψ T j))
    (i : ZMod Nx)
    (hm : P.a * P.κ * P.σc i * Ψ i * h' i + γ₁ / 2 * Dm P.Δx g₁ i = -P.σc i * h' i)
    (ht : (T' i - T i) / P.Δt = P.κ * P.σc i * h' i) :
    (1 + 2 * P.a * Ψ i / P.cν) * ((T' i - T i) / P.Δt) = P.diffOp Ψ T i := by
  have hcν := hP.cν_pos.ne'
  have hΔx := hP.Δx_pos.ne'
  have hσ1 : P.σf i ≠ 0 := (hP.σ₀_pos.trans_le (hP.σf_ge i)).ne'
  have hσ2 : P.σf (i - 1) ≠ 0 := (hP.σ₀_pos.trans_le (hP.σf_ge _)).ne'
  have hγ : γ₁ * γ₁ = 2 / 3 := by rw [← sq, γ₁_sq]
  have hD : Dm P.Δx g₁ i = -(γ₁ * Dm P.Δx (P.limitFlux Ψ T) i) := by
    simp only [Dm, hg]
    ring
  rw [hD] at hm
  have hk : (1 + 2 * P.a * Ψ i / P.cν) = 1 + P.a * P.κ * Ψ i := by
    simp only [κ]
    field_simp
  have key : (1 + P.a * P.κ * Ψ i) * (P.σc i * h' i) =
      γ₁ * γ₁ / 2 * Dm P.Δx (P.limitFlux Ψ T) i := by
    linear_combination hm
  rw [ht, hk]
  have e : (1 + P.a * P.κ * Ψ i) * (P.κ * P.σc i * h' i) =
      P.κ * ((1 + P.a * P.κ * Ψ i) * (P.σc i * h' i)) := by ring
  rw [e, key, hγ]
  simp only [diffOp, κ, Dm, limitFlux, Dp, sub_add_cancel]
  field_simp

omit [NeZero Nx] in
/-- **arXiv 2402.16746, Theorem 1** (asymptotic preservation of the full scheme), at `ε = 0`, which
is what the paper's proof computes: (3.1) reduces to `g¹ = -w bᵀ` and to the explicit Euler, centred
difference discretization `(1 + 2 a Ψ_i/cν) (Tⁿ⁺¹_i - Tⁿ_i)/Δt = diffOp` of the diffusion equation.
`Ψ` is arbitrary, in particular `Ψ_i = 4 (Tⁿ_i)³`. The genuine limit is `theorem_1_tendsto`. -/
theorem theorem_1 {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ T h T' h' : ZMod Nx → ℝ}
    {g g' : Matrix (ZMod Nx) (Fin N) ℝ} (hs : P.IsFullStep 0 Ψ T h g T' h' g') :
    g' = -vecMulVec (P.limitFlux Ψ T) (bvec N) ∧
      ∀ i, (1 + 2 * P.a * Ψ i / P.cν) * ((T' i - T i) / P.Δt) = P.diffOp Ψ T i := by
  have hg : g' = -vecMulVec (P.limitFlux Ψ T) (bvec N) := by
    ext j k
    have hσ : P.σf j ≠ 0 := (hP.σ₀_pos.trans_le (hP.σf_ge j)).ne'
    have h1 := hs.micro_eq j k
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
      zero_add, P.source_zero hP] at h1
    simp only [Matrix.neg_apply, Matrix.vecMulVec_apply]
    have : P.σf j * (g' j k + P.limitFlux Ψ T j * bvec N k) = 0 := by linear_combination h1
    have := (mul_eq_zero.1 this).resolve_left hσ
    linarith
  refine ⟨hg, fun i => ?_⟩
  have hm := hs.macro_eq i
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
    zero_add] at hm
  refine P.diffusion_of_limit hP (fun j => ?_) i hm (hs.temp_eq i)
  rw [hg]
  simp [Matrix.vecMulVec_apply, bvec, mul_comm]

omit [NeZero Nx] [NeZero N] in
/-- The macro update turns the limit `g₁ → -γ₁ w` of the first moment into the limit of the discrete
diffusion equation. -/
theorem macro_tendsto {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ T h : ZMod Nx → ℝ} (hΨ : ∀ i, 0 ≤ Ψ i)
    {T' h' g₁ : ℝ → ZMod Nx → ℝ}
    (hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, ε ^ 2 / P.c * ((h' ε i - h i) / P.Δt) +
      P.a * P.κ * P.σc i * Ψ i * h' ε i + γ₁ / 2 * Dm P.Δx (g₁ ε) i = -P.σc i * h' ε i)
    (ht : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, (T' ε i - T i) / P.Δt = P.κ * P.σc i * h' ε i)
    (hg : ∀ j, Tendsto (fun ε => g₁ ε j) (𝓝[>] 0) (𝓝 (-(γ₁ * P.limitFlux Ψ T j))))
    (i : ZMod Nx) :
    Tendsto (fun ε => (1 + 2 * P.a * Ψ i / P.cν) * ((T' ε i - T i) / P.Δt)) (𝓝[>] 0)
      (𝓝 (P.diffOp Ψ T i)) := by
  have hc := hP.c_pos
  have hΔt := hP.Δt_pos
  have hcν := hP.cν_pos
  have ha := hP.a_pos
  have hσc : 0 < P.σc i := hP.σ₀_pos.trans_le (hP.σc_ge i)
  have hκ : 0 < P.κ := by
    simp only [κ]
    positivity
  set g₀ : ZMod Nx → ℝ := fun j => -(γ₁ * P.limitFlux Ψ T j) with hg₀
  set D₀ := Dm P.Δx g₀ i with hD₀
  have hdenpos : 0 < P.a * P.κ * P.σc i * Ψ i + P.σc i := by
    have h2 := hΨ i
    positivity
  set h₀ := (-(γ₁ / 2 * D₀)) / (P.a * P.κ * P.σc i * Ψ i + P.σc i) with hh₀
  have hDt : Tendsto (fun ε => Dm P.Δx (g₁ ε) i) (𝓝[>] 0) (𝓝 D₀) := by
    simp only [hD₀, Dm]
    exact ((hg i).sub (hg (i - 1))).div_const _
  have hht : Tendsto (fun ε => h' ε i) (𝓝[>] 0) (𝓝 h₀) := by
    have hquot : Tendsto (fun ε => (ε ^ 2 / (P.c * P.Δt) * h i - γ₁ / 2 * Dm P.Δx (g₁ ε) i) /
          (ε ^ 2 / (P.c * P.Δt) + (P.a * P.κ * P.σc i * Ψ i + P.σc i))) (𝓝[>] 0) (𝓝 h₀) := by
      have hsq : Tendsto (fun ε : ℝ => ε ^ 2 / (P.c * P.Δt)) (𝓝[>] 0) (𝓝 0) := by
        have : ContinuousAt (fun ε : ℝ => ε ^ 2 / (P.c * P.Δt)) 0 := by fun_prop
        simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      have hnum := (hsq.mul_const (h i)).sub (hDt.const_mul (γ₁ / 2))
      have hden := hsq.add_const (P.a * P.κ * P.σc i * Ψ i + P.σc i)
      have hquot' := hnum.div hden (by simpa using hdenpos.ne')
      simp only [zero_mul, zero_sub, zero_add] at hquot'
      exact hquot'
    refine hquot.congr' ?_
    filter_upwards [hm] with ε hε
    have h1 := hε i
    have hden : ε ^ 2 / (P.c * P.Δt) + (P.a * P.κ * P.σc i * Ψ i + P.σc i) ≠ 0 := by
      positivity
    rw [div_eq_iff hden]
    linear_combination -h1
  have hTt : Tendsto (fun ε => (T' ε i - T i) / P.Δt) (𝓝[>] 0)
      (𝓝 (P.κ * P.σc i * h₀)) := by
    refine (hht.const_mul (P.κ * P.σc i)).congr' ?_
    filter_upwards [ht] with ε hε
    exact (hε i).symm
  have hval : (1 + 2 * P.a * Ψ i / P.cν) * (P.κ * P.σc i * h₀) = P.diffOp Ψ T i := by
    have hDen : (P.a * P.κ * P.σc i * Ψ i + P.σc i) * h₀ = -(γ₁ / 2 * D₀) := by
      rw [hh₀, mul_comm, div_mul_cancel₀ _ hdenpos.ne']
    have hm' : P.a * P.κ * P.σc i * Ψ i * h₀ + γ₁ / 2 * Dm P.Δx g₀ i = -P.σc i * h₀ := by
      rw [← hD₀]
      linear_combination hDen
    have ht' : ((T i + P.Δt * (P.κ * P.σc i * h₀)) - T i) / P.Δt = P.κ * P.σc i * h₀ := by
      field_simp
      ring
    have := P.diffusion_of_limit hP (Ψ := Ψ) (T := T)
      (T' := fun _ => T i + P.Δt * (P.κ * P.σc i * h₀)) (h' := fun _ => h₀) (g₁ := g₀)
      (fun _ => rfl) i hm' ht'
    rwa [ht'] at this
  rw [← hval]
  exact hTt.const_mul _

omit [NeZero Nx] in
/-- **arXiv 2402.16746, Theorem 1, as a genuine limit.** Fix the data of step `n` and let
`ε ↓ 0`, with any solutions of (3.1) for `ε > 0`. Then `gⁿ⁺¹` tends to `-w bᵀ`, and the left side of
the discrete diffusion equation tends to `diffOp`. The hypothesis `Ψ ≥ 0` (true for `Ψ = 4 T³` with
`T ≥ 0`, and for `Ψ = 1`) keeps `1 + 2 a Ψ/cν` away from zero; the paper uses it silently. -/
theorem theorem_1_tendsto {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ T h : ZMod Nx → ℝ}
    (hΨ : ∀ i, 0 ≤ Ψ i) {g : Matrix (ZMod Nx) (Fin N) ℝ} {T' h' : ℝ → ZMod Nx → ℝ}
    {g' : ℝ → Matrix (ZMod Nx) (Fin N) ℝ}
    (hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.IsFullStep ε Ψ T h g (T' ε) (h' ε) (g' ε)) :
    (∀ j k, Tendsto (fun ε => g' ε j k) (𝓝[>] 0)
      (𝓝 ((-vecMulVec (P.limitFlux Ψ T) (bvec N)) j k))) ∧
    ∀ i, Tendsto (fun ε => (1 + 2 * P.a * Ψ i / P.cν) * ((T' ε i - T i) / P.Δt)) (𝓝[>] 0)
      (𝓝 (P.diffOp Ψ T i)) := by
  have hc := hP.c_pos
  have hΔt := hP.Δt_pos
  have hΔx := hP.Δx_pos
  have hcν := hP.cν_pos
  have ha := hP.a_pos
  have hσf (j : ZMod Nx) : 0 < P.σf j := hP.σ₀_pos.trans_le (hP.σf_ge j)
  have hσc (i : ZMod Nx) : 0 < P.σc i := hP.σ₀_pos.trans_le (hP.σc_ge i)
  have hκ : 0 < P.κ := by
    simp only [κ]
    positivity
  have hpre (j : ZMod Nx) (k : Fin N) : Tendsto (fun ε => g' ε j k) (𝓝[>] 0)
      (𝓝 (-(P.limitFlux Ψ T j * bvec N k))) := by
    set A := P.a * P.c * ((Ψ (j + 1) + Ψ j) / 2) * Dp P.Δx T j with hA
    set G : ℝ → ℝ := fun ε => (ε ^ 2 / (P.c * P.Δt) * g j k - ε * P.flux g j k -
      bvec N k * (A + ε ^ 2 * Dp P.Δx h j)) / (ε ^ 2 / (P.c * P.Δt) + P.σf j) with hG
    have hcont : ContinuousAt G 0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simpa using (hσf j).ne'
    have hG0 : G 0 = -(P.limitFlux Ψ T j * bvec N k) := by
      simp only [hG, limitFlux, ← hA]
      have := (hσf j).ne'
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
        sub_zero, zero_sub, add_zero, zero_add]
      field_simp
    have hform : ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε = g' ε j k := by
      filter_upwards [hs] with ε hε
      have h1 := hε.micro_eq j k
      have hden : ε ^ 2 / (P.c * P.Δt) + P.σf j ≠ 0 := by
        have := hσf j
        positivity
      simp only [hG]
      rw [div_eq_iff hden]
      simp only [source, ← hA] at h1
      linear_combination -h1
    have := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).congr' hform
    rwa [hG0] at this
  refine ⟨fun j k => ?_, fun i => ?_⟩
  · simpa [Matrix.vecMulVec_apply] using hpre j k
  have hb0 : bvec N 0 = γ₁ := by simp [bvec]
  refine P.macro_tendsto hP hΨ (hs.mono fun ε hε => hε.macro_eq) (hs.mono fun ε hε => hε.temp_eq)
    (fun j => ?_) i
  have := hpre j 0
  rwa [hb0, mul_comm] at this

end Params

/-- A nonzero vector has a dual vector. -/
lemma exists_dotProduct_eq_one {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : v ≠ 0) :
    ∃ y : ι → ℝ, v ⬝ᵥ y = 1 := by
  have h : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.1 h)
  refine ⟨(v ⬝ᵥ v)⁻¹ • v, ?_⟩
  rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ h]

/-- If `A B = -w bᵀ` with `b ≠ 0`, then `w` lies in the range of `A`. -/
lemma mem_range_of_mul_eq {m n κ : Type*} [Fintype n] [Fintype κ] {A : Matrix m κ ℝ}
    {B : Matrix κ n ℝ} {w : m → ℝ} {b : n → ℝ} (hb : b ≠ 0) (h : A * B = -vecMulVec w b) :
    w ∈ Set.range A.mulVec := by
  obtain ⟨y, hy⟩ := exists_dotProduct_eq_one hb
  refine ⟨B *ᵥ (-y), ?_⟩
  rw [Matrix.mulVec_mulVec, h]
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Matrix.neg_apply, Matrix.vecMulVec_apply,
    neg_mul, mul_neg, neg_neg, mul_assoc, ← Finset.mul_sum]
  have hy' : ∑ k, b k * y k = 1 := hy
  rw [hy', mul_one]

lemma mulVec_mulVec_transpose_of_mem {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]
    {U : Matrix m ι ℝ} (hU : Uᵀ * U = 1) {x : m → ℝ} (hx : x ∈ Set.range U.mulVec) :
    U *ᵥ (Uᵀ *ᵥ x) = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [Matrix.mulVec_mulVec y Uᵀ U, hU, Matrix.one_mulVec]

/-- The shifted weighted Gram matrix `c + Xᵀ Σ X` is injective for `c ≥ 0`, `σ > 0` and orthonormal
`X`: the paper's "`∑ σ X Xᵀ`" is invertible, and the implicit collision terms can be solved. -/
lemma eq_zero_of_shifted_mul_eq_zero {Nx : ℕ} [NeZero Nx] {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] {σ : ZMod Nx → ℝ} (hσ : ∀ j, 0 < σ j) {c : ℝ} (hc : 0 ≤ c)
    {X : Matrix (ZMod Nx) ι ℝ} (hX : Xᵀ * X = 1) {Y : Matrix ι κ ℝ}
    (h : (c • (1 : Matrix ι ι ℝ) + Xᵀ * diagonal σ * X) * Y = 0) : Y = 0 := by
  have h1 : c * (⟪Y, Y⟫ : ℝ) + ⟪X * Y, diagonal σ * (X * Y)⟫ = 0 := by
    have e : (⟪Y, (c • (1 : Matrix ι ι ℝ) + Xᵀ * diagonal σ * X) * Y⟫ : ℝ) =
        c * ⟪Y, Y⟫ + ⟪X * Y, diagonal σ * (X * Y)⟫ := by
      rw [Matrix.add_mul, inner_add_right, Matrix.smul_mul, Matrix.one_mul, real_inner_smul_right,
        Frobenius.inner_mul_left X Y, show Xᵀ * (diagonal σ * (X * Y)) =
          (Xᵀ * diagonal σ * X) * Y by simp only [Matrix.mul_assoc]]
    rw [← e, h, inner_zero_right]
  have h2 : (0 : ℝ) ≤ ⟪Y, Y⟫ := real_inner_self_nonneg
  have h3 : (⟪X * Y, diagonal σ * (X * Y)⟫ : ℝ) =
      ∑ j, ∑ k, σ j * ((X * Y) j k * (X * Y) j k) := by
    rw [Frobenius.inner_def]
    simp only [Matrix.diagonal_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have h4 : ∀ j k, 0 ≤ σ j * ((X * Y) j k * (X * Y) j k) := fun j k =>
    mul_nonneg (hσ j).le (mul_self_nonneg _)
  have h5 : (0 : ℝ) ≤ ⟪X * Y, diagonal σ * (X * Y)⟫ := by
    rw [h3]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => h4 j k
  have h0 : (⟪X * Y, diagonal σ * (X * Y)⟫ : ℝ) = 0 := by nlinarith [mul_nonneg hc h2]
  rw [h3] at h0
  have hz : X * Y = 0 := by
    ext j k
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg fun k _ => h4 j k)).1 h0 j (Finset.mem_univ j)
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h4 j k)).1 hj k (Finset.mem_univ k)
    have hne := (hσ j).ne'
    simpa [hne] using hk
  calc Y = (Xᵀ * X) * Y := by rw [hX, Matrix.one_mul]
    _ = Xᵀ * (X * Y) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [hz, Matrix.mul_zero]

/-- The case `c = 0` of `eq_zero_of_shifted_mul_eq_zero`. -/
lemma eq_zero_of_weighted_mul_eq_zero {Nx : ℕ} [NeZero Nx] {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] {σ : ZMod Nx → ℝ} (hσ : ∀ j, 0 < σ j)
    {X : Matrix (ZMod Nx) ι ℝ} (hX : Xᵀ * X = 1) {Y : Matrix ι κ ℝ}
    (h : (Xᵀ * diagonal σ * X) * Y = 0) : Y = 0 :=
  eq_zero_of_shifted_mul_eq_zero hσ le_rfl hX (by simpa using h)

/-- The shifted weighted Gram matrix is invertible. -/
lemma isUnit_det_shifted {Nx : ℕ} [NeZero Nx] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : ZMod Nx → ℝ} (hσ : ∀ j, 0 < σ j) {c : ℝ} (hc : 0 ≤ c) {X : Matrix (ZMod Nx) ι ℝ}
    (hX : Xᵀ * X = 1) : IsUnit (c • (1 : Matrix ι ι ℝ) + Xᵀ * diagonal σ * X).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h : (c • (1 : Matrix ι ι ℝ) + Xᵀ * diagonal σ * X) *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub, sub_eq_zero]
    exact hab
  have hY := eq_zero_of_shifted_mul_eq_zero (κ := Unit) (Y := replicateCol Unit (a - b)) hσ hc hX
    (by
      ext i u
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun h i)
  funext i
  have := congrFun (congrFun hY i) ()
  simpa [sub_eq_zero] using this

namespace Params

/-- The S-step at `ε = 0`, eq. (4.22) and its fixed-rank analogue: if `X'` captures the limiting
flux `w`, the Galerkin step returns `S' = -(X'ᵀ w)(bᵀ V')`. -/
theorem IsSStep.limit {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] {σ₀ : ℝ}
    (hP : P.Admissible σ₀) {Ψ T h : ZMod Nx → ℝ} {St S' : Matrix ι ι' ℝ}
    {X' : Matrix (ZMod Nx) ι ℝ} {V' : Matrix (Fin N) ι' ℝ} (hX' : X'ᵀ * X' = 1)
    (hw : P.limitFlux Ψ T ∈ Set.range X'.mulVec) (hS : P.IsSStep 0 Ψ T h St X' V' S') :
    S' = -vecMulVec (X'ᵀ *ᵥ P.limitFlux Ψ T) (bvec N ᵥ* V') := by
  set w := P.limitFlux Ψ T with hwdef
  set c := X'ᵀ *ᵥ w with hc
  have hproj : X' *ᵥ c = w := mulVec_mulVec_transpose_of_mem hX' hw
  have hF : P.source 0 Ψ T h = diagonal P.σf *ᵥ w := by
    ext j
    rw [Matrix.mulVec_diagonal, P.source_zero hP]
  have hq : X'ᵀ *ᵥ P.source 0 Ψ T h = (X'ᵀ * diagonal P.σf * X') *ᵥ c := by
    rw [hF, ← hproj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have e0 : ((0 : ℝ) ^ 2 / (P.c * P.Δt)) = 0 := by simp
  have hS' := hS
  rw [IsSStep, e0, zero_smul, zero_smul, neg_zero, zero_sub, hq, ← Matrix.mul_vecMulVec] at hS'
  have hz : (X'ᵀ * diagonal P.σf * X') * (S' + vecMulVec c (bvec N ᵥ* V')) = 0 := by
    rw [Matrix.mul_add]
    have h2 := hS'.symm
    calc (X'ᵀ * diagonal P.σf * X') * S' + (X'ᵀ * diagonal P.σf * X') * vecMulVec c (bvec N ᵥ* V')
        = -(-((X'ᵀ * diagonal P.σf * X') * vecMulVec c (bvec N ᵥ* V')) -
            (X'ᵀ * diagonal P.σf * X') * S') := by abel
      _ = 0 := by rw [h2, neg_zero]
  have := eq_zero_of_weighted_mul_eq_zero
    (fun j => hP.σ₀_pos.trans_le (hP.σf_ge j)) hX' hz
  exact eq_neg_of_add_eq_zero_left this

/-- **arXiv 2402.16746, Theorem 3** (asymptotic preservation of the fixed-rank BUG integrator), at
`ε = 0`, which is what the paper's proof computes. The range inclusions `w ∈ range Xⁿ⁺¹`,
`b ∈ range Vⁿ⁺¹` are derived from the K- and L-steps, and then (4.7), (4.8) and the discrete
diffusion equation follow.

* The paper states Theorem 3 with `∂ₓ(σ⁻¹ ∂ₓ T)`. This misses the factor `Ψ` of Theorem 1 and of
  (4.8); we prove the version with `Ψ`.
* The range inclusions need two hypotheses, `bᵀ Vⁿ ≠ 0` and `Xⁿᵀ Ψδ⁰(acT) ≠ 0`. Without the first,
  the K-step gives `Kⁿ⁺¹ = 0` and says nothing about `Xⁿ⁺¹`. They replace the paper's assumption
  that `S_Lᵀ ∑ σ X Xᵀ` is invertible, which cannot hold for `r ≥ 2`
  (`theorem_3_invertible_rank_le_one`).

The hypotheses concern the old data only, and steps exist for all such data
(`exists_isFixedRankStep`). The genuine limit is `theorem_3_tendsto`. -/
theorem theorem_3 {σ₀ : ℝ} (hP : P.Admissible σ₀) {r : ℕ} {Ψ T h T' h' : ZMod Nx → ℝ}
    {X X' K' : Matrix (ZMod Nx) (Fin r) ℝ} {L' V V' : Matrix (Fin N) (Fin r) ℝ}
    {S SK SL S' : Matrix (Fin r) (Fin r) ℝ}
    (hs : P.IsFixedRankStep 0 Ψ T h X S V K' L' X' SK V' SL S' T' h')
    (hb : bvec N ᵥ* V ≠ 0) (hq : Xᵀ *ᵥ P.source 0 Ψ T h ≠ 0) :
    P.limitFlux Ψ T ∈ Set.range X'.mulVec ∧ bvec N ∈ Set.range V'.mulVec ∧
      S' = -vecMulVec (X'ᵀ *ᵥ P.limitFlux Ψ T) (bvec N ᵥ* V') ∧
      X' * S' * V'ᵀ = -vecMulVec (P.limitFlux Ψ T) (bvec N) ∧
      ∀ i, (1 + 2 * P.a * Ψ i / P.cν) * ((T' i - T i) / P.Δt) = P.diffOp Ψ T i := by
  set w := P.limitFlux Ψ T with hwdef
  have e0 : ((0 : ℝ) ^ 2 / (P.c * P.Δt)) = 0 := by simp
  -- `w ∈ range X'`
  have hwr : w ∈ Set.range X'.mulVec := by
    have hK := hs.K_eq
    rw [IsKStep, e0, zero_smul, zero_smul, neg_zero, zero_sub] at hK
    have hent (j : ZMod Nx) (m : Fin r) : K' j m = -(w j * (bvec N ᵥ* V) m) := by
      have h1 := congrFun (congrFun hK j) m
      simp only [Matrix.zero_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.vecMulVec_apply,
        Matrix.diagonal_mul, P.source_zero hP] at h1
      have hσ : P.σf j ≠ 0 := (hP.σ₀_pos.trans_le (hP.σf_ge j)).ne'
      have : P.σf j * (K' j m + w j * (bvec N ᵥ* V) m) = 0 := by linear_combination h1
      have := (mul_eq_zero.1 this).resolve_left hσ
      linarith
    refine mem_range_of_mul_eq (B := SK) hb ?_
    rw [← hs.K_qr]
    ext j m
    simp [Matrix.vecMulVec_apply, hent]
  -- `b ∈ range V'`
  have hbr : bvec N ∈ Set.range V'.mulVec := by
    have hL := hs.L_eq
    rw [IsLStep, e0, zero_smul, zero_smul, neg_zero, zero_sub] at hL
    have hLZ : L' * (Xᵀ * diagonal P.σf * X) =
        -vecMulVec (bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) := by
      have h2 := hL.symm
      calc L' * (Xᵀ * diagonal P.σf * X)
          = -(-vecMulVec (bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) - L' * (Xᵀ * diagonal P.σf * X)) -
            vecMulVec (bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) := by abel
        _ = _ := by rw [h2, neg_zero, zero_sub]
    refine mem_range_of_mul_eq (B := SLᵀ * (Xᵀ * diagonal P.σf * X)) hq ?_
    rw [← Matrix.mul_assoc, ← hs.L_qr, hLZ]
  have hS := hs.S_eq.limit P hP hs.X'_orth hwr
  have hg : X' * S' * V'ᵀ = -vecMulVec w (bvec N) := by
    have h1 : X' *ᵥ (X'ᵀ *ᵥ w) = w := mulVec_mulVec_transpose_of_mem hs.X'_orth hwr
    have h2 : (bvec N ᵥ* V') ᵥ* V'ᵀ = bvec N := by
      rw [← Matrix.mulVec_transpose, Matrix.transpose_transpose, ← Matrix.mulVec_transpose]
      exact mulVec_mulVec_transpose_of_mem hs.V'_orth hbr
    rw [hS, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, h1, h2]
  refine ⟨hwr, hbr, hS, hg, fun i => ?_⟩
  have hm := hs.macro_eq i
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
    zero_add] at hm
  refine P.diffusion_of_limit hP (fun j => ?_) i hm (hs.temp_eq i)
  rw [hg]
  simp [Matrix.vecMulVec_apply, bvec, mul_comm, hwdef]

/-- The paper's assumption "`S_Lᵀ ∑ σ X Xᵀ` is invertible" in the proof of arXiv 2402.16746,
Theorem 3 can hold at `ε = 0` only for rank `r ≤ 1`: the L-step gives
`Vⁿ⁺¹ (S_Lᵀ ∑ σ X Xᵀ) = -b (∑ X Ψδ⁰(acT))ᵀ`, of rank at most one. -/
theorem theorem_3_invertible_rank_le_one {r : ℕ} {Ψ T h : ZMod Nx → ℝ}
    {X : Matrix (ZMod Nx) (Fin r) ℝ} {L' V V' : Matrix (Fin N) (Fin r) ℝ}
    {S SL : Matrix (Fin r) (Fin r) ℝ} (hL : P.IsLStep 0 Ψ T h X S V L')
    (hV' : V'ᵀ * V' = 1) (hqr : L' = V' * SLᵀ)
    (hinv : IsUnit (SLᵀ * (Xᵀ * diagonal P.σf * X)).det) : r ≤ 1 := by
  have e0 : ((0 : ℝ) ^ 2 / (P.c * P.Δt)) = 0 := by simp
  rw [IsLStep, e0, zero_smul, zero_smul, neg_zero, zero_sub] at hL
  have hLZ : V' * (SLᵀ * (Xᵀ * diagonal P.σf * X)) =
      vecMulVec (-bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) := by
    have h2 := hL.symm
    have e : vecMulVec (-bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) =
        -vecMulVec (bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) := by
      ext i k
      simp [Matrix.vecMulVec_apply]
    rw [e, ← Matrix.mul_assoc, ← hqr]
    calc L' * (Xᵀ * diagonal P.σf * X)
        = -(-vecMulVec (bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) - L' * (Xᵀ * diagonal P.σf * X)) -
          vecMulVec (bvec N) (Xᵀ *ᵥ P.source 0 Ψ T h) := by abel
      _ = _ := by rw [h2, neg_zero, zero_sub]
  have hrank := Matrix.rank_mul_eq_left_of_isUnit_det _ V' hinv
  rw [hLZ, rank_eq_card_of_transpose_mul_eq_one hV', Fintype.card_fin] at hrank
  rw [← hrank]
  exact Matrix.rank_vecMulVec_le _ _

end Params

/-! ### The asymptotic-preserving rank-adaptive integrator -/

/-- The first column `b / γ₁ = e₁` of `V̂ⁿ⁺¹`. The paper writes `V̂^ap = [b]`, but `V̂ⁿ⁺¹` has
orthonormal columns and `‖b‖ = γ₁`. -/
noncomputable def e₁col (N : ℕ) [NeZero N] : Matrix (Fin N) Unit ℝ :=
  replicateCol Unit fun k => bvec N k / γ₁

lemma bvec_vecMul_hat {q : Type*} [Fintype q] [DecidableEq q]
    {Vrem : Matrix (Fin N) q ℝ}
    (hV : (fromCols (e₁col N) Vrem)ᵀ * fromCols (e₁col N) Vrem = 1) :
    bvec N ᵥ* fromCols (e₁col N) Vrem = Sum.elim (fun _ => γ₁) 0 := by
  classical
  funext x
  have hγ : γ₁ ≠ 0 := γ₁_pos.ne'
  have h1 := congrFun (congrFun hV (Sum.inl ())) x
  rw [Matrix.mul_apply] at h1
  simp only [Matrix.transpose_apply, fromCols_apply_inl, e₁col, Matrix.replicateCol_apply] at h1
  have e : (bvec N ᵥ* fromCols (e₁col N) Vrem) x =
      γ₁ * ∑ k, bvec N k / γ₁ * fromCols (e₁col N) Vrem k x := by
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, e₁col]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [e]
  simp only [e₁col] at h1 ⊢
  rw [h1]
  rcases x with u | m
  · simp
  · simp

section Adaptive

variable {ρ ι q q' τ ρs ρ₁ : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ι] [Fintype q]
  [DecidableEq q] [Fintype q'] [DecidableEq q'] [Fintype τ] [DecidableEq τ] [Fintype ρs]
  [DecidableEq ρs] [Fintype ρ₁] [DecidableEq ρ₁]

/-- `Vⁿ⁺¹ = [V̂^ap, Wⁿ⁺¹]`, with `Wⁿ⁺¹ = V̂^rem Ŵ`. -/
noncomputable def adaptV (Vrem : Matrix (Fin N) q ℝ) (W : Matrix q τ ℝ) (f : ρs ↪ τ) :
    Matrix (Fin N) (Unit ⊕ ρs) ℝ :=
  fromCols (e₁col N) (Vrem * W.submatrix id f)

/-- `Sⁿ⁺¹ = R₂ diag(S^ap, S^rem)`, eq. (4.19), with `S^rem = Σ̂`. -/
noncomputable def adaptS (R₂ : Matrix ρ₁ (Unit ⊕ ρs) ℝ) (Sa : Matrix Unit Unit ℝ) (s : τ → ℝ)
    (f : ρs ↪ τ) : Matrix ρ₁ (Unit ⊕ ρs) ℝ :=
  R₂ * (fromBlocks Sa 0 0 (diagonal (s ∘ f)) : Matrix (Unit ⊕ ρs) (Unit ⊕ ρs) ℝ)

namespace Params

/-- One step of the modal macro-micro BUG integrator of arXiv 2402.16746, Section 4.2.

1. `K'`, `L'` come from (4.2), (4.3). `Xh = X̂ⁿ⁺¹` is orthonormal and captures `w`, `K'`, `X`, and
   `V̂ⁿ⁺¹ = [e₁, Vrem]` is orthonormal and captures `L'`, `V`.
2. `Sh = Ŝⁿ⁺¹` is the Galerkin step from `M̂ S N̂ᵀ`. (The paper's `M̂ᵀ S N̂ᵀ` does not fit the
   dimensions.)
3. `K̂ = X̂ Ŝ` is split into its first column `K̂^ap` and the rest `K̂^rem`. (The paper also says
   `K̂^ap = (σ^a)⁻¹Ψδ⁰(acT)`, which is the direction at `ε = 0` only.) `K̂^rem = Xr Sr` is a QR
   decomposition, `Sr = U diag(s) Wᵀ` an SVD of which the triples selected by `f` are kept (the
   paper keeps the `r*` largest), `K̂^ap = Xa Sa` a QR decomposition, and `[Xa, Xr Û] = X' R₂`.
4. `T'`, `h'` come from (4.20), (4.21). -/
structure IsAdaptiveStep (ε : ℝ) (Ψ T h : ZMod Nx → ℝ) (X : Matrix (ZMod Nx) ρ ℝ) (S : Matrix ρ ρ ℝ)
    (V : Matrix (Fin N) ρ ℝ) (K' : Matrix (ZMod Nx) ρ ℝ) (L' : Matrix (Fin N) ρ ℝ)
    (Xh : Matrix (ZMod Nx) ι ℝ) (Vrem : Matrix (Fin N) q ℝ) (Sh : Matrix ι (Unit ⊕ q) ℝ)
    (Xr : Matrix (ZMod Nx) q' ℝ) (Sr : Matrix q' q ℝ) (U : Matrix q' τ ℝ) (W : Matrix q τ ℝ)
    (s : τ → ℝ) (f : ρs ↪ τ) (Xa : Matrix (ZMod Nx) Unit ℝ) (Sa : Matrix Unit Unit ℝ)
    (X' : Matrix (ZMod Nx) ρ₁ ℝ) (R₂ : Matrix ρ₁ (Unit ⊕ ρs) ℝ) (T' h' : ZMod Nx → ℝ) : Prop where
  K_eq : P.IsKStep ε Ψ T h X S V K'
  L_eq : P.IsLStep ε Ψ T h X S V L'
  Xh_orth : Xhᵀ * Xh = 1
  Xh_w : P.limitFlux Ψ T ∈ Set.range Xh.mulVec
  Xh_K : Xh * Xhᵀ * K' = K'
  Xh_X : Xh * Xhᵀ * X = X
  Vh_orth : (fromCols (e₁col N) Vrem)ᵀ * fromCols (e₁col N) Vrem = 1
  Vh_L : fromCols (e₁col N) Vrem * (fromCols (e₁col N) Vrem)ᵀ * L' = L'
  Vh_V : fromCols (e₁col N) Vrem * (fromCols (e₁col N) Vrem)ᵀ * V = V
  S_eq : P.IsSStep ε Ψ T h ((Xhᵀ * X) * S * (Vᵀ * fromCols (e₁col N) Vrem)) Xh
    (fromCols (e₁col N) Vrem) Sh
  rem_qr : (Xh * Sh).submatrix id Sum.inr = Xr * Sr
  Xr_orth : Xrᵀ * Xr = 1
  svd : Sr = U * diagonal s * Wᵀ
  U_orth : Uᵀ * U = 1
  W_orth : Wᵀ * W = 1
  ap_qr : (Xh * Sh).submatrix id Sum.inl = Xa * Sa
  Xa_orth : Xaᵀ * Xa = 1
  X'_orth : X'ᵀ * X' = 1
  R₂_eq : fromCols Xa (Xr * U.submatrix id f) = X' * R₂
  macro_eq : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * Ψ i * h' i +
    γ₁ / 2 * Dm P.Δx (fun j => (X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ) j 0) i =
      -P.σc i * h' i
  temp_eq : ∀ i, (T' i - T i) / P.Δt = P.κ * P.σc i * h' i

end Params

/-- Keeping singular triples: `Ŝ^rem Ŵ = Û S^rem`. -/
lemma svd_trunc {q q' τ ρs : Type*} [Fintype q] [Fintype τ] [DecidableEq τ] {Sr : Matrix q' q ℝ}
    {U : Matrix q' τ ℝ} {W : Matrix q τ ℝ} {s : τ → ℝ} {f : ρs ↪ τ} [DecidableEq ρs] [Fintype ρs]
    (hsvd : Sr = U * diagonal s * Wᵀ) (hW : Wᵀ * W = 1) :
    Sr * W.submatrix id f = U.submatrix id f * diagonal (s ∘ f) := by
  have hW1 : Wᵀ * W.submatrix id f = (1 : Matrix τ τ ℝ).submatrix id f := by
    rw [← hW]
    ext a b
    simp [Matrix.mul_apply]
  have hUfeq : U * (1 : Matrix τ τ ℝ).submatrix id f = U.submatrix id f := by
    ext a b
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hd1 : diagonal s * (1 : Matrix τ τ ℝ).submatrix id f =
      (1 : Matrix τ τ ℝ).submatrix id f * diagonal (s ∘ f) := by
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, id,
      Function.comp, Matrix.one_apply]
    split_ifs with hab
    · rw [hab]
      ring
    · simp
  calc Sr * W.submatrix id f = U * diagonal s * (Wᵀ * W.submatrix id f) := by
        rw [hsvd]
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal s * (1 : Matrix τ τ ℝ).submatrix id f) := by
        rw [hW1, Matrix.mul_assoc]
    _ = U * (1 : Matrix τ τ ℝ).submatrix id f * diagonal (s ∘ f) := by
        rw [hd1, Matrix.mul_assoc]
    _ = U.submatrix id f * diagonal (s ∘ f) := by rw [hUfeq]

lemma bvec_ne_zero : bvec N ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [bvec, ite_true, Pi.zero_apply] at this
  exact γ₁_pos.ne' this

namespace Params

/-- **arXiv 2402.16746, Theorem 6** (the integrator of Section 4.2 is asymptotic-preserving in the
sense of Theorem 3), at `ε = 0`: the truncated factors keep `w` and `b` in their ranges, (4.22)
holds for them, `gⁿ⁺¹ = -w bᵀ`, and `Tⁿ⁺¹` solves the discrete diffusion equation.

No invertibility is assumed. The paper's proof goes through its Lemma 1, whose hypotheses cannot
hold here: at `ε = 0` one has `Ŝ^rem = 0` (`IsAdaptiveStep.Sr_eq_zero`), so the inverses of
`Ŝ^rem` and of `S^rem` in that proof do not exist. The direct argument is that `K̂^rem = 0`, so
the truncation of the remainder changes nothing. -/
theorem theorem_6 {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ T h T' h' : ZMod Nx → ℝ}
    {X : Matrix (ZMod Nx) ρ ℝ} {S : Matrix ρ ρ ℝ} {V : Matrix (Fin N) ρ ℝ}
    {K' : Matrix (ZMod Nx) ρ ℝ} {L' : Matrix (Fin N) ρ ℝ} {Xh : Matrix (ZMod Nx) ι ℝ}
    {Vrem : Matrix (Fin N) q ℝ} {Sh : Matrix ι (Unit ⊕ q) ℝ} {Xr : Matrix (ZMod Nx) q' ℝ}
    {Sr : Matrix q' q ℝ} {U : Matrix q' τ ℝ} {W : Matrix q τ ℝ} {s : τ → ℝ} {f : ρs ↪ τ}
    {Xa : Matrix (ZMod Nx) Unit ℝ} {Sa : Matrix Unit Unit ℝ} {X' : Matrix (ZMod Nx) ρ₁ ℝ}
    {R₂ : Matrix ρ₁ (Unit ⊕ ρs) ℝ}
    (hs : P.IsAdaptiveStep 0 Ψ T h X S V K' L' Xh Vrem Sh Xr Sr U W s f Xa Sa X' R₂ T' h') :
    P.limitFlux Ψ T ∈ Set.range X'.mulVec ∧ bvec N ∈ Set.range (adaptV Vrem W f).mulVec ∧
      adaptS R₂ Sa s f =
        -vecMulVec (X'ᵀ *ᵥ P.limitFlux Ψ T) (bvec N ᵥ* adaptV Vrem W f) ∧
      X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ =
        -vecMulVec (P.limitFlux Ψ T) (bvec N) ∧
      ∀ i, (1 + 2 * P.a * Ψ i / P.cν) * ((T' i - T i) / P.Δt) = P.diffOp Ψ T i := by
  set w := P.limitFlux Ψ T with hwdef
  set Vh := fromCols (e₁col N) Vrem with hVh
  have hγ : γ₁ ≠ 0 := γ₁_pos.ne'
  have hS := hs.S_eq.limit P hP hs.Xh_orth hs.Xh_w
  have hbV := bvec_vecMul_hat hs.Vh_orth
  have hproj : Xh *ᵥ (Xhᵀ *ᵥ w) = w := mulVec_mulVec_transpose_of_mem hs.Xh_orth hs.Xh_w
  have hK : Xh * Sh = -vecMulVec w (bvec N ᵥ* Vh) := by
    rw [hS, Matrix.mul_neg, Matrix.mul_vecMulVec, hproj]
  have hrem : (Xh * Sh).submatrix id Sum.inr = 0 := by
    ext j m
    simp [hK, Matrix.vecMulVec_apply, hbV, hVh]
  have hSr : Sr = 0 := by
    have h1 := hs.rem_qr
    rw [hrem] at h1
    calc Sr = (Xrᵀ * Xr) * Sr := by rw [hs.Xr_orth, Matrix.one_mul]
      _ = Xrᵀ * (Xr * Sr) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [← h1, Matrix.mul_zero]
  have hs0 : diagonal s = 0 := by
    calc diagonal s = (Uᵀ * U) * diagonal s * (Wᵀ * W) := by
          rw [hs.U_orth, hs.W_orth, Matrix.one_mul, Matrix.mul_one]
      _ = Uᵀ * (U * diagonal s * Wᵀ) * W := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [← hs.svd, hSr, Matrix.mul_zero, Matrix.zero_mul]
  have hDiag : diagonal (s ∘ f) = (0 : Matrix ρs ρs ℝ) := by
    have h0 : s = 0 := by
      ext t
      simpa using congrFun (congrFun hs0 t) t
    rw [h0]
    ext a b
    simp [Matrix.diagonal_apply]
  have hap : ∀ j, (Xa * Sa) j () = -(w j * γ₁) := by
    intro j
    rw [← hs.ap_qr]
    simp [hK, Matrix.vecMulVec_apply, hbV, hVh]
  have hg : X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ = -vecMulVec w (bvec N) := by
    rw [adaptS, hDiag, ← Matrix.mul_assoc, ← hs.R₂_eq, adaptV, Matrix.transpose_fromCols,
      Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero]
    rw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, e₁col, Matrix.replicateCol_apply,
      Matrix.neg_apply, Matrix.vecMulVec_apply, Fintype.univ_unit, Finset.sum_singleton]
    have := hap j
    rw [Matrix.mul_apply] at this
    simp only [Fintype.univ_unit, Finset.sum_singleton] at this
    rw [this]
    field_simp
  have hŴ : (W.submatrix id f)ᵀ * W.submatrix id f = 1 := by
    have : (W.submatrix id f)ᵀ * W.submatrix id f = (Wᵀ * W).submatrix f f := by
      ext a b
      simp [Matrix.mul_apply]
    rw [this, hs.W_orth, Matrix.submatrix_one _ f.injective]
  set E : Matrix (Unit ⊕ q) (Unit ⊕ ρs) ℝ := fromBlocks 1 0 0 (W.submatrix id f) with hE
  have hV'fact : adaptV Vrem W f = Vh * E := by
    rw [hVh, hE, Matrix.fromCols_mul_fromBlocks]
    simp [adaptV]
  have hV' : (adaptV Vrem W f)ᵀ * adaptV Vrem W f = 1 := by
    rw [hV'fact, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vhᵀ, hs.Vh_orth,
      Matrix.one_mul, hE, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, hŴ, Matrix.fromBlocks_one]
  have hS' : adaptS R₂ Sa s f = -vecMulVec (X'ᵀ *ᵥ w) (bvec N ᵥ* adaptV Vrem W f) := by
    calc adaptS R₂ Sa s f =
        (X'ᵀ * X') * adaptS R₂ Sa s f * ((adaptV Vrem W f)ᵀ * adaptV Vrem W f) := by
          rw [hs.X'_orth, hV', Matrix.one_mul, Matrix.mul_one]
      _ = X'ᵀ * (X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ) * adaptV Vrem W f := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have hwr : w ∈ Set.range X'.mulVec := by
    refine mem_range_of_mul_eq (B := adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ) bvec_ne_zero ?_
    rw [← Matrix.mul_assoc, hg]
  have hbr : bvec N ∈ Set.range (adaptV Vrem W f).mulVec := by
    refine ⟨Sum.elim (fun _ => γ₁) 0, ?_⟩
    ext k
    simp only [adaptV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      fromCols_apply_inl, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, e₁col,
      Matrix.replicateCol_apply, Fintype.univ_unit, Finset.sum_singleton]
    field_simp
  refine ⟨hwr, hbr, hS', hg, fun i => ?_⟩
  have hm := hs.macro_eq i
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
    zero_add] at hm
  refine P.diffusion_of_limit hP (fun j => ?_) i hm (hs.temp_eq i)
  rw [hg]
  simp [Matrix.vecMulVec_apply, bvec, mul_comm, hwdef]

/-- arXiv 2402.16746, Theorem 5, for the integrator of Section 4.2, which has the macro update
(4.20), (4.21) with the truncated `gⁿ⁺¹`: the conservation laws (4.16a), (4.16b) and the
conservation of the total mass, for linear emission on the periodic grid. The paper states this
for the fixed-rank integrator and says in its introduction that the proposed algorithm also has
it. -/
theorem theorem_5_adaptive {ε : ℝ} (hc : P.c ≠ 0) (hcν : P.cν ≠ 0) (hΔt : P.Δt ≠ 0)
    {T h T' h' : ZMod Nx → ℝ} {X : Matrix (ZMod Nx) ρ ℝ} {S : Matrix ρ ρ ℝ}
    {V : Matrix (Fin N) ρ ℝ} {K' : Matrix (ZMod Nx) ρ ℝ} {L' : Matrix (Fin N) ρ ℝ}
    {Xh : Matrix (ZMod Nx) ι ℝ} {Vrem : Matrix (Fin N) q ℝ} {Sh : Matrix ι (Unit ⊕ q) ℝ}
    {Xr : Matrix (ZMod Nx) q' ℝ} {Sr : Matrix q' q ℝ} {U : Matrix q' τ ℝ} {W : Matrix q τ ℝ}
    {s : τ → ℝ} {f : ρs ↪ τ} {Xa : Matrix (ZMod Nx) Unit ℝ} {Sa : Matrix Unit Unit ℝ}
    {X' : Matrix (ZMod Nx) ρ₁ ℝ} {R₂ : Matrix ρ₁ (Unit ⊕ ρs) ℝ}
    (hs : P.IsAdaptiveStep ε 1 T h X S V K' L' Xh Vrem Sh Xr Sr U W s f Xa Sa X' R₂ T' h') :
    (∀ i, ((P.a * P.c * T' i + ε ^ 2 * h' i) - (P.a * P.c * T i + ε ^ 2 * h i)) / P.Δt +
        P.c * (γ₁ / 2) *
          Dm P.Δx (fun j => (X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ) j 0) i =
            -P.c * P.σc i * h' i ∧
      P.cν / 2 * ((T' i - T i) / P.Δt) = P.σc i * h' i) ∧
    ∑ i, ((P.a * P.c * T' i + ε ^ 2 * h' i) / P.c + P.cν / 2 * T' i) =
      ∑ i, ((P.a * P.c * T i + ε ^ 2 * h i) / P.c + P.cν / 2 * T i) := by
  have hm : ∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * h' i +
      γ₁ / 2 * Dm P.Δx (fun j => (X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ) j 0) i =
        -P.σc i * h' i :=
    fun i => by simpa using hs.macro_eq i
  exact ⟨P.local_conservation hc hcν hm hs.temp_eq, P.global_conservation hc hcν hΔt hm hs.temp_eq⟩

/-- At `ε = 0` the remainder vanishes: `K̂^rem = 0`, hence `Ŝ^rem = 0`. So the invertibility of
`Ŝ^rem` assumed in `lemma_1`, and used in the paper's proof of Theorem 6, fails in the regime of
that theorem whenever `q` is nonempty. -/
theorem IsAdaptiveStep.Sr_eq_zero {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ T h T' h' : ZMod Nx → ℝ}
    {X : Matrix (ZMod Nx) ρ ℝ} {S : Matrix ρ ρ ℝ} {V : Matrix (Fin N) ρ ℝ}
    {K' : Matrix (ZMod Nx) ρ ℝ} {L' : Matrix (Fin N) ρ ℝ} {Xh : Matrix (ZMod Nx) ι ℝ}
    {Vrem : Matrix (Fin N) q ℝ} {Sh : Matrix ι (Unit ⊕ q) ℝ} {Xr : Matrix (ZMod Nx) q' ℝ}
    {Sr : Matrix q' q ℝ} {U : Matrix q' τ ℝ} {W : Matrix q τ ℝ} {s : τ → ℝ} {f : ρs ↪ τ}
    {Xa : Matrix (ZMod Nx) Unit ℝ} {Sa : Matrix Unit Unit ℝ} {X' : Matrix (ZMod Nx) ρ₁ ℝ}
    {R₂ : Matrix ρ₁ (Unit ⊕ ρs) ℝ}
    (hs : P.IsAdaptiveStep 0 Ψ T h X S V K' L' Xh Vrem Sh Xr Sr U W s f Xa Sa X' R₂ T' h') :
    Sr = 0 := by
  have hS := hs.S_eq.limit P hP hs.Xh_orth hs.Xh_w
  have hbV := bvec_vecMul_hat hs.Vh_orth
  have hproj := mulVec_mulVec_transpose_of_mem hs.Xh_orth hs.Xh_w
  have hK : Xh * Sh = -vecMulVec (P.limitFlux Ψ T) (bvec N ᵥ* fromCols (e₁col N) Vrem) := by
    rw [hS, Matrix.mul_neg, Matrix.mul_vecMulVec, hproj]
  have hrem : (Xh * Sh).submatrix id Sum.inr = 0 := by
    ext j m
    simp [hK, Matrix.vecMulVec_apply, hbV]
  have h1 := hs.rem_qr
  rw [hrem] at h1
  calc Sr = (Xrᵀ * Xr) * Sr := by rw [hs.Xr_orth, Matrix.one_mul]
    _ = Xrᵀ * (Xr * Sr) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [← h1, Matrix.mul_zero]

/-- **arXiv 2402.16746, Lemma 1**, for every `ε`, on the matrices of the step: if `R₂`, `S^ap`,
`Ŝ^rem` and `S^rem = Σ̂` are invertible, then
`R₂⁻ᵀ diag((S^ap)⁻ᵀ, Ûᵀ (Ŝ^rem)⁻ᵀ) Ŝᵀ Ŝ diag(I, Ŵ) = Sⁿ⁺¹`. The paper leaves these invertibility
assumptions implicit, and they fail at `ε = 0` (`IsAdaptiveStep.Sr_eq_zero`). Here `Ŝ^rem` is
square, `q' = q`, and `R₂` is square, `ρ₁ = Unit ⊕ ρs`. -/
theorem lemma_1 {ε : ℝ} {Ψ T h T' h' : ZMod Nx → ℝ}
    {X : Matrix (ZMod Nx) ρ ℝ} {S : Matrix ρ ρ ℝ} {V : Matrix (Fin N) ρ ℝ}
    {K' : Matrix (ZMod Nx) ρ ℝ} {L' : Matrix (Fin N) ρ ℝ} {Xh : Matrix (ZMod Nx) ι ℝ}
    {Vrem : Matrix (Fin N) q ℝ} {Sh : Matrix ι (Unit ⊕ q) ℝ} {Xr : Matrix (ZMod Nx) q ℝ}
    {Sr : Matrix q q ℝ} {U : Matrix q τ ℝ} {W : Matrix q τ ℝ} {s : τ → ℝ} {f : ρs ↪ τ}
    {Xa : Matrix (ZMod Nx) Unit ℝ} {Sa : Matrix Unit Unit ℝ}
    {X' : Matrix (ZMod Nx) (Unit ⊕ ρs) ℝ} {R₂ : Matrix (Unit ⊕ ρs) (Unit ⊕ ρs) ℝ}
    (hs : P.IsAdaptiveStep ε Ψ T h X S V K' L' Xh Vrem Sh Xr Sr U W s f Xa Sa X' R₂ T' h')
    (hR : IsUnit R₂.det) (hSa : IsUnit Sa.det) (hSr : IsUnit Sr.det)
    (hD : IsUnit (diagonal (s ∘ f) : Matrix ρs ρs ℝ).det) :
    (R₂⁻¹)ᵀ * (fromBlocks (Saᵀ)⁻¹ 0 0 ((U.submatrix id f)ᵀ * (Srᵀ)⁻¹) :
        Matrix (Unit ⊕ ρs) (Unit ⊕ q) ℝ) * (Shᵀ * Sh) *
      (fromBlocks 1 0 0 (W.submatrix id f) : Matrix (Unit ⊕ q) (Unit ⊕ ρs) ℝ) =
      adaptS R₂ Sa s f := by
  set Uf := U.submatrix id f with hUf
  set Wf := W.submatrix id f with hWf
  set Df : Matrix ρs ρs ℝ := diagonal (s ∘ f) with hDf
  set D : Matrix (Unit ⊕ ρs) (Unit ⊕ ρs) ℝ := fromBlocks Sa 0 0 Df with hDdef
  set E : Matrix (Unit ⊕ q) (Unit ⊕ ρs) ℝ := fromBlocks 1 0 0 Wf with hE
  -- `Ŝ^rem Ŵ = Û S^rem`
  have ha : Sr * Wf = Uf * Df := svd_trunc hs.svd hs.W_orth
  -- `X̂ Ŝ diag(I, Ŵ) = Xⁿ⁺¹ R₂ diag(S^ap, S^rem)`
  have hsplit : Xh * Sh = fromCols (Xa * Sa) (Xr * Sr) := by
    rw [← hs.ap_qr, ← hs.rem_qr]
    ext j x
    rcases x with u | m <;> simp
  have hb : Xh * Sh * E = X' * R₂ * D := by
    rw [hsplit, ← hs.R₂_eq, hE, hDdef, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
    rw [Matrix.mul_assoc Xr Sr, ha, Matrix.mul_assoc Xr Uf]
  -- `diag(I, Ŵᵀ) Ŝᵀ Ŝ diag(I, Ŵ) = diag(S^ap, S^rem)ᵀ R₂ᵀ R₂ diag(S^ap, S^rem)`
  have hc : Eᵀ * (Shᵀ * Sh) * E = Dᵀ * (R₂ᵀ * R₂) * D := by
    calc Eᵀ * (Shᵀ * Sh) * E = Eᵀ * Shᵀ * (Xhᵀ * Xh) * Sh * E := by
          rw [hs.Xh_orth]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Xh * Sh * E)ᵀ * (Xh * Sh * E) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (X' * R₂ * D)ᵀ * (X' * R₂ * D) := by rw [hb]
      _ = Dᵀ * (R₂ᵀ * (X'ᵀ * X') * R₂) * D := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Dᵀ * (R₂ᵀ * R₂) * D := by rw [hs.X'_orth, Matrix.mul_one]
  have hSrT : IsUnit Srᵀ.det := by rwa [Matrix.det_transpose]
  have hDT : IsUnit Dfᵀ.det := by rwa [Matrix.det_transpose]
  have hSaT : IsUnit Saᵀ.det := by rwa [Matrix.det_transpose]
  -- `Ûᵀ (Ŝ^rem)⁻ᵀ = (S^rem)⁻ᵀ Ŵᵀ`
  have hd : Ufᵀ * (Srᵀ)⁻¹ = (Dfᵀ)⁻¹ * Wfᵀ := by
    have hT : Wfᵀ * Srᵀ = Dfᵀ * Ufᵀ := by
      rw [← Matrix.transpose_mul, ha, Matrix.transpose_mul]
    calc Ufᵀ * (Srᵀ)⁻¹ = ((Dfᵀ)⁻¹ * Dfᵀ) * Ufᵀ * (Srᵀ)⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ hDT, Matrix.one_mul]
      _ = (Dfᵀ)⁻¹ * (Dfᵀ * Ufᵀ) * (Srᵀ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (Dfᵀ)⁻¹ * (Wfᵀ * Srᵀ) * (Srᵀ)⁻¹ := by rw [hT]
      _ = (Dfᵀ)⁻¹ * Wfᵀ * (Srᵀ * (Srᵀ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = (Dfᵀ)⁻¹ * Wfᵀ := by rw [Matrix.mul_nonsing_inv _ hSrT, Matrix.mul_one]
  set DI : Matrix (Unit ⊕ ρs) (Unit ⊕ ρs) ℝ := fromBlocks (Saᵀ)⁻¹ 0 0 (Dfᵀ)⁻¹ with hDI
  have hDID : DI * Dᵀ = 1 := by
    rw [hDI, hDdef, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.nonsing_inv_mul _ hSaT, Matrix.nonsing_inv_mul _ hDT, Matrix.transpose_zero,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_one]
  have hG : (fromBlocks (Saᵀ)⁻¹ 0 0 (Ufᵀ * (Srᵀ)⁻¹) : Matrix (Unit ⊕ ρs) (Unit ⊕ q) ℝ) =
      DI * Eᵀ := by
    rw [hDI, hE, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hd]
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]
  rw [hG, adaptS]
  calc (R₂⁻¹)ᵀ * (DI * Eᵀ) * (Shᵀ * Sh) * E = (R₂⁻¹)ᵀ * DI * (Eᵀ * (Shᵀ * Sh) * E) := by
        simp only [Matrix.mul_assoc]
    _ = (R₂⁻¹)ᵀ * DI * (Dᵀ * (R₂ᵀ * R₂) * D) := by rw [hc]
    _ = (R₂⁻¹)ᵀ * (DI * Dᵀ) * R₂ᵀ * R₂ * D := by simp only [Matrix.mul_assoc]
    _ = ((R₂⁻¹)ᵀ * R₂ᵀ) * R₂ * D := by rw [hDID, Matrix.mul_one]
    _ = (R₂ * R₂⁻¹)ᵀ * R₂ * D := by rw [Matrix.transpose_mul]
    _ = R₂ * D := by rw [Matrix.mul_nonsing_inv _ hR, Matrix.transpose_one, Matrix.one_mul]

end Params

end Adaptive

/-! ### The sharp CFL condition, and zero boundary values -/

namespace Params

/-- arXiv 2402.16746, Theorem 2, with the sharp constant, for every factorization of the flux
matrix: the conclusion holds under `Δt ≤ (2 ε Δx/|μ_k| + σ₀ Δx²/μ_k²) / (4 c)`, without any
`β_N`. Since `β_N ≥ 2`, this CFL condition is weaker than (3.4) by a factor of at least
`5 β_N / 4 ≥ 5/2`. -/
theorem theorem_2_sharp {σ₀ ε : ℝ} (hP : P.Admissible σ₀) {t₀ : Fin (N + 1) → ℝ}
    (hF : IsFluxFactorization P.μ P.Tm t₀)
    (hCFL : ∀ k, P.μ k ≠ 0 →
      P.Δt ≤ 1 / (4 * P.c) * (2 * ε * P.Δx / |P.μ k| + σ₀ * P.Δx ^ 2 / P.μ k ^ 2))
    {T h T' h' : ZMod Nx → ℝ} {g g' : Matrix (ZMod Nx) (Fin N) ℝ}
    (hs : P.IsFullStep ε 1 T h g T' h' g') :
    P.energy ε T' h' g' ≤ P.energy ε T h g := by
  refine P.energy_le_of_tested hP hF hCFL (fun i => ?_) ?_ hs.temp_eq
  · simpa using hs.macro_eq i
  · simp [hs.microRes_eq_zero]

/-- arXiv 2402.16746, Theorem 2, for **zero boundary values**, which the paper's Lemma 2 also
covers. The physical cells are the `i ≠ 0` of `ZMod Nx`, so there are `Nx - 1` of them, and the
physical interfaces run from `0` (left of cell `1`) to `-1` (right of cell `Nx - 1`). The cell `0`
is a ghost cell carrying zeros, `g` vanishes at the two boundary interfaces, and the scheme (3.3)
holds at the physical cells and at the interior interfaces only. -/
theorem theorem_2_zero_boundary {σ₀ ε : ℝ} (hP : P.Admissible σ₀) {w : Fin (N + 1) → ℝ}
    (hGL : IsGaussLegendre P.μ w) (hTm : P.Tm = gaussT P.μ w) (hε : 0 ≤ ε)
    (hCFL : ∀ k, P.μ k ≠ 0 → P.Δt ≤ 1 / (5 * P.c * betaN w) *
      (2 * ε * P.Δx / |P.μ k| + σ₀ * P.Δx ^ 2 / P.μ k ^ 2))
    {T h T' h' : ZMod Nx → ℝ} {g g' : Matrix (ZMod Nx) (Fin N) ℝ}
    (hT : T 0 = 0) (hh : h 0 = 0) (hT' : T' 0 = 0) (hh' : h' 0 = 0)
    (hgl : ∀ k, g' 0 k = 0) (hgr : ∀ k, g' (-1) k = 0)
    (hmacro : ∀ i, i ≠ 0 → ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * h' i +
      γ₁ / 2 * Dm P.Δx (fun j => g' j 0) i = -P.σc i * h' i)
    (hmicro : ∀ j, j ≠ 0 → j ≠ -1 → ∀ k, ε ^ 2 / P.c * ((g' j k - g j k) / P.Δt) +
      ε * P.flux g j k + bvec N k * P.source ε 1 T h j = -P.σf j * g' j k)
    (htemp : ∀ i, i ≠ 0 → (T' i - T i) / P.Δt = P.κ * P.σc i * h' i) :
    P.energy ε T' h' g' ≤ P.energy ε T h g := by
  have hF := isFluxFactorization_gauss hGL
  rw [← hTm] at hF
  refine P.energy_le_of_tested hP hF
    (fun k hk => cfl_of_cfl hP.c_pos hε hP.Δx_pos hP.σ₀_pos hGL.two_le_betaN (hCFL k hk))
    (fun i => ?_) ?_ (fun i => ?_)
  · by_cases hi : i = 0
    · subst hi
      simp [hh, hh', Dm, hgl, hgr]
    · exact hmacro i hi
  · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hj0 : j = 0
    · subst hj0
      rw [hgl k, zero_mul]
    by_cases hj1 : j = -1
    · subst hj1
      rw [hgr k, zero_mul]
    have hres : P.microRes ε 1 T h g g' j k = 0 := by
      simp only [microRes, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        Matrix.vecMulVec_apply, Matrix.diagonal_mul]
      linear_combination hmicro j hj0 hj1 k
    rw [hres, mul_zero]
  · by_cases hi : i = 0
    · subst hi
      simp [hT, hT', hh']
    · exact htemp i hi

end Params

end LowRank

/-- `∑ (f (i+1) - f i) = f n - f 0`, for interface values `f` of `n` cells. -/
lemma sum_fin_succ_sub {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc, Fin.succ_last] at this ⊢
    rw [this]
    simp

/-- arXiv 2402.16746, Theorem 5, for general boundary values, on `Nc` cells with `Nc + 1` interface
values `g₁`: the proof's "`∑ c γ₁/2 D⁰ g₁ = 0` for zero or periodic boundary conditions" is
exactly `g₁ 0 = g₁ (last)`. Then the total mass `∑ (Φ_i / c + cν/2 T_i)` is conserved, with
`Φ = a c T + ε² h`. -/
theorem mass_conservation_of_boundary_flux {Nc : ℕ} {a c cν ε Δt Δx : ℝ} (hc : c ≠ 0)
    (hcν : cν ≠ 0) (hΔt : Δt ≠ 0) {σ T h T' h' : Fin Nc → ℝ} {g₁ : Fin (Nc + 1) → ℝ}
    (hb : g₁ 0 = g₁ (Fin.last Nc))
    (hmacro : ∀ i, ε ^ 2 / c * ((h' i - h i) / Δt) + a * (2 / cν) * σ i * h' i +
      γ₁ / 2 * ((g₁ i.succ - g₁ i.castSucc) / Δx) = -σ i * h' i)
    (htemp : ∀ i, (T' i - T i) / Δt = 2 / cν * σ i * h' i) :
    ∑ i, ((a * c * T' i + ε ^ 2 * h' i) / c + cν / 2 * T' i) =
      ∑ i, ((a * c * T i + ε ^ 2 * h i) / c + cν / 2 * T i) := by
  have hD : ∑ i : Fin Nc, (g₁ i.succ - g₁ i.castSucc) / Δx = 0 := by
    rw [← Finset.sum_div, sum_fin_succ_sub, ← hb, sub_self, zero_div]
  have hi (i : Fin Nc) : ((a * c * T' i + ε ^ 2 * h' i) / c + cν / 2 * T' i) =
      ((a * c * T i + ε ^ 2 * h i) / c + cν / 2 * T i) -
        Δt * (γ₁ / 2) * ((g₁ i.succ - g₁ i.castSucc) / Δx) := by
    have hT : T' i - T i = Δt * (2 / cν * σ i * h' i) := by
      rw [← htemp i]
      field_simp
    have hh : ε ^ 2 / c * (h' i - h i) + Δt * (a * (2 / cν) * σ i * h' i) +
        Δt * (γ₁ / 2 * ((g₁ i.succ - g₁ i.castSucc) / Δx)) = -Δt * σ i * h' i := by
      have e : Δt * (ε ^ 2 / c * ((h' i - h i) / Δt)) = ε ^ 2 / c * (h' i - h i) := by
        field_simp
      linear_combination Δt * hmacro i - e
    have hκ : cν / 2 * (2 / cν) = 1 := by field_simp
    have e1 : (a * c * T' i + ε ^ 2 * h' i) / c = a * T' i + ε ^ 2 / c * h' i := by field_simp
    have e2 : (a * c * T i + ε ^ 2 * h i) / c = a * T i + ε ^ 2 / c * h i := by field_simp
    rw [e1, e2]
    linear_combination (a + cν / 2) * hT + hh + Δt * σ i * h' i * hκ
  simp only [hi, Finset.sum_sub_distrib, ← Finset.mul_sum, hD]
  ring

/-! ### The spectral instance, and the false Lemmas 4 and 6 -/

section Instances

open Polynomial LeanDLRA.Literature.P1906_09940

/-- For every `N` the hypotheses of `theorem_2_sharp` can hold: any orthogonal diagonalization of
the full flux matrix `A_f = (⟨μ P_i P_j⟩_μ)_{0 ≤ i, j ≤ N}` is a flux factorization, and it
reproduces the flux matrix `A`. -/
theorem exists_isFluxFactorization (N : ℕ) [NeZero N] :
    ∃ (μ : Fin (N + 1) → ℝ) (Tm : Matrix (Fin N) (Fin (N + 1)) ℝ) (t₀ : Fin (N + 1) → ℝ),
      IsFluxFactorization μ Tm t₀ ∧
        Tm * diagonal μ * Tmᵀ = (muMatrix (N + 1)).submatrix Fin.succ Fin.succ := by
  have hA : (muMatrix (N + 1)).IsHermitian := muMatrix_isHermitian (N + 1)
  set Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    (hA.eigenvectorUnitary : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) with hQ
  have hQQ : Q * Qᵀ = 1 := by
    have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hspec : muMatrix (N + 1) = Q * diagonal hA.eigenvalues * Qᵀ := by
    have := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  refine ⟨hA.eigenvalues, Q.submatrix Fin.succ id, Q 0, ⟨?_, ?_, fun i => ?_⟩, ?_⟩
  · have : Q.submatrix Fin.succ id * (Q.submatrix Fin.succ id)ᵀ =
        (Q * Qᵀ).submatrix Fin.succ Fin.succ := by
      ext a b
      simp [Matrix.mul_apply]
    rw [this, hQQ, Matrix.submatrix_one _ (Fin.succ_injective N)]
  · have := congrFun (congrFun hQQ 0) 0
    simpa [Matrix.mul_apply, sq] using this
  · have h1 := congrFun (congrFun hspec i.succ) 0
    rw [muMatrix_apply] at h1
    have h2 : (Q * diagonal hA.eigenvalues * Qᵀ) i.succ 0 =
        ∑ k, Q i.succ k * hA.eigenvalues k * Q 0 k := by
      rw [Matrix.mul_apply]
      simp [Matrix.mul_diagonal]
    rw [h2] at h1
    simp only [Matrix.submatrix_apply, id]
    rw [← h1]
    simp only [Fin.val_succ, Fin.val_zero]
    by_cases hi : i = 0
    · subst hi
      simp [muOff]
    · have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext (by simpa using e))
      simp [hi, this]
  · ext a b
    have h1 := congrFun (congrFun hspec a.succ) b.succ
    simp only [Matrix.submatrix_apply]
    rw [h1]
    simp [Matrix.mul_apply]

/-- The nodes `∓1/√3` of the two-point Gauss-Legendre rule, `N = 1`. -/
noncomputable def gl₁μ : Fin 2 → ℝ := ![-(1 / √3), 1 / √3]

/-- The weights of the two-point Gauss-Legendre rule. -/
noncomputable def gl₁w : Fin 2 → ℝ := ![1, 1]

/-- The two-point rule is the Gauss-Legendre rule for `N = 1`. -/
theorem isGaussLegendre_two_point : IsGaussLegendre (N := 1) gl₁μ gl₁w := by
  intro p hp
  have hd : p.natDegree < 4 := by omega
  have ev (x : ℝ) : p.eval x =
      p.coeff 0 + p.coeff 1 * x + p.coeff 2 * x ^ 2 + p.coeff 3 * x ^ 3 := by
    rw [eval_eq_sum_range' hd]
    simp [Finset.sum_range_succ]
  have hs2 : (1 / √3 : ℝ) ^ 2 = 1 / 3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hint : ∫ t in (-1 : ℝ)..1, p.eval t = 2 * p.coeff 0 + 2 / 3 * p.coeff 2 := by
    have hF : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt
        (fun t => p.coeff 0 * t + p.coeff 1 * t ^ 2 / 2 + p.coeff 2 * t ^ 3 / 3 +
          p.coeff 3 * t ^ 4 / 4) (p.eval t) t := by
      intro t _
      rw [ev]
      have h0 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by simpa using hasDerivAt_pow 3 t
      have h4 : HasDerivAt (fun t : ℝ => t ^ 4) (4 * t ^ 3) t := by simpa using hasDerivAt_pow 4 t
      have := (((h0.const_mul (p.coeff 0)).add ((h2.const_mul (p.coeff 1)).div_const 2)).add
        ((h3.const_mul (p.coeff 2)).div_const 3)).add ((h4.const_mul (p.coeff 3)).div_const 4)
      exact this.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (p.continuous.intervalIntegrable _ _)]
    norm_num
    ring
  rw [hint, Fin.sum_univ_two]
  simp only [gl₁μ, gl₁w, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, ev]
  linear_combination (2 * p.coeff 2) * hs2

lemma gl₁w_eq (k : Fin 2) : gl₁w k = 1 := by
  fin_cases k <;> simp [gl₁w]

lemma gaussT_gl₁ (k : Fin 2) : gaussT gl₁μ gl₁w 0 k = √(3 / 2) * gl₁μ k := by
  have e : (2 * ((1 : ℕ) : ℝ) + 1) / 2 = 3 / 2 := by norm_num
  simp only [gaussT, Matrix.of_apply, gl₁w_eq, Real.sqrt_one, one_mul, nLeg, Fin.val_zero, zero_add,
    legendre_one, eval_X, e]

lemma gl₁_sq (k : Fin 2) : gl₁μ k ^ 2 = 1 / 3 := by
  have hs2 : (1 / √3 : ℝ) ^ 2 = 1 / 3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  fin_cases k
  · simp only [gl₁μ, Fin.zero_eta, Matrix.cons_val_zero, neg_sq]
    exact hs2
  · simp only [gl₁μ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact hs2

/-- `A = 0` for `P₁`: the flux matrix of the moment `g₁` alone vanishes. -/
lemma flux_gl₁ : gaussT gl₁μ gl₁w * diagonal gl₁μ * (gaussT gl₁μ gl₁w)ᵀ = 0 := by
  rw [gaussT_flux isGaussLegendre_two_point]
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp [muMatrix_apply]

/-- **The first identity of arXiv 2402.16746, Lemma 4 is false**: `gᵀ A² g = v̂ᵀ M² v̂` fails for
the two-point Gauss-Legendre rule, where `A = 0` and `v̂ = Tᵀ g` (`v̂ = T_fᵀ (0, g)`), at `g = 1`.
The term missing on the left is the square of the first moment, which `first_moment_le`
controls. -/
theorem lemma_4_false :
    ∃ (μ w : Fin 2 → ℝ) (g : Fin 1 → ℝ), IsGaussLegendre (N := 1) μ w ∧
      g ⬝ᵥ ((gaussT μ w * diagonal μ * (gaussT μ w)ᵀ) *
          (gaussT μ w * diagonal μ * (gaussT μ w)ᵀ)) *ᵥ g ≠
        (g ᵥ* gaussT μ w) ⬝ᵥ (diagonal fun k => μ k ^ 2) *ᵥ (g ᵥ* gaussT μ w) := by
  refine ⟨gl₁μ, gl₁w, fun _ => 1, isGaussLegendre_two_point, ?_⟩
  rw [flux_gl₁]
  have hv (k : Fin 2) : ((fun _ => 1 : Fin 1 → ℝ) ᵥ* gaussT gl₁μ gl₁w) k =
      √(3 / 2) * gl₁μ k := by
    simp [Matrix.vecMul, dotProduct, gaussT_gl₁]
  have hτ : √(3 / 2 : ℝ) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hr : ((fun _ => 1 : Fin 1 → ℝ) ᵥ* gaussT gl₁μ gl₁w) ⬝ᵥ
      (diagonal fun k => gl₁μ k ^ 2) *ᵥ ((fun _ => 1 : Fin 1 → ℝ) ᵥ* gaussT gl₁μ gl₁w) =
        1 / 3 := by
    simp only [dotProduct, Matrix.mulVec_diagonal, hv, gl₁_sq]
    rw [Fin.sum_univ_two]
    have h0 := gl₁_sq 0
    have h1 := gl₁_sq 1
    linear_combination (1 / 3 * (gl₁μ 0 ^ 2 + gl₁μ 1 ^ 2)) * hτ + 1 / 2 * h0 + 1 / 2 * h1
  rw [hr]
  simp

/-- The parameters of the counterexample to Lemma 6: three cells and `P₁`. -/
noncomputable def cx : Params 3 1 where
  a := 1
  c := 1
  cν := 1
  Δt := 1
  Δx := 1
  σc := fun _ => 1
  σf := fun _ => 1
  μ := gl₁μ
  Tm := gaussT gl₁μ gl₁w

lemma cx_Apl_Ami : cx.Apl 0 0 = 1 / (2 * √3) ∧ cx.Ami 0 0 = -(1 / (2 * √3)) := by
  have hs : (0 : ℝ) < 1 / √3 := by positivity
  have habs : |(1 / √3 : ℝ)| = 1 / √3 := abs_of_pos hs
  have hτ : √(3 / 2 : ℝ) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hp0 : upos (gl₁μ 0) = 0 := by
    simp only [upos, gl₁μ, Matrix.cons_val_zero, abs_neg, habs]
    ring
  have hp1 : upos (gl₁μ 1) = 1 / √3 := by
    simp only [upos, gl₁μ, Matrix.cons_val_one, Matrix.cons_val_zero, habs]
    ring
  have hm0 : uneg (gl₁μ 0) = -(1 / √3) := by
    simp only [uneg, gl₁μ, Matrix.cons_val_zero, abs_neg, habs]
    ring
  have hm1 : uneg (gl₁μ 1) = 0 := by
    simp only [uneg, gl₁μ, Matrix.cons_val_one, Matrix.cons_val_zero, habs]
    ring
  have hsq0 := gl₁_sq 0
  have hsq1 := gl₁_sq 1
  have e (d : Fin 2 → ℝ) : (gaussT gl₁μ gl₁w * diagonal d * (gaussT gl₁μ gl₁w)ᵀ) 0 0 =
      (d 0 + d 1) / 2 := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, gaussT_gl₁, Fin.sum_univ_two]
    linear_combination (gl₁μ 0 ^ 2 * d 0 + gl₁μ 1 ^ 2 * d 1) * hτ + 3 / 2 * d 0 * hsq0 +
      3 / 2 * d 1 * hsq1
  constructor
  · change (gaussT gl₁μ gl₁w * diagonal (fun k => upos (gl₁μ k)) *
      (gaussT gl₁μ gl₁w)ᵀ) 0 0 = _
    rw [e, hp0, hp1]
    ring
  · change (gaussT gl₁μ gl₁w * diagonal (fun k => uneg (gl₁μ k)) *
      (gaussT gl₁μ gl₁w)ᵀ) 0 0 = _
    rw [e, hm0, hm1]
    ring

/-- **arXiv 2402.16746, Lemma 6 is false**: `∑ |(A⁺D⁺ + A⁻D⁻) g|² ≤ 2 β_N ∑ (D⁺g)ᵀ A² D⁺g` fails for
`P₁` with the two-point rule on three cells. There `A = 0`, so the right side vanishes, while
`A^± = ±|A|/2 ≠ 0`. What is true and suffices is the mode-wise bound inside `mode_bound`, with the
full matrix, and `first_moment_le`. -/
theorem lemma_6_false :
    ∃ (P : Params 3 1) (w : Fin 2 → ℝ) (g : Matrix (ZMod 3) (Fin 1) ℝ),
      IsGaussLegendre P.μ w ∧ P.Tm = gaussT P.μ w ∧ 0 < P.Δx ∧
      2 * betaN w * ∑ j, DpM P.Δx g j ⬝ᵥ
          ((P.Tm * diagonal P.μ * P.Tmᵀ) * (P.Tm * diagonal P.μ * P.Tmᵀ)) *ᵥ DpM P.Δx g j <
        ∑ j, ∑ k, ((DpM P.Δx g * P.Apl + DmM P.Δx g * P.Ami) j k) ^ 2 := by
  set g : Matrix (ZMod 3) (Fin 1) ℝ := Matrix.of fun j _ => if j = 0 then 1 else 0 with hg
  refine ⟨cx, gl₁w, g, isGaussLegendre_two_point, rfl, by norm_num [cx], ?_⟩
  have hA : cx.Tm * diagonal cx.μ * cx.Tmᵀ = 0 := flux_gl₁
  rw [hA]
  simp only [Matrix.zero_mulVec, dotProduct_zero, Finset.sum_const_zero, mul_zero]
  have hle : ((DpM cx.Δx g * cx.Apl + DmM cx.Δx g * cx.Ami) 0 0) ^ 2 ≤
      ∑ j, ∑ k, ((DpM cx.Δx g * cx.Apl + DmM cx.Δx g * cx.Ami) j k) ^ 2 := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun j : ZMod 3 => ∑ k,
      ((DpM cx.Δx g * cx.Apl + DmM cx.Δx g * cx.Ami) j k) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ (0 : ZMod 3)))
    simp
  refine lt_of_lt_of_le ?_ hle
  have hΔ : cx.Δx = 1 := rfl
  have hp : DpM cx.Δx g 0 0 = -1 := by
    simp [DpM, Dp, hg, hΔ]
  have hm : DmM cx.Δx g 0 0 = 1 := by
    simp [DmM, Dm, hg, hΔ]
  obtain ⟨hAp, hAm⟩ := cx_Apl_Ami
  have hval : (DpM cx.Δx g * cx.Apl + DmM cx.Δx g * cx.Ami) 0 0 = -(1 / √3) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_one, hp, hm, hAp, hAm]
    ring
  rw [hval, neg_sq]
  positivity

end Instances

/-! ### The steps exist -/

section Existence

variable {Nx N : ℕ} [NeZero Nx] [NeZero N] (P : Params Nx N)

/-- `c (K' - Y) = W - Z K'` from the solved form `(c + Z) K' = c Y + W`. -/
lemma implicit_left {ι κ : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} {Z : Matrix ι ι ℝ}
    {K Y W : Matrix ι κ ℝ} (h : (c • (1 : Matrix ι ι ℝ) + Z) * K = c • Y + W) :
    c • (K - Y) = W - Z * K := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]

/-- `c (L' - Y) = W - L' Z` from the solved form `L' (c + Z) = c Y + W`. -/
lemma implicit_right {ι κ : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} {Z : Matrix ι ι ℝ}
    {L Y W : Matrix κ ι ℝ} (h : L * (c • (1 : Matrix ι ι ℝ) + Z) = c • Y + W) :
    c • (L - Y) = W - L * Z := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]

lemma exists_implicit_left {Nx : ℕ} [NeZero Nx] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {σ : ZMod Nx → ℝ} (hσ : ∀ j, 0 < σ j) {c : ℝ} (hc : 0 ≤ c) {X : Matrix (ZMod Nx) ι ℝ}
    (hX : Xᵀ * X = 1) (Y W : Matrix ι κ ℝ) [Fintype κ] :
    ∃ K : Matrix ι κ ℝ, c • (K - Y) = W - (Xᵀ * diagonal σ * X) * K := by
  have hu := isUnit_det_shifted hσ hc hX
  refine ⟨(c • (1 : Matrix ι ι ℝ) + Xᵀ * diagonal σ * X)⁻¹ * (c • Y + W), implicit_left ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

lemma exists_implicit_right {Nx : ℕ} [NeZero Nx] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {σ : ZMod Nx → ℝ} (hσ : ∀ j, 0 < σ j) {c : ℝ} (hc : 0 ≤ c)
    {X : Matrix (ZMod Nx) ι ℝ} (hX : Xᵀ * X = 1) (Y W : Matrix κ ι ℝ) :
    ∃ L : Matrix κ ι ℝ, c • (L - Y) = W - L * (Xᵀ * diagonal σ * X) := by
  have hu := isUnit_det_shifted hσ hc hX
  refine ⟨(c • Y + W) * (c • (1 : Matrix ι ι ℝ) + Xᵀ * diagonal σ * X)⁻¹, implicit_right ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

/-- `K` with the diagonal implicit term of (4.2): the case `X = 1` above. -/
lemma exists_implicit_diagonal {Nx : ℕ} [NeZero Nx] {κ : Type*} [Fintype κ]
    {σ : ZMod Nx → ℝ} (hσ : ∀ j, 0 < σ j) {c : ℝ} (hc : 0 ≤ c) (Y W : Matrix (ZMod Nx) κ ℝ) :
    ∃ K : Matrix (ZMod Nx) κ ℝ, c • (K - Y) = W - diagonal σ * K := by
  obtain ⟨K, hK⟩ := exists_implicit_left (X := (1 : Matrix (ZMod Nx) (ZMod Nx) ℝ)) hσ hc
    (by simp) Y W
  exact ⟨K, by simpa using hK⟩

namespace Params

omit [NeZero Nx] [NeZero N] in
/-- The macro update (3.1a), (3.1c) can be solved for all `ε` when `Ψ ≥ 0`. -/
lemma exists_macro {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ : ZMod Nx → ℝ} (hΨ : ∀ i, 0 ≤ Ψ i) (ε : ℝ)
    (T h g₁ : ZMod Nx → ℝ) :
    ∃ T' h' : ZMod Nx → ℝ,
      (∀ i, ε ^ 2 / P.c * ((h' i - h i) / P.Δt) + P.a * P.κ * P.σc i * Ψ i * h' i +
        γ₁ / 2 * Dm P.Δx g₁ i = -P.σc i * h' i) ∧
      ∀ i, (T' i - T i) / P.Δt = P.κ * P.σc i * h' i := by
  have hc := hP.c_pos
  have hΔt := hP.Δt_pos
  have ha := hP.a_pos
  have hcν := hP.cν_pos
  have hκ : 0 < P.κ := by
    simp only [κ]
    positivity
  have hd (i : ZMod Nx) : 0 < ε ^ 2 / (P.c * P.Δt) + P.a * P.κ * P.σc i * Ψ i + P.σc i := by
    have h1 := hP.σ₀_pos.trans_le (hP.σc_ge i)
    have h2 := hΨ i
    positivity
  refine ⟨fun i => T i + P.Δt * (P.κ * P.σc i *
      ((ε ^ 2 / (P.c * P.Δt) * h i - γ₁ / 2 * Dm P.Δx g₁ i) /
        (ε ^ 2 / (P.c * P.Δt) + P.a * P.κ * P.σc i * Ψ i + P.σc i))),
    fun i => (ε ^ 2 / (P.c * P.Δt) * h i - γ₁ / 2 * Dm P.Δx g₁ i) /
        (ε ^ 2 / (P.c * P.Δt) + P.a * P.κ * P.σc i * Ψ i + P.σc i), fun i => ?_, fun i => ?_⟩
  · have hh : (ε ^ 2 / (P.c * P.Δt) + P.a * P.κ * P.σc i * Ψ i + P.σc i) *
        ((ε ^ 2 / (P.c * P.Δt) * h i - γ₁ / 2 * Dm P.Δx g₁ i) /
          (ε ^ 2 / (P.c * P.Δt) + P.a * P.κ * P.σc i * Ψ i + P.σc i)) =
        ε ^ 2 / (P.c * P.Δt) * h i - γ₁ / 2 * Dm P.Δx g₁ i := by
      rw [mul_comm, div_mul_cancel₀ _ (hd i).ne']
    simp only
    linear_combination hh
  · simp only
    field_simp
    ring

omit [NeZero Nx] in
/-- The full scheme (3.1) has a solution for all data, `Ψ ≥ 0`. -/
theorem exists_isFullStep {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ : ZMod Nx → ℝ} (hΨ : ∀ i, 0 ≤ Ψ i)
    (ε : ℝ) (T h : ZMod Nx → ℝ) (g : Matrix (ZMod Nx) (Fin N) ℝ) :
    ∃ (T' h' : ZMod Nx → ℝ) (g' : Matrix (ZMod Nx) (Fin N) ℝ),
      P.IsFullStep ε Ψ T h g T' h' g' := by
  have hc := hP.c_pos
  have hΔt := hP.Δt_pos
  have hd (j : ZMod Nx) : 0 < ε ^ 2 / (P.c * P.Δt) + P.σf j := by
    have h1 := hP.σ₀_pos.trans_le (hP.σf_ge j)
    positivity
  set g' : Matrix (ZMod Nx) (Fin N) ℝ := Matrix.of fun j k =>
    (ε ^ 2 / (P.c * P.Δt) * g j k - ε * P.flux g j k - bvec N k * P.source ε Ψ T h j) /
      (ε ^ 2 / (P.c * P.Δt) + P.σf j) with hg'
  obtain ⟨T', h', hm, ht⟩ := P.exists_macro hP hΨ ε T h (fun j => g' j 0)
  refine ⟨T', h', g', hm, fun j k => ?_, ht⟩
  have hh : (ε ^ 2 / (P.c * P.Δt) + P.σf j) * g' j k =
      ε ^ 2 / (P.c * P.Δt) * g j k - ε * P.flux g j k - bvec N k * P.source ε Ψ T h j := by
    simp only [hg', Matrix.of_apply]
    rw [mul_comm, div_mul_cancel₀ _ (hd j).ne']
  linear_combination hh

/-- The fixed-rank integrator (4.2)-(4.6) has a step for all data with `Xⁿ` orthonormal and
`r ≤ Nx`, `r ≤ N`. -/
theorem exists_isFixedRankStep {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ : ZMod Nx → ℝ}
    (hΨ : ∀ i, 0 ≤ Ψ i) {r : ℕ} (hrx : r ≤ Nx) (hrN : r ≤ N) (ε : ℝ) (T h : ZMod Nx → ℝ)
    (X : Matrix (ZMod Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin N) (Fin r) ℝ)
    (hX : Xᵀ * X = 1) :
    ∃ (K' X' : Matrix (ZMod Nx) (Fin r) ℝ) (L' V' : Matrix (Fin N) (Fin r) ℝ)
      (SK SL S' : Matrix (Fin r) (Fin r) ℝ) (T' h' : ZMod Nx → ℝ),
      P.IsFixedRankStep ε Ψ T h X S V K' L' X' SK V' SL S' T' h' := by
  have hσ (j : ZMod Nx) : 0 < P.σf j := hP.σ₀_pos.trans_le (hP.σf_ge j)
  have hc : 0 ≤ ε ^ 2 / (P.c * P.Δt) := by
    have := hP.c_pos
    have := hP.Δt_pos
    positivity
  obtain ⟨K', hK⟩ := exists_implicit_diagonal hσ hc (X * S)
    (-(ε • (DmM P.Δx (X * S) * (Vᵀ * P.Apl * V) + DpM P.Δx (X * S) * (Vᵀ * P.Ami * V))) -
      vecMulVec (P.source ε Ψ T h) (bvec N ᵥ* V))
  obtain ⟨L', hL⟩ := exists_implicit_right hσ hc hX (V * Sᵀ)
    (-(ε • (P.Apl * (V * Sᵀ) * ((DmM P.Δx X)ᵀ * X) + P.Ami * (V * Sᵀ) * ((DpM P.Δx X)ᵀ * X))) -
      vecMulVec (bvec N) (Xᵀ *ᵥ P.source ε Ψ T h))
  obtain ⟨X', hX', hcapX⟩ := exists_orthonormal_capture_of_le_card K' (by simpa using hrx)
  obtain ⟨V', hV', hcapV⟩ := exists_orthonormal_capture_of_le_card L' (by simpa using hrN)
  set St := (X'ᵀ * X) * S * (Vᵀ * V') with hSt
  obtain ⟨S', hS'⟩ := exists_implicit_left hσ hc hX' St
    (-(ε • (X'ᵀ * DmM P.Δx X' * St * (V'ᵀ * P.Apl * V') +
        X'ᵀ * DpM P.Δx X' * St * (V'ᵀ * P.Ami * V'))) -
      vecMulVec (X'ᵀ *ᵥ P.source ε Ψ T h) (bvec N ᵥ* V'))
  obtain ⟨T', h', hm, ht⟩ := P.exists_macro hP hΨ ε T h (fun j => (X' * S' * V'ᵀ) j 0)
  refine ⟨K', X', L', V', X'ᵀ * K', (V'ᵀ * L')ᵀ, S', T', h', hK, hX', ?_, hL, hV', ?_, hS', hm, ht⟩
  · rw [← Matrix.mul_assoc, hcapX]
  · rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, hcapV]

end Params

/-- A column is captured by a single unit vector, if there is a row. -/
lemma exists_unit_capture {m : Type*} [Fintype m] (hm : 1 ≤ Fintype.card m) (K : Matrix m Unit ℝ) :
    ∃ Q : Matrix m Unit ℝ, Qᵀ * Q = 1 ∧ K = Q * (Qᵀ * K) := by
  obtain ⟨U, hU, hcap⟩ := exists_orthonormal_capture K (r := 1)
    (by simpa using K.rank_le_card_width) hm
  set Q : Matrix m Unit ℝ := U.submatrix id fun _ => 0 with hQ
  refine ⟨Q, ?_, ?_⟩
  · ext a b
    have := congrFun (congrFun hU 0) 0
    simpa [hQ, Matrix.mul_apply, Matrix.one_apply] using this
  · have e : Q * (Qᵀ * K) = U * Uᵀ * K := by
      ext i u
      simp [hQ, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rw [e, hcap]

lemma e₁col_orth : (e₁col N)ᵀ * e₁col N = 1 := by
  have e (k : Fin N) : bvec N k / γ₁ = if k = 0 then 1 else 0 := by
    have := γ₁_pos.ne'
    by_cases hk : k = 0 <;> simp [bvec, hk, this]
  ext a b
  simp [e₁col, Matrix.mul_apply, e]

namespace Params

/-- The integrator of arXiv 2402.16746, Section 4.2 has a step for all data with `Xⁿ` orthonormal
and `Ψ ≥ 0`. The bases here keep every singular triple. -/
theorem exists_isAdaptiveStep {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ : ZMod Nx → ℝ}
    (hΨ : ∀ i, 0 ≤ Ψ i) {r : ℕ} (ε : ℝ) (T h : ZMod Nx → ℝ)
    (X : Matrix (ZMod Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin N) (Fin r) ℝ)
    (hX : Xᵀ * X = 1) :
    ∃ (m n₁ n₂ t n₃ : ℕ) (K' : Matrix (ZMod Nx) (Fin r) ℝ) (L' : Matrix (Fin N) (Fin r) ℝ)
      (Xh : Matrix (ZMod Nx) (Fin m) ℝ) (Vrem : Matrix (Fin N) (Fin n₁) ℝ)
      (Sh : Matrix (Fin m) (Unit ⊕ Fin n₁) ℝ) (Xr : Matrix (ZMod Nx) (Fin n₂) ℝ)
      (Sr : Matrix (Fin n₂) (Fin n₁) ℝ) (U : Matrix (Fin n₂) (Fin t) ℝ)
      (W : Matrix (Fin n₁) (Fin t) ℝ) (s : Fin t → ℝ) (f : Fin t ↪ Fin t)
      (Xa : Matrix (ZMod Nx) Unit ℝ) (Sa : Matrix Unit Unit ℝ) (X' : Matrix (ZMod Nx) (Fin n₃) ℝ)
      (R₂ : Matrix (Fin n₃) (Unit ⊕ Fin t) ℝ) (T' h' : ZMod Nx → ℝ),
      P.IsAdaptiveStep ε Ψ T h X S V K' L' Xh Vrem Sh Xr Sr U W s f Xa Sa X' R₂ T' h' := by
  have hσ (j : ZMod Nx) : 0 < P.σf j := hP.σ₀_pos.trans_le (hP.σf_ge j)
  have hc : 0 ≤ ε ^ 2 / (P.c * P.Δt) := by
    have := hP.c_pos
    have := hP.Δt_pos
    positivity
  obtain ⟨K', hK⟩ := exists_implicit_diagonal hσ hc (X * S)
    (-(ε • (DmM P.Δx (X * S) * (Vᵀ * P.Apl * V) + DpM P.Δx (X * S) * (Vᵀ * P.Ami * V))) -
      vecMulVec (P.source ε Ψ T h) (bvec N ᵥ* V))
  obtain ⟨L', hL⟩ := exists_implicit_right hσ hc hX (V * Sᵀ)
    (-(ε • (P.Apl * (V * Sᵀ) * ((DmM P.Δx X)ᵀ * X) + P.Ami * (V * Sᵀ) * ((DpM P.Δx X)ᵀ * X))) -
      vecMulVec (bvec N) (Xᵀ *ᵥ P.source ε Ψ T h))
  -- the augmented spatial basis
  set K0 := fromCols (replicateCol Unit (P.limitFlux Ψ T)) (fromCols K' X) with hK0
  obtain ⟨Xh, hXh, hcap⟩ := exists_orthonormal_capture K0 le_rfl K0.rank_le_card_height
  have hcap' : Xh * Xhᵀ * fromCols (replicateCol Unit (P.limitFlux Ψ T)) (fromCols K' X) =
      fromCols (replicateCol Unit (P.limitFlux Ψ T)) (fromCols K' X) := hcap
  rw [Matrix.mul_fromCols, Matrix.mul_fromCols] at hcap'
  obtain ⟨hcw, hcr⟩ := Matrix.fromCols_inj.eq_iff.mp hcap'
  obtain ⟨hcK, hcX⟩ := Matrix.fromCols_inj.eq_iff.mp hcr
  have hwr : P.limitFlux Ψ T ∈ Set.range Xh.mulVec := by
    refine ⟨Xhᵀ *ᵥ P.limitFlux Ψ T, ?_⟩
    rw [Matrix.mulVec_mulVec]
    ext j
    have := congrFun (congrFun hcw j) ()
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  -- the augmented angular basis
  have he := e₁col_orth (N := N)
  set K1 := fromCols L' V with hK1
  have hzero : (e₁col N)ᵀ * ((1 - e₁col N * (e₁col N)ᵀ) * K1) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, he,
      Matrix.one_mul, sub_self, Matrix.zero_mul]
  have hrk := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  rw [Matrix.rank_transpose, rank_eq_card_of_transpose_mul_eq_one he] at hrk
  obtain ⟨Vr, hVr, hVre, hcapV⟩ := exists_orthonormal_capture_compl (e₁col N) he K1 le_rfl hrk
  obtain ⟨hVh, hcapK, -⟩ := fromCols_orthonormal_capture he hVr hVre hcapV
  have hcapK' : fromCols (e₁col N) Vr * (fromCols (e₁col N) Vr)ᵀ * fromCols L' V =
      fromCols L' V := hcapK
  rw [Matrix.mul_fromCols] at hcapK'
  obtain ⟨hcL, hcV⟩ := Matrix.fromCols_inj.eq_iff.mp hcapK'
  -- the Galerkin step
  set Vh := fromCols (e₁col N) Vr with hVhdef
  set St := (Xhᵀ * X) * S * (Vᵀ * Vh) with hSt
  obtain ⟨Sh, hSh⟩ := exists_implicit_left hσ hc hXh St
    (-(ε • (Xhᵀ * DmM P.Δx Xh * St * (Vhᵀ * P.Apl * Vh) +
        Xhᵀ * DpM P.Δx Xh * St * (Vhᵀ * P.Ami * Vh))) -
      vecMulVec (Xhᵀ *ᵥ P.source ε Ψ T h) (bvec N ᵥ* Vh))
  -- the truncation
  set Krem := (Xh * Sh).submatrix id Sum.inr with hKrem
  obtain ⟨Xr, hXr, hcrem⟩ := exists_orthonormal_capture Krem le_rfl Krem.rank_le_card_height
  obtain ⟨U, W, s, hU, hW, -, -, -, hsvd⟩ := LeanDLRA.SVD.exists_svd (Xrᵀ * Krem) rfl
  set Kap := (Xh * Sh).submatrix id Sum.inl with hKap
  have hcard : 1 ≤ Fintype.card (ZMod Nx) := Fintype.card_pos
  obtain ⟨Xa, hXa, hKa⟩ := exists_unit_capture hcard Kap
  set K2 := fromCols Xa (Xr * U.submatrix id (Function.Embedding.refl _)) with hK2
  obtain ⟨X', hX', hc2⟩ := exists_orthonormal_capture K2 le_rfl K2.rank_le_card_height
  obtain ⟨T', h', hm, ht⟩ := P.exists_macro hP hΨ ε T h
    (fun j => (X' * adaptS (X'ᵀ * K2) (Xaᵀ * Kap) s (Function.Embedding.refl _) *
      (adaptV Vr W (Function.Embedding.refl _))ᵀ) j 0)
  refine ⟨_, _, _, _, _, K', L', Xh, Vr, Sh, Xr, Xrᵀ * Krem, U, W, s, Function.Embedding.refl _,
    Xa, Xaᵀ * Kap, X', X'ᵀ * K2, T', h', hK, hL, hXh, hwr, hcK, hcX, hVh, hcL, hcV, hSh, ?_, hXr,
    hsvd, hU, hW, hKa, hXa, hX', ?_, hm, ht⟩
  · rw [← Matrix.mul_assoc, hcrem]
  · rw [← Matrix.mul_assoc, hc2]

end Params

end Existence

/-! ### The genuine limit `ε ↓ 0` of the low-rank integrators -/

section Limit

variable {Nx N : ℕ} [NeZero Nx] [NeZero N] (P : Params Nx N)

omit [NeZero N] in
lemma norm_DpM_le {ι : Type*} [Fintype ι] {Δx : ℝ} (hΔx : 0 < Δx) (Y : Matrix (ZMod Nx) ι ℝ) :
    ‖DpM Δx Y‖ ≤ 2 / Δx * ‖Y‖ := by
  have h : ‖DpM Δx Y‖ ^ 2 ≤ (2 / Δx * ‖Y‖) ^ 2 := by
    have e : (2 / Δx) ^ 2 = 4 / Δx ^ 2 := by ring
    rw [Frobenius.norm_sq_eq_sum, mul_pow, Frobenius.norm_sq_eq_sum, e, Finset.sum_comm,
      Finset.sum_comm (f := fun j k => Y j k ^ 2), Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => lemma_3 hΔx.ne' fun i => Y i k
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

omit [NeZero N] in
lemma norm_DmM_le {ι : Type*} [Fintype ι] {Δx : ℝ} (hΔx : 0 < Δx) (Y : Matrix (ZMod Nx) ι ℝ) :
    ‖DmM Δx Y‖ ≤ 2 / Δx * ‖Y‖ := by
  have h : ‖DmM Δx Y‖ ^ 2 ≤ (2 / Δx * ‖Y‖) ^ 2 := by
    have e : (2 / Δx) ^ 2 = 4 / Δx ^ 2 := by ring
    rw [Frobenius.norm_sq_eq_sum, mul_pow, Frobenius.norm_sq_eq_sum, e, Finset.sum_comm,
      Finset.sum_comm (f := fun j k => Y j k ^ 2), Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    change ∑ j, Dm Δx (fun i => Y i k) j ^ 2 ≤ _
    rw [sum_Dm_sq]
    exact lemma_3 hΔx.ne' fun i => Y i k
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

lemma norm_proj_le {m ι n : Type*} [Fintype m] [Fintype ι] [DecidableEq ι] [Fintype n]
    {X : Matrix m ι ℝ} (hX : Xᵀ * X = 1) (Y : Matrix m n ℝ) : ‖X * Xᵀ * Y‖ ≤ ‖Y‖ := by
  rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hX]
  exact norm_transpose_mul_le hX Y

lemma norm_rproj_le {m ι n : Type*} [Fintype m] [Fintype ι] [DecidableEq ι] [Fintype n]
    {V : Matrix n ι ℝ} (hV : Vᵀ * V = 1) (Y : Matrix m n ℝ) : ‖Y * (V * Vᵀ)‖ ≤ ‖Y‖ := by
  rw [← Matrix.mul_assoc, Frobenius.norm_mul_transpose_of_orthonormal hV]
  exact norm_mul_le_of_orthonormal hV Y

/-- If all entries converge, the Frobenius distance tends to zero. -/
lemma tendsto_norm_sub_of_entries {α m n : Type*} [Fintype m] [Fintype n] {l : Filter α}
    {A : α → Matrix m n ℝ} {B : Matrix m n ℝ}
    (h : ∀ i j, Tendsto (fun a => A a i j) l (𝓝 (B i j))) :
    Tendsto (fun a => ‖A a - B‖) l (𝓝 0) := by
  have h2 : Tendsto (fun a => ∑ i, ∑ j, (A a - B) i j ^ 2) l
      (𝓝 (∑ _i : m, ∑ _j : n, (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have := ((h i j).sub_const (B i j)).pow 2
    simpa using this
  have h3 := h2.sqrt
  simp only [Finset.sum_const_zero, Real.sqrt_zero] at h3
  simpa only [Frobenius.norm_def] using h3

/-- If the Frobenius distance tends to zero, all entries converge. -/
lemma tendsto_entry_of_norm_sub {α m n : Type*} [Fintype m] [Fintype n] {l : Filter α}
    {A : α → Matrix m n ℝ} {B : Matrix m n ℝ} (h : Tendsto (fun a => ‖A a - B‖) l (𝓝 0))
    (i : m) (j : n) : Tendsto (fun a => A a i j) l (𝓝 (B i j)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun a => ?_) h
  have := Frobenius.abs_apply_le_norm (A a - B) i j
  simpa using this

namespace Params

/-- The limit `G = -w bᵀ` of the micro variable. -/
noncomputable def limitG (Ψ T : ZMod Nx → ℝ) : Matrix (ZMod Nx) (Fin N) ℝ :=
  -vecMulVec (P.limitFlux Ψ T) (bvec N)

/-- A bound for the operator norm of `𝓛` in the Frobenius norm. -/
noncomputable def fluxBound : ℝ := 2 / P.Δx * (‖P.Apl‖ + ‖P.Ami‖)

omit [NeZero N] in
lemma norm_flux_le {σ₀ : ℝ} (hP : P.Admissible σ₀) (Y : Matrix (ZMod Nx) (Fin N) ℝ) :
    ‖P.flux Y‖ ≤ P.fluxBound * ‖Y‖ := by
  have hΔ := hP.Δx_pos
  have h1 := (Frobenius.norm_mul_le (DmM P.Δx Y) P.Apl).trans
    (mul_le_mul_of_nonneg_right (norm_DmM_le hΔ Y) (norm_nonneg _))
  have h2 := (Frobenius.norm_mul_le (DpM P.Δx Y) P.Ami).trans
    (mul_le_mul_of_nonneg_right (norm_DpM_le hΔ Y) (norm_nonneg _))
  calc ‖P.flux Y‖ ≤ ‖DmM P.Δx Y * P.Apl‖ + ‖DpM P.Δx Y * P.Ami‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [fluxBound]
      nlinarith

/-- The residual, with the limit equation split off. -/
lemma microRes_eq {σ₀ : ℝ} (hP : P.Admissible σ₀) (ε : ℝ) (Ψ T h : ZMod Nx → ℝ)
    (gold g' : Matrix (ZMod Nx) (Fin N) ℝ) :
    P.microRes ε Ψ T h gold g' = (ε ^ 2 / (P.c * P.Δt)) • (g' - gold) + ε • P.flux gold +
      ε ^ 2 • vecMulVec (Dp P.Δx h) (bvec N) + diagonal P.σf * (g' - P.limitG Ψ T) := by
  ext j k
  have hσ : P.σf j ≠ 0 := (hP.σ₀_pos.trans_le (hP.σf_ge j)).ne'
  have hsrc : P.source ε Ψ T h j = P.σf j * P.limitFlux Ψ T j + ε ^ 2 * Dp P.Δx h j := by
    simp only [source, limitFlux]
    field_simp
  simp only [microRes, limitG, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Matrix.diagonal_mul, Matrix.neg_apply, hsrc]
  ring

omit [NeZero N] in
lemma le_inner_diagonal {σ₀ : ℝ} (hP : P.Admissible σ₀) (E : Matrix (ZMod Nx) (Fin N) ℝ) :
    σ₀ * ‖E‖ ^ 2 ≤ ⟪E, diagonal P.σf * E⟫ := by
  rw [Frobenius.norm_sq_eq_sum, Frobenius.inner_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Matrix.diagonal_mul]
  nlinarith [hP.σf_ge j, sq_nonneg (E j k)]

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

/-- **The Galerkin estimate.** Let `S'` solve the S-step in any orthonormal bases `X'`, `V'`, and
let `Π G = X' X'ᵀ G V' V'ᵀ`. Then `g' = X' S' V'ᵀ` is close to `Π G`, uniformly in the bases. This
replaces the formal `ε = 0` computation of the proofs of Theorems 3 and 6. -/
theorem galerkin_bound {σ₀ ε : ℝ} (hP : P.Admissible σ₀) {Ψ T h : ZMod Nx → ℝ}
    {St S' : Matrix ι ι' ℝ} {X' : Matrix (ZMod Nx) ι ℝ} {V' : Matrix (Fin N) ι' ℝ}
    (hX' : X'ᵀ * X' = 1) (hV' : V'ᵀ * V' = 1) (hS : P.IsSStep ε Ψ T h St X' V' S') :
    (σ₀ - ε ^ 2 / (P.c * P.Δt)) *
        ‖X' * S' * V'ᵀ - X' * X'ᵀ * P.limitG Ψ T * (V' * V'ᵀ)‖ ≤
      ε ^ 2 / (P.c * P.Δt) * (‖P.limitG Ψ T‖ + ‖St‖) + |ε| * (P.fluxBound * ‖St‖) +
        ε ^ 2 * ‖vecMulVec (Dp P.Δx h) (bvec N)‖ +
        ‖(diagonal P.σf : Matrix (ZMod Nx) (ZMod Nx) ℝ)‖ *
          ‖X' * X'ᵀ * P.limitG Ψ T * (V' * V'ᵀ) - P.limitG Ψ T‖ := by
  have hc := hP.c_pos
  have hΔt := hP.Δt_pos
  set c₀ := ε ^ 2 / (P.c * P.Δt) with hc₀
  have hc0 : 0 ≤ c₀ := by positivity
  set G := P.limitG Ψ T with hG
  set H := vecMulVec (Dp P.Δx h) (bvec N) with hH
  set g' := X' * S' * V'ᵀ with hg'
  set gold := X' * St * V'ᵀ with hgold
  set Pg := X' * X'ᵀ * G * (V' * V'ᵀ) with hPg
  set E := g' - Pg with hE
  set M := ‖(diagonal P.σf : Matrix (ZMod Nx) (ZMod Nx) ℝ)‖ with hM
  set A := c₀ • (g' - gold) + ε • P.flux gold + ε ^ 2 • H with hA
  have hM0 : 0 ≤ M := norm_nonneg _
  have hE' : E = X' * (S' - X'ᵀ * G * V') * V'ᵀ := by
    simp only [hE, hg', hPg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hres : X'ᵀ * P.microRes ε Ψ T h gold g' * V' = 0 := hS.res_eq_zero P hX' hV'
  have hR0 : (⟪E, P.microRes ε Ψ T h gold g'⟫ : ℝ) = 0 := by
    rw [hE', Frobenius.inner_mul_right, Frobenius.inner_mul_left, Matrix.transpose_transpose,
      ← Matrix.mul_assoc, hres, inner_zero_right]
  have hR : P.microRes ε Ψ T h gold g' = A + diagonal P.σf * E + diagonal P.σf * (Pg - G) := by
    have h1 : P.microRes ε Ψ T h gold g' = c₀ • (g' - gold) + ε • P.flux gold + ε ^ 2 • H +
        diagonal P.σf * (g' - G) := P.microRes_eq hP ε Ψ T h gold g'
    have e : g' - G = E + (Pg - G) := by
      simp only [hE]
      abel
    rw [h1, e, Matrix.mul_add, ← add_assoc]
  have hsplit : (⟪E, A⟫ : ℝ) + ⟪E, diagonal P.σf * E⟫ + ⟪E, diagonal P.σf * (Pg - G)⟫ = 0 := by
    rw [← hR0, hR, inner_add_right E (A + diagonal P.σf * E), inner_add_right E A]
  have hlow := P.le_inner_diagonal hP E
  have hA1 : -(⟪E, A⟫ : ℝ) ≤ ‖E‖ * ‖A‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hA2 : -(⟪E, diagonal P.σf * (Pg - G)⟫ : ℝ) ≤ ‖E‖ * (M * ‖Pg - G‖) := by
    refine (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left (Frobenius.norm_mul_le _ _) (norm_nonneg _)
  have hgold : ‖gold‖ = ‖St‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV', Frobenius.norm_mul_of_orthonormal hX']
  have hPgn : ‖Pg‖ ≤ ‖G‖ := by
    have e : Pg = X' * X'ᵀ * (G * (V' * V'ᵀ)) := Matrix.mul_assoc _ _ _
    rw [e]
    exact (norm_proj_le hX' _).trans (norm_rproj_le hV' _)
  have hdiff : ‖g' - gold‖ ≤ ‖E‖ + ‖G‖ + ‖St‖ := by
    have e : g' - gold = E + Pg - gold := by
      simp only [hE]
      abel
    rw [e]
    calc ‖E + Pg - gold‖ ≤ ‖E + Pg‖ + ‖gold‖ := norm_sub_le _ _
      _ ≤ ‖E‖ + ‖Pg‖ + ‖gold‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by rw [hgold]; gcongr
  have hAn : ‖A‖ ≤ c₀ * (‖E‖ + ‖G‖ + ‖St‖) + |ε| * (P.fluxBound * ‖St‖) + ε ^ 2 * ‖H‖ := by
    have h1 : ‖c₀ • (g' - gold)‖ ≤ c₀ * (‖E‖ + ‖G‖ + ‖St‖) := by
      rw [norm_smul, Real.norm_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left hdiff hc0
    have h2 : ‖ε • P.flux gold‖ ≤ |ε| * (P.fluxBound * ‖St‖) := by
      rw [norm_smul, Real.norm_eq_abs, ← hgold]
      exact mul_le_mul_of_nonneg_left (P.norm_flux_le hP gold) (abs_nonneg _)
    have h3 : ‖ε ^ 2 • H‖ = ε ^ 2 * ‖H‖ := by
      rw [norm_smul, Real.norm_of_nonneg (sq_nonneg ε)]
    calc ‖A‖ ≤ ‖c₀ • (g' - gold) + ε • P.flux gold‖ + ‖ε ^ 2 • H‖ := norm_add_le _ _
      _ ≤ ‖c₀ • (g' - gold)‖ + ‖ε • P.flux gold‖ + ‖ε ^ 2 • H‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by rw [h3]; gcongr
  have hFB : 0 ≤ P.fluxBound := by
    have := hP.Δx_pos
    simp only [fluxBound]
    positivity
  rcases (norm_nonneg E).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    positivity
  · have hq : σ₀ * ‖E‖ ≤ ‖A‖ + M * ‖Pg - G‖ := by
      refine le_of_mul_le_mul_left ?_ hpos
      nlinarith
    nlinarith

/-- The implicit scalar equations of the K-step have the expected limit. -/
lemma tendsto_of_implicit {d σ u₀ f A B : ℝ} (hd : 0 < d) (hσ : 0 < σ) {u : ℝ → ℝ}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 / d * (u ε - u₀) = -(ε * f) - (A + ε ^ 2 * B) - σ * u ε) :
    Tendsto u (𝓝[>] 0) (𝓝 (-(A / σ))) := by
  set G : ℝ → ℝ := fun ε => (ε ^ 2 / d * u₀ - ε * f - (A + ε ^ 2 * B)) / (ε ^ 2 / d + σ) with hG
  have hcont : ContinuousAt G 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hσ.ne')
  have hG0 : G 0 = -(A / σ) := by
    simp only [hG, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
      sub_zero, zero_sub, add_zero, zero_add]
    ring
  have hform : ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε = u ε := by
    filter_upwards [h] with ε hε
    have hden : ε ^ 2 / d + σ ≠ 0 := by positivity
    simp only [hG]
    rw [div_eq_iff hden]
    linear_combination -hε
  have := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).congr' hform
  rwa [hG0] at this

lemma tendsto_sq_div {d : ℝ} : Tendsto (fun ε : ℝ => ε ^ 2 / d) (𝓝[>] 0) (𝓝 0) := by
  have : ContinuousAt (fun ε : ℝ => ε ^ 2 / d) 0 := by fun_prop
  simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))

/-- **The limit of the Galerkin step.** If the bases capture `G = -w bᵀ` in the limit, the Galerkin
step converges to `G`, whatever the bases do. -/
theorem galerkin_tendsto {σ₀ : ℝ} (hP : P.Admissible σ₀) {Ψ T h : ZMod Nx → ℝ}
    {St S' : ℝ → Matrix ι ι' ℝ} {X' : ℝ → Matrix (ZMod Nx) ι ℝ} {V' : ℝ → Matrix (Fin N) ι' ℝ}
    {C : ℝ} (hX : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (X' ε)ᵀ * X' ε = 1)
    (hV : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (V' ε)ᵀ * V' ε = 1)
    (hS : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.IsSStep ε Ψ T h (St ε) (X' ε) (V' ε) (S' ε))
    (hSt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖St ε‖ ≤ C)
    (hPX : Tendsto (fun ε => ‖X' ε * (X' ε)ᵀ * P.limitG Ψ T - P.limitG Ψ T‖) (𝓝[>] 0) (𝓝 0))
    (hQV : Tendsto (fun ε => ‖P.limitG Ψ T * (V' ε * (V' ε)ᵀ) - P.limitG Ψ T‖) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ‖X' ε * S' ε * (V' ε)ᵀ - P.limitG Ψ T‖) (𝓝[>] 0) (𝓝 0) := by
  have hc := hP.c_pos
  have hΔt := hP.Δt_pos
  have hσ₀ := hP.σ₀_pos
  set G := P.limitG Ψ T with hG
  set H := vecMulVec (Dp P.Δx h) (bvec N) with hH
  set M := ‖(diagonal P.σf : Matrix (ZMod Nx) (ZMod Nx) ℝ)‖ with hM
  set F := P.fluxBound with hF
  have hM0 : 0 ≤ M := norm_nonneg _
  have hFB : 0 ≤ F := by
    have := hP.Δx_pos
    simp only [hF, fluxBound]
    positivity
  have hsq : Tendsto (fun ε : ℝ => ε ^ 2 / (P.c * P.Δt)) (𝓝[>] 0) (𝓝 0) := tendsto_sq_div
  have hsq' : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_sq_div (d := 1)
  have habs : Tendsto (fun ε : ℝ => |ε|) (𝓝[>] 0) (𝓝 0) := by
    have : ContinuousAt (fun ε : ℝ => |ε|) 0 := by fun_prop
    simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 / (P.c * P.Δt) ≤ σ₀ / 2 :=
    hsq.eventually (Iic_mem_nhds (half_pos hσ₀))
  set b : ℝ → ℝ := fun ε => ‖X' ε * (X' ε)ᵀ * G - G‖ + ‖G * (V' ε * (V' ε)ᵀ) - G‖ with hb
  have hbt : Tendsto b (𝓝[>] 0) (𝓝 0) := by simpa using hPX.add hQV
  set a : ℝ → ℝ := fun ε => ε ^ 2 / (P.c * P.Δt) * (‖G‖ + C) + |ε| * (F * C) + ε ^ 2 * ‖H‖ +
    M * b ε with ha
  have hat : Tendsto a (𝓝[>] 0) (𝓝 0) := by
    have := (((hsq.mul_const (‖G‖ + C)).add (habs.mul_const (F * C))).add
      (hsq'.mul_const ‖H‖)).add (hbt.const_mul M)
    simpa using this
  have hbound : Tendsto (fun ε => 2 / σ₀ * a ε + b ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hat.const_mul (2 / σ₀)).add hbt
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [hX, hV, hS, hSt, hsmall] with ε h1 h2 h3 h4 h5
  have hgb := P.galerkin_bound hP h1 h2 h3
  rw [← hG, ← hH, ← hF, ← hM] at hgb
  set Pg := X' ε * (X' ε)ᵀ * G * (V' ε * (V' ε)ᵀ) with hPg
  have hPG : ‖Pg - G‖ ≤ b ε := by
    have e : Pg - G = X' ε * (X' ε)ᵀ * (G * (V' ε * (V' ε)ᵀ) - G) + (X' ε * (X' ε)ᵀ * G - G) := by
      rw [Matrix.mul_sub, hPg, Matrix.mul_assoc (X' ε * (X' ε)ᵀ) G]
      abel
    rw [e]
    calc _ ≤ ‖X' ε * (X' ε)ᵀ * (G * (V' ε * (V' ε)ᵀ) - G)‖ + ‖X' ε * (X' ε)ᵀ * G - G‖ :=
          norm_add_le _ _
      _ ≤ ‖G * (V' ε * (V' ε)ᵀ) - G‖ + ‖X' ε * (X' ε)ᵀ * G - G‖ := by
          gcongr
          exact norm_proj_le h1 _
      _ = b ε := add_comm _ _
  set E := ‖X' ε * S' ε * (V' ε)ᵀ - Pg‖ with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  have hc0 : 0 ≤ ε ^ 2 / (P.c * P.Δt) := by positivity
  have hE1 : σ₀ / 2 * E ≤ a ε := by
    have h6 : σ₀ / 2 * E ≤ (σ₀ - ε ^ 2 / (P.c * P.Δt)) * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE0
    have h7 : ε ^ 2 / (P.c * P.Δt) * (‖G‖ + ‖St ε‖) ≤ ε ^ 2 / (P.c * P.Δt) * (‖G‖ + C) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    have h8 : |ε| * (F * ‖St ε‖) ≤ |ε| * (F * C) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hFB) (abs_nonneg _)
    have h9 : M * ‖Pg - G‖ ≤ M * b ε := mul_le_mul_of_nonneg_left hPG hM0
    simp only [ha]
    linarith
  have hE2 : E ≤ 2 / σ₀ * a ε := by
    have : E = 2 / σ₀ * (σ₀ / 2 * E) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hE1 (by positivity)
  calc ‖X' ε * S' ε * (V' ε)ᵀ - G‖ ≤ E + ‖Pg - G‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **arXiv 2402.16746, Theorem 3, as a genuine limit.** Fix the data of step `n`, with
`bᵀ Vⁿ ≠ 0` and `Xⁿᵀ Ψδ⁰(acT) ≠ 0`, and let `ε ↓ 0`, with any fixed-rank steps. Then
`gⁿ⁺¹ → -w bᵀ` and the left side of the discrete diffusion equation tends to `diffOp`. The bases
need not converge. For `ε > 0` they contain `w` and `b` only approximately: this is the true content
of the range inclusions in the paper's proof. -/
theorem theorem_3_tendsto {σ₀ : ℝ} (hP : P.Admissible σ₀) {r : ℕ} {Ψ T h : ZMod Nx → ℝ}
    (hΨ : ∀ i, 0 ≤ Ψ i) {X : Matrix (ZMod Nx) (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix (Fin N) (Fin r) ℝ} {K' X' : ℝ → Matrix (ZMod Nx) (Fin r) ℝ}
    {L' V' : ℝ → Matrix (Fin N) (Fin r) ℝ} {SK SL S' : ℝ → Matrix (Fin r) (Fin r) ℝ}
    {T' h' : ℝ → ZMod Nx → ℝ}
    (hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.IsFixedRankStep ε Ψ T h X S V (K' ε) (L' ε) (X' ε) (SK ε) (V' ε)
      (SL ε) (S' ε) (T' ε) (h' ε))
    (hb : bvec N ᵥ* V ≠ 0) (hq : Xᵀ *ᵥ P.source 0 Ψ T h ≠ 0) :
    (∀ j k, Tendsto (fun ε => (X' ε * S' ε * (V' ε)ᵀ) j k) (𝓝[>] 0) (𝓝 (P.limitG Ψ T j k))) ∧
    ∀ i, Tendsto (fun ε => (1 + 2 * P.a * Ψ i / P.cν) * ((T' ε i - T i) / P.Δt)) (𝓝[>] 0)
      (𝓝 (P.diffOp Ψ T i)) := by
  have hcpos := hP.c_pos
  have hΔt := hP.Δt_pos
  have hd : 0 < P.c * P.Δt := by positivity
  set w := P.limitFlux Ψ T with hw
  set G := P.limitG Ψ T with hG
  have hGapply (j : ZMod Nx) (k : Fin N) : G j k = -(w j * bvec N k) := by
    simp [hG, limitG, Matrix.vecMulVec_apply, hw]
  set v := bvec N ᵥ* V with hv
  have hsrc (ε : ℝ) (j : ZMod Nx) :
      P.source ε Ψ T h j = P.source 0 Ψ T h j + ε ^ 2 * Dp P.Δx h j := by
    simp [source]
  -- the K-step
  have hKent (j : ZMod Nx) (m : Fin r) :
      Tendsto (fun ε => K' ε j m) (𝓝[>] 0) (𝓝 (-(w j * v m))) := by
    have hσ : 0 < P.σf j := hP.σ₀_pos.trans_le (hP.σf_ge j)
    have hlim := tendsto_of_implicit (d := P.c * P.Δt) (σ := P.σf j) (u₀ := (X * S) j m)
      (f := (DmM P.Δx (X * S) * (Vᵀ * P.Apl * V) + DpM P.Δx (X * S) * (Vᵀ * P.Ami * V)) j m)
      (A := P.source 0 Ψ T h j * v m) (B := Dp P.Δx h j * v m) (u := fun ε => K' ε j m) hd hσ ?_
    · have e : P.source 0 Ψ T h j * v m / P.σf j = w j * v m := by
        rw [P.source_zero hP, ← hw]
        field_simp
      rwa [e] at hlim
    · filter_upwards [hs] with ε hε
      have h1 := congrFun (congrFun hε.K_eq j) m
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul,
        Matrix.vecMulVec_apply, Matrix.diagonal_mul, hsrc ε j] at h1
      linear_combination h1
  obtain ⟨y, hy⟩ := exists_dotProduct_eq_one hb
  set M₁ : ℝ → Matrix (ZMod Nx) (Fin N) ℝ := fun ε => K' ε * vecMulVec y (bvec N) with hM₁
  have hM₁t : Tendsto (fun ε => ‖M₁ ε - G‖) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_norm_sub_of_entries fun j k => ?_
    have e : G j k = ∑ m, -(w j * v m) * (y m * bvec N k) := by
      rw [hGapply]
      have hy' : ∑ m, v m * y m = 1 := hy
      calc -(w j * bvec N k) = -(w j * bvec N k) * ∑ m, v m * y m := by rw [hy', mul_one]
        _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
    rw [e]
    simp only [hM₁, Matrix.mul_apply, Matrix.vecMulVec_apply]
    exact tendsto_finsetSum _ fun m _ => (hKent j m).mul_const _
  have hPX : Tendsto (fun ε => ‖X' ε * (X' ε)ᵀ * G - G‖) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hM₁t.const_mul 2)
    filter_upwards [hs] with ε hε
    have hfix : X' ε * (X' ε)ᵀ * M₁ ε = M₁ ε := by
      have e : M₁ ε = X' ε * (SK ε * vecMulVec y (bvec N)) := by
        simp only [hM₁, hε.K_qr, Matrix.mul_assoc]
      rw [e, ← Matrix.mul_assoc, Matrix.mul_assoc (X' ε), hε.X'_orth, Matrix.mul_one]
    have e : X' ε * (X' ε)ᵀ * G - G = X' ε * (X' ε)ᵀ * (G - M₁ ε) + (M₁ ε - G) := by
      rw [Matrix.mul_sub, hfix]
      abel
    rw [e]
    calc _ ≤ ‖X' ε * (X' ε)ᵀ * (G - M₁ ε)‖ + ‖M₁ ε - G‖ := norm_add_le _ _
      _ ≤ ‖G - M₁ ε‖ + ‖M₁ ε - G‖ := by
          gcongr
          exact norm_proj_le hε.X'_orth _
      _ = 2 * ‖M₁ ε - G‖ := by
          rw [norm_sub_rev]
          ring
  -- the L-step
  set q := Xᵀ *ᵥ P.source 0 Ψ T h with hqdef
  set q₂ := Xᵀ *ᵥ Dp P.Δx h with hq₂
  obtain ⟨y', hy'⟩ := exists_dotProduct_eq_one hq
  set Y₂ := P.Apl * (V * Sᵀ) * ((DmM P.Δx X)ᵀ * X) + P.Ami * (V * Sᵀ) * ((DpM P.Δx X)ᵀ * X) with hY₂
  set U : ℝ → Matrix (Fin N) (Fin r) ℝ := fun ε =>
    L' ε * ((ε ^ 2 / (P.c * P.Δt)) • (1 : Matrix (Fin r) (Fin r) ℝ) +
      Xᵀ * diagonal P.σf * X) with hU
  have hqε (ε : ℝ) : Xᵀ *ᵥ P.source ε Ψ T h = q + ε ^ 2 • q₂ := by
    have e : P.source ε Ψ T h = P.source 0 Ψ T h + ε ^ 2 • Dp P.Δx h := by
      funext j
      simp [hsrc ε j]
    rw [e, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hUeq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k m, U ε k m =
      ε ^ 2 / (P.c * P.Δt) * (V * Sᵀ) k m - ε * Y₂ k m - bvec N k * (q m + ε ^ 2 * q₂ m) := by
    filter_upwards [hs] with ε hε
    have hL := hε.L_eq
    rw [IsLStep, smul_sub, sub_eq_sub_iff_add_eq_add] at hL
    have hsol : U ε = (ε ^ 2 / (P.c * P.Δt)) • (V * Sᵀ) + (-(ε • Y₂) -
        vecMulVec (bvec N) (Xᵀ *ᵥ P.source ε Ψ T h)) := by
      simp only [hU, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      rw [hL, add_comm]
    intro k m
    rw [hsol, hqε ε]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply,
      smul_eq_mul, Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply]
    ring
  have hUt (k : Fin N) (m : Fin r) :
      Tendsto (fun ε => U ε k m) (𝓝[>] 0) (𝓝 (-(bvec N k * q m))) := by
    have hcont : ContinuousAt (fun ε : ℝ => ε ^ 2 / (P.c * P.Δt) * (V * Sᵀ) k m - ε * Y₂ k m -
        bvec N k * (q m + ε ^ 2 * q₂ m)) 0 := by fun_prop
    have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    have e : (0 : ℝ) ^ 2 / (P.c * P.Δt) * (V * Sᵀ) k m - 0 * Y₂ k m -
        bvec N k * (q m + 0 ^ 2 * q₂ m) = -(bvec N k * q m) := by
      simp
    rw [e] at ht
    refine ht.congr' ?_
    filter_upwards [hUeq] with ε hε
    exact (hε k m).symm
  have hu (k : Fin N) :
      Tendsto (fun ε => (U ε *ᵥ (-y')) k) (𝓝[>] 0) (𝓝 (bvec N k)) := by
    have e : bvec N k = ∑ m, -(bvec N k * q m) * (-y') m := by
      have hy'' : ∑ m, q m * y' m = 1 := hy'
      calc bvec N k = bvec N k * ∑ m, q m * y' m := by rw [hy'', mul_one]
        _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by simp only [Pi.neg_apply]; ring
    rw [e]
    simp only [Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum _ fun m _ => (hUt k m).mul_const _
  set M₂ : ℝ → Matrix (ZMod Nx) (Fin N) ℝ := fun ε => -vecMulVec w (U ε *ᵥ (-y')) with hM₂
  have hM₂t : Tendsto (fun ε => ‖M₂ ε - G‖) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_norm_sub_of_entries fun j k => ?_
    rw [hGapply]
    simp only [hM₂, Matrix.neg_apply, Matrix.vecMulVec_apply]
    exact ((hu k).const_mul (w j)).neg
  have hQV : Tendsto (fun ε => ‖G * (V' ε * (V' ε)ᵀ) - G‖) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hM₂t.const_mul 2)
    filter_upwards [hs] with ε hε
    have hmem : U ε *ᵥ (-y') ∈ Set.range (V' ε).mulVec := by
      refine ⟨((SL ε)ᵀ * ((ε ^ 2 / (P.c * P.Δt)) • (1 : Matrix (Fin r) (Fin r) ℝ) +
        Xᵀ * diagonal P.σf * X)) *ᵥ (-y'), ?_⟩
      simp only [hU, hε.L_qr]
      rw [Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc]
    have hfix : M₂ ε * (V' ε * (V' ε)ᵀ) = M₂ ε := by
      have h2 : (U ε *ᵥ (-y')) ᵥ* (V' ε * (V' ε)ᵀ) = U ε *ᵥ (-y') := by
        rw [← Matrix.vecMul_vecMul, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
          ← Matrix.mulVec_transpose]
        exact mulVec_mulVec_transpose_of_mem hε.V'_orth hmem
      simp only [hM₂]
      rw [Matrix.neg_mul, Matrix.vecMulVec_mul, h2]
    have e : G * (V' ε * (V' ε)ᵀ) - G = (G - M₂ ε) * (V' ε * (V' ε)ᵀ) + (M₂ ε - G) := by
      rw [Matrix.sub_mul, hfix]
      abel
    rw [e]
    calc _ ≤ ‖(G - M₂ ε) * (V' ε * (V' ε)ᵀ)‖ + ‖M₂ ε - G‖ := norm_add_le _ _
      _ ≤ ‖G - M₂ ε‖ + ‖M₂ ε - G‖ := by
          gcongr
          exact norm_rproj_le hε.V'_orth _
      _ = 2 * ‖M₂ ε - G‖ := by
          rw [norm_sub_rev]
          ring
  -- the S-step
  have hSt : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖((X' ε)ᵀ * X) * S * (Vᵀ * V' ε)‖ ≤ ‖X * S * Vᵀ‖ := by
    filter_upwards [hs] with ε hε
    have e : ((X' ε)ᵀ * X) * S * (Vᵀ * V' ε) = (X' ε)ᵀ * (X * S * Vᵀ) * V' ε := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact (norm_mul_le_of_orthonormal hε.V'_orth _).trans (norm_transpose_mul_le hε.X'_orth _)
  have hg := P.galerkin_tendsto hP (hs.mono fun _ hε => hε.X'_orth)
    (hs.mono fun _ hε => hε.V'_orth) (hs.mono fun _ hε => hε.S_eq) hSt hPX hQV
  refine ⟨fun j k => tendsto_entry_of_norm_sub hg j k, fun i => ?_⟩
  refine P.macro_tendsto hP hΨ (g₁ := fun ε j => (X' ε * S' ε * (V' ε)ᵀ) j 0)
    (hs.mono fun _ hε => hε.macro_eq) (hs.mono fun _ hε => hε.temp_eq) (fun j => ?_) i
  have ht : Tendsto (fun ε => (X' ε * S' ε * (V' ε)ᵀ) j 0) (𝓝[>] 0) (𝓝 (G j 0)) :=
    tendsto_entry_of_norm_sub hg j 0
  have hb0 : bvec N 0 = γ₁ := by simp [bvec]
  have e : G j 0 = -(γ₁ * P.limitFlux Ψ T j) := by rw [hGapply, hb0, mul_comm]
  rwa [e] at ht

/-- **The estimate behind arXiv 2402.16746, Theorem 6, for `ε > 0`.** Every step of the integrator
of Section 4.2 satisfies, as soon as `ε²/(c Δt) ≤ σ₀/2`,
`‖gⁿ⁺¹ + w bᵀ‖ ≤ 4/σ₀ (ε²/(cΔt) (‖w bᵀ‖ + ‖gⁿ‖) + ε ‖𝓛‖ ‖gⁿ‖ + ε² ‖δ⁰h bᵀ‖)`.
The bound does not depend on the bases, nor on the ranks, which may vary with `ε`, nor on the
truncation. Exact augmentation with `w` and `b` is what makes it `O(ε)`. No invertibility is
assumed. -/
theorem IsAdaptiveStep.norm_sub_le {ρ q q' τ ρs ρ₁ : Type*} [Fintype ρ] [Fintype q]
    [DecidableEq q] [Fintype q'] [DecidableEq q'] [Fintype τ] [DecidableEq τ] [Fintype ρs]
    [DecidableEq ρs] [Fintype ρ₁] [DecidableEq ρ₁] {σ₀ ε : ℝ} (hP : P.Admissible σ₀)
    {Ψ T h T' h' : ZMod Nx → ℝ}
    {X : Matrix (ZMod Nx) ρ ℝ} {S : Matrix ρ ρ ℝ} {V : Matrix (Fin N) ρ ℝ}
    {K' : Matrix (ZMod Nx) ρ ℝ} {L' : Matrix (Fin N) ρ ℝ} {Xh : Matrix (ZMod Nx) ι ℝ}
    {Vrem : Matrix (Fin N) q ℝ} {Sh : Matrix ι (Unit ⊕ q) ℝ} {Xr : Matrix (ZMod Nx) q' ℝ}
    {Sr : Matrix q' q ℝ} {U : Matrix q' τ ℝ} {W : Matrix q τ ℝ} {s : τ → ℝ} {f : ρs ↪ τ}
    {Xa : Matrix (ZMod Nx) Unit ℝ} {Sa : Matrix Unit Unit ℝ} {X' : Matrix (ZMod Nx) ρ₁ ℝ}
    {R₂ : Matrix ρ₁ (Unit ⊕ ρs) ℝ}
    (hs : P.IsAdaptiveStep ε Ψ T h X S V K' L' Xh Vrem Sh Xr Sr U W s f Xa Sa X' R₂ T' h')
    (hsmall : ε ^ 2 / (P.c * P.Δt) ≤ σ₀ / 2) :
    ‖X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ - P.limitG Ψ T‖ ≤
      4 / σ₀ * (ε ^ 2 / (P.c * P.Δt) * (‖P.limitG Ψ T‖ + ‖X * S * Vᵀ‖) +
        |ε| * (P.fluxBound * ‖X * S * Vᵀ‖) + ε ^ 2 * ‖vecMulVec (Dp P.Δx h) (bvec N)‖) := by
  have hc := hP.c_pos
  have hΔt := hP.Δt_pos
  have hσ₀ := hP.σ₀_pos
  set G := P.limitG Ψ T with hG
  set H := vecMulVec (Dp P.Δx h) (bvec N) with hH
  set C := ‖X * S * Vᵀ‖ with hC
  set F := P.fluxBound with hF
  have hFB : 0 ≤ F := by
    have := hP.Δx_pos
    simp only [hF, fluxBound]
    positivity
  have hVorth := hs.Vh_orth
  have hbV := bvec_vecMul_hat hs.Vh_orth
  set Vh := fromCols (e₁col N) Vrem with hVh
  -- `G` is fixed by the Galerkin projection
  have hfixL : Xh * Xhᵀ * G = G := by
    simp only [hG, limitG, Matrix.mul_neg, Matrix.mul_vecMulVec]
    rw [← Matrix.mulVec_mulVec, mulVec_mulVec_transpose_of_mem hs.Xh_orth hs.Xh_w]
  have hγ : γ₁ ≠ 0 := γ₁_pos.ne'
  have hbmem : bvec N ∈ Set.range Vh.mulVec := by
    refine ⟨Sum.elim (fun _ => γ₁) 0, ?_⟩
    ext k
    simp only [hVh, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      fromCols_apply_inl, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, e₁col,
      Matrix.replicateCol_apply, Fintype.univ_unit, Finset.sum_singleton]
    field_simp
  have hb2 : bvec N ᵥ* (Vh * Vhᵀ) = bvec N := by
    rw [← Matrix.vecMul_vecMul, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      ← Matrix.mulVec_transpose]
    exact mulVec_mulVec_transpose_of_mem hVorth hbmem
  have hfixR : G * (Vh * Vhᵀ) = G := by
    simp only [hG, limitG, Matrix.neg_mul, Matrix.vecMulVec_mul, hb2]
  have hSt : ‖(Xhᵀ * X) * S * (Vᵀ * Vh)‖ ≤ C := by
    have e : (Xhᵀ * X) * S * (Vᵀ * Vh) = Xhᵀ * (X * S * Vᵀ) * Vh := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact (norm_mul_le_of_orthonormal hVorth _).trans (norm_transpose_mul_le hs.Xh_orth _)
  have hgb := P.galerkin_bound hP hs.Xh_orth hVorth hs.S_eq
  rw [← hG, ← hH, ← hF, hfixL, hfixR, sub_self, norm_zero, mul_zero, add_zero] at hgb
  set gh := Xh * Sh * Vhᵀ with hghdef
  set a := ε ^ 2 / (P.c * P.Δt) * (‖G‖ + C) + |ε| * (F * C) + ε ^ 2 * ‖H‖ with ha
  have hc0 : 0 ≤ ε ^ 2 / (P.c * P.Δt) := by positivity
  have hgh : ‖gh - G‖ ≤ 2 / σ₀ * a := by
    have hE0 : 0 ≤ ‖gh - G‖ := norm_nonneg _
    have h6 : σ₀ / 2 * ‖gh - G‖ ≤ (σ₀ - ε ^ 2 / (P.c * P.Δt)) * ‖gh - G‖ :=
      mul_le_mul_of_nonneg_right (by linarith) hE0
    have h7 : ε ^ 2 / (P.c * P.Δt) * (‖G‖ + ‖(Xhᵀ * X) * S * (Vᵀ * Vh)‖) ≤
        ε ^ 2 / (P.c * P.Δt) * (‖G‖ + C) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    have h8 : |ε| * (F * ‖(Xhᵀ * X) * S * (Vᵀ * Vh)‖) ≤ |ε| * (F * C) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSt hFB) (abs_nonneg _)
    have h9 : σ₀ / 2 * ‖gh - G‖ ≤ a := by
      simp only [ha]
      linarith
    have : ‖gh - G‖ = 2 / σ₀ * (σ₀ / 2 * ‖gh - G‖) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h9 (by positivity)
  -- the factors of the new iterate
  have hVrem : Vremᵀ * Vrem = 1 := by
    ext m m'
    have := congrFun (congrFun hVorth (Sum.inr m)) (Sum.inr m')
    simpa [hVh, Matrix.mul_apply, Matrix.one_apply] using this
  have he := e₁col_orth (N := N)
  have hKh : Xh * Sh = gh * Vh := by
    simp only [hghdef]
    rw [Matrix.mul_assoc, hVorth, Matrix.mul_one]
  have hap : Xa * Sa = gh * e₁col N := by
    rw [← hs.ap_qr, hKh, hVh, Matrix.mul_fromCols]
    ext j u
    simp
  have hrem : Xr * Sr = gh * Vrem := by
    rw [← hs.rem_qr, hKh, hVh, Matrix.mul_fromCols]
    ext j m
    simp
  have hbm : bvec N ∈ Set.range (e₁col N).mulVec := by
    refine ⟨fun _ => γ₁, ?_⟩
    ext k
    simp only [Matrix.mulVec, dotProduct, e₁col, Matrix.replicateCol_apply, Fintype.univ_unit,
      Finset.sum_singleton]
    field_simp
  have hbe : bvec N ᵥ* (e₁col N * (e₁col N)ᵀ) = bvec N := by
    rw [← Matrix.vecMul_vecMul, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      ← Matrix.mulVec_transpose]
    exact mulVec_mulVec_transpose_of_mem he hbm
  have hGe : G * (e₁col N * (e₁col N)ᵀ) = G := by
    simp only [hG, limitG, Matrix.neg_mul, Matrix.vecMulVec_mul, hbe]
  have hGV : G * Vrem = 0 := by
    have hb0 : bvec N ᵥ* Vrem = 0 := by
      funext m
      have := congrFun hbV (Sum.inr m)
      simpa [hVh, Matrix.vecMul, dotProduct] using this
    simp only [hG, limitG, Matrix.neg_mul, Matrix.vecMulVec_mul, hb0]
    ext j m
    simp [Matrix.vecMulVec_apply]
  set Wf := W.submatrix id f with hWfdef
  set Uf := U.submatrix id f with hUfdef
  have ha' : Sr * Wf = Uf * diagonal (s ∘ f) := svd_trunc hs.svd hs.W_orth
  have hWf : Wfᵀ * Wf = 1 := by
    have e : Wfᵀ * Wf = (Wᵀ * W).submatrix f f := by
      ext a b
      simp [hWfdef, Matrix.mul_apply]
    rw [e, hs.W_orth, Matrix.submatrix_one _ f.injective]
  have hg' : X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ =
      (Xa * Sa) * (e₁col N)ᵀ + (Xr * Uf) * diagonal (s ∘ f) * (Vrem * Wf)ᵀ := by
    rw [adaptS, ← Matrix.mul_assoc, ← hs.R₂_eq, adaptV, Matrix.transpose_fromCols,
      Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero, zero_add]
    rw [Matrix.fromCols_mul_fromRows]
  have hTrem : (Xr * Uf) * diagonal (s ∘ f) * (Vrem * Wf)ᵀ =
      (gh * Vrem) * (Wf * Wfᵀ) * Vremᵀ := by
    rw [Matrix.mul_assoc Xr Uf, ← ha', ← Matrix.mul_assoc Xr Sr, hrem, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hdiff : X' * adaptS R₂ Sa s f * (adaptV Vrem W f)ᵀ - G =
      (gh - G) * (e₁col N * (e₁col N)ᵀ) + ((gh - G) * Vrem) * (Wf * Wfᵀ) * Vremᵀ := by
    have e1 : (gh - G) * (e₁col N * (e₁col N)ᵀ) = gh * e₁col N * (e₁col N)ᵀ - G := by
      rw [Matrix.sub_mul, hGe, ← Matrix.mul_assoc gh]
    have e2 : (gh - G) * Vrem = gh * Vrem := by
      rw [Matrix.sub_mul, hGV, sub_zero]
    rw [hg', hap, hTrem, e1, e2]
    abel
  rw [hdiff]
  have h1 := norm_rproj_le he (gh - G)
  have h2 : ‖((gh - G) * Vrem) * (Wf * Wfᵀ) * Vremᵀ‖ = ‖((gh - G) * Vrem) * (Wf * Wfᵀ)‖ :=
    Frobenius.norm_mul_transpose_of_orthonormal hVrem _
  have h3 := norm_rproj_le hWf ((gh - G) * Vrem)
  have h4 := norm_mul_le_of_orthonormal hVrem (gh - G)
  calc _ ≤ ‖(gh - G) * (e₁col N * (e₁col N)ᵀ)‖ + ‖((gh - G) * Vrem) * (Wf * Wfᵀ) * Vremᵀ‖ :=
        norm_add_le _ _
    _ ≤ 4 / σ₀ * a := by
        have e : 4 / σ₀ * a = 2 * (2 / σ₀ * a) := by ring
        rw [e, h2]
        linarith

/-- **arXiv 2402.16746, Theorem 6, as a genuine limit.** Fix the data of step `n` and let `ε ↓ 0`,
with any steps of the integrator of Section 4.2. Then `gⁿ⁺¹ → -w bᵀ`, and the left side of the
discrete diffusion equation tends to `diffOp`. No invertibility and no condition on the old bases
are needed, unlike in Theorem 3. The families have fixed index types here. For ranks varying with
`ε`, use `IsAdaptiveStep.norm_sub_le`, which is uniform in the ranks. -/
theorem theorem_6_tendsto {ρ q q' τ ρs ρ₁ : Type*} [Fintype ρ] [Fintype q]
    [DecidableEq q] [Fintype q'] [DecidableEq q'] [Fintype τ] [DecidableEq τ] [Fintype ρs]
    [DecidableEq ρs] [Fintype ρ₁] [DecidableEq ρ₁] {σ₀ : ℝ} (hP : P.Admissible σ₀)
    {Ψ T h : ZMod Nx → ℝ} (hΨ : ∀ i, 0 ≤ Ψ i)
    {X : Matrix (ZMod Nx) ρ ℝ} {S : Matrix ρ ρ ℝ} {V : Matrix (Fin N) ρ ℝ}
    {K' : ℝ → Matrix (ZMod Nx) ρ ℝ} {L' : ℝ → Matrix (Fin N) ρ ℝ}
    {Xh : ℝ → Matrix (ZMod Nx) ι ℝ} {Vrem : ℝ → Matrix (Fin N) q ℝ}
    {Sh : ℝ → Matrix ι (Unit ⊕ q) ℝ} {Xr : ℝ → Matrix (ZMod Nx) q' ℝ}
    {Sr : ℝ → Matrix q' q ℝ} {U : ℝ → Matrix q' τ ℝ} {W : ℝ → Matrix q τ ℝ} {s : ℝ → τ → ℝ}
    {f : ℝ → (ρs ↪ τ)} {Xa : ℝ → Matrix (ZMod Nx) Unit ℝ} {Sa : ℝ → Matrix Unit Unit ℝ}
    {X' : ℝ → Matrix (ZMod Nx) ρ₁ ℝ} {R₂ : ℝ → Matrix ρ₁ (Unit ⊕ ρs) ℝ}
    {T' h' : ℝ → ZMod Nx → ℝ}
    (hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.IsAdaptiveStep ε Ψ T h X S V (K' ε) (L' ε) (Xh ε) (Vrem ε) (Sh ε)
      (Xr ε) (Sr ε) (U ε) (W ε) (s ε) (f ε) (Xa ε) (Sa ε) (X' ε) (R₂ ε) (T' ε) (h' ε)) :
    (∀ j k, Tendsto (fun ε => (X' ε * adaptS (R₂ ε) (Sa ε) (s ε) (f ε) *
        (adaptV (Vrem ε) (W ε) (f ε))ᵀ) j k) (𝓝[>] 0) (𝓝 (P.limitG Ψ T j k))) ∧
    ∀ i, Tendsto (fun ε => (1 + 2 * P.a * Ψ i / P.cν) * ((T' ε i - T i) / P.Δt)) (𝓝[>] 0)
      (𝓝 (P.diffOp Ψ T i)) := by
  have hσ₀ := hP.σ₀_pos
  set G := P.limitG Ψ T with hG
  set H := vecMulVec (Dp P.Δx h) (bvec N) with hH
  set C := ‖X * S * Vᵀ‖ with hC
  set F := P.fluxBound with hF
  have hsq : Tendsto (fun ε : ℝ => ε ^ 2 / (P.c * P.Δt)) (𝓝[>] 0) (𝓝 0) := tendsto_sq_div
  have hsq' : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_sq_div (d := 1)
  have habs : Tendsto (fun ε : ℝ => |ε|) (𝓝[>] 0) (𝓝 0) := by
    have : ContinuousAt (fun ε : ℝ => |ε|) 0 := by fun_prop
    simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 / (P.c * P.Δt) ≤ σ₀ / 2 :=
    hsq.eventually (Iic_mem_nhds (half_pos hσ₀))
  have hbound : Tendsto (fun ε => 4 / σ₀ * (ε ^ 2 / (P.c * P.Δt) * (‖G‖ + C) + |ε| * (F * C) +
      ε ^ 2 * ‖H‖)) (𝓝[>] 0) (𝓝 0) := by
    have := (((hsq.mul_const (‖G‖ + C)).add (habs.mul_const (F * C))).add
      (hsq'.mul_const ‖H‖)).const_mul (4 / σ₀)
    simpa using this
  have hg : Tendsto (fun ε => ‖X' ε * adaptS (R₂ ε) (Sa ε) (s ε) (f ε) *
      (adaptV (Vrem ε) (W ε) (f ε))ᵀ - G‖) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
    filter_upwards [hs, hsmall] with ε hε h5
    exact hε.norm_sub_le P hP h5
  refine ⟨fun j k => tendsto_entry_of_norm_sub hg j k, fun i => ?_⟩
  refine P.macro_tendsto hP hΨ (g₁ := fun ε j => (X' ε * adaptS (R₂ ε) (Sa ε) (s ε) (f ε) *
      (adaptV (Vrem ε) (W ε) (f ε))ᵀ) j 0)
    (hs.mono fun _ hε => hε.macro_eq) (hs.mono fun _ hε => hε.temp_eq) (fun j => ?_) i
  have ht := tendsto_entry_of_norm_sub hg j 0
  have e : G j 0 = -(γ₁ * P.limitFlux Ψ T j) := by
    simp [hG, limitG, Matrix.vecMulVec_apply, bvec, mul_comm]
  rwa [e] at ht

end Params

end Limit

end LeanDLRA.Literature.P2402_16746
