import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Kinetic.Defs
import LeanDLRA.LinearAlgebra.LowRank.SepRank

/-!
# Results of arXiv 2412.05912: a review of low-rank methods for kinetic simulations

Einkemmer, Kormann, Kusch, McClarren, Qiu, *A review of low-rank methods for time-dependent kinetic
simulations*. A review has no numbered theorems: its claims are made in passing and often cited.
This module proves the claims of Sections 2, 6.2, 6.3 about the rank of kinetic solutions, on the
equations themselves wherever Mathlib has the objects, and refutes two of them.

**Two claims are false.** Sec. 2 says that "if the rank of the initial value is `r`, then the
linearized solution is at most rank `r + 1`", citing [61] = arXiv 1902.00424, and that for `(1 + α
cos (k x)) f^eq (v)` "the solution is at most rank 2 in the linear regime". What [61] proves is the
bound `m + 1` for `m` excited Fourier modes, and `m` is not the rank of the initial value.

* `linearized_rank_claim_false`, `linearized_rank_claim_false_perturbation`: the general claim fails
  for the linearized Vlasov–Maxwell system (`IsLinearizedVM`, the system of [61]) around a
  Maxwellian, for the whole distribution and for the perturbation alone. The witness `pert` has two
  wave numbers on the torus, no charge and no current, so `E = B = 0`: it is exact. It starts at
  rank `2` (`full_rank_zero`) and for every `t ≠ 0` it does not have rank `3`
  (`full_not_rank_le_three`). The perturbation starts at rank `1` and does not have rank `2`
  (`pert_not_rank_le_two`). `full_rank_le_five` is the bound of [61].
* `linearized_example_rank_eq_three`: the example fails too. For the Lorentzian `f^eq` the
  linearized Vlasov–Poisson system (`IsLinearizedVP`) is solved in closed form (`landauPert`,
  `landauField`, with density `e^{-k t} cos t`), and from the rank-one initial value the rank is
  exactly `3` for every `t > 0`: `cos (k x)` is two Fourier modes. The count `2` is true of the
  perturbation alone (`landauPert_rank_le_two`). This needs the Fourier transform of the Lorentzian,
  `integral_cos_mul_lor`, proved here by Fourier inversion. Uniqueness of solutions is not claimed.

## Free streaming, Sec. 2, Eq. (3)

For `x, v, k` in any real inner product space: `freeStream` satisfies the equation
(`freeStream_transport`), the initial condition (`freeStream_zero`), both forms of Eq. (3)
(`freeStream_eq_product`), and is the unique differentiable solution (`freeStream_unique`). Its
complex rank is exactly one, also on every grid (`freeStream_rank_eq_one`,
`freeStream_sample_rank`). Over `ℝ` the rank is two (`freeStream_re_rank_le_two`,
`freeStream_re_not_rank_le_one`), which matters for the real integrators of this library. On a grid
with any discretization having the plane wave as an eigenvector, `discreteStream_hasDerivAt`,
`discreteStream_rank_le` and `transportField_normal_eq_zero` give the exact rank-one solution and
the vanishing normal component, so `ε = 0` in the robust bounds. That last statement uses Hermitian
projectors over `ℂ` and does not run the integrators.

## `f = g²`, Sec. 6.3

For the Vlasov operator with any force: `vlasovOp_comp` (the chain rule, so any transformation),
`vlasovOp_sq`, `vlasov_sq_iff` (for `g ∈ C¹`, also through zeros of `g`), `vlasov_sq_of_solves`,
`vlasov_sqrt_of_solves`, `vlasov_selfConsistent_iff` (force depending on `f`). For diffusion, in
every finite dimension: `laplacian_comp`, `heatOp_sq`, `heat_sq_iff_const` (`g` and `g²` both solve
the heat equation only for constants), `heat_sqrt_counterexample`; for the Fokker–Planck operator,
`fpOp_sq`, `fp_sq_iff`, `fp_sqrt_maxwellian` (the Maxwellian is an equilibrium, its square root is
not). On rank: `exp_not_low_rank`, and `HasRankLEOver.sq`, which is not in the paper.

## Near equilibrium, Secs. 2, 6.2

The expansion with its ranks `6` and `10` is already in `Literature/Kinetic/P1804_04561a.lean` and
is not repeated: `eq8_remainder`, `eq8_rank_le_two`, `eq8_rank_le_three`, `eq8_rank_sharp_two`,
`eq8_rank_sharp_three`, `maxwellian_not_low_rank`. New here: `multiplicative_rank_le` and
`additive_not_low_rank`, the comparison of the two decompositions of Sec. 6.2.

## Rank four up to `ε²`, Sec. 2

`IsDiffusiveStructure.chapmanEnskog` is the expansion `f = ρ - ε v · ∇ρ + O(ε²)` for `ε ∂ₜ f + T f =
ε⁻¹ (P f - f)` on an inner product space, with an initial layer and constants that do not see `‖T‖`.
`linearTransport_chapmanEnskog` and `linearTransport_rank_four` are the case of a grid in `x` and a
quadrature in `v`, in `d` and in three dimensions; `ceApprox_rank_le` is the count `d + 1`.
`linearTransport_rank_four_grid` runs on central differences on `(ℤ/N)³` with six velocities.
`Novel/EpsRank.lean` has the slab case in `distLR_flow_le`; the case of several space dimensions is
new.

## Integrators, Sec. 3.1, Table 1

Proved elsewhere and not repeated: first order, `ksl_global_error_le`, `bug_global_error_le`,
`rankAdaptiveBUG_global_error_le`, `parallelBUG_global_error`; midpoint BUG,
`IsMidpointBUGStep.local_error_le`, `midpointBUG_global_error`; Strang, for which the paper reports
no robust proof, `strangKSL_not_robust_second_order_rankTwo`. Second-order parallel BUG: the stage
and capture estimates are `P2608_27749.lemma3_Kstep`, `lemma4_Sstep`, `lemma5`; a global
second-order bound is not in the library, and it is left out here, since it is the subject of arXiv
2403.02834.

## Differences from the paper

* The rank-four claim is proved after discretizing `x` and `v`, since transport on a function space
  is not available, with constant cross section and no source (a constant `σ` is a rescaling). The
  constants are discrete `H⁴` norms of the data, uniform in the mesh when those are.
* "Rank" is the core separation rank `HasSepRankLE` over a semiring, Eq. (2) with `S` absorbed
  (`hasRankLEOver_of_core`). `P1804_04561a` and `P1801_01103a` use it over `ℝ`, `P1902_00424a`
  over `ℂ`, and it bounds the matrix rank on every grid (`HasRankLEOver.rank_sample_le`). The two
  false claims stay false over `ℂ` (`full_not_complex_rank_le_three`,
  `landauFull_not_complex_rank_le_two`).
* Eq. (31) and the displays after it print `exp ((v - u)²/2)`; `exp (-(v - u)²/2)` is meant, as in
  Sec. 2, and the normalization `(2π)^{-d/2}` of the expansion is dropped there.
* The Fokker–Planck operator is taken in the form `∇ᵥ · (v f + ∇ᵥ f)`, temperature one and no drift;
  the paper names no specific operator.
* The sign of the current in eq. (7) of [61] does not match its Gauss law. The witness of
  `linearized_rank_claim_false` has no charge and no current, so this does not matter.

## Core vocabulary

A `VelocityRule` gives a core quadrature `Kinetic.Quadrature` for every velocity component
(`VelocityRule.toQuadrature`: the same weights, of sum one, with the nodes `node l`). Its density
and its streaming operator are the core `Kinetic.density` and `Kinetic.streaming` of
`LeanDLRA/Kinetic/Defs.lean`: `VelocityRule.density_eq_kinetic`,
`VelocityRule.streaming_eq_kinetic`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix Gradient Laplacian

namespace LeanDLRA.Literature.P2412_05912

open LeanDLRA

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ### Separation rank over a ring, and sampling -/

section Rank

variable {X Y R : Type*}

/-- Eq. (2) of arXiv 2412.05912 as printed, with a core `S`, gives separation rank at most `r`:
absorbing `S` in `U` loses nothing. -/
theorem hasRankLEOver_of_core [CommSemiring R] {r : ℕ} (f : X → Y → R) (U : Fin r → X → R)
    (S : Fin r → Fin r → R) (V : Fin r → Y → R)
    (h : ∀ x y, f x y = ∑ i, ∑ j, U i x * S i j * V j y) : HasSepRankLE R f r := by
  refine ⟨fun j x => ∑ i, U i x * S i j, V, fun x y => ?_⟩
  rw [h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm

/-- The matrix of samples `f (x_i, y_j)`: what a grid stores. -/
def sample {ι κ : Type*} (f : X → Y → R) (xs : ι → X) (ys : κ → Y) : Matrix ι κ R :=
  Matrix.of fun i j => f (xs i) (ys j)

/-- Separation rank `≤ r` implies matrix rank `≤ r` on every grid (arXiv 2412.05912, Eq. (2)). -/
theorem HasRankLEOver.rank_sample_le [CommRing R] [StrongRankCondition R]
    {ι κ : Type*} [Finite ι] [Fintype κ]
    {f : X → Y → R} {r : ℕ} (h : HasSepRankLE R f r) (xs : ι → X) (ys : κ → Y) :
    (sample f xs ys).rank ≤ r :=
  h.rank_le xs ys

/-- A square sample of size `r + 1` with nonzero determinant excludes separation rank `≤ r`
(arXiv 2412.05912, Eq. (2)). -/
theorem not_hasRankLEOver_of_det_ne_zero {K : Type*} [Field K] {f : X → Y → K} {r : ℕ}
    (xs : Fin (r + 1) → X) (ys : Fin (r + 1) → Y) (hdet : (sample f xs ys).det ≠ 0) :
    ¬ HasSepRankLE K f r := by
  intro h
  have h1 := HasRankLEOver.rank_sample_le h xs ys
  have hu : IsUnit (sample f xs ys) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have h2 := Matrix.rank_of_isUnit (sample f xs ys) hu
  simp only [Fintype.card_fin] at h2
  omega

/-- For a real function, a nonzero real sample determinant also excludes complex separation rank
`≤ r`: the rank claims of arXiv 2412.05912, Sec. 2, can be read over `ℂ` without changing the
conclusions below, unlike the rank of the complex function of Eq. (3). -/
theorem not_hasRankLEOver_complex_of_det_ne_zero {f : X → Y → ℝ} {r : ℕ}
    (xs : Fin (r + 1) → X) (ys : Fin (r + 1) → Y) (hdet : (sample f xs ys).det ≠ 0) :
    ¬ HasSepRankLE ℂ (fun x y => ((f x y : ℝ) : ℂ)) r := by
  refine not_hasRankLEOver_of_det_ne_zero xs ys ?_
  have h : sample (fun x y => ((f x y : ℝ) : ℂ)) xs ys =
      Complex.ofRealHom.mapMatrix (sample f xs ys) := by
    ext i j
    simp [sample]
  rw [h, ← RingHom.map_det]
  simpa using hdet

end Rank

/-! ### Section 2: free streaming, Eq. (3) -/

section FreeStreaming

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The solution `f (t, x, v) = exp (i k · (x - v t)) exp (-v² / 2)` of Eq. (3) of arXiv 2412.05912,
for `x, v, k` in an arbitrary real inner product space. -/
noncomputable def freeStream (k : E) (t : ℝ) (x v : E) : ℂ :=
  Complex.exp (Complex.I * ((⟪k, x - t • v⟫ : ℝ) : ℂ)) * ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ)

/-- The second equality of Eq. (3) of arXiv 2412.05912:
`exp (i k · (x - v t)) exp (-v²/2) = exp (i k · x) exp (-i (k · v) t) exp (-v²/2)`. -/
theorem freeStream_eq_product (k : E) (t : ℝ) (x v : E) :
    freeStream k t x v = Complex.exp (Complex.I * ((⟪k, x⟫ : ℝ) : ℂ)) *
      (Complex.exp (-Complex.I * ((⟪k, v⟫ : ℝ) : ℂ) * (t : ℂ)) *
        ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ)) := by
  unfold freeStream
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [inner_sub_right, inner_smul_right]
  push_cast
  ring

/-- The initial value of Sec. 2 of arXiv 2412.05912: `f (0, x, v) = exp (i k · x) exp (-v²/2)`. -/
theorem freeStream_zero (k x v : E) :
    freeStream k 0 x v = Complex.exp (Complex.I * ((⟪k, x⟫ : ℝ) : ℂ)) *
      ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ) := by
  simp [freeStream]

/-- The time derivative of the solution of Eq. (3) of arXiv 2412.05912: `∂ₜ f = -i (k · v) f`. -/
theorem hasDerivAt_freeStream_time (k : E) (t : ℝ) (x v : E) :
    HasDerivAt (fun s => freeStream k s x v)
      (-(Complex.I * ((⟪k, v⟫ : ℝ) : ℂ)) * freeStream k t x v) t := by
  have h1 : HasDerivAt
      (fun s : ℝ => Complex.I * (((⟪k, x⟫ : ℝ) : ℂ) - (s : ℂ) * ((⟪k, v⟫ : ℝ) : ℂ)))
      (-(Complex.I * ((⟪k, v⟫ : ℝ) : ℂ))) t := by
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have := ((h0.mul_const ((⟪k, v⟫ : ℝ) : ℂ)).const_sub ((⟪k, x⟫ : ℝ) : ℂ)).const_mul Complex.I
    convert this using 1
    ring
  have h2 := (h1.cexp).mul_const ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ)
  have hfun : (fun s => freeStream k s x v) = fun s : ℝ =>
      Complex.exp (Complex.I * (((⟪k, x⟫ : ℝ) : ℂ) - (s : ℂ) * ((⟪k, v⟫ : ℝ) : ℂ))) *
        ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ) := by
    funext s
    simp only [freeStream, inner_sub_right, inner_smul_right]
    push_cast
    rfl
  rw [hfun]
  convert h2 using 1
  rw [congrFun hfun t]
  ring

/-- The space derivative of the solution of Eq. (3) of arXiv 2412.05912, in the direction `w`:
`w · ∇ₓ f = i (k · w) f`. -/
theorem fderiv_freeStream_space (k : E) (t : ℝ) (x v w : E) :
    fderiv ℝ (fun y => freeStream k t y v) x w =
      Complex.I * ((⟪k, w⟫ : ℝ) : ℂ) * freeStream k t x v := by
  have h0 : HasFDerivAt (fun y : E => ((⟪k, y - t • v⟫ : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (innerSL ℝ k)) x := by
    have h1 : HasFDerivAt (fun y : E => ⟪k, y - t • v⟫) (innerSL ℝ k) x := by
      have : (fun y : E => ⟪k, y - t • v⟫) = fun y => innerSL ℝ k y - ⟪k, t • v⟫ := by
        funext y
        simp [inner_sub_right]
      rw [this]
      exact (innerSL ℝ k).hasFDerivAt.sub_const _
    exact Complex.ofRealCLM.hasFDerivAt.comp x h1
  have h2 := ((h0.const_mul Complex.I).cexp).mul_const ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ)
  have h3 : (fun y => freeStream k t y v) = fun y =>
      Complex.exp (Complex.I * ((⟪k, y - t • v⟫ : ℝ) : ℂ)) *
        ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ) := rfl
  rw [h3, h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, freeStream]
  ring

/-- **Free streaming, the equation** (arXiv 2412.05912, Sec. 2): the function of Eq. (3) solves
`∂ₜ f + v · ∇ₓ f = 0`, in every dimension. `v · ∇ₓ f` is the directional derivative in `x` along
`v`, written `fderiv`. -/
theorem freeStream_transport (k : E) (t : ℝ) (x v : E) :
    deriv (fun s => freeStream k s x v) t + fderiv ℝ (fun y => freeStream k t y v) x v = 0 := by
  rw [(hasDerivAt_freeStream_time k t x v).deriv, fderiv_freeStream_space]
  ring

/-- Solutions of free transport are constant along characteristics, for values in any real normed
space, so `f (t, x, v) = f (0, x - t v, v)`. Differentiability is joint in `(t, x)`
(arXiv 2412.05912, Sec. 2). -/
theorem transport_eq_initial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E → E → F}
    (hf : ∀ v, Differentiable ℝ fun p : ℝ × E => f p.1 p.2 v)
    (hsol : ∀ t x v, deriv (fun s => f s x v) t + fderiv ℝ (fun y => f t y v) x v = 0)
    (t : ℝ) (x v : E) : f t x v = f 0 (x - t • v) v := by
  set G : ℝ × E → F := fun p => f p.1 p.2 v with hG
  have hline : ∀ s : ℝ,
      HasDerivAt (fun s => ((s, x + (s - t) • v) : ℝ × E)) ((1, v) : ℝ × E) s := by
    intro s
    refine (hasDerivAt_id s).prodMk ?_
    have h1 : HasDerivAt (fun s : ℝ => (s - t) • v) ((1 : ℝ) • v) s :=
      ((hasDerivAt_id s).sub_const t).smul_const v
    simpa using h1.const_add x
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s => f s (x + (s - t) • v) v) 0 s := by
    intro s
    have hd := (hf v (s, x + (s - t) • v)).hasFDerivAt
    have hc := hd.comp_hasDerivAt s (hline s)
    set D := fderiv ℝ G (s, x + (s - t) • v) with hD
    have h1 : HasDerivAt (fun r => f r (x + (s - t) • v) v) (D (1, 0)) s := by
      have hl : HasDerivAt (fun r : ℝ => ((r, x + (s - t) • v) : ℝ × E)) ((1, 0) : ℝ × E) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s _)
      exact hd.comp_hasDerivAt s hl
    have h2 : HasFDerivAt (fun y => f s y v) (D.comp (ContinuousLinearMap.inr ℝ ℝ E))
        (x + (s - t) • v) := by
      have hl : HasFDerivAt (fun y : E => ((s, y) : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E)
          (x + (s - t) • v) := by
        exact (hasFDerivAt_const s _).prodMk (hasFDerivAt_id _)
      exact hd.comp (x + (s - t) • v) hl
    have h0 := hsol s (x + (s - t) • v) v
    rw [h1.deriv, h2.fderiv] at h0
    have hsplit : ((1, v) : ℝ × E) = (1, 0) + (0, v) := by simp
    have hval : D (1, v) = 0 := by
      rw [hsplit, map_add]
      simpa using h0
    rw [hval] at hc
    exact hc
  have hconst : ∀ s, f s (x + (s - t) • v) v = f 0 (x + (0 - t) • v) v := by
    intro s
    have hdiff : Differentiable ℝ fun s => f s (x + (s - t) • v) v :=
      fun s => (hderiv s).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff (fun s => (hderiv s).deriv) s 0
  have := hconst t
  simp only [sub_self, zero_smul, add_zero, zero_sub, neg_smul] at this
  rw [this, sub_eq_add_neg]

/-- The function of Eq. (3) of arXiv 2412.05912 is jointly differentiable in `(t, x)`. -/
theorem differentiable_freeStream (k v : E) :
    Differentiable ℝ fun p : ℝ × E => freeStream k p.1 p.2 v := by
  unfold freeStream
  refine Differentiable.mul ?_ (differentiable_const _)
  refine Differentiable.cexp (Differentiable.const_mul ?_ _)
  refine Complex.ofRealCLM.differentiable.comp ?_
  exact (differentiable_const k).inner ℝ (differentiable_snd.sub (differentiable_fst.smul
    (differentiable_const v)))

/-- **Free streaming, uniqueness** (arXiv 2412.05912, Sec. 2, "we can immediately write down an
analytic solution"): Eq. (3) is the only solution of `∂ₜ f + v · ∇ₓ f = 0` with
`f (0, x, v) = exp (i k · x) exp (-v²/2)` among functions differentiable in `(t, x)`. -/
theorem freeStream_unique (k : E) {f : ℝ → E → E → ℂ}
    (hf : ∀ v, Differentiable ℝ fun p : ℝ × E => f p.1 p.2 v)
    (hsol : ∀ t x v, deriv (fun s => f s x v) t + fderiv ℝ (fun y => f t y v) x v = 0)
    (h0 : ∀ x v, f 0 x v = Complex.exp (Complex.I * ((⟪k, x⟫ : ℝ) : ℂ)) *
      ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ)) (t : ℝ) (x v : E) :
    f t x v = freeStream k t x v := by
  rw [transport_eq_initial hf hsol, h0, freeStream]

/-- **Free streaming, the rank** (arXiv 2412.05912, Sec. 2, "this is a rank-1 solution"): for every
`t`, the function of Eq. (3) has complex separation rank at most one, and not zero, with an `x`
factor that does not depend on `t` (Figure 1 of the paper). -/
theorem freeStream_rank_eq_one (k : E) (t : ℝ) :
    HasSepRankLE ℂ (freeStream k t) 1 ∧ ¬ HasSepRankLE ℂ (freeStream k t) 0 := by
  constructor
  · refine ⟨fun _ x => Complex.exp (Complex.I * ((⟪k, x⟫ : ℝ) : ℂ)), fun _ v =>
      Complex.exp (-Complex.I * ((⟪k, v⟫ : ℝ) : ℂ) * (t : ℂ)) *
        ((Real.exp (-‖v‖ ^ 2 / 2) : ℝ) : ℂ), fun x v => ?_⟩
    simpa using freeStream_eq_product k t x v
  · rintro ⟨U, V, h⟩
    have h1 := h 0 0
    simp [freeStream] at h1

/-- The function of Eq. (3) of arXiv 2412.05912 never vanishes. -/
theorem freeStream_ne_zero (k : E) (t : ℝ) (x v : E) : freeStream k t x v ≠ 0 := by
  unfold freeStream
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  exact_mod_cast (Real.exp_pos _).ne'

/-- **Free streaming on a grid** (arXiv 2412.05912, Sec. 2): on every nonempty grid in `x` and `v`
the sample matrix of Eq. (3) has complex rank exactly one, for every `t`. -/
theorem freeStream_sample_rank {ι κ : Type*} [Finite ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (k : E) (t : ℝ) (xs : ι → E) (vs : κ → E) :
    (sample (freeStream k t) xs vs).rank = 1 := by
  classical
  have := Fintype.ofFinite ι
  apply le_antisymm (HasRankLEOver.rank_sample_le (freeStream_rank_eq_one k t).1 xs vs)
  by_contra h
  have h0 : (sample (freeStream k t) xs vs).rank = 0 := by omega
  have h1 : (sample (freeStream k t) xs vs).mulVecLin = 0 :=
    LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨j⟩ := ‹Nonempty κ›
  have h2 := congrFun (LinearMap.congr_fun h1 (Pi.single j 1)) i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, LinearMap.zero_apply,
    Pi.zero_apply, Matrix.col_apply] at h2
  exact freeStream_ne_zero k t (xs i) (vs j) h2


/-- **Free streaming over the reals** (arXiv 2412.05912, Sec. 2, Eq. (3)): the rank one in Eq. (3)
is a complex rank. The real part `cos (k · (x - v t)) exp (-v²/2)` has real separation rank at most
two for every `t`. It equals `cos (k · x) cos ((k · v) t) e + sin (k · x) sin ((k · v) t) e`. -/
theorem freeStream_re_rank_le_two (k : E) (t : ℝ) :
    HasSepRankLE ℝ (fun x v => (freeStream k t x v).re) 2 := by
  refine ⟨![fun x => Real.cos ⟪k, x⟫, fun x => Real.sin ⟪k, x⟫],
    ![fun v => Real.cos (⟪k, v⟫ * t) * Real.exp (-‖v‖ ^ 2 / 2),
      fun v => Real.sin (⟪k, v⟫ * t) * Real.exp (-‖v‖ ^ 2 / 2)], fun x v => ?_⟩
  have h : (freeStream k t x v).re =
      Real.cos (⟪k, x⟫ - ⟪k, v⟫ * t) * Real.exp (-‖v‖ ^ 2 / 2) := by
    have e : ⟪k, x - t • v⟫ = ⟪k, x⟫ - ⟪k, v⟫ * t := by
      rw [inner_sub_right, inner_smul_right, mul_comm]
    unfold freeStream
    rw [Complex.re_mul_ofReal, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re, e]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, Real.cos_sub]
  ring

/-- The bound `2` of `freeStream_re_rank_le_two` is attained for `k ≠ 0`, `t ≠ 0`: over the reals,
the solution of Eq. (3) of arXiv 2412.05912 has rank exactly two. -/
theorem freeStream_re_not_rank_le_one {k : E} (hk : k ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    ¬ HasSepRankLE ℝ (fun x v => (freeStream k t x v).re) 1 := by
  have hk2 : ⟪k, k⟫ ≠ 0 := by simpa using hk
  set e : E := (⟪k, k⟫)⁻¹ • k with he
  have hke : ⟪k, e⟫ = 1 := by
    rw [he, inner_smul_right]
    field_simp
  set xs : Fin 2 → E := ![0, (Real.pi / 2) • e] with hxs
  set vs : Fin 2 → E := ![0, (t⁻¹ * (Real.pi / 2)) • e] with hvs
  have hval : ∀ x v : E, (freeStream k t x v).re =
      Real.cos (⟪k, x⟫ - ⟪k, v⟫ * t) * Real.exp (-‖v‖ ^ 2 / 2) := by
    intro x v
    have e : ⟪k, x - t • v⟫ = ⟪k, x⟫ - ⟪k, v⟫ * t := by
      rw [inner_sub_right, inner_smul_right, mul_comm]
    unfold freeStream
    rw [Complex.re_mul_ofReal, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re, e]
  refine not_hasRankLEOver_of_det_ne_zero xs vs ?_
  have h1 : ⟪k, (t⁻¹ * (Real.pi / 2)) • e⟫ * t = Real.pi / 2 := by
    rw [inner_smul_right, hke]
    field_simp
  have h2 : ⟪k, (Real.pi / 2) • e⟫ = Real.pi / 2 := by
    rw [inner_smul_right, hke, mul_one]
  rw [Matrix.det_fin_two]
  simp only [sample, Matrix.of_apply, hval, hxs, hvs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, inner_zero_right, zero_mul, sub_zero, h1, h2, sub_self, zero_sub,
    Real.cos_neg, Real.cos_pi_div_two, Real.cos_zero]
  simp

end FreeStreaming

/-! ### Section 2: free streaming on a grid, and the exactness of DLRA -/

section DiscreteFreeStreaming

variable {X V : Type*} [Fintype X] [Fintype V] [DecidableEq V] {d : ℕ}

/-- The semi-discrete transport field `F (Y) = -∑ₗ Dₗ Y diag(vₗ)`: `v · ∇ₓ` with an arbitrary
spatial discretization `Dₗ` of `∂_{xₗ}` and velocity nodes with components `vₗ`. -/
def transportField (D : Fin d → Matrix X X ℂ) (ν : Fin d → V → ℝ) (Y : Matrix X V ℂ) :
    Matrix X V ℂ :=
  -∑ l, D l * Y * Matrix.diagonal fun j => ((ν l j : ℝ) : ℂ)

/-- The low-rank solution `u (e^{-i (k · v_j) t} w_j)ᵀ` of the semi-discrete free streaming problem:
the left factor is fixed, as in Figure 1 of arXiv 2412.05912. -/
noncomputable def discreteStream (k : Fin d → ℝ) (ν : Fin d → V → ℝ) (u : X → ℂ) (w : V → ℂ)
    (t : ℝ) : Matrix X V ℂ :=
  Matrix.vecMulVec u fun j =>
    Complex.exp (-Complex.I * ((∑ l, k l * ν l j : ℝ) : ℂ) * (t : ℂ)) * w j

/-- The field of the semi-discrete free streaming problem on a plane wave: `u` is an eigenvector of
every `Dₗ` with eigenvalue `i kₗ`, as `e^{i k · x}` is for `∂_{xₗ}` (arXiv 2412.05912, Sec. 2). -/
theorem transportField_vecMulVec {D : Fin d → Matrix X X ℂ} {k : Fin d → ℝ} {ν : Fin d → V → ℝ}
    {u : X → ℂ} (hu : ∀ l, D l *ᵥ u = (Complex.I * ((k l : ℝ) : ℂ)) • u) (z : V → ℂ) :
    transportField D ν (Matrix.vecMulVec u z) =
      Matrix.vecMulVec u fun j => -(Complex.I * ((∑ l, k l * ν l j : ℝ) : ℂ)) * z j := by
  ext i j
  have h : ∀ l, (D l * Matrix.vecMulVec u z * Matrix.diagonal fun j => ((ν l j : ℝ) : ℂ)) i j =
      Complex.I * ((k l : ℝ) : ℂ) * u i * z j * ((ν l j : ℝ) : ℂ) := by
    intro l
    have h1 := congrFun (hu l) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : (D l * Matrix.vecMulVec u z) i j = Complex.I * ((k l : ℝ) : ℂ) * u i * z j := by
      rw [← h1, Matrix.mul_apply, Finset.sum_mul]
      simp only [Matrix.vecMulVec_apply]
      exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    rw [Matrix.mul_diagonal, h2]
  simp only [transportField, Matrix.neg_apply, Matrix.sum_apply, h, Matrix.vecMulVec_apply]
  push_cast
  rw [neg_mul, mul_neg, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)

/-- **Free streaming on a grid** (arXiv 2412.05912, Sec. 2): for every spatial discretization having
`u` as a plane wave and all velocity data `w`, the rank-one matrix `discreteStream` solves the
semi-discrete problem `Ẏ = F (Y)`, entry by entry. The paper's solution is the case
`w_j = exp (-v_j² / 2)` with `u` the samples of `exp (i k · x)` and spectral `Dₗ`. -/
theorem discreteStream_hasDerivAt {D : Fin d → Matrix X X ℂ} {k : Fin d → ℝ} {ν : Fin d → V → ℝ}
    {u : X → ℂ} (hu : ∀ l, D l *ᵥ u = (Complex.I * ((k l : ℝ) : ℂ)) • u) (w : V → ℂ) (t : ℝ)
    (i : X) (j : V) :
    HasDerivAt (fun s => discreteStream k ν u w s i j)
      (transportField D ν (discreteStream k ν u w t) i j) t := by
  have h0 : HasDerivAt (fun s : ℝ => -Complex.I * ((∑ l, k l * ν l j : ℝ) : ℂ) * (s : ℂ))
      (-Complex.I * ((∑ l, k l * ν l j : ℝ) : ℂ)) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
      (-Complex.I * ((∑ l, k l * ν l j : ℝ) : ℂ))
  have h1 := ((h0.cexp).mul_const (w j)).const_mul (u i)
  simp only [discreteStream, Matrix.vecMulVec_apply, transportField_vecMulVec hu]
  convert h1 using 1
  ring

/-- The solution of `discreteStream_hasDerivAt` has rank at most one for all `t` (arXiv 2412.05912,
Sec. 2). -/
theorem discreteStream_rank_le [DecidableEq X] (k : Fin d → ℝ) (ν : Fin d → V → ℝ) (u : X → ℂ)
    (w : V → ℂ) (t : ℝ) : (discreteStream k ν u w t).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le _ _

/-- **DLRA is exact for free streaming, `ε = 0`** (arXiv 2412.05912, Sec. 2, in the sense of the
exactness theorems): at every point `Y = u zᵀ` of the rank-one family with fixed unit vector `u`,
the field has no component outside the left space, `(I - u uᴴ) F (Y) = 0`, so its normal component
`(I - u uᴴ) F (Y) (I - R)` vanishes for every right projector `R`: the modelling error of the
robust error bounds is zero along the solution. Stated with Hermitian projectors, over `ℂ`. -/
theorem transportField_normal_eq_zero [DecidableEq X] {D : Fin d → Matrix X X ℂ} {k : Fin d → ℝ}
    {ν : Fin d → V → ℝ} {u : X → ℂ} (hu : ∀ l, D l *ᵥ u = (Complex.I * ((k l : ℝ) : ℂ)) • u)
    (hnorm : star u ⬝ᵥ u = 1) (z : V → ℂ) (R : Matrix V V ℂ) :
    (1 - Matrix.vecMulVec u (star u)) * transportField D ν (Matrix.vecMulVec u z) = 0 ∧
    (1 - Matrix.vecMulVec u (star u)) * transportField D ν (Matrix.vecMulVec u z) * (1 - R) =
      0 := by
  have h : (1 - Matrix.vecMulVec u (star u)) * transportField D ν (Matrix.vecMulVec u z) = 0 := by
    rw [transportField_vecMulVec hu, Matrix.sub_mul, Matrix.one_mul,
      Matrix.vecMulVec_mul_vecMulVec, hnorm]
    simp
  exact ⟨h, by rw [h, Matrix.zero_mul]⟩

end DiscreteFreeStreaming

/-! ### Section 6.3: `f = g²` and first order operators -/

section Vlasov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Vlasov operator `∂ₜ f + v · ∇ₓ f + A · ∇ᵥ f`, with a force field `A (t, x, v)` and phase
space `E × E`. The Vlasov–Maxwell equation of Sec. 2 of arXiv 2412.05912 has
`A = -(E + v × B)`. -/
noncomputable def vlasovOp (A : ℝ → E → E → E) (f : ℝ → E → E → ℝ) (t : ℝ) (x v : E) : ℝ :=
  deriv (fun s => f s x v) t + fderiv ℝ (fun y => f t y v) x v +
    fderiv ℝ (fun w => f t x w) v (A t x v)

/-- A first order operator obeys the chain rule: `L (φ ∘ g) = φ' (g) L g`. This is why, as Sec. 6.3
of arXiv 2412.05912 says, the transformation works for "very specific first-order differential
operators", and why "different transformations are possible as well". -/
theorem vlasovOp_comp (A : ℝ → E → E → E) {g : ℝ → E → E → ℝ} {φ : ℝ → ℝ} {t : ℝ} {x v : E}
    (hφ : DifferentiableAt ℝ φ (g t x v))
    (h1 : DifferentiableAt ℝ (fun s => g s x v) t)
    (h2 : DifferentiableAt ℝ (fun y => g t y v) x)
    (h3 : DifferentiableAt ℝ (fun w => g t x w) v) :
    vlasovOp A (fun s y w => φ (g s y w)) t x v = deriv φ (g t x v) * vlasovOp A g t x v := by
  have e1 : deriv (fun s => φ (g s x v)) t = deriv φ (g t x v) * deriv (fun s => g s x v) t :=
    (hφ.hasDerivAt.comp t h1.hasDerivAt).deriv
  have e2 : fderiv ℝ (fun y => φ (g t y v)) x =
      deriv φ (g t x v) • fderiv ℝ (fun y => g t y v) x :=
    (hφ.hasDerivAt.comp_hasFDerivAt x h2.hasFDerivAt).fderiv
  have e3 : fderiv ℝ (fun w => φ (g t x w)) v =
      deriv φ (g t x v) • fderiv ℝ (fun w => g t x w) v :=
    (hφ.hasDerivAt.comp_hasFDerivAt v h3.hasFDerivAt).fderiv
  simp only [vlasovOp, e1, e2, e3, smul_apply, smul_eq_mul]
  ring

/-- **`f = g²`, the identity** (arXiv 2412.05912, Sec. 6.3): `L (g²) = 2 g L g` for the Vlasov
operator `L`. -/
theorem vlasovOp_sq (A : ℝ → E → E → E) {g : ℝ → E → E → ℝ} {t : ℝ} {x v : E}
    (h1 : DifferentiableAt ℝ (fun s => g s x v) t)
    (h2 : DifferentiableAt ℝ (fun y => g t y v) x)
    (h3 : DifferentiableAt ℝ (fun w => g t x w) v) :
    vlasovOp A (fun s y w => g s y w ^ 2) t x v = 2 * g t x v * vlasovOp A g t x v := by
  have := vlasovOp_comp A (φ := fun s => s ^ 2) (differentiableAt_pow 2) h1 h2 h3
  simpa using this

/-- The operator of `vlasovOp` is the derivative along `(1, v, A)` of the function on phase space
and time (arXiv 2412.05912, Sec. 6.3). -/
theorem vlasovOp_eq_fderiv (A : ℝ → E → E → E) {g : ℝ → E → E → ℝ} {t : ℝ} {x v : E}
    (hg : DifferentiableAt ℝ (fun p : ℝ × E × E => g p.1 p.2.1 p.2.2) (t, x, v)) :
    vlasovOp A g t x v =
      fderiv ℝ (fun p : ℝ × E × E => g p.1 p.2.1 p.2.2) (t, x, v) (1, v, A t x v) := by
  set G : ℝ × E × E → ℝ := fun p => g p.1 p.2.1 p.2.2 with hG
  set D := fderiv ℝ G (t, x, v) with hD
  have hd : HasFDerivAt G D (t, x, v) := hg.hasFDerivAt
  have h1 : HasDerivAt (fun s => g s x v) (D (1, 0, 0)) t := by
    have hl : HasDerivAt (fun s : ℝ => ((s, x, v) : ℝ × E × E)) ((1, 0, 0) : ℝ × E × E) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t (x, v))
    exact hd.comp_hasDerivAt t hl
  have h2 : HasFDerivAt (fun y => g t y v)
      (D.comp ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inl ℝ E E))) x := by
    have hl : HasFDerivAt (fun y : E => ((t, y, v) : ℝ × E × E))
        ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inl ℝ E E)) x :=
      (hasFDerivAt_prodMk_right t (x, v)).comp x (hasFDerivAt_prodMk_left x v)
    exact hd.comp x hl
  have h3 : HasFDerivAt (fun w => g t x w)
      (D.comp ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inr ℝ E E))) v := by
    have hl : HasFDerivAt (fun w : E => ((t, x, w) : ℝ × E × E))
        ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inr ℝ E E)) v :=
      (hasFDerivAt_prodMk_right t (x, v)).comp v (hasFDerivAt_prodMk_right x v)
    exact hd.comp v hl
  have hsplit : ((1, v, A t x v) : ℝ × E × E) = (1, 0, 0) + (0, v, 0) + (0, 0, A t x v) := by
    simp
  rw [vlasovOp, h1.deriv, h2.fderiv, h3.fderiv, hsplit, map_add, map_add]
  simp

/-- **`f = g²` for Vlasov** (arXiv 2412.05912, Sec. 6.3, "It can be easily checked that `g`
satisfies a Vlasov equation if `f` does"): for `g ∈ C¹` and a continuous force, `g²` solves the
Vlasov equation if and only if `g` does. `g` may change sign and vanish; at a zero of `g` the
identity `L (g²) = 2 g L g` says nothing, and the implication comes from continuity of `L g`. -/
theorem vlasov_sq_iff {A : ℝ → E → E → E} {g : ℝ → E → E → ℝ}
    (hg : ContDiff ℝ 1 fun p : ℝ × E × E => g p.1 p.2.1 p.2.2)
    (hA : Continuous fun p : ℝ × E × E => A p.1 p.2.1 p.2.2) :
    (∀ t x v, vlasovOp A (fun s y w => g s y w ^ 2) t x v = 0) ↔
      ∀ t x v, vlasovOp A g t x v = 0 := by
  set G : ℝ × E × E → ℝ := fun p => g p.1 p.2.1 p.2.2 with hG
  have hd : Differentiable ℝ G := hg.differentiable (by norm_num)
  have hslices : ∀ t x v, DifferentiableAt ℝ (fun s => g s x v) t ∧
      DifferentiableAt ℝ (fun y => g t y v) x ∧ DifferentiableAt ℝ (fun w => g t x w) v := by
    intro t x v
    refine ⟨?_, ?_, ?_⟩
    · have hl : DifferentiableAt ℝ (fun s : ℝ => ((s, x, v) : ℝ × E × E)) t := by fun_prop
      change DifferentiableAt ℝ (G ∘ fun s : ℝ => ((s, x, v) : ℝ × E × E)) t
      exact (hd (t, x, v)).comp t hl
    · have hl : DifferentiableAt ℝ (fun y : E => ((t, y, v) : ℝ × E × E)) x := by fun_prop
      change DifferentiableAt ℝ (G ∘ fun y : E => ((t, y, v) : ℝ × E × E)) x
      exact (hd (t, x, v)).comp x hl
    · have hl : DifferentiableAt ℝ (fun w : E => ((t, x, w) : ℝ × E × E)) v := by fun_prop
      change DifferentiableAt ℝ (G ∘ fun w : E => ((t, x, w) : ℝ × E × E)) v
      exact (hd (t, x, v)).comp v hl
  have hid : ∀ t x v, vlasovOp A (fun s y w => g s y w ^ 2) t x v =
      2 * g t x v * vlasovOp A g t x v := fun t x v =>
    vlasovOp_sq A (hslices t x v).1 (hslices t x v).2.1 (hslices t x v).2.2
  constructor
  · intro h t x v
    set R : ℝ × E × E → ℝ := fun p => fderiv ℝ G p (1, p.2.2, A p.1 p.2.1 p.2.2) with hR
    have hRc : Continuous R := by
      have h1 : Continuous (fderiv ℝ G) := hg.continuous_fderiv (by norm_num)
      exact h1.clm_apply (continuous_const.prodMk (continuous_snd.snd.prodMk hA))
    have hRval : ∀ p : ℝ × E × E, vlasovOp A g p.1 p.2.1 p.2.2 = R p := fun p =>
      vlasovOp_eq_fderiv A (hd p)
    by_contra hne
    have hne' : R (t, x, v) ≠ 0 := by
      have := hRval (t, x, v)
      simpa [this] using hne
    have hev : ∀ᶠ q in 𝓝 ((t, x, v) : ℝ × E × E), R q ≠ 0 :=
      hRc.continuousAt.eventually_ne hne'
    have hzero : G =ᶠ[𝓝 ((t, x, v) : ℝ × E × E)] fun _ => 0 := by
      filter_upwards [hev] with q hq
      have h1 := h q.1 q.2.1 q.2.2
      rw [hid, hRval q] at h1
      have h2 : G q = 0 := by
        rcases mul_eq_zero.1 h1 with h3 | h3
        · simpa [hG] using h3
        · exact absurd h3 hq
      exact h2
    have hfd : fderiv ℝ G (t, x, v) = 0 := by
      rw [hzero.fderiv_eq]
      simp
    exact hne' (by simp [hR, hfd])
  · intro h t x v
    rw [hid, h, mul_zero]

/-- **`f = g²` for Vlasov, forward direction** (arXiv 2412.05912, Sec. 6.3): if `g` solves the
Vlasov equation, then `f = g²` solves it too, and `f ≥ 0`. Only differentiability of the slices of
`g` is needed. -/
theorem vlasov_sq_of_solves {A : ℝ → E → E → E} {g : ℝ → E → E → ℝ}
    (h1 : ∀ t x v, DifferentiableAt ℝ (fun s => g s x v) t)
    (h2 : ∀ t x v, DifferentiableAt ℝ (fun y => g t y v) x)
    (h3 : ∀ t x v, DifferentiableAt ℝ (fun w => g t x w) v)
    (hsol : ∀ t x v, vlasovOp A g t x v = 0) :
    (∀ t x v, vlasovOp A (fun s y w => g s y w ^ 2) t x v = 0) ∧ ∀ t x v, 0 ≤ g t x v ^ 2 := by
  refine ⟨fun t x v => ?_, fun _ _ _ => sq_nonneg _⟩
  rw [vlasovOp_sq A (h1 t x v) (h2 t x v) (h3 t x v), hsol, mul_zero]

/-- **The auxiliary quantity** (arXiv 2412.05912, Sec. 6.3): if `f > 0` solves the Vlasov equation,
then `g = √f` solves it too, for an arbitrary force, without continuity. -/
theorem vlasov_sqrt_of_solves {A : ℝ → E → E → E} {f : ℝ → E → E → ℝ}
    (hpos : ∀ t x v, 0 < f t x v)
    (h1 : ∀ t x v, DifferentiableAt ℝ (fun s => f s x v) t)
    (h2 : ∀ t x v, DifferentiableAt ℝ (fun y => f t y v) x)
    (h3 : ∀ t x v, DifferentiableAt ℝ (fun w => f t x w) v)
    (hsol : ∀ t x v, vlasovOp A f t x v = 0) (t : ℝ) (x v : E) :
    vlasovOp A (fun s y w => √(f s y w)) t x v = 0 := by
  rw [vlasovOp_comp A (Real.hasDerivAt_sqrt (hpos t x v).ne').differentiableAt (h1 t x v) (h2 t x v)
    (h3 t x v), hsol, mul_zero]

/-- **Self-consistent Vlasov** (arXiv 2412.05912, Sec. 6.3, for Vlasov–Maxwell, where the force
depends on `f`): if `𝒜` maps a distribution to its force, then for `f = g²`, `g` solves the Vlasov
equation with force `𝒜 (g²)` if and only if `f` solves the nonlinear equation with force `𝒜 f`. -/
theorem vlasov_selfConsistent_iff {𝒜 : (ℝ → E → E → ℝ) → ℝ → E → E → E} {g : ℝ → E → E → ℝ}
    (hg : ContDiff ℝ 1 fun p : ℝ × E × E => g p.1 p.2.1 p.2.2)
    (hA : Continuous fun p : ℝ × E × E =>
      𝒜 (fun s y w => g s y w ^ 2) p.1 p.2.1 p.2.2) :
    (∀ t x v, vlasovOp (𝒜 fun s y w => g s y w ^ 2) (fun s y w => g s y w ^ 2) t x v = 0) ↔
      ∀ t x v, vlasovOp (𝒜 fun s y w => g s y w ^ 2) g t x v = 0 :=
  vlasov_sq_iff hg hA

end Vlasov

/-! ### Section 6.3: the failure for second order operators -/

section Diffusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hessian of a composition, in one direction (arXiv 2412.05912, Sec. 6.3). -/
theorem fderiv_fderiv_comp_apply {φ : ℝ → ℝ} {g : E → ℝ} {x : E} (hφ : ContDiff ℝ 2 φ)
    (hg : ContDiffAt ℝ 2 g x) (w : E) :
    fderiv ℝ (fderiv ℝ fun y => φ (g y)) x w w =
      deriv φ (g x) * fderiv ℝ (fderiv ℝ g) x w w + deriv (deriv φ) (g x) * fderiv ℝ g x w ^ 2 := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have e : fderiv ℝ (fun y => φ (g y)) =ᶠ[𝓝 x] fun y => deriv φ (g y) • fderiv ℝ g y := by
    filter_upwards [hev] with y hy
    exact ((hφd (g y)).hasDerivAt.comp_hasFDerivAt y hy.hasFDerivAt).fderiv
  have hdφ : Differentiable ℝ (deriv φ) := by
    have h1 : ContDiff ℝ 1 (deriv φ) := by
      have : ContDiff ℝ (1 + 1) φ := by simpa [one_add_one_eq_two] using hφ
      exact (contDiff_succ_iff_deriv (n := 1).1 this).2.2
    exact h1.differentiable (by norm_num)
  have h1 : HasFDerivAt (fun y => deriv φ (g y)) (deriv (deriv φ) (g x) • fderiv ℝ g x) x :=
    (hdφ (g x)).hasDerivAt.comp_hasFDerivAt x hgd.hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x := by
    have h3 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
    exact (h3.differentiableAt (by norm_num)).hasFDerivAt
  have h3 : HasFDerivAt (fun y => deriv φ (g y) • fderiv ℝ g y) _ x := h1.smul h2
  rw [e.fderiv_eq, h3.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  ring

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The chain rule for the Laplacian: `Δ (φ ∘ g) = φ' (g) Δ g + φ'' (g) |∇ g|²`. The term with `φ''`
is what first order operators do not have (arXiv 2412.05912, Sec. 6.3). -/
theorem laplacian_comp {φ : ℝ → ℝ} {g : E → ℝ} {x : E} (hφ : ContDiff ℝ 2 φ)
    (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y => φ (g y)) x =
      deriv φ (g x) * Δ g x + deriv (deriv φ) (g x) * ‖∇ g x‖ ^ 2 := by
  classical
  set b := stdOrthonormalBasis ℝ E with hb
  have hsq : ∑ i, fderiv ℝ g x (b i) ^ 2 = ‖∇ g x‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (∇ g x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, ← inner_gradient_left (𝕜 := ℝ), real_inner_comm]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, Finset.mul_sum, ← hsq,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact fderiv_fderiv_comp_apply hφ hg _

/-- `s ↦ s²` as a `C²` function, with its derivatives. -/
private lemma deriv_sq_fun : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
  funext s
  simp

private lemma deriv_deriv_sq_fun (s : ℝ) : deriv (deriv fun s : ℝ => s ^ 2) s = 2 := by
  rw [deriv_sq_fun]
  simp

/-- `Δ (g²) = 2 g Δ g + 2 |∇ g|²` (arXiv 2412.05912, Sec. 6.3). -/
theorem laplacian_sq {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y => g y ^ 2) x = 2 * g x * Δ g x + 2 * ‖∇ g x‖ ^ 2 := by
  have h := laplacian_comp (φ := fun s => s ^ 2) (contDiff_id.pow 2) hg
  rw [deriv_deriv_sq_fun, deriv_sq_fun] at h
  exact h

/-- The heat operator `∂ₜ g - Δ g`. -/
noncomputable def heatOp (g : ℝ → E → ℝ) (t : ℝ) (x : E) : ℝ :=
  deriv (fun s => g s x) t - Δ (g t) x

/-- **`f = g²` fails for diffusion, the identity** (arXiv 2412.05912, Sec. 6.3):
`(∂ₜ - Δ) g² = 2 g (∂ₜ - Δ) g - 2 |∇ g|²`, in every finite dimension. -/
theorem heatOp_sq {g : ℝ → E → ℝ} {t : ℝ} {x : E}
    (ht : DifferentiableAt ℝ (fun s => g s x) t) (hx : ContDiffAt ℝ 2 (g t) x) :
    heatOp (fun s y => g s y ^ 2) t x = 2 * g t x * heatOp g t x - 2 * ‖∇ (g t) x‖ ^ 2 := by
  have e1 : deriv (fun s => g s x ^ 2) t = 2 * g t x * deriv (fun s => g s x) t := by
    have h := (ht.hasDerivAt.fun_pow 2).deriv
    simpa using h
  have e2 := laplacian_sq hx
  simp only [heatOp]
  rw [e1]
  change _ - Δ (fun y => g t y ^ 2) x = _
  rw [e2]
  ring

/-- **`f = g²` fails for diffusion** (arXiv 2412.05912, Sec. 6.3, "can not be extended to ... the
heat equation"): the only functions `g`, `C²` in `x` and differentiable in `t`, such that `g` and
`g²` both solve the heat equation on `ℝ × E` are the constants. -/
theorem heat_sq_iff_const {g : ℝ → E → ℝ} (hx : ∀ t, ContDiff ℝ 2 (g t))
    (ht : ∀ x, Differentiable ℝ fun s => g s x) :
    ((∀ t x, heatOp g t x = 0) ∧ ∀ t x, heatOp (fun s y => g s y ^ 2) t x = 0) ↔
      ∃ c, ∀ t x, g t x = c := by
  constructor
  · rintro ⟨h1, h2⟩
    have hgrad : ∀ t x, fderiv ℝ (g t) x = 0 := by
      intro t x
      have h3 := h2 t x
      rw [heatOp_sq (ht x t) (hx t).contDiffAt, h1, mul_zero] at h3
      have h4 : ‖∇ (g t) x‖ = 0 := by nlinarith [norm_nonneg (∇ (g t) x)]
      have h5 : ∇ (g t) x = 0 := norm_eq_zero.1 h4
      ext w
      rw [← inner_gradient_left (𝕜 := ℝ), h5, inner_zero_left]
      simp
    have hdx : ∀ t, Differentiable ℝ (g t) := fun t => (hx t).differentiable (by norm_num)
    have hconstx : ∀ t x, g t x = g t 0 := fun t x =>
      is_const_of_fderiv_eq_zero (hdx t) (hgrad t) x 0
    have hlap : ∀ t x, Δ (g t) x = 0 := by
      intro t x
      have : g t = fun _ => g t 0 := funext (hconstx t)
      rw [this]
      simp
    have hderiv : ∀ t, deriv (fun s => g s 0) t = 0 := by
      intro t
      have h3 := h1 t 0
      rw [heatOp, hlap, sub_zero] at h3
      exact h3
    refine ⟨g 0 0, fun t x => ?_⟩
    rw [hconstx t x]
    exact is_const_of_deriv_eq_zero (ht 0) hderiv t 0
  · rintro ⟨c, hc⟩
    have hg : ∀ t, g t = fun _ => c := fun t => funext (hc t)
    have hg2 : ∀ t y, g t y ^ 2 = c ^ 2 := fun t y => by rw [hc]
    have hs : ∀ x, (fun s => g s x) = fun _ => c := fun x => funext fun s => hc s x
    constructor
    · intro t x
      simp [heatOp, hg]
    · intro t x
      simp only [heatOp, hg2]
      simp

/-- The second derivative of `y ↦ exp (a y + c)` on `ℝ`. -/
private lemma laplacian_exp_affine (a c x : ℝ) :
    Δ (fun y : ℝ => Real.exp (a * y + c)) x = a ^ 2 * Real.exp (a * x + c) := by
  have h1 : ∀ y, HasDerivAt (fun y : ℝ => Real.exp (a * y + c)) (Real.exp (a * y + c) * a) y := by
    intro y
    have : HasDerivAt (fun y : ℝ => a * y + c) a y := by
      simpa using ((hasDerivAt_id y).const_mul a).add_const c
    exact this.exp
  have h2 : deriv (fun y : ℝ => Real.exp (a * y + c)) = fun y => Real.exp (a * y + c) * a :=
    funext fun y => (h1 y).deriv
  rw [InnerProductSpace.laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one, h2,
    ((h1 x).mul_const a).deriv]
  ring

/-- **Square roots of heat solutions** (arXiv 2412.05912, Sec. 6.3, "can not be extended to ... the
heat equation"): `f = e^{t + x} > 0` solves the heat equation on `ℝ × ℝ`, and `g = √f` does not, so
`g` does not inherit the equation from `f` as it does for Vlasov (`vlasov_sqrt_of_solves`). -/
theorem heat_sqrt_counterexample :
    ∃ f : ℝ → ℝ → ℝ, (∀ t x, 0 < f t x) ∧ (∀ t x, heatOp f t x = 0) ∧
      ¬ ∀ t x, heatOp (fun s y => √(f s y)) t x = 0 := by
  refine ⟨fun t x => Real.exp (t + x), fun _ _ => Real.exp_pos _, fun t x => ?_, fun h => ?_⟩
  · have h1 : HasDerivAt (fun s : ℝ => Real.exp (s + x)) (Real.exp (t + x)) t := by
      simpa using ((hasDerivAt_id t).add_const x).exp
    have h2 : (fun y : ℝ => Real.exp (t + y)) = fun y => Real.exp (1 * y + t) := by
      funext y
      rw [one_mul, add_comm]
    simp only [heatOp]
    rw [h1.deriv, h2, laplacian_exp_affine]
    rw [one_mul, add_comm x t]
    ring
  · have h0 := h 0 0
    have hg : ∀ s y : ℝ, √(Real.exp (s + y)) = Real.exp ((s + y) / 2) := fun s y =>
      (Real.exp_half _).symm
    simp only [heatOp, hg] at h0
    have h1 : HasDerivAt (fun s : ℝ => Real.exp ((s + 0) / 2)) (Real.exp ((0 + 0) / 2) * (1 / 2))
        0 := by
      have : HasDerivAt (fun s : ℝ => (s + 0) / 2) (1 / 2) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).add_const (0 : ℝ)).div_const 2
      exact this.exp
    have h2 : (fun y : ℝ => Real.exp ((0 + y) / 2)) = fun y => Real.exp ((1 / 2) * y + 0) := by
      funext y
      congr 1
      ring
    rw [h1.deriv, h2, laplacian_exp_affine] at h0
    norm_num at h0

/-- `‖·‖²`: its gradient. -/
private lemma hasFDerivAt_normSq (x : E) :
    HasFDerivAt (fun v : E => ‖v‖ ^ 2) (2 • innerSL ℝ x) x := by
  simpa using (hasFDerivAt_id x).norm_sq

private lemma gradient_normSq (x : E) : ∇ (fun v : E => ‖v‖ ^ 2) x = (2 : ℝ) • x := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient_left (𝕜 := ℝ), (hasFDerivAt_normSq x).fderiv, inner_smul_left]
  simp

/-- `Δ ‖v‖² = 2 d` (arXiv 2412.05912, Sec. 6.3, used for the Fokker–Planck equilibrium). -/
theorem laplacian_normSq (x : E) :
    Δ (fun v : E => ‖v‖ ^ 2) x = 2 * Module.finrank ℝ E := by
  classical
  set b := stdOrthonormalBasis ℝ E with hb
  have hf : fderiv ℝ (fun v : E => ‖v‖ ^ 2) = fun x => 2 • innerSL ℝ x :=
    funext fun x => (hasFDerivAt_normSq x).fderiv
  have hd : HasFDerivAt (fun x : E => (2 : ℕ) • innerSL ℝ x) ((2 : ℕ) • innerSL ℝ) x :=
    ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt).const_smul (2 : ℕ)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, ← hb]
  have h1 : ∀ i, iteratedFDeriv ℝ 2 (fun v : E => ‖v‖ ^ 2) x ![b i, b i] = 2 := by
    intro i
    have h2 : ⟪b i, b i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
      norm_num
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hf, hd.fderiv]
    have h3 : innerSL ℝ (b i) (b i) = 1 := h2
    simp [h3]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The Fokker–Planck collision operator `∇ᵥ · (v f + ∇ᵥ f) = Δ f + v · ∇ f + d f`. -/
noncomputable def fpOp (f : E → ℝ) (v : E) : ℝ :=
  Δ f v + ⟪v, ∇ f v⟫ + Module.finrank ℝ E * f v

/-- **`f = g²` fails for Fokker–Planck, the identity** (arXiv 2412.05912, Sec. 6.3):
`Q (g²) = 2 g (Δ g + v · ∇ g + (d/2) g) + 2 |∇ g|²`. The last term is the obstruction, as for the
heat equation. -/
theorem fpOp_sq {g : E → ℝ} {v : E} (hg : ContDiffAt ℝ 2 g v) :
    fpOp (fun y => g y ^ 2) v =
      2 * g v * (Δ g v + ⟪v, ∇ g v⟫ + Module.finrank ℝ E / 2 * g v) + 2 * ‖∇ g v‖ ^ 2 := by
  have hgd : DifferentiableAt ℝ g v := hg.differentiableAt (by norm_num)
  have e : ⟪v, ∇ (fun y => g y ^ 2) v⟫ = 2 * g v * ⟪v, ∇ g v⟫ := by
    have h1 : HasFDerivAt (fun y => g y ^ 2) ((2 * g v) • fderiv ℝ g v) v := by
      have h0 := (hasDerivAt_pow 2 (g v)).comp_hasFDerivAt v hgd.hasFDerivAt
      have e : ((2 : ℕ) : ℝ) * g v ^ (2 - 1) = 2 * g v := by norm_num
      rw [e] at h0
      exact h0
    have a : ∀ h : E → ℝ, ⟪v, ∇ h v⟫ = fderiv ℝ h v v := fun h => by
      rw [real_inner_comm, inner_gradient_left (𝕜 := ℝ)]
    rw [a, a, h1.fderiv]
    simp
  simp only [fpOp]
  rw [laplacian_sq hg, e]
  ring

/-- The time-dependent form of `fpOp_sq`: for `∂ₜ f = Q f`, with `Q` the Fokker–Planck operator and
`f = g²`, `(∂ₜ - Q) g² = 2 g (∂ₜ g - Δ g - v · ∇ g - (d/2) g) - 2 |∇ g|²`. So if `g` solves the
equation that makes the first term vanish, `f` solves Fokker–Planck iff `∇ g = 0` everywhere
(arXiv 2412.05912, Sec. 6.3). -/
theorem fp_sq_iff {g : ℝ → E → ℝ} (hx : ∀ t, ContDiff ℝ 2 (g t))
    (ht : ∀ t x, DifferentiableAt ℝ (fun s => g s x) t)
    (hg : ∀ t v, deriv (fun s => g s v) t =
      Δ (g t) v + ⟪v, ∇ (g t) v⟫ + Module.finrank ℝ E / 2 * g t v) :
    (∀ t v, deriv (fun s => g s v ^ 2) t = fpOp (fun y => g t y ^ 2) v) ↔
      ∀ t v, ∇ (g t) v = 0 := by
  have key : ∀ t v, deriv (fun s => g s v ^ 2) t - fpOp (fun y => g t y ^ 2) v =
      -(2 * ‖∇ (g t) v‖ ^ 2) := by
    intro t v
    have e1 : deriv (fun s => g s v ^ 2) t = 2 * g t v * deriv (fun s => g s v) t := by
      have h := ((ht t v).hasDerivAt.fun_pow 2).deriv
      simpa using h
    rw [fpOp_sq (hx t).contDiffAt, e1, hg]
    ring
  constructor
  · intro h t v
    have h1 := key t v
    rw [h t v, sub_self] at h1
    have h2 : ‖∇ (g t) v‖ = 0 := by nlinarith [norm_nonneg (∇ (g t) v)]
    exact norm_eq_zero.1 h2
  · intro h t v
    have h1 := key t v
    rw [h, norm_zero] at h1
    linarith

/-- The Gaussian `e^{-c |v|²}` under the Fokker–Planck operator (arXiv 2412.05912, Sec. 6.3). -/
theorem fpOp_gaussian (c : ℝ) (v : E) :
    fpOp (fun y : E => Real.exp (-c * ‖y‖ ^ 2)) v =
      Real.exp (-c * ‖v‖ ^ 2) *
        (Module.finrank ℝ E * (1 - 2 * c) + (4 * c ^ 2 - 2 * c) * ‖v‖ ^ 2) := by
  have hq : ContDiffAt ℝ 2 (fun y : E => ‖y‖ ^ 2) v := (contDiff_norm_sq ℝ).contDiffAt
  have hφ : ContDiff ℝ 2 (fun s : ℝ => Real.exp (-c * s)) := by fun_prop
  have hd1 : deriv (fun s : ℝ => Real.exp (-c * s)) = fun s => Real.exp (-c * s) * -c := by
    funext s
    have : HasDerivAt (fun s : ℝ => -c * s) (-c) s := by
      simpa using (hasDerivAt_id s).const_mul (-c)
    exact this.exp.deriv
  have hd2 : ∀ s, deriv (deriv fun s : ℝ => Real.exp (-c * s)) s =
      Real.exp (-c * s) * -c * -c := by
    intro s
    rw [hd1]
    have : HasDerivAt (fun s : ℝ => -c * s) (-c) s := by
      simpa using (hasDerivAt_id s).const_mul (-c)
    exact (this.exp.mul_const (-c)).deriv
  have hl := laplacian_comp hφ hq
  rw [laplacian_normSq, gradient_normSq, hd2, hd1, norm_smul] at hl
  beta_reduce at hl
  have hin : ⟪v, ∇ (fun y : E => Real.exp (-c * ‖y‖ ^ 2)) v⟫ =
      Real.exp (-c * ‖v‖ ^ 2) * (-c * (2 * ‖v‖ ^ 2)) := by
    have h1 : HasFDerivAt (fun y : E => Real.exp (-c * ‖y‖ ^ 2))
        (Real.exp (-c * ‖v‖ ^ 2) • (-c • (2 • innerSL ℝ v))) v :=
      ((hasFDerivAt_normSq v).const_mul (-c)).exp
    have h2 : innerSL ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    rw [real_inner_comm, inner_gradient_left (𝕜 := ℝ), h1.fderiv]
    simp only [smul_apply, smul_eq_mul, h2, two_smul, add_apply]
    ring
  simp only [fpOp]
  rw [hl, hin]
  simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-- **The Fokker–Planck equilibrium** (arXiv 2412.05912, Sec. 6.3): the Maxwellian `f = e^{-v²/2}`
satisfies `Q f = 0`, a stationary solution, while `g = √f = e^{-v²/4}` satisfies
`Q g = (d/2 - v²/4) g`, so it does not solve the equation (`d ≥ 1`, at `v = 0`). -/
theorem fp_sqrt_maxwellian (hd : 0 < Module.finrank ℝ E) :
    (∀ v : E, fpOp (fun y : E => Real.exp (-(1 / 2) * ‖y‖ ^ 2)) v = 0) ∧
    (∀ v : E, √(Real.exp (-(1 / 2) * ‖v‖ ^ 2)) = Real.exp (-(1 / 4) * ‖v‖ ^ 2)) ∧
    ¬ ∀ v : E, fpOp (fun y : E => Real.exp (-(1 / 4) * ‖y‖ ^ 2)) v = 0 := by
  refine ⟨fun v => ?_, fun v => ?_, fun h => ?_⟩
  · rw [fpOp_gaussian]
    norm_num
  · rw [← Real.exp_half]
    congr 1
    ring
  · have h1 := h 0
    rw [fpOp_gaussian] at h1
    norm_num at h1
    exact hd.ne' h1

end Diffusion

/-! ### Sections 6.2, 6.3: nonlinear transformations and decompositions -/

section Transformations

/-- The matrix `exp (i j)` is a Vandermonde matrix. -/
private lemma det_exp_mul_ne_zero (r : ℕ) :
    (Matrix.of fun i j : Fin (r + 1) => Real.exp ((i : ℝ) * (j : ℝ))).det ≠ 0 := by
  have h : (Matrix.of fun i j : Fin (r + 1) => Real.exp ((i : ℝ) * (j : ℝ))) =
      Matrix.vandermonde fun i : Fin (r + 1) => Real.exp (i : ℝ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.vandermonde_apply]
    rw [← Real.exp_nat_mul, mul_comm]
  rw [h]
  refine Matrix.det_vandermonde_ne_zero_iff.2 fun a b hab => ?_
  have := Real.exp_injective hab
  exact Fin.ext (by exact_mod_cast this)

/-- **"A nonlinear transformation of a low-rank function is not necessarily low-rank"**
(arXiv 2412.05912, Sec. 6.3): `(x, v) ↦ x v` has rank one, and `exp (x v)` has no finite rank. -/
theorem exp_not_low_rank :
    HasSepRankLE ℝ (fun x v : ℝ => x * v) 1 ∧
      ∀ r, ¬ HasSepRankLE ℝ (fun x v : ℝ => Real.exp (x * v)) r := by
  refine ⟨⟨fun _ x => x, fun _ v => v, fun x v => by simp⟩, fun r => ?_⟩
  exact not_hasRankLEOver_of_det_ne_zero (fun i : Fin (r + 1) => (i : ℝ))
    (fun j : Fin (r + 1) => (j : ℝ)) (det_exp_mul_ne_zero r)

/-- **The square stays low rank** (arXiv 2412.05912, Sec. 6.3, "the choice of the transformation has
to be made with computational efficiency in mind"; this count is not in the paper): if `g` has rank
`r`, then `f = g²` has rank at most `r (r + 1) / 2 = C(r + 1, 2)`, so the transformation `f = g²`
keeps a low-rank `g` low rank in `f`, at a quadratic price. -/
theorem HasRankLEOver.sq {X Y : Type*} {g : X → Y → ℝ} {r : ℕ} (h : HasSepRankLE ℝ g r) :
    HasSepRankLE ℝ (fun x y => g x y ^ 2) ((r + 1).choose 2) := by
  classical
  obtain ⟨U, V, hg⟩ := h
  set m : Sym2 (Fin r) → Y → ℝ := fun p y =>
    Sym2.lift ⟨fun i j => V i y * V j y, fun _ _ => mul_comm _ _⟩ p with hm
  have hmem : ∀ x, (fun y => g x y ^ 2) ∈ Submodule.span ℝ (Set.range m) := by
    intro x
    have e : (fun y => g x y ^ 2) = ∑ i, ∑ j, (U i x * U j x) • m s(i, j) := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm, Sym2.lift_mk]
      rw [hg, pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  choose c hc using fun x => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hmem x)
  have hcard : Fintype.card (Sym2 (Fin r)) = (r + 1).choose 2 := by
    rw [Sym2.card, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k x => c x (e.symm k), fun k => m (e.symm k), fun x y => ?_⟩
  have h1 := congrFun (hc x) y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  change g x y ^ 2 = _
  rw [← h1]
  exact (Equiv.sum_comp e.symm fun p => c x p * m p y).symm

/-- **The multiplicative decomposition** (arXiv 2412.05912, Sec. 6.2): for
`f = exp (-(v - u)²/2) (ρ + ε a b)`, the quotient `g = ρ + ε a b` of the multiplicative
decomposition has rank at most two; the leading term `ρ` has rank one, as the paper says. The paper
prints Eq. (31) and the decompositions with `exp ((v - u)²/2)`; the minus sign is meant. -/
theorem multiplicative_rank_le {X Y : Type*} (ρ a : X → ℝ) (b : Y → ℝ) (ε : ℝ) :
    HasSepRankLE ℝ (fun x v => ρ x + ε * (a x * b v)) 2 := by
  refine ⟨![ρ, fun x => ε * a x], ![fun _ => 1, b], fun x v => ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **The additive decomposition is not low rank** (arXiv 2412.05912, Sec. 6.2, "an additive
decomposition ... does not result in a `g` that is of low rank"): let `f = M (ρ + ε a b)` with
`M = exp (-(v - u (x))²/2)`, velocities `v ∈ ℝ`, `a`, `b` without zeros, `ε ≠ 0`, and let the speed
`u` take all values in some interval `[0, δ]`. Then the remainder `g = f - ρ M` of the additive
decomposition has no finite rank, while the multiplicative one has rank two
(`multiplicative_rank_le`). In `d` dimensions the same holds along a line of velocities. -/
theorem additive_not_low_rank {X : Type*} {u : X → ℝ} {δ ε : ℝ} (hδ : 0 < δ)
    (hu : Icc 0 δ ⊆ range u) (hε : ε ≠ 0) (ρ a : X → ℝ) (b : ℝ → ℝ) (ha : ∀ x, a x ≠ 0)
    (hb : ∀ v, b v ≠ 0) (r : ℕ) :
    ¬ HasSepRankLE ℝ (fun x v => Real.exp (-(v - u x) ^ 2 / 2) * (ρ x + ε * (a x * b v)) -
      ρ x * Real.exp (-(v - u x) ^ 2 / 2)) r := by
  set c : ℝ := δ / (r + 1) with hc
  have hc0 : 0 < c := by positivity
  have hmem : ∀ i : Fin (r + 1), c * (i : ℝ) ∈ Icc 0 δ := by
    intro i
    refine ⟨by positivity, ?_⟩
    have hi : (i : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 i.2
    have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ hr]
    nlinarith
  choose xs hxs using fun i : Fin (r + 1) => hu (hmem i)
  set vs : Fin (r + 1) → ℝ := fun j => (j : ℝ) / c with hvs
  set d₁ : Fin (r + 1) → ℝ := fun i => ε * a (xs i) * Real.exp (-(c * (i : ℝ)) ^ 2 / 2) with hd₁
  set d₂ : Fin (r + 1) → ℝ := fun j => b (vs j) * Real.exp (-(vs j) ^ 2 / 2) with hd₂
  refine not_hasRankLEOver_of_det_ne_zero xs vs ?_
  have hfac : sample (fun x v => Real.exp (-(v - u x) ^ 2 / 2) * (ρ x + ε * (a x * b v)) -
      ρ x * Real.exp (-(v - u x) ^ 2 / 2)) xs vs =
      Matrix.diagonal d₁ * (Matrix.of fun i j : Fin (r + 1) => Real.exp ((i : ℝ) * (j : ℝ))) *
        Matrix.diagonal d₂ := by
    ext i j
    have hprod : c * (i : ℝ) * vs j = (i : ℝ) * (j : ℝ) := by
      simp only [hvs]
      field_simp
    have hexp : Real.exp (-(vs j - c * (i : ℝ)) ^ 2 / 2) = Real.exp (-(c * (i : ℝ)) ^ 2 / 2) *
        Real.exp ((i : ℝ) * (j : ℝ)) * Real.exp (-(vs j) ^ 2 / 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← hprod]
      congr 1
      ring
    simp only [sample, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hxs, hexp, hd₁,
      hd₂]
    ring
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  refine mul_ne_zero (mul_ne_zero ?_ (det_exp_mul_ne_zero r)) ?_
  · exact Finset.prod_ne_zero_iff.2 fun i _ =>
      mul_ne_zero (mul_ne_zero hε (ha _)) (Real.exp_pos _).ne'
  · exact Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hb _) (Real.exp_pos _).ne'

end Transformations

/-! ### Sections 2, 6.2: linear transport in the diffusive scaling, abstractly -/

section ChapmanEnskog

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The structure of the linear transport equation `ε ∂ₜ f + T f = ε⁻¹ (P f - f)` in the diffusive
scaling: `P` is the orthogonal projector on the velocity-independent functions, `T` (streaming) is
skew, `P T P = 0` says that the mean velocity vanishes. `S` measures regularity in `x`: it commutes
with `T` and `P` and controls `T`. For bounded `T`, `S = 1` and `c = ‖T‖` is always possible. -/
structure IsDiffusiveStructure (P T S : H →L[ℝ] H) (c : ℝ) : Prop where
  proj : IsOrthProj P
  skew : ∀ x y, ⟪T x, y⟫ = -⟪x, T y⟫
  mean_zero : ∀ x, P (T (P x)) = 0
  comm_T : ∀ x, S (T x) = T (S x)
  comm_P : ∀ x, S (P x) = P (S x)
  bound : ∀ x, ‖T x‖ ≤ c * ‖S x‖

/-- The field of `∂ₜ f = -ε⁻¹ T f + ε⁻² (P f - f)`. -/
noncomputable def kineticField (P T : H →L[ℝ] H) (ε : ℝ) (_t : ℝ) (y : H) : H :=
  -(ε⁻¹ • T y) + (ε⁻¹ ^ 2) • (P y - y)

/-- The linear relaxation estimate: `y' = -l y + b` with `‖b‖ ≤ B` gives
`‖y (t)‖ ≤ e^{-l t} ‖y (0)‖ + B / l` (arXiv 2412.05912, Sec. 2, for the Chapman–Enskog estimate). -/
theorem norm_le_of_relaxation {y b : ℝ → H} {l B τ : ℝ} (hl : 0 < l) (hB : 0 ≤ B)
    (hc : ContinuousOn y (Icc 0 τ))
    (hy : ∀ t ∈ Ico 0 τ, HasDerivWithinAt y (-(l • y t) + b t) (Ici t) t)
    (hb : ∀ t ∈ Ico 0 τ, ‖b t‖ ≤ B) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖y t‖ ≤ Real.exp (-l * t) * ‖y 0‖ + B / l := by
  set z : ℝ → H := fun s => Real.exp (l * s) • y s with hz
  have hexp : ∀ s, HasDerivAt (fun s => Real.exp (l * s)) (Real.exp (l * s) * l) s := by
    intro s
    have : HasDerivAt (fun s : ℝ => l * s) l s := by
      simpa using (hasDerivAt_id s).const_mul l
    exact this.exp
  have hzc : ContinuousOn z (Icc 0 τ) := by
    refine ContinuousOn.smul ?_ hc
    exact (Continuous.continuousOn (by fun_prop))
  have hz' : ∀ s ∈ Ico 0 τ, HasDerivWithinAt z (Real.exp (l * s) • b s) (Ici s) s := by
    intro s hs
    have h : HasDerivWithinAt z _ (Ici s) s :=
      ((hexp s).hasDerivWithinAt (s := Ici s)).smul (hy s hs)
    refine h.congr_deriv ?_
    module
  have hbound : ∀ x, HasDerivAt (fun s => ‖y 0‖ + B / l * (Real.exp (l * s) - 1))
      (B * Real.exp (l * x)) x := by
    intro x
    have h := (((hexp x).sub_const 1).const_mul (B / l)).const_add ‖y 0‖
    convert h using 1
    field_simp
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary hzc hz'
    (B := fun s => ‖y 0‖ + B / l * (Real.exp (l * s) - 1)) (B' := fun s => B * Real.exp (l * s))
    (by simp [hz]) hbound (fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hb s hs) (Real.exp_pos _).le) ht
  have hnorm : ‖z t‖ = Real.exp (l * t) * ‖y t‖ := by
    simp only [hz]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hnorm] at hmain
  have hE : Real.exp (-l * t) * Real.exp (l * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hEpos : 0 < Real.exp (-l * t) := Real.exp_pos _
  calc ‖y t‖ = Real.exp (-l * t) * (Real.exp (l * t) * ‖y t‖) := by
        rw [← mul_assoc, hE, one_mul]
    _ ≤ Real.exp (-l * t) * (‖y 0‖ + B / l * (Real.exp (l * t) - 1)) :=
        mul_le_mul_of_nonneg_left hmain hEpos.le
    _ = Real.exp (-l * t) * ‖y 0‖ + B / l * (1 - Real.exp (-l * t)) := by
        rw [mul_add, mul_left_comm, mul_sub, hE]
        ring
    _ ≤ Real.exp (-l * t) * ‖y 0‖ + B / l := by
        have h1 : 1 - Real.exp (-l * t) ≤ 1 := by linarith
        have h2 : 0 ≤ B / l := by positivity
        nlinarith

variable {P T S : H →L[ℝ] H} {c ε τ K : ℝ} {f : ℝ → H}

/-- **Energy estimate** (arXiv 2412.05912, Sec. 2, for the Chapman–Enskog estimate): `‖f‖` does not
grow along a solution. -/
theorem IsDiffusiveStructure.norm_le (hS : IsDiffusiveStructure P T S c)
    (hf : ODESolution (kineticField P T ε) f 0 τ) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖f t‖ ≤ ‖f 0‖ := by
  have hsq : ‖f t‖ ^ 2 ≤ ‖f 0‖ ^ 2 := by
    refine image_le_of_deriv_right_le_deriv_boundary (f := fun s => ‖f s‖ ^ 2)
      (f' := fun s => 2 * ⟪f s, kineticField P T ε s (f s)⟫) (B := fun _ => ‖f 0‖ ^ 2)
      (B' := fun _ => 0) (hf.cont.norm.pow 2) (fun s hs => (hf.deriv s hs).norm_sq) le_rfl
      continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _) (fun s _ => ?_) ht
    have h1 : ⟪f s, T (f s)⟫ = 0 := by
      have := hS.skew (f s) (f s)
      rw [real_inner_comm] at this
      linarith
    have h2 : ⟪f s, P (f s) - f s⟫ = -‖f s - P (f s)‖ ^ 2 := by
      have h3 := hS.proj.inner_sub_self (f s) (f s)
      have h5 : ⟪f s, f s - P (f s)⟫ = ‖f s - P (f s)‖ ^ 2 := by
        have h6 := real_inner_self_eq_norm_sq (f s - P (f s))
        rw [inner_sub_left, h3, sub_zero] at h6
        exact h6
      rw [← neg_sub, inner_neg_right, h5]
    simp only [kineticField, inner_add_right, inner_neg_right, inner_smul_right, h1, h2]
    have : 0 ≤ (ε⁻¹ ^ 2) * ‖f s - P (f s)‖ ^ 2 := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 hsq

/-- `S` maps solutions to solutions: spatial derivatives of a solution solve the same equation
(arXiv 2412.05912, Sec. 2, for the Chapman–Enskog estimate). -/
theorem IsDiffusiveStructure.odeSolution_apply (hS : IsDiffusiveStructure P T S c)
    (hf : ODESolution (kineticField P T ε) f 0 τ) :
    ODESolution (kineticField P T ε) (fun t => S (f t)) 0 τ where
  cont := S.continuous.comp_continuousOn hf.cont
  deriv := fun t ht => by
    have h : HasDerivWithinAt (fun t => S (f t)) (S (kineticField P T ε t (f t))) (Ici t) t :=
      S.hasFDerivAt.comp_hasDerivWithinAt t (hf.deriv t ht)
    refine h.congr_deriv ?_
    simp only [kineticField, map_add, map_neg, map_smul, map_sub, hS.comm_T, hS.comm_P]

/-- The first order estimate `‖(1 - P) f‖ ≤ ‖(1 - P) f₀‖ + ε c ‖S f₀‖`, which is the `f = ρ + ε g`
of arXiv 2412.05912, Sec. 2, for all times. -/
theorem IsDiffusiveStructure.norm_micro_le (hS : IsDiffusiveStructure P T S c) (hc : 0 ≤ c)
    (hε : 0 < ε) (hf : ODESolution (kineticField P T ε) f 0 τ) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖f t - P (f t)‖ ≤ ‖f 0 - P (f 0)‖ + ε * (c * ‖S (f 0)‖) := by
  have hSf := hS.odeSolution_apply hf
  have hl : 0 < ε⁻¹ ^ 2 := by positivity
  have hBnn : 0 ≤ ε⁻¹ * (c * ‖S (f 0)‖) := by positivity
  have hmain := norm_le_of_relaxation (y := fun s => f s - P (f s))
    (b := fun s => -(ε⁻¹ • (T (f s) - P (T (f s))))) hl hBnn
    (hf.cont.sub (P.continuous.comp_continuousOn hf.cont)) (fun s hs => ?_) (fun s hs => ?_) ht
  · have hE : Real.exp (-ε⁻¹ ^ 2 * t) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := ht.1
      nlinarith
    calc ‖f t - P (f t)‖ ≤ Real.exp (-ε⁻¹ ^ 2 * t) * ‖f 0 - P (f 0)‖ +
          ε⁻¹ * (c * ‖S (f 0)‖) / ε⁻¹ ^ 2 := hmain
      _ ≤ ‖f 0 - P (f 0)‖ + ε * (c * ‖S (f 0)‖) := by
        have e : ε⁻¹ * (c * ‖S (f 0)‖) / ε⁻¹ ^ 2 = ε * (c * ‖S (f 0)‖) := by
          field_simp
        rw [e]
        have := mul_le_of_le_one_left (norm_nonneg (f 0 - P (f 0))) hE
        linarith
  · have h : HasDerivWithinAt (fun s => f s - P (f s))
        (kineticField P T ε s (f s) - P (kineticField P T ε s (f s))) (Ici s) s :=
      (hf.deriv s hs).sub (P.hasFDerivAt.comp_hasDerivWithinAt s (hf.deriv s hs))
    refine h.congr_deriv ?_
    have hP := hS.proj.idem (f s)
    simp only [kineticField, map_add, map_neg, map_smul, map_sub, hP, sub_self, smul_zero]
    module
  · rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hε).le
    have h1 := hS.proj.norm_sub_le (T (f s))
    have h2 := hS.bound (f s)
    have h3 := hS.norm_le hSf (t := s) ⟨hs.1, hs.2.le⟩
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hc))

/-- The projector `1 - P` commutes with `S`. -/
private lemma IsDiffusiveStructure.map_micro (hS : IsDiffusiveStructure P T S c) (x : H) :
    S (x - P x) = S x - P (S x) := by
  rw [map_sub, hS.comm_P]

/-- **The Chapman–Enskog expansion, abstractly** (arXiv 2412.05912, Sec. 2, "using a Chapman–Enskog
expansion it can be shown ...", with [51] = arXiv 2005.06571). Let `f` solve
`ε ∂ₜ f + T f = ε⁻¹ (P f - f)` with data `f₀ = P f₀ + O(ε)` in the sense `‖S (1 - P) f₀‖ ≤ ε K`.
Then `f = P f - ε T P f + e` with
`‖e (t)‖ ≤ e^{-t/ε²} ‖e (0)‖ + ε² (c K + 2 c² ‖S² f₀‖)`, for all `t`. So `f` is the macroscopic
`P f`, plus its explicit first correction, up to `O(ε²)`, after an initial layer of thickness
`O(ε²)`, with a constant that depends on `S² f₀` only, not on `‖T‖`. -/
theorem IsDiffusiveStructure.chapmanEnskog (hS : IsDiffusiveStructure P T S c) (hc : 0 ≤ c)
    (hε : 0 < ε) (hf : ODESolution (kineticField P T ε) f 0 τ)
    (hK : ‖S (f 0 - P (f 0))‖ ≤ ε * K) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖f t - (P (f t) - ε • T (P (f t)))‖ ≤
      Real.exp (-t / ε ^ 2) * ‖f 0 - (P (f 0) - ε • T (P (f 0)))‖ +
        ε ^ 2 * (c * K + 2 * c ^ 2 * ‖S (S (f 0))‖) := by
  have hSf := hS.odeSolution_apply hf
  have hSSf := hS.odeSolution_apply hSf
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  have hl : 0 < ε⁻¹ ^ 2 := by positivity
  have hKnn : 0 ≤ K := by
    have h1 : 0 ≤ ε * K := (norm_nonneg _).trans hK
    exact nonneg_of_mul_nonneg_right h1 hε
  set N := ‖S (S (f 0))‖ with hN
  have hNnn : 0 ≤ N := norm_nonneg _
  -- the bound on `S (1 - P) f`
  have hSh : ∀ s ∈ Ico 0 τ, ‖S (f s - P (f s))‖ ≤ ε * (K + c * N) := by
    intro s hs
    have h1 := hS.norm_micro_le hc hε hSf (t := s) ⟨hs.1, hs.2.le⟩
    rw [hS.map_micro]
    have h2 : ‖S (f 0) - P (S (f 0))‖ ≤ ε * K := by rw [← hS.map_micro]; exact hK
    calc ‖S (f s) - P (S (f s))‖ ≤ ‖S (f 0) - P (S (f 0))‖ + ε * (c * N) := h1
      _ ≤ ε * K + ε * (c * N) := by linarith
      _ = ε * (K + c * N) := by ring
  have hSSh : ∀ s ∈ Ico 0 τ, ‖S (S (f s - P (f s)))‖ ≤ N := by
    intro s hs
    rw [hS.map_micro, hS.map_micro]
    exact (hS.proj.norm_sub_le _).trans (hS.norm_le hSSf ⟨hs.1, hs.2.le⟩)
  set h : ℝ → H := fun s => f s - P (f s) with hh
  set b : ℝ → H := fun s => -(ε⁻¹ • (T (h s) - P (T (h s)))) - T (P (T (h s))) with hb
  have hBnn : 0 ≤ c * (K + c * N) + c ^ 2 * N := by positivity
  have hmain := norm_le_of_relaxation (y := fun s => f s - (P (f s) - ε • T (P (f s)))) (b := b)
    hl hBnn ?_ ?_ ?_ ht
  · have e1 : -ε⁻¹ ^ 2 * t = -t / ε ^ 2 := by
      field_simp
    have e2 : (c * (K + c * N) + c ^ 2 * N) / ε⁻¹ ^ 2 = ε ^ 2 * (c * K + 2 * c ^ 2 * N) := by
      field_simp
      ring
    rw [e1, e2] at hmain
    exact hmain
  · refine hf.cont.sub (ContinuousOn.sub ?_ ?_)
    · exact P.continuous.comp_continuousOn hf.cont
    · exact (continuous_const.smul (T.continuous.comp P.continuous)).comp_continuousOn hf.cont
  · intro s hs
    have hd := hf.deriv s hs
    have hPd := P.hasFDerivAt.comp_hasDerivWithinAt s hd
    have hTPd := T.hasFDerivAt.comp_hasDerivWithinAt s hPd
    have hsum := hd.sub (hPd.sub (hTPd.const_smul ε))
    have hP := hS.proj.idem (f s)
    have hPTP : P (T (P (f s))) = 0 := hS.mean_zero (f s)
    have hFP : P (kineticField P T ε s (f s)) = -(ε⁻¹ • P (T (f s))) := by
      simp [kineticField, hP]
    have hTFP : T (P (kineticField P T ε s (f s))) = -(ε⁻¹ • T (P (T (f s)))) := by
      rw [hFP, map_neg, map_smul]
    have hbs : b s = -(ε⁻¹ • ((T (f s) - T (P (f s))) - P (T (f s)))) - T (P (T (f s))) := by
      simp only [hb, hh, map_sub, hPTP, sub_zero, map_zero]
    have hee : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    refine HasDerivWithinAt.congr_deriv (f := fun s => f s - (P (f s) - ε • T (P (f s)))) hsum ?_
    rw [hTFP, hFP, hbs]
    simp only [kineticField]
    linear_combination (norm := module)
      hee • (ε⁻¹ • T (P (f s)) - T (P (T (f s))))
  · intro s hs
    have hSs := hSh s hs
    have hSSs := hSSh s hs
    have h1 : ‖T (h s)‖ ≤ c * (ε * (K + c * N)) :=
      (hS.bound (h s)).trans (mul_le_mul_of_nonneg_left hSs hc)
    have h2 : ‖T (h s) - P (T (h s))‖ ≤ c * (ε * (K + c * N)) :=
      (hS.proj.norm_sub_le _).trans h1
    have h3 : ‖ε⁻¹ • (T (h s) - P (T (h s)))‖ ≤ c * (K + c * N) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεi]
      calc ε⁻¹ * ‖T (h s) - P (T (h s))‖ ≤ ε⁻¹ * (c * (ε * (K + c * N))) :=
            mul_le_mul_of_nonneg_left h2 hεi.le
        _ = c * (K + c * N) := by
          field_simp
    have h4 : ‖T (P (T (h s)))‖ ≤ c ^ 2 * N := by
      have h5 : ‖S (P (T (h s)))‖ ≤ c * N := by
        rw [hS.comm_P, hS.comm_T]
        exact (hS.proj.norm_le _).trans
          ((hS.bound _).trans (mul_le_mul_of_nonneg_left hSSs hc))
      calc ‖T (P (T (h s)))‖ ≤ c * ‖S (P (T (h s)))‖ := hS.bound _
        _ ≤ c * (c * N) := mul_le_mul_of_nonneg_left h5 hc
        _ = c ^ 2 * N := by ring
    calc ‖b s‖ ≤ ‖-(ε⁻¹ • (T (h s) - P (T (h s))))‖ + ‖T (P (T (h s)))‖ := norm_sub_le _ _
      _ ≤ c * (K + c * N) + c ^ 2 * N := by
        rw [norm_neg]
        exact add_le_add h3 h4

/-- **The transport equation has solutions** (arXiv 2412.05912, Sec. 2). For complete `H` and all
data the kinetic equation has a solution on `[0, τ]`, so the hypotheses of
`IsDiffusiveStructure.chapmanEnskog` on `f` are not vacuous. -/
theorem exists_kinetic_solution [CompleteSpace H] (P T : H →L[ℝ] H) (ε : ℝ) (f₀ : H) :
    ∃ f : ℝ → H, f 0 = f₀ ∧ ∀ τ, ODESolution (kineticField P T ε) f 0 τ := by
  set A : H →L[ℝ] H := -(ε⁻¹ • T) + (ε⁻¹ ^ 2) • (P - 1) with hA
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) f₀)
      (A (NormedSpace.exp (s • A) f₀)) s := by
    intro s
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s).clm_apply (hasDerivAt_const s f₀)
    simpa using h
  refine ⟨fun s => NormedSpace.exp (s • A) f₀, by simp, fun τ => ?_⟩
  refine ⟨fun s _ => (hd s).continuousAt.continuousWithinAt, fun s _ => ?_⟩
  have h := (hd s).hasDerivWithinAt (s := Ici s)
  convert h using 1
  simp [kineticField, hA]

end ChapmanEnskog

/-! ### Sections 2, 6.2: linear transport in the diffusive scaling, on a grid -/

/-- A velocity quadrature in `ℝ^d` with nodes `node · j`, positive weights of sum one, and vanishing
mean velocity, the discrete form of `∫ v dv = 0`. -/
structure VelocityRule (V : Type*) [Fintype V] (d : ℕ) where
  /-- the weights -/
  w : V → ℝ
  w_pos : ∀ j, 0 < w j
  sum_w : ∑ j, w j = 1
  /-- the components of the nodes -/
  node : Fin d → V → ℝ
  mean_zero : ∀ l, ∑ j, w j * node l j = 0

section LinearTransport

open scoped LeanDLRA.Frobenius
open LeanDLRA.Frobenius

variable {X V : Type*} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] {d : ℕ}

/-- The matrix `ρ ⊗ 1` of a velocity-independent function. -/
def isoM (V : Type*) (ρ : X → ℝ) : Matrix X V ℝ := Matrix.of fun i _ => ρ i

namespace VelocityRule

variable (q : VelocityRule V d) (D : Fin d → Matrix X X ℝ)

/-- The square roots of the weights. -/
noncomputable def sq (j : V) : ℝ := √(q.w j)

lemma sq_mul_sq (j : V) : q.sq j * q.sq j = q.w j := Real.mul_self_sqrt (q.w_pos j).le

/-- The unit vector `√w`, as a matrix with one column. -/
noncomputable def colS : Matrix V Unit ℝ := Matrix.of fun j _ => q.sq j

lemma colS_orth : q.colSᵀ * q.colS = 1 := by
  ext a b
  simp [Matrix.mul_apply, colS, q.sq_mul_sq, q.sum_w]

/-- The weight `diag (√w)`: `‖F diag (√w)‖` is the norm of `L²ₓ L²ᵥ` of the quadrature. -/
noncomputable def weight : Matrix V V ℝ := Matrix.diagonal q.sq

/-- The density `ρ = ⟨f⟩`. -/
def density (F : Matrix X V ℝ) : X → ℝ := F *ᵥ q.w

/-- Streaming `v · ∇ₓ F = ∑ₗ Dₗ F diag (vₗ)`, with `Dₗ` a discretization of `∂_{xₗ}`. -/
def streaming (F : Matrix X V ℝ) : Matrix X V ℝ := ∑ l, D l * F * Matrix.diagonal (q.node l)

/-- The right side of the semi-discrete linear transport equation in the diffusive scaling,
`ε ∂ₜ F + v · ∇ₓ F = ε⁻¹ (⟨F⟩ - F)`. -/
noncomputable def field (ε : ℝ) (_t : ℝ) (F : Matrix X V ℝ) : Matrix X V ℝ :=
  -(ε⁻¹ • q.streaming D F) + (ε⁻¹ ^ 2) • (isoM V (q.density F) - F)

/-- The Chapman–Enskog approximation `ρ - ε v · ∇ₓ ρ`, with `ρ = ⟨F⟩`. -/
noncomputable def ceApprox (ε : ℝ) (F : Matrix X V ℝ) : Matrix X V ℝ :=
  isoM V (q.density F) - ε • ∑ l, Matrix.vecMulVec (D l *ᵥ q.density F) (q.node l)

/-- `v · ∇ₓ` as a continuous linear map. -/
noncomputable def streamC : Matrix X V ℝ →L[ℝ] Matrix X V ℝ :=
  ∑ l, (leftMulCLM (D l)).comp (rightMulCLM (Matrix.diagonal (q.node l)))

lemma streamC_apply (F : Matrix X V ℝ) : q.streamC D F = q.streaming D F := by
  simp [streamC, streaming, Matrix.mul_assoc]

/-- The projector on `√w` in the weighted variables, which is `⟨·⟩` in the variables `F`. -/
noncomputable def projC : Matrix X V ℝ →L[ℝ] Matrix X V ℝ := rightProj q.colS

end VelocityRule

/-- The regularity operator `1 - ∑ₗ Dₗ²`, a discrete `1 - Δ`. -/
def regM (D : Fin d → Matrix X X ℝ) : Matrix X X ℝ := 1 - ∑ l, D l * D l

/-- `regM` as a continuous linear map. -/
noncomputable def regC (V : Type*) [Fintype V] (D : Fin d → Matrix X X ℝ) :
    Matrix X V ℝ →L[ℝ] Matrix X V ℝ := leftMulCLM (regM D)

/-- A diagonal bounded by `M` scales the Frobenius norm by at most `M` (arXiv 2412.05912, Sec. 2,
the bound on streaming). -/
theorem norm_mul_diagonal_le {Y : Matrix X V ℝ} {ν : V → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ j, |ν j| ≤ M) : ‖Y * Matrix.diagonal ν‖ ≤ M * ‖Y‖ := by
  have hsq : ‖Y * Matrix.diagonal ν‖ ^ 2 ≤ (M * ‖Y‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.mul_diagonal, mul_pow, mul_comm]
    have h : ν j ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [(abs_le.1 (hM j)).1]) (abs_le.1 (hM j)).2
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hsq

/-- Every skew `Dₗ` is controlled by `regM`: `‖Dₗ x‖ ≤ ‖(1 - ∑ D²) x‖` (arXiv 2412.05912, Sec. 2,
the bound on streaming). -/
theorem norm_mul_le_regM {D : Fin d → Matrix X X ℝ} (hskew : ∀ l, (D l)ᵀ = -D l) (l : Fin d)
    (x : Matrix X V ℝ) : ‖D l * x‖ ≤ ‖regM D * x‖ := by
  set B : Matrix X V ℝ := -∑ i, D i * (D i * x) with hB
  have hA : regM D * x = x + B := by
    rw [regM, Matrix.sub_mul, Matrix.one_mul, Matrix.sum_mul, hB, sub_eq_add_neg]
    simp only [Matrix.mul_assoc]
  have hinner : ∑ i, ‖D i * x‖ ^ 2 = ⟪x, B⟫ := by
    rw [hB, inner_neg_right, inner_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_mul_left', hskew, Matrix.neg_mul, inner_neg_left, neg_neg,
      real_inner_self_eq_norm_sq]
  have h1 : ‖D l * x‖ ^ 2 ≤ ∑ i, ‖D i * x‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖D i * x‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ l)
  have hsq : ‖D l * x‖ ^ 2 ≤ ‖regM D * x‖ ^ 2 := by
    rw [hA, norm_add_sq_real, ← hinner]
    nlinarith [norm_nonneg x, norm_nonneg B, sq_nonneg ‖D l * x‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 hsq

namespace VelocityRule

variable (q : VelocityRule V d) {D : Fin d → Matrix X X ℝ}

/-- The transport structure on the grid: `T = ∑ₗ Dₗ ⊗ diag (vₗ)`, `P = √w √wᵀ`, `S = 1 - ∑ D²`
(arXiv 2412.05912, Sec. 2). -/
theorem isDiffusiveStructure (hskew : ∀ l, (D l)ᵀ = -D l)
    (hcomm : ∀ i j, D i * D j = D j * D i) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ l j, |q.node l j| ≤ M) :
    IsDiffusiveStructure (q.projC : Matrix X V ℝ →L[ℝ] Matrix X V ℝ) (q.streamC D) (regC V D)
      (d * M) where
  proj := isOrthProj_rightProj q.colS_orth
  skew x y := by
    rw [q.streamC_apply, q.streamC_apply]
    simp only [streaming, sum_inner, inner_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_mul_right, inner_mul_left, hskew, Matrix.diagonal_transpose, Matrix.neg_mul,
      inner_neg_right, Matrix.mul_assoc]
  mean_zero x := by
    have h0 : ∀ l, q.colSᵀ * Matrix.diagonal (q.node l) * q.colS = 0 := by
      intro l
      ext a b
      have : ∑ j, q.sq j * (q.node l j * q.sq j) = 0 := by
        rw [← q.mean_zero l]
        exact Finset.sum_congr rfl fun j _ => by
          rw [← q.sq_mul_sq j]
          ring
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simpa only [Matrix.diagonal_mul, colS, Matrix.transpose_apply, Matrix.of_apply,
        Matrix.zero_apply] using this
    rw [q.streamC_apply]
    simp only [projC, rightProj_apply, streaming, Matrix.sum_mul]
    refine Finset.sum_eq_zero fun l _ => ?_
    calc D l * (x * q.colS * q.colSᵀ) * Matrix.diagonal (q.node l) * q.colS * q.colSᵀ
        = D l * x * q.colS * (q.colSᵀ * Matrix.diagonal (q.node l) * q.colS) * q.colSᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  comm_T x := by
    have hc : ∀ l, regM D * D l = D l * regM D := by
      intro l
      simp only [regM, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.sum_mul, Matrix.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_assoc, hcomm i l, ← Matrix.mul_assoc, hcomm i l, Matrix.mul_assoc]
    rw [q.streamC_apply, q.streamC_apply]
    simp only [regC, leftMulCLM_apply, streaming, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc (D l)]
  comm_P x := by
    simp only [regC, leftMulCLM_apply, projC, rightProj_apply, Matrix.mul_assoc]
  bound x := by
    rw [q.streamC_apply]
    calc ‖q.streaming D x‖ ≤ ∑ l, ‖D l * x * Matrix.diagonal (q.node l)‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin d, M * ‖regC V D x‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine (norm_mul_diagonal_le hM0 (hM l)).trans ?_
        exact mul_le_mul_of_nonneg_left (norm_mul_le_regM hskew l x) hM0
      _ = d * M * ‖regC V D x‖ := by
        simp [mul_assoc]

/-- In the weighted variables, streaming is the same operator. -/
lemma streaming_mul_weight (D : Fin d → Matrix X X ℝ) (F : Matrix X V ℝ) :
    q.streaming D F * q.weight = q.streamC D (F * q.weight) := by
  rw [q.streamC_apply]
  simp only [streaming, Matrix.sum_mul, weight]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  rw [show (fun i => q.node l i * q.sq i) = fun i => q.sq i * q.node l i from
    funext fun _ => mul_comm _ _]

/-- In the weighted variables, `⟨·⟩ ⊗ 1` is the projector on `√w`. -/
lemma isoM_mul_weight (F : Matrix X V ℝ) :
    isoM V (q.density F) * q.weight = q.projC (F * q.weight) := by
  have e : ∀ i, (F * q.weight * q.colS) i () = q.density F i := by
    intro i
    rw [Matrix.mul_apply]
    simp only [weight, Matrix.mul_diagonal, colS, Matrix.of_apply, density, Matrix.mulVec,
      dotProduct]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_assoc, q.sq_mul_sq]
  have rhs : ∀ i j, q.projC (F * q.weight) i j = q.density F i * q.sq j := by
    intro i j
    simp only [projC, rightProj_apply]
    rw [Matrix.mul_apply, Fintype.sum_unique]
    change (F * q.weight * q.colS) i () * q.colS j () = _
    rw [e]
    rfl
  have lhs : ∀ i j, (isoM V (q.density F) * q.weight) i j = q.density F i * q.sq j := by
    intro i j
    simp [weight, isoM, Matrix.mul_diagonal]
  ext i j
  rw [lhs, rhs]

/-- The field in the weighted variables is `kineticField`. -/
lemma field_mul_weight (D : Fin d → Matrix X X ℝ) (ε t : ℝ) (F : Matrix X V ℝ) :
    q.field D ε t F * q.weight = kineticField q.projC (q.streamC D) ε t (F * q.weight) := by
  simp only [field, kineticField, Matrix.add_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.sub_mul,
    q.streaming_mul_weight, q.isoM_mul_weight]

/-- The first correction: streaming of `ρ ⊗ 1` is `∑ₗ (Dₗ ρ) ⊗ vₗ`. -/
lemma streaming_isoM (D : Fin d → Matrix X X ℝ) (ρ : X → ℝ) :
    q.streaming D (isoM V ρ) = ∑ l, Matrix.vecMulVec (D l *ᵥ ρ) (q.node l) := by
  simp only [streaming]
  refine Finset.sum_congr rfl fun l _ => ?_
  ext i j
  rw [Matrix.mul_diagonal, Matrix.vecMulVec_apply]
  congr 1

/-- The error of the Chapman–Enskog approximation, in the weighted variables. -/
lemma sub_ceApprox_mul_weight (D : Fin d → Matrix X X ℝ) (ε : ℝ) (F : Matrix X V ℝ) :
    (F - q.ceApprox D ε F) * q.weight =
      F * q.weight - (q.projC (F * q.weight) -
        ε • q.streamC D (q.projC (F * q.weight))) := by
  rw [← q.isoM_mul_weight, ← q.streaming_mul_weight, q.streaming_isoM]
  simp only [ceApprox, Matrix.sub_mul, Matrix.smul_mul]

/-- **Rank of the first order expansion** (arXiv 2412.05912, Sec. 2): `ρ - ε v · ∇ₓ ρ` has rank at
most `d + 1`: one for `ρ` and one for each component of `v`. -/
theorem ceApprox_rank_le (D : Fin d → Matrix X X ℝ) (ε : ℝ) (F : Matrix X V ℝ) :
    (q.ceApprox D ε F).rank ≤ d + 1 := by
  set ρ := q.density F with hρ
  set U : Matrix X (Option (Fin d)) ℝ :=
    Matrix.of fun i a => a.elim (ρ i) fun l => (D l *ᵥ ρ) i with hU
  set W : Matrix (Option (Fin d)) V ℝ :=
    Matrix.of fun a j => a.elim 1 fun l => -ε * q.node l j with hW
  have hfac : q.ceApprox D ε F = U * W := by
    ext i j
    simp only [ceApprox, hU, hW, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_option,
      Option.elim_none, Option.elim_some, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, isoM, ← hρ, mul_one, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hfac]
  refine (Matrix.rank_mul_le_left U W).trans ?_
  simpa using Matrix.rank_le_card_width U

/-- **Linear transport is close to rank `d + 1`** (arXiv 2412.05912, Sec. 2, citing [51] = arXiv
2005.06571), semi-discrete: let `F` solve `ε ∂ₜ F + v · ∇ₓ F = ε⁻¹ (⟨F⟩ - F)` with skew commuting
`Dₗ`, nodes bounded by `M`, and data with `‖(1 - ∑ D²) (F₀ - ⟨F₀⟩) diag √w‖ ≤ ε K`, which is the
paper's `f = ρ + ε g`. Then, with `c = d M`, in the norm `‖X diag √w‖` of `L²ₓ L²ᵥ`,
`‖F - (ρ - ε v · ∇ₓ ρ)‖ ≤ e^{-t/ε²} ‖F₀ - (ρ₀ - ε v · ∇ₓ ρ₀)‖ + ε² (c K + 2 c² ‖(1 - ∑ D²)² F₀‖)`.
The constants do not depend on the mesh: they are discrete `H⁴` norms of the data. The paper gives
no conditions; the semi-discretization, the constant cross section and the absence of sources are
the choices made here, and the initial layer `e^{-t/ε²}` is what happens for data that are not
well prepared. -/
theorem linearTransport_chapmanEnskog (hskew : ∀ l, (D l)ᵀ = -D l)
    (hcomm : ∀ i j, D i * D j = D j * D i) {M ε τ K : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ l j, |q.node l j| ≤ M) (hε : 0 < ε) {F : ℝ → Matrix X V ℝ}
    (hF : ODESolution (q.field D ε) F 0 τ)
    (hK : ‖regM D * ((F 0 - isoM V (q.density (F 0))) * q.weight)‖ ≤ ε * K)
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖(F t - q.ceApprox D ε (F t)) * q.weight‖ ≤
      Real.exp (-t / ε ^ 2) * ‖(F 0 - q.ceApprox D ε (F 0)) * q.weight‖ +
        ε ^ 2 * ((d * M) * K +
          2 * (d * M) ^ 2 * ‖regM D * (regM D * (F 0 * q.weight))‖) := by
  have hS := q.isDiffusiveStructure hskew hcomm hM0 hM
  have hG : ODESolution (kineticField q.projC (q.streamC D) ε) (fun s => F s * q.weight) 0 τ := by
    refine ⟨?_, fun s hs => ?_⟩
    · exact (rightMulCLM q.weight).continuous.comp_continuousOn hF.cont
    · have h : HasDerivWithinAt (fun s => F s * q.weight)
          (rightMulCLM q.weight (q.field D ε s (F s))) (Ici s) s :=
        (rightMulCLM q.weight).hasFDerivAt.comp_hasDerivWithinAt s (hF.deriv s hs)
      refine h.congr_deriv ?_
      rw [rightMulCLM_apply, q.field_mul_weight]
  have hK' : ‖regC V D ((F 0 * q.weight) - q.projC (F 0 * q.weight))‖ ≤ ε * K := by
    rw [← q.isoM_mul_weight, ← Matrix.sub_mul]
    exact hK
  have hc : (0 : ℝ) ≤ d * M := by positivity
  have h := hS.chapmanEnskog hc hε hG hK' ht
  rw [q.sub_ceApprox_mul_weight, q.sub_ceApprox_mul_weight]
  exact h

/-- **`f` has at most rank 4 up to terms of order `ε²`** (arXiv 2412.05912, Sec. 2, citing [51] =
arXiv 2005.06571), in three dimensions, for the semi-discrete system of
`linearTransport_chapmanEnskog`: there is a matrix of rank at most `4` at distance
`e^{-t/ε²} ‖e₀‖ + C ε²` of `F (t)`, with `C` independent of `ε` and of the mesh when `K` and the
discrete `H⁴` norm of `F₀` are. -/
theorem linearTransport_rank_four (q : VelocityRule V 3) {D : Fin 3 → Matrix X X ℝ}
    (hskew : ∀ l, (D l)ᵀ = -D l) (hcomm : ∀ i j, D i * D j = D j * D i) {M ε τ K : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ l j, |q.node l j| ≤ M) (hε : 0 < ε) {F : ℝ → Matrix X V ℝ}
    (hF : ODESolution (q.field D ε) F 0 τ)
    (hK : ‖regM D * ((F 0 - isoM V (q.density (F 0))) * q.weight)‖ ≤ ε * K)
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ∃ R : Matrix X V ℝ, R.rank ≤ 4 ∧ ‖(F t - R) * q.weight‖ ≤
      Real.exp (-t / ε ^ 2) * ‖(F 0 - q.ceApprox D ε (F 0)) * q.weight‖ +
        ε ^ 2 * ((3 * M) * K +
          2 * (3 * M) ^ 2 * ‖regM D * (regM D * (F 0 * q.weight))‖) := by
  refine ⟨q.ceApprox D ε (F t), q.ceApprox_rank_le D ε (F t), ?_⟩
  simpa using q.linearTransport_chapmanEnskog hskew hcomm hM0 hM hε hF hK ht

/-- The semi-discrete transport equation has a global solution for every initial value (arXiv
2412.05912, Sec. 2), so `linearTransport_chapmanEnskog` is not vacuous. -/
theorem exists_transport_solution (D : Fin d → Matrix X X ℝ) (ε : ℝ) (F₀ : Matrix X V ℝ) :
    ∃ F : ℝ → Matrix X V ℝ, F 0 = F₀ ∧ ∀ τ, ODESolution (q.field D ε) F 0 τ := by
  set M : Matrix V V ℝ := Matrix.of fun i _ => q.w i with hM
  set A : Matrix X V ℝ →L[ℝ] Matrix X V ℝ :=
    -(ε⁻¹ • q.streamC D) + (ε⁻¹ ^ 2) • (rightMulCLM M - 1) with hA
  have hAval : ∀ F, A F = q.field D ε 0 F := by
    intro F
    have h : F * M = isoM V (q.density F) := by
      ext i j
      simp [Matrix.mul_apply, hM, isoM, density, Matrix.mulVec, dotProduct]
    simp [hA, field, h, q.streamC_apply]
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) F₀)
      (A (NormedSpace.exp (s • A) F₀)) s := by
    intro s
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s).clm_apply (hasDerivAt_const s F₀)
    simpa using h
  refine ⟨fun s => NormedSpace.exp (s • A) F₀, by simp, fun τ => ?_⟩
  refine ⟨fun s _ => (hd s).continuousAt.continuousWithinAt, fun s _ => ?_⟩
  have h := (hd s).hasDerivWithinAt (s := Ici s)
  refine h.congr_deriv ?_
  rw [hAval]
  rfl

end VelocityRule

end LinearTransport

/-! The hypotheses of `linearTransport_rank_four` hold for the standard discretization. -/

section Instance

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The shift by `a` on a finite group, as a matrix. -/
def shiftM (a : G) : Matrix G G ℝ := Matrix.of fun x y => if y = x + a then 1 else 0

lemma shiftM_mul (a b : G) : shiftM a * shiftM b = shiftM (a + b) := by
  ext x y
  simp only [shiftM, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [add_assoc]

lemma shiftM_transpose (a : G) : (shiftM a)ᵀ = shiftM (-a) := by
  ext x y
  simp only [shiftM, Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  exact propext ⟨fun h => by simp [h], fun h => by simp [h]⟩

/-- The central difference in the direction `a`, step `h`. -/
noncomputable def centralM (h : ℝ) (a : G) : Matrix G G ℝ :=
  (2 * h)⁻¹ • (shiftM a - shiftM (-a))

/-- Central differences are skew (arXiv 2412.05912, Sec. 2, the setting of the rank four claim). -/
theorem centralM_skew (h : ℝ) (a : G) : (centralM h a)ᵀ = -centralM h a := by
  simp only [centralM, Matrix.transpose_smul, Matrix.transpose_sub, shiftM_transpose, neg_neg,
    ← smul_neg, neg_sub]

/-- Central differences commute (arXiv 2412.05912, Sec. 2, the setting of the rank four claim). -/
theorem centralM_comm (h : ℝ) (a b : G) :
    centralM h a * centralM h b = centralM h b * centralM h a := by
  simp only [centralM, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, shiftM_mul]
  rw [add_comm a b, add_comm (-a) b, add_comm a (-b), add_comm (-a) (-b)]
  module

/-- The six velocities `± e_l` with equal weights: the three-dimensional `S₂`-type rule. -/
noncomputable def sixPointRule : VelocityRule (Fin 3 × Bool) 3 where
  w := fun _ => 1 / 6
  w_pos := fun _ => by norm_num
  sum_w := by simp [Fintype.card_prod]
  node := fun l j => if l = j.1 then (if j.2 then 1 else -1) else 0
  mean_zero := fun l => by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h : l = x <;> simp [h]


/-- Central differences on the periodic grid `(ℤ/N)³`, with step `h`. -/
noncomputable def gridD (N : ℕ) [NeZero N] (h : ℝ) (l : Fin 3) :
    Matrix (Fin 3 → ZMod N) (Fin 3 → ZMod N) ℝ :=
  centralM h (Pi.single l 1)

/-- **The hypotheses hold** (arXiv 2412.05912, Sec. 2, the setting of `linearTransport_rank_four`):
central differences on `(ℤ/N)³` are skew and commute, and the six velocities `± e_l` are bounded. -/
theorem grid_hypotheses (N : ℕ) [NeZero N] (h : ℝ) :
    (∀ l, (gridD N h l)ᵀ = -gridD N h l) ∧
      (∀ i j, gridD N h i * gridD N h j = gridD N h j * gridD N h i) ∧
        ∀ l j, |sixPointRule.node l j| ≤ 1 := by
  refine ⟨fun l => centralM_skew h _, fun i j => centralM_comm h _ _, fun l j => ?_⟩
  simp only [sixPointRule]
  split_ifs <;> simp

section GridInstance

open scoped LeanDLRA.Frobenius

/-- **Rank four on the standard grid** (arXiv 2412.05912, Sec. 2, citing [51]): for central
differences on `(ℤ/N)³` and the six-point rule, every initial value generates a solution, and if
it has the form `ρ + ε g` then the solution is within `e^{-t/ε²} ‖e₀‖ + C ε²` of rank four. So
`linearTransport_rank_four` is not vacuous. -/
theorem linearTransport_rank_four_grid (N : ℕ) [NeZero N] (h : ℝ) {ε τ K : ℝ} (hε : 0 < ε)
    (F₀ : Matrix (Fin 3 → ZMod N) (Fin 3 × Bool) ℝ)
    (hK : ‖regM (gridD N h) * ((F₀ - isoM _ (sixPointRule.density F₀)) * sixPointRule.weight)‖ ≤
      ε * K) :
    ∃ F : ℝ → Matrix (Fin 3 → ZMod N) (Fin 3 × Bool) ℝ, F 0 = F₀ ∧
      ODESolution (sixPointRule.field (gridD N h) ε) F 0 τ ∧ ∀ t ∈ Icc 0 τ,
        ∃ R : Matrix (Fin 3 → ZMod N) (Fin 3 × Bool) ℝ, R.rank ≤ 4 ∧
          ‖(F t - R) * sixPointRule.weight‖ ≤
            Real.exp (-t / ε ^ 2) *
                ‖(F₀ - sixPointRule.ceApprox (gridD N h) ε F₀) * sixPointRule.weight‖ +
              ε ^ 2 * ((3 * 1) * K + 2 * (3 * 1) ^ 2 *
                ‖regM (gridD N h) * (regM (gridD N h) * (F₀ * sixPointRule.weight))‖) := by
  obtain ⟨hskew, hcomm, hM⟩ := grid_hypotheses N h
  obtain ⟨F, hF0, hF⟩ := sixPointRule.exists_transport_solution (gridD N h) ε F₀
  refine ⟨F, hF0, hF τ, fun t ht => ?_⟩
  have hK' : ‖regM (gridD N h) * ((F 0 - isoM _ (sixPointRule.density (F 0))) *
      sixPointRule.weight)‖ ≤ ε * K := by rwa [hF0]
  have := sixPointRule.linearTransport_rank_four hskew hcomm zero_le_one hM hε (hF τ) hK' ht
  rwa [hF0] at this

end GridInstance

end Instance


/-! ### Section 2: the rank of linearized Vlasov–Maxwell -/

section LinearizedVlasov

open MeasureTheory

/-- `ℝ³`, for positions and velocities. -/
abbrev R3 : Type := Fin 3 → ℝ

/-- The partial derivative `∂ᵢ Bⱼ`. -/
noncomputable def pd (B : R3 → R3) (x : R3) (i j : Fin 3) : ℝ :=
  fderiv ℝ B x (Pi.single i 1) j

/-- The curl `∇ × B`. -/
noncomputable def curl (B : R3 → R3) (x : R3) : R3 :=
  ![pd B x 1 2 - pd B x 2 1, pd B x 2 0 - pd B x 0 2, pd B x 0 1 - pd B x 1 0]

/-- The divergence `∇ · B`. -/
noncomputable def divg (B : R3 → R3) (x : R3) : ℝ := ∑ i, pd B x i i

/-- The linearized Vlasov–Maxwell system around a homogeneous equilibrium `f₀ (v)`, Sec. 3 of [61]
= arXiv 1902.00424, which arXiv 2412.05912, Sec. 2, cites: `f` is the perturbation `f⁽¹⁾`, and
`E`, `B` are `E⁽¹⁾`, `B⁽¹⁾`. The Gauss laws, which [61] imposes on the initial value, are required
for all `t`. Integrability is required, so that the moments mean what they say. -/
structure IsLinearizedVM (f₀ : R3 → ℝ) (f : ℝ → R3 → R3 → ℝ) (E B : ℝ → R3 → R3) : Prop where
  integrable : ∀ t x, Integrable (f t x)
  integrable_moment : ∀ t x i, Integrable fun v => v i * f t x v
  vlasov : ∀ t x v, deriv (fun s => f s x v) t + fderiv ℝ (fun y => f t y v) x v -
    fderiv ℝ f₀ v (E t x + v ⨯₃ B t x) = 0
  ampere : ∀ t x i, deriv (fun s => E s x i) t =
    curl (B t) x i - ∫ v, v i * f₀ v - ∫ v, v i * f t x v
  faraday : ∀ t x i, deriv (fun s => B s x i) t = -curl (E t) x i
  gauss : ∀ t x, divg (E t) x = -∫ v, f t x v
  gauss_magnetic : ∀ t x, divg (B t) x = 0

/-- The Maxwellian `(2π)^{-3/2} exp (-|v|²/2)`, written coordinate by coordinate. -/
noncomputable def maxw3 (v : R3) : ℝ :=
  ((2 * Real.pi) ^ (3 / 2 : ℝ))⁻¹ * Real.exp (-(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) / 2)

lemma maxw3_pos (v : R3) : 0 < maxw3 v := by
  have := Real.pi_pos
  unfold maxw3
  positivity

/-- The two-mode profile `cos s + cos 2 s`. -/
noncomputable def wave (s : ℝ) : ℝ := Real.cos s + Real.cos (2 * s)

/-- The derivative of `wave`. -/
noncomputable def wave' (s : ℝ) : ℝ := -Real.sin s - 2 * Real.sin (2 * s)

lemma hasDerivAt_wave (s : ℝ) : HasDerivAt wave (wave' s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun s => Real.cos s + Real.cos (2 * s))
      (-Real.sin s + -Real.sin (2 * s) * 2) s :=
    (Real.hasDerivAt_cos s).add ((Real.hasDerivAt_cos (2 * s)).comp s h1)
  refine HasDerivAt.congr_deriv (f := wave) h2 ?_
  simp only [wave']
  ring

/-- The perturbation `α (cos (x₁ - v₁ t) + cos 2 (x₁ - v₁ t)) v₂ v₃ M (v)`: two wave numbers in
`x₁`, `2π`-periodic in `x`, and free of charge and current since it is odd in `v₂` and in `v₃`. -/
noncomputable def pert (α t : ℝ) (x v : R3) : ℝ :=
  α * wave (x 0 - t * v 0) * (v 1 * v 2) * maxw3 v

/-- `pert` is `2π`-periodic in each space direction, so the counterexample of arXiv 2412.05912,
Sec. 2, lives on the torus, the usual domain of the test problems. -/
theorem pert_periodic (α t : ℝ) (x v : R3) (i : Fin 3) :
    pert α t (x + (2 * Real.pi) • Pi.single i 1) v = pert α t x v := by
  have hw : ∀ s, wave (s + 2 * Real.pi) = wave s := by
    intro s
    simp only [wave, mul_add]
    rw [Real.cos_add_two_pi, show 2 * s + 2 * (2 * Real.pi) = 2 * s + 2 * Real.pi + 2 * Real.pi by
      ring, Real.cos_add_two_pi, Real.cos_add_two_pi]
  unfold pert
  congr 3
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one]
    rw [show x 0 + 2 * Real.pi - t * v 0 = x 0 - t * v 0 + 2 * Real.pi by ring]
    exact hw _
  · simp
  · simp

/-- Reflection of one coordinate. -/
def flipC (k : Fin 3) (v : R3) : R3 := fun i => if i = k then -v i else v i

lemma flipC_flipC (k : Fin 3) (v : R3) : flipC k (flipC k v) = v := by
  funext i
  by_cases h : i = k <;> simp [flipC, h]

lemma measurePreserving_flipC (k : Fin 3) : MeasurePreserving (flipC k) volume volume := by
  have h : ∀ i : Fin 3, MeasurePreserving (fun s : ℝ => if i = k then -s else s) volume volume := by
    intro i
    by_cases hi : i = k
    · simpa [hi] using Measure.measurePreserving_neg (volume : Measure ℝ)
    · simp only [hi, ite_false]
      exact MeasurePreserving.id _
  exact measurePreserving_pi _ _ h

/-- The reflection, as a measurable equivalence. -/
def flipE (k : Fin 3) : R3 ≃ᵐ R3 where
  toFun := flipC k
  invFun := flipC k
  left_inv := flipC_flipC k
  right_inv := flipC_flipC k
  measurable_toFun := (measurePreserving_flipC k).measurable
  measurable_invFun := (measurePreserving_flipC k).measurable

/-- An integrand odd in one coordinate has integral zero (arXiv 2412.05912, Sec. 2, used for the
moments of the witness). -/
theorem integral_eq_zero_of_flip (k : Fin 3) {g : R3 → ℝ} (h : ∀ v, g (flipC k v) = -g v) :
    ∫ v, g v = 0 := by
  have h1 : ∫ v, g (flipC k v) = ∫ v, g v :=
    (measurePreserving_flipC k).integral_comp (flipE k).measurableEmbedding g
  simp only [h, integral_neg] at h1
  linarith

/-- The moments of `s ↦ sⁿ exp (-s²/2)` converge. -/
lemma integrable_gaussPow (n : ℕ) :
    Integrable fun s : ℝ => s ^ n * Real.exp (-s ^ 2 / 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := (n : ℝ))
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  refine h.congr (ae_of_all _ fun s => ?_)
  simp only [Real.rpow_natCast]
  congr 2
  ring

/-- A product of three integrable functions of the three coordinates. -/
lemma integrable_prod3 {a b c : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hc : Integrable c) : Integrable fun v : R3 => a (v 0) * b (v 1) * c (v 2) := by
  have h := Integrable.fintype_prod (ι := Fin 3) (f := ![a, b, c]) (μ := fun _ => volume)
    (fun i => by fin_cases i <;> simpa)
  refine h.congr (ae_of_all _ fun v => ?_)
  simp [Fin.prod_univ_three]

/-- `pert`, with polynomial weights, is integrable. -/
lemma integrable_pert_weight (α t : ℝ) (x : R3) (p q r : ℕ) :
    Integrable fun v : R3 => v 0 ^ p * v 1 ^ q * v 2 ^ r * pert α t x v := by
  have hb : Integrable fun s : ℝ => wave (x 0 - t * s) * (s ^ p * Real.exp (-s ^ 2 / 2)) := by
    refine (integrable_gaussPow p).bdd_mul (c := 2) ?_ ?_
    · have hc : Continuous fun s : ℝ => wave (x 0 - t * s) := by
        unfold wave
        fun_prop
      exact hc.aestronglyMeasurable
    · refine ae_of_all _ fun s => ?_
      have h1 := Real.abs_cos_le_one (x 0 - t * s)
      have h2 := Real.abs_cos_le_one (2 * (x 0 - t * s))
      simp only [wave, Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (by linarith)
  have h := (integrable_prod3 hb (integrable_gaussPow (q + 1))
    (integrable_gaussPow (r + 1))).const_mul (α * ((2 * Real.pi) ^ (3 / 2 : ℝ))⁻¹)
  refine h.congr (ae_of_all _ fun v => ?_)
  have e : Real.exp (-(v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) / 2) =
      Real.exp (-v 0 ^ 2 / 2) * Real.exp (-v 1 ^ 2 / 2) * Real.exp (-v 2 ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [pert, maxw3, e]
  ring

/-- The perturbation has no charge. -/
lemma integral_pert (α t : ℝ) (x : R3) : ∫ v, pert α t x v = 0 := by
  refine integral_eq_zero_of_flip 1 fun v => ?_
  simp [pert, flipC, maxw3]

/-- The perturbation has no current. -/
lemma integral_moment_pert (α t : ℝ) (x : R3) (i : Fin 3) :
    ∫ v, v i * pert α t x v = 0 := by
  fin_cases i
  · refine integral_eq_zero_of_flip 1 fun v => ?_
    simp [pert, flipC, maxw3]
  · refine integral_eq_zero_of_flip 2 fun v => ?_
    simp [pert, flipC, maxw3]
  · refine integral_eq_zero_of_flip 1 fun v => ?_
    simp [pert, flipC, maxw3]

/-- The Maxwellian has no current. -/
lemma integral_moment_maxw3 (i : Fin 3) : ∫ v, v i * maxw3 v = 0 := by
  refine integral_eq_zero_of_flip i fun v => ?_
  fin_cases i <;> simp [flipC, maxw3]

/-- **The witness** (arXiv 2412.05912, Sec. 2, the claim about [61]). `pert α` is an exact solution
of the linearized Vlasov–Maxwell system around the Maxwellian, with `E = B = 0`: it has neither
charge nor current, so free streaming solves the system, and for either sign convention of the
current in [61]. -/
theorem isLinearizedVM_pert (α : ℝ) :
    IsLinearizedVM maxw3 (pert α) (fun _ _ => 0) (fun _ _ => 0) where
  integrable t x := by
    simpa using integrable_pert_weight α t x 0 0 0
  integrable_moment t x i := by
    fin_cases i
    · simpa using integrable_pert_weight α t x 1 0 0
    · simpa using integrable_pert_weight α t x 0 1 0
    · simpa using integrable_pert_weight α t x 0 0 1
  vlasov t x v := by
    set c := α * ((v 1 * v 2) * maxw3 v) with hc
    have h1 : HasDerivAt (fun s => pert α s x v) (c * (wave' (x 0 - t * v 0) * -v 0)) t := by
      have h0 : HasDerivAt (fun s : ℝ => x 0 - s * v 0) (-v 0) t := by
        simpa using ((hasDerivAt_id t).mul_const (v 0)).const_sub (x 0)
      have h2 := ((hasDerivAt_wave _).comp t h0).const_mul c
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      simp only [pert, hc, Function.comp]
      ring
    have h3 : HasFDerivAt (fun y : R3 => pert α t y v)
        ((c * wave' (x 0 - t * v 0)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) x := by
      have h0 : HasFDerivAt (fun y : R3 => y 0 - t * v 0)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) x :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt.sub_const _
      have h2 := ((hasDerivAt_wave _).comp_hasFDerivAt x h0).const_mul c
      refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_fderiv ?_
      · simp only [pert, hc, Function.comp]
        ring
      · ext w
        simp [mul_assoc]
    rw [h1.deriv, h3.fderiv]
    simp
    ring
  ampere t x i := by
    have h2 := integral_moment_pert α t x i
    simp only [h2]
    fin_cases i
    · simpa [curl, pd] using integral_moment_maxw3 0
    · simpa [curl, pd] using integral_moment_maxw3 1
    · simpa [curl, pd] using integral_moment_maxw3 2
  faraday t x i := by
    fin_cases i <;> simp [curl, pd]
  gauss t x := by
    rw [integral_pert]
    simp [divg, pd]
  gauss_magnetic t x := by
    simp [divg, pd]

/-- At `t = 0` the perturbation is one product: rank one (arXiv 2412.05912, Sec. 2). -/
theorem pert_rank_zero (α : ℝ) : HasSepRankLE ℝ (pert α 0) 1 := by
  refine ⟨fun _ x => α * wave (x 0), fun _ v => (v 1 * v 2) * maxw3 v, fun x v => ?_⟩
  simp [pert]
  ring

/-- At `t = 0` the whole distribution `M + pert` has rank at most two (arXiv 2412.05912, Sec. 2). -/
theorem full_rank_zero (α : ℝ) : HasSepRankLE ℝ (fun x v => maxw3 v + pert α 0 x v) 2 := by
  refine ⟨![fun _ => 1, fun x => α * wave (x 0)], ![maxw3, fun v => (v 1 * v 2) * maxw3 v],
    fun x v => ?_⟩
  simp [pert]
  ring

/-- The sampling angles `0, π/2, π, 3π/2`. -/
noncomputable def θ₄ : Fin 4 → ℝ := ![0, Real.pi / 2, Real.pi, 3 * Real.pi / 2]

/-- The values of `cos`, `sin`, on `θ₄`, and of the double angle. -/
lemma table_θ₄ (i : Fin 4) :
    Real.cos (θ₄ i) = ![1, 0, -1, 0] i ∧ Real.sin (θ₄ i) = ![0, 1, 0, -1] i ∧
      Real.cos (2 * θ₄ i) = ![1, -1, 1, -1] i ∧ Real.sin (2 * θ₄ i) = 0 := by
  have h3c : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi]
    simp
  have h3s : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi]
    simp
  have h6c : Real.cos (2 * (3 * Real.pi / 2)) = -1 := by
    rw [show 2 * (3 * Real.pi / 2) = Real.pi + 2 * Real.pi by ring, Real.cos_add_two_pi]
    simp
  have h6s : Real.sin (2 * (3 * Real.pi / 2)) = 0 := by
    rw [show 2 * (3 * Real.pi / 2) = Real.pi + 2 * Real.pi by ring, Real.sin_add_two_pi]
    simp
  have h2c : Real.cos (2 * (Real.pi / 2)) = -1 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring]
    simp
  have h2s : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring]
    simp
  fin_cases i <;> simp [θ₄, h3c, h3s, h6c, h6s, h2c, h2s]

/-- `wave (θ_i - θ_j)` is a circulant table. -/
noncomputable def waveTable : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, -1, 0, -1; -1, 2, -1, 0; 0, -1, 2, -1; -1, 0, -1, 2]

lemma wave_table (i j : Fin 4) : wave (θ₄ i - θ₄ j) = waveTable i j := by
  obtain ⟨c1, s1, d1, e1⟩ := table_θ₄ i
  obtain ⟨c2, s2, d2, e2⟩ := table_θ₄ j
  have h : wave (θ₄ i - θ₄ j) =
      Real.cos (θ₄ i) * Real.cos (θ₄ j) + Real.sin (θ₄ i) * Real.sin (θ₄ j) +
      (Real.cos (2 * θ₄ i) * Real.cos (2 * θ₄ j) + Real.sin (2 * θ₄ i) * Real.sin (2 * θ₄ j)) := by
    rw [wave, mul_sub, Real.cos_sub, Real.cos_sub]
  rw [h, c1, s1, d1, e1, c2, s2, d2, e2]
  fin_cases i <;> fin_cases j <;> norm_num [waveTable]

/-- The sample points of the rank lower bound. -/
noncomputable def xs₄ (i : Fin 4) : R3 := ![θ₄ i, 0, 0]

/-- The sample velocities of the rank lower bound: `t v₁ = θ_j`, `v₂ = v₃ = 1`. -/
noncomputable def vs₄ (t : ℝ) (j : Fin 4) : R3 := ![θ₄ j / t, 1, 1]

lemma pert_sample {α t : ℝ} (ht : t ≠ 0) (i j : Fin 4) :
    pert α t (xs₄ i) (vs₄ t j) = α * waveTable i j * maxw3 (vs₄ t j) := by
  have e : t * (θ₄ j / t) = θ₄ j := by field_simp
  simp only [pert, xs₄, vs₄]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [e, wave_table]
  ring

/-- The sample determinant of the whole distribution is nonzero. -/
lemma full_sample_det_ne_zero {α t : ℝ} (hα : α ≠ 0) (ht : t ≠ 0) :
    (sample (fun x v => maxw3 v + pert α t x v) xs₄ (vs₄ t)).det ≠ 0 := by
  set m : Fin 4 → ℝ := fun j => maxw3 (vs₄ t j) with hm
  set K : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => 1 + α * waveTable i j with hK
  have hfac : sample (fun x v => maxw3 v + pert α t x v) xs₄ (vs₄ t) = K * Matrix.diagonal m := by
    ext i j
    simp only [sample, Matrix.of_apply, Matrix.mul_diagonal, hK, pert_sample ht, hm]
    ring
  have hK' : K = !![1 + 2 * α, 1 - α, 1, 1 - α; 1 - α, 1 + 2 * α, 1 - α, 1;
      1, 1 - α, 1 + 2 * α, 1 - α; 1 - α, 1, 1 - α, 1 + 2 * α] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hK, waveTable] <;> ring
  have hdet : K.det = 64 * α ^ 3 := by
    rw [hK']
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal, hdet]
  refine mul_ne_zero (by positivity) ?_
  exact Finset.prod_ne_zero_iff.2 fun j _ => (maxw3_pos _).ne'

/-- **The whole distribution has rank at least four** (arXiv 2412.05912, Sec. 2). For all `α ≠ 0`,
`t ≠ 0`, the solution `M + pert` of the linearized system has no separation of rank `3`. -/
theorem full_not_rank_le_three {α t : ℝ} (hα : α ≠ 0) (ht : t ≠ 0) :
    ¬ HasSepRankLE ℝ (fun x v => maxw3 v + pert α t x v) 3 :=
  not_hasRankLEOver_of_det_ne_zero xs₄ (vs₄ t) (full_sample_det_ne_zero hα ht)

/-- `full_not_rank_le_three` over `ℂ` (arXiv 2412.05912, Sec. 2; [61] writes complex modes). -/
theorem full_not_complex_rank_le_three {α t : ℝ} (hα : α ≠ 0) (ht : t ≠ 0) :
    ¬ HasSepRankLE ℂ (fun x v => ((maxw3 v + pert α t x v : ℝ) : ℂ)) 3 :=
  not_hasRankLEOver_complex_of_det_ne_zero xs₄ (vs₄ t) (full_sample_det_ne_zero hα ht)

/-- **The perturbation has rank at least three** (arXiv 2412.05912, Sec. 2), for all `α ≠ 0`,
`t ≠ 0`. -/
theorem pert_not_rank_le_two {α t : ℝ} (hα : α ≠ 0) (ht : t ≠ 0) :
    ¬ HasSepRankLE ℝ (pert α t) 2 := by
  refine not_hasRankLEOver_of_det_ne_zero (fun i : Fin 3 => xs₄ i.castSucc)
    (fun j : Fin 3 => vs₄ t j.castSucc) ?_
  set m : Fin 3 → ℝ := fun j => maxw3 (vs₄ t j.castSucc) with hm
  set K : Matrix (Fin 3) (Fin 3) ℝ := !![2 * α, -α, 0; -α, 2 * α, -α; 0, -α, 2 * α] with hK
  have hfac : sample (pert α t) (fun i : Fin 3 => xs₄ i.castSucc)
      (fun j : Fin 3 => vs₄ t j.castSucc) = K * Matrix.diagonal m := by
    ext i j
    simp only [sample, Matrix.of_apply, Matrix.mul_diagonal, pert_sample ht, hm]
    congr 1
    fin_cases i <;> fin_cases j <;> simp [hK, waveTable] <;> ring
  have hdet : K.det = 4 * α ^ 3 := by
    simp only [hK, Matrix.det_fin_three]
    simp
    ring
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal, hdet]
  refine mul_ne_zero (by positivity) ?_
  exact Finset.prod_ne_zero_iff.2 fun j _ => (maxw3_pos _).ne'

/-- **The bound of [61] for this solution** (arXiv 2412.05912, Sec. 2, citing [61]). It has five
Fourier modes in `x`, namely `0, ±1, ±2`, and rank at most `5`: the bound `m + 1` of [61] = arXiv
1902.00424, Sec. 3, eq. (9), with `m = 4` excited modes, is what holds, and it depends on the
modes, not on the rank of the initial value. -/
theorem full_rank_le_five (α t : ℝ) : HasSepRankLE ℝ (fun x v => maxw3 v + pert α t x v) 5 := by
  refine ⟨![fun _ => 1, fun x => α * Real.cos (x 0), fun x => α * Real.sin (x 0),
    fun x => α * Real.cos (2 * x 0), fun x => α * Real.sin (2 * x 0)],
    ![maxw3, fun v => Real.cos (t * v 0) * (v 1 * v 2) * maxw3 v,
      fun v => Real.sin (t * v 0) * (v 1 * v 2) * maxw3 v,
      fun v => Real.cos (2 * (t * v 0)) * (v 1 * v 2) * maxw3 v,
      fun v => Real.sin (2 * (t * v 0)) * (v 1 * v 2) * maxw3 v], fun x v => ?_⟩
  simp only [Fin.sum_univ_five, pert, wave, Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, one_mul, Matrix.cons_val_one, Matrix.cons_val]
  rw [mul_sub, Real.cos_sub, Real.cos_sub]
  ring

/-- **The claim of arXiv 2412.05912, Sec. 2, is false, for the distribution**: "if the rank of the
initial value is `r`, then the linearized solution is at most rank `r + 1`". With the linearized
Vlasov–Maxwell system of [61], around the Maxwellian, the full solution `f₀ + f⁽¹⁾` starts with
rank at most `2`, and for `t ≠ 0` it does not have rank `3`. [61] proves `m + 1` for `m` Fourier
modes, which is a different number: see `full_rank_le_five`. -/
theorem linearized_rank_claim_false :
    ¬ ∀ (f₀ : R3 → ℝ) (f : ℝ → R3 → R3 → ℝ) (E B : ℝ → R3 → R3), IsLinearizedVM f₀ f E B →
      ∀ r, HasSepRankLE ℝ (fun x v => f₀ v + f 0 x v) r →
        ∀ t, HasSepRankLE ℝ (fun x v => f₀ v + f t x v) (r + 1) := fun h =>
  full_not_rank_le_three one_ne_zero one_ne_zero
    (h maxw3 (pert 1) _ _ (isLinearizedVM_pert 1) 2 (full_rank_zero 1) 1)

/-- **The claim of arXiv 2412.05912, Sec. 2, is false, for the perturbation**: the same statement
for `f⁽¹⁾` alone, which starts with rank one and does not have rank two for `t ≠ 0`. -/
theorem linearized_rank_claim_false_perturbation :
    ¬ ∀ (f₀ : R3 → ℝ) (f : ℝ → R3 → R3 → ℝ) (E B : ℝ → R3 → R3), IsLinearizedVM f₀ f E B →
      ∀ r, HasSepRankLE ℝ (f 0) r → ∀ t, HasSepRankLE ℝ (f t) (r + 1) := fun h =>
  pert_not_rank_le_two one_ne_zero one_ne_zero
    (h maxw3 (pert 1) _ _ (isLinearizedVM_pert 1) 1 (pert_rank_zero 1) 1)

end LinearizedVlasov

/-! ### Section 2: the example `(1 + α cos (k x)) f^eq (v)`, linearized Vlasov–Poisson -/

section Lorentzian

open MeasureTheory FourierTransform

/-- The Lorentzian equilibrium `1 / (π (1 + v²))`, for which linear Landau damping is explicit. -/
noncomputable def lor (v : ℝ) : ℝ := (Real.pi * (1 + v ^ 2))⁻¹

/-- The derivative of `lor`. -/
noncomputable def lor' (v : ℝ) : ℝ := -(2 * v / (1 + v ^ 2)) * lor v

lemma one_add_sq_pos (v : ℝ) : 0 < 1 + v ^ 2 := by positivity

lemma lor_pos (v : ℝ) : 0 < lor v := by
  have := Real.pi_pos
  unfold lor
  positivity

lemma lor_neg (v : ℝ) : lor (-v) = lor v := by simp [lor]

lemma lor'_neg (v : ℝ) : lor' (-v) = -lor' v := by
  simp only [lor', lor_neg, neg_sq]
  ring

lemma lor'_zero : lor' 0 = 0 := by simp [lor']

lemma hasDerivAt_lor (v : ℝ) : HasDerivAt lor (lor' v) v := by
  have h1 : HasDerivAt (fun v : ℝ => Real.pi * (1 + v ^ 2)) (Real.pi * (2 * v)) v := by
    have h0 : HasDerivAt (fun v : ℝ => 1 + v ^ 2) (2 * v) v := by
      simpa using ((hasDerivAt_id v).pow 2).const_add 1
    exact h0.const_mul Real.pi
  have hne : Real.pi * (1 + v ^ 2) ≠ 0 := (mul_pos Real.pi_pos (one_add_sq_pos v)).ne'
  have h2 := h1.inv hne
  refine HasDerivAt.congr_deriv (f := lor) h2 ?_
  have := one_add_sq_pos v
  simp only [lor', lor]
  field_simp

lemma integrable_lor : Integrable lor := by
  have h := integrable_inv_one_add_sq.const_mul Real.pi⁻¹
  refine h.congr (ae_of_all _ fun v => ?_)
  simp only [lor, mul_inv]

lemma abs_two_mul_div_le (v : ℝ) : |2 * v / (1 + v ^ 2)| ≤ 1 := by
  have h := one_add_sq_pos v
  rw [abs_div, abs_of_pos h, div_le_one h, abs_mul, abs_two]
  nlinarith [sq_abs v, sq_nonneg (|v| - 1)]

lemma integrable_lor' : Integrable lor' := by
  refine integrable_lor.bdd_mul (c := 1) (f := fun v => -(2 * v / (1 + v ^ 2))) ?_ ?_
  · have hc : Continuous fun v : ℝ => -(2 * v / (1 + v ^ 2)) := by
      refine Continuous.neg (Continuous.div (by fun_prop) (by fun_prop) fun v => ?_)
      exact (one_add_sq_pos v).ne'
    exact hc.aestronglyMeasurable
  · exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_neg]
      exact abs_two_mul_div_le v

/-- `e^{-|x|}`, complex valued. -/
private noncomputable def expAbs (x : ℝ) : ℂ := ((Real.exp (-|x|) : ℝ) : ℂ)

private lemma continuous_expAbs : Continuous expAbs := by
  unfold expAbs
  fun_prop

private lemma expAbs_Ioi {z : ℂ} {x : ℝ} (hx : 0 < x) :
    Complex.exp (z * x) * expAbs x = Complex.exp ((z - 1) * x) := by
  rw [expAbs, abs_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma expAbs_Iic {z : ℂ} {x : ℝ} (hx : x ≤ 0) :
    Complex.exp (z * x) * expAbs x = Complex.exp ((z + 1) * x) := by
  rw [expAbs, abs_of_nonpos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Laplace-type integral of `e^{-|x|}` along the imaginary axis. -/
private lemma integral_exp_mul_expAbs {z : ℂ} (hz : z.re = 0) :
    Integrable (fun x : ℝ => Complex.exp (z * x) * expAbs x) ∧
      ∫ x : ℝ, Complex.exp (z * x) * expAbs x = 1 / (z + 1) + 1 / (1 - z) := by
  have ha : (z - 1).re < 0 := by simp [hz]
  have hb : 0 < (z + 1).re := by simp [hz]
  have hneg : EqOn (fun x : ℝ => Complex.exp ((z + 1) * x))
      (fun x : ℝ => Complex.exp (z * x) * expAbs x) (Iic 0) :=
    fun x hx => (expAbs_Iic hx).symm
  have hpos : EqOn (fun x : ℝ => Complex.exp ((z - 1) * x))
      (fun x : ℝ => Complex.exp (z * x) * expAbs x) (Ioi 0) :=
    fun x hx => (expAbs_Ioi hx).symm
  have h1 : IntegrableOn (fun x : ℝ => Complex.exp (z * x) * expAbs x) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hb 0).congr_fun hneg measurableSet_Iic
  have h2 : IntegrableOn (fun x : ℝ => Complex.exp (z * x) * expAbs x) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi ha 0).congr_fun hpos measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · have := h1.union h2
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  · rw [← intervalIntegral.integral_Iic_add_Ioi h1 h2,
      ← setIntegral_congr_fun measurableSet_Iic hneg,
      ← setIntegral_congr_fun measurableSet_Ioi hpos, integral_exp_mul_complex_Iic hb 0,
      integral_exp_mul_complex_Ioi ha 0]
    have h3 : z - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp [hz] at this
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [neg_div, ← div_neg, neg_sub]

private lemma integrable_expAbs : Integrable expAbs := by
  simpa using (integral_exp_mul_expAbs (z := 0) (by simp)).1

/-- The Fourier transform of `e^{-|x|}`. -/
private lemma fourier_expAbs (w : ℝ) :
    𝓕 expAbs w = ((2 * (1 + (2 * Real.pi * w) ^ 2)⁻¹ : ℝ) : ℂ) := by
  set z : ℂ := ((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I with hz
  have hre : z.re = 0 := by simp [hz]
  have h2 : z ^ 2 = -(((2 * Real.pi * w : ℝ) : ℂ) ^ 2) := by
    rw [hz, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hp : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp [hre] at this
  have hm : 1 - z ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp [hre] at this
  have hval := (integral_exp_mul_expAbs hre).2
  have hsame : 𝓕 expAbs w = ∫ x : ℝ, Complex.exp (z * x) * expAbs x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [smul_eq_mul]
    congr 2
    rw [hz]
    push_cast
    ring
  have hden : (1 : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) + (2 * Real.pi * w) ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  rw [hsame, hval]
  push_cast
  push_cast at hden h2
  have e : (1 + z) * (1 - z) = 1 + (2 * (Real.pi : ℂ) * w) ^ 2 := by
    have : (1 + z) * (1 - z) = 1 - z ^ 2 := by ring
    rw [this, h2]
    ring
  have hp' : 1 + z ≠ 0 := by rwa [add_comm]
  rw [add_comm z 1, ← e] at *
  field_simp
  ring

private lemma integrable_fourier_expAbs : Integrable (𝓕 expAbs) := by
  have h1 : Integrable fun w : ℝ => (1 + (2 * Real.pi * w) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have h2 := (h1.const_mul 2).ofReal (𝕜 := ℂ)
  exact h2.congr (ae_of_all _ fun w => (fourier_expAbs w).symm)

/-- **The Fourier transform of the Lorentzian** (arXiv 2412.05912, Sec. 2, used for the example):
`∫ cos (s v) / (π (1 + v²)) dv = e^{-|s|}`, by Fourier inversion. Mathlib has the Cauchy
distribution, not this formula. -/
theorem integral_cos_mul_lor (s : ℝ) : ∫ v, Real.cos (s * v) * lor v = Real.exp (-|s|) := by
  have hinv := congrFun (continuous_expAbs.fourierInv_fourier_eq integrable_expAbs
    integrable_fourier_expAbs) s
  rw [Real.fourierInv_eq'] at hinv
  set G : ℝ → ℝ := fun v => Real.cos (v * s) * (2 * (1 + v ^ 2)⁻¹) with hG
  have hint : Integrable fun v : ℝ =>
      Complex.exp (((2 * Real.pi * ⟪v, s⟫ : ℝ) : ℂ) * Complex.I) • 𝓕 expAbs v := by
    refine integrable_fourier_expAbs.bdd_mul (c := 1) ?_ ?_
    · have hc : Continuous fun v : ℝ =>
          Complex.exp (((2 * Real.pi * ⟪v, s⟫ : ℝ) : ℂ) * Complex.I) := by
        simp only [real_inner_comm]
        fun_prop
      exact hc.aestronglyMeasurable
    · exact ae_of_all _ fun v => by
        rw [Complex.norm_exp_ofReal_mul_I]
  have hre : ∫ v : ℝ, G (2 * Real.pi * v) = Real.exp (-|s|) := by
    have h1 := Complex.reCLM.integral_comp_comm hint
    have h2 := congrArg Complex.reCLM hinv
    rw [← h1] at h2
    simp only [Complex.reCLM_apply] at h2
    have h3 : Complex.re (expAbs s) = Real.exp (-|s|) := by
      simp only [expAbs, Complex.ofReal_re]
    rw [h3] at h2
    rw [← h2]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    change G (2 * Real.pi * v) =
      (Complex.exp (((2 * Real.pi * ⟪v, s⟫ : ℝ) : ℂ) * Complex.I) • 𝓕 expAbs v).re
    have hin : ⟪v, s⟫ = v * s := by simp [mul_comm]
    rw [fourier_expAbs, smul_eq_mul, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, hin]
    simp only [hG]
    rw [mul_assoc]
  have hcv := Measure.integral_comp_mul_left G (2 * Real.pi)
  rw [hre, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), smul_eq_mul] at hcv
  rw [hcv, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  have := Real.pi_pos
  have := one_add_sq_pos v
  simp only [hG, lor, mul_comm v s]
  field_simp

/-- Integration by parts: `∫ sin (s v) f₀' (v) dv = -s e^{-|s|}` for the Lorentzian (arXiv
2412.05912, Sec. 2, used for the example). -/
theorem integral_sin_mul_lor' (s : ℝ) :
    ∫ v, Real.sin (s * v) * lor' v = -s * Real.exp (-|s|) := by
  have hu : ∀ v, HasDerivAt (fun v => Real.sin (s * v)) (Real.cos (s * v) * s) v := fun v => by
    have h : HasDerivAt (fun v : ℝ => s * v) s v := by simpa using (hasDerivAt_id v).const_mul s
    exact h.sin
  have bddc : ∀ {g : ℝ → ℝ} (_ : Continuous g) (_ : ∀ v, |g v| ≤ 1) {h : ℝ → ℝ}
      (_ : Integrable h), Integrable fun v => g v * h v := by
    intro g hg hb h hh
    exact hh.bdd_mul (c := 1) hg.aestronglyMeasurable (ae_of_all _ fun v => by simpa using hb v)
  have h1 : Integrable (fun v => Real.sin (s * v) * lor' v) :=
    bddc (by fun_prop) (fun v => Real.abs_sin_le_one _) integrable_lor'
  have h2 : Integrable (fun v => Real.cos (s * v) * lor v) :=
    bddc (by fun_prop) (fun v => Real.abs_cos_le_one _) integrable_lor
  have h3 : Integrable (fun v => Real.sin (s * v) * lor v) :=
    bddc (by fun_prop) (fun v => Real.abs_sin_le_one _) integrable_lor
  have h4 : Integrable (fun v => Real.cos (s * v) * s * lor v) := by
    refine (h2.mul_const s).congr (ae_of_all _ fun v => ?_)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (fun v _ => hu v)
    (fun v _ => hasDerivAt_lor v) h1 h4 h3
  rw [h]
  have e : ∫ v, Real.cos (s * v) * s * lor v = s * ∫ v, Real.cos (s * v) * lor v := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun v => by ring)
  rw [e, integral_cos_mul_lor]
  ring

/-- The linearized Vlasov–Poisson system around `f₀ (v)` in one space and one velocity dimension,
with the signs of [61] = arXiv 1902.00424, Sec. 3: `∂ₜ f + v ∂ₓ f - E f₀' = 0`, `∂ₓ E = -∫ f dv`.
Here `f` is the perturbation `f⁽¹⁾`, and solutions are asked for on `t ≥ 0`. -/
structure IsLinearizedVP (f₀ : ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ) (E : ℝ → ℝ → ℝ) : Prop where
  integrable : ∀ t, 0 ≤ t → ∀ x, Integrable (f t x)
  vlasov : ∀ t, 0 ≤ t → ∀ x v,
    deriv (fun s => f s x v) t + v * deriv (fun y => f t y v) x - E t x * deriv f₀ v = 0
  gauss : ∀ t, 0 ≤ t → ∀ x, deriv (E t) x = -∫ v, f t x v

/-- The amplitude of the electric field for the Lorentzian: `-e^{-k t} cos t / k`. -/
noncomputable def eL (k t : ℝ) : ℝ := -(k⁻¹ * Real.exp (-k * t) * Real.cos t)

/-- The Duhamel integral `∫₀ᵗ cos (k v (t - τ)) e (τ) dτ`. -/
noncomputable def cL (k t v : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, Real.cos (k * v * (t - τ)) * eL k τ

/-- The Duhamel integral `∫₀ᵗ sin (k v (t - τ)) e (τ) dτ`. -/
noncomputable def sL (k t v : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, Real.sin (k * v * (t - τ)) * eL k τ

/-- The coefficient of `cos (k x)`. -/
noncomputable def aL (k t v : ℝ) : ℝ := Real.cos (k * v * t) * lor v - lor' v * sL k t v

/-- The coefficient of `sin (k x)`. -/
noncomputable def bL (k t v : ℝ) : ℝ := Real.sin (k * v * t) * lor v + lor' v * cL k t v

/-- The perturbation `α (cos (k x) a (t, v) + sin (k x) b (t, v))`. -/
noncomputable def landauPert (k α t x v : ℝ) : ℝ :=
  α * (Real.cos (k * x) * aL k t v + Real.sin (k * x) * bL k t v)

/-- The electric field `α sin (k x) e (t)`. -/
noncomputable def landauField (k α t x : ℝ) : ℝ := α * Real.sin (k * x) * eL k t

/-- The whole distribution, `f^eq + f⁽¹⁾`. -/
noncomputable def landauFull (k α t x v : ℝ) : ℝ := lor v + landauPert k α t x v

lemma continuous_eL (k : ℝ) : Continuous (eL k) := by
  unfold eL
  fun_prop

/-- The time derivatives of the Duhamel integrals. -/
lemma hasDerivAt_cL_sL (k t v : ℝ) :
    HasDerivAt (fun s => cL k s v) (eL k t - k * v * sL k t v) t ∧
      HasDerivAt (fun s => sL k s v) (k * v * cL k t v) t := by
  set ω := k * v with hω
  have hc1 : Continuous fun τ => Real.cos (ω * τ) * eL k τ :=
    (by fun_prop : Continuous fun τ => Real.cos (ω * τ)).mul (continuous_eL k)
  have hc2 : Continuous fun τ => Real.sin (ω * τ) * eL k τ :=
    (by fun_prop : Continuous fun τ => Real.sin (ω * τ)).mul (continuous_eL k)
  set I₁ : ℝ → ℝ := fun s => ∫ τ in (0 : ℝ)..s, Real.cos (ω * τ) * eL k τ with hI₁
  set I₂ : ℝ → ℝ := fun s => ∫ τ in (0 : ℝ)..s, Real.sin (ω * τ) * eL k τ with hI₂
  have hd₁ : HasDerivAt I₁ (Real.cos (ω * t) * eL k t) t :=
    (hc1.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd₂ : HasDerivAt I₂ (Real.sin (ω * t) * eL k t) t :=
    (hc2.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hC : (fun s => cL k s v) =
      fun s => Real.cos (ω * s) * I₁ s + Real.sin (ω * s) * I₂ s := by
    funext s
    simp only [cL, hI₁, hI₂]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
        ((hc2.const_mul _).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [← hω, mul_sub, Real.cos_sub]
    ring
  have hS : (fun s => sL k s v) =
      fun s => Real.sin (ω * s) * I₁ s - Real.cos (ω * s) * I₂ s := by
    funext s
    simp only [sL, hI₁, hI₂]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hc1.const_mul _).intervalIntegrable _ _)
        ((hc2.const_mul _).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [← hω, mul_sub, Real.sin_sub]
    ring
  have hl : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hcos := hl.cos
  have hsin := hl.sin
  have hval : ∀ {u : ℝ → ℝ}, (u = fun s => cL k s v) → u t = cL k t v := fun h => by rw [h]
  have hCt : cL k t v = Real.cos (ω * t) * I₁ t + Real.sin (ω * t) * I₂ t := congrFun hC t
  have hSt : sL k t v = Real.sin (ω * t) * I₁ t - Real.cos (ω * t) * I₂ t := congrFun hS t
  have hsc := Real.sin_sq_add_cos_sq (ω * t)
  constructor
  · rw [hC]
    refine ((hcos.mul hd₁).add (hsin.mul hd₂)).congr_deriv ?_
    rw [hSt]
    linear_combination (eL k t) * hsc
  · rw [hS]
    refine ((hsin.mul hd₁).sub (hcos.mul hd₂)).congr_deriv ?_
    rw [hCt]
    ring

lemma hasDerivAt_aL (k t v : ℝ) :
    HasDerivAt (fun s => aL k s v) (-(k * v) * bL k t v) t := by
  have hl : HasDerivAt (fun s : ℝ => k * v * s) (k * v) t := by
    simpa using (hasDerivAt_id t).const_mul (k * v)
  refine ((hl.cos.mul_const (lor v)).sub
    ((hasDerivAt_cL_sL k t v).2.const_mul (lor' v))).congr_deriv ?_
  simp only [bL]
  ring

lemma hasDerivAt_bL (k t v : ℝ) :
    HasDerivAt (fun s => bL k s v) (k * v * aL k t v + eL k t * lor' v) t := by
  have hl : HasDerivAt (fun s : ℝ => k * v * s) (k * v) t := by
    simpa using (hasDerivAt_id t).const_mul (k * v)
  refine ((hl.sin.mul_const (lor v)).add
    ((hasDerivAt_cL_sL k t v).1.const_mul (lor' v))).congr_deriv ?_
  simp only [aL]
  ring

/-- `f = f^eq + f⁽¹⁾` solves the Vlasov equation, for all `t` (arXiv 2412.05912, Sec. 2, the
example `(1 + α cos (k x)) f^eq (v)`). -/
theorem landau_vlasov (k α t x v : ℝ) :
    deriv (fun s => landauPert k α s x v) t + v * deriv (fun y => landauPert k α t y v) x -
      landauField k α t x * deriv lor v = 0 := by
  have h1 : HasDerivAt (fun s => landauPert k α s x v)
      (α * (Real.cos (k * x) * (-(k * v) * bL k t v) +
        Real.sin (k * x) * (k * v * aL k t v + eL k t * lor' v))) t :=
    (((hasDerivAt_aL k t v).const_mul _).add ((hasDerivAt_bL k t v).const_mul _)).const_mul α
  have hl : HasDerivAt (fun y : ℝ => k * y) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have h2 : HasDerivAt (fun y => landauPert k α t y v)
      (α * (-Real.sin (k * x) * k * aL k t v + Real.cos (k * x) * k * bL k t v)) x :=
    ((hl.cos.mul_const _).add (hl.sin.mul_const _)).const_mul α
  rw [h1.deriv, h2.deriv, (hasDerivAt_lor v).deriv]
  simp only [landauField]
  ring

lemma abs_eL_le {k τ : ℝ} (hk : 0 < k) (hτ : 0 ≤ τ) : |eL k τ| ≤ k⁻¹ := by
  have hE : Real.exp (-k * τ) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith
  have hE0 := Real.exp_pos (-k * τ)
  have hk' : 0 < k⁻¹ := inv_pos.2 hk
  rw [eL, abs_neg, abs_mul, abs_mul, abs_of_pos hk', abs_of_pos hE0]
  calc k⁻¹ * Real.exp (-k * τ) * |Real.cos τ| ≤ k⁻¹ * 1 * 1 := by
        gcongr
        exact Real.abs_cos_le_one τ
    _ = k⁻¹ := by ring

lemma abs_cL_le {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) (v : ℝ) : |cL k t v| ≤ k⁻¹ * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := k⁻¹)
    (f := fun τ => Real.cos (k * v * (t - τ)) * eL k τ) fun τ hτ => by
      rw [uIoc_of_le ht] at hτ
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |Real.cos (k * v * (t - τ))| * |eL k τ| ≤ 1 * k⁻¹ := by
            gcongr
            · exact Real.abs_cos_le_one _
            · exact abs_eL_le hk hτ.1.le
        _ = k⁻¹ := one_mul _
  simpa [cL, Real.norm_eq_abs, abs_of_nonneg ht] using h

lemma abs_sL_le {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) (v : ℝ) : |sL k t v| ≤ k⁻¹ * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := k⁻¹)
    (f := fun τ => Real.sin (k * v * (t - τ)) * eL k τ) fun τ hτ => by
      rw [uIoc_of_le ht] at hτ
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |Real.sin (k * v * (t - τ))| * |eL k τ| ≤ 1 * k⁻¹ := by
            gcongr
            · exact Real.abs_sin_le_one _
            · exact abs_eL_le hk hτ.1.le
        _ = k⁻¹ := one_mul _
  simpa [sL, Real.norm_eq_abs, abs_of_nonneg ht] using h

lemma continuous_cL (k t : ℝ) : Continuous (cL k t) := by
  unfold cL
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 t
  have h := continuous_eL k
  simp only [Function.uncurry_def]
  fun_prop

lemma continuous_sL (k t : ℝ) : Continuous (sL k t) := by
  unfold sL
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 t
  have h := continuous_eL k
  simp only [Function.uncurry_def]
  fun_prop

/-- A continuous function bounded by `C` times an integrable function is integrable. -/
private lemma integrable_bdd {g h : ℝ → ℝ} {C : ℝ} (hg : Continuous g) (hC : ∀ v, |g v| ≤ C)
    (hh : Integrable h) : Integrable fun v => g v * h v :=
  hh.bdd_mul (c := C) hg.aestronglyMeasurable (ae_of_all _ fun v => by simpa using hC v)

lemma integrable_aL {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) : Integrable (aL k t) := by
  have h1 := integrable_bdd (g := fun v => Real.cos (k * v * t)) (C := 1) (by fun_prop)
    (fun v => Real.abs_cos_le_one _) integrable_lor
  have h2 := integrable_bdd (g := sL k t) (C := k⁻¹ * t) (continuous_sL k t)
    (abs_sL_le hk ht) integrable_lor'
  refine (h1.sub h2).congr (ae_of_all _ fun v => ?_)
  simp only [aL, Pi.sub_apply]
  ring

lemma integrable_bL {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) : Integrable (bL k t) := by
  have h1 := integrable_bdd (g := fun v => Real.sin (k * v * t)) (C := 1) (by fun_prop)
    (fun v => Real.abs_sin_le_one _) integrable_lor
  have h2 := integrable_bdd (g := cL k t) (C := k⁻¹ * t) (continuous_cL k t)
    (abs_cL_le hk ht) integrable_lor'
  refine (h1.add h2).congr (ae_of_all _ fun v => ?_)
  simp only [bL, Pi.add_apply]
  ring

lemma cL_neg (k t v : ℝ) : cL k t (-v) = cL k t v := by
  simp only [cL]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only [mul_neg, neg_mul, Real.cos_neg]

lemma sL_neg (k t v : ℝ) : sL k t (-v) = -sL k t v := by
  simp only [sL]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only [mul_neg, neg_mul, Real.sin_neg]

lemma aL_neg (k t v : ℝ) : aL k t (-v) = aL k t v := by
  simp only [aL, lor_neg, lor'_neg, sL_neg, mul_neg, neg_mul, Real.cos_neg]
  ring

lemma bL_neg (k t v : ℝ) : bL k t (-v) = -bL k t v := by
  simp only [bL, lor_neg, lor'_neg, cL_neg, mul_neg, neg_mul, Real.sin_neg]
  ring

/-- `∫₀ᵗ (t - τ) cos τ dτ = 1 - cos t`. -/
lemma integral_sub_mul_cos (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, (t - τ) * Real.cos τ = 1 - Real.cos t := by
  have hd : ∀ τ ∈ uIcc 0 t, HasDerivAt (fun τ => (t - τ) * Real.sin τ - Real.cos τ)
      ((t - τ) * Real.cos τ) τ := by
    intro τ _
    have h1 : HasDerivAt (fun τ : ℝ => t - τ) (-1) τ := by
      simpa using (hasDerivAt_id τ).const_sub t
    refine ((h1.mul (Real.hasDerivAt_sin τ)).sub (Real.hasDerivAt_cos τ)).congr_deriv ?_
    ring
  have hc : Continuous fun τ => (t - τ) * Real.cos τ := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp
  ring

/-- The Fubini step of Gauss's law. -/
lemma integral_lor'_mul_sL {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) :
    ∫ v, lor' v * sL k t v = Real.exp (-k * t) * (1 - Real.cos t) := by
  set F : ℝ → ℝ → ℝ := fun τ v => Real.sin (k * v * (t - τ)) * (eL k τ * lor' v) with hF
  have hswap : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc 0 t)).prod (volume : Measure ℝ)) := by
    have h1 : Integrable (eL k) (volume.restrict (uIoc 0 t)) := by
      rw [uIoc_of_le ht]
      exact ((continuous_eL k).integrableOn_Icc (a := 0) (b := t)).mono_set Ioc_subset_Icc_self
    have h2 := h1.mul_prod integrable_lor'
    refine h2.bdd_mul (c := 1) (f := fun z : ℝ × ℝ => Real.sin (k * z.2 * (t - z.1))) ?_ ?_
    · have hc : Continuous fun z : ℝ × ℝ => Real.sin (k * z.2 * (t - z.1)) := by fun_prop
      exact hc.aestronglyMeasurable
    · exact ae_of_all _ fun z => by
        simpa using Real.abs_sin_le_one _
  have hinner : ∀ τ ∈ uIcc 0 t, ∫ v, F τ v = Real.exp (-k * t) * ((t - τ) * Real.cos τ) := by
    intro τ hτ
    rw [uIcc_of_le ht] at hτ
    have hnn : 0 ≤ k * (t - τ) := mul_nonneg hk.le (sub_nonneg.2 hτ.2)
    have h1 := integral_sin_mul_lor' (k * (t - τ))
    rw [abs_of_nonneg hnn] at h1
    have h2 : ∫ v, F τ v = eL k τ * ∫ v, Real.sin (k * (t - τ) * v) * lor' v := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      simp only [hF]
      rw [show k * v * (t - τ) = k * (t - τ) * v by ring]
      ring
    rw [h2, h1, eL]
    have e : Real.exp (-k * τ) * Real.exp (-(k * (t - τ))) = Real.exp (-k * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hk' : k⁻¹ * k = 1 := inv_mul_cancel₀ hk.ne'
    calc -(k⁻¹ * Real.exp (-k * τ) * Real.cos τ) *
          (-(k * (t - τ)) * Real.exp (-(k * (t - τ))))
        = (k⁻¹ * k) * (Real.exp (-k * τ) * Real.exp (-(k * (t - τ)))) *
            ((t - τ) * Real.cos τ) := by ring
      _ = _ := by rw [hk', one_mul, e]
  have h1 : ∫ v, lor' v * sL k t v = ∫ v, ∫ τ in (0 : ℝ)..t, F τ v := by
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [sL, hF]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    ring
  rw [h1, ← intervalIntegral_integral_swap hswap, intervalIntegral.integral_congr hinner,
    intervalIntegral.integral_const_mul, integral_sub_mul_cos]

/-- `∫ a (t, v) dv = e^{-k t} cos t`: the density oscillates at the plasma frequency `1`, and decays
at the Landau rate `k`. -/
lemma integral_aL {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) :
    ∫ v, aL k t v = Real.exp (-k * t) * Real.cos t := by
  have h1 := integrable_bdd (g := fun v => Real.cos (k * v * t)) (C := 1) (by fun_prop)
    (fun v => Real.abs_cos_le_one _) integrable_lor
  have h2 : Integrable fun v => lor' v * sL k t v := by
    have := integrable_bdd (g := sL k t) (C := k⁻¹ * t) (continuous_sL k t)
      (abs_sL_le hk ht) integrable_lor'
    refine this.congr (ae_of_all _ fun v => ?_)
    beta_reduce
    ring
  simp only [aL]
  rw [integral_sub h1 h2, integral_lor'_mul_sL hk ht]
  have h3 := integral_cos_mul_lor (k * t)
  rw [abs_of_nonneg (mul_nonneg hk.le ht)] at h3
  have h4 : ∫ v, Real.cos (k * v * t) * lor v = Real.exp (-(k * t)) := by
    rw [← h3]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    beta_reduce
    rw [show k * v * t = k * t * v by ring]
  rw [h4, neg_mul]
  ring

lemma integral_bL (k t : ℝ) : ∫ v, bL k t v = 0 := by
  have h := integral_neg_eq_self (bL k t) (volume : Measure ℝ)
  simp only [bL_neg, integral_neg] at h
  linarith

/-- **The example, as a solution** (arXiv 2412.05912, Sec. 2): `landauPert` solves the linearized
Vlasov–Poisson system around the Lorentzian for every `k > 0` and `α`. -/
theorem isLinearizedVP_landau {k : ℝ} (hk : 0 < k) (α : ℝ) :
    IsLinearizedVP lor (landauPert k α) (landauField k α) where
  integrable t ht x := by
    have h := (((integrable_aL hk ht).const_mul (Real.cos (k * x))).add
      ((integrable_bL hk ht).const_mul (Real.sin (k * x)))).const_mul α
    exact h
  vlasov t _ x v := landau_vlasov k α t x v
  gauss t ht x := by
    have hl : HasDerivAt (fun y : ℝ => k * y) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    have h1 : HasDerivAt (landauField k α t) (α * (Real.cos (k * x) * k) * eL k t) x :=
      (hl.sin.const_mul α).mul_const (eL k t)
    have h2 : ∫ v, landauPert k α t x v =
        α * (Real.cos (k * x) * (Real.exp (-k * t) * Real.cos t)) := by
      simp only [landauPert]
      rw [integral_const_mul, integral_add ((integrable_aL hk ht).const_mul _)
        ((integrable_bL hk ht).const_mul _), integral_const_mul, integral_const_mul,
        integral_aL hk ht, integral_bL]
      ring
    rw [h1.deriv, h2, eL]
    have hk' : k * k⁻¹ = 1 := mul_inv_cancel₀ hk.ne'
    linear_combination (-(α * Real.cos (k * x) * Real.exp (-k * t) * Real.cos t)) * hk'

/-- At `t = 0` the solution is the initial value of arXiv 2412.05912, Sec. 2:
`f (0, x, v) = (1 + α cos (k x)) f^eq (v)`. -/
theorem landau_initial (k α x v : ℝ) :
    landauFull k α 0 x v = (1 + α * Real.cos (k * x)) * lor v := by
  simp [landauFull, landauPert, aL, bL, cL, sL]
  ring

/-- The initial value of the example has rank one, as arXiv 2412.05912, Sec. 2, says. -/
theorem landau_initial_rank (k α : ℝ) : HasSepRankLE ℝ (landauFull k α 0) 1 := by
  refine ⟨fun _ x => 1 + α * Real.cos (k * x), fun _ v => lor v, fun x v => ?_⟩
  simpa using landau_initial k α x v

/-- The perturbation has rank at most two: this is the count in arXiv 2412.05912, Sec. 2, if "the
solution" there means `f⁽¹⁾` and not `f`. -/
theorem landauPert_rank_le_two (k α t : ℝ) : HasSepRankLE ℝ (landauPert k α t) 2 := by
  refine ⟨![fun x => α * Real.cos (k * x), fun x => α * Real.sin (k * x)],
    ![aL k t, bL k t], fun x v => ?_⟩
  simp only [Fin.sum_univ_two, landauPert, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The whole distribution has rank at most three, `f^eq`, `a`, `b` (arXiv 2412.05912, Sec. 2). -/
theorem landauFull_rank_le_three (k α t : ℝ) : HasSepRankLE ℝ (landauFull k α t) 3 := by
  refine ⟨![fun _ => 1, fun x => α * Real.cos (k * x), fun x => α * Real.sin (k * x)],
    ![lor, aL k t, bL k t], fun x v => ?_⟩
  simp only [Fin.sum_univ_three, landauFull, landauPert, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- For every `t > 0` there is a large velocity at which the phase `k v t` is `π/2`, up to periods:
there `a ≠ f^eq` and `b ≠ 0`. -/
lemma exists_velocity {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    ∃ w : ℝ, aL k t w ≠ lor w ∧ bL k t w ≠ 0 := by
  set L := k⁻¹ * t with hL
  have hL0 : 0 ≤ L := by positivity
  have hkt : 0 < k * t := mul_pos hk ht
  obtain ⟨n, hn⟩ := exists_nat_ge ((4 * L + 1) * (k * t) / (2 * Real.pi))
  set w : ℝ := (Real.pi / 2 + n * (2 * Real.pi)) / (k * t) with hw
  have hpi := Real.pi_pos
  have hw1 : 4 * L + 1 ≤ w := by
    rw [hw, le_div_iff₀ hkt]
    rw [div_le_iff₀ (by positivity)] at hn
    nlinarith
  have hw0 : 0 < w := by linarith
  have hphase : k * w * t = Real.pi / 2 + n * (2 * Real.pi) := by
    rw [hw]
    field_simp
  have hc : Real.cos (k * w * t) = 0 := by
    rw [hphase, Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two]
  have hs : Real.sin (k * w * t) = 1 := by
    rw [hphase, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  set D := 2 * w / (1 + w ^ 2) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDw : D * w ≤ 2 := by
    rw [hD, div_mul_eq_mul_div, div_le_iff₀ (one_add_sq_pos w)]
    nlinarith
  have hDL : D * L ≤ 1 / 2 := by
    have h1 : D * (4 * L + 1) ≤ 2 := (mul_le_mul_of_nonneg_left hw1 hD0).trans hDw
    nlinarith
  have hsb := abs_sL_le hk ht.le w
  have hcb := abs_cL_le hk ht.le w
  have hsb' : |D * sL k t w| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hD0]
    exact (mul_le_mul_of_nonneg_left hsb hD0).trans hDL
  have hcb' : |D * cL k t w| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hD0]
    exact (mul_le_mul_of_nonneg_left hcb hD0).trans hDL
  have hp := lor_pos w
  have ha : aL k t w = D * sL k t w * lor w := by
    simp only [aL, lor', hc, ← hD]
    ring
  have hb : bL k t w = (1 - D * cL k t w) * lor w := by
    simp only [bL, lor', hs, ← hD]
    ring
  refine ⟨w, fun h => ?_, fun h => ?_⟩
  · rw [ha] at h
    have h1 : D * sL k t w = 1 := mul_right_cancel₀ hp.ne' (by rw [h, one_mul])
    rw [h1, abs_one] at hsb'
    norm_num at hsb'
  · rw [hb] at h
    have h1 : 1 - D * cL k t w = 0 := (mul_eq_zero.1 h).resolve_right hp.ne'
    have h2 : D * cL k t w = 1 := by linarith
    rw [h2, abs_one] at hcb'
    norm_num at hcb'

/-- A sample of size three with nonzero determinant, at every `t > 0`. -/
lemma exists_landau_sample {k α t : ℝ} (hk : 0 < k) (hα : α ≠ 0) (ht : 0 < t) :
    ∃ xs vs : Fin 3 → ℝ, (sample (landauFull k α t) xs vs).det ≠ 0 := by
  obtain ⟨w, ha, hb⟩ := exists_velocity hk ht
  have hk0 : k ≠ 0 := hk.ne'
  set xs : Fin 3 → ℝ := ![0, Real.pi / (2 * k), Real.pi / k] with hxs
  set vs : Fin 3 → ℝ := ![0, w, -w] with hvs
  refine ⟨xs, vs, ?_⟩
  have e1 : k * (Real.pi / (2 * k)) = Real.pi / 2 := by
    field_simp
  have e2 : k * (Real.pi / k) = Real.pi := by
    field_simp
  have hx0 : ∀ v, landauFull k α t 0 v = lor v + α * aL k t v := fun v => by
    simp [landauFull, landauPert]
  have hx1 : ∀ v, landauFull k α t (Real.pi / (2 * k)) v = lor v + α * bL k t v := fun v => by
    simp [landauFull, landauPert, e1]
  have hx2 : ∀ v, landauFull k α t (Real.pi / k) v = lor v - α * aL k t v := fun v => by
    simp [landauFull, landauPert, e2]
    ring
  have ha0 : aL k t 0 = lor 0 := by simp [aL, lor'_zero]
  have hb0 : bL k t 0 = 0 := by simp [bL, lor'_zero]
  set p₀ := lor 0 with hp₀
  set p := lor w with hp
  set q := aL k t w with hq
  set r := bL k t w with hr
  have hdet : (sample (landauFull k α t) xs vs).det = 4 * α ^ 2 * r * p₀ * (p - q) := by
    rw [Matrix.det_fin_three]
    simp only [sample, Matrix.of_apply, hxs, hvs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, hx0, hx1, hx2, lor_neg, aL_neg, bL_neg, ha0, hb0, ← hp₀, ← hp, ← hq, ← hr]
    ring
  rw [hdet]
  have hp0 : p₀ ≠ 0 := (lor_pos 0).ne'
  have hpq : p - q ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have h2 : (4 : ℝ) * α ^ 2 ≠ 0 := by positivity
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hb) hp0) hpq

/-- **The rank in the example is three** (arXiv 2412.05912, Sec. 2). For `k > 0`, `α ≠ 0` and every
`t > 0` the solution `landauFull` of the linearized Vlasov–Poisson system has no separation of rank
`2`. -/
theorem landauFull_not_rank_le_two {k α t : ℝ} (hk : 0 < k) (hα : α ≠ 0) (ht : 0 < t) :
    ¬ HasSepRankLE ℝ (landauFull k α t) 2 := by
  obtain ⟨xs, vs, h⟩ := exists_landau_sample hk hα ht
  exact not_hasRankLEOver_of_det_ne_zero xs vs h

/-- `landauFull_not_rank_le_two` over `ℂ` (arXiv 2412.05912, Sec. 2): complex exponentials do not
lower the rank of this real function. -/
theorem landauFull_not_complex_rank_le_two {k α t : ℝ} (hk : 0 < k) (hα : α ≠ 0) (ht : 0 < t) :
    ¬ HasSepRankLE ℂ (fun x v => ((landauFull k α t x v : ℝ) : ℂ)) 2 := by
  obtain ⟨xs, vs, h⟩ := exists_landau_sample hk hα ht
  exact not_hasRankLEOver_complex_of_det_ne_zero xs vs h

/-- **The example of arXiv 2412.05912, Sec. 2, is false as stated for the distribution.** "The
initial value has rank 1 and the solution is at most rank 2 in the linear regime": for the
equilibrium `f^eq = 1/(π (1 + v²))`, every `k > 0` and `α ≠ 0`, the initial value
`(1 + α cos (k x)) f^eq (v)` has rank one and the solution of the linearized Vlasov–Poisson system
has rank exactly three at every `t > 0`. The modes are `0`, `k`, `-k`: `cos (k x)` is two Fourier
modes, and [61] = arXiv 1902.00424 gives `m + 1 = 3`. `landauPert_rank_le_two` is the count `2`, and
it is true of the perturbation `f⁽¹⁾` only. Uniqueness of the solution is not claimed here. -/
theorem linearized_example_rank_eq_three {k α : ℝ} (hk : 0 < k) (hα : α ≠ 0) :
    IsLinearizedVP lor (landauPert k α) (landauField k α) ∧
    (∀ x v, landauFull k α 0 x v = (1 + α * Real.cos (k * x)) * lor v) ∧
    HasSepRankLE ℝ (landauFull k α 0) 1 ∧
    ∀ t, 0 < t → HasSepRankLE ℝ (landauFull k α t) 3 ∧
      ¬ HasSepRankLE ℝ (landauFull k α t) 2 ∧
      ¬ HasSepRankLE ℂ (fun x v => ((landauFull k α t x v : ℝ) : ℂ)) 2 :=
  ⟨isLinearizedVP_landau hk α, landau_initial k α, landau_initial_rank k α,
    fun _ ht => ⟨landauFull_rank_le_three k α _, landauFull_not_rank_le_two hk hα ht,
      landauFull_not_complex_rank_le_two hk hα ht⟩⟩

end Lorentzian

/-! ### The velocity rule in the core kinetic vocabulary -/

section KineticCore

variable {X V : Type*} [Fintype V] {d : ℕ}

namespace VelocityRule

/-- **A velocity rule as core quadratures**: for every velocity component `l`, the weights of the
rule and the nodes `node l` are a core quadrature `Kinetic.Quadrature`. The normalization is the
same (weights of sum one); the mean-zero condition of the rule is not part of the core
structure. -/
def toQuadrature (q : VelocityRule V d) (l : Fin d) : Kinetic.Quadrature V :=
  ⟨q.node l, q.w, q.w_pos, q.sum_w⟩

@[simp] lemma toQuadrature_μ (q : VelocityRule V d) (l : Fin d) :
    (q.toQuadrature l).μ = q.node l := rfl

@[simp] lemma toQuadrature_w (q : VelocityRule V d) (l : Fin d) : (q.toQuadrature l).w = q.w := rfl

/-- The density `F w` of a velocity rule is the core `Kinetic.density` with the weights of the
rule. -/
theorem density_eq_kinetic (q : VelocityRule V d) (F : Matrix X V ℝ) :
    q.density F = Kinetic.density q.w F :=
  (Kinetic.density_eq_mulVec q.w F).symm

/-- The streaming operator `∑_l D_l F diag(node l)` of a velocity rule is the core
`Kinetic.streaming` with the stencils `D` and the diagonal matrices of the nodes. -/
theorem streaming_eq_kinetic [Fintype X] [DecidableEq V] (q : VelocityRule V d)
    (D : Fin d → Matrix X X ℝ) (F : Matrix X V ℝ) :
    q.streaming D F = Kinetic.streaming D (fun l => Matrix.diagonal (q.node l)) F :=
  (Kinetic.streaming_apply _ _ _).symm

end VelocityRule

/-- The bridges at the six-point rule in three dimensions. -/
example (D : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (F : Matrix (Fin 2) (Fin 3 × Bool) ℝ) :
    (sixPointRule.toQuadrature 0).w = sixPointRule.w ∧
      sixPointRule.density F = Kinetic.density sixPointRule.w F ∧
      sixPointRule.streaming D F =
        Kinetic.streaming D (fun l => Matrix.diagonal (sixPointRule.node l)) F :=
  ⟨rfl, sixPointRule.density_eq_kinetic F, sixPointRule.streaming_eq_kinetic D F⟩

end KineticCore

/-- The separation rank of Eq. (2) of arXiv 2412.05912 over a semiring is the core
`LeanDLRA.HasSepRankLE`; the former name of this file is kept as an alias. -/
@[deprecated (since := "2026-11-10")] alias HasRankLEOver := LeanDLRA.HasSepRankLE

end LeanDLRA.Literature.P2412_05912
