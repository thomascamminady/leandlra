import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stiff.ImplicitSolvability

/-!
# Results of arXiv 2607.27736: AP low-rank semi-Lagrangian kinetic

Li, Jiang, Zhang, Xiong, *An asymptotic-preserving dynamical low-rank semi-Lagrangian method for
multiscale linear kinetic transport equations*. This module formalizes the fully discrete scheme of
the paper in its one-dimensional periodic source-free setting, on the grid `ZMod N` with a finite
velocity set `κ` (`Disc`, `Disc.Admissible`): the backtracked flux derivative and its sampled form
(`Disc.flux`, `Disc.fluxS`), the density solve (`Disc.IsMacroSolve`), the full-rank update
(`Disc.IsFullStep`) and the implicit BUG integrator (`Disc.IsBUGSubsteps`, `Disc.IsDLRFullStep`,
`Disc.IsDLRStep`), all well defined (`Disc.exists_fullStep`, `Disc.exists_dlrFullStep`,
`Disc.exists_dlrStep`). It proves the sampling estimates `Disc.lemma3`, `Disc.estimate11`,
`Disc.estimate11_enlarged` and `Disc.lemma4`; the results on the density solve `Disc.lemma5`,
`Disc.prop6`, `Disc.estimate14`, `Disc.prop6_diffusive_le` and `Disc.prop6_diffusive_tendsto`; the
energy stability `Disc.lemma8`, `Disc.lemma9`, `Disc.lemma10`, `Disc.prop1` and `Disc.prop2`; and
the asymptotic-preserving property `Disc.prop7_full`, `Disc.prop7_sampled`, also for data
independent of `ε` (`Disc.prop7_full_fixed`, `Disc.prop7_sampled_fixed`), with
`Disc.prop7_nonvacuous` as an instance. No claim of the paper was found to be false, except that
(25) of Lemma 10 needs a moment condition on the quadrature that the paper does not state
(`Disc.lemma10_third_needs_moment`).

Differences from the paper, which the docstrings repeat where they matter:

* (25) holds for rules with `∑ⱼ wⱼ vⱼ² ≤ 1/3` (equality for a rule exact on `v²`), which the
  paper does not state: for the normalized rule `v = ±1`, `w = 1/2` it fails
  (`Disc.lemma10_third_needs_moment`). `Disc.lemma10` has `∑ⱼ wⱼ vⱼ²` in place of `1/3`, and
  `Disc.prop1`, `Disc.prop2` do not need the exactness: the final estimate closes for
  `∑ⱼ wⱼ vⱼ² ≤ 4/3` (`Disc.closing_ineq`), so `|vⱼ| ≤ 1` is enough. The operator `T^{-1/2}` of
  the paper is avoided by a direct Young inequality.
* (11) and the estimate after it are formal expansions in the paper, with unspecified `C`. Here
  they are theorems for a state that samples a smooth periodic low-rank function
  (`Disc.IsSmoothState`), with explicit constants. The first-order accuracy of the reconstruction
  (`Disc.IsSmoothState.abs_bvec_sub_le`) and the membership of the leading terms in the target
  spaces are proved. `Disc.lemma3` itself has no such assumption.
* In Proposition 7 the data may depend on `ε`, with uniform bounds; the uniform bounds on `ρⁿ` are
  implicit in the paper. Both nonvanishing conditions (16), (17) are derived; (17) needs the
  discrete maximum principle (`Disc.diffusion_nonneg`), which the paper does not mention. Nothing
  is inverted, so the bases need not converge and the QR factors may be singular.
* The sampled rule `(idx, wt)` is arbitrary, subject to the exactness (9) and `‖w̃‖₁ ≤ C`, as in
  the paper's lemmas. The QDEIM selection is not formalized, nor are nonperiodic boundaries, sources
  or several space dimensions, none of which enter the paper's analysis.

The abstract cores `densitySolve_invertible`, `densitySolve_perturbation` and
`grid_l2_le_sqrt_mul` of `Stiff/ImplicitSolvability.lean` are the starting point here; the first
and the last are used directly.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2607_27736

open LeanDLRA LeanDLRA.Frobenius

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

/-! ### The periodic grid -/

section Grid

variable {N : ℕ} [NeZero N]

/-- The periodic shift `(S_m q)_i = q_{i-m}`. -/
def shift (m : ℤ) (q : ZMod N → ℝ) (i : ZMod N) : ℝ := q (i - m)

/-- The linear interpolation `𝓑 = (1 - λ) S_m + λ S_{m+1}`, where `c = m + λ`, `m ∈ ℤ`,
`0 ≤ λ < 1`. In the scheme `c = v Δt / (ε Δx)`. -/
def backtrack (c : ℝ) (q : ZMod N → ℝ) (i : ZMod N) : ℝ :=
  (1 - Int.fract c) * shift ⌊c⌋ q i + Int.fract c * shift (⌊c⌋ + 1) q i

/-- The backward difference `(D⁻ u)_i = (u_i - u_{i-1}) / Δx`. -/
def dMinus (Δx : ℝ) (u : ZMod N → ℝ) (i : ZMod N) : ℝ := (u i - u (i - 1)) / Δx

/-- The forward difference `(D⁺ u)_i = (u_{i+1} - u_i) / Δx`. -/
def dPlus (Δx : ℝ) (u : ZMod N → ℝ) (i : ZMod N) : ℝ := (u (i + 1) - u i) / Δx

/-- The upwind difference: `D⁻` for `v ≥ 0` and `D⁺` for `v < 0`. -/
def dUp (Δx v : ℝ) (u : ZMod N → ℝ) : ZMod N → ℝ := if 0 ≤ v then dMinus Δx u else dPlus Δx u

/-- The discrete inner product `⟨u, φ⟩_Δx = Δx ∑ᵢ uᵢ φᵢ`. -/
def gridInner (Δx : ℝ) (u φ : ZMod N → ℝ) : ℝ := Δx * ∑ i, u i * φ i

/-- The discrete norm `‖u‖_Δx`. -/
def gridNorm (Δx : ℝ) (u : ZMod N → ℝ) : ℝ := √(gridInner Δx u u)

/-- The weighted Frobenius norm squared, `‖Y‖²_{F,Δx} = Δx ∑ᵢ ∑ⱼ Yᵢⱼ²`. -/
def gridFrobSq {κ : Type*} [Fintype κ] (Δx : ℝ) (Y : Matrix (ZMod N) κ ℝ) : ℝ :=
  Δx * ∑ i, ∑ j, Y i j ^ 2

/-- The midpoint values `β_{i+1/2} = (β_i + β_{i+1}) / 2`. -/
def betaHalf (β : ZMod N → ℝ) (i : ZMod N) : ℝ := (β i + β (i + 1)) / 2

/-- The periodic diffusion operator
`(L_β u)_i = (β_{i+1/2} (u_{i+1} - u_i) - β_{i-1/2} (u_i - u_{i-1})) / Δx²`. -/
def lapBeta (Δx : ℝ) (β u : ZMod N → ℝ) (i : ZMod N) : ℝ :=
  (betaHalf β i * (u (i + 1) - u i) - betaHalf β (i - 1) * (u i - u (i - 1))) / Δx ^ 2

/-- Translation invariance of sums on the periodic grid. -/
theorem sum_add_right (f : ZMod N → ℝ) (a : ZMod N) : ∑ i, f (i + a) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.addRight a) f

/-- Translation invariance of sums on the periodic grid. -/
theorem sum_sub_right (f : ZMod N → ℝ) (a : ZMod N) : ∑ i, f (i - a) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.subRight a) f

/-- `S_m` is an isometry of `‖·‖_Δx`. -/
theorem sum_sq_shift (m : ℤ) (q : ZMod N → ℝ) : ∑ i, shift m q i ^ 2 = ∑ i, q i ^ 2 :=
  sum_sub_right (fun i => q i ^ 2) (m : ZMod N)

/-- `𝓑` is a contraction in `‖·‖_Δx`. -/
theorem sum_sq_backtrack_le (c : ℝ) (q : ZMod N → ℝ) :
    ∑ i, backtrack c q i ^ 2 ≤ ∑ i, q i ^ 2 := by
  set l := Int.fract c with hl
  have h0 : 0 ≤ l := Int.fract_nonneg c
  have h1 : l ≤ 1 := (Int.fract_lt_one c).le
  have hpt : ∀ i, backtrack c q i ^ 2 ≤
      (1 - l) * shift ⌊c⌋ q i ^ 2 + l * shift (⌊c⌋ + 1) q i ^ 2 := by
    intro i
    unfold backtrack
    rw [← hl]
    nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1))
      (sq_nonneg (shift ⌊c⌋ q i - shift (⌊c⌋ + 1) q i))]
  calc ∑ i, backtrack c q i ^ 2
      ≤ ∑ i, ((1 - l) * shift ⌊c⌋ q i ^ 2 + l * shift (⌊c⌋ + 1) q i ^ 2) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = ∑ i, q i ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_sq_shift, sum_sq_shift]
        ring

/-- `𝓑` is a contraction in the sup norm, used in Lemma 4. -/
theorem abs_backtrack_le (c : ℝ) {q : ZMod N → ℝ} {B : ℝ} (hq : ∀ i, |q i| ≤ B) (i : ZMod N) :
    |backtrack c q i| ≤ B := by
  have h0 : 0 ≤ Int.fract c := Int.fract_nonneg c
  have h1 : 0 ≤ 1 - Int.fract c := sub_nonneg.2 (Int.fract_lt_one c).le
  unfold backtrack shift
  calc |(1 - Int.fract c) * q (i - (⌊c⌋ : ℤ)) + Int.fract c * q (i - ((⌊c⌋ + 1 : ℤ) : ZMod N))|
      ≤ (1 - Int.fract c) * |q (i - (⌊c⌋ : ℤ))| +
          Int.fract c * |q (i - ((⌊c⌋ + 1 : ℤ) : ZMod N))| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
    _ ≤ (1 - Int.fract c) * B + Int.fract c * B := by gcongr <;> exact hq _
    _ = B := by ring

/-- `𝓑` commutes with `D⁻`. -/
theorem backtrack_dMinus (c Δx : ℝ) (q : ZMod N → ℝ) :
    backtrack c (dMinus Δx q) = dMinus Δx (backtrack c q) := by
  funext i
  simp only [backtrack, shift, dMinus]
  have e1 : i - 1 - (⌊c⌋ : ZMod N) = i - (⌊c⌋ : ZMod N) - 1 := by ring
  have e2 : i - 1 - ((⌊c⌋ + 1 : ℤ) : ZMod N) = i - ((⌊c⌋ + 1 : ℤ) : ZMod N) - 1 := by ring
  rw [e1, e2]
  ring

/-- `𝓑` commutes with `D⁺`. -/
theorem backtrack_dPlus (c Δx : ℝ) (q : ZMod N → ℝ) :
    backtrack c (dPlus Δx q) = dPlus Δx (backtrack c q) := by
  funext i
  simp only [backtrack, shift, dPlus]
  have e1 : i + 1 - (⌊c⌋ : ZMod N) = i - (⌊c⌋ : ZMod N) + 1 := by ring
  have e2 : i + 1 - ((⌊c⌋ + 1 : ℤ) : ZMod N) = i - ((⌊c⌋ + 1 : ℤ) : ZMod N) + 1 := by ring
  rw [e1, e2]
  ring

/-- Discrete summation by parts. -/
theorem sum_dMinus_mul (Δx : ℝ) (a b : ZMod N → ℝ) :
    ∑ i, dMinus Δx a i * b i = -∑ i, a i * dPlus Δx b i := by
  have h : ∑ i, a (i - 1) * b i = ∑ i, a i * b (i + 1) := by
    rw [← sum_add_right (fun i => a (i - 1) * b i) 1]
    simp
  simp only [dMinus, dPlus, sub_div, sub_mul, mul_sub, Finset.sum_sub_distrib, div_mul_eq_mul_div,
    mul_div_assoc', ← Finset.sum_div]
  rw [h]
  ring

/-- Discrete summation by parts, for `D⁺`. -/
theorem sum_dPlus_mul (Δx : ℝ) (a b : ZMod N → ℝ) :
    ∑ i, dPlus Δx a i * b i = -∑ i, a i * dMinus Δx b i := by
  have := sum_dMinus_mul Δx b a
  simp only [mul_comm] at this ⊢
  linarith

/-- `‖D⁺ u‖ = ‖D⁻ u‖` by periodicity. -/
theorem sum_sq_dPlus (Δx : ℝ) (u : ZMod N → ℝ) :
    ∑ i, dPlus Δx u i ^ 2 = ∑ i, dMinus Δx u i ^ 2 := by
  rw [← sum_add_right (fun i => dMinus Δx u i ^ 2) 1]
  simp [dPlus, dMinus]

/-- `⟨D⁻ u, u⟩ ≥ 0`: backward differences are monotone. -/
theorem sum_dMinus_mul_self_nonneg {Δx : ℝ} (hΔx : 0 < Δx) (u : ZMod N → ℝ) :
    0 ≤ ∑ i, dMinus Δx u i * u i := by
  have h : ∑ i, dMinus Δx u i * u i = Δx / 2 * ∑ i, dMinus Δx u i ^ 2 := by
    have h1 : ∑ i, (u i ^ 2 - u (i - 1) ^ 2) = 0 := by
      rw [Finset.sum_sub_distrib, sum_sub_right (fun i => u i ^ 2) 1, sub_self]
    have h2 : ∀ i, dMinus Δx u i * u i =
        Δx / 2 * dMinus Δx u i ^ 2 + (u i ^ 2 - u (i - 1) ^ 2) / (2 * Δx) := by
      intro i
      simp only [dMinus]
      field_simp
      ring
    simp only [h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, h1]
    simp
  rw [h]
  positivity

/-- `⟨D⁺ u, u⟩ ≤ 0`: forward differences are antitone. -/
theorem sum_dPlus_mul_self_nonpos {Δx : ℝ} (hΔx : 0 < Δx) (u : ZMod N → ℝ) :
    ∑ i, dPlus Δx u i * u i ≤ 0 := by
  rw [sum_dPlus_mul]
  have := sum_dMinus_mul_self_nonneg hΔx u
  simp only [mul_comm] at this ⊢
  linarith

/-- The upwind difference is monotone: `v ⟨D^{up} u, u⟩ ≥ 0`. -/
theorem sum_dUp_mul_self {Δx v : ℝ} (hΔx : 0 < Δx) (u : ZMod N → ℝ) :
    0 ≤ v * ∑ i, dUp Δx v u i * u i := by
  by_cases hv : 0 ≤ v
  · simp only [dUp, hv, ↓reduceIte]
    exact mul_nonneg hv (sum_dMinus_mul_self_nonneg hΔx u)
  · simp only [dUp, hv, ↓reduceIte]
    exact mul_nonneg_of_nonpos_of_nonpos (not_le.1 hv).le (sum_dPlus_mul_self_nonpos hΔx u)

/-- The periodic summation by parts of `L_β`:
`-⟨L_β u, u⟩ = Δx⁻² ∑ᵢ β_{i+1/2} (u_{i+1} - u_i)²`. -/
theorem sum_lapBeta_mul_self {Δx : ℝ} (β u : ZMod N → ℝ) :
    ∑ i, lapBeta Δx β u i * u i =
      -(∑ i, betaHalf β i * (u (i + 1) - u i) ^ 2) / Δx ^ 2 := by
  have h : ∑ i, betaHalf β (i - 1) * (u i - u (i - 1)) * u i =
      ∑ i, betaHalf β i * (u (i + 1) - u i) * u (i + 1) := by
    rw [← sum_add_right (fun i => betaHalf β (i - 1) * (u i - u (i - 1)) * u i) 1]
    simp
  simp only [lapBeta, div_mul_eq_mul_div, ← Finset.sum_div, sub_mul, Finset.sum_sub_distrib]
  rw [h, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `L_β` is additive in `β`, a fact used to compare the diffusion coefficients. -/
theorem lapBeta_sub (Δx : ℝ) (β γ u : ZMod N → ℝ) (i : ZMod N) :
    lapBeta Δx β u i - lapBeta Δx γ u i = lapBeta Δx (β - γ) u i := by
  simp only [lapBeta, betaHalf, Pi.sub_apply]
  ring

/-- For constant `β`, `L_β = D⁺ (β D⁻)`. -/
theorem lapBeta_const (Δx b : ℝ) (u : ZMod N → ℝ) (i : ZMod N) :
    lapBeta Δx (fun _ => b) u i = dPlus Δx (fun l => b * dMinus Δx u l) i := by
  simp only [lapBeta, betaHalf, dPlus, dMinus, add_sub_cancel_right]
  field_simp
  ring

/-- `⟨u, u⟩_Δx = Δx ∑ᵢ uᵢ²`. -/
theorem gridInner_self_eq (Δx : ℝ) (u : ZMod N → ℝ) :
    gridInner Δx u u = Δx * ∑ i, u i ^ 2 := by
  simp only [gridInner, sq]

/-- `‖u‖²_Δx = Δx ∑ᵢ uᵢ²`. -/
theorem gridNorm_sq {Δx : ℝ} (hΔx : 0 ≤ Δx) (u : ZMod N → ℝ) :
    gridNorm Δx u ^ 2 = Δx * ∑ i, u i ^ 2 := by
  rw [gridNorm, Real.sq_sqrt, gridInner_self_eq]
  rw [gridInner_self_eq]
  exact mul_nonneg hΔx (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- The grid norm is nonnegative. -/
theorem gridNorm_nonneg (Δx : ℝ) (u : ZMod N → ℝ) : 0 ≤ gridNorm Δx u := Real.sqrt_nonneg _

/-- Bounding the grid norm through its square. -/
theorem gridNorm_le_of_sum_sq_le {Δx c : ℝ} (hc : 0 ≤ c) {u : ZMod N → ℝ}
    (h : Δx * ∑ i, u i ^ 2 ≤ c ^ 2) : gridNorm Δx u ≤ c := by
  rw [gridNorm, gridInner_self_eq]
  exact Real.sqrt_le_iff.2 ⟨hc, h⟩

/-- The sup norm controls the grid norm: `‖u‖_Δx ≤ √(N Δx) ‖u‖_∞`. -/
theorem gridNorm_le_of_abs_le {Δx B : ℝ} (hΔx : 0 ≤ Δx) (hB : 0 ≤ B) {u : ZMod N → ℝ}
    (hu : ∀ i, |u i| ≤ B) : gridNorm Δx u ≤ √(N * Δx) * B := by
  refine gridNorm_le_of_sum_sq_le (by positivity) ?_
  have h1 : ∑ i, u i ^ 2 ≤ ∑ _i : ZMod N, B ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hu i) 2
  have h2 : ∑ _i : ZMod N, B ^ 2 = N * B ^ 2 := by
    simp [Finset.card_univ, ZMod.card]
  rw [h2] at h1
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have := mul_le_mul_of_nonneg_left h1 hΔx
  nlinarith

/-- `‖Y‖²_{F,Δx}` in terms of the Frobenius norm of the library. -/
theorem gridFrobSq_eq {κ : Type*} [Fintype κ] (Δx : ℝ) (Y : Matrix (ZMod N) κ ℝ) :
    gridFrobSq Δx Y = Δx * ‖Y‖ ^ 2 := by
  rw [gridFrobSq, norm_sq_eq_sum]

/-- The key estimate of Lemma 10, one velocity: `|⟨𝓑 D^{up} q, φ⟩|² ≤ ‖q‖² ‖D⁻ φ‖²`, by the
commutation of `𝓑` with the differences, summation by parts and the contraction property. -/
theorem sum_backtrack_dUp_mul_sq_le (c Δx v : ℝ) (q φ : ZMod N → ℝ) :
    (∑ i, backtrack c (dUp Δx v q) i * φ i) ^ 2 ≤
      (∑ i, q i ^ 2) * ∑ i, dMinus Δx φ i ^ 2 := by
  by_cases hv : 0 ≤ v
  · simp only [dUp, hv, ↓reduceIte]
    rw [backtrack_dMinus, sum_dMinus_mul, neg_sq, ← sum_sq_dPlus Δx φ]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (sum_sq_backtrack_le c q)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · simp only [dUp, hv, ↓reduceIte]
    rw [backtrack_dPlus, sum_dPlus_mul, neg_sq]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (sum_sq_backtrack_le c q)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)

end Grid

/-! ### The scheme -/

/-- The fixed data of the discretization on the periodic grid with `N` cells and the velocity
nodes `κ`: mesh width, time step, scattering and absorption cross-sections, velocities and
quadrature weights. The scaling `ε` is a separate argument, since Proposition 7 lets it vary. -/
structure Disc (N : ℕ) (κ : Type*) where
  Δx : ℝ
  Δt : ℝ
  σs : ZMod N → ℝ
  σa : ZMod N → ℝ
  v : κ → ℝ
  w : κ → ℝ

namespace Disc

variable {N : ℕ} [NeZero N] {κ : Type*} [Fintype κ] [DecidableEq κ] (P : Disc N κ)

/-- The standing assumptions: positive mesh and time step, `σˢ > 0`, `σᵃ ≥ 0`, a normalized
quadrature rule with positive weights, and `v ∈ [-1, 1]`. -/
structure Admissible : Prop where
  Δx_pos : 0 < P.Δx
  Δt_pos : 0 < P.Δt
  σs_pos : ∀ i, 0 < P.σs i
  σa_nonneg : ∀ i, 0 ≤ P.σa i
  w_pos : ∀ j, 0 < P.w j
  w_sum : ∑ j, P.w j = 1
  v_le : ∀ j, |P.v j| ≤ 1

/-- `μᵢ = σˢᵢ / ε² + σᵃᵢ`. -/
def mu (ε : ℝ) (i : ZMod N) : ℝ := P.σs i / ε ^ 2 + P.σa i

/-- `α₁ᵢ = e^{-μᵢ Δt}`. -/
def alpha1 (ε : ℝ) (i : ZMod N) : ℝ := Real.exp (-(P.mu ε i * P.Δt))

/-- `α₂ᵢ = (σˢᵢ / (μᵢ ε²))² (1 - e^{-μᵢ Δt})`. -/
def alpha2 (ε : ℝ) (i : ZMod N) : ℝ :=
  (P.σs i / (P.mu ε i * ε ^ 2)) ^ 2 * (1 - Real.exp (-(P.mu ε i * P.Δt)))

/-- `βᵢ = α₂ᵢ / (3 σˢᵢ)`. -/
def beta (ε : ℝ) (i : ZMod N) : ℝ := P.alpha2 ε i / (3 * P.σs i)

/-- The limit `1 / (3 σˢᵢ)` of `βᵢ` as `ε → 0`, the coefficient of the diffusion equation. -/
def betaLim (i : ZMod N) : ℝ := 1 / (3 * P.σs i)

/-- The operator `A_ρ = I - Δt L_β + Δt diag(σᵃ)` of the density solve. -/
def macroOp (β u : ZMod N → ℝ) (i : ZMod N) : ℝ :=
  u i - P.Δt * lapBeta P.Δx β u i + P.Δt * (P.σa i * u i)

/-- The vector `M 𝟏 = (√wⱼ)ⱼ`. -/
def m (j : κ) : ℝ := √(P.w j)

/-- `M = diag(√wⱼ)`. -/
def M : Matrix κ κ ℝ := Matrix.diagonal P.m

/-- `M⁻¹`. -/
def Minv : Matrix κ κ ℝ := Matrix.diagonal fun j => (P.m j)⁻¹

/-- The density `ρ = F w`. -/
def density (F : Matrix (ZMod N) κ ℝ) (i : ZMod N) : ℝ := ∑ j, F i j * P.w j

/-- The backtracked derivative `bⱼ = 𝓑ⱼ (D^{up,(j)} (fⱼ - ρ))`, equation (5), where
`𝓑ⱼ` interpolates at the shift `vⱼ Δt / (ε Δx)`. -/
def bvec (ε : ℝ) (F : Matrix (ZMod N) κ ℝ) (j : κ) : ZMod N → ℝ :=
  backtrack (P.v j * P.Δt / (ε * P.Δx)) (dUp P.Δx (P.v j) fun i => F i j - P.density F i)

/-- The angular vector `hᵢ = (vⱼ (bⱼ)ᵢ)ⱼ` of Section 3.3. -/
def hvec (ε : ℝ) (F : Matrix (ZMod N) κ ℝ) (i : ZMod N) (j : κ) : ℝ := P.v j * P.bvec ε F j i

/-- The flux derivative `𝓙ᵢ = wᵀ hᵢ = ∑ⱼ wⱼ vⱼ (bⱼ)ᵢ`. -/
def flux (ε : ℝ) (F : Matrix (ZMod N) κ ℝ) (i : ZMod N) : ℝ := ∑ j, P.w j * P.hvec ε F i j

/-- The sampled flux derivative `𝓙̃ᵢ = w̃ᵀ Pₙᵀ hᵢ`, equation (7). `idx` lists the sampled
directions and `wt` is `w̃`. -/
def fluxS {ι : Type*} [Fintype ι] (idx : ι → κ) (wt : ι → ℝ) (ε : ℝ) (F : Matrix (ZMod N) κ ℝ)
    (i : ZMod N) : ℝ := ∑ k, wt k * P.hvec ε F i (idx k)

/-- `ρs` solves the source-free macroscopic system (6), or (8) when `J` is sampled:
`A_ρ ρs = ρ - (Δt / ε) diag(α₁) J`. -/
def IsMacroSolve (ε : ℝ) (ρ J ρs : ZMod N → ℝ) : Prop :=
  ∀ i, P.macroOp (P.beta ε) ρs i = ρ i - P.Δt / ε * (P.alpha1 ε i * J i)

variable {P}

/-- A normalized quadrature rule has at least one node. -/
theorem Admissible.nonempty (hP : P.Admissible) : Nonempty κ := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hP.w_sum
  simp at this

/-- `μ ≥ 0`. -/
theorem Admissible.mu_nonneg (hP : P.Admissible) (ε : ℝ) (i : ZMod N) : 0 ≤ P.mu ε i :=
  add_nonneg (div_nonneg (hP.σs_pos i).le (sq_nonneg ε)) (hP.σa_nonneg i)

/-- `μ > 0`. -/
theorem Admissible.mu_pos (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) (i : ZMod N) :
    0 < P.mu ε i :=
  add_pos_of_pos_of_nonneg (div_pos (hP.σs_pos i) (by positivity)) (hP.σa_nonneg i)

/-- `β ≥ 0`, needed for Lemma 5. -/
theorem Admissible.beta_nonneg (hP : P.Admissible) (ε : ℝ) (i : ZMod N) : 0 ≤ P.beta ε i := by
  have h1 : Real.exp (-(P.mu ε i * P.Δt)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg (hP.mu_nonneg ε i) hP.Δt_pos.le
    linarith
  have h2 := hP.σs_pos i
  unfold beta alpha2
  have h3 : 0 ≤ 1 - Real.exp (-(P.mu ε i * P.Δt)) := sub_nonneg.2 h1
  positivity

/-- `1 / (3 σˢ) > 0`. -/
theorem Admissible.betaLim_pos (hP : P.Admissible) (i : ZMod N) : 0 < P.betaLim i := by
  have := hP.σs_pos i
  unfold betaLim
  positivity

/-- `α₁ ≥ 0`. -/
theorem Admissible.alpha1_nonneg (_hP : P.Admissible) (ε : ℝ) (i : ZMod N) :
    0 ≤ P.alpha1 ε i := (Real.exp_pos _).le

/-! ### Lemma 3: the sampling error and the target space -/

/-- The pointwise step of Lemma 3: a rule exact on `Z` errs by at most `(1 + C) ‖h - ξ‖_∞`. -/
theorem Admissible.abs_sampled_sub_le (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ι → κ}
    {wt : ι → ℝ} {Z : Submodule ℝ (κ → ℝ)} {C : ℝ}
    (hex : ∀ z ∈ Z, ∑ j, P.w j * z j = ∑ k, wt k * z (idx k)) (hC : ∑ k, |wt k| ≤ C)
    (h ξ : κ → ℝ) (hξ : ξ ∈ Z) :
    |∑ k, wt k * h (idx k) - ∑ j, P.w j * h j| ≤ (1 + C) * ‖h - ξ‖ := by
  have hsplit : ∑ k, wt k * h (idx k) - ∑ j, P.w j * h j =
      ∑ k, wt k * (h - ξ) (idx k) - ∑ j, P.w j * (h - ξ) j := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hex ξ hξ]
    ring
  have hle : ∀ j, |(h - ξ) j| ≤ ‖h - ξ‖ := fun j => by
    simpa using norm_le_pi_norm (h - ξ) j
  have h1 : |∑ k, wt k * (h - ξ) (idx k)| ≤ C * ‖h - ξ‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |wt k * (h - ξ) (idx k)| ≤ ∑ k, |wt k| * ‖h - ξ‖ :=
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hle _) (abs_nonneg _)
      _ = (∑ k, |wt k|) * ‖h - ξ‖ := by rw [Finset.sum_mul]
      _ ≤ C * ‖h - ξ‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg _)
  have h2 : |∑ j, P.w j * (h - ξ) j| ≤ ‖h - ξ‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |P.w j * (h - ξ) j| ≤ ∑ j, P.w j * ‖h - ξ‖ :=
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_pos (hP.w_pos j)]
            exact mul_le_mul_of_nonneg_left (hle _) (hP.w_pos j).le
      _ = ‖h - ξ‖ := by rw [← Finset.sum_mul, hP.w_sum, one_mul]
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  linarith

/-- **Lemma 3 of arXiv 2607.27736**, inequality (10). If the sampled rule `(idx, wt)` is exact on
the target space `Z` (condition (9)) and `‖w̃‖₁ ≤ C`, then
`‖𝓙̃ - 𝓙‖_Δx ≤ (1 + C) (Δx ∑ᵢ inf_{ξ ∈ Z} ‖hᵢ - ξ‖²_∞)^{1/2}`. The sup norm is Mathlib's norm on
`κ → ℝ`. No difference from the paper. -/
theorem lemma3 (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ι → κ} {wt : ι → ℝ} (ε : ℝ)
    (F : Matrix (ZMod N) κ ℝ) {Z : Submodule ℝ (κ → ℝ)} {C : ℝ}
    (hex : ∀ z ∈ Z, ∑ j, P.w j * z j = ∑ k, wt k * z (idx k)) (hC : ∑ k, |wt k| ≤ C) :
    gridNorm P.Δx (P.fluxS idx wt ε F - P.flux ε F) ≤
      (1 + C) * √(P.Δx * ∑ i, ⨅ ξ : Z, ‖P.hvec ε F i - (ξ : κ → ℝ)‖ ^ 2) := by
  have hC0 : 0 ≤ 1 + C := by
    have : 0 ≤ ∑ k, |wt k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  have hpt : ∀ i, (P.fluxS idx wt ε F i - P.flux ε F i) ^ 2 ≤
      (1 + C) ^ 2 * ⨅ ξ : Z, ‖P.hvec ε F i - (ξ : κ → ℝ)‖ ^ 2 := by
    intro i
    have hne : 0 ≤ (P.fluxS idx wt ε F i - P.flux ε F i) ^ 2 := sq_nonneg _
    rcases eq_or_lt_of_le hC0 with h0 | hpos
    · have h1 := hP.abs_sampled_sub_le hex hC (P.hvec ε F i) 0 (Submodule.zero_mem _)
      rw [← h0, zero_mul, abs_nonpos_iff] at h1
      simp only [fluxS, flux]
      rw [h1, ← h0]
      simp
    · rw [← div_le_iff₀' (by positivity)]
      refine le_ciInf fun ξ => ?_
      rw [div_le_iff₀' (by positivity)]
      have h1 := hP.abs_sampled_sub_le hex hC (P.hvec ε F i) ξ ξ.2
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsum : P.Δx * ∑ i, (P.fluxS idx wt ε F i - P.flux ε F i) ^ 2 ≤
      (1 + C) ^ 2 * (P.Δx * ∑ i, ⨅ ξ : Z, ‖P.hvec ε F i - (ξ : κ → ℝ)‖ ^ 2) := by
    calc _ ≤ P.Δx * ∑ i, (1 + C) ^ 2 * ⨅ ξ : Z, ‖P.hvec ε F i - (ξ : κ → ℝ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpt i) hP.Δx_pos.le
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [gridNorm, gridInner_self_eq]
  refine (Real.sqrt_le_sqrt hsum).trans_eq ?_
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC0]

/-- The form of Lemma 3 used for (11): the best approximations `ξᵢ` may be replaced by any
candidates in `Z` with `‖hᵢ - ξᵢ‖_∞ ≤ rᵢ`. -/
theorem lemma3_of_candidates (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ι → κ}
    {wt : ι → ℝ} (ε : ℝ) (F : Matrix (ZMod N) κ ℝ) {Z : Submodule ℝ (κ → ℝ)} {C : ℝ}
    (hex : ∀ z ∈ Z, ∑ j, P.w j * z j = ∑ k, wt k * z (idx k)) (hC : ∑ k, |wt k| ≤ C)
    {ξ : ZMod N → κ → ℝ} {r : ZMod N → ℝ} (hξ : ∀ i, ξ i ∈ Z)
    (hr : ∀ i, ‖P.hvec ε F i - ξ i‖ ≤ r i) :
    gridNorm P.Δx (P.fluxS idx wt ε F - P.flux ε F) ≤ (1 + C) * gridNorm P.Δx r := by
  have hC0 : 0 ≤ 1 + C := by
    have : 0 ≤ ∑ k, |wt k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  refine (lemma3 hP ε F hex hC).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  rw [gridNorm, gridInner_self_eq]
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_)
    hP.Δx_pos.le)
  have hbdd : BddBelow (Set.range fun ξ : Z => ‖P.hvec ε F i - (ξ : κ → ℝ)‖ ^ 2) :=
    ⟨0, by rintro _ ⟨ξ, rfl⟩; positivity⟩
  refine (ciInf_le hbdd ⟨ξ i, hξ i⟩).trans ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (hr i) 2

/-! ### Lemma 4: the sampling error in the diffusive regime -/

/-- The first bound of the proof of Lemma 4: `|(bⱼ)ᵢ| ≤ 2 C_g / Δx`. -/
theorem Admissible.abs_bvec_le (hP : P.Admissible) (ε : ℝ) {F : Matrix (ZMod N) κ ℝ} {Cg : ℝ}
    (hG : ∀ i j, |F i j - P.density F i| ≤ Cg) (j : κ) (i : ZMod N) :
    |P.bvec ε F j i| ≤ 2 * Cg / P.Δx := by
  refine abs_backtrack_le _ (fun l => ?_) i
  have hΔx := hP.Δx_pos
  have h1 := hG l j
  by_cases hv : 0 ≤ P.v j
  · simp only [dUp, hv, ↓reduceIte, dMinus]
    rw [abs_div, abs_of_pos hΔx]
    gcongr
    have h2 := hG (l - 1) j
    calc _ ≤ _ + _ := abs_sub _ _
      _ ≤ 2 * Cg := by linarith
  · simp only [dUp, hv, ↓reduceIte, dPlus]
    rw [abs_div, abs_of_pos hΔx]
    gcongr
    have h2 := hG (l + 1) j
    calc _ ≤ _ + _ := abs_sub _ _
      _ ≤ 2 * Cg := by linarith

/-- `|vⱼ (bⱼ)ᵢ| ≤ 2 C_g / Δx`, since `|vⱼ| ≤ 1`. -/
theorem Admissible.abs_hvec_le (hP : P.Admissible) (ε : ℝ) {F : Matrix (ZMod N) κ ℝ} {Cg : ℝ}
    (hG : ∀ i j, |F i j - P.density F i| ≤ Cg) (i : ZMod N) (j : κ) :
    |P.hvec ε F i j| ≤ 2 * Cg / P.Δx := by
  rw [hvec, abs_mul]
  have h := hP.abs_bvec_le ε hG j i
  calc |P.v j| * |P.bvec ε F j i| ≤ 1 * (2 * Cg / P.Δx) :=
        mul_le_mul (hP.v_le j) h (abs_nonneg _) zero_le_one
    _ = 2 * Cg / P.Δx := one_mul _

/-- `‖𝓙‖_∞ ≤ 2 C_g / Δx`, from the proof of Lemma 4. -/
theorem Admissible.abs_flux_le (hP : P.Admissible) (ε : ℝ) {F : Matrix (ZMod N) κ ℝ} {Cg : ℝ}
    (hG : ∀ i j, |F i j - P.density F i| ≤ Cg) (i : ZMod N) :
    |P.flux ε F i| ≤ 2 * Cg / P.Δx := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |P.w j * P.hvec ε F i j| ≤ ∑ j, P.w j * (2 * Cg / P.Δx) :=
        Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_pos (hP.w_pos j)]
          exact mul_le_mul_of_nonneg_left (hP.abs_hvec_le ε hG i j) (hP.w_pos j).le
    _ = 2 * Cg / P.Δx := by rw [← Finset.sum_mul, hP.w_sum, one_mul]

/-- `‖𝓙̃‖_∞ ≤ 2 C_g C_w̃ / Δx`, from the proof of Lemma 4. -/
theorem Admissible.abs_fluxS_le (hP : P.Admissible) {ι : Type*} [Fintype ι] (idx : ι → κ)
    {wt : ι → ℝ} (ε : ℝ) {F : Matrix (ZMod N) κ ℝ} {Cg C : ℝ}
    (hG : ∀ i j, |F i j - P.density F i| ≤ Cg) (hC : ∑ k, |wt k| ≤ C) (i : ZMod N) :
    |P.fluxS idx wt ε F i| ≤ C * (2 * Cg / P.Δx) := by
  obtain ⟨j₀⟩ := hP.nonempty
  have hb : 0 ≤ 2 * Cg / P.Δx := (abs_nonneg _).trans (hP.abs_hvec_le ε hG i j₀)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |wt k * P.hvec ε F i (idx k)| ≤ ∑ k, |wt k| * (2 * Cg / P.Δx) :=
        Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hP.abs_hvec_le ε hG i _) (abs_nonneg _)
    _ = (∑ k, |wt k|) * (2 * Cg / P.Δx) := by rw [Finset.sum_mul]
    _ ≤ C * (2 * Cg / P.Δx) := mul_le_mul_of_nonneg_right hC hb

/-- **Lemma 4 of arXiv 2607.27736.** If `maxⱼ ‖fⱼ - ρ‖_∞ ≤ C_g` and `‖w̃‖₁ ≤ C`, then
`‖𝓙̃ - 𝓙‖_Δx ≤ C_η / Δx`, with the paper's constant `C_η = 2 √(x_R - x_L) C_g (1 + C)` and
`x_R - x_L = N Δx`. This uses `|vⱼ| ≤ 1` and `∑ⱼ wⱼ = 1`, as the paper does. The final passage from
the sup norm to the grid norm is `grid_l2_le_sqrt_mul`. -/
theorem lemma4 (hP : P.Admissible) {ι : Type*} [Fintype ι] (idx : ι → κ) {wt : ι → ℝ} (ε : ℝ)
    {F : Matrix (ZMod N) κ ℝ} {Cg C : ℝ} (hG : ∀ i j, |F i j - P.density F i| ≤ Cg)
    (hC : ∑ k, |wt k| ≤ C) :
    gridNorm P.Δx (P.fluxS idx wt ε F - P.flux ε F) ≤
      2 * √(N * P.Δx) * Cg * (1 + C) / P.Δx := by
  let e : Fin N ≃ ZMod N := (Fintype.equivFinOfCardEq (ZMod.card N)).symm
  have h := grid_l2_le_sqrt_mul (N := N) hP.Δx_pos.le
    (J' := fun i => P.fluxS idx wt ε F (e i)) (J := fun i => P.flux ε F (e i))
    (fun i => hP.abs_fluxS_le idx ε hG hC (e i)) (fun i => hP.abs_flux_le ε hG (e i))
  rw [Equiv.sum_comp e fun i => P.Δx * (P.fluxS idx wt ε F i - P.flux ε F i) ^ 2,
    ← Finset.mul_sum] at h
  rw [gridNorm, gridInner_self_eq]
  simp only [Pi.sub_apply]
  refine h.trans_eq ?_
  ring

/-! ### Lemma 5 and Proposition 6: the density solve -/

/-- Cauchy–Schwarz for `⟨·, ·⟩_Δx`. -/
theorem gridInner_le (hΔx : 0 ≤ P.Δx) (a b : ZMod N → ℝ) :
    gridInner P.Δx a b ≤ gridNorm P.Δx a * gridNorm P.Δx b := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have h1 := mul_le_mul_of_nonneg_left h hΔx
  have h2 : gridNorm P.Δx a * gridNorm P.Δx b =
      P.Δx * (√(∑ i, a i ^ 2) * √(∑ i, b i ^ 2)) := by
    simp only [gridNorm, gridInner_self_eq]
    rw [Real.sqrt_mul hΔx, Real.sqrt_mul hΔx]
    have := Real.mul_self_sqrt hΔx
    linear_combination (√(∑ i, a i ^ 2) * √(∑ i, b i ^ 2)) * this
  rw [h2]
  exact h1

/-- The energy identity of `A_ρ`, by periodic summation by parts. -/
theorem sum_macroOp_mul_self (β u : ZMod N → ℝ) :
    ∑ i, P.macroOp β u i * u i = ∑ i, u i ^ 2 +
      P.Δt * ((∑ i, betaHalf β i * (u (i + 1) - u i) ^ 2) / P.Δx ^ 2) +
      P.Δt * ∑ i, P.σa i * u i ^ 2 := by
  have h : ∀ i, P.macroOp β u i * u i = u i ^ 2 - P.Δt * (lapBeta P.Δx β u i * u i) +
      P.Δt * (P.σa i * u i ^ 2) := fun i => by
    simp only [macroOp]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_lapBeta_mul_self]
  ring

/-- `A_ρ` is additive. -/
theorem macroOp_sub (β a b : ZMod N → ℝ) (i : ZMod N) :
    P.macroOp β (a - b) i = P.macroOp β a i - P.macroOp β b i := by
  simp only [macroOp, lapBeta, Pi.sub_apply]
  ring

/-- The coercivity in Lemma 5: `⟨A_ρ u, u⟩_Δx ≥ ‖u‖²_Δx`, for `β ≥ 0` and `σᵃ ≥ 0`. -/
theorem lemma5_inner (hP : P.Admissible) {β : ZMod N → ℝ} (hβ : ∀ i, 0 ≤ β i) (u : ZMod N → ℝ) :
    gridNorm P.Δx u ^ 2 ≤ gridInner P.Δx (P.macroOp β u) u := by
  rw [gridNorm_sq hP.Δx_pos.le, gridInner, sum_macroOp_mul_self]
  refine mul_le_mul_of_nonneg_left ?_ hP.Δx_pos.le
  have h1 : 0 ≤ ∑ i, betaHalf β i * (u (i + 1) - u i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (div_nonneg (add_nonneg (hβ _) (hβ _)) (by norm_num))
      (sq_nonneg _)
  have h2 : 0 ≤ ∑ i, P.σa i * u i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hP.σa_nonneg i) (sq_nonneg _)
  have h3 := hP.Δt_pos
  have h4 : 0 ≤ (∑ i, betaHalf β i * (u (i + 1) - u i) ^ 2) / P.Δx ^ 2 := by positivity
  nlinarith [mul_nonneg h3.le h4, mul_nonneg h3.le h2]

/-- `‖u‖_Δx ≤ ‖A_ρ u‖_Δx`. -/
theorem gridNorm_le_macroOp (hP : P.Admissible) {β : ZMod N → ℝ} (hβ : ∀ i, 0 ≤ β i)
    (u : ZMod N → ℝ) : gridNorm P.Δx u ≤ gridNorm P.Δx (P.macroOp β u) := by
  have h1 := lemma5_inner hP hβ u
  have h2 := gridInner_le (P := P) hP.Δx_pos.le (P.macroOp β u) u
  have h3 := gridNorm_nonneg P.Δx u
  have h4 := gridNorm_nonneg P.Δx (P.macroOp β u)
  rcases h3.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact h4
  · nlinarith

/-- **Lemma 5 of arXiv 2607.27736**: `A_ρ = I - Δt L_β + Δt diag(σᵃ)`, for any `β ≥ 0`, is bijective
and `‖A_ρ⁻¹‖_{Δx→Δx} ≤ 1`, written as `‖u‖_Δx ≤ ‖A_ρ u‖_Δx`. The operator is the concrete periodic
one, with variable `β` and `σᵃ`, and the bijectivity comes from `densitySolve_invertible`. -/
theorem lemma5 (hP : P.Admissible) {β : ZMod N → ℝ} (hβ : ∀ i, 0 ≤ β i) :
    Function.Bijective (P.macroOp β) ∧
      ∀ u, gridNorm P.Δx u ≤ gridNorm P.Δx (P.macroOp β u) := by
  refine ⟨?_, gridNorm_le_macroOp hP hβ⟩
  let L : (ZMod N → ℝ) →ₗ[ℝ] (ZMod N → ℝ) :=
    { toFun := P.macroOp β
      map_add' := fun a b => by
        funext i
        simp only [macroOp, lapBeta, Pi.add_apply]
        ring
      map_smul' := fun c a => by
        funext i
        simp only [macroOp, lapBeta, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  let e := WithLp.linearEquiv 2 ℝ (ZMod N → ℝ)
  let A : EuclideanSpace ℝ (ZMod N) →ₗ[ℝ] EuclideanSpace ℝ (ZMod N) :=
    e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap
  have hA : ∀ u, ‖u‖ ^ 2 ≤ ⟪A u, u⟫ := by
    intro u
    have h := lemma5_inner hP hβ (u : ZMod N → ℝ)
    rw [gridNorm_sq hP.Δx_pos.le, gridInner] at h
    have h' := le_of_mul_le_mul_left h hP.Δx_pos
    rw [EuclideanSpace.norm_sq_eq]
    simpa [A, L, e, PiLp.inner_apply, mul_comm] using h'
  have hb := (densitySolve_invertible A hA).1
  have hL : P.macroOp β = e ∘ A ∘ e.symm := by
    funext u
    simp [A, L]
  rw [hL]
  exact e.bijective.comp (hb.comp e.symm.bijective)

/-- `‖c α₁ u‖_Δx ≤ |c| ‖α₁‖_∞ ‖u‖_Δx`. -/
theorem gridNorm_mul_le {Δx : ℝ} (hΔx : 0 ≤ Δx) (c : ℝ) (a u : ZMod N → ℝ) :
    gridNorm Δx (fun i => c * (a i * u i)) ≤ |c| * ‖a‖ * gridNorm Δx u := by
  refine gridNorm_le_of_sum_sq_le (mul_nonneg (by positivity) (gridNorm_nonneg _ _)) ?_
  rw [mul_pow, mul_pow, gridNorm_sq hΔx, sq_abs]
  have h : ∀ i, (c * (a i * u i)) ^ 2 ≤ c ^ 2 * ‖a‖ ^ 2 * u i ^ 2 := fun i => by
    have h1 : a i ^ 2 ≤ ‖a‖ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm a i) 2
    have h2 : (c * (a i * u i)) ^ 2 = c ^ 2 * (a i ^ 2 * u i ^ 2) := by ring
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (sq_nonneg _)
  calc Δx * ∑ i, (c * (a i * u i)) ^ 2
      ≤ Δx * ∑ i, c ^ 2 * ‖a‖ ^ 2 * u i ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) hΔx
    _ = c ^ 2 * ‖a‖ ^ 2 * (Δx * ∑ i, u i ^ 2) := by rw [← Finset.mul_sum]; ring

/-- Equation (12): the difference of two solves. -/
theorem IsMacroSolve.macroOp_sub {ε : ℝ} {ρ J J' ρ₁ ρ₂ : ZMod N → ℝ}
    (h₁ : P.IsMacroSolve ε ρ J ρ₁) (h₂ : P.IsMacroSolve ε ρ J' ρ₂) (i : ZMod N) :
    P.macroOp (P.beta ε) (ρ₁ - ρ₂) i = -(P.Δt / ε) * (P.alpha1 ε i * (J - J') i) := by
  rw [P.macroOp_sub, h₁ i, h₂ i]
  simp only [Pi.sub_apply]
  ring

/-- **Proposition 6 of arXiv 2607.27736**, inequality (13). Two density solves (6) and (8) from the
same `ρⁿ` with flux derivatives `J` and `J̃` differ by at most `(Δt ‖α₁‖_∞ / ε) ‖J̃ - J‖_Δx`.
`‖α₁‖_∞` is Mathlib's sup norm on `ZMod N → ℝ`. The statement holds for any two right-hand sides;
the abstract core is `densitySolve_perturbation`. -/
theorem prop6 (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) {ρ J J' ρ₁ ρ₂ : ZMod N → ℝ}
    (h₁ : P.IsMacroSolve ε ρ J ρ₁) (h₂ : P.IsMacroSolve ε ρ J' ρ₂) :
    gridNorm P.Δx (ρ₁ - ρ₂) ≤ P.Δt * ‖P.alpha1 ε‖ / ε * gridNorm P.Δx (J - J') := by
  have h1 := gridNorm_le_macroOp hP (hP.beta_nonneg ε) (ρ₁ - ρ₂)
  have h2 : P.macroOp (P.beta ε) (ρ₁ - ρ₂) =
      fun i => -(P.Δt / ε) * (P.alpha1 ε i * (J - J') i) := funext (h₁.macroOp_sub h₂)
  rw [h2] at h1
  refine h1.trans ((gridNorm_mul_le hP.Δx_pos.le _ _ _).trans_eq ?_)
  rw [abs_neg, abs_of_pos (div_pos hP.Δt_pos hε)]
  ring

/-- **Proposition 6, inequality (15)** (the bound). Under the assumptions of Lemma 4 the two
densities differ by at most `(C_η Δt / Δx) (‖α₁‖_∞ / ε)`. -/
theorem prop6_diffusive_le (hP : P.Admissible) {ι : Type*} [Fintype ι] (idx : ι → κ) {wt : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) {F : Matrix (ZMod N) κ ℝ} {Cg C : ℝ}
    (hG : ∀ i j, |F i j - P.density F i| ≤ Cg) (hC : ∑ k, |wt k| ≤ C) {ρ₁ ρ₂ : ZMod N → ℝ}
    (h₁ : P.IsMacroSolve ε (P.density F) (P.fluxS idx wt ε F) ρ₁)
    (h₂ : P.IsMacroSolve ε (P.density F) (P.flux ε F) ρ₂) :
    gridNorm P.Δx (ρ₁ - ρ₂) ≤
      2 * √(N * P.Δx) * Cg * (1 + C) * P.Δt / P.Δx * (‖P.alpha1 ε‖ / ε) := by
  have h1 := prop6 hP hε h₁ h₂
  have h2 := lemma4 hP idx ε hG hC
  have h3 : 0 ≤ P.Δt * ‖P.alpha1 ε‖ / ε := div_nonneg
    (mul_nonneg hP.Δt_pos.le (norm_nonneg _)) hε.le
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 h3).trans_eq ?_)
  ring

/-- A positive lower and an upper bound for `σˢ`. -/
theorem Admissible.exists_crossSection (hP : P.Admissible) :
    ∃ σ₀ σ₁, 0 < σ₀ ∧ σ₀ ≤ σ₁ ∧ (∀ i, σ₀ ≤ P.σs i) ∧ ∀ i, P.σs i ≤ σ₁ := by
  obtain ⟨i₀, -, h₀⟩ := Finset.exists_min_image (Finset.univ : Finset (ZMod N)) P.σs
    ⟨0, Finset.mem_univ _⟩
  obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod N)) P.σs
    ⟨0, Finset.mem_univ _⟩
  exact ⟨P.σs i₀, P.σs i₁, hP.σs_pos i₀, h₀ i₁ (Finset.mem_univ _),
    fun i => h₀ i (Finset.mem_univ _), fun i => h₁ i (Finset.mem_univ _)⟩

/-- `‖α₁‖_∞ / ε ≤ ε / (σ₀ Δt)`: the prefactor of the flux derivative is negligible. -/
theorem Admissible.norm_alpha1_div_le (hP : P.Admissible) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    (hlow : ∀ i, σ₀ ≤ P.σs i) {ε : ℝ} (hε : 0 < ε) :
    ‖P.alpha1 ε‖ / ε ≤ ε / (σ₀ * P.Δt) := by
  have hΔt := hP.Δt_pos
  have hbound : ‖P.alpha1 ε‖ ≤ ε ^ 2 / (σ₀ * P.Δt) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_of_nonneg (hP.alpha1_nonneg ε i), alpha1]
    set x := P.mu ε i * P.Δt with hx
    have hxpos : 0 < x := mul_pos (hP.mu_pos hε i) hΔt
    have h1 : Real.exp (-x) ≤ 1 / x := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hxpos (by linarith [Real.add_one_le_exp x])
    refine h1.trans ?_
    have h2 : σ₀ * P.Δt / ε ^ 2 ≤ x := by
      have h3 : σ₀ / ε ^ 2 ≤ P.mu ε i := by
        have := hP.σa_nonneg i
        have h4 : σ₀ / ε ^ 2 ≤ P.σs i / ε ^ 2 := by gcongr; exact hlow i
        unfold mu
        linarith
      calc σ₀ * P.Δt / ε ^ 2 = σ₀ / ε ^ 2 * P.Δt := by ring
        _ ≤ x := mul_le_mul_of_nonneg_right h3 hΔt.le
    calc 1 / x ≤ 1 / (σ₀ * P.Δt / ε ^ 2) := one_div_le_one_div_of_le (by positivity) h2
      _ = ε ^ 2 / (σ₀ * P.Δt) := by field_simp
  rw [div_le_iff₀ hε]
  calc ‖P.alpha1 ε‖ ≤ ε ^ 2 / (σ₀ * P.Δt) := hbound
    _ = ε / (σ₀ * P.Δt) * ε := by ring

/-- `‖α₁‖_∞ / ε → 0` as `ε → 0`. -/
theorem Admissible.tendsto_norm_alpha1_div (hP : P.Admissible) :
    Tendsto (fun ε => ‖P.alpha1 ε‖ / ε) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨σ₀, σ₁, hσ₀, -, hlow, -⟩ := hP.exists_crossSection
  have h0 : Tendsto (fun ε : ℝ => ε / (σ₀ * P.Δt)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => ε / (σ₀ * P.Δt)) (𝓝 0) (𝓝 (0 / (σ₀ * P.Δt))) :=
      tendsto_id.div_const _
    rw [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ h0
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_nonneg (norm_nonneg _) (le_of_lt hε)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hP.norm_alpha1_div_le hσ₀ hlow hε

/-- **Proposition 6, inequality (15)** (the limit). If the data may depend on `ε` but the bounds
`C_g`, `C` of Lemma 4 do not, the two densities have the same limit as `ε → 0`, for fixed `Δt` and
mesh. -/
theorem prop6_diffusive_tendsto (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ℝ → ι → κ}
    {wt : ℝ → ι → ℝ} {F : ℝ → Matrix (ZMod N) κ ℝ} {Cg C : ℝ} {ρ₁ ρ₂ : ℝ → ZMod N → ℝ}
    (hG : ∀ᶠ ε in 𝓝[>] 0, ∀ i j, |F ε i j - P.density (F ε) i| ≤ Cg)
    (hC : ∀ᶠ ε in 𝓝[>] 0, ∑ k, |wt ε k| ≤ C)
    (h₁ : ∀ᶠ ε in 𝓝[>] 0, P.IsMacroSolve ε (P.density (F ε))
      (P.fluxS (idx ε) (wt ε) ε (F ε)) (ρ₁ ε))
    (h₂ : ∀ᶠ ε in 𝓝[>] 0, P.IsMacroSolve ε (P.density (F ε)) (P.flux ε (F ε)) (ρ₂ ε)) :
    Tendsto (fun ε => gridNorm P.Δx (ρ₁ ε - ρ₂ ε)) (𝓝[>] 0) (𝓝 0) := by
  have h0 := hP.tendsto_norm_alpha1_div.const_mul
    (2 * √(N * P.Δx) * Cg * (1 + C) * P.Δt / P.Δx)
  rw [mul_zero] at h0
  refine squeeze_zero' (Eventually.of_forall fun ε => gridNorm_nonneg _ _) ?_ h0
  filter_upwards [hG, hC, h₁, h₂, self_mem_nhdsWithin] with ε g c a b hε
  exact prop6_diffusive_le hP (idx ε) hε g c a b

/-! ### The microscopic update and the low-rank scheme -/

variable (P) in
/-- The upwind transport term `D⁻ Y Q⁺ + D⁺ Y Q⁻`, whose column `j` is `vⱼ D^{up,(j)} Yⱼ`; see
`transport_apply_eq`. -/
def transport (Y : Matrix (ZMod N) κ ℝ) : Matrix (ZMod N) κ ℝ :=
  Matrix.of fun i j => P.v j * dUp P.Δx (P.v j) (fun l => Y l j) i

/-- The transport term is `D⁻ Y Q⁺ + D⁺ Y Q⁻` with `Q^± = (Q ± |Q|) / 2`. -/
theorem transport_apply_eq (Y : Matrix (ZMod N) κ ℝ) (i : ZMod N) (j : κ) :
    P.transport Y i j = dMinus P.Δx (fun l => Y l j) i * ((P.v j + |P.v j|) / 2) +
      dPlus P.Δx (fun l => Y l j) i * ((P.v j - |P.v j|) / 2) := by
  by_cases hv : 0 ≤ P.v j
  · simp only [transport, Matrix.of_apply, dUp, hv, ↓reduceIte, abs_of_nonneg hv]
    ring
  · simp only [transport, Matrix.of_apply, dUp, hv, ↓reduceIte, abs_of_neg (not_le.1 hv)]
    ring

variable (P) in
/-- The microscopic right-hand side `𝓖(Y; ρ)` of Section 3.2, source-free:
`𝓖(Y; ρ) = -ε⁻¹ (D⁻ Y Q⁺ + D⁺ Y Q⁻) + ε⁻² diag(σˢ) (ρ (M𝟏)ᵀ - Y) - diag(σᵃ) Y`. -/
def gOp (ε : ℝ) (ρ : ZMod N → ℝ) (Y : Matrix (ZMod N) κ ℝ) : Matrix (ZMod N) κ ℝ :=
  -(1 / ε) • P.transport Y + (1 / ε ^ 2) • (Matrix.diagonal P.σs * (Matrix.vecMulVec ρ P.m - Y))
    - Matrix.diagonal P.σa * Y

variable (P) in
/-- One step of the full-rank FD-SL scheme of Section 3.1, source-free: the density solve (6), and
the backward-Euler column solves with `ρs = ρ^{n+1,*}` frozen. -/
structure IsFullStep (ε : ℝ) (F : Matrix (ZMod N) κ ℝ) (ρs : ZMod N → ℝ)
    (F₁ : Matrix (ZMod N) κ ℝ) : Prop where
  macroEq : P.IsMacroSolve ε (P.density F) (P.flux ε F) ρs
  micro : ∀ i j, (F₁ i j - F i j) / P.Δt + P.v j / ε * dUp P.Δx (P.v j) (fun l => F₁ l j) i =
    P.σs i / ε ^ 2 * (ρs i - F₁ i j) - P.σa i * F₁ i j

variable {r p q : Type*} [Fintype r] [Fintype p] [Fintype q] [DecidableEq r] [DecidableEq p]
  [DecidableEq q]

variable (P) in
/-- The implicit BUG integrator of Section 3.2 for `∂ₜ Y = 𝓖(Y; ρs)`, from `Yⁿ = X S Vᵀ`: the
`K`-step, the `L`-step, the basis update by QR factorizations `K = X₁ R` and `L = V₁ R`, and the
`S`-step. The paper has `p = q = r`. The factors `R` may be singular. -/
structure IsBUGSubsteps (ε : ℝ) (ρs : ZMod N → ℝ) (X : Matrix (ZMod N) r ℝ) (S : Matrix r r ℝ)
    (V : Matrix κ r ℝ) (K : Matrix (ZMod N) r ℝ) (L : Matrix κ r ℝ) (X₁ : Matrix (ZMod N) p ℝ)
    (V₁ : Matrix κ q ℝ) (S₁ : Matrix p q ℝ) : Prop where
  orthX : Xᵀ * X = 1
  orthV : Vᵀ * V = 1
  kStep : K - X * S = P.Δt • (P.gOp ε ρs (K * Vᵀ) * V)
  lStep : L - V * Sᵀ = P.Δt • ((P.gOp ε ρs (X * Lᵀ))ᵀ * X)
  orthX₁ : X₁ᵀ * X₁ = 1
  orthV₁ : V₁ᵀ * V₁ = 1
  qrX : ∃ R : Matrix p r ℝ, K = X₁ * R
  qrV : ∃ R : Matrix q r ℝ, L = V₁ * R
  sStep : S₁ - X₁ᵀ * X * S * Vᵀ * V₁ = P.Δt • (X₁ᵀ * P.gOp ε ρs (X₁ * S₁ * V₁ᵀ) * V₁)

variable (P) in
/-- One step of SL-DLR(full): the density solve (6) with the full flux derivative of
`Fⁿ = X S Vᵀ M⁻¹`, then the BUG integrator. -/
def IsDLRFullStep (ε : ℝ) (ρs : ZMod N → ℝ) (X : Matrix (ZMod N) r ℝ) (S : Matrix r r ℝ)
    (V : Matrix κ r ℝ) (K : Matrix (ZMod N) r ℝ) (L : Matrix κ r ℝ) (X₁ : Matrix (ZMod N) p ℝ)
    (V₁ : Matrix κ q ℝ) (S₁ : Matrix p q ℝ) : Prop :=
  P.IsMacroSolve ε (P.density (X * S * Vᵀ * P.Minv)) (P.flux ε (X * S * Vᵀ * P.Minv)) ρs ∧
    P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁

variable (P) in
/-- One step of SL-DLR: the density solve (8) with the sampled flux derivative (7), then the BUG
integrator. -/
def IsDLRStep {ι : Type*} [Fintype ι] (idx : ι → κ) (wt : ι → ℝ) (ε : ℝ) (ρs : ZMod N → ℝ)
    (X : Matrix (ZMod N) r ℝ) (S : Matrix r r ℝ)
    (V : Matrix κ r ℝ) (K : Matrix (ZMod N) r ℝ) (L : Matrix κ r ℝ) (X₁ : Matrix (ZMod N) p ℝ)
    (V₁ : Matrix κ q ℝ) (S₁ : Matrix p q ℝ) : Prop :=
  P.IsMacroSolve ε (P.density (X * S * Vᵀ * P.Minv)) (P.fluxS idx wt ε (X * S * Vᵀ * P.Minv)) ρs ∧
    P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁

/-- All three substeps of the BUG integrator, and the full-rank update, are Galerkin steps:
`x ∈ range Pr` and `x - Pr x₀ = Δt Pr 𝓖(x; ρs)`. -/
structure IsGalerkinStep (P : Disc N κ) (ε : ℝ) (ρs : ZMod N → ℝ)
    (Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ) (x₀ x : Matrix (ZMod N) κ ℝ) : Prop where
  proj : IsOrthProj Pr
  mem : Pr x = x
  step : x - Pr x₀ = P.Δt • Pr (P.gOp ε ρs x)

namespace IsBUGSubsteps

variable {ε : ℝ} {ρs : ZMod N → ℝ} {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ}
  {V : Matrix κ r ℝ} {K : Matrix (ZMod N) r ℝ} {L : Matrix κ r ℝ} {X₁ : Matrix (ZMod N) p ℝ}
  {V₁ : Matrix κ q ℝ} {S₁ : Matrix p q ℝ}

/-- The `K`-step is a Galerkin step on `ℝ^{N} ⊗ range V`. -/
theorem kLift (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) :
    IsGalerkinStep P ε ρs (rightProj V) (X * S * Vᵀ) (K * Vᵀ) := by
  have hVV : Vᵀ * V * Vᵀ = Vᵀ := by rw [h.orthV, Matrix.one_mul]
  refine ⟨isOrthProj_rightProj h.orthV, rightProj_mul_transpose h.orthV K, ?_⟩
  rw [rightProj_apply, rightProj_apply]
  have h1 : X * S * Vᵀ * V * Vᵀ = X * S * Vᵀ := by
    rw [Matrix.mul_assoc (X * S), Matrix.mul_assoc (X * S), hVV]
  rw [h1, ← Matrix.sub_mul, h.kStep, Matrix.smul_mul]

/-- The `L`-step is a Galerkin step on `range X ⊗ ℝ^{κ}`. -/
theorem lLift (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) :
    IsGalerkinStep P ε ρs (leftProj X) (X * S * Vᵀ) (X * Lᵀ) := by
  refine ⟨isOrthProj_leftProj h.orthX, leftProj_mul_left h.orthX Lᵀ, ?_⟩
  have h1 : leftProj X (X * S * Vᵀ) = X * (S * Vᵀ) := by
    rw [Matrix.mul_assoc]
    exact leftProj_mul_left h.orthX _
  have h2 : Lᵀ - S * Vᵀ = P.Δt • (Xᵀ * P.gOp ε ρs (X * Lᵀ)) := by
    have := congrArg Matrix.transpose h.lStep
    simpa only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose] using this
  rw [h1, ← Matrix.mul_sub, h2, leftProj_apply, Matrix.mul_smul, Matrix.mul_assoc]

/-- The `S`-step is a Galerkin step on `range X₁ ⊗ range V₁`. -/
theorem sLift (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) :
    IsGalerkinStep P ε ρs (leftProj X₁ * rightProj V₁) (X * S * Vᵀ) (X₁ * S₁ * V₁ᵀ) := by
  have hPr : ∀ Z : Matrix (ZMod N) κ ℝ,
      (leftProj X₁ * rightProj V₁ : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ) Z =
        X₁ * (X₁ᵀ * Z * V₁) * V₁ᵀ := fun Z => leftProj_rightProj_apply X₁ V₁ Z
  refine ⟨isOrthProj_leftProj_mul_rightProj h.orthX₁ h.orthV₁, ?_, ?_⟩
  · rw [hPr]
    congr 2
    rw [← Matrix.mul_assoc X₁ᵀ, ← Matrix.mul_assoc X₁ᵀ, h.orthX₁, Matrix.one_mul,
      Matrix.mul_assoc S₁, h.orthV₁, Matrix.mul_one]
  · rw [hPr, hPr]
    have h1 := congrArg (fun Z => X₁ * Z * V₁ᵀ) h.sStep
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] at h1
    simp only [Matrix.mul_assoc] at h1 ⊢
    exact h1

end IsBUGSubsteps

/-! ### Energy stability: Lemmas 8–10 and Propositions 1–2 -/

/-- The upwind term is monotone: `⟨D⁻ Y Q⁺ + D⁺ Y Q⁻, Y⟩ ≥ 0`, used in Lemma 9. -/
theorem inner_transport_self_nonneg (hP : P.Admissible) (Y : Matrix (ZMod N) κ ℝ) :
    0 ≤ ⟪P.transport Y, Y⟫ := by
  rw [inner_def, Finset.sum_comm]
  refine Finset.sum_nonneg fun j _ => ?_
  have h := sum_dUp_mul_self (v := P.v j) hP.Δx_pos fun l => Y l j
  rw [Finset.mul_sum] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  simp only [transport, Matrix.of_apply]
  ring

/-- The Frobenius inner product with a diagonal left factor. -/
theorem inner_diagonal_mul (c : ZMod N → ℝ) (Y Z : Matrix (ZMod N) κ ℝ) :
    ⟪Matrix.diagonal c * Y, Z⟫ = ∑ i, c i * ∑ j, Y i j * Z i j := by
  rw [inner_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul]
  ring

/-- A constant diagonal is a multiple of the identity. -/
theorem diagonal_const {c : ℝ} {f : ZMod N → ℝ} (hf : ∀ i, f i = c) :
    Matrix.diagonal f = c • (1 : Matrix (ZMod N) (ZMod N) ℝ) := by
  ext i k
  by_cases h : i = k
  · subst h
    simp [hf]
  · simp [h]

/-- Testing a Galerkin step with its own solution removes the projector. -/
theorem IsGalerkinStep.energy {ε : ℝ} {ρs : ZMod N → ℝ}
    {Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ} {x₀ x : Matrix (ZMod N) κ ℝ}
    (h : IsGalerkinStep P ε ρs Pr x₀ x) : ‖x‖ ^ 2 = ⟪x₀, x⟫ + P.Δt * ⟪P.gOp ε ρs x, x⟫ := by
  have h1 : ⟪x - Pr x₀, x⟫ = ⟪P.Δt • Pr (P.gOp ε ρs x), x⟫ := by rw [h.step]
  rw [inner_sub_left, h.proj.symm, h.mem, real_inner_smul_left, h.proj.symm, h.mem,
    real_inner_self_eq_norm_sq] at h1
  linarith

/-- The full-rank microscopic update is a Galerkin step with the identity projector; this is
equation (23) of the paper, for variable coefficients. -/
theorem IsFullStep.lift (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) {F F₁ : Matrix (ZMod N) κ ℝ}
    {ρs : ZMod N → ℝ} (h : P.IsFullStep ε F ρs F₁) :
    IsGalerkinStep P ε ρs 1 (F * P.M) (F₁ * P.M) := by
  refine ⟨IsOrthProj.one, rfl, ?_⟩
  ext i j
  have h1 := h.micro i j
  have hΔt := hP.Δt_pos.ne'
  have hd : dUp P.Δx (P.v j) (fun l => (F₁ * P.M) l j) i =
      dUp P.Δx (P.v j) (fun l => F₁ l j) i * P.m j := by
    by_cases hv : 0 ≤ P.v j
    · simp only [dUp, hv, ↓reduceIte, dMinus, M, Matrix.mul_diagonal]
      ring
    · simp only [dUp, hv, ↓reduceIte, dPlus, M, Matrix.mul_diagonal]
      ring
  have h2 : F₁ i j - F i j = P.Δt * (P.σs i / ε ^ 2 * (ρs i - F₁ i j) - P.σa i * F₁ i j -
      P.v j / ε * dUp P.Δx (P.v j) (fun l => F₁ l j) i) := by
    rw [← h1]
    field_simp
    ring
  simp only [gOp, transport, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, Matrix.diagonal_mul, Matrix.vecMulVec_apply, smul_eq_mul, hd,
    one_apply_eq_self]
  simp only [M, Matrix.mul_diagonal]
  rw [← sub_mul, h2]
  ring

variable (P) in
/-- The nonequilibrium part `Gⁿ = Yⁿ - ρⁿ (M𝟏)ᵀ` of Appendix A. -/
def nonEq (F : Matrix (ZMod N) κ ℝ) : Matrix (ZMod N) κ ℝ :=
  F * P.M - Matrix.vecMulVec (P.density F) P.m

/-- The entries of `Gⁿ`: `Gⁿ_{ij} = √wⱼ (fⱼⁿ - ρⁿ)ᵢ`. -/
theorem nonEq_apply (F : Matrix (ZMod N) κ ℝ) (i : ZMod N) (j : κ) :
    P.nonEq F i j = (F i j - P.density F i) * P.m j := by
  simp only [nonEq, M, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.vecMulVec_apply]
  ring

/-- `(M𝟏)ⱼ² = wⱼ`. -/
theorem Admissible.m_sq (hP : P.Admissible) (j : κ) : P.m j ^ 2 = P.w j :=
  Real.sq_sqrt (hP.w_pos j).le

/-- `(M𝟏)ⱼ > 0`. -/
theorem Admissible.m_pos (hP : P.Admissible) (j : κ) : 0 < P.m j := Real.sqrt_pos.2 (hP.w_pos j)

/-- `‖M𝟏‖² = ∑ⱼ wⱼ = 1`. -/
theorem Admissible.sum_m_sq (hP : P.Admissible) : ∑ j, P.m j ^ 2 = 1 := by
  simp only [hP.m_sq, hP.w_sum]

/-- `Gⁿ M𝟏 = 0`. -/
theorem Admissible.sum_nonEq_mul_m (hP : P.Admissible) (F : Matrix (ZMod N) κ ℝ) (i : ZMod N) :
    ∑ j, P.nonEq F i j * P.m j = 0 := by
  have h : ∀ j, P.nonEq F i j * P.m j = F i j * P.w j - P.density F i * P.w j := fun j => by
    rw [nonEq_apply, ← hP.m_sq]
    ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, hP.w_sum]
  simp [density]

/-- The orthogonality behind (19). -/
theorem Admissible.norm_sq_nonEq_add (hP : P.Admissible) (F : Matrix (ZMod N) κ ℝ)
    (r : ZMod N → ℝ) :
    ‖P.nonEq F + Matrix.vecMulVec r P.m‖ ^ 2 = ‖P.nonEq F‖ ^ 2 + ∑ i, r i ^ 2 := by
  rw [norm_sq_eq_sum, norm_sq_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∀ j, (P.nonEq F + Matrix.vecMulVec r P.m) i j ^ 2 =
      P.nonEq F i j ^ 2 + 2 * r i * (P.nonEq F i j * P.m j) + r i ^ 2 * P.m j ^ 2 := fun j => by
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hP.sum_nonEq_mul_m, hP.sum_m_sq]
  ring

/-- `Yⁿ = Gⁿ + ρⁿ (M𝟏)ᵀ`. -/
theorem weighted_eq_nonEq_add (F : Matrix (ZMod N) κ ℝ) :
    F * P.M = P.nonEq F + Matrix.vecMulVec (P.density F) P.m := by
  simp [nonEq]

/-- **Equation (19) of arXiv 2607.27736**: `‖Yⁿ‖²_{F,Δx} = ‖ρⁿ‖²_Δx + ‖Gⁿ‖²_{F,Δx}`. -/
theorem eq19 (hP : P.Admissible) (F : Matrix (ZMod N) κ ℝ) :
    gridFrobSq P.Δx (F * P.M) = gridNorm P.Δx (P.density F) ^ 2 + gridFrobSq P.Δx (P.nonEq F) := by
  rw [gridFrobSq_eq, gridFrobSq_eq, weighted_eq_nonEq_add, hP.norm_sq_nonEq_add,
    gridNorm_sq hP.Δx_pos.le]
  ring

/-- Lemma 10 without the factors `Δx`. -/
theorem Admissible.sum_flux_mul_sq_le (hP : P.Admissible) (ε : ℝ) (F : Matrix (ZMod N) κ ℝ)
    (φ : ZMod N → ℝ) :
    (∑ i, P.flux ε F i * φ i) ^ 2 ≤
      (∑ j, P.w j * P.v j ^ 2) * ‖P.nonEq F‖ ^ 2 * ∑ i, dMinus P.Δx φ i ^ 2 := by
  set D := ∑ i, dMinus P.Δx φ i ^ 2 with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  let B : κ → ℝ := fun j => ∑ i, P.bvec ε F j i * φ i
  have h1 : ∑ i, P.flux ε F i * φ i = ∑ j, (P.m j * P.v j) * (P.m j * B j) := by
    simp only [flux, hvec, Finset.sum_mul, B, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← hP.m_sq]
    ring
  have h2 : ∀ j, B j ^ 2 ≤ (∑ i, (F i j - P.density F i) ^ 2) * D := fun j =>
    sum_backtrack_dUp_mul_sq_le _ _ _ _ _
  have h3 : ‖P.nonEq F‖ ^ 2 = ∑ j, P.w j * ∑ i, (F i j - P.density F i) ^ 2 := by
    rw [norm_sq_eq_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nonEq_apply, ← hP.m_sq]
    ring
  rw [h1]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  have h4 : ∑ j, (P.m j * P.v j) ^ 2 = ∑ j, P.w j * P.v j ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [mul_pow, hP.m_sq]
  have h5 : ∑ j, (P.m j * B j) ^ 2 ≤ ‖P.nonEq F‖ ^ 2 * D := by
    rw [h3, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, hP.m_sq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 j) (hP.w_pos j).le
  rw [h4, mul_assoc]
  exact mul_le_mul_of_nonneg_left h5 (Finset.sum_nonneg fun j _ =>
    mul_nonneg (hP.w_pos j).le (sq_nonneg _))

/-- **Lemma 10 of arXiv 2607.27736**, inequality (25). Here `C_v = ∑ⱼ wⱼ vⱼ²` replaces the paper's
constant `1/3`; the two agree exactly when the quadrature integrates `v²`, which the paper uses
without stating it (see `lemma10_third`, and `lemma10_third_needs_moment` for a rule where the
printed constant fails). -/
theorem lemma10 (hP : P.Admissible) (ε : ℝ) (F : Matrix (ZMod N) κ ℝ) (φ : ZMod N → ℝ) :
    gridInner P.Δx (P.flux ε F) φ ^ 2 ≤
      (∑ j, P.w j * P.v j ^ 2) * gridFrobSq P.Δx (P.nonEq F) *
        gridNorm P.Δx (dMinus P.Δx φ) ^ 2 := by
  rw [gridInner, gridFrobSq_eq, gridNorm_sq hP.Δx_pos.le, mul_pow, sq P.Δx]
  have := mul_le_mul_of_nonneg_left (hP.sum_flux_mul_sq_le ε F φ)
    (mul_self_nonneg P.Δx)
  refine this.trans_eq ?_
  ring

/-- **Lemma 10**, inequality (25) as printed, for a quadrature rule exact on `v²`. -/
theorem lemma10_third (hP : P.Admissible) (hv : ∑ j, P.w j * P.v j ^ 2 = 1 / 3) (ε : ℝ)
    (F : Matrix (ZMod N) κ ℝ) (φ : ZMod N → ℝ) :
    gridInner P.Δx (P.flux ε F) φ ^ 2 ≤
      1 / 3 * gridFrobSq P.Δx (P.nonEq F) * gridNorm P.Δx (dMinus P.Δx φ) ^ 2 := by
  simpa only [hv] using lemma10 hP ε F φ

/-- **Lemma 10**, equation (26): the reconstructed flux derivative has zero discrete mean. -/
theorem lemma10_mean (hP : P.Admissible) (ε : ℝ) (F : Matrix (ZMod N) κ ℝ) :
    gridInner P.Δx (P.flux ε F) (fun _ => 1) = 0 := by
  have h := lemma10 hP ε F fun _ => 1
  have h0 : gridNorm P.Δx (dMinus P.Δx fun _ : ZMod N => (1 : ℝ)) = 0 := by
    have : dMinus P.Δx (fun _ : ZMod N => (1 : ℝ)) = fun _ => 0 := by
      funext i
      simp [dMinus]
    rw [this, gridNorm, gridInner_self_eq]
    simp
  rw [h0] at h
  have h1 : gridInner P.Δx (P.flux ε F) (fun _ => 1) ^ 2 ≤ 0 := by simpa using h
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h1 (sq_nonneg _))

/-! #### (25) needs a moment condition

The printed (25) has the constant `1/3`, which is `∑ⱼ wⱼ vⱼ²` for a rule exact on `v²`. The paper
asks only for normalized weights. Here is an admissible rule with `∑ⱼ wⱼ vⱼ² = 1` for which (25)
with `1/3` fails: `N = 4`, `Δx = 1`, `Δt = 4`, `ε = 1`, `v = (1, -1)`, `w = (1/2, 1/2)`. The shifts
`vⱼ Δt / (ε Δx) = ±4` are whole periods, so `𝓑ⱼ` is the identity. -/

/-- The data of `lemma10_third_needs_moment`. -/
def ceP : Disc 4 (Fin 2) where
  Δx := 1
  Δt := 4
  σs := fun _ => 1
  σa := fun _ => 0
  v := ![1, -1]
  w := fun _ => 1 / 2

theorem ceP_admissible : ceP.Admissible where
  Δx_pos := by norm_num [ceP]
  Δt_pos := by norm_num [ceP]
  σs_pos := fun _ => by norm_num [ceP]
  σa_nonneg := fun _ => by norm_num [ceP]
  w_pos := fun _ => by norm_num [ceP]
  w_sum := by norm_num [ceP]
  v_le := fun j => by fin_cases j <;> norm_num [ceP]

/-- The profile `g = (1, 0, -1, 0)` on `ZMod 4`. -/
def ceG (i : ZMod 4) : ℝ := if i = 0 then 1 else if i = 2 then -1 else 0

/-- The state `f₁ = g`, `f₂ = -g`, with density `0`. -/
def ceF : Matrix (ZMod 4) (Fin 2) ℝ := Matrix.of fun i j => if j = 0 then ceG i else -ceG i

/-- The test function `φ = (0, -1, 0, 1)`. -/
def cePhi (i : ZMod 4) : ℝ := (![0, -1, 0, 1] : Fin 4 → ℝ) i

/-- In the example the flux derivative is the central difference of `g`, which is `φ`. -/
theorem ceP_flux : ceP.flux 1 ceF = cePhi := by
  funext i
  simp only [flux, hvec, bvec, density, backtrack, dUp, shift, ceP, ceF]
  fin_cases i <;> norm_num [Fin.sum_univ_two, ceG, cePhi, dMinus, dPlus, Matrix.of_apply] <;>
    simp +decide <;> norm_num

/-- Sums over `ZMod 4`. -/
theorem sum_zmod4 (f : ZMod 4 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  have hu : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem ceP_density (i : ZMod 4) : ceP.density ceF i = 0 := by
  simp [density, ceP, ceF, Fin.sum_univ_two]

/-- **(25) as printed fails without a moment condition** (arXiv 2607.27736, Lemma 10). For the
admissible rule `v = (1, -1)`, `w = (1/2, 1/2)` (so `∑ⱼ wⱼ vⱼ² = 1`), with `N = 4`, `Δx = 1`,
`Δt = 4`, `ε = 1`, the state `f₁ = -f₂ = (1, 0, -1, 0)` and `φ = (0, -1, 0, 1)` give
`|⟨𝓙, φ⟩_Δx|² = 4`, while the right side of (25) is `(1/3) · 2 · 4 = 8/3`. `lemma10`, with
`∑ⱼ wⱼ vⱼ²` in place of `1/3`, gives the bound `8`. -/
theorem lemma10_third_needs_moment :
    ∃ (P : Disc 4 (Fin 2)) (F : Matrix (ZMod 4) (Fin 2) ℝ) (φ : ZMod 4 → ℝ), P.Admissible ∧
      ∑ j, P.w j * P.v j ^ 2 = 1 ∧
      ¬ gridInner P.Δx (P.flux 1 F) φ ^ 2 ≤
        1 / 3 * gridFrobSq P.Δx (P.nonEq F) * gridNorm P.Δx (dMinus P.Δx φ) ^ 2 := by
  refine ⟨ceP, ceF, cePhi, ceP_admissible, by norm_num [ceP, Fin.sum_univ_two], ?_⟩
  have hm : ∀ j, ceP.m j ^ 2 = 1 / 2 := fun j => ceP_admissible.m_sq j
  rw [ceP_flux, gridNorm, Real.sq_sqrt (by
    simp only [gridInner]; exact mul_nonneg (by norm_num [ceP])
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _))]
  simp only [gridFrobSq, nonEq_apply, ceP_density, sub_zero, mul_pow, hm, gridInner,
    Fin.sum_univ_two, sum_zmod4]
  have h10 : (1 : ZMod 4) ≠ 0 := by decide
  have h12 : (1 : ZMod 4) ≠ 2 := by decide
  have h30 : (3 : ZMod 4) ≠ 0 := by decide
  have h32 : (3 : ZMod 4) ≠ 2 := by decide
  norm_num [ceP, ceF, ceG, cePhi, dMinus, h10, h12, h30, h32]

/-- **Lemma 8 of arXiv 2607.27736**, inequality (20), for a constant absorption `a` and diffusion
coefficient `b`. Here `‖√β D⁻ρs‖² = b ‖D⁻ρs‖²` and `‖√σᵃ ρs‖² = a ‖ρs‖²`. -/
theorem lemma8 (hP : P.Admissible) {a b ε : ℝ} (hε : 0 < ε) (hσa : ∀ i, P.σa i = a)
    (hβ : ∀ i, P.beta ε i = b) {ρ J ρs : ZMod N → ℝ} (h : P.IsMacroSolve ε ρ J ρs) :
    1 / 2 * gridNorm P.Δx ρs ^ 2 + P.Δt * b * gridNorm P.Δx (dMinus P.Δx ρs) ^ 2 +
        P.Δt * a * gridNorm P.Δx ρs ^ 2 ≤
      1 / 2 * gridNorm P.Δx ρ ^ 2 +
        P.Δt / ε * |gridInner P.Δx (fun i => P.alpha1 ε i * J i) ρs| := by
  have hΔx := hP.Δx_pos
  have h1 : ∑ i, P.macroOp (P.beta ε) ρs i * ρs i =
      ∑ i, ρ i * ρs i - P.Δt / ε * ∑ i, P.alpha1 ε i * J i * ρs i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h i]
    ring
  have h2 : ∑ i, betaHalf (P.beta ε) i * (ρs (i + 1) - ρs i) ^ 2 =
      b * P.Δx ^ 2 * ∑ i, dMinus P.Δx ρs i ^ 2 := by
    rw [← sum_sq_dPlus, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [betaHalf, hβ, dPlus]
    field_simp
    ring
  rw [sum_macroOp_mul_self, h2] at h1
  simp only [hσa, ← Finset.mul_sum] at h1
  have h5 : b * P.Δx ^ 2 * (∑ i, dMinus P.Δx ρs i ^ 2) / P.Δx ^ 2 =
      b * ∑ i, dMinus P.Δx ρs i ^ 2 := by
    field_simp
  rw [h5] at h1
  have h6 : ∑ i, ρ i * ρs i ≤ 1 / 2 * ∑ i, ρ i ^ 2 + 1 / 2 * ∑ i, ρs i ^ 2 := by
    calc ∑ i, ρ i * ρs i ≤ ∑ i, (1 / 2 * ρ i ^ 2 + 1 / 2 * ρs i ^ 2) :=
          Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (ρ i - ρs i)]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have h7 := congrArg (P.Δx * ·) h1
  have h8 := mul_le_mul_of_nonneg_left h6 hΔx.le
  have h9 : -(P.Δx * ∑ i, P.alpha1 ε i * J i * ρs i) ≤
      |gridInner P.Δx (fun i => P.alpha1 ε i * J i) ρs| := by
    rw [gridInner]
    exact neg_le_abs _
  have h10 := mul_le_mul_of_nonneg_left h9 (div_nonneg hP.Δt_pos.le hε.le)
  rw [gridNorm_sq hΔx.le, gridNorm_sq hΔx.le, gridNorm_sq hΔx.le]
  nlinarith

/-- Inequality (29) of arXiv 2607.27736, with `C_v = ∑ⱼ wⱼ vⱼ²` in place of `1/3`. -/
theorem eq29 (hP : P.Admissible) {a b α ε : ℝ} (hε : 0 < ε) (hσa : ∀ i, P.σa i = a)
    (ha : 0 ≤ a) (hβ : ∀ i, P.beta ε i = b) (hb : 0 < b) (hα : ∀ i, P.alpha1 ε i = α)
    (hα0 : 0 ≤ α) {F : Matrix (ZMod N) κ ℝ} {ρs : ZMod N → ℝ}
    (h : P.IsMacroSolve ε (P.density F) (P.flux ε F) ρs) :
    gridNorm P.Δx ρs ^ 2 ≤ gridNorm P.Δx (P.density F) ^ 2 +
      P.Δt * α ^ 2 * (∑ j, P.w j * P.v j ^ 2) / (2 * ε ^ 2 * b) *
        gridFrobSq P.Δx (P.nonEq F) := by
  have hΔt := hP.Δt_pos
  have hl8 := lemma8 hP hε hσa hβ h
  have hl10 := lemma10 hP ε F ρs
  set Cv := ∑ j, P.w j * P.v j ^ 2 with hCv
  have hCv0 : 0 ≤ Cv := Finset.sum_nonneg fun j _ => mul_nonneg (hP.w_pos j).le (sq_nonneg _)
  set Gw := gridFrobSq P.Δx (P.nonEq F) with hGw
  have hGw0 : 0 ≤ Gw := by
    rw [hGw, gridFrobSq_eq]
    exact mul_nonneg hP.Δx_pos.le (sq_nonneg _)
  set D := gridNorm P.Δx (dMinus P.Δx ρs) ^ 2 with hD
  have hD0 : 0 ≤ D := sq_nonneg _
  set I := gridInner P.Δx (P.flux ε F) ρs with hI
  have hαI : gridInner P.Δx (fun i => P.alpha1 ε i * P.flux ε F i) ρs = α * I := by
    simp only [hI, gridInner, hα, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hαI, abs_mul, abs_of_nonneg hα0] at hl8
  set t := α / ε with ht
  have ht0 : 0 ≤ t := div_nonneg hα0 hε.le
  have hkey : t * |I| ≤ b * D + t ^ 2 * Cv * Gw / (4 * b) := by
    have h1 : (t * |I|) ^ 2 ≤ (b * D + t ^ 2 * Cv * Gw / (4 * b)) ^ 2 := by
      have h2 : (b * D - t ^ 2 * Cv * Gw / (4 * b)) ^ 2 ≥ 0 := sq_nonneg _
      have h3 : 4 * (b * D) * (t ^ 2 * Cv * Gw / (4 * b)) = t ^ 2 * (Cv * Gw * D) := by
        field_simp
      have h4 : t ^ 2 * I ^ 2 ≤ t ^ 2 * (Cv * Gw * D) :=
        mul_le_mul_of_nonneg_left hl10 (sq_nonneg _)
      rw [mul_pow, sq_abs]
      nlinarith
    exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
  have h5 : P.Δt / ε * (α * |I|) = P.Δt * (t * |I|) := by
    rw [ht]
    ring
  have h6 : P.Δt * (t * |I|) ≤ P.Δt * (b * D + t ^ 2 * Cv * Gw / (4 * b)) :=
    mul_le_mul_of_nonneg_left hkey hΔt.le
  have h7 : P.Δt * α ^ 2 * Cv / (2 * ε ^ 2 * b) * Gw =
      2 * (P.Δt * (t ^ 2 * Cv * Gw / (4 * b))) := by
    rw [ht]
    field_simp
    ring
  have h8 : 0 ≤ P.Δt * a * gridNorm P.Δx ρs ^ 2 := by positivity
  rw [h7]
  rw [h5] at hl8
  nlinarith

/-- The constant-coefficient identity at the end of the proof of Proposition 1: with
`z = μ Δt`, `s = μˢ Δt` and `α₁ = e^{-z}`,
`1 + (1 + s) s (Δt α₁² C_v / (2 ε² β)) ≤ (1 + z)²` for every `C_v ≤ 4/3`. For `C_v = 1/3` the
left side is `1 + ½ (1 + s) z ψ(z)` with `ψ(z) = z e^{-z} / (e^z - 1)`. -/
theorem closing_ineq {σ a ε Δt Cv : ℝ} (hσ : 0 < σ) (ha : 0 ≤ a) (hε : 0 < ε) (hΔt : 0 < Δt)
    (hCv0 : 0 ≤ Cv) (hCv : Cv ≤ 4 / 3) {μ e b s : ℝ} (hμ : μ = σ / ε ^ 2 + a)
    (he : e = Real.exp (-(μ * Δt))) (hb : b = (σ / (μ * ε ^ 2)) ^ 2 * (1 - e) / (3 * σ))
    (hs : s = σ / ε ^ 2 * Δt) :
    1 + (1 + s) * (s * (Δt * e ^ 2 * Cv / (2 * ε ^ 2 * b))) ≤ (1 + μ * Δt) ^ 2 := by
  set μs := σ / ε ^ 2 with hμs
  have hμs0 : 0 < μs := by positivity
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  set z := μ * Δt with hz
  have hz0 : 0 < z := by positivity
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsz : s ≤ z := by
    rw [hs, hz, hμ]
    nlinarith
  have he0 : 0 < e := by rw [he]; exact Real.exp_pos _
  have he1 : e * (1 + z) ≤ 1 := by
    have h1 := Real.add_one_le_exp z
    have h2 : e * Real.exp z = 1 := by rw [he, ← Real.exp_add]; simp
    calc e * (1 + z) ≤ e * Real.exp z := mul_le_mul_of_nonneg_left (by linarith) he0.le
      _ = 1 := h2
  have he2 : 0 < 1 - e := by nlinarith
  have hσe : σ = μs * ε ^ 2 := by rw [hμs]; field_simp
  have hb' : b = μs * (1 - e) / (3 * μ ^ 2 * ε ^ 2) := by
    rw [hb, hσe]
    field_simp
  have hid : s * (Δt * e ^ 2 * Cv / (2 * ε ^ 2 * b)) = 3 / 2 * Cv * ((e * z) ^ 2 / (1 - e)) := by
    rw [hb', hs, hz]
    field_simp
  set y := e * z with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 - e := by nlinarith
  have hy2 : y ^ 2 / (1 - e) ≤ y := by
    rw [div_le_iff₀ he2]
    nlinarith
  rw [hid]
  have h1 : 3 / 2 * Cv ≤ 2 := by linarith
  have h2 : 0 ≤ y ^ 2 / (1 - e) := by positivity
  have h3 : (1 + s) * (3 / 2 * Cv * (y ^ 2 / (1 - e))) ≤ (1 + z) * (2 * y) := by
    have h4 : 3 / 2 * Cv * (y ^ 2 / (1 - e)) ≤ 2 * y :=
      mul_le_mul h1 hy2 h2 (by norm_num)
    exact mul_le_mul (by linarith) h4 (by positivity) (by linarith)
  have h4 : (1 + z) * (2 * y) ≤ 2 * z := by
    rw [hy]
    nlinarith
  nlinarith

/-- `∑ⱼ wⱼ vⱼ² ≤ 1` for `|vⱼ| ≤ 1`. -/
theorem Admissible.sum_w_v_sq_le (hP : P.Admissible) : ∑ j, P.w j * P.v j ^ 2 ≤ 1 := by
  calc ∑ j, P.w j * P.v j ^ 2 ≤ ∑ j, P.w j := Finset.sum_le_sum fun j _ => by
        have h1 : P.v j ^ 2 ≤ 1 := by
          rw [← sq_abs]
          exact pow_le_one₀ (abs_nonneg _) (hP.v_le j)
        nlinarith [hP.w_pos j]
    _ = 1 := hP.w_sum

/-- **Lemma 9 of arXiv 2607.27736**, inequality (22), for constant coefficients and for every
Galerkin step. The identity projector gives the full-rank update (the paper's statement), and the
`S`-step gives (24) for Proposition 2. Here `s = μˢ Δt`, `μ = μˢ + σᵃ`. -/
theorem lemma9 (hP : P.Admissible) {σ a ε : ℝ} (hσ : ∀ i, P.σs i = σ) (hσa : ∀ i, P.σa i = a)
    (hε : 0 < ε) (hσ0 : 0 < σ) (ha : 0 ≤ a) {F Y₁ : Matrix (ZMod N) κ ℝ} {ρs : ZMod N → ℝ}
    {Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ}
    (h : IsGalerkinStep P ε ρs Pr (F * P.M) Y₁) :
    gridFrobSq P.Δx Y₁ ≤ 1 / (1 + (σ / ε ^ 2 + a) * P.Δt) ^ 2 *
      (gridFrobSq P.Δx (P.nonEq F) + (1 + σ / ε ^ 2 * P.Δt) *
        (gridNorm P.Δx (P.density F) ^ 2 + σ / ε ^ 2 * P.Δt * gridNorm P.Δx ρs ^ 2)) := by
  have hΔx := hP.Δx_pos
  have hΔt := hP.Δt_pos
  set s := σ / ε ^ 2 * P.Δt with hs
  have hs0 : 0 ≤ s := by positivity
  set z := (σ / ε ^ 2 + a) * P.Δt with hz
  have hz0 : 0 ≤ z := by positivity
  set e := Matrix.vecMulVec ρs P.m with he
  have hg : ⟪P.gOp ε ρs Y₁, Y₁⟫ = -(1 / ε) * ⟪P.transport Y₁, Y₁⟫ +
      σ / ε ^ 2 * ⟪e, Y₁⟫ - (σ / ε ^ 2 + a) * ‖Y₁‖ ^ 2 := by
    rw [gOp, diagonal_const hσ, diagonal_const hσa, inner_sub_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.one_mul, real_inner_smul_left, real_inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq]
    ring
  have hT := inner_transport_self_nonneg hP Y₁
  have hE := h.energy
  rw [hg] at hE
  have hle : (1 + z) * ‖Y₁‖ ^ 2 ≤ ⟪F * P.M + s • e, Y₁⟫ := by
    rw [inner_add_left, real_inner_smul_left]
    have h1 : 0 ≤ P.Δt * (1 / ε * ⟪P.transport Y₁, Y₁⟫) := by positivity
    have hzs : (1 + z) * ‖Y₁‖ ^ 2 = ‖Y₁‖ ^ 2 + P.Δt * ((σ / ε ^ 2 + a) * ‖Y₁‖ ^ 2) := by
      rw [hz]
      ring
    rw [hzs, hs]
    nlinarith
  have hcs := real_inner_le_norm (F * P.M + s • e) Y₁
  have hnorm : (1 + z) * ‖Y₁‖ ≤ ‖F * P.M + s • e‖ := by
    rcases (norm_nonneg Y₁).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · have : (1 + z) * ‖Y₁‖ * ‖Y₁‖ ≤ ‖F * P.M + s • e‖ * ‖Y₁‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  have hsplit : F * P.M + s • e =
      P.nonEq F + Matrix.vecMulVec (fun i => P.density F i + s * ρs i) P.m := by
    rw [weighted_eq_nonEq_add, he, add_assoc]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  have h2 : ‖F * P.M + s • e‖ ^ 2 ≤ ‖P.nonEq F‖ ^ 2 +
      (1 + s) * (∑ i, P.density F i ^ 2 + s * ∑ i, ρs i ^ 2) := by
    rw [hsplit, hP.norm_sq_nonEq_add]
    have h3 : ∑ i, (P.density F i + s * ρs i) ^ 2 ≤
        (1 + s) * (∑ i, P.density F i ^ 2 + s * ∑ i, ρs i ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [mul_nonneg hs0 (sq_nonneg (P.density F i - ρs i))]
    linarith
  have h3 : (1 + z) ^ 2 * ‖Y₁‖ ^ 2 ≤ ‖F * P.M + s • e‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hnorm 2
  rw [gridFrobSq_eq, gridFrobSq_eq, gridNorm_sq hΔx.le, gridNorm_sq hΔx.le]
  have hpos : 0 < (1 + z) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  have h4 := mul_le_mul_of_nonneg_left (h3.trans h2) hΔx.le
  nlinarith

/-- The energy bound shared by Propositions 1 and 2: the density solve (6) followed by any Galerkin
step of the microscopic equation does not increase `‖·‖_{F,Δx}`. -/
theorem energy_of_galerkin (hP : P.Admissible) {σ a ε : ℝ} (hσ : ∀ i, P.σs i = σ)
    (hσa : ∀ i, P.σa i = a) (hε : 0 < ε) {F Y₁ : Matrix (ZMod N) κ ℝ} {ρs : ZMod N → ℝ}
    {Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ}
    (hm : P.IsMacroSolve ε (P.density F) (P.flux ε F) ρs)
    (h : IsGalerkinStep P ε ρs Pr (F * P.M) Y₁) :
    gridFrobSq P.Δx Y₁ ≤ gridFrobSq P.Δx (F * P.M) := by
  have hΔt := hP.Δt_pos
  have hσ0 : 0 < σ := by simpa [hσ] using hP.σs_pos 0
  have ha : 0 ≤ a := by simpa [hσa] using hP.σa_nonneg 0
  set μ := σ / ε ^ 2 + a with hμ
  set e := Real.exp (-(μ * P.Δt)) with he
  set b := (σ / (μ * ε ^ 2)) ^ 2 * (1 - e) / (3 * σ) with hb
  set s := σ / ε ^ 2 * P.Δt with hs
  have hs0 : 0 < s := by positivity
  have hμ0 : 0 < μ := by positivity
  have hmu : ∀ i, P.mu ε i = μ := fun i => by simp only [mu, hσ, hσa, hμ]
  have hα : ∀ i, P.alpha1 ε i = e := fun i => by simp only [alpha1, hmu, he]
  have hβ : ∀ i, P.beta ε i = b := fun i => by
    simp only [beta, alpha2, hmu, hσ, hb, he]
  have he1 : e < 1 := by
    rw [he, Real.exp_lt_one_iff]
    have : 0 < μ * P.Δt := by positivity
    linarith
  have hb0 : 0 < b := by
    have : 0 < 1 - e := by linarith
    rw [hb]
    positivity
  set Cv := ∑ j, P.w j * P.v j ^ 2 with hCv
  have hCv0 : 0 ≤ Cv := Finset.sum_nonneg fun j _ => mul_nonneg (hP.w_pos j).le (sq_nonneg _)
  have hCv1 : Cv ≤ 4 / 3 := by linarith [hP.sum_w_v_sq_le]
  have h29 := eq29 hP hε hσa ha hβ hb0 hα (Real.exp_pos _).le hm
  have hl9 := lemma9 hP hσ hσa hε hσ0 ha h
  have hc := closing_ineq hσ0 ha hε hΔt hCv0 hCv1 hμ he hb hs
  rw [eq19 hP F]
  set Gw := gridFrobSq P.Δx (P.nonEq F) with hGw
  have hGw0 : 0 ≤ Gw := by
    rw [hGw, gridFrobSq_eq]
    exact mul_nonneg hP.Δx_pos.le (sq_nonneg _)
  set R := gridNorm P.Δx (P.density F) ^ 2 with hR
  have hR0 : 0 ≤ R := sq_nonneg _
  set Rs := gridNorm P.Δx ρs ^ 2 with hRs
  set K := P.Δt * e ^ 2 * Cv / (2 * ε ^ 2 * b) with hK
  have hz : (0 : ℝ) < (1 + μ * P.Δt) ^ 2 := by positivity
  refine hl9.trans ?_
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hz]
  have h1 : (1 + s) ^ 2 ≤ (1 + μ * P.Δt) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have : s ≤ μ * P.Δt := by
      rw [hs, hμ]
      nlinarith
    linarith
  have h2 : (1 + s) * (R + s * Rs) ≤ (1 + s) * (R + s * (R + K * Gw)) := by
    have := mul_le_mul_of_nonneg_left h29 hs0.le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : (1 + (1 + s) * (s * K)) * Gw ≤ (1 + μ * P.Δt) ^ 2 * Gw :=
    mul_le_mul_of_nonneg_right hc hGw0
  have h4 : (1 + s) ^ 2 * R ≤ (1 + μ * P.Δt) ^ 2 * R := mul_le_mul_of_nonneg_right h1 hR0
  nlinarith

/-- **Proposition 1 of arXiv 2607.27736** (energy stability of the full-rank FD-SL scheme): in the
one-dimensional periodic source-free constant-coefficient setting, `‖F^{n+1} M‖²_{F,Δx} ≤
‖Fⁿ M‖²_{F,Δx}` for every `Δt > 0` and `ε > 0`. The scheme is the concrete one, with the backtracked
flux derivative, the density solve (6) and the backward-Euler column solves.

Difference from the paper: its proof uses `∑ⱼ wⱼ vⱼ² = 1/3` in (25), so a rule exact on `v²`, which
is not stated. We need only `|vⱼ| ≤ 1`: the final estimate closes for any `∑ⱼ wⱼ vⱼ² ≤ 4/3`
(`closing_ineq`). -/
theorem prop1 (hP : P.Admissible) {σ a ε : ℝ} (hσ : ∀ i, P.σs i = σ) (hσa : ∀ i, P.σa i = a)
    (hε : 0 < ε) {F F₁ : Matrix (ZMod N) κ ℝ} {ρs : ZMod N → ℝ} (h : P.IsFullStep ε F ρs F₁) :
    gridFrobSq P.Δx (F₁ * P.M) ≤ gridFrobSq P.Δx (F * P.M) :=
  energy_of_galerkin hP hσ hσa hε h.macroEq (h.lift hP hε)

/-- `F = Y M⁻¹` undoes the weighting. -/
theorem Admissible.mul_Minv_mul_M (hP : P.Admissible) (Y : Matrix (ZMod N) κ ℝ) :
    Y * P.Minv * P.M = Y := by
  rw [Matrix.mul_assoc, Minv, M, Matrix.diagonal_mul_diagonal]
  have : (fun j => (P.m j)⁻¹ * P.m j) = fun _ => (1 : ℝ) := by
    funext j
    exact inv_mul_cancel₀ (hP.m_pos j).ne'
  rw [this, Matrix.diagonal_one, Matrix.mul_one]

/-- **Proposition 2 of arXiv 2607.27736** (stability inherited by SL-DLR(full)): under the setting
of Proposition 1, one step from `Yⁿ = X S Vᵀ` gives `‖Y^{n+1}‖²_{F,Δx} ≤ ‖Yⁿ‖²_{F,Δx}`, for every
`Δt > 0` and `ε > 0`. The step is the concrete implicit BUG integrator with the density solve (6);
only the orthonormality of `X₁`, `V₁` and the `S`-step enter. The same difference as in `prop1`. -/
theorem prop2 (hP : P.Admissible) {σ a ε : ℝ} (hσ : ∀ i, P.σs i = σ) (hσa : ∀ i, P.σa i = a)
    (hε : 0 < ε) {ρs : ZMod N → ℝ} {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ}
    {V : Matrix κ r ℝ} {K : Matrix (ZMod N) r ℝ} {L : Matrix κ r ℝ} {X₁ : Matrix (ZMod N) p ℝ}
    {V₁ : Matrix κ q ℝ} {S₁ : Matrix p q ℝ}
    (h : P.IsDLRFullStep ε ρs X S V K L X₁ V₁ S₁) :
    gridFrobSq P.Δx (X₁ * S₁ * V₁ᵀ) ≤ gridFrobSq P.Δx (X * S * Vᵀ) := by
  have hl := h.2.sLift
  have hF := hP.mul_Minv_mul_M (X * S * Vᵀ)
  rw [← hF] at hl ⊢
  exact energy_of_galerkin hP hσ hσa hε h.1 hl

/-! ### Asymptotic preservation: Proposition 7 -/

/-- A vector as a one-column matrix, so that the Frobenius calculus applies. -/
def cv {ι : Type*} (u : ι → ℝ) : Matrix ι Unit ℝ := Matrix.of fun i _ => u i

@[simp] theorem cv_apply {ι : Type*} (u : ι → ℝ) (i : ι) (c : Unit) : cv u i c = u i := rfl

/-- The Frobenius norm of a column is its Euclidean norm. -/
theorem norm_cv_sq {ι : Type*} [Fintype ι] (u : ι → ℝ) : ‖cv u‖ ^ 2 = ∑ i, u i ^ 2 := by
  rw [norm_sq_eq_sum]
  simp

/-- `u vᵀ` as a product of one-column matrices. -/
theorem vecMulVec_eq_cv {ι ι' : Type*} [Fintype ι'] (u : ι → ℝ) (v : ι' → ℝ) :
    Matrix.vecMulVec u v = cv u * (cv v)ᵀ := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mul_apply]

/-- `‖x yᵀ‖ = ‖x‖ ‖y‖`. -/
theorem norm_mul_transpose_col {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (x : Matrix ι Unit ℝ) (y : Matrix ι' Unit ℝ) : ‖x * yᵀ‖ = ‖x‖ * ‖y‖ := by
  have h : ‖x * yᵀ‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
    rw [mul_pow]
    simp only [norm_sq_eq_sum, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_unique]
    simp only [mul_pow, Finset.sum_mul, Finset.mul_sum, PUnit.default_eq_unit]
    exact Finset.sum_comm
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- `‖D^{up} u‖² ≤ (2 / Δx)² ‖u‖²`. -/
theorem sum_dUp_sq_le {Δx : ℝ} (hΔx : 0 < Δx) (v : ℝ) (u : ZMod N → ℝ) :
    ∑ i, dUp Δx v u i ^ 2 ≤ 4 / Δx ^ 2 * ∑ i, u i ^ 2 := by
  have hm : ∑ i, dMinus Δx u i ^ 2 ≤ 4 / Δx ^ 2 * ∑ i, u i ^ 2 := by
    have h1 : ∀ i, dMinus Δx u i ^ 2 ≤ 2 / Δx ^ 2 * (u i ^ 2 + u (i - 1) ^ 2) := fun i => by
      simp only [dMinus, div_pow]
      rw [div_mul_eq_mul_div]
      gcongr
      nlinarith [sq_nonneg (u i + u (i - 1))]
    calc ∑ i, dMinus Δx u i ^ 2 ≤ ∑ i, 2 / Δx ^ 2 * (u i ^ 2 + u (i - 1) ^ 2) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 4 / Δx ^ 2 * ∑ i, u i ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_sub_right (fun i => u i ^ 2) 1]
          ring
  by_cases hv : 0 ≤ v
  · simpa only [dUp, hv, ↓reduceIte] using hm
  · simp only [dUp, hv, ↓reduceIte]
    rw [sum_sq_dPlus]
    exact hm

/-- The upwind transport is bounded by `2 / Δx` for `|v| ≤ 1`. -/
theorem norm_transport_le (hP : P.Admissible) (Y : Matrix (ZMod N) κ ℝ) :
    ‖P.transport Y‖ ≤ 2 / P.Δx * ‖Y‖ := by
  have hΔx := hP.Δx_pos
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, Finset.sum_comm, div_pow,
    Finset.sum_comm (f := fun i j => Y i j ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := sum_dUp_sq_le hΔx (P.v j) fun l => Y l j
  calc ∑ i, P.transport Y i j ^ 2 ≤ ∑ i, dUp P.Δx (P.v j) (fun l => Y l j) i ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          simp only [transport, Matrix.of_apply, mul_pow]
          have h2 : P.v j ^ 2 ≤ 1 := by
            rw [← sq_abs]
            exact pow_le_one₀ (abs_nonneg _) (hP.v_le j)
          nlinarith [sq_nonneg (dUp P.Δx (P.v j) (fun l => Y l j) i)]
    _ ≤ _ := h1.trans_eq (by norm_num)

/-- A diagonal left factor is bounded by its entries. -/
theorem norm_diagonal_mul_le {c : ZMod N → ℝ} {C : ℝ} (hC : ∀ i, |c i| ≤ C)
    (Y : Matrix (ZMod N) r ℝ) : ‖Matrix.diagonal c * Y‖ ≤ C * ‖Y‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.diagonal_mul, mul_pow]
  have : c i ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC i) 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- A diagonal left factor is coercive with its smallest entry. -/
theorem inner_diagonal_mul_self_ge {c : ZMod N → ℝ} {c₀ : ℝ}
    (hc : ∀ i, c₀ ≤ c i) (Y : Matrix (ZMod N) r ℝ) :
    c₀ * ‖Y‖ ^ 2 ≤ ⟪Matrix.diagonal c * Y, Y⟫ := by
  rw [inner_diagonal_mul, norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : 0 ≤ ∑ j, Y i j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  simp only [← sq]
  exact mul_le_mul_of_nonneg_right (hc i) h

/-- `𝓖` tested with the state. -/
theorem inner_gOp (ε : ℝ) (ρ : ZMod N → ℝ) (x : Matrix (ZMod N) κ ℝ) :
    ⟪P.gOp ε ρ x, x⟫ = -(1 / ε) * ⟪P.transport x, x⟫ +
      1 / ε ^ 2 * (⟪Matrix.diagonal P.σs * Matrix.vecMulVec ρ P.m, x⟫ -
        ⟪Matrix.diagonal P.σs * x, x⟫) - ⟪Matrix.diagonal P.σa * x, x⟫ := by
  rw [gOp, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    Matrix.mul_sub, inner_sub_left]

/-- A Galerkin step is bounded uniformly in `ε`. -/
theorem IsGalerkinStep.norm_le (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    (hlow : ∀ i, σ₀ ≤ P.σs i) {ρs : ZMod N → ℝ}
    {Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ} {x₀ x : Matrix (ZMod N) κ ℝ}
    (h : IsGalerkinStep P ε ρs Pr x₀ x) :
    ‖x‖ ≤ ‖x₀‖ + ‖Matrix.diagonal P.σs * Matrix.vecMulVec ρs P.m‖ / σ₀ := by
  have hΔt := hP.Δt_pos
  set e := Matrix.diagonal P.σs * Matrix.vecMulVec ρs P.m with he
  set c := P.Δt / ε ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hE := h.energy
  rw [inner_gOp] at hE
  have h1 := inner_transport_self_nonneg hP x
  have h2 := inner_diagonal_mul_self_ge hlow x
  have h3 : 0 ≤ ⟪Matrix.diagonal P.σa * x, x⟫ := by
    have := inner_diagonal_mul_self_ge (c₀ := 0) hP.σa_nonneg x
    simpa using this
  have h4 := real_inner_le_norm (F := Matrix (ZMod N) κ ℝ) x₀ x
  have h5 := real_inner_le_norm (F := Matrix (ZMod N) κ ℝ) e x
  have h6 : (1 + c * σ₀) * ‖x‖ ^ 2 ≤ (‖x₀‖ + c * ‖e‖) * ‖x‖ := by
    have h7 : P.Δt * (1 / ε ^ 2 * (⟪e, x⟫ - ⟪Matrix.diagonal P.σs * x, x⟫)) =
        c * (⟪e, x⟫ - ⟪Matrix.diagonal P.σs * x, x⟫) := by
      rw [hc]
      ring
    have h8 : 0 ≤ P.Δt * (1 / ε * ⟪P.transport x, x⟫) := by positivity
    have h9 := mul_le_mul_of_nonneg_left h5 hc0
    have h10 := mul_le_mul_of_nonneg_left h2 hc0
    have h11 := mul_nonneg hΔt.le h3
    rw [mul_sub, mul_add] at hE
    nlinarith
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : (1 + c * σ₀) * ‖x‖ ≤ ‖x₀‖ + c * ‖e‖ := by
    rcases hx0.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      positivity
    · have : (1 + c * σ₀) * ‖x‖ * ‖x‖ ≤ (‖x₀‖ + c * ‖e‖) * ‖x‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  have hez : 0 ≤ ‖e‖ / σ₀ := by positivity
  have hkey : ‖e‖ = σ₀ * (‖e‖ / σ₀) := by field_simp
  have hn : (1 + c * σ₀) * ‖x‖ ≤ (1 + c * σ₀) * (‖x₀‖ + ‖e‖ / σ₀) := by
    refine hy.trans ?_
    have h12 : 0 ≤ c * σ₀ * ‖x₀‖ := by positivity
    rw [hkey]
    field_simp
    nlinarith
  exact le_of_mul_le_mul_left hn (by positivity)

/-- The residual of a Galerkin step: the stiff term is `O(ε)` once the step is bounded. -/
theorem IsGalerkinStep.residual_le (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) {a₁ : ℝ}
    (hup : ∀ i, |P.σa i| ≤ a₁) {ρs : ZMod N → ℝ}
    {Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ} {x₀ x : Matrix (ZMod N) κ ℝ}
    (h : IsGalerkinStep P ε ρs Pr x₀ x) :
    ‖Pr (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - x))‖ ≤
      ε ^ 2 / P.Δt * (‖x‖ + ‖x₀‖) + ε * (2 / P.Δx) * ‖x‖ + ε ^ 2 * a₁ * ‖x‖ := by
  have hΔt := hP.Δt_pos
  set R := Pr (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - x)) with hR
  set t := Pr (P.transport x) with ht
  set n := Pr (Matrix.diagonal P.σa * x) with hn
  have hs := h.step
  rw [gOp, map_sub, map_add, map_smul, map_smul, ← hR, ← ht, ← hn] at hs
  have hRe : R = (ε ^ 2 / P.Δt) • (x - Pr x₀) + ε • t + ε ^ 2 • n := by
    rw [hs]
    simp only [smul_sub, smul_add, smul_smul]
    have e1 : ε ^ 2 / P.Δt * (P.Δt * -(1 / ε)) = -ε := by field_simp
    have e2 : ε ^ 2 / P.Δt * (P.Δt * (1 / ε ^ 2)) = 1 := by field_simp
    have e3 : ε ^ 2 / P.Δt * P.Δt = ε ^ 2 := by field_simp
    rw [e1, e2, e3, one_smul, neg_smul]
    abel
  have h1 : ‖t‖ ≤ 2 / P.Δx * ‖x‖ := (h.proj.norm_le _).trans (norm_transport_le hP x)
  have h2 : ‖n‖ ≤ a₁ * ‖x‖ := (h.proj.norm_le _).trans (norm_diagonal_mul_le hup x)
  have h3 : ‖x - Pr x₀‖ ≤ ‖x‖ + ‖x₀‖ :=
    (norm_sub_le _ _).trans (by linarith [h.proj.norm_le x₀])
  rw [hRe]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  · rw [norm_smul, Real.norm_of_nonneg hε.le]
    calc ε * ‖t‖ ≤ ε * (2 / P.Δx * ‖x‖) := mul_le_mul_of_nonneg_left h1 hε.le
      _ = _ := by ring
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ε ^ 2 * ‖n‖ ≤ ε ^ 2 * (a₁ * ‖x‖) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring

/-- `σ₀ ‖d‖ ≤ ‖Pr (σˢ d)‖` on the range of an orthogonal projector. -/
theorem norm_le_of_mem_range {σ₀ : ℝ} (hlow : ∀ i, σ₀ ≤ P.σs i)
    {Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ} (hPr : IsOrthProj Pr)
    {d : Matrix (ZMod N) κ ℝ} (hd : Pr d = d) :
    σ₀ * ‖d‖ ≤ ‖Pr (Matrix.diagonal P.σs * d)‖ := by
  have h1 := inner_diagonal_mul_self_ge hlow d
  have h2 : ⟪Matrix.diagonal P.σs * d, d⟫ = ⟪Pr (Matrix.diagonal P.σs * d), d⟫ := by
    rw [hPr.symm, hd]
  have h3 := real_inner_le_norm (Pr (Matrix.diagonal P.σs * d)) d
  rcases (norm_nonneg d).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_right ?_ hpos
    nlinarith


/-- `‖M𝟏‖ = 1`. -/
theorem Admissible.norm_cv_m (hP : P.Admissible) : ‖cv P.m‖ = 1 := by
  have h : ‖cv P.m‖ ^ 2 = 1 := by rw [norm_cv_sq, hP.sum_m_sq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

variable (P) in
/-- The constant of `step_le`. -/
def stepConst (σ₀ σ₁ a₁ B₀ B₃ ca cb : ℝ) : ℝ :=
  ((B₀ + σ₁ * B₃ / σ₀ + B₀) / P.Δt + 2 / P.Δx * (B₀ + σ₁ * B₃ / σ₀) + a₁ * (B₀ + σ₁ * B₃ / σ₀)) *
    (1 + (σ₁ + σ₀) * (1 / (σ₀ * ca) + B₃ / cb)) / σ₀

namespace IsBUGSubsteps

variable {ε : ℝ} {ρs : ZMod N → ℝ} {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ}
  {V : Matrix κ r ℝ} {K : Matrix (ZMod N) r ℝ} {L : Matrix κ r ℝ} {X₁ : Matrix (ZMod N) p ℝ}
  {V₁ : Matrix κ q ℝ} {S₁ : Matrix p q ℝ}

/-- `K = X₁ R` gives `X₁ X₁ᵀ K = K`, whatever the rank of `R`. -/
theorem captureX (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) : X₁ * X₁ᵀ * K = K := by
  obtain ⟨R, hR⟩ := h.qrX
  have := leftProj_mul_left h.orthX₁ R
  rwa [leftProj_apply, ← hR] at this

/-- `L = V₁ R` gives `Lᵀ V₁ V₁ᵀ = Lᵀ`, whatever the rank of `R`. -/
theorem captureV (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) : Lᵀ * V₁ * V₁ᵀ = Lᵀ := by
  obtain ⟨R, hR⟩ := h.qrV
  have := rightProj_mul_transpose h.orthV₁ Rᵀ
  rw [rightProj_apply] at this
  rwa [hR, Matrix.transpose_mul]

/-- The `K`-step limit and the first balance of the proof of Proposition 7:
`K^{n+1} = ρs (M𝟏)ᵀ Vⁿ + o(1)`, hence `ρs ∈ span X^{n+1} + o(1)` when `(M𝟏)ᵀ Vⁿ ≠ 0`. -/
theorem k_capture {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hlow : ∀ i, σ₀ ≤ P.σs i)
    (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) :
    σ₀ * (‖cv ρs - X₁ * X₁ᵀ * cv ρs‖ * ‖Vᵀ * cv P.m‖) ≤
      ‖rightProj V (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - K * Vᵀ))‖ := by
  set a := Vᵀ * cv P.m with ha
  have hat : (cv P.m)ᵀ * V = aᵀ := by
    rw [ha, Matrix.transpose_mul, Matrix.transpose_transpose]
  set Z := cv ρs * aᵀ - K with hZ
  have hPe : rightProj V (Matrix.vecMulVec ρs P.m - K * Vᵀ) = Z * Vᵀ := by
    rw [map_sub, rightProj_mul_transpose h.orthV K, rightProj_apply, vecMulVec_eq_cv,
      Matrix.mul_assoc (cv ρs), hat, hZ, Matrix.sub_mul]
  have hd : rightProj V (Z * Vᵀ) = Z * Vᵀ := rightProj_mul_transpose h.orthV Z
  have hcomm : rightProj V (Matrix.diagonal P.σs * (Z * Vᵀ)) =
      rightProj V (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - K * Vᵀ)) := by
    have e : ∀ W : Matrix (ZMod N) κ ℝ, rightProj V (Matrix.diagonal P.σs * W) =
        Matrix.diagonal P.σs * rightProj V W := fun W => by
      simp only [rightProj_apply, Matrix.mul_assoc]
    rw [e, e, hd, hPe]
  have h1 := norm_le_of_mem_range (P := P) hlow (isOrthProj_rightProj h.orthV) hd
  rw [hcomm, norm_mul_transpose_of_orthonormal h.orthV] at h1
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hσ₀) h1
  have h2 := (isOrthProj_leftProj (n := r) h.orthX₁).norm_sub_le Z
  have h3 : Z - leftProj X₁ Z = (cv ρs - X₁ * X₁ᵀ * cv ρs) * aᵀ := by
    rw [leftProj_apply, hZ, Matrix.mul_sub, h.captureX, Matrix.sub_mul,
      Matrix.mul_assoc (X₁ * X₁ᵀ)]
    abel
  rwa [h3, norm_mul_transpose_col] at h2

/-- The `L`-step limit: `L^{n+1} (Xⁿ)ᵀ diag(σˢ) Xⁿ = M𝟏 (diag(σˢ) ρs)ᵀ Xⁿ + o(1)`, hence
`M𝟏 ∈ span V^{n+1} + o(1)` when `(Xⁿ)ᵀ diag(σˢ) ρs ≠ 0`, condition (17). -/
theorem l_capture (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) :
    ‖Xᵀ * (Matrix.diagonal P.σs * cv ρs)‖ * ‖cv P.m - V₁ * V₁ᵀ * cv P.m‖ ≤
      ‖leftProj X (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - X * Lᵀ))‖ := by
  set b := Xᵀ * (Matrix.diagonal P.σs * cv ρs) with hb
  set A := Xᵀ * (Matrix.diagonal P.σs * X) with hA
  set Z := b * (cv P.m)ᵀ - A * Lᵀ with hZ
  have h1 : Xᵀ * (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - X * Lᵀ)) = Z := by
    rw [vecMulVec_eq_cv, Matrix.mul_sub, Matrix.mul_sub, hZ, hb, hA]
    simp only [Matrix.mul_assoc]
  rw [← norm_transpose_mul_eq h.orthX, h1]
  have h2 := (isOrthProj_rightProj (m := r) h.orthV₁).norm_sub_le Z
  have h3 : Z - rightProj V₁ Z = b * (cv P.m - V₁ * V₁ᵀ * cv P.m)ᵀ := by
    have e1 : A * Lᵀ * V₁ * V₁ᵀ = A * Lᵀ := by
      rw [Matrix.mul_assoc (A * Lᵀ), Matrix.mul_assoc A, ← Matrix.mul_assoc Lᵀ, h.captureV]
    have e2 : (V₁ * V₁ᵀ * cv P.m)ᵀ = (cv P.m)ᵀ * V₁ * V₁ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [rightProj_apply, hZ, Matrix.sub_mul, Matrix.sub_mul, e1, Matrix.transpose_sub, e2,
      Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    abel
  rwa [h3, norm_mul_transpose_col] at h2

/-- The `S`-step limit: the new iterate is close to `ρs (M𝟏)ᵀ`, once `ρs` and `M𝟏` are close to the
new bases. The `(X^{n+1})ᵀ diag(σˢ) X^{n+1}` of the paper is not inverted. -/
theorem s_estimate (hP : P.Admissible) {σ₀ σ₁ : ℝ} (hσ₀ : 0 < σ₀) (hlow : ∀ i, σ₀ ≤ P.σs i)
    (hup : ∀ i, |P.σs i| ≤ σ₁) (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) :
    σ₀ * ‖X₁ * S₁ * V₁ᵀ - Matrix.vecMulVec ρs P.m‖ ≤
      ‖(leftProj X₁ * rightProj V₁ : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ)
        (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - X₁ * S₁ * V₁ᵀ))‖ +
      (σ₁ + σ₀) * (‖cv ρs - X₁ * X₁ᵀ * cv ρs‖ + ‖cv ρs‖ * ‖cv P.m - V₁ * V₁ᵀ * cv P.m‖) := by
  set e := Matrix.vecMulVec ρs P.m with he
  set Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ := leftProj X₁ * rightProj V₁ with hPr
  set δ := ‖cv ρs - X₁ * X₁ᵀ * cv ρs‖ + ‖cv ρs‖ * ‖cv P.m - V₁ * V₁ᵀ * cv P.m‖ with hδ
  have hS := h.sLift
  set x := X₁ * S₁ * V₁ᵀ with hx
  have hPrA : ∀ Z, Pr Z = leftProj X₁ (rightProj V₁ Z) := fun _ => rfl
  have hee : ‖e - Pr e‖ ≤ δ := by
    have h1 : e - leftProj X₁ e = (cv ρs - X₁ * X₁ᵀ * cv ρs) * (cv P.m)ᵀ := by
      rw [he, vecMulVec_eq_cv, leftProj_apply, Matrix.sub_mul, Matrix.mul_assoc (X₁ * X₁ᵀ)]
    have h2 : e - rightProj V₁ e = cv ρs * (cv P.m - V₁ * V₁ᵀ * cv P.m)ᵀ := by
      have e2 : (V₁ * V₁ᵀ * cv P.m)ᵀ = (cv P.m)ᵀ * V₁ * V₁ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [he, vecMulVec_eq_cv, rightProj_apply, Matrix.transpose_sub, e2, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
    have h3 : e - Pr e = (e - leftProj X₁ e) + leftProj X₁ (e - rightProj V₁ e) := by
      rw [hPrA, map_sub]
      abel
    rw [h3]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [h1, norm_mul_transpose_col, hP.norm_cv_m, mul_one]
    · refine ((isOrthProj_leftProj h.orthX₁).norm_le _).trans ?_
      rw [h2, norm_mul_transpose_col]
  set d := x - Pr e with hd
  have hdP : Pr d = d := by rw [hd, map_sub, hS.mem, hS.proj.idem]
  have h1 := norm_le_of_mem_range (P := P) hlow hS.proj hdP
  have h2 : Matrix.diagonal P.σs * d = -(Matrix.diagonal P.σs * (e - x)) +
      Matrix.diagonal P.σs * (e - Pr e) := by
    rw [hd, ← Matrix.mul_neg, ← Matrix.mul_add]
    congr 1
    abel
  have h3 : ‖Pr (Matrix.diagonal P.σs * d)‖ ≤ ‖Pr (Matrix.diagonal P.σs * (e - x))‖ + σ₁ * δ := by
    rw [h2, map_add, map_neg]
    refine (norm_add_le _ _).trans (add_le_add (norm_neg _).le ?_)
    refine (hS.proj.norm_le _).trans ((norm_diagonal_mul_le hup _).trans ?_)
    have hσ₁ : 0 ≤ σ₁ := (abs_nonneg _).trans (hup 0)
    exact mul_le_mul_of_nonneg_left hee hσ₁
  have h4 : ‖x - e‖ ≤ ‖d‖ + ‖e - Pr e‖ := by
    have : x - e = d - (e - Pr e) := by
      rw [hd]
      abel
    rw [this]
    exact norm_sub_le _ _
  have h5 := mul_le_mul_of_nonneg_left (h4.trans (add_le_add le_rfl hee)) hσ₀.le
  nlinarith

/-- **The one-step bound behind Proposition 7**, at fixed `ε ∈ (0, 1]`. If `‖Yⁿ‖ ≤ B₀`,
`‖ρs‖ ≤ B₃`, and the two nonvanishing conditions (16) and (17) hold quantitatively, namely
`c_a ≤ ‖(M𝟏)ᵀ Vⁿ‖` and `c_b ≤ ‖(Xⁿ)ᵀ diag(σˢ) ρs‖`, then
`‖Y^{n+1} - ρs (M𝟏)ᵀ‖ ≤ C ε`. Nothing is inverted, and the bases may be arbitrarily badly
conditioned. -/
theorem step_le (hP : P.Admissible) (hε : 0 < ε) (hε1 : ε ≤ 1) {σ₀ σ₁ a₁ B₀ B₃ ca cb : ℝ}
    (hσ₀ : 0 < σ₀) (hlow : ∀ i, σ₀ ≤ P.σs i) (hup : ∀ i, |P.σs i| ≤ σ₁)
    (hupa : ∀ i, |P.σa i| ≤ a₁) (hca : 0 < ca) (hcb : 0 < cb)
    (h : P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁) (hY : ‖X * S * Vᵀ‖ ≤ B₀)
    (hρ : ‖cv ρs‖ ≤ B₃) (ha : ca ≤ ‖Vᵀ * cv P.m‖)
    (hb : cb ≤ ‖Xᵀ * (Matrix.diagonal P.σs * cv ρs)‖) :
    ‖X₁ * S₁ * V₁ᵀ - Matrix.vecMulVec ρs P.m‖ ≤ ε * P.stepConst σ₀ σ₁ a₁ B₀ B₃ ca cb := by
  have hΔt := hP.Δt_pos
  have hΔx := hP.Δx_pos
  have hσ₁ : 0 ≤ σ₁ := (abs_nonneg _).trans (hup 0)
  have ha₁ : 0 ≤ a₁ := (abs_nonneg _).trans (hupa 0)
  have hB₀ : 0 ≤ B₀ := (norm_nonneg _).trans hY
  have hB₃ : 0 ≤ B₃ := (norm_nonneg _).trans hρ
  set B₁ := B₀ + σ₁ * B₃ / σ₀ with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  set C := (B₁ + B₀) / P.Δt + 2 / P.Δx * B₁ + a₁ * B₁ with hC
  have hC0 : 0 ≤ C := by positivity
  have hSe : ‖Matrix.diagonal P.σs * Matrix.vecMulVec ρs P.m‖ / σ₀ ≤ σ₁ * B₃ / σ₀ := by
    gcongr
    refine (norm_diagonal_mul_le hup _).trans (mul_le_mul_of_nonneg_left ?_ hσ₁)
    rw [vecMulVec_eq_cv, norm_mul_transpose_col, hP.norm_cv_m, mul_one]
    exact hρ
  have hres : ∀ {Pr : Matrix (ZMod N) κ ℝ →L[ℝ] Matrix (ZMod N) κ ℝ}
      {x : Matrix (ZMod N) κ ℝ}, IsGalerkinStep P ε ρs Pr (X * S * Vᵀ) x →
      ‖Pr (Matrix.diagonal P.σs * (Matrix.vecMulVec ρs P.m - x))‖ ≤ ε * C := by
    intro Pr x hg
    have h1 : ‖x‖ ≤ B₁ := (hg.norm_le hP hε hσ₀ hlow).trans (add_le_add hY hSe)
    refine (hg.residual_le hP hε hupa).trans ?_
    have h2 : ε ^ 2 ≤ ε := by nlinarith
    have h3 : ‖x‖ + ‖X * S * Vᵀ‖ ≤ B₁ + B₀ := add_le_add h1 hY
    have e1 : ε ^ 2 / P.Δt * (‖x‖ + ‖X * S * Vᵀ‖) ≤ ε / P.Δt * (B₁ + B₀) := by
      gcongr
    have e2 : ε * (2 / P.Δx) * ‖x‖ ≤ ε * (2 / P.Δx) * B₁ := by gcongr
    have e3 : ε ^ 2 * a₁ * ‖x‖ ≤ ε * a₁ * B₁ := by gcongr
    have e4 : ε * C = ε / P.Δt * (B₁ + B₀) + ε * (2 / P.Δx) * B₁ + ε * a₁ * B₁ := by
      rw [hC]
      ring
    linarith
  have hK := h.k_capture hσ₀.le hlow
  have hL := h.l_capture
  have hS := h.s_estimate hP hσ₀ hlow hup
  have rK := hres h.kLift
  have rL := hres h.lLift
  have rS := hres h.sLift
  set δX := ‖cv ρs - X₁ * X₁ᵀ * cv ρs‖ with hδX
  set δV := ‖cv P.m - V₁ * V₁ᵀ * cv P.m‖ with hδV
  have hδX0 : 0 ≤ δX := norm_nonneg _
  have hδV0 : 0 ≤ δV := norm_nonneg _
  have h1 : δX ≤ ε * C * (1 / (σ₀ * ca)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    have h2 : σ₀ * (δX * ca) ≤ σ₀ * (δX * ‖Vᵀ * cv P.m‖) := by gcongr
    linarith
  have h2 : δV ≤ ε * C * (1 / cb) := by
    rw [mul_one_div, le_div_iff₀ hcb]
    have h3 : cb * δV ≤ ‖Xᵀ * (Matrix.diagonal P.σs * cv ρs)‖ * δV := by gcongr
    linarith
  have h3 : ‖cv ρs‖ * δV ≤ ε * C * (B₃ / cb) := by
    calc ‖cv ρs‖ * δV ≤ B₃ * (ε * C * (1 / cb)) := mul_le_mul hρ h2 hδV0 hB₃
      _ = ε * C * (B₃ / cb) := by ring
  have h4 : (σ₁ + σ₀) * (δX + ‖cv ρs‖ * δV) ≤
      (σ₁ + σ₀) * (ε * C * (1 / (σ₀ * ca) + B₃ / cb)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_add]
    exact add_le_add h1 h3
  have h5 : σ₀ * ‖X₁ * S₁ * V₁ᵀ - Matrix.vecMulVec ρs P.m‖ ≤
      ε * C * (1 + (σ₁ + σ₀) * (1 / (σ₀ * ca) + B₃ / cb)) := by
    have e : ε * C * (1 + (σ₁ + σ₀) * (1 / (σ₀ * ca) + B₃ / cb)) =
        ε * C + (σ₁ + σ₀) * (ε * C * (1 / (σ₀ * ca) + B₃ / cb)) := by ring
    rw [e]
    linarith
  have e : ε * P.stepConst σ₀ σ₁ a₁ B₀ B₃ ca cb =
      ε * C * (1 + (σ₁ + σ₀) * (1 / (σ₀ * ca) + B₃ / cb)) / σ₀ := by
    rw [stepConst, ← hB₁, hC]
    ring
  rw [e, le_div_iff₀ hσ₀]
  linarith

end IsBUGSubsteps

/-! The limit `ε → 0` of the density solve. -/

/-- `‖u‖_Δx = √Δx ‖u‖₂`. -/
theorem gridNorm_eq {Δx : ℝ} (hΔx : 0 ≤ Δx) (u : ZMod N → ℝ) :
    gridNorm Δx u = √Δx * ‖cv u‖ := by
  rw [gridNorm, gridInner_self_eq, Real.sqrt_mul hΔx, ← norm_cv_sq,
    Real.sqrt_sq (norm_nonneg _)]

/-- Taking columns is additive. -/
theorem cv_sub {ι : Type*} (u v : ι → ℝ) : cv (u - v) = cv u - cv v := rfl

/-- `α₁ ≤ ε² / (σ₀ Δt)`. -/
theorem Admissible.abs_alpha1_le (hP : P.Admissible) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    (hlow : ∀ i, σ₀ ≤ P.σs i) {ε : ℝ} (hε : 0 < ε) (i : ZMod N) :
    P.alpha1 ε i ≤ ε * (ε / (σ₀ * P.Δt)) := by
  have h1 := hP.norm_alpha1_div_le hσ₀ hlow hε
  rw [div_le_iff₀ hε] at h1
  have h2 : |P.alpha1 ε i| ≤ ‖P.alpha1 ε‖ := by simpa using norm_le_pi_norm (P.alpha1 ε) i
  rw [abs_of_nonneg (hP.alpha1_nonneg ε i)] at h2
  linarith

/-- `β → 1 / (3 σˢ)` as `ε → 0`: this is `α₂ → 1`. -/
theorem Admissible.tendsto_beta (hP : P.Admissible) :
    Tendsto (fun ε => ‖P.beta ε - P.betaLim‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨σ₀, σ₁, hσ₀, -, hlow, -⟩ := hP.exists_crossSection
  have hΔt := hP.Δt_pos
  have key : Tendsto (fun ε => P.beta ε) (𝓝[>] 0) (𝓝 P.betaLim) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    have hσ := hP.σs_pos i
    have ha := hP.σa_nonneg i
    have h1 : Tendsto (fun ε => P.alpha1 ε i) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => ε * (ε / (σ₀ * P.Δt))) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => ε * (ε / (σ₀ * P.Δt))) (𝓝 0) (𝓝 (0 * (0 / (σ₀ * P.Δt)))) :=
          tendsto_id.mul (tendsto_id.div_const _)
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero' (Eventually.of_forall fun ε => hP.alpha1_nonneg ε i) ?_ h0
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hP.abs_alpha1_le hσ₀ hlow hε i
    have h2 : Tendsto (fun ε : ℝ => (P.σs i / (P.σs i + P.σa i * ε ^ 2)) ^ 2 *
        (1 - P.alpha1 ε i) / (3 * P.σs i)) (𝓝[>] 0) (𝓝 (P.betaLim i)) := by
      have h3 : Tendsto (fun ε : ℝ => P.σs i / (P.σs i + P.σa i * ε ^ 2)) (𝓝[>] 0)
          (𝓝 (P.σs i / (P.σs i + P.σa i * 0 ^ 2))) := by
        refine (Tendsto.div tendsto_const_nhds ?_ (by simpa using hσ.ne')).mono_left
          nhdsWithin_le_nhds
        exact (Continuous.tendsto (by fun_prop) 0)
      have h4 := ((h3.pow 2).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub h1)).div_const
        (3 * P.σs i)
      have e : (P.σs i / (P.σs i + P.σa i * 0 ^ 2)) ^ 2 * (1 - 0) / (3 * P.σs i) = P.betaLim i := by
        rw [betaLim]
        field_simp
        simp
      rwa [e] at h4
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have e : P.mu ε i * ε ^ 2 = P.σs i + P.σa i * ε ^ 2 := by
      rw [mu]
      field_simp
    simp only [beta, alpha2, e, alpha1]
  have := tendsto_iff_norm_sub_tendsto_zero.1 key
  simpa using this

/-- `|L_γ u| ≤ 4 ‖γ‖_∞ ‖u‖_∞ / Δx²`. -/
theorem abs_lapBeta_le {Δx : ℝ} (hΔx : 0 < Δx) (γ : ZMod N → ℝ) {u : ZMod N → ℝ} {U : ℝ}
    (hu : ∀ i, |u i| ≤ U) (i : ZMod N) : |lapBeta Δx γ u i| ≤ 4 * ‖γ‖ * U / Δx ^ 2 := by
  have hγ : ∀ l, |γ l| ≤ ‖γ‖ := fun l => by simpa using norm_le_pi_norm γ l
  have hh : ∀ l, |betaHalf γ l| ≤ ‖γ‖ := fun l => by
    rw [betaHalf, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    linarith [abs_add_le (γ l) (γ (l + 1)), hγ l, hγ (l + 1)]
  have hd : ∀ a b, |u a - u b| ≤ 2 * U := fun a b => by
    linarith [abs_sub (u a) (u b), hu a, hu b]
  rw [lapBeta, abs_div, abs_of_pos (by positivity : 0 < Δx ^ 2)]
  gcongr
  calc |betaHalf γ i * (u (i + 1) - u i) - betaHalf γ (i - 1) * (u i - u (i - 1))|
      ≤ |betaHalf γ i * (u (i + 1) - u i)| + |betaHalf γ (i - 1) * (u i - u (i - 1))| :=
        abs_sub _ _
    _ ≤ ‖γ‖ * (2 * U) + ‖γ‖ * (2 * U) := by
        rw [abs_mul, abs_mul]
        have hU : 0 ≤ 2 * U := (abs_nonneg _).trans (hd 0 0)
        exact add_le_add (mul_le_mul (hh _) (hd _ _) (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul (hh _) (hd _ _) (abs_nonneg _) (norm_nonneg _))
    _ = 4 * ‖γ‖ * U := by ring

/-- **The density solve converges to the limiting diffusion update**: if the data `ρ` and the flux
derivatives `J` are bounded uniformly in `ε`, the solution of (6) or (8) and the solution `ρ0` of
`(I - Δt L_{1/(3σˢ)} + Δt diag(σᵃ)) ρ0 = ρ` have the same limit as `ε → 0`. This covers the
semi-Lagrangian foot points, whose integer parts tend to infinity with `1/ε`. -/
theorem tendsto_macro (hP : P.Admissible) {ρ J ρs ρ0 : ℝ → ZMod N → ℝ} {B CJ : ℝ}
    (hρ : ∀ᶠ ε in 𝓝[>] 0, ∀ i, |ρ ε i| ≤ B) (hJ : ∀ᶠ ε in 𝓝[>] 0, ∀ i, |J ε i| ≤ CJ)
    (hs : ∀ᶠ ε in 𝓝[>] 0, P.IsMacroSolve ε (ρ ε) (J ε) (ρs ε))
    (h0 : ∀ᶠ ε in 𝓝[>] 0, ∀ i, P.macroOp P.betaLim (ρ0 ε) i = ρ ε i) :
    Tendsto (fun ε => gridNorm P.Δx (ρs ε - ρ0 ε)) (𝓝[>] 0) (𝓝 0) := by
  have hΔx := hP.Δx_pos
  have hΔt := hP.Δt_pos
  have hsq : 0 < √P.Δx := Real.sqrt_pos.2 hΔx
  have hβ0 : ∀ i, 0 ≤ P.betaLim i := fun i => (hP.betaLim_pos i).le
  set t₁ : ℝ → ℝ := fun ε => P.Δt * (‖P.alpha1 ε‖ / ε) * CJ with ht₁
  have ht₁0 : Tendsto t₁ (𝓝[>] 0) (𝓝 0) := by
    have := (hP.tendsto_norm_alpha1_div.const_mul P.Δt).mul_const CJ
    simpa using this
  set U : ℝ → ℝ := fun ε => √(N * P.Δx) * (B + t₁ ε) / √P.Δx with hU
  set t₃ : ℝ → ℝ := fun ε => t₁ ε + P.Δt * (4 * ‖P.beta ε - P.betaLim‖ * U ε / P.Δx ^ 2) with ht₃
  have hU0 : Tendsto U (𝓝[>] 0) (𝓝 (√(N * P.Δx) * (B + 0) / √P.Δx)) :=
    ((tendsto_const_nhds.add ht₁0).const_mul _).div_const _
  have ht₃0 : Tendsto t₃ (𝓝[>] 0) (𝓝 (0 + P.Δt * (4 * 0 * (√(N * P.Δx) * (B + 0) / √P.Δx) /
      P.Δx ^ 2))) :=
    ht₁0.add ((((hP.tendsto_beta.const_mul 4).mul hU0).div_const _).const_mul _)
  have hlim : Tendsto (fun ε => √(N * P.Δx) * t₃ ε) (𝓝[>] 0) (𝓝 0) := by
    have := ht₃0.const_mul (√(N * P.Δx))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun ε => gridNorm_nonneg _ _) ?_ hlim
  filter_upwards [hρ, hJ, hs, h0, self_mem_nhdsWithin] with ε hρε hJε hsε h0ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hαJ : ∀ i, |P.Δt / ε * (P.alpha1 ε i * J ε i)| ≤ t₁ ε := fun i => by
    have h1 : |P.alpha1 ε i| ≤ ‖P.alpha1 ε‖ := by simpa using norm_le_pi_norm (P.alpha1 ε) i
    have hCJ : 0 ≤ CJ := (abs_nonneg _).trans (hJε 0)
    rw [abs_mul, abs_mul, abs_of_pos (div_pos hΔt hε')]
    calc P.Δt / ε * (|P.alpha1 ε i| * |J ε i|) ≤ P.Δt / ε * (‖P.alpha1 ε‖ * CJ) := by
          gcongr
          exact hJε i
      _ = t₁ ε := by simp only [ht₁]; ring
  have ht₁n : 0 ≤ t₁ ε := (abs_nonneg _).trans (hαJ 0)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hρε 0)
  have hA : ∀ i, |P.macroOp (P.beta ε) (ρs ε) i| ≤ B + t₁ ε := fun i => by
    rw [hsε i]
    exact (abs_sub _ _).trans (add_le_add (hρε i) (hαJ i))
  have hn1 : gridNorm P.Δx (ρs ε) ≤ √(N * P.Δx) * (B + t₁ ε) :=
    (gridNorm_le_macroOp hP (hP.beta_nonneg ε) _).trans
      (gridNorm_le_of_abs_le hΔx.le (by positivity) hA)
  have hsup : ∀ i, |ρs ε i| ≤ U ε := fun i => by
    have h1 : |ρs ε i| ≤ ‖cv (ρs ε)‖ := abs_apply_le_norm (cv (ρs ε)) i ()
    rw [gridNorm_eq hΔx.le] at hn1
    simp only [hU]
    rw [le_div_iff₀ hsq]
    nlinarith
  have hdiff : ∀ i, P.macroOp P.betaLim (ρs ε - ρ0 ε) i =
      -(P.Δt / ε * (P.alpha1 ε i * J ε i)) +
        P.Δt * lapBeta P.Δx (P.beta ε - P.betaLim) (ρs ε) i := by
    intro i
    have h1 := hsε i
    have h2 := lapBeta_sub P.Δx (P.beta ε) P.betaLim (ρs ε) i
    rw [macroOp_sub, h0ε i, ← h2]
    simp only [macroOp] at h1 ⊢
    linear_combination h1
  have hB3 : ∀ i, |P.macroOp P.betaLim (ρs ε - ρ0 ε) i| ≤ t₃ ε := fun i => by
    rw [hdiff i]
    refine (abs_add_le _ _).trans (add_le_add ((abs_neg _).le.trans (hαJ i)) ?_)
    rw [abs_mul, abs_of_pos hΔt]
    exact mul_le_mul_of_nonneg_left (abs_lapBeta_le hΔx _ hsup i) hΔt.le
  have ht₃n : 0 ≤ t₃ ε := (abs_nonneg _).trans (hB3 0)
  exact (gridNorm_le_macroOp hP hβ0 _).trans (gridNorm_le_of_abs_le hΔx.le ht₃n hB3)

/-- `ρ = Y M𝟏`, the density of a weighted state. -/
theorem Admissible.cv_density (hP : P.Admissible) (Y : Matrix (ZMod N) κ ℝ) :
    cv (P.density (Y * P.Minv)) = Y * cv P.m := by
  ext i c
  have h1 : P.density (Y * P.Minv) i = ∑ j, Y i j * P.m j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := (hP.m_pos j).ne'
    rw [Minv, Matrix.mul_diagonal, ← hP.m_sq]
    field_simp
  simp [Matrix.mul_apply, h1]

/-- The balance of `A_ρ ρ0 = ρ` at one grid point. -/
theorem diffusion_balance {β ρ ρ0 : ZMod N → ℝ} (h : ∀ i, P.macroOp β ρ0 i = ρ i) (i : ZMod N) :
    (1 + P.Δt * P.σa i + P.Δt * (betaHalf β i + betaHalf β (i - 1)) / P.Δx ^ 2) * ρ0 i =
      ρ i + P.Δt * (betaHalf β i * ρ0 (i + 1) + betaHalf β (i - 1) * ρ0 (i - 1)) / P.Δx ^ 2 := by
  have h1 := h i
  simp only [macroOp, lapBeta] at h1
  linear_combination h1

/-- The discrete maximum principle for `A_ρ`, used for the condition (17): `ρ ≥ 0` gives `ρ0 ≥ 0`,
with `ρ ≤ d ρ0` for the diagonal `d` of `A_ρ`. The paper uses this implicitly. -/
theorem diffusion_nonneg (hP : P.Admissible) {β ρ ρ0 : ZMod N → ℝ} (hβ : ∀ i, 0 ≤ β i)
    (hρ : ∀ i, 0 ≤ ρ i) (h : ∀ i, P.macroOp β ρ0 i = ρ i) (i : ZMod N) : 0 ≤ ρ0 i := by
  have hΔt := hP.Δt_pos
  have hΔx := hP.Δx_pos
  have hh : ∀ l, 0 ≤ betaHalf β l := fun l =>
    div_nonneg (add_nonneg (hβ _) (hβ _)) (by norm_num)
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min ρ0
  refine le_trans ?_ (hi₀ i)
  have h1 := h i₀
  simp only [macroOp, lapBeta] at h1
  have h2 : 0 ≤ P.Δt * ((betaHalf β i₀ * (ρ0 (i₀ + 1) - ρ0 i₀) +
      betaHalf β (i₀ - 1) * (ρ0 (i₀ - 1) - ρ0 i₀)) / P.Δx ^ 2) := by
    have e1 := mul_nonneg (hh i₀) (sub_nonneg.2 (hi₀ (i₀ + 1)))
    have e2 := mul_nonneg (hh (i₀ - 1)) (sub_nonneg.2 (hi₀ (i₀ - 1)))
    positivity
  have h3 : (1 + P.Δt * P.σa i₀) * ρ0 i₀ = ρ i₀ + P.Δt * ((betaHalf β i₀ * (ρ0 (i₀ + 1) - ρ0 i₀) +
      betaHalf β (i₀ - 1) * (ρ0 (i₀ - 1) - ρ0 i₀)) / P.Δx ^ 2) := by
    linear_combination h1
  have h4 : 0 < 1 + P.Δt * P.σa i₀ := by
    have := mul_nonneg hΔt.le (hP.σa_nonneg i₀)
    linarith
  have h5 := hρ i₀
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_pos_of_neg h4 hneg]

/-- The positivity of the limiting update behind (17): for `ρ ≥ 0`,
`c ‖ρ‖² ≤ ⟨ρ, diag(σˢ) ρ0⟩` with `c > 0` independent of `ρ`. -/
theorem Admissible.exists_diffusion_coercive (hP : P.Admissible) :
    ∃ c₃ > 0, ∀ ρ ρ0 : ZMod N → ℝ, (∀ i, 0 ≤ ρ i) → (∀ i, P.macroOp P.betaLim ρ0 i = ρ i) →
      c₃ * ‖cv ρ‖ ^ 2 ≤ ⟪cv ρ, Matrix.diagonal P.σs * cv ρ0⟫ := by
  obtain ⟨σ₀, σ₁, hσ₀, -, hlow, -⟩ := hP.exists_crossSection
  have hΔt := hP.Δt_pos
  have hΔx := hP.Δx_pos
  have hβ : ∀ i, 0 ≤ P.betaLim i := fun i => (hP.betaLim_pos i).le
  have hh : ∀ l, 0 ≤ betaHalf P.betaLim l := fun l =>
    div_nonneg (add_nonneg (hβ _) (hβ _)) (by norm_num)
  set d : ZMod N → ℝ := fun i => 1 + P.Δt * P.σa i +
    P.Δt * (betaHalf P.betaLim i + betaHalf P.betaLim (i - 1)) / P.Δx ^ 2 with hd
  have hd1 : ∀ i, 1 ≤ d i := fun i => by
    have h1 := mul_nonneg hΔt.le (hP.σa_nonneg i)
    have h2 : 0 ≤ P.Δt * (betaHalf P.betaLim i + betaHalf P.betaLim (i - 1)) / P.Δx ^ 2 :=
      div_nonneg (mul_nonneg hΔt.le (add_nonneg (hh _) (hh _))) (by positivity)
    simp only [hd]
    linarith
  set D := ∑ i, d i with hD
  have hdD : ∀ i, d i ≤ D := fun i =>
    Finset.single_le_sum (fun l _ => (zero_le_one.trans (hd1 l))) (Finset.mem_univ i)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one ((hd1 0).trans (hdD 0))
  refine ⟨σ₀ / D, by positivity, fun ρ ρ0 hρ h => ?_⟩
  have hρ0 := diffusion_nonneg hP hβ hρ h
  have e1 : ‖cv ρ‖ ^ 2 = ∑ i, ρ i ^ 2 := norm_cv_sq ρ
  have e2 : ⟪cv ρ, Matrix.diagonal P.σs * cv ρ0⟫ = ∑ i, P.σs i * (ρ i * ρ0 i) := by
    rw [inner_def]
    simp [Matrix.diagonal_mul, mul_left_comm]
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := diffusion_balance h i
  have h2 : 0 ≤ P.Δt * (betaHalf P.betaLim i * ρ0 (i + 1) +
      betaHalf P.betaLim (i - 1) * ρ0 (i - 1)) / P.Δx ^ 2 := by
    have e3 := mul_nonneg (hh i) (hρ0 (i + 1))
    have e4 := mul_nonneg (hh (i - 1)) (hρ0 (i - 1))
    positivity
  have h3 : ρ i ≤ D * ρ0 i := by
    have h4 : d i * ρ0 i ≤ D * ρ0 i := mul_le_mul_of_nonneg_right (hdD i) (hρ0 i)
    have h5 : d i * ρ0 i = _ := h1
    linarith
  have h4 : ρ i ^ 2 ≤ D * (ρ i * ρ0 i) := by nlinarith [hρ i]
  have h5 : σ₀ * ρ i ^ 2 ≤ P.σs i * (D * (ρ i * ρ0 i)) := by
    have := mul_le_mul (hlow i) h4 (sq_nonneg _) (hP.σs_pos i).le
    exact this
  rw [div_mul_eq_mul_div, div_le_iff₀ hD0]
  linarith

/-- The core of Proposition 7: the BUG step started from a state with `ρ ≥ 0` and `‖ρ‖ ≥ c`, with
any `ρs = ρ0 + o(1)`, returns `ρ0 (M𝟏)ᵀ + o(1)`. The two nonvanishing conditions (16) and (17) are
derived, not assumed. -/
theorem prop7_core (hP : P.Admissible)
    {X : ℝ → Matrix (ZMod N) r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix κ r ℝ}
    {K : ℝ → Matrix (ZMod N) r ℝ} {L : ℝ → Matrix κ r ℝ} {X₁ : ℝ → Matrix (ZMod N) p ℝ}
    {V₁ : ℝ → Matrix κ q ℝ} {S₁ : ℝ → Matrix p q ℝ} {ρs ρ0 : ℝ → ZMod N → ℝ} {B c : ℝ}
    (hc : 0 < c)
    (hstep : ∀ᶠ ε in 𝓝[>] 0, P.IsBUGSubsteps ε (ρs ε) (X ε) (S ε) (V ε) (K ε) (L ε) (X₁ ε) (V₁ ε)
      (S₁ ε))
    (hY : ∀ᶠ ε in 𝓝[>] 0, ‖X ε * S ε * (V ε)ᵀ‖ ≤ B)
    (hlow : ∀ᶠ ε in 𝓝[>] 0, c ≤ ‖cv (P.density (X ε * S ε * (V ε)ᵀ * P.Minv))‖)
    (hnn : ∀ᶠ ε in 𝓝[>] 0, ∀ i, 0 ≤ P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i)
    (h0 : ∀ᶠ ε in 𝓝[>] 0, ∀ i, P.macroOp P.betaLim (ρ0 ε) i =
      P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i)
    (hρs : Tendsto (fun ε => ‖cv (ρs ε - ρ0 ε)‖) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ‖X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec (ρ0 ε) P.m‖) (𝓝[>] 0) (𝓝 0) := by
  have hΔx := hP.Δx_pos
  have hsq : 0 < √P.Δx := Real.sqrt_pos.2 hΔx
  obtain ⟨σ₀, σ₁', hσ₀, -, hlowσ, hupσ⟩ := hP.exists_crossSection
  obtain ⟨c₃, hc₃, hcoer⟩ := hP.exists_diffusion_coercive
  set σ₁ := |σ₁'| + 1 with hσ₁
  have hσ₁0 : 0 < σ₁ := by positivity
  have hup : ∀ i, |P.σs i| ≤ σ₁ := fun i => by
    rw [abs_of_pos (hP.σs_pos i)]
    linarith [hupσ i, le_abs_self σ₁']
  set a₁ := ∑ i, |P.σa i| with ha₁
  have hupa : ∀ i, |P.σa i| ≤ a₁ := fun i =>
    Finset.single_le_sum (fun l _ => abs_nonneg (P.σa l)) (Finset.mem_univ i)
  -- the eventual smallness of `ρs - ρ0`
  have hsmall : ∀ᶠ ε in 𝓝[>] 0, ‖cv (ρs ε - ρ0 ε)‖ < min 1 (c₃ * c / (2 * σ₁)) :=
    hρs.eventually (gt_mem_nhds (lt_min one_pos (by positivity)))
  have hB0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, c ≤ B := by
    filter_upwards [hY, hlow] with ε h1 h2
    have hP1 := hP.cv_density (X ε * S ε * (V ε)ᵀ)
    have h3 : ‖cv (P.density (X ε * S ε * (V ε)ᵀ * P.Minv))‖ ≤ ‖X ε * S ε * (V ε)ᵀ‖ * 1 := by
      rw [hP1, ← hP.norm_cv_m]
      exact Frobenius.norm_mul_le _ _
    linarith
  have hcB : c ≤ B := by
    obtain ⟨ε, hε⟩ := hB0.exists
    exact hε
  have hB : 0 < B := lt_of_lt_of_le hc hcB
  set ca := c / B with hca
  set cb := c₃ * c / 2 with hcb
  have hca0 : 0 < ca := by positivity
  have hcb0 : 0 < cb := by positivity
  set C := P.stepConst σ₀ σ₁ a₁ B (B + 1) ca cb with hC
  have h0lim : Tendsto (fun ε : ℝ => ε * C + ‖cv (ρs ε - ρ0 ε)‖) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε * C) (𝓝[>] 0) (𝓝 (0 * C)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const C
    simpa using h1.add hρs
  refine squeeze_zero' (Eventually.of_forall fun ε => norm_nonneg _) ?_ h0lim
  filter_upwards [hstep, hY, hlow, hnn, h0, hsmall, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with
    ε hs hYε hlε hnε h0ε hsε hε
  obtain ⟨hε0, hε1⟩ := hε
  set Y := X ε * S ε * (V ε)ᵀ with hYdef
  set ρ := P.density (Y * P.Minv) with hρ
  have hcvρ : cv ρ = Y * cv P.m := hP.cv_density Y
  have hρB : ‖cv ρ‖ ≤ B := by
    have h3 : ‖cv ρ‖ ≤ ‖Y‖ * 1 := by
      rw [hcvρ, ← hP.norm_cv_m]
      exact Frobenius.norm_mul_le _ _
    linarith
  have hsε1 : ‖cv (ρs ε - ρ0 ε)‖ < 1 := hsε.trans_le (min_le_left _ _)
  have hsε2 : σ₁ * ‖cv (ρs ε - ρ0 ε)‖ ≤ cb := by
    have h1 : ‖cv (ρs ε - ρ0 ε)‖ < c₃ * c / (2 * σ₁) := hsε.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    rw [hcb]
    nlinarith
  -- the bound of `ρ0` and of `ρs`
  have hρ0 : ‖cv (ρ0 ε)‖ ≤ ‖cv ρ‖ := by
    have h1 := gridNorm_le_macroOp hP (fun i => (hP.betaLim_pos i).le) (ρ0 ε)
    have h2 : P.macroOp P.betaLim (ρ0 ε) = ρ := funext h0ε
    rw [h2, gridNorm_eq hΔx.le, gridNorm_eq hΔx.le] at h1
    exact le_of_mul_le_mul_left h1 hsq
  have hρsB : ‖cv (ρs ε)‖ ≤ B + 1 := by
    have h1 : cv (ρs ε) = cv (ρs ε - ρ0 ε) + cv (ρ0 ε) := by
      rw [cv_sub]
      abel
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    linarith
  -- condition (16)
  have hXS : ‖X ε * S ε‖ = ‖Y‖ := (norm_mul_transpose_of_orthonormal hs.orthV _).symm
  have hcvρ2 : cv ρ = X ε * S ε * ((V ε)ᵀ * cv P.m) := by
    rw [hcvρ, hYdef]
    simp only [Matrix.mul_assoc]
  have ha : ca ≤ ‖(V ε)ᵀ * cv P.m‖ := by
    have h1 : ‖cv ρ‖ ≤ ‖X ε * S ε‖ * ‖(V ε)ᵀ * cv P.m‖ := by
      rw [hcvρ2]
      exact Frobenius.norm_mul_le _ _
    rw [hXS] at h1
    rw [hca, div_le_iff₀ hB]
    have h2 : ‖Y‖ * ‖(V ε)ᵀ * cv P.m‖ ≤ B * ‖(V ε)ᵀ * cv P.m‖ := by gcongr
    linarith
  -- condition (17)
  have hb : cb ≤ ‖(X ε)ᵀ * (Matrix.diagonal P.σs * cv (ρs ε))‖ := by
    set b := (X ε)ᵀ * (Matrix.diagonal P.σs * cv (ρs ε)) with hbdef
    set pv := S ε * ((V ε)ᵀ * cv P.m) with hpv
    have hcvρ3 : cv ρ = X ε * pv := by
      rw [hcvρ2, hpv, Matrix.mul_assoc]
    have h1 : ‖pv‖ = ‖cv ρ‖ := by
      rw [hcvρ3, norm_mul_of_orthonormal hs.orthX]
    have h2 : ⟪cv ρ, Matrix.diagonal P.σs * cv (ρs ε)⟫ ≤ ‖cv ρ‖ * ‖b‖ := by
      rw [hcvρ3, Frobenius.inner_mul_left, ← hcvρ3, ← h1]
      exact real_inner_le_norm _ _
    have h3 := hcoer ρ (ρ0 ε) hnε h0ε
    have h4 : ⟪cv ρ, Matrix.diagonal P.σs * cv (ρs ε)⟫ =
        ⟪cv ρ, Matrix.diagonal P.σs * cv (ρ0 ε)⟫ +
        ⟪cv ρ, Matrix.diagonal P.σs * cv (ρs ε - ρ0 ε)⟫ := by
      rw [← inner_add_right, ← Matrix.mul_add, cv_sub]
      congr 2
      abel
    have h5 : -(‖cv ρ‖ * (σ₁ * ‖cv (ρs ε - ρ0 ε)‖)) ≤
        ⟪cv ρ, Matrix.diagonal P.σs * cv (ρs ε - ρ0 ε)⟫ := by
      have h6 := abs_real_inner_le_norm (cv ρ) (Matrix.diagonal P.σs * cv (ρs ε - ρ0 ε))
      have h7 := norm_diagonal_mul_le hup (cv (ρs ε - ρ0 ε))
      have h8 := (abs_le.1 h6).1
      have h9 : ‖cv ρ‖ * ‖Matrix.diagonal P.σs * cv (ρs ε - ρ0 ε)‖ ≤
          ‖cv ρ‖ * (σ₁ * ‖cv (ρs ε - ρ0 ε)‖) := by gcongr
      linarith
    have hcρ : 0 < ‖cv ρ‖ := lt_of_lt_of_le hc hlε
    have h10 : ‖cv ρ‖ * (c₃ * ‖cv ρ‖ - σ₁ * ‖cv (ρs ε - ρ0 ε)‖) ≤ ‖cv ρ‖ * ‖b‖ := by
      nlinarith
    have h11 := le_of_mul_le_mul_left h10 hcρ
    have h12 : c₃ * c ≤ c₃ * ‖cv ρ‖ := by gcongr
    have h13 : cb = c₃ * c - cb := by
      rw [hcb]
      ring
    linarith
  have hstepb := hs.step_le hP hε0 hε1.le hσ₀ hlowσ hup hupa hca0 hcb0 hYε hρsB ha hb
  have hsplit : X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec (ρ0 ε) P.m =
      (X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec (ρs ε) P.m) +
        cv (ρs ε - ρ0 ε) * (cv P.m)ᵀ := by
    rw [vecMulVec_eq_cv, vecMulVec_eq_cv, cv_sub, Matrix.sub_mul]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add hstepb ?_)
  rw [norm_mul_transpose_col, hP.norm_cv_m, mul_one]

/-- From `‖ρ‖` and the bound of Lemma 4 to a bound of `Yⁿ`. -/
theorem Admissible.norm_le_of_bounds (hP : P.Admissible) {Y : Matrix (ZMod N) κ ℝ} {Cg B : ℝ}
    (hG : ∀ i j, |(Y * P.Minv) i j - P.density (Y * P.Minv) i| ≤ Cg)
    (hB : gridNorm P.Δx (P.density (Y * P.Minv)) ≤ B) :
    ‖Y‖ ≤ √(B ^ 2 / P.Δx + N * Cg ^ 2) := by
  have hΔx := hP.Δx_pos
  have h1 := eq19 hP (Y * P.Minv)
  rw [hP.mul_Minv_mul_M, gridFrobSq_eq, gridFrobSq_eq] at h1
  have h2 : ‖P.nonEq (Y * P.Minv)‖ ^ 2 ≤ N * Cg ^ 2 := by
    rw [norm_sq_eq_sum]
    calc ∑ i, ∑ j, P.nonEq (Y * P.Minv) i j ^ 2 ≤ ∑ _i : ZMod N, Cg ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            calc ∑ j, P.nonEq (Y * P.Minv) i j ^ 2 ≤ ∑ j, Cg ^ 2 * P.w j :=
                  Finset.sum_le_sum fun j _ => by
                    rw [nonEq_apply, mul_pow, hP.m_sq]
                    refine mul_le_mul_of_nonneg_right ?_ (hP.w_pos j).le
                    rw [← sq_abs]
                    exact pow_le_pow_left₀ (abs_nonneg _) (hG i j) 2
              _ = Cg ^ 2 := by rw [← Finset.mul_sum, hP.w_sum, mul_one]
      _ = N * Cg ^ 2 := by simp [Finset.card_univ, ZMod.card]
  have h3 : gridNorm P.Δx (P.density (Y * P.Minv)) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (gridNorm_nonneg _ _) hB 2
  refine Real.le_sqrt_of_sq_le ?_
  have h4 : ‖Y‖ ^ 2 =
      gridNorm P.Δx (P.density (Y * P.Minv)) ^ 2 / P.Δx + ‖P.nonEq (Y * P.Minv)‖ ^ 2 := by
    field_simp
    linarith
  have h5 : gridNorm P.Δx (P.density (Y * P.Minv)) ^ 2 / P.Δx ≤ B ^ 2 / P.Δx := by gcongr
  linarith

/-- The common form of Proposition 7: one step with a density solve whose flux derivative `J` is
bounded uniformly in `ε`. -/
theorem prop7_of_flux (hP : P.Admissible)
    {X : ℝ → Matrix (ZMod N) r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix κ r ℝ}
    {K : ℝ → Matrix (ZMod N) r ℝ} {L : ℝ → Matrix κ r ℝ} {X₁ : ℝ → Matrix (ZMod N) p ℝ}
    {V₁ : ℝ → Matrix κ q ℝ} {S₁ : ℝ → Matrix p q ℝ} {ρs ρ0 J : ℝ → ZMod N → ℝ} {Cg B c CJ : ℝ}
    (hc : 0 < c)
    (hmacro : ∀ᶠ ε in 𝓝[>] 0, P.IsMacroSolve ε (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)) (J ε)
      (ρs ε))
    (hstep : ∀ᶠ ε in 𝓝[>] 0, P.IsBUGSubsteps ε (ρs ε) (X ε) (S ε) (V ε) (K ε) (L ε) (X₁ ε) (V₁ ε)
      (S₁ ε))
    (hJ : ∀ᶠ ε in 𝓝[>] 0, ∀ i, |J ε i| ≤ CJ)
    (hG : ∀ᶠ ε in 𝓝[>] 0, ∀ i j, |(X ε * S ε * (V ε)ᵀ * P.Minv) i j -
      P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i| ≤ Cg)
    (hB : ∀ᶠ ε in 𝓝[>] 0, gridNorm P.Δx (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)) ≤ B)
    (hlow : ∀ᶠ ε in 𝓝[>] 0, c ≤ gridNorm P.Δx (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)))
    (hnn : ∀ᶠ ε in 𝓝[>] 0, ∀ i, 0 ≤ P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i)
    (h0 : ∀ᶠ ε in 𝓝[>] 0, ∀ i, P.macroOp P.betaLim (ρ0 ε) i =
      P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i) :
    Tendsto (fun ε => ‖X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec (ρ0 ε) P.m‖) (𝓝[>] 0) (𝓝 0) := by
  have hΔx := hP.Δx_pos
  have hsq : 0 < √P.Δx := Real.sqrt_pos.2 hΔx
  have hρsup : ∀ᶠ ε in 𝓝[>] 0, ∀ i, |P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i| ≤ B / √P.Δx := by
    filter_upwards [hB] with ε h i
    have h1 := abs_apply_le_norm (cv (P.density (X ε * S ε * (V ε)ᵀ * P.Minv))) i ()
    rw [gridNorm_eq hΔx.le] at h
    rw [le_div_iff₀ hsq]
    have h2 : √P.Δx * |cv (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)) i ()| ≤
      √P.Δx * ‖cv (P.density (X ε * S ε * (V ε)ᵀ * P.Minv))‖ :=
      mul_le_mul_of_nonneg_left h1 hsq.le
    simp only [cv_apply] at h2
    linarith
  have hlim := tendsto_macro hP hρsup hJ hmacro h0
  refine prop7_core hP (c := c / √P.Δx) (B := √(B ^ 2 / P.Δx + N * Cg ^ 2)) (by positivity) hstep
    ?_ ?_ hnn h0 ?_
  · filter_upwards [hG, hB] with ε h1 h2
    exact hP.norm_le_of_bounds h1 h2
  · filter_upwards [hlow] with ε h
    rw [gridNorm_eq hΔx.le] at h
    rw [div_le_iff₀ hsq]
    linarith
  · have := hlim.div_const √P.Δx
    rw [zero_div] at this
    refine this.congr fun ε => ?_
    rw [gridNorm_eq hΔx.le]
    field_simp

/-- **Proposition 7 of arXiv 2607.27736, for SL-DLR(full)** (asymptotic preservation). One step of
the scheme with `Δt` and mesh fixed, in the source-free periodic setting with variable `σˢ > 0`,
`σᵃ ≥ 0`. The state `(X ε, S ε, V ε)` may depend on `ε`. Assume `ρⁿ ≥ 0`, `‖ρⁿ‖_Δx ≥ c > 0`, the
bound `C_g` of Lemma 4 on `fⱼⁿ - ρⁿ` and a bound `B` on `‖ρⁿ‖_Δx`, all uniform in `ε`. If `ρ0 ε` is
the limiting diffusion update `(I - Δt L_{1/(3σˢ)} + Δt diag(σᵃ)) ρ0 = ρⁿ`, then
`Y^{n+1} = ρ0 (M𝟏)ᵀ + o(1)` as `ε → 0`, in the Frobenius norm, which on a fixed mesh is equivalent
to `‖·‖_{F,Δx}`. See `prop7_full_fixed` for data independent of `ε`.

Differences from the paper: the uniform bounds on `ρⁿ` from above and below are implicit there. The
conditions (16) and (17) are derived; (17) uses the discrete maximum principle
(`diffusion_nonneg`), which the paper leaves implicit. The QR factors of `K` and `L` may be
singular, as they are in the limit, the bases need not converge, and the matrix
`(A_X^{n+1})⁻¹` of the paper's proof is not needed. -/
theorem prop7_full (hP : P.Admissible)
    {X : ℝ → Matrix (ZMod N) r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix κ r ℝ}
    {K : ℝ → Matrix (ZMod N) r ℝ} {L : ℝ → Matrix κ r ℝ} {X₁ : ℝ → Matrix (ZMod N) p ℝ}
    {V₁ : ℝ → Matrix κ q ℝ} {S₁ : ℝ → Matrix p q ℝ} {ρs ρ0 : ℝ → ZMod N → ℝ} {Cg B c : ℝ}
    (hc : 0 < c)
    (hstep : ∀ᶠ ε in 𝓝[>] 0, P.IsDLRFullStep ε (ρs ε) (X ε) (S ε) (V ε) (K ε) (L ε) (X₁ ε) (V₁ ε)
      (S₁ ε))
    (hG : ∀ᶠ ε in 𝓝[>] 0, ∀ i j, |(X ε * S ε * (V ε)ᵀ * P.Minv) i j -
      P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i| ≤ Cg)
    (hB : ∀ᶠ ε in 𝓝[>] 0, gridNorm P.Δx (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)) ≤ B)
    (hlow : ∀ᶠ ε in 𝓝[>] 0, c ≤ gridNorm P.Δx (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)))
    (hnn : ∀ᶠ ε in 𝓝[>] 0, ∀ i, 0 ≤ P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i)
    (h0 : ∀ᶠ ε in 𝓝[>] 0, ∀ i, P.macroOp P.betaLim (ρ0 ε) i =
      P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i) :
    Tendsto (fun ε => ‖X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec (ρ0 ε) P.m‖) (𝓝[>] 0) (𝓝 0) := by
  refine prop7_of_flux hP (J := fun ε => P.flux ε (X ε * S ε * (V ε)ᵀ * P.Minv))
    (CJ := 2 * Cg / P.Δx) hc (hstep.mono fun ε h => h.1) (hstep.mono fun ε h => h.2) ?_ hG hB hlow
    hnn h0
  filter_upwards [hG] with ε h i
  exact hP.abs_flux_le ε h i

/-- **Proposition 7 of arXiv 2607.27736, for SL-DLR** (asymptotic preservation with sampling): the
sampled scheme has the same limit, given in addition `‖w̃‖₁ ≤ C` uniformly in `ε` (the sampled
directions and weights may depend on `ε`). No exactness of the sampled rule is needed. The paper
derives this from Proposition 6; here the same uniform bound on the flux derivative is fed into the
same limit. Otherwise as in `prop7_full`. -/
theorem prop7_sampled (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ℝ → ι → κ}
    {wt : ℝ → ι → ℝ}
    {X : ℝ → Matrix (ZMod N) r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix κ r ℝ}
    {K : ℝ → Matrix (ZMod N) r ℝ} {L : ℝ → Matrix κ r ℝ} {X₁ : ℝ → Matrix (ZMod N) p ℝ}
    {V₁ : ℝ → Matrix κ q ℝ} {S₁ : ℝ → Matrix p q ℝ} {ρs ρ0 : ℝ → ZMod N → ℝ} {Cg B c C : ℝ}
    (hc : 0 < c)
    (hstep : ∀ᶠ ε in 𝓝[>] 0, P.IsDLRStep (idx ε) (wt ε) ε (ρs ε) (X ε) (S ε) (V ε) (K ε) (L ε)
      (X₁ ε) (V₁ ε) (S₁ ε))
    (hC : ∀ᶠ ε in 𝓝[>] 0, ∑ k, |wt ε k| ≤ C)
    (hG : ∀ᶠ ε in 𝓝[>] 0, ∀ i j, |(X ε * S ε * (V ε)ᵀ * P.Minv) i j -
      P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i| ≤ Cg)
    (hB : ∀ᶠ ε in 𝓝[>] 0, gridNorm P.Δx (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)) ≤ B)
    (hlow : ∀ᶠ ε in 𝓝[>] 0, c ≤ gridNorm P.Δx (P.density (X ε * S ε * (V ε)ᵀ * P.Minv)))
    (hnn : ∀ᶠ ε in 𝓝[>] 0, ∀ i, 0 ≤ P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i)
    (h0 : ∀ᶠ ε in 𝓝[>] 0, ∀ i, P.macroOp P.betaLim (ρ0 ε) i =
      P.density (X ε * S ε * (V ε)ᵀ * P.Minv) i) :
    Tendsto (fun ε => ‖X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec (ρ0 ε) P.m‖) (𝓝[>] 0) (𝓝 0) := by
  refine prop7_of_flux hP (J := fun ε => P.fluxS (idx ε) (wt ε) ε (X ε * S ε * (V ε)ᵀ * P.Minv))
    (CJ := C * (2 * Cg / P.Δx)) hc (hstep.mono fun ε h => h.1) (hstep.mono fun ε h => h.2) ?_ hG hB
    hlow hnn h0
  filter_upwards [hG, hC] with ε h h' i
  exact hP.abs_fluxS_le (idx ε) ε h h' i

/-- A finite matrix of data obeys the bound of Lemma 4 for some `C_g`. -/
theorem exists_bound (P : Disc N κ) (F : Matrix (ZMod N) κ ℝ) :
    ∃ Cg, ∀ i j, |F i j - P.density F i| ≤ Cg := by
  refine ⟨∑ i, ∑ j, |F i j - P.density F i|, fun i j => ?_⟩
  calc |F i j - P.density F i| ≤ ∑ j, |F i j - P.density F i| :=
        Finset.single_le_sum (f := fun j => |F i j - P.density F i|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, |F i j - P.density F i|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- **Proposition 7 for SL-DLR(full), data independent of `ε`**: this is the paper's statement. If
`ρⁿ ≥ 0` and `‖ρⁿ‖_Δx > 0`, then `Y^{n+1} = ρ₀^{n+1} (M𝟏)ᵀ + o(1)` as `ε → 0`. -/
theorem prop7_full_fixed (hP : P.Admissible) {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ}
    {V : Matrix κ r ℝ} {K : ℝ → Matrix (ZMod N) r ℝ} {L : ℝ → Matrix κ r ℝ}
    {X₁ : ℝ → Matrix (ZMod N) p ℝ} {V₁ : ℝ → Matrix κ q ℝ} {S₁ : ℝ → Matrix p q ℝ}
    {ρs : ℝ → ZMod N → ℝ} {ρ0 : ZMod N → ℝ}
    (hnn : ∀ i, 0 ≤ P.density (X * S * Vᵀ * P.Minv) i)
    (hpos : 0 < gridNorm P.Δx (P.density (X * S * Vᵀ * P.Minv)))
    (hstep : ∀ᶠ ε in 𝓝[>] 0, P.IsDLRFullStep ε (ρs ε) X S V (K ε) (L ε) (X₁ ε) (V₁ ε) (S₁ ε))
    (h0 : ∀ i, P.macroOp P.betaLim ρ0 i = P.density (X * S * Vᵀ * P.Minv) i) :
    Tendsto (fun ε => ‖X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec ρ0 P.m‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Cg, hCg⟩ := exists_bound P (X * S * Vᵀ * P.Minv)
  exact prop7_full hP (X := fun _ => X) (S := fun _ => S) (V := fun _ => V) (ρ0 := fun _ => ρ0)
    (c := gridNorm P.Δx (P.density (X * S * Vᵀ * P.Minv))) hpos hstep (.of_forall fun _ => hCg)
    (.of_forall fun _ => le_rfl) (.of_forall fun _ => le_rfl) (.of_forall fun _ => hnn)
    (.of_forall fun _ => h0)

/-- **Proposition 7 for SL-DLR, data independent of `ε`**: SL-DLR has the same limiting equation as
SL-DLR(full). -/
theorem prop7_sampled_fixed (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ℝ → ι → κ}
    {wt : ℝ → ι → ℝ} {C : ℝ} (hC : ∀ᶠ ε in 𝓝[>] 0, ∑ k, |wt ε k| ≤ C)
    {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ}
    {V : Matrix κ r ℝ} {K : ℝ → Matrix (ZMod N) r ℝ} {L : ℝ → Matrix κ r ℝ}
    {X₁ : ℝ → Matrix (ZMod N) p ℝ} {V₁ : ℝ → Matrix κ q ℝ} {S₁ : ℝ → Matrix p q ℝ}
    {ρs : ℝ → ZMod N → ℝ} {ρ0 : ZMod N → ℝ}
    (hnn : ∀ i, 0 ≤ P.density (X * S * Vᵀ * P.Minv) i)
    (hpos : 0 < gridNorm P.Δx (P.density (X * S * Vᵀ * P.Minv)))
    (hstep : ∀ᶠ ε in 𝓝[>] 0, P.IsDLRStep (idx ε) (wt ε) ε (ρs ε) X S V (K ε) (L ε) (X₁ ε) (V₁ ε)
      (S₁ ε))
    (h0 : ∀ i, P.macroOp P.betaLim ρ0 i = P.density (X * S * Vᵀ * P.Minv) i) :
    Tendsto (fun ε => ‖X₁ ε * S₁ ε * (V₁ ε)ᵀ - Matrix.vecMulVec ρ0 P.m‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Cg, hCg⟩ := exists_bound P (X * S * Vᵀ * P.Minv)
  exact prop7_sampled hP (X := fun _ => X) (S := fun _ => S) (V := fun _ => V) (ρ0 := fun _ => ρ0)
    (c := gridNorm P.Δx (P.density (X * S * Vᵀ * P.Minv))) hpos hstep hC (.of_forall fun _ => hCg)
    (.of_forall fun _ => le_rfl) (.of_forall fun _ => le_rfl) (.of_forall fun _ => hnn)
    (.of_forall fun _ => h0)

/-! ### Well-posedness of the scheme -/

/-- `D^{up}` is additive. -/
theorem dUp_add (Δx v : ℝ) (a b : ZMod N → ℝ) (i : ZMod N) :
    dUp Δx v (a + b) i = dUp Δx v a i + dUp Δx v b i := by
  by_cases hv : 0 ≤ v
  · simp only [dUp, hv, ↓reduceIte, dMinus, Pi.add_apply]
    ring
  · simp only [dUp, hv, ↓reduceIte, dPlus, Pi.add_apply]
    ring

/-- `D^{up}` is homogeneous. -/
theorem dUp_smul (Δx v c : ℝ) (a : ZMod N → ℝ) (i : ZMod N) :
    dUp Δx v (c • a) i = c * dUp Δx v a i := by
  by_cases hv : 0 ≤ v
  · simp only [dUp, hv, ↓reduceIte, dMinus, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [dUp, hv, ↓reduceIte, dPlus, Pi.smul_apply, smul_eq_mul]
    ring

variable (P) in
/-- The linear part of `𝓖`. -/
def gLin (ε : ℝ) : Matrix (ZMod N) κ ℝ →ₗ[ℝ] Matrix (ZMod N) κ ℝ where
  toFun Y := -(1 / ε) • P.transport Y - (1 / ε ^ 2) • (Matrix.diagonal P.σs * Y) -
    Matrix.diagonal P.σa * Y
  map_add' Y Z := by
    have h : P.transport (Y + Z) = P.transport Y + P.transport Z := by
      ext i j
      have := dUp_add P.Δx (P.v j) (fun l => Y l j) (fun l => Z l j) i
      simp only [transport, Matrix.of_apply, Matrix.add_apply]
      rw [← mul_add, ← this]
      rfl
    rw [h, Matrix.mul_add, Matrix.mul_add]
    simp only [smul_add]
    abel
  map_smul' c Y := by
    have h : P.transport (c • Y) = c • P.transport Y := by
      ext i j
      have := dUp_smul P.Δx (P.v j) c (fun l => Y l j) i
      simp only [transport, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_left_comm, ← this]
      rfl
    simp only [h, Matrix.mul_smul, RingHom.id_apply, smul_sub, smul_smul, mul_comm]

/-- `𝓖` splits into its linear part and the equilibrium forcing. -/
theorem gOp_eq (ε : ℝ) (ρ : ZMod N → ℝ) (Y : Matrix (ZMod N) κ ℝ) :
    P.gOp ε ρ Y = P.gLin ε Y +
      (1 / ε ^ 2) • (Matrix.diagonal P.σs * Matrix.vecMulVec ρ P.m) := by
  simp only [gOp, gLin, Matrix.mul_sub, smul_sub, LinearMap.coe_mk, AddHom.coe_mk]
  abel

/-- The linear part of `𝓖` is dissipative. -/
theorem inner_gLin_self_nonpos (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε)
    (Y : Matrix (ZMod N) κ ℝ) : ⟪P.gLin ε Y, Y⟫ ≤ 0 := by
  have h1 := inner_transport_self_nonneg hP Y
  have h2 : 0 ≤ ⟪Matrix.diagonal P.σs * Y, Y⟫ := by
    simpa using inner_diagonal_mul_self_ge (c₀ := 0) (fun i => (hP.σs_pos i).le) Y
  have h3 : 0 ≤ ⟪Matrix.diagonal P.σa * Y, Y⟫ := by
    simpa using inner_diagonal_mul_self_ge (c₀ := 0) hP.σa_nonneg Y
  simp only [gLin, LinearMap.coe_mk, AddHom.coe_mk, inner_sub_left, real_inner_smul_left]
  have h4 : 0 ≤ 1 / ε * ⟪P.transport Y, Y⟫ := by positivity
  have h5 : 0 ≤ 1 / ε ^ 2 * ⟪Matrix.diagonal P.σs * Y, Y⟫ := by positivity
  linarith

/-- Every implicit substep is uniquely solvable; here existence, for a Galerkin lift `ℓ` with
adjoint `ℓs`. -/
theorem exists_galerkin_solve {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) (ρ : ZMod N → ℝ)
    (ℓ : E →ₗ[ℝ] Matrix (ZMod N) κ ℝ) (ℓs : Matrix (ZMod N) κ ℝ →ₗ[ℝ] E)
    (hadj : ∀ x y, ⟪ℓs y, x⟫ = ⟪y, ℓ x⟫) (x₀ : E) :
    ∃ x, x - x₀ = P.Δt • ℓs (P.gOp ε ρ (ℓ x)) := by
  set f := (1 / ε ^ 2) • (Matrix.diagonal P.σs * Matrix.vecMulVec ρ P.m) with hf
  let G : E →ₗ[ℝ] E := LinearMap.id - P.Δt • (ℓs ∘ₗ P.gLin ε ∘ₗ ℓ)
  have hG : ∀ x, 1 * ‖x‖ ^ 2 ≤ ⟪G x, x⟫ := by
    intro x
    have h1 := inner_gLin_self_nonpos hP hε (ℓ x)
    have h2 : ⟪G x, x⟫ = ‖x‖ ^ 2 - P.Δt * ⟪P.gLin ε (ℓ x), ℓ x⟫ := by
      simp only [G, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, inner_sub_left, real_inner_smul_left, hadj,
        real_inner_self_eq_norm_sq]
    rw [h2]
    have := mul_nonneg hP.Δt_pos.le (neg_nonneg.2 h1)
    linarith
  obtain ⟨x, hx⟩ := (bijective_of_coercive G one_pos hG).1.2 (x₀ + P.Δt • ℓs f)
  refine ⟨x, ?_⟩
  have h1 : x - P.Δt • ℓs (P.gLin ε (ℓ x)) = x₀ + P.Δt • ℓs f := hx
  rw [gOp_eq, map_add, smul_add, ← hf]
  set T := P.Δt • ℓs (P.gLin ε (ℓ x)) with hT
  have h2 : x - x₀ = (x - T) + T - x₀ := by abel
  rw [h2, h1]
  abel

/-- The right multiplication `K ↦ K Vᵀ`, the `K`-step lift. -/
def liftK (V : Matrix κ r ℝ) : Matrix (ZMod N) r ℝ →ₗ[ℝ] Matrix (ZMod N) κ ℝ where
  toFun K := K * Vᵀ
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' _ _ := Matrix.smul_mul _ _ _

/-- The projection `Y ↦ Y V` of the `K`-step. -/
def projK (V : Matrix κ r ℝ) : Matrix (ZMod N) κ ℝ →ₗ[ℝ] Matrix (ZMod N) r ℝ where
  toFun Y := Y * V
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' _ _ := Matrix.smul_mul _ _ _

/-- The map `L ↦ X Lᵀ`, the `L`-step lift. -/
def liftL (X : Matrix (ZMod N) r ℝ) : Matrix κ r ℝ →ₗ[ℝ] Matrix (ZMod N) κ ℝ where
  toFun L := X * Lᵀ
  map_add' a b := by rw [Matrix.transpose_add, Matrix.mul_add]
  map_smul' c a := by rw [Matrix.transpose_smul, Matrix.mul_smul]; rfl

/-- The projection `Y ↦ Yᵀ X` of the `L`-step. -/
def projL (X : Matrix (ZMod N) r ℝ) : Matrix (ZMod N) κ ℝ →ₗ[ℝ] Matrix κ r ℝ where
  toFun Y := Yᵀ * X
  map_add' a b := by rw [Matrix.transpose_add, Matrix.add_mul]
  map_smul' c a := by rw [Matrix.transpose_smul, Matrix.smul_mul]; rfl

/-- The map `S ↦ X₁ S V₁ᵀ`, the `S`-step lift. -/
def liftS (X₁ : Matrix (ZMod N) p ℝ) (V₁ : Matrix κ q ℝ) :
    Matrix p q ℝ →ₗ[ℝ] Matrix (ZMod N) κ ℝ where
  toFun S := X₁ * S * V₁ᵀ
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- The projection `Y ↦ X₁ᵀ Y V₁` of the `S`-step. -/
def projS (X₁ : Matrix (ZMod N) p ℝ) (V₁ : Matrix κ q ℝ) :
    Matrix (ZMod N) κ ℝ →ₗ[ℝ] Matrix p q ℝ where
  toFun Y := X₁ᵀ * Y * V₁
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- **The BUG step is well defined** for all data, so that `IsBUGSubsteps` is never vacuous when the
rank `k` is at most `N` and the number of velocities. Rank-deficient `K`, `L` are allowed. -/
theorem exists_bugSubsteps (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hN : k ≤ N)
    (hκ : k ≤ Fintype.card κ) (ρs : ZMod N → ℝ) {X : Matrix (ZMod N) (Fin k) ℝ}
    (S : Matrix (Fin k) (Fin k) ℝ) {V : Matrix κ (Fin k) ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) :
    ∃ (K : Matrix (ZMod N) (Fin k) ℝ) (L : Matrix κ (Fin k) ℝ) (X₁ : Matrix (ZMod N) (Fin k) ℝ)
      (V₁ : Matrix κ (Fin k) ℝ) (S₁ : Matrix (Fin k) (Fin k) ℝ),
      P.IsBUGSubsteps ε ρs X S V K L X₁ V₁ S₁ := by
  obtain ⟨K, hK⟩ := exists_galerkin_solve hP hε ρs (liftK V) (projK V)
    (fun x y => Frobenius.inner_mul_right y V x) (X * S)
  obtain ⟨L, hL⟩ := exists_galerkin_solve hP hε ρs (liftL X) (projL X)
    (fun x y => by
      change ⟪yᵀ * X, x⟫ = ⟪y, X * xᵀ⟫
      rw [Frobenius.inner_mul_left', ← Frobenius.inner_transpose, Matrix.transpose_mul,
        Matrix.transpose_transpose])
    (V * Sᵀ)
  obtain ⟨X₁, hX₁, cX⟩ := MatrixBUG.exists_qr (by simpa [ZMod.card] using hN) K
  obtain ⟨V₁, hV₁, cV⟩ := MatrixBUG.exists_qr hκ L
  obtain ⟨S₁, hS⟩ := exists_galerkin_solve hP hε ρs (liftS X₁ V₁) (projS X₁ V₁)
    (fun x y => by
      change ⟪X₁ᵀ * y * V₁, x⟫ = ⟪y, X₁ * x * V₁ᵀ⟫
      rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, Matrix.transpose_transpose,
        Matrix.mul_assoc])
    (X₁ᵀ * X * S * Vᵀ * V₁)
  exact ⟨K, L, X₁, V₁, S₁, hX, hV, hK, hL, hX₁, hV₁, ⟨X₁ᵀ * K, by rw [← Matrix.mul_assoc, cX]⟩,
    ⟨V₁ᵀ * L, by rw [← Matrix.mul_assoc, cV]⟩, hS⟩

/-- The density solve is well defined, by Lemma 5. -/
theorem exists_macroSolve (hP : P.Admissible) (ε : ℝ) (ρ J : ZMod N → ℝ) :
    ∃ ρs, P.IsMacroSolve ε ρ J ρs := by
  obtain ⟨ρs, h⟩ := (lemma5 hP (hP.beta_nonneg ε)).1.2
    fun i => ρ i - P.Δt / ε * (P.alpha1 ε i * J i)
  exact ⟨ρs, fun i => congrFun h i⟩

/-- **One step of SL-DLR(full) is well defined** for all data. -/
theorem exists_dlrFullStep (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hN : k ≤ N)
    (hκ : k ≤ Fintype.card κ) {X : Matrix (ZMod N) (Fin k) ℝ}
    (S : Matrix (Fin k) (Fin k) ℝ) {V : Matrix κ (Fin k) ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) :
    ∃ (ρs : ZMod N → ℝ) (K : Matrix (ZMod N) (Fin k) ℝ) (L : Matrix κ (Fin k) ℝ)
      (X₁ : Matrix (ZMod N) (Fin k) ℝ) (V₁ : Matrix κ (Fin k) ℝ) (S₁ : Matrix (Fin k) (Fin k) ℝ),
      P.IsDLRFullStep ε ρs X S V K L X₁ V₁ S₁ := by
  obtain ⟨ρs, hρs⟩ := exists_macroSolve hP ε (P.density (X * S * Vᵀ * P.Minv))
    (P.flux ε (X * S * Vᵀ * P.Minv))
  obtain ⟨K, L, X₁, V₁, S₁, h⟩ := exists_bugSubsteps hP hε hN hκ ρs S hX hV
  exact ⟨ρs, K, L, X₁, V₁, S₁, hρs, h⟩

/-- **One step of SL-DLR is well defined** for all data. -/
theorem exists_dlrStep (hP : P.Admissible) {ι : Type*} [Fintype ι] (idx : ι → κ) (wt : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hN : k ≤ N)
    (hκ : k ≤ Fintype.card κ) {X : Matrix (ZMod N) (Fin k) ℝ}
    (S : Matrix (Fin k) (Fin k) ℝ) {V : Matrix κ (Fin k) ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) :
    ∃ (ρs : ZMod N → ℝ) (K : Matrix (ZMod N) (Fin k) ℝ) (L : Matrix κ (Fin k) ℝ)
      (X₁ : Matrix (ZMod N) (Fin k) ℝ) (V₁ : Matrix κ (Fin k) ℝ) (S₁ : Matrix (Fin k) (Fin k) ℝ),
      P.IsDLRStep idx wt ε ρs X S V K L X₁ V₁ S₁ := by
  obtain ⟨ρs, hρs⟩ := exists_macroSolve hP ε (P.density (X * S * Vᵀ * P.Minv))
    (P.fluxS idx wt ε (X * S * Vᵀ * P.Minv))
  obtain ⟨K, L, X₁, V₁, S₁, h⟩ := exists_bugSubsteps hP hε hN hκ ρs S hX hV
  exact ⟨ρs, K, L, X₁, V₁, S₁, hρs, h⟩

/-- **One step of the full-rank FD-SL scheme is well defined** for all data. -/
theorem exists_fullStep (hP : P.Admissible) {ε : ℝ} (hε : 0 < ε) (F : Matrix (ZMod N) κ ℝ) :
    ∃ (ρs : ZMod N → ℝ) (F₁ : Matrix (ZMod N) κ ℝ), P.IsFullStep ε F ρs F₁ := by
  obtain ⟨ρs, hρs⟩ := exists_macroSolve hP ε (P.density F) (P.flux ε F)
  obtain ⟨x, hx⟩ := exists_galerkin_solve hP hε ρs LinearMap.id LinearMap.id (fun _ _ => rfl)
    (F * P.M)
  refine ⟨ρs, x * P.Minv, hρs, fun i j => ?_⟩
  have hΔt := hP.Δt_pos.ne'
  have hm := (hP.m_pos j).ne'
  set F₁ := x * P.Minv with hF₁
  have hxe : ∀ l, x l j = F₁ l j * P.m j := fun l => by
    have := congrFun (congrFun (hP.mul_Minv_mul_M x) l) j
    rw [M, Matrix.mul_diagonal] at this
    exact this.symm
  have hd : dUp P.Δx (P.v j) (fun l => x l j) i =
      dUp P.Δx (P.v j) (fun l => F₁ l j) i * P.m j := by
    by_cases hv : 0 ≤ P.v j
    · simp only [dUp, hv, ↓reduceIte, dMinus, hxe]
      ring
    · simp only [dUp, hv, ↓reduceIte, dPlus, hxe]
      ring
  have h1 := congrFun (congrFun hx i) j
  simp only [gOp, transport, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, Matrix.diagonal_mul, Matrix.vecMulVec_apply, smul_eq_mul, hd,
    LinearMap.id_apply] at h1
  simp only [M, Matrix.mul_diagonal, hxe i] at h1
  have h2 : (F₁ i j - F i j) * P.m j = P.Δt * (P.σs i / ε ^ 2 * (ρs i - F₁ i j) -
      P.σa i * F₁ i j - P.v j / ε * dUp P.Δx (P.v j) (fun l => F₁ l j) i) * P.m j := by
    rw [sub_mul, h1]
    ring
  have h3 := mul_right_cancel₀ hm h2
  rw [h3]
  field_simp
  ring

/-- The hypotheses of Proposition 7 can hold: a rank-one state with positive density, together with
a step for each `ε > 0`. -/
theorem prop7_nonvacuous (hP : P.Admissible) :
    ∃ (X : Matrix (ZMod N) (Fin 1) ℝ) (S : Matrix (Fin 1) (Fin 1) ℝ) (V : Matrix κ (Fin 1) ℝ),
      (∀ i, 0 ≤ P.density (X * S * Vᵀ * P.Minv) i) ∧
      0 < gridNorm P.Δx (P.density (X * S * Vᵀ * P.Minv)) ∧
      ∀ ε, 0 < ε → ∃ (ρs : ZMod N → ℝ) (K : Matrix (ZMod N) (Fin 1) ℝ) (L : Matrix κ (Fin 1) ℝ)
        (X₁ : Matrix (ZMod N) (Fin 1) ℝ) (V₁ : Matrix κ (Fin 1) ℝ)
        (S₁ : Matrix (Fin 1) (Fin 1) ℝ), P.IsDLRFullStep ε ρs X S V K L X₁ V₁ S₁ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN0
  set c := (√(N : ℝ))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  let X : Matrix (ZMod N) (Fin 1) ℝ := Matrix.of fun _ _ => c
  let V : Matrix κ (Fin 1) ℝ := Matrix.of fun j _ => P.m j
  have hX : Xᵀ * X = 1 := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [Matrix.mul_apply, Matrix.transpose_apply, X, Matrix.of_apply, Matrix.one_apply_eq]
    have : c * c = (N : ℝ)⁻¹ := by
      rw [hc, ← mul_inv, Real.mul_self_sqrt hN0.le]
    simp [this, Finset.card_univ, ZMod.card, hN0.ne']
  have hV : Vᵀ * V = 1 := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [Matrix.mul_apply, Matrix.transpose_apply, V, Matrix.of_apply, Matrix.one_apply_eq]
    simpa [sq] using hP.sum_m_sq
  have hρ : ∀ i, P.density (X * (1 : Matrix (Fin 1) (Fin 1) ℝ) * Vᵀ * P.Minv) i = c := fun i => by
    have h1 := congrFun (congrFun (hP.cv_density (X * (1 : Matrix (Fin 1) (Fin 1) ℝ) * Vᵀ)) i) ()
    rw [cv_apply] at h1
    rw [h1]
    simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, X, V, Matrix.of_apply,
      cv_apply, Fin.sum_univ_one]
    calc ∑ j, c * P.m j * P.m j = c * ∑ j, P.m j ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = c := by rw [hP.sum_m_sq, mul_one]
  have hk : 1 ≤ N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hk' : 1 ≤ Fintype.card κ := by
    have := hP.nonempty
    exact Fintype.card_pos
  refine ⟨X, 1, V, fun i => by rw [hρ]; exact hc0.le, ?_, fun ε hε =>
    exists_dlrFullStep hP hε hk hk' 1 hX hV⟩
  have h2 : 0 < gridNorm P.Δx
      (P.density (X * (1 : Matrix (Fin 1) (Fin 1) ℝ) * Vᵀ * P.Minv)) ^ 2 := by
    rw [gridNorm_sq hP.Δx_pos.le]
    simp only [hρ]
    have h3 := hP.Δx_pos
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    positivity
  exact lt_of_le_of_ne (gridNorm_nonneg _ _) (fun h => by rw [← h] at h2; simp at h2)
/-! ### Estimates (11) and (14): the kinetic regime -/

/-- The mean value inequality on the segment from `0` to `t`. -/
theorem abs_sub_le_of_segment {ψ ψ' : ℝ → ℝ} (h : ∀ s, HasDerivAt ψ (ψ' s) s) {W t : ℝ}
    (hW : ∀ s ∈ Set.uIcc 0 t, |ψ' s| ≤ W) : |ψ t - ψ 0| ≤ W * |t| := by
  have h1 := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ψ) (f' := ψ') (C := W) (x := 0) (y := t)
    (fun s _ => (h s).hasDerivWithinAt) (fun s hs => by simpa using hW s hs)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa using h1

/-- The mean value inequality for a globally bounded derivative. -/
theorem abs_sub_le_of_deriv {φ φ' : ℝ → ℝ} (h : ∀ x, HasDerivAt φ (φ' x) x) {M : ℝ}
    (hM : ∀ x, |φ' x| ≤ M) (x t : ℝ) : |φ (x + t) - φ x| ≤ M * |t| := by
  have hd : ∀ s, HasDerivAt (fun s => φ (x + s)) (φ' (x + s)) s := fun s => by
    simpa using (h (x + s)).comp_const_add x s
  simpa using abs_sub_le_of_segment hd (W := M) (t := t) (fun s _ => hM _)

/-- First-order Taylor bound: `|φ(x + t) - φ(x) - t φ'(x)| ≤ M t²` if `|φ''| ≤ M`. The constant `1`
instead of `1/2` is enough here. -/
theorem taylor_first {φ φ' φ'' : ℝ → ℝ} (h1 : ∀ x, HasDerivAt φ (φ' x) x)
    (h2 : ∀ x, HasDerivAt φ' (φ'' x) x) {M : ℝ} (hM : ∀ x, |φ'' x| ≤ M) (x t : ℝ) :
    |φ (x + t) - φ x - t * φ' x| ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hd : ∀ s, HasDerivAt (fun s => φ (x + s) - s * φ' x) (φ' (x + s) - φ' x) s := fun s => by
    have e1 : HasDerivAt (fun s => φ (x + s)) (φ' (x + s)) s := by
      simpa using (h1 (x + s)).comp_const_add x s
    have e2 : HasDerivAt (fun s => s * φ' x) (φ' x) s := by
      simpa using (hasDerivAt_id s).mul_const (φ' x)
    exact e1.fun_sub e2
  have hb : ∀ s ∈ Set.uIcc 0 t, |φ' (x + s) - φ' x| ≤ M * |t| := fun s hs => by
    refine (abs_sub_le_of_deriv h2 hM x s).trans (mul_le_mul_of_nonneg_left ?_ hM0)
    simpa using Set.abs_sub_left_of_mem_uIcc hs
  have h3 := abs_sub_le_of_segment hd hb
  simp only [add_zero, zero_mul, sub_zero] at h3
  calc |φ (x + t) - φ x - t * φ' x| = |φ (x + t) - t * φ' x - φ x| := by ring_nf
    _ ≤ M * |t| * |t| := h3
    _ = M * t ^ 2 := by rw [mul_assoc, abs_mul_abs_self, sq]

/-- Second-order Taylor bound, with the sharp second coefficient. -/
theorem taylor_second {φ φ' φ'' φ''' : ℝ → ℝ} (h1 : ∀ x, HasDerivAt φ (φ' x) x)
    (h2 : ∀ x, HasDerivAt φ' (φ'' x) x) (h3 : ∀ x, HasDerivAt φ'' (φ''' x) x) {M : ℝ}
    (hM : ∀ x, |φ''' x| ≤ M) (x t : ℝ) :
    |φ (x + t) - φ x - t * φ' x - t ^ 2 / 2 * φ'' x| ≤ M * t ^ 2 * |t| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hd : ∀ s, HasDerivAt (fun s => φ (x + s) - s * φ' x - s ^ 2 / 2 * φ'' x)
      (φ' (x + s) - φ' x - s * φ'' x) s := fun s => by
    have e1 : HasDerivAt (fun s => φ (x + s)) (φ' (x + s)) s := by
      simpa using (h1 (x + s)).comp_const_add x s
    have e2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * φ'' x) (s * φ'' x) s := by
      have := ((hasDerivAt_pow 2 s).div_const 2).mul_const (φ'' x)
      simpa using this
    have e3 : HasDerivAt (fun s => s * φ' x) (φ' x) s := by
      simpa using (hasDerivAt_id s).mul_const (φ' x)
    exact (e1.fun_sub e3).fun_sub e2
  have hb : ∀ s ∈ Set.uIcc 0 t, |φ' (x + s) - φ' x - s * φ'' x| ≤ M * t ^ 2 := fun s hs => by
    refine (taylor_first h2 h3 hM x s).trans (mul_le_mul_of_nonneg_left ?_ hM0)
    have : |s| ≤ |t| := by simpa using Set.abs_sub_left_of_mem_uIcc hs
    rw [← sq_abs s, ← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h4 := abs_sub_le_of_segment hd hb
  simp only [add_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at h4
  calc |φ (x + t) - φ x - t * φ' x - t ^ 2 / 2 * φ'' x|
      = |φ (x + t) - t * φ' x - t ^ 2 / 2 * φ'' x - φ x| := by ring_nf
    _ ≤ M * t ^ 2 * |t| := h4

/-- The grid point `xᵢ = x₀ + i Δx`. -/
def gridPt (x₀ Δx : ℝ) (i : ZMod N) : ℝ := x₀ + i.val * Δx

/-- Sampling a periodic function: the index `i + k` lands at `xᵢ + k Δx`. -/
theorem sample_add {g : ℝ → ℝ} {x₀ Δx : ℝ} (hper : Function.Periodic g (N * Δx)) (i : ZMod N)
    (k : ℤ) : g (gridPt x₀ Δx (i + (k : ZMod N))) = g (gridPt x₀ Δx i + k * Δx) := by
  have hcast : (((i + (k : ZMod N)).val : ℤ) : ZMod N) = (((i.val : ℤ) + k : ℤ) : ZMod N) := by
    push_cast
    simp
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).1 hcast
  have h1 : ((i + (k : ZMod N)).val : ℝ) = (i.val : ℝ) + k - N * t := by
    have : (((i + (k : ZMod N)).val : ℤ) : ℝ) = ((i.val : ℤ) + k - N * t : ℤ) := by
      rw [← ht]
      ring_nf
    push_cast at this
    exact this
  have h2 := (hper.int_mul t).sub_eq (gridPt x₀ Δx i + k * Δx)
  rw [← h2]
  congr 1
  simp only [gridPt, h1]
  ring

/-- The upwind difference quotient of a sampled periodic function is first-order accurate. -/
theorem dUp_sample_sub_le {g g1 g2 : ℝ → ℝ} {x₀ Δx M : ℝ} (hΔx : 0 < Δx)
    (hper : Function.Periodic g (N * Δx)) (h1 : ∀ x, HasDerivAt g (g1 x) x)
    (h2 : ∀ x, HasDerivAt g1 (g2 x) x) (hM : ∀ x, |g2 x| ≤ M) (v : ℝ) (i : ZMod N) (k : ℤ) :
    |dUp Δx v (fun l => g (gridPt x₀ Δx l)) (i + (k : ZMod N)) -
      g1 (gridPt x₀ Δx i + k * Δx)| ≤ M * Δx := by
  set y := gridPt x₀ Δx i + k * Δx with hy
  have hy0 : g (gridPt x₀ Δx (i + (k : ZMod N))) = g y := sample_add hper i k
  have hne := hΔx.ne'
  by_cases hv : 0 ≤ v
  · simp only [dUp, hv, ↓reduceIte, dMinus]
    have e : i + (k : ZMod N) - 1 = i + ((k - 1 : ℤ) : ZMod N) := by
      push_cast
      ring
    have hy1 : g (gridPt x₀ Δx (i + (k : ZMod N) - 1)) = g (y + -Δx) := by
      rw [e, sample_add hper]
      congr 1
      rw [hy]
      push_cast
      ring
    rw [hy0, hy1]
    have h3 := taylor_first h1 h2 hM y (-Δx)
    have e2 : (g y - g (y + -Δx)) / Δx - g1 y = -(g (y + -Δx) - g y - -Δx * g1 y) / Δx := by
      field_simp
      ring
    rw [e2, abs_div, abs_neg, abs_of_pos hΔx, div_le_iff₀ hΔx]
    calc _ ≤ M * (-Δx) ^ 2 := h3
      _ = M * Δx * Δx := by ring
  · simp only [dUp, hv, ↓reduceIte, dPlus]
    have e : i + (k : ZMod N) + 1 = i + ((k + 1 : ℤ) : ZMod N) := by
      push_cast
      ring
    have hy1 : g (gridPt x₀ Δx (i + (k : ZMod N) + 1)) = g (y + Δx) := by
      rw [e, sample_add hper]
      congr 1
      rw [hy]
      push_cast
      ring
    rw [hy0, hy1]
    have h3 := taylor_first h1 h2 hM y Δx
    have e2 : (g (y + Δx) - g y) / Δx - g1 y = (g (y + Δx) - g y - Δx * g1 y) / Δx := by
      field_simp
    rw [e2, abs_div, abs_of_pos hΔx, div_le_iff₀ hΔx]
    calc _ ≤ M * Δx ^ 2 := h3
      _ = M * Δx * Δx := by ring

/-- `𝓑 D^{up}` applied to a sampled periodic function reconstructs the derivative at the foot point
`xᵢ - c Δx`, up to `2 M Δx`. -/
theorem backtrack_sample_sub_le {g g1 g2 : ℝ → ℝ} {x₀ Δx M : ℝ} (hΔx : 0 < Δx)
    (hper : Function.Periodic g (N * Δx)) (h1 : ∀ x, HasDerivAt g (g1 x) x)
    (h2 : ∀ x, HasDerivAt g1 (g2 x) x) (hM : ∀ x, |g2 x| ≤ M) (v c : ℝ) (i : ZMod N) :
    |backtrack c (dUp Δx v fun l => g (gridPt x₀ Δx l)) i -
      g1 (gridPt x₀ Δx i - c * Δx)| ≤ 2 * M * Δx := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set q := dUp Δx v fun l => g (gridPt x₀ Δx l) with hq
  set x := gridPt x₀ Δx i with hx
  set m := ⌊c⌋ with hm
  set l := Int.fract c with hl
  have hl0 : 0 ≤ l := Int.fract_nonneg c
  have hl1 : l ≤ 1 := (Int.fract_lt_one c).le
  have hc : c = m + l := (Int.floor_add_fract c).symm
  set foot := x - c * Δx with hfoot
  have i1 : i - ((m : ℤ) : ZMod N) = i + ((-m : ℤ) : ZMod N) := by
    push_cast
    ring
  have i2 : i - ((m + 1 : ℤ) : ZMod N) = i + ((-(m + 1) : ℤ) : ZMod N) := by
    push_cast
    ring
  have b1 := dUp_sample_sub_le (x₀ := x₀) hΔx hper h1 h2 hM v i (-m)
  have b2 := dUp_sample_sub_le (x₀ := x₀) hΔx hper h1 h2 hM v i (-(m + 1))
  rw [← hq, ← hx] at b1 b2
  have f1 := abs_sub_le_of_deriv h2 hM foot (l * Δx)
  have f2 := abs_sub_le_of_deriv h2 hM foot ((l - 1) * Δx)
  have e1 : foot + l * Δx = x + ((-m : ℤ) : ℝ) * Δx := by
    rw [hfoot, hc]
    push_cast
    ring
  have e2 : foot + (l - 1) * Δx = x + ((-(m + 1) : ℤ) : ℝ) * Δx := by
    rw [hfoot, hc]
    push_cast
    ring
  rw [e1] at f1
  rw [e2] at f2
  have f1' : |g1 (x + ((-m : ℤ) : ℝ) * Δx) - g1 foot| ≤ M * Δx := by
    refine f1.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    rw [abs_mul, abs_of_nonneg hl0, abs_of_pos hΔx]
    nlinarith
  have f2' : |g1 (x + ((-(m + 1) : ℤ) : ℝ) * Δx) - g1 foot| ≤ M * Δx := by
    refine f2.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    rw [abs_mul, abs_of_nonpos (by linarith), abs_of_pos hΔx]
    nlinarith
  set A := q (i + ((-m : ℤ) : ZMod N)) with hA
  set B := q (i + ((-(m + 1) : ℤ) : ZMod N)) with hB
  have hback : backtrack c q i = (1 - l) * A + l * B := by
    simp only [backtrack, shift, ← hm, ← hl, i1, i2, hA, hB]
  have s1 : |A - g1 foot| ≤ 2 * M * Δx := by
    have := abs_sub_le A (g1 (x + ((-m : ℤ) : ℝ) * Δx)) (g1 foot)
    linarith
  have s2 : |B - g1 foot| ≤ 2 * M * Δx := by
    have := abs_sub_le B (g1 (x + ((-(m + 1) : ℤ) : ℝ) * Δx)) (g1 foot)
    linarith
  have e3 : backtrack c q i - g1 foot = (1 - l) * (A - g1 foot) + l * (B - g1 foot) := by
    rw [hback]
    ring
  rw [e3]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hl1), abs_of_nonneg hl0]
  calc (1 - l) * |A - g1 foot| + l * |B - g1 foot|
      ≤ (1 - l) * (2 * M * Δx) + l * (2 * M * Δx) := by
        gcongr
    _ = 2 * M * Δx := by ring

/-! The smooth low-rank state of the formal expansion leading to (11). -/

variable (P) in
/-- The smooth profile `(f - ρ)(x, vⱼ) = ∑ₖ aₖ(x) Vⱼₖ / √wⱼ - ρ(x)` of a low-rank state, and its
derivatives when `a` and `ρf` are replaced by theirs. -/
def profile (V : Matrix κ r ℝ) (a : r → ℝ → ℝ) (ρf : ℝ → ℝ) (j : κ) (x : ℝ) : ℝ :=
  ∑ k, a k x * (V j k / P.m j) - ρf x

variable (P) in
/-- `Fⁿ = X S Vᵀ M⁻¹` samples, at the grid points `xᵢ = x₀ + i Δx`, a `(N Δx)`-periodic low-rank
function with `s` derivatives: `a 0 k` interpolates the column `k` of `X S`, `ρf 0` interpolates
`ρⁿ`, and `a n`, `ρf n` are the `n`-th derivatives. -/
structure IsSmoothState (s : ℕ) (x₀ : ℝ) (X : Matrix (ZMod N) r ℝ) (S : Matrix r r ℝ)
    (V : Matrix κ r ℝ) (a : ℕ → r → ℝ → ℝ) (ρf : ℕ → ℝ → ℝ) : Prop where
  da : ∀ n < s, ∀ k x, HasDerivAt (a n k) (a (n + 1) k x) x
  dρ : ∀ n < s, ∀ x, HasDerivAt (ρf n) (ρf (n + 1) x) x
  per : ∀ k, Function.Periodic (a 0 k) (N * P.Δx)
  perρ : Function.Periodic (ρf 0) (N * P.Δx)
  sampleA : ∀ i k, a 0 k (gridPt x₀ P.Δx i) = (X * S) i k
  sampleρ : ∀ i, ρf 0 (gridPt x₀ P.Δx i) = P.density (X * S * Vᵀ * P.Minv) i

variable (P) in
/-- `maxⱼ | |vⱼ|^{p+1} ∂ₓ^{p+1} (f - ρ)(xᵢ, vⱼ) |`. -/
def thetaPt (V : Matrix κ r ℝ) (a : ℕ → r → ℝ → ℝ) (ρf : ℕ → ℝ → ℝ) (x₀ : ℝ) (p : ℕ)
    (i : ZMod N) : ℝ :=
  ⨆ j, |P.v j| ^ (p + 1) * |P.profile V (a (p + 1)) (ρf (p + 1)) j (gridPt x₀ P.Δx i)|

variable (P) in
/-- The backtracking regularity measure `Θ_pⁿ` of Section 4.2.1. -/
def theta (V : Matrix κ r ℝ) (a : ℕ → r → ℝ → ℝ) (ρf : ℕ → ℝ → ℝ) (x₀ : ℝ) (p : ℕ) : ℝ :=
  gridNorm P.Δx (P.thetaPt V a ρf x₀ p)

variable (P) in
/-- The default target space `𝓩ₙ = span [𝟏, Q𝟏, Q M⁻¹ V]` of Section 3.3. -/
def target1 (V : Matrix κ r ℝ) : Submodule ℝ (κ → ℝ) :=
  Submodule.span ℝ (Set.range (fun (k : r) (j : κ) => P.v j * (V j k / P.m j)) ∪
    {fun _ => 1, P.v})

variable (P) in
/-- The enlarged target space `span [𝟏, Q𝟏, Q M⁻¹ V, Q²𝟏, Q² M⁻¹ V]` of Section 3.3. -/
def target2 (V : Matrix κ r ℝ) : Submodule ℝ (κ → ℝ) :=
  Submodule.span ℝ (Set.range (fun (k : r) (j : κ) => P.v j * (V j k / P.m j)) ∪
    Set.range (fun (k : r) (j : κ) => P.v j ^ 2 * (V j k / P.m j)) ∪
    {fun _ => 1, P.v, fun j => P.v j ^ 2})

namespace IsSmoothState

variable {s : ℕ} {x₀ : ℝ} {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ} {V : Matrix κ r ℝ}
  {a : ℕ → r → ℝ → ℝ} {ρf : ℕ → ℝ → ℝ}

/-- The derivatives of the profile. -/
theorem hasDeriv (hs : P.IsSmoothState s x₀ X S V a ρf) {n : ℕ} (hn : n < s) (j : κ) (x : ℝ) :
    HasDerivAt (P.profile V (a n) (ρf n) j) (P.profile V (a (n + 1)) (ρf (n + 1)) j x) x :=
  (HasDerivAt.fun_sum fun k _ => (hs.da n hn k x).mul_const (V j k / P.m j)).fun_sub
    (hs.dρ n hn x)

/-- The profile is periodic. -/
theorem periodic (hs : P.IsSmoothState s x₀ X S V a ρf) (j : κ) :
    Function.Periodic (P.profile V (a 0) (ρf 0) j) (N * P.Δx) := fun x => by
  simp only [profile, hs.perρ x]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hs.per k x]

/-- The profile samples `fⱼ - ρ` at the grid points. -/
theorem sample (hs : P.IsSmoothState s x₀ X S V a ρf) (i : ZMod N) (j : κ) :
    (X * S * Vᵀ * P.Minv) i j - P.density (X * S * Vᵀ * P.Minv) i =
      P.profile V (a 0) (ρf 0) j (gridPt x₀ P.Δx i) := by
  rw [profile, hs.sampleρ i]
  congr 1
  rw [Minv, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hs.sampleA i k, Matrix.transpose_apply]
  ring

/-- `|(bⱼ)ᵢ - ∂ₓ(f - ρ)(xᵢ - vⱼ Δt / ε, vⱼ)| ≤ 2 M₂ Δx`, the "first-order accuracy" of the FD-SL
reconstruction that the paper states without proof. -/
theorem abs_bvec_sub_le (hP : P.Admissible) (hs : P.IsSmoothState s x₀ X S V a ρf) (h2 : 2 ≤ s)
    {M₂ : ℝ} (hM₂ : ∀ j x, |P.profile V (a 2) (ρf 2) j x| ≤ M₂) {ε : ℝ} (hε : 0 < ε) (j : κ)
    (i : ZMod N) :
    |P.bvec ε (X * S * Vᵀ * P.Minv) j i -
      P.profile V (a 1) (ρf 1) j (gridPt x₀ P.Δx i - P.v j * P.Δt / ε)| ≤ 2 * M₂ * P.Δx := by
  have hΔx := hP.Δx_pos
  have e1 : (fun l => (X * S * Vᵀ * P.Minv) l j - P.density (X * S * Vᵀ * P.Minv) l) =
      fun l => P.profile V (a 0) (ρf 0) j (gridPt x₀ P.Δx l) := funext fun l => hs.sample l j
  have h := backtrack_sample_sub_le (x₀ := x₀) hΔx (hs.periodic j)
    (fun x => hs.hasDeriv (n := 0) (by omega) j x) (fun x => hs.hasDeriv (n := 1) (by omega) j x)
    (hM₂ j) (P.v j) (P.v j * P.Δt / (ε * P.Δx)) i
  have e2 : P.v j * P.Δt / (ε * P.Δx) * P.Δx = P.v j * P.Δt / ε := by
    field_simp
  rw [e2] at h
  simp only [bvec, e1]
  exact h

end IsSmoothState

/-- The hypotheses of `estimate11` can hold: any `(N Δx)`-periodic smooth coefficients `a`, with `V`
arbitrary, define a state `X = (a_k(xᵢ))ᵢₖ`, `S = 1` of this form, whose density is interpolated by
`∑ₖ aₖ ∑ⱼ Vⱼₖ √wⱼ`. -/
theorem isSmoothState_of_sample (hP : P.Admissible) {s : ℕ} {a : ℕ → r → ℝ → ℝ}
    (hda : ∀ n < s, ∀ k x, HasDerivAt (a n k) (a (n + 1) k x) x)
    (hper : ∀ k, Function.Periodic (a 0 k) (N * P.Δx)) (x₀ : ℝ) (V : Matrix κ r ℝ) :
    P.IsSmoothState s x₀ (Matrix.of fun i k => a 0 k (gridPt x₀ P.Δx i)) 1 V a
      (fun n x => ∑ k, a n k x * ∑ j, V j k * P.m j) where
  da := hda
  dρ n hn x := HasDerivAt.fun_sum fun k _ => (hda n hn k x).mul_const _
  per := hper
  perρ x := Finset.sum_congr rfl fun k _ => by rw [hper k x]
  sampleA i k := by simp
  sampleρ i := by
    have h1 := congrFun (congrFun (hP.cv_density
      ((Matrix.of fun i k => a 0 k (gridPt x₀ P.Δx i)) * (1 : Matrix r r ℝ) * Vᵀ)) i) ()
    rw [cv_apply] at h1
    rw [h1]
    simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, cv_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      ring)

/-- The triangle inequality for `‖t θ + c‖_Δx`, with a constant `c`. -/
theorem gridNorm_mul_add_const_le {Δx t c : ℝ} (hΔx : 0 ≤ Δx) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (θ : ZMod N → ℝ) :
    gridNorm Δx (fun i => t * θ i + c) ≤ t * gridNorm Δx θ + √(N * Δx) * c := by
  have h1 : cv (fun i => t * θ i + c) = t • cv θ + cv (fun _ : ZMod N => c) := by
    ext i u
    simp
  have h2 : gridNorm Δx (fun _ : ZMod N => c) ≤ √(N * Δx) * c :=
    gridNorm_le_of_abs_le hΔx hc fun _ => by rw [abs_of_nonneg hc]
  rw [gridNorm_eq hΔx] at h2 ⊢
  rw [gridNorm_eq hΔx, h1]
  have h3 : ‖t • cv θ + cv (fun _ : ZMod N => c)‖ ≤ t * ‖cv θ‖ + ‖cv (fun _ : ZMod N => c)‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg ht]
  have h4 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg Δx)
  nlinarith

/-- A term of the maximum is at most the maximum. -/
theorem le_thetaPt (P : Disc N κ) (V : Matrix κ r ℝ) (a : ℕ → r → ℝ → ℝ) (ρf : ℕ → ℝ → ℝ) (x₀ : ℝ)
    (p : ℕ) (i : ZMod N) (j : κ) :
    |P.v j| ^ (p + 1) * |P.profile V (a (p + 1)) (ρf (p + 1)) j (gridPt x₀ P.Δx i)| ≤
      P.thetaPt V a ρf x₀ p i :=
  le_ciSup (f := fun j =>
    |P.v j| ^ (p + 1) * |P.profile V (a (p + 1)) (ρf (p + 1)) j (gridPt x₀ P.Δx i)|)
    (Set.finite_range _).bddAbove j

/-- **Estimate (11) of arXiv 2607.27736**, made rigorous. The paper derives it by a leading-order
Taylor expansion with an unspecified constant, up to an `𝓞(Δx)` contribution. Here
`Fⁿ = X S Vᵀ M⁻¹` samples a smooth periodic low-rank function (`IsSmoothState`), the rule
`(idx, wt)` is exact on the default target space `𝓩₍₁₎ = span [𝟏, Q𝟏, Q M⁻¹ V]`, and `‖w̃‖₁ ≤ C`.
Then `‖𝓙̃ - 𝓙‖_Δx ≤ (1 + C) ((Δt / ε) Θ₁ + K (Δt² / ε² + Δx))`, with the explicit
`K = √(x_R - x_L) (2 M₂ + M₃)`, where `M₂`, `M₃` bound `∂ₓ²(f - ρ)`, `∂ₓ³(f - ρ)`. The membership
of the zeroth-order term in the target space is proved, not assumed. Three derivatives are used. -/
theorem estimate11 (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ι → κ} {wt : ι → ℝ} {ε : ℝ}
    (hε : 0 < ε) {x₀ : ℝ} {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ} {V : Matrix κ r ℝ}
    {a : ℕ → r → ℝ → ℝ} {ρf : ℕ → ℝ → ℝ} {M₂ M₃ C : ℝ} (hs : P.IsSmoothState 3 x₀ X S V a ρf)
    (hM₂ : ∀ j x, |P.profile V (a 2) (ρf 2) j x| ≤ M₂)
    (hM₃ : ∀ j x, |P.profile V (a 3) (ρf 3) j x| ≤ M₃)
    (hex : ∀ z ∈ P.target1 V, ∑ j, P.w j * z j = ∑ k, wt k * z (idx k)) (hC : ∑ k, |wt k| ≤ C) :
    gridNorm P.Δx (P.fluxS idx wt ε (X * S * Vᵀ * P.Minv) - P.flux ε (X * S * Vᵀ * P.Minv)) ≤
      (1 + C) * (P.Δt / ε * P.theta V a ρf x₀ 1 +
        √(N * P.Δx) * (2 * M₂ + M₃) * (P.Δt ^ 2 / ε ^ 2 + P.Δx)) := by
  have hΔx := hP.Δx_pos
  have hΔt := hP.Δt_pos
  have hM₂0 : 0 ≤ M₂ := by
    obtain ⟨j⟩ := hP.nonempty
    exact (abs_nonneg _).trans (hM₂ j 0)
  have hM₃0 : 0 ≤ M₃ := by
    obtain ⟨j⟩ := hP.nonempty
    exact (abs_nonneg _).trans (hM₃ j 0)
  have hC0 : 0 ≤ 1 + C := by
    have : 0 ≤ ∑ k, |wt k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  set t := P.Δt / ε with ht
  have ht0 : 0 ≤ t := by positivity
  set F := X * S * Vᵀ * P.Minv with hF
  set c₀ := 2 * M₂ * P.Δx + M₃ * t ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set ξ : ZMod N → κ → ℝ := fun i j =>
    P.v j * P.profile V (a 1) (ρf 1) j (gridPt x₀ P.Δx i) with hξ
  have hmem : ∀ i, ξ i ∈ P.target1 V := fun i => by
    have e : ξ i = ∑ k, a 1 k (gridPt x₀ P.Δx i) • (fun j => P.v j * (V j k / P.m j)) -
        ρf 1 (gridPt x₀ P.Δx i) • P.v := by
      funext j
      simp only [hξ, profile, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    rw [e]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span (Or.inl ⟨k, rfl⟩)
    · exact Submodule.subset_span (Or.inr (by simp))
  have hr : ∀ i, ‖P.hvec ε F i - ξ i‖ ≤ t * P.thetaPt V a ρf x₀ 1 i + c₀ := by
    intro i
    have hθ0 : 0 ≤ P.thetaPt V a ρf x₀ 1 i := by
      obtain ⟨j⟩ := hP.nonempty
      exact le_trans (by positivity) (le_thetaPt P V a ρf x₀ 1 i j)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    set x := gridPt x₀ P.Δx i with hx
    set v := P.v j with hv
    have hv1 : |v| ≤ 1 := hP.v_le j
    have hv2 : v ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) hv1
    set d := v * P.Δt / ε with hd
    have hdt : d = v * t := by
      rw [hd, ht]
      ring
    set g1 := P.profile V (a 1) (ρf 1) j with hg1
    set g2 := P.profile V (a 2) (ρf 2) j with hg2
    have h1 : |P.bvec ε F j i - g1 (x - d)| ≤ 2 * M₂ * P.Δx :=
      hs.abs_bvec_sub_le hP (by norm_num) hM₂ hε j i
    have h2 : |g1 (x + -d) - g1 x - -d * g2 x| ≤ M₃ * (-d) ^ 2 :=
      taylor_first (fun x => hs.hasDeriv (n := 1) (by norm_num) j x)
        (fun x => hs.hasDeriv (n := 2) (by norm_num) j x) (hM₃ j) x (-d)
    rw [← sub_eq_add_neg] at h2
    set e₁ := P.bvec ε F j i - g1 (x - d) with he₁
    set e₂ := g1 (x - d) - g1 x - -d * g2 x with he₂
    have hsplit : P.hvec ε F i j - ξ i j = v * e₁ + v * e₂ - t * (v ^ 2 * g2 x) := by
      simp only [hvec, hξ, he₁, he₂]
      rw [hdt]
      ring
    have b1 : |v * e₁| ≤ 2 * M₂ * P.Δx := by
      rw [abs_mul]
      calc |v| * |e₁| ≤ 1 * (2 * M₂ * P.Δx) := mul_le_mul hv1 h1 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have b2 : |v * e₂| ≤ M₃ * t ^ 2 := by
      rw [abs_mul]
      have h3 : M₃ * (-d) ^ 2 ≤ M₃ * t ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hM₃0
        rw [neg_sq, hdt, mul_pow]
        nlinarith [sq_nonneg t]
      calc |v| * |e₂| ≤ 1 * (M₃ * t ^ 2) :=
            mul_le_mul hv1 (h2.trans h3) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have b3 : |t * (v ^ 2 * g2 x)| ≤ t * P.thetaPt V a ρf x₀ 1 i := by
      rw [abs_mul, abs_of_nonneg ht0, abs_mul, abs_of_nonneg (sq_nonneg v), ← sq_abs v]
      exact mul_le_mul_of_nonneg_left (le_thetaPt P V a ρf x₀ 1 i j) ht0
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    have b4 := abs_add_le (v * e₁) (v * e₂)
    linarith
  have h3 := lemma3_of_candidates hP ε F hex hC hmem hr
  have h4 := gridNorm_mul_add_const_le (N := N) hΔx.le ht0 hc₀0 (P.thetaPt V a ρf x₀ 1)
  refine h3.trans (mul_le_mul_of_nonneg_left (h4.trans ?_) hC0)
  have h5 : c₀ ≤ (2 * M₂ + M₃) * (P.Δt ^ 2 / ε ^ 2 + P.Δx) := by
    have e : P.Δt ^ 2 / ε ^ 2 = t ^ 2 := by
      rw [ht, div_pow]
    rw [e, hc₀]
    nlinarith [mul_nonneg hM₂0 (sq_nonneg t), mul_nonneg hM₃0 hΔx.le]
  have h6 : 0 ≤ √(N * P.Δx) := Real.sqrt_nonneg _
  have h7 := mul_le_mul_of_nonneg_left h5 h6
  simp only [theta]
  linarith

/-- **Estimate (14) of arXiv 2607.27736**: the kinetic-regime density perturbation, from (13) and
(11). For `ε = 𝓞(1)` this is the paper's `𝓞(Δt² + Δt Δx)`. -/
theorem estimate14 (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ι → κ} {wt : ι → ℝ} {ε : ℝ}
    (hε : 0 < ε) {x₀ : ℝ} {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ} {V : Matrix κ r ℝ}
    {a : ℕ → r → ℝ → ℝ} {ρf : ℕ → ℝ → ℝ} {M₂ M₃ C : ℝ} (hs : P.IsSmoothState 3 x₀ X S V a ρf)
    (hM₂ : ∀ j x, |P.profile V (a 2) (ρf 2) j x| ≤ M₂)
    (hM₃ : ∀ j x, |P.profile V (a 3) (ρf 3) j x| ≤ M₃)
    (hex : ∀ z ∈ P.target1 V, ∑ j, P.w j * z j = ∑ k, wt k * z (idx k)) (hC : ∑ k, |wt k| ≤ C)
    {ρ₁ ρ₂ : ZMod N → ℝ}
    (h₁ : P.IsMacroSolve ε (P.density (X * S * Vᵀ * P.Minv))
      (P.fluxS idx wt ε (X * S * Vᵀ * P.Minv)) ρ₁)
    (h₂ : P.IsMacroSolve ε (P.density (X * S * Vᵀ * P.Minv))
      (P.flux ε (X * S * Vᵀ * P.Minv)) ρ₂) :
    gridNorm P.Δx (ρ₁ - ρ₂) ≤ P.Δt * ‖P.alpha1 ε‖ / ε *
      ((1 + C) * (P.Δt / ε * P.theta V a ρf x₀ 1 +
        √(N * P.Δx) * (2 * M₂ + M₃) * (P.Δt ^ 2 / ε ^ 2 + P.Δx))) :=
  (prop6 hP hε h₁ h₂).trans (mul_le_mul_of_nonneg_left (estimate11 hP hε hs hM₂ hM₃ hex hC)
    (div_nonneg (mul_nonneg hP.Δt_pos.le (norm_nonneg _)) hε.le))

/-- **The estimate after (11) in arXiv 2607.27736**, for the enlarged target space, made rigorous in
the same way as `estimate11`: if the rule is exact on `𝓩₍₂₎ = span [𝟏, Q𝟏, Q M⁻¹ V, Q²𝟏, Q² M⁻¹ V]`,
the first backtracking correction is captured and
`‖𝓙̃ - 𝓙‖_Δx ≤ (1 + C) ((Δt² / (2 ε²)) Θ₂ + K (Δt³ / ε³ + Δx))`, with the explicit
`K = √(x_R - x_L) (2 M₂ + M₄)`, where `M₂`, `M₄` bound `∂ₓ²(f - ρ)`, `∂ₓ⁴(f - ρ)`. -/
theorem estimate11_enlarged (hP : P.Admissible) {ι : Type*} [Fintype ι] {idx : ι → κ} {wt : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) {x₀ : ℝ} {X : Matrix (ZMod N) r ℝ} {S : Matrix r r ℝ} {V : Matrix κ r ℝ}
    {a : ℕ → r → ℝ → ℝ} {ρf : ℕ → ℝ → ℝ} {M₂ M₄ C : ℝ} (hs : P.IsSmoothState 4 x₀ X S V a ρf)
    (hM₂ : ∀ j x, |P.profile V (a 2) (ρf 2) j x| ≤ M₂)
    (hM₄ : ∀ j x, |P.profile V (a 4) (ρf 4) j x| ≤ M₄)
    (hex : ∀ z ∈ P.target2 V, ∑ j, P.w j * z j = ∑ k, wt k * z (idx k)) (hC : ∑ k, |wt k| ≤ C) :
    gridNorm P.Δx (P.fluxS idx wt ε (X * S * Vᵀ * P.Minv) - P.flux ε (X * S * Vᵀ * P.Minv)) ≤
      (1 + C) * (P.Δt ^ 2 / (2 * ε ^ 2) * P.theta V a ρf x₀ 2 +
        √(N * P.Δx) * (2 * M₂ + M₄) * (P.Δt ^ 3 / ε ^ 3 + P.Δx)) := by
  have hΔx := hP.Δx_pos
  have hΔt := hP.Δt_pos
  have hM₂0 : 0 ≤ M₂ := by
    obtain ⟨j⟩ := hP.nonempty
    exact (abs_nonneg _).trans (hM₂ j 0)
  have hM₄0 : 0 ≤ M₄ := by
    obtain ⟨j⟩ := hP.nonempty
    exact (abs_nonneg _).trans (hM₄ j 0)
  have hC0 : 0 ≤ 1 + C := by
    have : 0 ≤ ∑ k, |wt k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  set t := P.Δt / ε with ht
  have ht0 : 0 ≤ t := by positivity
  set F := X * S * Vᵀ * P.Minv with hF
  set c₀ := 2 * M₂ * P.Δx + M₄ * t ^ 3 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set ξ : ZMod N → κ → ℝ := fun i j => P.v j * P.profile V (a 1) (ρf 1) j (gridPt x₀ P.Δx i) -
    t * (P.v j ^ 2 * P.profile V (a 2) (ρf 2) j (gridPt x₀ P.Δx i)) with hξ
  have hmem : ∀ i, ξ i ∈ P.target2 V := fun i => by
    have e : ξ i = (∑ k, a 1 k (gridPt x₀ P.Δx i) • (fun j => P.v j * (V j k / P.m j)) -
        ρf 1 (gridPt x₀ P.Δx i) • P.v) -
        t • (∑ k, a 2 k (gridPt x₀ P.Δx i) • (fun j => P.v j ^ 2 * (V j k / P.m j)) -
          ρf 2 (gridPt x₀ P.Δx i) • fun j => P.v j ^ 2) := by
      funext j
      simp only [hξ, profile, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_sub, Finset.mul_sum]
      congr 2
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    rw [e]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)))
    · exact Submodule.subset_span (Or.inl (Or.inl ⟨k, rfl⟩))
    · exact Submodule.subset_span (Or.inr (by simp))
    · exact Submodule.subset_span (Or.inl (Or.inr ⟨k, rfl⟩))
    · exact Submodule.subset_span (Or.inr (by simp))
  have hr : ∀ i, ‖P.hvec ε F i - ξ i‖ ≤ t ^ 2 / 2 * P.thetaPt V a ρf x₀ 2 i + c₀ := by
    intro i
    have hθ0 : 0 ≤ P.thetaPt V a ρf x₀ 2 i := by
      obtain ⟨j⟩ := hP.nonempty
      exact le_trans (by positivity) (le_thetaPt P V a ρf x₀ 2 i j)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    set x := gridPt x₀ P.Δx i with hx
    set v := P.v j with hv
    have hv1 : |v| ≤ 1 := hP.v_le j
    set d := v * P.Δt / ε with hd
    have hdt : d = v * t := by
      rw [hd, ht]
      ring
    have hd1 : |d| ≤ t := by
      rw [hdt, abs_mul, abs_of_nonneg ht0]
      nlinarith [abs_nonneg v]
    set g1 := P.profile V (a 1) (ρf 1) j with hg1
    set g2 := P.profile V (a 2) (ρf 2) j with hg2
    set g3 := P.profile V (a 3) (ρf 3) j with hg3
    have h1 : |P.bvec ε F j i - g1 (x - d)| ≤ 2 * M₂ * P.Δx :=
      hs.abs_bvec_sub_le hP (by norm_num) hM₂ hε j i
    have h2 : |g1 (x + -d) - g1 x - -d * g2 x - (-d) ^ 2 / 2 * g3 x| ≤ M₄ * (-d) ^ 2 * |-d| :=
      taylor_second (fun x => hs.hasDeriv (n := 1) (by norm_num) j x)
        (fun x => hs.hasDeriv (n := 2) (by norm_num) j x)
        (fun x => hs.hasDeriv (n := 3) (by norm_num) j x) (hM₄ j) x (-d)
    rw [← sub_eq_add_neg, abs_neg, neg_sq] at h2
    set e₁ := P.bvec ε F j i - g1 (x - d) with he₁
    set e₂ := g1 (x - d) - g1 x - -d * g2 x - d ^ 2 / 2 * g3 x with he₂
    have hsplit : P.hvec ε F i j - ξ i j = v * e₁ + v * e₂ + t ^ 2 / 2 * (v ^ 3 * g3 x) := by
      simp only [hvec, hξ, he₁, he₂]
      rw [hdt]
      ring
    have b1 : |v * e₁| ≤ 2 * M₂ * P.Δx := by
      rw [abs_mul]
      calc |v| * |e₁| ≤ 1 * (2 * M₂ * P.Δx) := mul_le_mul hv1 h1 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have b2 : |v * e₂| ≤ M₄ * t ^ 3 := by
      rw [abs_mul]
      have h3 : M₄ * d ^ 2 * |d| ≤ M₄ * t ^ 3 := by
        have h4 : d ^ 2 ≤ t ^ 2 := by
          rw [← sq_abs d]
          exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
        calc M₄ * d ^ 2 * |d| ≤ M₄ * t ^ 2 * t := by gcongr
          _ = M₄ * t ^ 3 := by ring
      calc |v| * |e₂| ≤ 1 * (M₄ * t ^ 3) :=
            mul_le_mul hv1 (h2.trans h3) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have b3 : |t ^ 2 / 2 * (v ^ 3 * g3 x)| ≤ t ^ 2 / 2 * P.thetaPt V a ρf x₀ 2 i := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ 2 / 2), abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (le_thetaPt P V a ρf x₀ 2 i j) (by positivity)
    rw [hsplit]
    have b4 := abs_add_le (v * e₁ + v * e₂) (t ^ 2 / 2 * (v ^ 3 * g3 x))
    have b5 := abs_add_le (v * e₁) (v * e₂)
    linarith
  have h3 := lemma3_of_candidates hP ε F hex hC hmem hr
  have h4 := gridNorm_mul_add_const_le (N := N) hΔx.le (by positivity : 0 ≤ t ^ 2 / 2) hc₀0
    (P.thetaPt V a ρf x₀ 2)
  refine h3.trans (mul_le_mul_of_nonneg_left (h4.trans ?_) hC0)
  have h5 : c₀ ≤ (2 * M₂ + M₄) * (P.Δt ^ 3 / ε ^ 3 + P.Δx) := by
    have e : P.Δt ^ 3 / ε ^ 3 = t ^ 3 := by
      rw [ht, div_pow]
    rw [e, hc₀]
    have e3 : 0 ≤ t ^ 3 := by positivity
    nlinarith [mul_nonneg hM₂0 e3, mul_nonneg hM₄0 hΔx.le]
  have h6 : 0 ≤ √(N * P.Δx) := Real.sqrt_nonneg _
  have h7 := mul_le_mul_of_nonneg_left h5 h6
  have e : P.Δt ^ 2 / (2 * ε ^ 2) = t ^ 2 / 2 := by
    rw [ht, div_pow]
    field_simp
  rw [e]
  simp only [theta]
  linarith

/-- The new density of a step inherits the limit of the state: `‖ρ^{n+1} - ρ0‖₂` is bounded by
`‖Y^{n+1} - ρ0 (M𝟏)ᵀ‖`, so that `prop7_full` and `prop7_sampled` give `ρ^{n+1} = ρ0 + o(1)`. -/
theorem norm_density_sub_le (hP : P.Admissible) (Y : Matrix (ZMod N) κ ℝ) (ρ0 : ZMod N → ℝ) :
    ‖cv (P.density (Y * P.Minv) - ρ0)‖ ≤ ‖Y - Matrix.vecMulVec ρ0 P.m‖ := by
  have h1 : (cv P.m)ᵀ * cv P.m = 1 := by
    ext a b
    have ha : a = () := rfl
    have hb : b = () := rfl
    subst ha hb
    simpa [Matrix.mul_apply, sq] using hP.sum_m_sq
  have h2 : cv (P.density (Y * P.Minv) - ρ0) = (Y - Matrix.vecMulVec ρ0 P.m) * cv P.m := by
    rw [cv_sub, hP.cv_density, vecMulVec_eq_cv, Matrix.sub_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  rw [h2]
  have h3 := Frobenius.norm_mul_le (Y - Matrix.vecMulVec ρ0 P.m) (cv P.m)
  rwa [hP.norm_cv_m, mul_one] at h3

end Disc

end

end LeanDLRA.Literature.P2607_27736
