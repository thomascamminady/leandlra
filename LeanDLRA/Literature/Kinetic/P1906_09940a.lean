import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Stability.Energy
import LeanDLRA.Foundations.Localization
import LeanDLRA.OpenProblems.Stiff.Part1Defs

/-!
# Results of arXiv 1906.09940: low-rank KSL for slab-geometry transport

Peng, McClarren and Frank, *A low-rank method for time-dependent transport calculations*, apply
the projector-splitting integrator to the linear Boltzmann equation in slab geometry, with finite
volumes in `z` and normalised Legendre polynomials in `μ`.  The paper states no theorems; this
module proves the claims of its Section 2 for the concrete bases and the concrete discrete
operator, not just for an abstract field.  It builds the Legendre polynomials from Bonnet's
recursion, derives their orthogonality, norm and differential equation, and computes
`C = ⟨μ P_i P_k⟩_μ` from the integrals as the tridiagonal recursion matrix; it proves the
discrete realisation
(2.11)-(2.14), the projectors (2.2)-(2.3), the memory count (2.13), the upwind flux identity
(2.15)-(2.16), the factor equations (2.8)-(2.10) with their lift to (2.4)-(2.6), and the particle
count and rescaling of Sec. 2.2, together with the non-conservation that motivates it.  It also
settles what the paper leaves open about stability: the full scheme is `L²`-stable under a CFL
condition, this transfers to BUG, and it does not transfer to the paper's explicit Euler KSL step.

## Main results

* Legendre theory, from the recursion alone: `legendre_ode`, `polyInt_legendre_mul`,
  `polyInt_legendre_sq`, `integral_nLeg_mul`.
* Sec. 2.1: `muMatrix_apply` (tridiagonal `C`, closed form), `muMatrix_eq_legendreJacobi`,
  `one_add_smul_muMatrix_posSemidef` (`-1 ≤ C ≤ 1`), `integral_angularBasis_mul`,
  `integral_mu_angularBasis` (2.14), `integral_spatialBasis_mul`, `integral_pwConst_spatialBasis`,
  `expansion_factored` (2.1), `angular_projector`, `spatial_projector` (2.2)-(2.3),
  `lowRankMemory_eq_card`, `lowRankMemory_lt_iff`, `lowRankMemory_le_fraction` (2.13).
* Eqs. (2.15)-(2.16): `integral_cellFn_deriv`, `faceFlux_sub`, `faceFlux_upwind`,
  `faceFlux_galerkin`, `ghostShift_stencil`, `laxFriedrichs_reduced`,
  `isStabilisation_absSymm_muMatrix`, `isStabilisation_laxFriedrichs`.
* Eqs. (2.4)-(2.10): `galerkin_collisionOp`, `integral_mu_sum_nLeg`, `mul_muMatrix_apply`,
  `TransportProblem.kField_eq`, `.sField_eq`, `.lField_eq`, `.full_P_N`, `.isStep_lift`,
  `.exists_isStep`.
* Sec. 2.2: `integral_expansion`, `particles_rescale`, `rescale_factored`, `rank_rescale`,
  `rescale_comm_proj`, `norm_rescale_sub_le`, `ksl_euler_particles`, `ksl_euler_not_conservative`.
* Stability, beyond the paper: `TransportProblem.inner_op_nonpos`, `.norm_euler_op_le`,
  `.bug_euler_op_norm_le`, `.bug_op_norm_le`, and the negative results `ksl_euler_unstable`,
  `ksl_euler_unstable_upwind`, `ksl_euler_unstable_laxFriedrichs`, `ksl_amplification_gt_one`.
* Robust error bound for the unbounded field: `TransportProblem.ksl_global_error`, through
  `kslStep_tubeExt` and `ksl_global_error_le_of_tube`.  The library's `ksl_global_error_le` needs
  a bounded field and does not apply to `R` directly.

## Differences from the paper

* The PDE (1.1) in `z` is not formalised: streaming is the semi-discrete `streamOp`, and only its
  first step, testing a derivative with `Z_k`, is derived (`integral_cellFn_deriv`).  The angular
  part and the collision terms are derived from the integrals (`integral_mu_sum_nLeg`,
  `galerkin_collisionOp`).  (2.4)-(2.10) are therefore statements on coefficient matrices.
* We take `c = 1`, as (2.4)-(2.6) do.  (1.1) has the source `S`, while (2.4)-(2.6) and (2.8) have
  `S / 2`; we follow the latter.
* After (2.12) the paper prints `P_j(μ) = √((2n - 1) / 2) P̄_{n-1}(μ)`, with the number of modes `n`
  where the index `j` is meant; `nLeg l = √((2 l + 1) / 2) P̄_l` is the intended `P_{l+1}`.
* (2.8) has the misprint `g^r` in its sum over `j'`.  (2.9) prints `σt S_ij` and
  `⟨X_i⟩_z ⟨W_j⟩_μ / 2`, which is the case of constant `σt` and `S = 1`, and (2.10) drops the index
  `k` in its `σ` terms; `sField_eq`, `lField_eq` give the general forms.
* The prefactor `1 / √Δz` of (2.15)-(2.16) is correct for interface values of `K` tested with
  `Z_k` (`integral_cellFn_deriv`).  On cell coefficients, as used in `streamOp`, the factor is `1
  / Δz` (`interface_scaling`).
* "A diagonal matrix with the singular values of `C`" is read in the eigenbasis of `C`, i.e. as `Σ
  = |C|` (`absSymm`, `transpose_mul_absSymm_mul`).  Any other `Σ ≥ 0` is still covered by
  `inner_streamOp_nonpos`, but `IsStabilisation` asks for `Σ ≥ ±C`.
* The paper names no boundary treatment.  `TransportProblem.T` is any `IsShift`: zero ghost cells
  (`ghostShift`) or a periodic mesh (`cyclicShift`).  Conservation needs `IsConservativeShift`.
* Sec. 2.2 only says "globally scaling"; the formula `rescale` and a free target `N₀` are ours.
* Indices count from `0`, and the cells are half-open, a null-set difference.
* The instability theorems need `h a = Δz`, resp. CFL number above `(1 + √5) / 4`, and concern the
  explicit Euler substeps of Sec. 2.1 with pure streaming on a periodic mesh of even size.  For
  small CFL numbers nothing is claimed; with exact substeps the same mode is stable.
* `ksl_global_error` is for exact substeps, and its normal-component bound `ε` is a hypothesis, on
  the K-step results only.

## Not formalised

The Lanczos filter (no formula is given in the paper), the operation counts `O(n² r)`, `O(n r²)`,
and the numerical experiments of Sec. 3.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1906_09940

/- Real matrices with `Fin`-indexed rows and columns. -/
local notation "𝐌[" a ", " b "]" => Matrix (Fin a) (Fin b) ℝ

/-! ### Legendre polynomials -/

section Legendre

open Polynomial

/-- The Legendre polynomials `P̄ₙ`, defined by Bonnet's three-term recursion
`(n + 2) P̄ₙ₊₂ = (2 n + 3) X P̄ₙ₊₁ - (n + 1) P̄ₙ`, `P̄₀ = 1`, `P̄₁ = X`. -/
noncomputable def legendre : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => C ((2 * (n : ℝ) + 3) / (n + 2)) * X * legendre (n + 1)
      - C (((n : ℝ) + 1) / (n + 2)) * legendre n

/-- `P̄₀ = 1`. -/
@[simp] lemma legendre_zero : legendre 0 = 1 := by rw [legendre]
/-- `P̄₁ = X`. -/
@[simp] lemma legendre_one : legendre 1 = X := by rw [legendre]

/-- arXiv 1906.09940, Sec. 2.1 (the Legendre polynomials): Bonnet's recursion. -/
theorem legendre_recursion (n : ℕ) :
    ((n : ℝ[X]) + 2) * legendre (n + 2) =
      (2 * (n : ℝ[X]) + 3) * X * legendre (n + 1) - ((n : ℝ[X]) + 1) * legendre n := by
  have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h0 : ((n : ℝ[X]) + 2) = C ((n : ℝ) + 2) := by
    simp only [map_add, map_natCast, map_ofNat]
  have h1 : ((n : ℝ[X]) + 2) * C ((2 * (n : ℝ) + 3) / (n + 2)) = 2 * (n : ℝ[X]) + 3 := by
    rw [h0, ← C_mul, mul_div_cancel₀ _ hn]
    simp only [map_add, map_mul, map_natCast, map_ofNat]
  have h2 : ((n : ℝ[X]) + 2) * C (((n : ℝ) + 1) / (n + 2)) = (n : ℝ[X]) + 1 := by
    rw [h0, ← C_mul, mul_div_cancel₀ _ hn]
    simp only [map_add, map_natCast, map_one]
  rw [legendre]
  linear_combination (X * legendre (n + 1)) * h1 - legendre n * h2

/-- arXiv 1906.09940, Sec. 2.1 (the Legendre polynomials): `P̄ₙ(1) = 1`: the standard normalisation.
-/
theorem legendre_eval_one (n : ℕ) : (legendre n).eval 1 = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    have h := congrArg (eval (1 : ℝ)) (legendre_recursion n)
    simp only [eval_mul, eval_add, eval_sub, eval_natCast, eval_ofNat, eval_X, eval_one, h0,
      h1] at h
    have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    rw [h]; ring

private lemma legendre_H (n : ℕ) :
    (X ^ 2 - 1) * derivative (legendre n) =
      ((n : ℝ[X]) + 1) * (legendre (n + 1) - X * legendre n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have h : (2 : ℝ[X]) * legendre 2 = 3 * X * X - 1 := by
      have := legendre_recursion 0
      simpa using this
    change (X ^ 2 - 1) * derivative (legendre 1) =
      (((1 : ℕ) : ℝ[X]) + 1) * (legendre 2 - X * legendre 1)
    simp only [legendre_one, derivative_X, Nat.cast_one]
    linear_combination (-1 : ℝ[X]) * h
  | more n ih0 ih1 =>
    have hne : ((n : ℝ[X]) + 2) ≠ 0 := by
      have : ((n : ℝ[X]) + 2) = C ((n : ℝ) + 2) := by
        simp only [map_add, map_natCast, map_ofNat]
      rw [this, Ne, C_eq_zero]; positivity
    have R0 := legendre_recursion n
    have R1 := legendre_recursion (n + 1)
    have dR := congrArg derivative R0
    simp only [derivative_mul, derivative_add, derivative_sub, derivative_natCast,
      derivative_ofNat, derivative_X, derivative_one] at dR
    push_cast at ih1 R1 ⊢
    apply mul_left_cancel₀ hne
    linear_combination (X ^ 2 - 1) * dR + (2 * (n : ℝ[X]) + 3) * X * ih1
      - ((n : ℝ[X]) + 1) * ih0 - ((n : ℝ[X]) + 2) * R1 + ((n : ℝ[X]) + 1) * X * R0

private lemma legendre_T (n : ℕ) :
    (X ^ 2 - 1) * derivative (legendre (n + 1)) =
      ((n : ℝ[X]) + 1) * (X * legendre (n + 1) - legendre n) := by
  have h := legendre_H (n + 1)
  have R := legendre_recursion n
  push_cast at h
  linear_combination h + R

private lemma X_sq_sub_one_ne_zero : (X ^ 2 - 1 : ℝ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval (2 : ℝ)) h
  norm_num at this

private lemma legendre_b (n : ℕ) :
    X * derivative (legendre (n + 1)) - derivative (legendre n) =
      ((n : ℝ[X]) + 1) * legendre (n + 1) := by
  apply mul_left_cancel₀ X_sq_sub_one_ne_zero
  have h1 := legendre_T n
  have h0 := legendre_H n
  linear_combination X * h1 - h0

/-- arXiv 1906.09940, Sec. 2.1 (the Legendre polynomials): **Legendre's differential equation**
`((X² - 1) P̄ₙ')' = n (n + 1) P̄ₙ`, derived from Bonnet's recursion. -/
theorem legendre_ode (n : ℕ) :
    derivative ((X ^ 2 - 1) * derivative (legendre n)) =
      C ((n : ℝ) * (n + 1)) * legendre n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [legendre_T n]
    have hb := legendre_b n
    simp only [derivative_mul, derivative_sub, derivative_natCast, derivative_one,
      derivative_X, map_mul, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
    linear_combination ((n : ℝ[X]) + 1) * hb

/-- The integral `∫₋₁¹ q` of a polynomial. -/
noncomputable def polyInt (q : ℝ[X]) : ℝ := ∫ x in (-1 : ℝ)..1, q.eval x

private lemma poly_intervalIntegrable (q : ℝ[X]) (a b : ℝ) :
    IntervalIntegrable (fun x => q.eval x) MeasureTheory.volume a b :=
  q.continuous.intervalIntegrable _ _

private lemma polyInt_add (p q : ℝ[X]) : polyInt (p + q) = polyInt p + polyInt q := by
  simp only [polyInt, eval_add]
  exact intervalIntegral.integral_add (poly_intervalIntegrable _ _ _)
    (poly_intervalIntegrable _ _ _)

private lemma polyInt_sub (p q : ℝ[X]) : polyInt (p - q) = polyInt p - polyInt q := by
  simp only [polyInt, eval_sub]
  exact intervalIntegral.integral_sub (poly_intervalIntegrable _ _ _)
    (poly_intervalIntegrable _ _ _)

private lemma polyInt_C_mul (a : ℝ) (q : ℝ[X]) : polyInt (C a * q) = a * polyInt q := by
  simp only [polyInt, eval_mul, eval_C]
  exact intervalIntegral.integral_const_mul _ _

private lemma polyInt_derivative (q : ℝ[X]) :
    polyInt (derivative q) = q.eval 1 - q.eval (-1) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => q.hasDerivAt x)
    (poly_intervalIntegrable _ _ _)

private lemma polyInt_sl (a b : ℝ[X]) :
    polyInt (a * derivative ((X ^ 2 - 1) * derivative b)) =
      - polyInt ((X ^ 2 - 1) * derivative a * derivative b) := by
  have h := polyInt_derivative (a * ((X ^ 2 - 1) * derivative b))
  have e : derivative (a * ((X ^ 2 - 1) * derivative b)) =
      (X ^ 2 - 1) * derivative a * derivative b + a * derivative ((X ^ 2 - 1) * derivative b) := by
    exact (derivative_mul (f := a) (g := (X ^ 2 - 1) * derivative b)).trans (by ring)
  have e1 : (a * ((X ^ 2 - 1) * derivative b)).eval 1 = 0 := by simp
  have e2 : (a * ((X ^ 2 - 1) * derivative b)).eval (-1) = 0 := by simp
  rw [e, polyInt_add, e1, e2] at h
  linarith

/-- arXiv 1906.09940, Sec. 2.1 (the Legendre polynomials): **Orthogonality of the Legendre
polynomials**, `∫₋₁¹ P̄ₘ P̄ₙ = 0` for `m ≠ n`. -/
theorem polyInt_legendre_mul {m n : ℕ} (hmn : m ≠ n) :
    polyInt (legendre m * legendre n) = 0 := by
  have h1 := polyInt_sl (legendre m) (legendre n)
  have h2 := polyInt_sl (legendre n) (legendre m)
  rw [legendre_ode, show legendre m * (C ((n : ℝ) * (n + 1)) * legendre n) =
    C ((n : ℝ) * (n + 1)) * (legendre m * legendre n) by ring, polyInt_C_mul] at h1
  rw [legendre_ode, show legendre n * (C ((m : ℝ) * (m + 1)) * legendre m) =
    C ((m : ℝ) * (m + 1)) * (legendre m * legendre n) by ring, polyInt_C_mul,
    show (X ^ 2 - 1) * derivative (legendre n) * derivative (legendre m) =
      (X ^ 2 - 1) * derivative (legendre m) * derivative (legendre n) by ring] at h2
  have hne : (n : ℝ) * (n + 1) - m * (m + 1) ≠ 0 := by
    intro h
    have h' : (n : ℝ) * (n + 1) = m * (m + 1) := by linarith
    have h'' : n * (n + 1) = m * (m + 1) := by exact_mod_cast h'
    apply hmn
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt <;> nlinarith
  have : ((n : ℝ) * (n + 1) - m * (m + 1)) * polyInt (legendre m * legendre n) = 0 := by
    linear_combination h1 - h2
  exact (mul_eq_zero.mp this).resolve_left hne

private lemma recursion_C (n : ℕ) :
    C ((n : ℝ) + 2) * legendre (n + 2) =
      C (2 * (n : ℝ) + 3) * (X * legendre (n + 1)) - C ((n : ℝ) + 1) * legendre n := by
  have h := legendre_recursion n
  simp only [map_add, map_mul, map_natCast, map_ofNat, map_one]
  linear_combination h

private lemma moment_down (n : ℕ) :
    (2 * (n : ℝ) + 3) * polyInt (X * legendre (n + 1) * legendre n) =
      ((n : ℝ) + 1) * polyInt (legendre n * legendre n) := by
  have h := congrArg (fun q => polyInt (legendre n * q)) (recursion_C n)
  rw [show legendre n * (C ((n : ℝ) + 2) * legendre (n + 2)) =
      C ((n : ℝ) + 2) * (legendre n * legendre (n + 2)) by ring,
    show legendre n * (C (2 * (n : ℝ) + 3) * (X * legendre (n + 1)) -
        C ((n : ℝ) + 1) * legendre n) =
      C (2 * (n : ℝ) + 3) * (X * legendre (n + 1) * legendre n) -
        C ((n : ℝ) + 1) * (legendre n * legendre n) by ring,
    polyInt_sub, polyInt_C_mul, polyInt_C_mul, polyInt_C_mul,
    polyInt_legendre_mul (by omega : n ≠ n + 2)] at h
  linarith

private lemma moment_up (n : ℕ) :
    ((n : ℝ) + 1) * polyInt (legendre (n + 1) * legendre (n + 1)) =
      (2 * (n : ℝ) + 1) * polyInt (X * legendre (n + 1) * legendre n) := by
  cases n with
  | zero =>
    have e : legendre (0 + 1) * legendre (0 + 1) = X * legendre (0 + 1) * legendre 0 := by simp
    rw [e]
    push_cast
    ring
  | succ k =>
    have h := congrArg (fun q => polyInt (legendre (k + 2) * q)) (recursion_C k)
    rw [show legendre (k + 2) * (C ((k : ℝ) + 2) * legendre (k + 2)) =
        C ((k : ℝ) + 2) * (legendre (k + 2) * legendre (k + 2)) by ring,
      show legendre (k + 2) * (C (2 * (k : ℝ) + 3) * (X * legendre (k + 1)) -
          C ((k : ℝ) + 1) * legendre k) =
        C (2 * (k : ℝ) + 3) * (X * legendre (k + 2) * legendre (k + 1)) -
          C ((k : ℝ) + 1) * (legendre (k + 2) * legendre k) by ring,
      polyInt_sub, polyInt_C_mul, polyInt_C_mul, polyInt_C_mul,
      polyInt_legendre_mul (by omega : k + 2 ≠ k), mul_zero, sub_zero] at h
    push_cast
    linarith

/-- arXiv 1906.09940, Sec. 2.1 (the Legendre polynomials): **Norm of the Legendre polynomials**,
`∫₋₁¹ P̄ₙ² = 2 / (2 n + 1)`. -/
theorem polyInt_legendre_sq (n : ℕ) :
    polyInt (legendre n * legendre n) = 2 / (2 * n + 1) := by
  have key : (2 * (n : ℝ) + 1) * polyInt (legendre n * legendre n) = 2 := by
    induction n with
    | zero =>
      have : polyInt (legendre 0 * legendre 0) = 2 := by
        simp only [legendre_zero, mul_one, polyInt, eval_one]
        norm_num
      rw [this]
      norm_num
    | succ n ih =>
      have h1 := moment_down n
      have h2 := moment_up n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      push_cast
      linear_combination (2 * (n : ℝ) + 3) * h2 + (2 * (n : ℝ) + 1) * h1 + ((n : ℝ) + 1) * ih
  have hn : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith

private lemma X_mul_succ (k : ℕ) :
    C (2 * (k : ℝ) + 3) * (X * legendre (k + 1)) =
      C ((k : ℝ) + 2) * legendre (k + 2) + C ((k : ℝ) + 1) * legendre k := by
  rw [recursion_C]; ring

/-- arXiv 1906.09940, Sec. 2.1 (the Legendre polynomials): `∫₋₁¹ X P̄ᵢ P̄ⱼ = 0` unless `j = i ± 1`:
the matrix of multiplication by `X` is tridiagonal (with zero diagonal). -/
theorem polyInt_X_legendre_eq_zero {i j : ℕ} (h1 : j ≠ i + 1) (h2 : i ≠ j + 1) :
    polyInt (X * legendre i * legendre j) = 0 := by
  cases i with
  | zero =>
    simp only [legendre_zero, mul_one]
    have hj : j ≠ 1 := by simpa using h1
    have := polyInt_legendre_mul (m := 1) (n := j) hj.symm
    simpa using this
  | succ k =>
    have hne : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    have h := congrArg (fun q => polyInt (q * legendre j)) (X_mul_succ k)
    rw [show C (2 * (k : ℝ) + 3) * (X * legendre (k + 1)) * legendre j =
        C (2 * (k : ℝ) + 3) * (X * legendre (k + 1) * legendre j) by ring,
      show (C ((k : ℝ) + 2) * legendre (k + 2) + C ((k : ℝ) + 1) * legendre k) * legendre j =
        C ((k : ℝ) + 2) * (legendre (k + 2) * legendre j) +
          C ((k : ℝ) + 1) * (legendre k * legendre j) by ring,
      polyInt_add, polyInt_C_mul, polyInt_C_mul, polyInt_C_mul,
      polyInt_legendre_mul (by omega : k + 2 ≠ j), polyInt_legendre_mul (by omega : k ≠ j)] at h
    apply (mul_eq_zero.mp (h.trans (by ring))).resolve_left hne

/-- arXiv 1906.09940, Sec. 2.1 (the Legendre polynomials): `∫₋₁¹ X P̄ᵢ₊₁ P̄ᵢ = 2 (i + 1) / ((2 i +
1) (2 i + 3))`. -/
theorem polyInt_X_legendre_succ (i : ℕ) :
    polyInt (X * legendre (i + 1) * legendre i) =
      2 * ((i : ℝ) + 1) / ((2 * i + 1) * (2 * i + 3)) := by
  have h := moment_down i
  rw [polyInt_legendre_sq] at h
  have h1 : (2 * (i : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (2 * (i : ℝ) + 3) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

/-- The normalised Legendre functions of the paper: `P_{l+1}(μ) = √((2 l + 1) / 2) P̄_l(μ)`
(paper's index `j = l + 1`; we count from `0`). -/
noncomputable def nLeg (l : ℕ) (μ : ℝ) : ℝ := √((2 * (l : ℝ) + 1) / 2) * (legendre l).eval μ

/-- The normalised Legendre functions are continuous. -/
lemma continuous_nLeg (l : ℕ) : Continuous (nLeg l) :=
  continuous_const.mul (legendre l).continuous

private lemma nLeg_mul (k l : ℕ) (μ : ℝ) :
    nLeg k μ * nLeg l μ = √((2 * (k : ℝ) + 1) / 2) * √((2 * (l : ℝ) + 1) / 2) *
      (legendre k * legendre l).eval μ := by
  simp only [nLeg, eval_mul]; ring

/-- Sec. 2.1 of arXiv 1906.09940: the normalised Legendre functions are orthonormal on `[-1, 1]`,
`⟨P_k, P_l⟩_μ = δ_kl`. -/
theorem integral_nLeg_mul (k l : ℕ) :
    ∫ μ in (-1 : ℝ)..1, nLeg k μ * nLeg l μ = if k = l then 1 else 0 := by
  simp_rw [nLeg_mul]
  rw [intervalIntegral.integral_const_mul]
  change _ * polyInt _ = _
  split_ifs with h
  · subst h
    have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    rw [polyInt_legendre_sq, Real.mul_self_sqrt (by positivity)]
    field_simp
  · rw [polyInt_legendre_mul h, mul_zero]

/-- `P_0 = 1 / √2`: the isotropic mode. -/
lemma nLeg_zero (μ : ℝ) : nLeg 0 μ = (√2)⁻¹ := by
  have h : √((2 * ((0 : ℕ) : ℝ) + 1) / 2) = (√2)⁻¹ := by
    rw [show (2 * ((0 : ℕ) : ℝ) + 1) / 2 = 2⁻¹ by norm_num, Real.sqrt_inv]
  simp only [nLeg, h, legendre_zero, eval_one, mul_one]

/-- arXiv 1906.09940, (2.8)-(2.9): `⟨P_l⟩_μ = √2 δ_{l0}`: only the isotropic mode has a nonzero
mean. -/
theorem integral_nLeg (l : ℕ) :
    ∫ μ in (-1 : ℝ)..1, nLeg l μ = if l = 0 then √2 else 0 := by
  have h := integral_nLeg_mul l 0
  simp_rw [nLeg_zero, mul_comm (nLeg l _) (√2)⁻¹] at h
  rw [intervalIntegral.integral_const_mul] at h
  have h2 : √2 ≠ 0 := by positivity
  split_ifs at h ⊢ with hl
  · field_simp at h
    linarith
  · simpa [h2] using h

/-- The off-diagonal recursion coefficient `(i + 1) / √((2 i + 1) (2 i + 3))` of the matrix `C`. -/
noncomputable def muOff (i : ℕ) : ℝ := ((i : ℝ) + 1) / √((2 * i + 1) * (2 * i + 3))

private lemma nLeg_mu_mul (i k : ℕ) (μ : ℝ) :
    μ * nLeg i μ * nLeg k μ = √((2 * (i : ℝ) + 1) / 2) * √((2 * (k : ℝ) + 1) / 2) *
      (X * legendre i * legendre k).eval μ := by
  simp only [nLeg, eval_mul, eval_X]; ring

private lemma coeff_muOff (i : ℕ) :
    √((2 * (i : ℝ) + 1) / 2) * √((2 * ((i + 1 : ℕ) : ℝ) + 1) / 2) *
      (2 * ((i : ℝ) + 1) / ((2 * i + 1) * (2 * i + 3))) = muOff i := by
  set r := √((2 * (i : ℝ) + 1) * (2 * i + 3)) with hr
  have hr2 : r ^ 2 = (2 * (i : ℝ) + 1) * (2 * i + 3) := Real.sq_sqrt (by positivity)
  have hr0 : r ≠ 0 := by
    have : 0 < r := Real.sqrt_pos.2 (by positivity)
    exact this.ne'
  have hst : √((2 * (i : ℝ) + 1) / 2) * √((2 * ((i + 1 : ℕ) : ℝ) + 1) / 2) = r / 2 := by
    rw [← Real.sqrt_mul (by positivity),
      show (2 * (i : ℝ) + 1) / 2 * ((2 * ((i + 1 : ℕ) : ℝ) + 1) / 2) =
        ((2 * (i : ℝ) + 1) * (2 * i + 3)) / 2 ^ 2 by push_cast; ring,
      Real.sqrt_div (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hst, ← hr2, muOff, ← hr]
  field_simp

/-- **The recursion matrix** (arXiv 1906.09940, Sec. 2.1, after (2.14)): the entries of
`C = ⟨μ P_i P_k⟩_μ` in closed form, `C_{i,i+1} = C_{i+1,i} = (i + 1) / √((2 i + 1) (2 i + 3))`,
all other entries zero. -/
theorem integral_mu_nLeg (i k : ℕ) :
    ∫ μ in (-1 : ℝ)..1, μ * nLeg i μ * nLeg k μ =
      if k = i + 1 then muOff i else if i = k + 1 then muOff k else 0 := by
  simp_rw [nLeg_mu_mul]
  rw [intervalIntegral.integral_const_mul]
  change _ * polyInt _ = _
  split_ifs with h1 h2
  · subst h1
    rw [show (X : ℝ[X]) * legendre i * legendre (i + 1) = X * legendre (i + 1) * legendre i by ring,
      polyInt_X_legendre_succ, coeff_muOff]
  · subst h2
    rw [polyInt_X_legendre_succ, mul_comm (√_) (√_), coeff_muOff]
  · rw [polyInt_X_legendre_eq_zero h1 h2, mul_zero]

/-- The matrix `C = ⟨μ P_i P_k⟩_μ` of arXiv 1906.09940, Sec. 2.1 (the `n × n` matrix after
(2.14)), defined by the integrals themselves. -/
noncomputable def muMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ∫ μ in (-1 : ℝ)..1, μ * nLeg i μ * nLeg k μ

/-- arXiv 1906.09940, Sec. 2.1: `C` is the tridiagonal Legendre recursion matrix with zero
diagonal. -/
theorem muMatrix_apply {n : ℕ} (i k : Fin n) :
    muMatrix n i k = if (k : ℕ) = i + 1 then muOff i else if (i : ℕ) = k + 1 then muOff k else 0 :=
  integral_mu_nLeg i k

/-- arXiv 1906.09940, Sec. 2.1: the integrals `⟨μ P_i P_k⟩_μ` are the library's formula for the
Legendre moment matrix, `LeanDLRA.OpenProblems.Stiff.legendreJacobi`. -/
theorem muMatrix_eq_legendreJacobi (n : ℕ) :
    muMatrix n = LeanDLRA.OpenProblems.Stiff.legendreJacobi n := by
  ext i k
  rw [muMatrix_apply]
  rfl

/-- arXiv 1906.09940, Sec. 2.1: `C` is symmetric. -/
theorem muMatrix_transpose (n : ℕ) : (muMatrix n)ᵀ = muMatrix n := by
  ext i k
  simp only [Matrix.transpose_apply, muMatrix, Matrix.of_apply]
  exact intervalIntegral.integral_congr fun μ _ => by ring

/-- arXiv 1906.09940, Sec. 2.1: `C` is tridiagonal: `C_ik = 0` unless `|i - k| = 1`. -/
theorem muMatrix_eq_zero {n : ℕ} {i k : Fin n} (h1 : (k : ℕ) ≠ i + 1) (h2 : (i : ℕ) ≠ k + 1) :
    muMatrix n i k = 0 := by
  simp [muMatrix_apply, h1, h2]

end Legendre

/-! ### The angular and spatial bases, eqs. (2.11), (2.12), (2.14) -/

section Bases

private lemma integral_sum_mul_sum {α : Type*} [Fintype α] {a b : ℝ} (w : ℝ → ℝ) (f : α → ℝ → ℝ)
    (hint : ∀ l k, IntervalIntegrable (fun x => w x * f l x * f k x) MeasureTheory.volume a b)
    (u v : α → ℝ) :
    ∫ x in a..b, w x * (∑ l, f l x * u l) * (∑ k, f k x * v k) =
      ∑ l, ∑ k, u l * v k * ∫ x in a..b, w x * f l x * f k x := by
  have e : ∀ x, w x * (∑ l, f l x * u l) * (∑ k, f k x * v k) =
      ∑ l, ∑ k, u l * v k * (w x * f l x * f k x) := by
    intro x
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
    · exact fun k _ => (hint l k).const_mul _
  · refine fun l _ => ?_
    have := IntervalIntegrable.sum (Finset.univ : Finset α)
      (fun k _ => (hint l k).const_mul (u l * v k))
    convert this using 1
    ext x
    simp

variable {ι : Type*} {n : ℕ}

/-- The angular basis (2.12): `W_j(μ) = ∑_l P_l(μ) v_lj`. -/
noncomputable def angularBasis (V : Matrix (Fin n) ι ℝ) (j : ι) (μ : ℝ) : ℝ :=
  ∑ l : Fin n, nLeg l μ * V l j

private lemma nLeg_triple_integrable (w : ℝ → ℝ) (hw : Continuous w) (l k : Fin n) :
    IntervalIntegrable (fun μ => w μ * nLeg l μ * nLeg k μ) MeasureTheory.volume (-1) 1 :=
  ((hw.mul (continuous_nLeg l)).mul (continuous_nLeg k)).intervalIntegrable _ _

/-- arXiv 1906.09940, (2.12): `⟨W_j, W_j'⟩_μ = (Vᵀ V)_jj'`, so the `W_j` are orthonormal exactly
when `V` has orthonormal columns. -/
theorem integral_angularBasis_mul (V : Matrix (Fin n) ι ℝ) (j j' : ι) :
    ∫ μ in (-1 : ℝ)..1, angularBasis V j μ * angularBasis V j' μ = (Vᵀ * V) j j' := by
  have h := integral_sum_mul_sum (a := -1) (b := 1) (fun _ => 1) (fun l : Fin n => nLeg l)
    (nLeg_triple_integrable _ continuous_const) (fun l => V l j) (fun k => V k j')
  simp only [one_mul] at h
  simp only [angularBasis]
  rw [h]
  simp only [integral_nLeg_mul, Matrix.mul_apply, Matrix.transpose_apply, Fin.val_inj]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

/-- **Eq. (2.14) of arXiv 1906.09940**: `⟨μ W_j W_j'⟩_μ = (Vᵀ C V)_jj'`. -/
theorem integral_mu_angularBasis (V : Matrix (Fin n) ι ℝ) (j j' : ι) :
    ∫ μ in (-1 : ℝ)..1, μ * angularBasis V j μ * angularBasis V j' μ =
      (Vᵀ * muMatrix n * V) j j' := by
  have h := integral_sum_mul_sum (a := -1) (b := 1) (fun μ => μ) (fun l : Fin n => nLeg l)
    (nLeg_triple_integrable _ continuous_id) (fun l => V l j) (fun k => V k j')
  simp only [angularBasis]
  rw [h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, muMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- arXiv 1906.09940, (2.8): `⟨W_j⟩_μ = √2 v_0j`: the mean of an angular basis function, as it
enters (2.8) and (2.9). -/
theorem integral_angularBasis [NeZero n] (V : Matrix (Fin n) ι ℝ) (j : ι) :
    ∫ μ in (-1 : ℝ)..1, angularBasis V j μ = √2 * V 0 j := by
  have hI : ∀ l ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
      (fun μ => nLeg l μ * V l j) MeasureTheory.volume (-1) 1 := fun l _ =>
    ((continuous_nLeg l).mul continuous_const).intervalIntegrable _ _
  simp only [angularBasis]
  rw [intervalIntegral.integral_finsetSum hI]
  simp only [intervalIntegral.integral_mul_const, integral_nLeg]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro l _ hl
    have : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext (by simpa using h))
    simp [this]
  · simp

/-- arXiv 1906.09940, Sec. 2.1: `-1 ≤ s C ≤ 1` for `|s| ≤ 1`, in the form `1 + s C ≥ 0`.  This
follows from `∫ (1 + s μ) f² ≥ 0`; the spectrum of `C` lies in `[-1, 1]`, i.e. all characteristic
speeds of the discrete system are bounded by the particle speed. -/
theorem one_add_smul_muMatrix_posSemidef (n : ℕ) {s : ℝ} (hs : |s| ≤ 1) :
    (1 + s • muMatrix n).PosSemidef := by
  have hsym : (1 + s • muMatrix n).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add,
      Matrix.transpose_smul, muMatrix_transpose, Matrix.transpose_one]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym fun x => ?_
  have h := integral_sum_mul_sum (a := -1) (b := 1) (fun μ => 1 + s * μ)
    (fun l : Fin n => nLeg l) (nLeg_triple_integrable _ (by fun_prop)) x x
  have hent : ∀ l k : Fin n, ∫ μ in (-1 : ℝ)..1, (1 + s * μ) * nLeg l μ * nLeg k μ =
      (1 + s • muMatrix n) l k := by
    intro l k
    have e : ∀ μ, (1 + s * μ) * nLeg l μ * nLeg k μ =
        nLeg l μ * nLeg k μ + s * (μ * nLeg l μ * nLeg k μ) := fun μ => by ring
    have h1 : IntervalIntegrable (fun μ => nLeg l μ * nLeg k μ) MeasureTheory.volume (-1) 1 :=
      ((continuous_nLeg l).mul (continuous_nLeg k)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun μ => s * (μ * nLeg l μ * nLeg k μ))
        MeasureTheory.volume (-1) 1 :=
      (nLeg_triple_integrable (fun μ => μ) continuous_id l k).const_mul s
    simp_rw [e]
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      integral_nLeg_mul]
    simp [Matrix.add_apply, Matrix.one_apply, muMatrix, Fin.val_inj]
  have key : star x ⬝ᵥ ((1 + s • muMatrix n) *ᵥ x) =
      ∫ μ in (-1 : ℝ)..1, (1 + s * μ) * (∑ l : Fin n, nLeg l μ * x l) *
        (∑ k : Fin n, nLeg k μ * x k) := by
    rw [h]
    simp only [hent, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [key]
  refine intervalIntegral.integral_nonneg (by norm_num) fun μ hμ => ?_
  have h1 : 0 ≤ 1 + s * μ := by
    have := abs_le.1 hs
    nlinarith [hμ.1, hμ.2, this.1, this.2]
  rw [mul_assoc]
  exact mul_nonneg h1 (mul_self_nonneg _)

end Bases

/-! ### The finite-volume basis, eq. (2.11) -/

section FiniteVolume

/-- Cell `k` of the uniform mesh on `[0, m Δz]` (zero-based; the paper's closed cells differ from
these half-open ones by a null set). -/
def cell (Δz : ℝ) (k : ℕ) : Set ℝ := Set.Ioc (k * Δz) ((k + 1) * Δz)

/-- The orthonormal cell function `Z_k = (√Δz)⁻¹ 𝟙_{cell k}` of (2.11). -/
noncomputable def cellFn (Δz : ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  (cell Δz k).indicator (fun _ => (√Δz)⁻¹) z

variable {Δz : ℝ} {k l m : ℕ}

private lemma cell_disjoint (hΔ : 0 < Δz) (h : k ≠ l) {z : ℝ} (hk : z ∈ cell Δz k)
    (hl : z ∈ cell Δz l) : False := by
  have key : ∀ {a b : ℕ}, a < b → z ∈ cell Δz a → z ∈ cell Δz b → False := by
    intro a b hab ha hb
    have h1 : ((a : ℝ) + 1) * Δz ≤ b * Δz :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hΔ.le
    linarith [ha.2, hb.1]
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · exact key hlt hk hl
  · exact key hlt hl hk

/-- Different cell functions have disjoint supports. -/
lemma cellFn_mul_of_ne (hΔ : 0 < Δz) (h : k ≠ l) (z : ℝ) :
    cellFn Δz k z * cellFn Δz l z = 0 := by
  by_cases hk : z ∈ cell Δz k
  · by_cases hl : z ∈ cell Δz l
    · exact (cell_disjoint hΔ h hk hl).elim
    · simp [cellFn, hl]
  · simp [cellFn, hk]

/-- `Z_k² = Z_k / √Δz`. -/
lemma cellFn_mul_self (z : ℝ) : cellFn Δz k z * cellFn Δz k z = (√Δz)⁻¹ * cellFn Δz k z := by
  by_cases hk : z ∈ cell Δz k <;> simp [cellFn, hk]

private lemma cell_subset (hΔ : 0 < Δz) (hk : k < m) :
    cell Δz k ⊆ Set.Ioc 0 (m * Δz) := by
  have h1 : ((k : ℝ) + 1) * Δz ≤ m * Δz :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔ.le
  have h0 : (0 : ℝ) ≤ k * Δz := by positivity
  exact fun z hz => ⟨h0.trans_lt hz.1, hz.2.trans h1⟩

/-- arXiv 1906.09940, (2.11), (2.15): Testing with the cell function `Z_k` is `(√Δz)⁻¹` times
integration over cell `k`. -/
theorem integral_cellFn_mul (hΔ : 0 < Δz) (hk : k < m) (g : ℝ → ℝ) :
    ∫ z in (0 : ℝ)..(m * Δz), cellFn Δz k z * g z =
      (√Δz)⁻¹ * ∫ z in ((k : ℝ) * Δz)..(((k : ℝ) + 1) * Δz), g z := by
  have hle : (0 : ℝ) ≤ m * Δz := by positivity
  have hle' : (k : ℝ) * Δz ≤ ((k : ℝ) + 1) * Δz := by nlinarith
  have e : (fun z => cellFn Δz k z * g z) = (cell Δz k).indicator fun z => (√Δz)⁻¹ * g z := by
    ext z
    by_cases hz : z ∈ cell Δz k <;> simp [cellFn, hz]
  have hm : MeasurableSet (cell Δz k) := measurableSet_Ioc
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle', e,
    MeasureTheory.setIntegral_indicator hm,
    Set.inter_eq_right.2 (cell_subset hΔ hk), MeasureTheory.integral_const_mul]
  rfl

/-- The cell functions are integrable. -/
lemma cellFn_intervalIntegrable (Δz : ℝ) (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (cellFn Δz k) MeasureTheory.volume a b := by
  have hfin : MeasureTheory.IntegrableOn (fun _ : ℝ => (√Δz)⁻¹) (cell Δz k)
      MeasureTheory.volume := by
    apply MeasureTheory.integrableOn_const
    · simp [cell]
    · simp
  have hm : MeasurableSet (cell Δz k) := measurableSet_Ioc
  have h : MeasureTheory.Integrable (cellFn Δz k) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hm).2 hfin
  exact h.intervalIntegrable

/-- arXiv 1906.09940, (2.11): `⟨Z_k⟩_z = √Δz`. -/
theorem integral_cellFn (hΔ : 0 < Δz) (hk : k < m) :
    ∫ z in (0 : ℝ)..(m * Δz), cellFn Δz k z = √Δz := by
  have h := integral_cellFn_mul hΔ hk (fun _ => 1)
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at h
  rw [h]
  have hs : √Δz ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  have hs2 : √Δz * √Δz = Δz := Real.mul_self_sqrt hΔ.le
  field_simp
  nlinarith

/-- A piecewise constant coefficient (cross section) with value `σ_j` on cell `j`. -/
noncomputable def pwConst (Δz : ℝ) {m : ℕ} (σ : Fin m → ℝ) (z : ℝ) : ℝ :=
  ∑ j : Fin m, σ j * (√Δz * cellFn Δz j z)

/-- On cell `j`, the piecewise constant `σ` is the constant `σ_j`. -/
lemma pwConst_mul_cellFn (hΔ : 0 < Δz) {m : ℕ} (σ : Fin m → ℝ) (j : Fin m) (z : ℝ) :
    pwConst Δz σ z * cellFn Δz j z = σ j * cellFn Δz j z := by
  rw [pwConst, Finset.sum_mul, Finset.sum_eq_single j]
  · have hs : √Δz ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
    rw [mul_assoc, mul_assoc, cellFn_mul_self, ← mul_assoc (√Δz), mul_inv_cancel₀ hs, one_mul]
  · intro i _ hi
    have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
    rw [mul_assoc, mul_assoc, cellFn_mul_of_ne hΔ this]
    simp
  · simp

/-- arXiv 1906.09940, (2.9), (2.11): The weighted Gram matrix of the cell functions: `⟨σ Z_l, Z_k⟩_z
= σ_l δ_lk`.  For `σ ≡ 1` these are the orthonormality relations of the finite-volume basis. -/
theorem integral_pwConst_cellFn_mul (hΔ : 0 < Δz) {m : ℕ} (σ : Fin m → ℝ) (l k : Fin m) :
    ∫ z in (0 : ℝ)..((m : ℝ) * Δz), pwConst Δz σ z * cellFn Δz l z * cellFn Δz k z =
      if l = k then σ l else 0 := by
  have hs : √Δz ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  simp_rw [pwConst_mul_cellFn hΔ, mul_assoc]
  split_ifs with h
  · subst h
    simp_rw [cellFn_mul_self]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cellFn hΔ l.2, inv_mul_cancel₀ hs, mul_one]
  · have hne : (l : ℕ) ≠ k := fun e => h (Fin.ext e)
    simp_rw [cellFn_mul_of_ne hΔ hne]
    simp

/-- arXiv 1906.09940, (2.11): `⟨Z_l, Z_k⟩_z = δ_lk` (the orthonormal finite-volume basis of Sec.
2.1). -/
theorem integral_cellFn_mul_cellFn (hΔ : 0 < Δz) (hk : k < m) (l : ℕ) :
    ∫ z in (0 : ℝ)..((m : ℝ) * Δz), cellFn Δz l z * cellFn Δz k z = if l = k then 1 else 0 := by
  have hs : √Δz ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  split_ifs with h
  · subst h
    simp_rw [cellFn_mul_self]
    rw [intervalIntegral.integral_const_mul, integral_cellFn hΔ hk, inv_mul_cancel₀ hs]
  · simp_rw [cellFn_mul_of_ne hΔ h]
    simp

/-- **Eq. (2.15), first equality** of arXiv 1906.09940: testing a derivative with `Z_k` gives the
difference of the interface values, with the paper's prefactor `1 / √Δz`. -/
theorem integral_cellFn_deriv (hΔ : 0 < Δz) (hk : k < m) {f f' : ℝ → ℝ}
    (hf : ∀ z ∈ Set.uIcc ((k : ℝ) * Δz) (((k : ℝ) + 1) * Δz), HasDerivAt f (f' z) z)
    (hint : IntervalIntegrable f' MeasureTheory.volume ((k : ℝ) * Δz) (((k : ℝ) + 1) * Δz)) :
    ∫ z in (0 : ℝ)..((m : ℝ) * Δz), cellFn Δz k z * f' z =
      (f (((k : ℝ) + 1) * Δz) - f ((k : ℝ) * Δz)) / √Δz := by
  rw [integral_cellFn_mul hΔ hk, intervalIntegral.integral_eq_sub_of_hasDerivAt hf hint,
    div_eq_inv_mul]

variable {ι : Type*}

/-- The spatial basis (2.11): `X_i(z) = ∑_k Z_k(z) u_ki`. -/
noncomputable def spatialBasis (Δz : ℝ) {m : ℕ} (U : Matrix (Fin m) ι ℝ) (i : ι) (z : ℝ) : ℝ :=
  ∑ k : Fin m, cellFn Δz k z * U k i

private lemma pw_triple_integrable (hΔ : 0 < Δz) {m : ℕ} (σ : Fin m → ℝ) (l k : Fin m) (a b : ℝ) :
    IntervalIntegrable (fun z => pwConst Δz σ z * cellFn Δz l z * cellFn Δz k z)
      MeasureTheory.volume a b := by
  simp_rw [pwConst_mul_cellFn hΔ, mul_assoc]
  by_cases h : l = k
  · subst h
    simp_rw [cellFn_mul_self]
    exact ((cellFn_intervalIntegrable Δz _ a b).const_mul _).const_mul _
  · have hne : (l : ℕ) ≠ k := fun e => h (Fin.ext e)
    simp_rw [cellFn_mul_of_ne hΔ hne, mul_zero]
    exact intervalIntegrable_const

/-- arXiv 1906.09940, (2.11): `⟨σ X_i, X_j⟩_z = (Uᵀ diag(σ) U)_ij` for a piecewise constant `σ`. -/
theorem integral_pwConst_spatialBasis (hΔ : 0 < Δz) {m : ℕ} (σ : Fin m → ℝ)
    (U : Matrix (Fin m) ι ℝ) (i j : ι) :
    ∫ z in (0 : ℝ)..((m : ℝ) * Δz),
        pwConst Δz σ z * spatialBasis Δz U i z * spatialBasis Δz U j z =
      (Uᵀ * Matrix.diagonal σ * U) i j := by
  have h := integral_sum_mul_sum (a := 0) (b := (m : ℝ) * Δz) (pwConst Δz σ)
    (fun k : Fin m => cellFn Δz k)
    (fun l k => pw_triple_integrable hΔ σ l k _ _) (fun k => U k i) (fun k => U k j)
  simp only [spatialBasis]
  rw [h, Matrix.mul_apply]
  simp only [integral_pwConst_cellFn_mul hΔ, Matrix.transpose_apply, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- arXiv 1906.09940, (2.11): `⟨X_i, X_j⟩_z = (Uᵀ U)_ij`, so the `X_i` are orthonormal exactly
when `U` has orthonormal columns. -/
theorem integral_spatialBasis_mul (hΔ : 0 < Δz) {m : ℕ} (U : Matrix (Fin m) ι ℝ) (i j : ι) :
    ∫ z in (0 : ℝ)..((m : ℝ) * Δz), spatialBasis Δz U i z * spatialBasis Δz U j z =
      (Uᵀ * U) i j := by
  have hint : ∀ l k : Fin m, IntervalIntegrable (fun z => 1 * cellFn Δz l z * cellFn Δz k z)
      MeasureTheory.volume 0 ((m : ℝ) * Δz) := by
    intro l k
    simp only [one_mul]
    by_cases h : l = k
    · subst h
      simp_rw [cellFn_mul_self]
      exact (cellFn_intervalIntegrable Δz _ _ _).const_mul _
    · have hne : (l : ℕ) ≠ k := fun e => h (Fin.ext e)
      simp_rw [cellFn_mul_of_ne hΔ hne]
      exact intervalIntegrable_const
  have h := integral_sum_mul_sum (a := 0) (b := (m : ℝ) * Δz) (fun _ => 1)
    (fun k : Fin m => cellFn Δz k) hint (fun k => U k i) (fun k => U k j)
  simp only [one_mul] at h
  simp only [spatialBasis]
  rw [h]
  simp only [integral_cellFn_mul_cellFn hΔ (Fin.isLt _), Matrix.mul_apply, Matrix.transpose_apply,
    Fin.val_inj]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

end FiniteVolume

/-! ### The projectors (2.2), (2.3) in the coefficients -/

section Projectors

variable {n r : ℕ}

private lemma sum_basis_proj (f : Fin n → ℝ) (V : 𝐌[n, r]) (y : Fin n → ℝ) :
    ∑ j : Fin r, (∑ l : Fin n, f l * V l j) * (∑ a : Fin n, V a j * y a) =
      ∑ l : Fin n, f l * (y ᵥ* (V * Vᵀ)) l := by
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, p]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Eq. (2.3) of arXiv 1906.09940**: on `ψ = ∑_l y_l P_l`, the projector
`P_W ψ = ∑_j W_j ⟨W_j ψ⟩_μ` acts on the coefficients as `y ↦ y V Vᵀ`, i.e. as
`LeanDLRA.rightProj V` on the rows of a coefficient matrix. -/
theorem angular_projector (V : 𝐌[n, r]) (y : Fin n → ℝ) (μ : ℝ) :
    ∑ j : Fin r, angularBasis V j μ *
        ∫ μ' in (-1 : ℝ)..1, angularBasis V j μ' * (∑ l : Fin n, nLeg l μ' * y l) =
      ∑ l : Fin n, nLeg l μ * (y ᵥ* (V * Vᵀ)) l := by
  have hin : ∀ j : Fin r, ∫ μ' in (-1 : ℝ)..1, angularBasis V j μ' *
      (∑ l : Fin n, nLeg l μ' * y l) = ∑ a : Fin n, V a j * y a := by
    intro j
    have h := integral_sum_mul_sum (a := -1) (b := 1) (fun _ => 1) (fun l : Fin n => nLeg l)
      (nLeg_triple_integrable _ continuous_const) (fun l => V l j) y
    simp only [one_mul] at h
    simp only [angularBasis]
    rw [h]
    simp only [integral_nLeg_mul, Fin.val_inj]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  simp_rw [hin]
  simp only [angularBasis]
  exact sum_basis_proj (fun l => nLeg l μ) V y

/-- **Eq. (2.2) of arXiv 1906.09940**: on `ψ = ∑_k y_k Z_k`, the projector
`P_X ψ = ∑_i X_i ⟨X_i ψ⟩_z` acts on the coefficients as `y ↦ y U Uᵀ`, i.e. as
`LeanDLRA.leftProj U` on the columns of a coefficient matrix. -/
theorem spatial_projector {Δz : ℝ} (hΔ : 0 < Δz) {m : ℕ} (U : 𝐌[m, r]) (y : Fin m → ℝ) (z : ℝ) :
    ∑ i : Fin r, spatialBasis Δz U i z *
        ∫ z' in (0 : ℝ)..((m : ℝ) * Δz), spatialBasis Δz U i z' *
          (∑ k : Fin m, cellFn Δz k z' * y k) =
      ∑ k : Fin m, cellFn Δz k z * (y ᵥ* (U * Uᵀ)) k := by
  have hint : ∀ l k : Fin m, IntervalIntegrable (fun z => 1 * cellFn Δz l z * cellFn Δz k z)
      MeasureTheory.volume 0 ((m : ℝ) * Δz) := by
    intro l k
    simp only [one_mul]
    by_cases h : l = k
    · subst h
      simp_rw [cellFn_mul_self]
      exact (cellFn_intervalIntegrable Δz _ _ _).const_mul _
    · have hne : (l : ℕ) ≠ k := fun e => h (Fin.ext e)
      simp_rw [cellFn_mul_of_ne hΔ hne]
      exact intervalIntegrable_const
  have hin : ∀ i : Fin r, ∫ z' in (0 : ℝ)..((m : ℝ) * Δz), spatialBasis Δz U i z' *
      (∑ k : Fin m, cellFn Δz k z' * y k) = ∑ a : Fin m, U a i * y a := by
    intro i
    have h := integral_sum_mul_sum (a := 0) (b := (m : ℝ) * Δz) (fun _ => 1)
      (fun k : Fin m => cellFn Δz k) hint (fun l => U l i) y
    simp only [one_mul] at h
    simp only [spatialBasis]
    rw [h]
    simp only [integral_cellFn_mul_cellFn hΔ (Fin.isLt _), Fin.val_inj]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  simp_rw [hin]
  simp only [spatialBasis]
  exact sum_basis_proj (fun k => cellFn Δz k z) U y

end Projectors

/-! ### Positive semidefinite matrices -/

section Psd

variable {n : ℕ}

open scoped MatrixOrder Matrix.Norms.L2Operator in
private lemma exists_factor {P : 𝐌[n, n]} (hP : P.PosSemidef) :
    ∃ B : 𝐌[n, n], P = Bᵀ * B := by
  obtain ⟨a, ha⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  exact ⟨a, by simpa [Matrix.star_eq_conjTranspose] using ha⟩

end Psd

/-! ### Discrete streaming: shifts, upwind fluxes and the stabilisation, eqs. (2.15), (2.16) -/

section Streaming

open scoped LeanDLRA.Frobenius

variable {m n r : ℕ}

/-- For positive semidefinite `P`, `Q`: `⟪P Y Q, Y⟫ ≥ 0`. -/
lemma inner_mul_mul_nonneg {P : 𝐌[m, m]} {Q : 𝐌[n, n]} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) (Y : 𝐌[m, n]) : 0 ≤ ⟪P * Y * Q, Y⟫ := by
  obtain ⟨B, rfl⟩ := exists_factor hP
  obtain ⟨D, rfl⟩ := exists_factor hQ
  have e : ⟪Bᵀ * B * Y * (Dᵀ * D), Y⟫ = ‖B * Y * Dᵀ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      show Bᵀ * B * Y * (Dᵀ * D) = Bᵀ * (B * Y * Dᵀ * D) by simp only [Matrix.mul_assoc],
      Frobenius.inner_mul_left, Matrix.transpose_transpose, Frobenius.inner_mul_right]
  rw [e]
  positivity

/-- A matrix with `Tᵀ T ≤ 1` is a contraction for the Frobenius norm. -/
lemma norm_mul_le_of_posSemidef {T : 𝐌[m, m]} (hT : (1 - Tᵀ * T).PosSemidef)
    (Y : 𝐌[m, n]) : ‖T * Y‖ ≤ ‖Y‖ := by
  have h := inner_mul_mul_nonneg hT Matrix.PosSemidef.one Y
  rw [Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, inner_sub_left, Matrix.mul_assoc,
    Frobenius.inner_mul_left, Matrix.transpose_transpose] at h
  have h2 : ‖T * Y‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- A *grid shift*: a matrix `T` such that `T` and `Tᵀ` are contractions.  `T Y` has rows
`Y_{i+1}`, `Tᵀ Y` has rows `Y_{i-1}`; see `ghostShift` (zero ghost cells) and `cyclicShift`
(periodic mesh). -/
structure IsShift (T : 𝐌[m, m]) : Prop where
  left : (1 - Tᵀ * T).PosSemidef
  right : (1 - T * Tᵀ).PosSemidef

namespace IsShift

variable {T : 𝐌[m, m]}

/-- A grid shift is a contraction. -/
lemma norm_mul_le (hT : IsShift T) (Y : 𝐌[m, n]) : ‖T * Y‖ ≤ ‖Y‖ :=
  norm_mul_le_of_posSemidef hT.left Y

/-- The transpose of a grid shift is a contraction. -/
lemma norm_transpose_mul_le (hT : IsShift T) (Y : 𝐌[m, n]) : ‖Tᵀ * Y‖ ≤ ‖Y‖ :=
  norm_mul_le_of_posSemidef (by simpa using hT.right) Y

/-- The negative second difference `2 - T - Tᵀ` is positive semidefinite. -/
lemma second_difference (hT : IsShift T) : ((2 : ℝ) • (1 : 𝐌[m, m]) - T - Tᵀ).PosSemidef := by
  have e : (2 : ℝ) • (1 : 𝐌[m, m]) - T - Tᵀ = (1 - T)ᴴ * (1 - T) + (1 - Tᵀ * T) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, two_smul]
    abel
  rw [e]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).add hT.left

end IsShift

/-- The numerical interface flux of (2.15)-(2.16) between left states `Kl` and right states `Kr`:
`½ [(Kl + Kr) M - (Kr - Kl) D]`, a central flux with advection matrix `M` plus a stabilisation
with matrix `D`. -/
noncomputable def faceFlux (M D : 𝐌[n, n]) (Kl Kr : 𝐌[m, n]) : 𝐌[m, n] :=
  (1 / 2 : ℝ) • ((Kl + Kr) * M - (Kr - Kl) * D)

/-- **Eq. (2.16) of arXiv 1906.09940**: the flux difference across a cell is the central
difference plus the stabilising second difference,
`F_{i+½} - F_{i-½} = ½ [(K_{i+1} - K_{i-1}) M - (K_{i+1} - 2 K_i + K_{i-1}) D]`.  Rows of `T K`
are `K_{i+1}`, rows of `Tᵀ K` are `K_{i-1}`.  The paper's prefactor `1 / √Δz` is the one of
`integral_cellFn_deriv`, for interface *values* of `K`. -/
theorem faceFlux_sub (T : 𝐌[m, m]) (M D : 𝐌[n, n]) (K : 𝐌[m, n]) :
    faceFlux M D K (T * K) - faceFlux M D (Tᵀ * K) K =
      (1 / 2 : ℝ) • ((T - Tᵀ) * K * M - (T + Tᵀ - (2 : ℝ) • 1) * K * D) := by
  simp only [faceFlux, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  module

/-- **Low-rank upwinding is the Galerkin projection of full upwinding** (arXiv 1906.09940, (2.16)):
the interface flux with `Vᵀ M V`, `Vᵀ D V` on the K-factors is the full flux of `K Vᵀ`, tested
with `V`. -/
theorem faceFlux_galerkin (M D : 𝐌[n, n]) (V : 𝐌[n, r]) (Kl Kr : 𝐌[m, r]) :
    faceFlux (Vᵀ * M * V) (Vᵀ * D * V) Kl Kr = faceFlux M D (Kl * Vᵀ) (Kr * Vᵀ) * V := by
  simp only [faceFlux, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc]

/-- The semi-discrete streaming operator: `-(2 Δz)⁻¹ [(T - Tᵀ) Y M - (T + Tᵀ - 2) Y D]`, i.e. minus
the flux difference of `faceFlux_sub` divided by `Δz` (in the coefficients with respect to `Z_k`,
see the module docstring for the factor `1 / Δz`). -/
noncomputable def streamOp (T : 𝐌[m, m]) (Δz : ℝ) (M D : 𝐌[n, n]) (Y : 𝐌[m, n]) :
    𝐌[m, n] :=
  -(2 * Δz)⁻¹ • ((T - Tᵀ) * Y * M - (T + Tᵀ - (2 : ℝ) • 1) * Y * D)

/-- arXiv 1906.09940, (2.15)-(2.16): `streamOp` is minus the interface flux difference over `Δz`. -/
theorem streamOp_eq_flux (T : 𝐌[m, m]) (Δz : ℝ) (M D : 𝐌[n, n]) (Y : 𝐌[m, n]) :
    streamOp T Δz M D Y = -Δz⁻¹ • (faceFlux M D Y (T * Y) - faceFlux M D (Tᵀ * Y) Y) := by
  rw [faceFlux_sub, streamOp, smul_smul]
  congr 1
  rw [mul_inv]
  ring

/-- arXiv 1906.09940, (2.8), (2.16): The streaming operator of the K-step: `(streamOp M D (K Vᵀ)) V
= streamOp (Vᵀ M V) (Vᵀ D V) K`. No orthonormality is needed. -/
theorem streamOp_galerkin (T : 𝐌[m, m]) (Δz : ℝ) (M D : 𝐌[n, n]) (V : 𝐌[n, r])
    (K : 𝐌[m, r]) :
    streamOp T Δz M D (K * Vᵀ) * V = streamOp T Δz (Vᵀ * M * V) (Vᵀ * D * V) K := by
  simp only [streamOp, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_assoc]

/-- arXiv 1906.09940, (2.16), stability note of the slice, not in the paper: **Energy identity of
the streaming operator**: the central part is skew, so only the stabilisation changes the energy,
`⟪streamOp Y, Y⟫ = -(2 Δz)⁻¹ ⟪(2 - T - Tᵀ) Y D, Y⟫`, for symmetric `M`. -/
theorem inner_streamOp (T : 𝐌[m, m]) (Δz : ℝ) {M : 𝐌[n, n]} (hM : Mᵀ = M)
    (D : 𝐌[n, n]) (Y : 𝐌[m, n]) :
    ⟪streamOp T Δz M D Y, Y⟫ = -(2 * Δz)⁻¹ * ⟪((2 : ℝ) • 1 - T - Tᵀ) * Y * D, Y⟫ := by
  have hskew : ⟪(T - Tᵀ) * Y * M, Y⟫ = 0 := by
    have h : ⟪(T - Tᵀ) * Y * M, Y⟫ = -⟪(T - Tᵀ) * Y * M, Y⟫ := by
      calc ⟪(T - Tᵀ) * Y * M, Y⟫ = ⟪(T - Tᵀ) * (Y * M), Y⟫ := by rw [Matrix.mul_assoc]
        _ = ⟪Y * M, (T - Tᵀ)ᵀ * Y⟫ := Frobenius.inner_mul_left _ _ _
        _ = ⟪Y, (T - Tᵀ)ᵀ * Y * Mᵀ⟫ := Frobenius.inner_mul_right _ _ _
        _ = -⟪(T - Tᵀ) * Y * M, Y⟫ := by
          rw [hM, real_inner_comm, show (T - Tᵀ)ᵀ = -(T - Tᵀ) by
            rw [Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub],
            Matrix.neg_mul, Matrix.neg_mul, inner_neg_left]
    linarith
  have e : ((2 : ℝ) • 1 - T - Tᵀ) * Y * D = -((T + Tᵀ - (2 : ℝ) • 1) * Y * D) := by
    rw [← Matrix.neg_mul, ← Matrix.neg_mul]
    congr 2
    abel
  rw [streamOp, inner_smul_left, inner_sub_left, hskew, e, inner_neg_left]
  simp

/-- arXiv 1906.09940, (2.16), stability note of the slice, not in the paper: **`L²`-dissipativity of
the stabilised streaming operator**: for a grid shift, `M` symmetric and `D ≥ 0`, `⟪streamOp Y, Y⟫ ≤
0`. -/
theorem inner_streamOp_nonpos {T : 𝐌[m, m]} (hT : IsShift T) {Δz : ℝ} (hΔ : 0 < Δz)
    {M D : 𝐌[n, n]} (hM : Mᵀ = M) (hD : D.PosSemidef) (Y : 𝐌[m, n]) :
    ⟪streamOp T Δz M D Y, Y⟫ ≤ 0 := by
  rw [inner_streamOp T Δz hM]
  have h := inner_mul_mul_nonneg hT.second_difference hD Y
  have h2 : 0 ≤ (2 * Δz)⁻¹ := by positivity
  nlinarith

private lemma norm_sq_mul_transpose (B : 𝐌[n, n]) (Y : 𝐌[m, n]) :
    ‖Y * Bᵀ‖ ^ 2 = ⟪Y * (Bᵀ * B), Y⟫ := by
  rw [← Matrix.mul_assoc, Frobenius.inner_mul_right, real_inner_self_eq_norm_sq]

private lemma inner_shift_le {T : 𝐌[m, m]}
    (hT : ∀ Y : 𝐌[m, n], ‖T * Y‖ ≤ ‖Y‖) (B : 𝐌[n, n])
    (Y Z : 𝐌[m, n]) :
    ⟪T * Y * (Bᵀ * B), Z⟫ ≤ ‖Y * Bᵀ‖ * ‖Z * Bᵀ‖ := by
  rw [← Matrix.mul_assoc, Frobenius.inner_mul_right]
  refine (real_inner_le_norm _ _).trans ?_
  rw [Matrix.mul_assoc]
  exact mul_le_mul_of_nonneg_right (hT _) (norm_nonneg _)

/-- A "convex combination of contractions": if `P₀, P₁, P₂ ≥ 0` sum to `c · 1` and `T₁`, `T₂` are
contractions, then `‖Y P₀ + T₁ Y P₁ + T₂ Y P₂‖ ≤ c ‖Y‖`.  This is the matrix form of the
monotonicity of an upwind scheme. -/
private lemma norm_three_term_le {T₁ T₂ : 𝐌[m, m]}
    (h₁ : ∀ Y : 𝐌[m, n], ‖T₁ * Y‖ ≤ ‖Y‖)
    (h₂ : ∀ Y : 𝐌[m, n], ‖T₂ * Y‖ ≤ ‖Y‖)
    {P₀ P₁ P₂ : 𝐌[n, n]} (hP₀ : P₀.PosSemidef) (hP₁ : P₁.PosSemidef)
    (hP₂ : P₂.PosSemidef) {c : ℝ} (hc : 0 ≤ c) (hsum : P₀ + P₁ + P₂ = c • 1)
    (Y : 𝐌[m, n]) :
    ‖Y * P₀ + T₁ * Y * P₁ + T₂ * Y * P₂‖ ≤ c * ‖Y‖ := by
  obtain ⟨B₀, rfl⟩ := exists_factor hP₀
  obtain ⟨B₁, rfl⟩ := exists_factor hP₁
  obtain ⟨B₂, rfl⟩ := exists_factor hP₂
  set Z := Y * (B₀ᵀ * B₀) + T₁ * Y * (B₁ᵀ * B₁) + T₂ * Y * (B₂ᵀ * B₂) with hZ
  have hsq : ∀ W : 𝐌[m, n],
      ‖W * B₀ᵀ‖ ^ 2 + ‖W * B₁ᵀ‖ ^ 2 + ‖W * B₂ᵀ‖ ^ 2 = c * ‖W‖ ^ 2 := by
    intro W
    rw [norm_sq_mul_transpose, norm_sq_mul_transpose, norm_sq_mul_transpose, ← inner_add_left,
      ← inner_add_left, ← Matrix.mul_add, ← Matrix.mul_add, hsum, Matrix.mul_smul, Matrix.mul_one,
      inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  have h0 : ⟪Y * (B₀ᵀ * B₀), Z⟫ ≤ ‖Y * B₀ᵀ‖ * ‖Z * B₀ᵀ‖ := by
    simpa using inner_shift_le (T := 1) (fun W => by simp) B₀ Y Z
  have h1 := inner_shift_le h₁ B₁ Y Z
  have h2 := inner_shift_le h₂ B₂ Y Z
  have hZZ : ‖Z‖ ^ 2 =
      ⟪Y * (B₀ᵀ * B₀), Z⟫ + ⟪T₁ * Y * (B₁ᵀ * B₁), Z⟫ + ⟪T₂ * Y * (B₂ᵀ * B₂), Z⟫ := by
    rw [← inner_add_left, ← inner_add_left, ← hZ, real_inner_self_eq_norm_sq]
  have hY := hsq Y
  have hZs := hsq Z
  set a₀ := ‖Y * B₀ᵀ‖
  set a₁ := ‖Y * B₁ᵀ‖
  set a₂ := ‖Y * B₂ᵀ‖
  set b₀ := ‖Z * B₀ᵀ‖
  set b₁ := ‖Z * B₁ᵀ‖
  set b₂ := ‖Z * B₂ᵀ‖
  have hle : ‖Z‖ ^ 2 ≤ a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by linarith
  have hCS : (a₀ * b₀ + a₁ * b₁ + a₂ * b₂) ^ 2 ≤
      (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2) * (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2) := by
    nlinarith [sq_nonneg (a₀ * b₁ - a₁ * b₀), sq_nonneg (a₀ * b₂ - a₂ * b₀),
      sq_nonneg (a₁ * b₂ - a₂ * b₁)]
  rw [hY, hZs] at hCS
  have hz := norm_nonneg Z
  have hy := norm_nonneg Y
  by_contra! hcon
  have hzpos : 0 < ‖Z‖ := lt_of_le_of_lt (mul_nonneg hc hy) hcon
  have h3 : (‖Z‖ ^ 2) ^ 2 ≤ (a₀ * b₀ + a₁ * b₁ + a₂ * b₂) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have h4 : ‖Z‖ ^ 2 ≤ (c * ‖Y‖) ^ 2 := by
    have : ‖Z‖ ^ 2 * ‖Z‖ ^ 2 ≤ (c * ‖Y‖) ^ 2 * ‖Z‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  have h5 : (c * ‖Y‖) ^ 2 < ‖Z‖ ^ 2 := pow_lt_pow_left₀ hcon (mul_nonneg hc hy) two_ne_zero
  linarith

/-- The data of a stabilisation: `D` dominates `±M`, and `D ≤ a`.  For `M = C` this holds for the
upwind choice `D = |C|` and the Lax-Friedrichs choice `D = α 1`, `α ≥ 1`
(`isStabilisation_absSymm`, `isStabilisation_laxFriedrichs`). -/
structure IsStabilisation (M D : 𝐌[n, n]) (a : ℝ) : Prop where
  sub : (D - M).PosSemidef
  add : (D + M).PosSemidef
  le : (a • (1 : 𝐌[n, n]) - D).PosSemidef

/-- A stabilisation is positive semidefinite. -/
lemma IsStabilisation.posSemidef {M D : 𝐌[n, n]} {a : ℝ}
    (h : IsStabilisation M D a) : D.PosSemidef := by
  have e : D = (1 / 2 : ℝ) • (D - M) + (1 / 2 : ℝ) • (D + M) := by
    rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ D, smul_smul]
    norm_num
  rw [e]
  exact (h.sub.smul (by norm_num)).add (h.add.smul (by norm_num))

/-- **Discrete `L²`-stability of the stabilised streaming step, the core estimate**: under the CFL
number `ν = h / Δz`, `‖ν a Y + h streamOp Y‖ ≤ ν a ‖Y‖`.  Not in arXiv 1906.09940, which gives no
stability analysis. -/
theorem norm_cfl_streamOp_le {T : 𝐌[m, m]} (hT : IsShift T) {Δz h a : ℝ}
    (hΔ : 0 < Δz) (hh : 0 ≤ h) (ha : 0 ≤ a) {M D : 𝐌[n, n]}
    (hS : IsStabilisation M D a) (Y : 𝐌[m, n]) :
    ‖(h / Δz * a) • Y + h • streamOp T Δz M D Y‖ ≤ h / Δz * a * ‖Y‖ := by
  have hν : 0 ≤ h / Δz := by positivity
  have hν2 : 0 ≤ h / Δz / 2 := by positivity
  have e : (h / Δz * a) • Y + h • streamOp T Δz M D Y =
      Y * ((h / Δz) • (a • 1 - D)) + T * Y * ((h / Δz / 2) • (D - M)) +
        Tᵀ * Y * ((h / Δz / 2) • (D + M)) := by
    have hΔ' : Δz ≠ 0 := hΔ.ne'
    simp only [streamOp, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_sub,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, smul_sub,
      smul_add]
    have e1 : h * (-(2 * Δz)⁻¹ * 2) = -(h / Δz) := by field_simp
    have e2 : h * -(2 * Δz)⁻¹ = -(h / Δz / 2) := by field_simp
    rw [e1, e2]
    simp only [neg_smul]
    abel_nf
  rw [e]
  exact norm_three_term_le hT.norm_mul_le hT.norm_transpose_mul_le (hS.le.smul hν)
    (hS.sub.smul hν2) (hS.add.smul hν2) (by positivity) (by module) Y

/-- The grid shift with zero ghost cells: `(T K)_i = K_{i+1}`, and `K_{m} = 0`. -/
def ghostShift (m : ℕ) : 𝐌[m, m] := Matrix.of fun i j => if (j : ℕ) = i + 1 then 1 else 0

/-- arXiv 1906.09940, (2.16), boundary treatment (unspecified in the paper): `ghostShift` shifts the
rows up and fills in a zero ghost cell. -/
theorem ghostShift_mul_apply (K : 𝐌[m, n]) (i : Fin m) (c : Fin n) :
    (ghostShift m * K) i c = if h : (i : ℕ) + 1 < m then K ⟨i + 1, h⟩ c else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i : ℕ) + 1, h⟩]
    · simp [ghostShift]
    · intro j _ hj
      have : (j : ℕ) ≠ i + 1 := fun e => hj (Fin.ext e)
      simp [ghostShift, this]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have : (j : ℕ) ≠ i + 1 := fun e => h (e ▸ j.2)
    simp [ghostShift, this]

/-- arXiv 1906.09940, (2.16), boundary treatment (unspecified in the paper): `(ghostShift)ᵀ` shifts
the rows down and fills in a zero ghost cell. -/
theorem ghostShift_transpose_mul_apply (K : 𝐌[m, n]) (i : Fin m) (c : Fin n) :
    ((ghostShift m)ᵀ * K) i c = if h : 1 ≤ (i : ℕ) then K ⟨i - 1, by omega⟩ c else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i : ℕ) - 1, by omega⟩]
    · have : (i : ℕ) = i - 1 + 1 := by omega
      simp [ghostShift, ← this]
    · intro j _ hj
      have : (i : ℕ) ≠ j + 1 := fun e => hj (Fin.ext (by simp; omega))
      simp [ghostShift, this]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have : (i : ℕ) ≠ j + 1 := fun e => h (by omega)
    simp [ghostShift, this]

/-- The stencils of arXiv 1906.09940, (2.16), in an interior cell `i`: `T - Tᵀ` is the central
difference `K_{i+1} - K_{i-1}`, `T + Tᵀ - 2` the second difference `K_{i+1} - 2 K_i + K_{i-1}`. -/
theorem ghostShift_stencil (K : 𝐌[m, n]) (i : Fin m) (c : Fin n) (h₁ : 1 ≤ (i : ℕ))
    (h₂ : (i : ℕ) + 1 < m) :
    ((ghostShift m - (ghostShift m)ᵀ) * K) i c = K ⟨i + 1, h₂⟩ c - K ⟨i - 1, by omega⟩ c ∧
      ((ghostShift m + (ghostShift m)ᵀ - (2 : ℝ) • (1 : 𝐌[m, m])) * K) i c =
        K ⟨i + 1, h₂⟩ c - 2 * K i c + K ⟨i - 1, by omega⟩ c := by
  constructor
  · rw [Matrix.sub_mul, Matrix.sub_apply, ghostShift_mul_apply, ghostShift_transpose_mul_apply]
    simp [h₁, h₂]
  · rw [Matrix.sub_mul, Matrix.add_mul, Matrix.sub_apply, Matrix.add_apply, ghostShift_mul_apply,
      ghostShift_transpose_mul_apply, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul]
    simp only [h₁, h₂, dite_true]
    ring

private lemma one_sub_diagonal_posSemidef {d : Fin m → ℝ} (hd : ∀ i, d i ≤ 1) :
    ((1 : 𝐌[m, m]) - Matrix.diagonal d).PosSemidef := by
  have e : (1 : 𝐌[m, m]) - Matrix.diagonal d = Matrix.diagonal fun i => 1 - d i := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [e, Matrix.posSemidef_diagonal_iff]
  exact fun i => sub_nonneg.2 (hd i)

/-- arXiv 1906.09940, (2.16), boundary treatment (unspecified in the paper): The zero-ghost-cell
shift is a grid shift. -/
theorem isShift_ghostShift (m : ℕ) : IsShift (ghostShift m) := by
  have h1 : ghostShift m * (ghostShift m)ᵀ =
      Matrix.diagonal fun i : Fin m => if (i : ℕ) + 1 < m then 1 else 0 := by
    ext i c
    rw [ghostShift_mul_apply, Matrix.diagonal_apply]
    by_cases h : (i : ℕ) + 1 < m
    · by_cases hic : i = c
      · subst hic; simp [ghostShift, h]
      · have : (i : ℕ) ≠ c := fun e => hic (Fin.ext e)
        simp [ghostShift, h, hic, this]
    · by_cases hic : i = c
      · subst hic; simp [h]
      · simp [h, hic]
  have h2 : (ghostShift m)ᵀ * ghostShift m =
      Matrix.diagonal fun i : Fin m => if 1 ≤ (i : ℕ) then 1 else 0 := by
    ext i c
    rw [ghostShift_transpose_mul_apply, Matrix.diagonal_apply]
    by_cases h : 1 ≤ (i : ℕ)
    · by_cases hic : i = c
      · subst hic
        have : (i : ℕ) = i - 1 + 1 := by omega
        simp [ghostShift, h, ← this]
      · have h' : (c : ℕ) ≠ i := fun e => hic (Fin.ext e.symm)
        have e : (i : ℕ) - 1 + 1 = i := by omega
        simp [ghostShift, h, hic, e, h']
    · by_cases hic : i = c
      · subst hic; simp [h]
      · simp [h, hic]
  constructor
  · rw [h2]
    exact one_sub_diagonal_posSemidef fun i => by split_ifs <;> norm_num
  · rw [h1]
    exact one_sub_diagonal_posSemidef fun i => by split_ifs <;> norm_num

/-- The grid shift of a periodic mesh: `(T K)_i = K_{(i+1) mod m}`. -/
def cyclicShift (m : ℕ) : 𝐌[m, m] := Matrix.of fun i j => if (j : ℕ) = (i + 1) % m then 1 else 0

/-- arXiv 1906.09940, (2.16), boundary treatment (unspecified in the paper): `cyclicShift` shifts
the rows cyclically. -/
theorem cyclicShift_mul_apply (K : 𝐌[m, n]) (i : Fin m) (c : Fin n) :
    (cyclicShift m * K) i c = K ⟨(i + 1) % m, Nat.mod_lt _ i.pos⟩ c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨(i + 1) % m, Nat.mod_lt _ i.pos⟩]
  · simp [cyclicShift]
  · intro j _ hj
    have : (j : ℕ) ≠ (i + 1) % m := fun e => hj (Fin.ext e)
    simp [cyclicShift, this]
  · simp

private lemma cyclicShift_mul_transpose (m : ℕ) : cyclicShift m * (cyclicShift m)ᵀ = 1 := by
  ext i c
  rw [cyclicShift_mul_apply, Matrix.one_apply]
  have hiff : (i + 1 : ℕ) % m = (c + 1) % m ↔ i = c := by
    constructor
    · intro h
      have h' : (i : ℕ) ≡ c [MOD m] := Nat.ModEq.add_right_cancel' 1 h
      have h'' : (i : ℕ) = c := by
        rw [Nat.ModEq, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt c.2] at h'
        exact h'
      exact Fin.ext h''
    · rintro rfl; rfl
  by_cases hic : i = c
  · simp [cyclicShift, hic]
  · have h : ¬ ((i + 1 : ℕ) % m = (c + 1) % m) := fun e => hic (hiff.1 e)
    simp [cyclicShift, hic, h]

/-- arXiv 1906.09940, (2.16), boundary treatment (unspecified in the paper): The periodic shift is a
grid shift. -/
theorem isShift_cyclicShift (m : ℕ) : IsShift (cyclicShift m) := by
  have h1 := cyclicShift_mul_transpose m
  have h2 : (cyclicShift m)ᵀ * cyclicShift m = 1 := mul_eq_one_comm.1 h1
  constructor
  · rw [h2, sub_self]; exact Matrix.PosSemidef.zero
  · rw [h1, sub_self]; exact Matrix.PosSemidef.zero

end Streaming

/-! ### The matrix absolute value and upwinding -/

section AbsValue

variable {m n : ℕ} {C : 𝐌[n, n]}

/-- The orthogonal eigenvector matrix `Q` of a symmetric `C`. -/
noncomputable abbrev eigQ (hC : C.IsHermitian) : 𝐌[n, n] := hC.eigenvectorUnitary

private lemma eigQ_transpose_mul (hC : C.IsHermitian) : (eigQ hC)ᵀ * eigQ hC = 1 := by
  have h := Unitary.coe_star_mul_self hC.eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

private lemma eigQ_mul_transpose (hC : C.IsHermitian) : eigQ hC * (eigQ hC)ᵀ = 1 :=
  mul_eq_one_comm.1 (eigQ_transpose_mul hC)

private lemma spectral (hC : C.IsHermitian) :
    C = eigQ hC * Matrix.diagonal hC.eigenvalues * (eigQ hC)ᵀ := by
  have h := hC.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  simpa using h

private lemma conj_posSemidef (hC : C.IsHermitian) {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) :
    (eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ).PosSemidef := by
  have h := (Matrix.posSemidef_diagonal_iff.2 hd).mul_mul_conjTranspose_same (eigQ hC)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The matrix absolute value `|C| = Q |Λ| Qᵀ` of a symmetric matrix `C = Q Λ Qᵀ`: the stabilisation
matrix `Σ` of arXiv 1906.09940, (2.16).  In the eigenbasis it is "a diagonal matrix with the
singular values of `C`" (`transpose_mul_absSymm_mul`). -/
noncomputable def absSymm (hC : C.IsHermitian) : 𝐌[n, n] :=
  eigQ hC * Matrix.diagonal (fun i => |hC.eigenvalues i|) * (eigQ hC)ᵀ

/-- arXiv 1906.09940, (2.16): In the eigenbasis of `C`, `|C|` is the diagonal matrix of the singular
values `|λ_i|` of `C`. -/
theorem transpose_mul_absSymm_mul (hC : C.IsHermitian) :
    (eigQ hC)ᵀ * absSymm hC * eigQ hC = Matrix.diagonal fun i => |hC.eigenvalues i| := by
  rw [absSymm, show (eigQ hC)ᵀ * (eigQ hC * Matrix.diagonal (fun i => |hC.eigenvalues i|) *
      (eigQ hC)ᵀ) * eigQ hC = ((eigQ hC)ᵀ * eigQ hC) * Matrix.diagonal
        (fun i => |hC.eigenvalues i|) * ((eigQ hC)ᵀ * eigQ hC) by
      simp only [Matrix.mul_assoc], eigQ_transpose_mul]
  simp

private lemma conj_add (hC : C.IsHermitian) (d e : Fin n → ℝ) :
    eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ + eigQ hC * Matrix.diagonal e * (eigQ hC)ᵀ =
      eigQ hC * Matrix.diagonal (d + e) * (eigQ hC)ᵀ := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
  rfl

private lemma conj_sub (hC : C.IsHermitian) (d e : Fin n → ℝ) :
    eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ - eigQ hC * Matrix.diagonal e * (eigQ hC)ᵀ =
      eigQ hC * Matrix.diagonal (d - e) * (eigQ hC)ᵀ := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  rfl

private lemma conj_mul (hC : C.IsHermitian) (d e : Fin n → ℝ) :
    (eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ) * (eigQ hC * Matrix.diagonal e * (eigQ hC)ᵀ) =
      eigQ hC * Matrix.diagonal (d * e) * (eigQ hC)ᵀ := by
  rw [show (eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ) * (eigQ hC * Matrix.diagonal e * (eigQ hC)ᵀ)
      = eigQ hC * Matrix.diagonal d * ((eigQ hC)ᵀ * eigQ hC) * Matrix.diagonal e * (eigQ hC)ᵀ by
    simp only [Matrix.mul_assoc], eigQ_transpose_mul, Matrix.mul_one, Matrix.mul_assoc (eigQ hC),
    Matrix.diagonal_mul_diagonal]
  rfl

/-- arXiv 1906.09940, (2.16): `|C|² = C²`. -/
theorem absSymm_mul_self (hC : C.IsHermitian) : absSymm hC * absSymm hC = C * C := by
  have hs : C * C = (eigQ hC * Matrix.diagonal hC.eigenvalues * (eigQ hC)ᵀ) *
      (eigQ hC * Matrix.diagonal hC.eigenvalues * (eigQ hC)ᵀ) :=
    congrArg₂ (· * ·) (spectral hC) (spectral hC)
  rw [hs, absSymm, conj_mul, conj_mul]
  congr 3
  ext i
  simp [abs_mul_abs_self]

private lemma absSymm_sub_self (hC : C.IsHermitian) :
    (absSymm hC - C).PosSemidef := by
  have e : absSymm hC - C = eigQ hC * Matrix.diagonal
      ((fun i => |hC.eigenvalues i|) - hC.eigenvalues) * (eigQ hC)ᵀ := by
    have h := congrArg (fun X => absSymm hC - X) (spectral hC)
    rw [h, absSymm, conj_sub]
  rw [e]
  refine conj_posSemidef hC fun i => ?_
  have := le_abs_self (hC.eigenvalues i)
  simp only [Pi.sub_apply]
  linarith

private lemma absSymm_add_self (hC : C.IsHermitian) :
    (absSymm hC + C).PosSemidef := by
  have e : absSymm hC + C = eigQ hC * Matrix.diagonal
      ((fun i => |hC.eigenvalues i|) + hC.eigenvalues) * (eigQ hC)ᵀ := by
    have h := congrArg (fun X => absSymm hC + X) (spectral hC)
    rw [h, absSymm, conj_add]
  rw [e]
  refine conj_posSemidef hC fun i => ?_
  have := neg_abs_le (hC.eigenvalues i)
  simp only [Pi.add_apply]
  linarith

private lemma smul_one_eq_conj (hC : C.IsHermitian) (a : ℝ) :
    a • (1 : 𝐌[n, n]) = eigQ hC * Matrix.diagonal (fun _ => a) * (eigQ hC)ᵀ := by
  have : Matrix.diagonal (fun _ : Fin n => a) = a • (1 : 𝐌[n, n]) := by
    ext p q
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, eigQ_mul_transpose]

/-- The eigenvalues of `C` are bounded by `a` if `-a ≤ C ≤ a`. -/
private lemma abs_eigenvalue_le (hC : C.IsHermitian) {a : ℝ}
    (h₁ : (a • (1 : 𝐌[n, n]) - C).PosSemidef) (h₂ : (a • (1 : 𝐌[n, n]) + C).PosSemidef)
    (i : Fin n) : |hC.eigenvalues i| ≤ a := by
  have key : ∀ d : Fin n → ℝ, (eigQ hC)ᵀ * (eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ) * eigQ hC =
      Matrix.diagonal d := by
    intro d
    rw [show (eigQ hC)ᵀ * (eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ) * eigQ hC =
        ((eigQ hC)ᵀ * eigQ hC) * Matrix.diagonal d * ((eigQ hC)ᵀ * eigQ hC) by
      simp only [Matrix.mul_assoc], eigQ_transpose_mul]
    simp
  have hs := spectral hC
  have hone := smul_one_eq_conj hC a
  have d₁ : (a • (1 : 𝐌[n, n]) - C) =
      eigQ hC * Matrix.diagonal ((fun _ => a) - hC.eigenvalues) * (eigQ hC)ᵀ := by
    rw [← conj_sub, ← hs, ← hone]
  have d₂ : (a • (1 : 𝐌[n, n]) + C) =
      eigQ hC * Matrix.diagonal ((fun _ => a) + hC.eigenvalues) * (eigQ hC)ᵀ := by
    rw [← conj_add, ← hs, ← hone]
  have e₁ := (h₁.conjTranspose_mul_mul_same (eigQ hC)).diag_nonneg (i := i)
  have e₂ := (h₂.conjTranspose_mul_mul_same (eigQ hC)).diag_nonneg (i := i)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, d₁, key] at e₁
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, d₂, key] at e₂
  simp only [Matrix.diagonal_apply_eq, Pi.sub_apply, Pi.add_apply] at e₁ e₂
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- `-a ≤ C ≤ a` if all eigenvalues of `C` are bounded by `a`. -/
private lemma smul_one_add_sub_of_eigenvalue (hC : C.IsHermitian) {a : ℝ}
    (h : ∀ i, |hC.eigenvalues i| ≤ a) :
    (a • (1 : 𝐌[n, n]) - C).PosSemidef ∧ (a • (1 : 𝐌[n, n]) + C).PosSemidef := by
  have hs := spectral hC
  have hone := smul_one_eq_conj hC a
  have d₁ : (a • (1 : 𝐌[n, n]) - C) =
      eigQ hC * Matrix.diagonal ((fun _ => a) - hC.eigenvalues) * (eigQ hC)ᵀ := by
    rw [← conj_sub, ← hs, ← hone]
  have d₂ : (a • (1 : 𝐌[n, n]) + C) =
      eigQ hC * Matrix.diagonal ((fun _ => a) + hC.eigenvalues) * (eigQ hC)ᵀ := by
    rw [← conj_add, ← hs, ← hone]
  refine ⟨?_, ?_⟩
  · rw [d₁]
    refine conj_posSemidef hC fun i => ?_
    have := abs_le.1 (h i)
    simp only [Pi.sub_apply]
    linarith [this.2]
  · rw [d₂]
    refine conj_posSemidef hC fun i => ?_
    have := abs_le.1 (h i)
    simp only [Pi.add_apply]
    linarith [this.1]

/-- arXiv 1906.09940, (2.16): `|C|` is a stabilisation of `C`, with bound `a` for `-a ≤ C ≤ a`. -/
theorem isStabilisation_absSymm (hC : C.IsHermitian) {a : ℝ}
    (h₁ : (a • (1 : 𝐌[n, n]) - C).PosSemidef) (h₂ : (a • (1 : 𝐌[n, n]) + C).PosSemidef) :
    IsStabilisation C (absSymm hC) a := by
  refine ⟨absSymm_sub_self hC, absSymm_add_self hC, ?_⟩
  have hone := smul_one_eq_conj hC a
  rw [hone, absSymm, conj_sub]
  exact conj_posSemidef hC fun i => by
    have := abs_eigenvalue_le hC h₁ h₂ i
    simp only [Pi.sub_apply]
    linarith

/-- The positive part `C⁺ = ½ (C + |C|)` of the advection matrix. -/
noncomputable def upPos (hC : C.IsHermitian) : 𝐌[n, n] := (1 / 2 : ℝ) • (C + absSymm hC)

/-- The negative part `C⁻ = ½ (C - |C|)` of the advection matrix. -/
noncomputable def upNeg (hC : C.IsHermitian) : 𝐌[n, n] := (1 / 2 : ℝ) • (C - absSymm hC)

/-- **Eqs. (2.15)-(2.16) of arXiv 1906.09940 are standard upwinding**: with `Σ = |C|` the interface
flux of (2.16) is the characteristic upwind flux `F_{i+½} = K_i C⁺ + K_{i+1} C⁻`. -/
theorem faceFlux_upwind (hC : C.IsHermitian) (Kl Kr : 𝐌[m, n]) :
    faceFlux C (absSymm hC) Kl Kr = Kl * upPos hC + Kr * upNeg hC := by
  simp only [faceFlux, upPos, upNeg, Matrix.mul_smul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_add, Matrix.mul_sub]
  module

/-- arXiv 1906.09940, (2.16): `C⁺ ≥ 0`: right-going characteristics are taken from the left state.
-/
theorem upPos_posSemidef (hC : C.IsHermitian) : (upPos hC).PosSemidef := by
  have e : upPos hC = (1 / 2 : ℝ) • (absSymm hC + C) := by rw [upPos, add_comm]
  rw [e]
  exact (absSymm_add_self hC).smul (by norm_num)

/-- arXiv 1906.09940, (2.16): `C⁻ ≤ 0`: left-going characteristics are taken from the right state.
-/
theorem neg_upNeg_posSemidef (hC : C.IsHermitian) : (-upNeg hC).PosSemidef := by
  have e : -upNeg hC = (1 / 2 : ℝ) • (absSymm hC - C) := by
    rw [upNeg, ← smul_neg, neg_sub]
  rw [e]
  exact (absSymm_sub_self hC).smul (by norm_num)

private lemma conj_smul (hC : C.IsHermitian) (a : ℝ) (d : Fin n → ℝ) :
    a • (eigQ hC * Matrix.diagonal d * (eigQ hC)ᵀ) =
      eigQ hC * Matrix.diagonal (fun i => a * d i) * (eigQ hC)ᵀ := by
  have e : Matrix.diagonal (fun i => a * d i) = a • Matrix.diagonal d := by
    ext p q
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [hpq]
  rw [e, Matrix.mul_smul, Matrix.smul_mul]

/-- arXiv 1906.09940, (2.16): In the eigenbasis of `C`, `C⁺` keeps the positive eigenvalues:
upwinding acts on each characteristic variable. -/
theorem upPos_eq (hC : C.IsHermitian) :
    upPos hC = eigQ hC * Matrix.diagonal (fun i => max (hC.eigenvalues i) 0) * (eigQ hC)ᵀ := by
  have h := congrArg (fun X => (1 / 2 : ℝ) • (X + absSymm hC)) (spectral hC)
  rw [upPos, h, absSymm, conj_add, conj_smul]
  congr 3
  ext i
  simp only [Pi.add_apply]
  rcases le_total 0 (hC.eigenvalues i) with hl | hl
  · rw [abs_of_nonneg hl, max_eq_left hl]; ring
  · rw [abs_of_nonpos hl, max_eq_right hl]; ring

/-- arXiv 1906.09940, (2.16): In the eigenbasis of `C`, `C⁻` keeps the negative eigenvalues. -/
theorem upNeg_eq (hC : C.IsHermitian) :
    upNeg hC = eigQ hC * Matrix.diagonal (fun i => min (hC.eigenvalues i) 0) * (eigQ hC)ᵀ := by
  have h := congrArg (fun X => (1 / 2 : ℝ) • (X - absSymm hC)) (spectral hC)
  rw [upNeg, h, absSymm, conj_sub, conj_smul]
  congr 3
  ext i
  simp only [Pi.sub_apply]
  rcases le_total 0 (hC.eigenvalues i) with hl | hl
  · rw [abs_of_nonneg hl, min_eq_right hl]; ring
  · rw [abs_of_nonpos hl, min_eq_left hl]; ring

/-- arXiv 1906.09940, (2.16): `C⁺ + C⁻ = C`, `C⁺ - C⁻ = |C|`, `C⁺ C⁻ = 0`: the splitting into
characteristic directions. -/
theorem upPos_add_upNeg (hC : C.IsHermitian) :
    upPos hC + upNeg hC = C ∧ upPos hC - upNeg hC = absSymm hC ∧ upPos hC * upNeg hC = 0 := by
  refine ⟨by simp only [upPos, upNeg]; module, by simp only [upPos, upNeg]; module, ?_⟩
  rw [upPos_eq, upNeg_eq, conj_mul]
  have : ((fun i => max (hC.eigenvalues i) 0) * fun i => min (hC.eigenvalues i) 0) = 0 := by
    ext i
    simp only [Pi.mul_apply, Pi.zero_apply]
    rcases le_total 0 (hC.eigenvalues i) with hl | hl
    · rw [min_eq_right hl, mul_zero]
    · rw [max_eq_right hl, zero_mul]
  rw [this]
  simp

end AbsValue

/-! ### The discrete transport equation -/

section Transport

open scoped LeanDLRA.Frobenius

variable {m n r : ℕ}

/-- arXiv 1906.09940, Sec. 2.1: `C` is symmetric, as a Hermitian matrix. -/
theorem muMatrix_isHermitian (n : ℕ) : (muMatrix n).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, muMatrix_transpose]

private lemma smul_one_add_muMatrix {a : ℝ} (ha : 1 ≤ a) {s : ℝ} (hs : |s| ≤ 1) :
    (a • (1 : 𝐌[n, n]) + s • muMatrix n).PosSemidef := by
  have ha0 : a ≠ 0 := by linarith
  have hapos : 0 < a := by linarith
  have e : a • (1 : 𝐌[n, n]) + s • muMatrix n = a • (1 + (s / a) • muMatrix n) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ ha0]
  have hs' : |s / a| ≤ 1 := by
    rw [abs_div, abs_of_pos hapos, div_le_one hapos]
    linarith
  rw [e]
  exact (one_add_smul_muMatrix_posSemidef n hs').smul hapos.le

/-- The Lax-Friedrichs stabilisation `D = α 1`, `α ≥ 1` (arXiv 1906.09940, after (2.16)) is a
stabilisation of `C`. -/
theorem isStabilisation_laxFriedrichs {α : ℝ} (hα : 1 ≤ α) :
    IsStabilisation (muMatrix n) (α • 1) α := by
  refine ⟨?_, ?_, ?_⟩
  · have h := smul_one_add_muMatrix (n := n) hα (s := -1) (by simp)
    simpa [sub_eq_add_neg] using h
  · have h := smul_one_add_muMatrix (n := n) hα (s := 1) (by simp)
    simpa using h
  · rw [sub_self]
    exact Matrix.PosSemidef.zero

/-- The upwind stabilisation `Σ = |C|` of arXiv 1906.09940, (2.16), is a stabilisation of `C` with
bound `1`: all characteristic speeds are at most the particle speed. -/
theorem isStabilisation_absSymm_muMatrix (n : ℕ) :
    IsStabilisation (muMatrix n) (absSymm (muMatrix_isHermitian n)) 1 := by
  refine isStabilisation_absSymm _ ?_ ?_
  · have h := smul_one_add_muMatrix (n := n) le_rfl (s := -1) (by simp)
    simpa [sub_eq_add_neg] using h
  · have h := smul_one_add_muMatrix (n := n) le_rfl (s := 1) (by simp)
    simpa using h

/-- The P_N recursion: in the coefficients, multiplication by `C` is the standard three-term
coupling of neighbouring Legendre moments (arXiv 1906.09940: (2.8) "resembles the standard P_N
equations"). -/
theorem mul_muMatrix_apply (Y : 𝐌[m, n]) (k : Fin m) (l : Fin n) :
    (Y * muMatrix n) k l =
      (if h : 1 ≤ (l : ℕ) then Y k ⟨l - 1, by omega⟩ * muOff (l - 1) else 0) +
        (if h : (l : ℕ) + 1 < n then Y k ⟨l + 1, h⟩ * muOff l else 0) := by
  have e : ∀ j : Fin n, Y k j * muMatrix n j l =
      (if (l : ℕ) = j + 1 then Y k j * muOff j else 0) +
        (if (j : ℕ) = l + 1 then Y k j * muOff l else 0) := by
    intro j
    rw [muMatrix_apply]
    split_ifs with h1 h2 h3 <;> first | omega | ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single (⟨(l : ℕ) - 1, by omega⟩ : Fin n)]
      · have : (l : ℕ) = l - 1 + 1 := by omega
        simp [← this]
      · intro j _ hj
        have : (l : ℕ) ≠ j + 1 := fun e => hj (Fin.ext (by simp; omega))
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : (l : ℕ) ≠ j + 1 := fun e => h (by omega)
      simp [this]
  · split_ifs with h
    · rw [Finset.sum_eq_single (⟨(l : ℕ) + 1, h⟩ : Fin n)]
      · simp
      · intro j _ hj
        have : (j : ℕ) ≠ l + 1 := fun e => hj (Fin.ext e)
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : (j : ℕ) ≠ l + 1 := fun e => h (e ▸ j.2)
      simp [this]

/-- The Lax-Friedrichs replacement of arXiv 1906.09940 after (2.16): for orthonormal `V`, the
reduced stabilisation of `Σ = α 1` is the constant times the identity `α 1`, as stated there. -/
theorem laxFriedrichs_reduced (α : ℝ) {V : 𝐌[n, r]} (hV : Vᵀ * V = 1) :
    Vᵀ * (α • (1 : 𝐌[n, n])) * V = α • 1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hV]

variable [NeZero n]

/-- The projector `e₀ e₀ᵀ` onto the isotropic mode `P₀` in the Legendre coefficients. -/
def isoProj (n : ℕ) [NeZero n] : 𝐌[n, n] := Matrix.diagonal fun l => if l = 0 then 1 else 0

/-- The isotropic source of (1.1) in the coefficients: `½ S` has the Legendre coefficient
`⟨P_l, ½⟩ = δ_{l0} / √2`; `q_k = ⟨Z_k, S⟩_z` are the cell coefficients of `S`. -/
noncomputable def sourceMat (q : Fin m → ℝ) : 𝐌[m, n] :=
  Matrix.of fun k l => if l = 0 then (√2)⁻¹ * q k else 0

/-- arXiv 1906.09940, (2.8)/(2.9): `(Vᵀ e₀ e₀ᵀ V)_jj' = ½ ⟨W_j⟩_μ ⟨W_j'⟩_μ`, the coefficient of
the scattering term. -/
theorem isoProj_moment (V : 𝐌[n, r]) (j j' : Fin r) :
    (Vᵀ * isoProj n * V) j j' =
      (1 / 2) * (∫ μ in (-1 : ℝ)..1, angularBasis V j μ) *
        ∫ μ in (-1 : ℝ)..1, angularBasis V j' μ := by
  rw [integral_angularBasis, integral_angularBasis, Matrix.mul_apply]
  simp only [isoProj, Matrix.mul_diagonal, Matrix.transpose_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (-(1 / 2 : ℝ) * V 0 j * V 0 j') * h2

/-- arXiv 1906.09940, (2.8): `(Q V)_kj = ½ ⟨W_j⟩_μ q_k`, the coefficient of the source term. -/
theorem sourceMat_moment (q : Fin m → ℝ) (V : 𝐌[n, r]) (k : Fin m) (j : Fin r) :
    ((sourceMat q : 𝐌[m, n]) * V) k j =
      (1 / 2) * (∫ μ in (-1 : ℝ)..1, angularBasis V j μ) * q k := by
  rw [integral_angularBasis, Matrix.mul_apply]
  simp only [sourceMat, Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : √2 ≠ 0 := by positivity
  field_simp
  linear_combination (-(q k) * V 0 j) * h2

/-- A slab-geometry transport problem discretised as in arXiv 1906.09940, Sec. 2.1: `m` cells of
width `Δz` (grid shift `T` for the boundary treatment), `n` normalised Legendre modes,
stabilisation `D` (`Σ` in the paper), cross sections `σs`, `σt` on the cells, and the source
coefficients `q t k = ⟨Z_k, S(·, t)⟩_z`.  We use unit particle speed, `c = 1`. -/
structure TransportProblem (m n : ℕ) where
  Δz : ℝ
  Δz_pos : 0 < Δz
  T : 𝐌[m, m]
  D : 𝐌[n, n]
  σs : Fin m → ℝ
  σt : Fin m → ℝ
  q : ℝ → Fin m → ℝ

namespace TransportProblem

variable (P : TransportProblem m n)

/-- The linear part `Y ↦ -streaming + scattering - absorption` of the right-hand side. -/
noncomputable def op (Y : 𝐌[m, n]) : 𝐌[m, n] :=
  streamOp P.T P.Δz (muMatrix n) P.D Y +
    (Matrix.diagonal P.σs * Y * isoProj n - Matrix.diagonal P.σt * Y)

/-- The right-hand side `R` of (2.4)-(2.6): the discrete transport equation is `Y' = R(t, Y)`, the
full `P_N`-finite-volume scheme (`full_P_N`). -/
noncomputable def field (t : ℝ) (Y : 𝐌[m, n]) : 𝐌[m, n] := P.op Y + sourceMat (P.q t)

/-- **Eq. (2.8) of arXiv 1906.09940, discrete form**: the K-step field for `ψ₁ = K Vᵀ`,
`K' = -(flux difference with Vᵀ C V, Vᵀ Σ V) + σs K (Vᵀ e₀ e₀ᵀ V) - σt K + Q V`.  With
`isoProj_moment`, `sourceMat_moment` the last terms are the paper's
`(σs / 2) ⟨W_j⟩ ⟨W_j'⟩ K_j'`, `σt K_j`, `⟨W_j⟩ S / 2`. -/
theorem kField_eq {V : 𝐌[n, r]} (hV : Vᵀ * V = 1) (t : ℝ) (K : 𝐌[m, r]) :
    MatrixKSL.kField V P.field t K =
      streamOp P.T P.Δz (Vᵀ * muMatrix n * V) (Vᵀ * P.D * V) K +
        (Matrix.diagonal P.σs * K * (Vᵀ * isoProj n * V) - Matrix.diagonal P.σt * K) +
        (sourceMat (P.q t) : 𝐌[m, n]) * V := by
  have h1 : Matrix.diagonal P.σt * (K * Vᵀ) * V = Matrix.diagonal P.σt * K := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hV, Matrix.mul_one]
  simp only [MatrixKSL.kField, field, op, Matrix.add_mul, Matrix.sub_mul, streamOp_galerkin, h1]
  simp only [Matrix.mul_assoc]

/-- **Eq. (2.9) of arXiv 1906.09940, discrete form**: the backward S-step field.
Here `(2 Δz)⁻¹ Uᵀ (T - Tᵀ) U` is the discrete `⟨∂_z X_k X_i⟩_z` of the paper and `Uᵀ diag(σ) U` is
`⟨σ X_k X_i⟩_z` (`integral_pwConst_spatialBasis`).  The paper prints `σt S_ij` and
`⟨X_i⟩_z ⟨W_j⟩_μ / 2`, i.e. the case of constant `σt` and `S = 1`. -/
theorem sField_eq {U : 𝐌[m, r]} {V : 𝐌[n, r]} (hV : Vᵀ * V = 1) (t : ℝ) (S : 𝐌[r, r]) :
    MatrixKSL.sField U V P.field t S =
      (2 * P.Δz)⁻¹ • (Uᵀ * (P.T - P.Tᵀ) * U * S * (Vᵀ * muMatrix n * V) -
          Uᵀ * (P.T + P.Tᵀ - (2 : ℝ) • 1) * U * S * (Vᵀ * P.D * V)) -
        (Uᵀ * Matrix.diagonal P.σs * U * S * (Vᵀ * isoProj n * V) -
          Uᵀ * Matrix.diagonal P.σt * U * S) -
        Uᵀ * (sourceMat (P.q t) : 𝐌[m, n]) * V := by
  have h2 := P.kField_eq hV t (U * S)
  simp only [MatrixKSL.kField] at h2
  simp only [MatrixKSL.sField, Matrix.mul_assoc Uᵀ _ V, h2]
  simp only [streamOp, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
  module

/-- **Eq. (2.10) of arXiv 1906.09940, discrete form**: the L-step field for `ψ₃ = U Lᵀ`, in the
Legendre coefficients of `L_i(μ) = ∑_l L_li P_l(μ)`; `C L` is multiplication of `L_i` by `μ`,
`e₀ e₀ᵀ L` is `½ ⟨L_i⟩_μ`.  (The paper's (2.10) omits the indices `k` of the `σ` terms and the
sums over them.) -/
theorem lField_eq (U : 𝐌[m, r]) (t : ℝ) (L : 𝐌[n, r]) :
    MatrixKSL.lField U P.field t L =
      -(2 * P.Δz)⁻¹ • (muMatrix n * L * (Uᵀ * (P.T - P.Tᵀ) * U)ᵀ -
          P.Dᵀ * L * (Uᵀ * (P.T + P.Tᵀ - (2 : ℝ) • 1) * U)ᵀ) +
        (isoProj n * L * (Uᵀ * Matrix.diagonal P.σs * U)ᵀ -
          L * (Uᵀ * Matrix.diagonal P.σt * U)ᵀ) +
        (sourceMat (P.q t) : 𝐌[m, n])ᵀ * U := by
  have hC := muMatrix_transpose n
  have hE : (isoProj n)ᵀ = isoProj n := by simp [isoProj]
  simp only [MatrixKSL.lField, field, op, streamOp, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, hC, hE,
    Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.diagonal_transpose, Matrix.mul_sub,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]

/-- The K-step of full rank is the full scheme: for `V = 1`, (2.8) is the `P_N` system
`Y' = R(t, Y)` (arXiv 1906.09940: "Equation (2.8) resembles the standard P_N equations"). -/
theorem full_P_N (t : ℝ) (Y : 𝐌[m, n]) : MatrixKSL.kField 1 P.field t Y = P.field t Y := by
  simp [MatrixKSL.kField]

/-- **Eqs. (2.4)-(2.6) of arXiv 1906.09940**: the factor equations (2.8)-(2.10) give the projected
evolutions `ψ₁' = P_W R ψ₁`, `ψ₂' = -P_X P_W R ψ₂`, `ψ₃' = P_X R ψ₃`, chained by their initial
values, and each trajectory stays of rank at most `r`. -/
theorem isStep_lift {t₀ t₁ : ℝ} {U₀ U₁ : 𝐌[m, r]} {S₀ Ŝ₁ : 𝐌[r, r]} {V₀ : 𝐌[n, r]}
    {K : ℝ → 𝐌[m, r]} {S : ℝ → 𝐌[r, r]} {Lf : ℝ → 𝐌[n, r]}
    (hs : MatrixKSL.IsStep P.field t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) :
    ODESolution (fun t x => rightProj V₀ (P.field t x)) (fun t => K t * V₀ᵀ) t₀ t₁ ∧
    ODESolution (fun t x => -leftProj U₁ (rightProj V₀ (P.field t x)))
      (fun t => U₁ * S t * V₀ᵀ) t₀ t₁ ∧
    ODESolution (fun t x => leftProj U₁ (P.field t x)) (fun t => U₁ * (Lf t)ᵀ) t₀ t₁ ∧
    K t₀ * V₀ᵀ = U₀ * S₀ * V₀ᵀ ∧ U₁ * S t₀ * V₀ᵀ = K t₁ * V₀ᵀ ∧
    U₁ * (Lf t₀)ᵀ = U₁ * S t₁ * V₀ᵀ ∧
    ∀ t, (K t * V₀ᵀ).rank ≤ r ∧ (U₁ * S t * V₀ᵀ).rank ≤ r ∧ (U₁ * (Lf t)ᵀ).rank ≤ r := by
  refine ⟨MatrixKSL.odeSolution_kField hs.kSol, MatrixKSL.odeSolution_sField hs.sSol,
    MatrixKSL.odeSolution_lField hs.lSol, by rw [hs.kStart], by rw [hs.sStart, hs.kQR],
    ?_, fun t => ⟨?_, ?_, ?_⟩⟩
  · rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  · simpa using (Matrix.rank_mul_le_right (K t) V₀ᵀ).trans (Matrix.rank_le_height _)
  · simpa using (Matrix.rank_mul_le_right (U₁ * S t) V₀ᵀ).trans (Matrix.rank_le_height _)
  · simpa using (Matrix.rank_mul_le_left U₁ (Lf t)ᵀ).trans (Matrix.rank_le_width _)

private lemma coll_apply (σs σt : Fin m → ℝ) (Y : 𝐌[m, n]) (k : Fin m) (l : Fin n) :
    (Matrix.diagonal σs * Y * isoProj n - Matrix.diagonal σt * Y) k l =
      ((if l = 0 then σs k else 0) - σt k) * Y k l := by
  simp only [isoProj, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> ring

/-- Physical and numerical assumptions on a transport problem: `T` is a grid shift, `D` is a
stabilisation of `C` with bound `a`, and `0 ≤ σs ≤ σt ≤ b`. -/
structure IsAdmissible (a b : ℝ) : Prop where
  shift : IsShift P.T
  stab : IsStabilisation (muMatrix n) P.D a
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  σs_nonneg : ∀ k, 0 ≤ P.σs k
  σs_le : ∀ k, P.σs k ≤ P.σt k
  σt_le : ∀ k, P.σt k ≤ b

variable {P}

/-- **`L²`-dissipativity of the discrete transport operator** (not in arXiv 1906.09940): for
`0 ≤ σs ≤ σt`, `⟪op Y, Y⟫ ≤ 0`.  Streaming only contributes the stabilisation. -/
theorem inner_op_nonpos {a b : ℝ} (hP : P.IsAdmissible a b) (Y : 𝐌[m, n]) : ⟪P.op Y, Y⟫ ≤ 0 := by
  have h1 := inner_streamOp_nonpos hP.shift P.Δz_pos (muMatrix_transpose n) hP.stab.posSemidef Y
  have h2 : ⟪Matrix.diagonal P.σs * Y * isoProj n - Matrix.diagonal P.σt * Y, Y⟫ ≤ 0 := by
    rw [Frobenius.inner_def]
    refine Finset.sum_nonpos fun k _ => Finset.sum_nonpos fun l _ => ?_
    rw [coll_apply]
    have hs := hP.σs_nonneg k
    have hl := hP.σs_le k
    have hc : (if l = 0 then P.σs k else 0) - P.σt k ≤ 0 := by
      split_ifs <;> linarith
    nlinarith [mul_self_nonneg (Y k l)]
  rw [op, inner_add_left]
  linarith

/-- **`L²`-stability of the full scheme under a CFL condition** (not in arXiv 1906.09940): if
`h (a / Δz + b) ≤ 1`, the explicit Euler step of the source-free scheme is norm-nonincreasing. -/
theorem norm_euler_op_le {a b h : ℝ} (hP : P.IsAdmissible a b) (hh : 0 ≤ h)
    (hcfl : h * (a / P.Δz + b) ≤ 1) (Y : 𝐌[m, n]) : ‖Y + h • P.op Y‖ ≤ ‖Y‖ := by
  have hΔ := P.Δz_pos
  have ha := hP.a_nonneg
  have hb := hP.b_nonneg
  have h1 := norm_cfl_streamOp_le hP.shift hΔ hh ha hP.stab Y
  set Z : 𝐌[m, n] := (h * b) • Y +
    h • (Matrix.diagonal P.σs * Y * isoProj n - Matrix.diagonal P.σt * Y) with hZ
  have h2 : ‖Z‖ ≤ h * b * ‖Y‖ := by
    have hcoef : 0 ≤ h * b := by positivity
    have hent : ∀ k l, Z k l ^ 2 ≤ (h * b) ^ 2 * Y k l ^ 2 := by
      intro k l
      have e : Z k l = (h * b + h * ((if l = 0 then P.σs k else 0) - P.σt k)) * Y k l := by
        simp only [hZ, Matrix.add_apply, Matrix.smul_apply, coll_apply, smul_eq_mul]
        ring
      have hs := hP.σs_nonneg k
      have hl := hP.σs_le k
      have ht := hP.σt_le k
      have h0 : 0 ≤ h * b + h * ((if l = 0 then P.σs k else 0) - P.σt k) := by
        have : 0 ≤ b + ((if l = 0 then P.σs k else 0) - P.σt k) := by
          split_ifs <;> linarith
        nlinarith
      have h3 : h * b + h * ((if l = 0 then P.σs k else 0) - P.σt k) ≤ h * b := by
        have : (if l = 0 then P.σs k else 0) - P.σt k ≤ 0 := by
          split_ifs <;> linarith
        nlinarith
      rw [e, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h3 2) (sq_nonneg _)
    have hsq : ‖Z‖ ^ 2 ≤ (h * b * ‖Y‖) ^ 2 := by
      rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => hent k l
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have e : Y + h • P.op Y = (1 - (h / P.Δz * a + h * b)) • Y +
      ((h / P.Δz * a) • Y + h • streamOp P.T P.Δz (muMatrix n) P.D Y) + Z := by
    simp only [op, hZ]
    module
  have hc0 : 0 ≤ 1 - (h / P.Δz * a + h * b) := by
    have : h / P.Δz * a + h * b = h * (a / P.Δz + b) := by
      field_simp
    linarith
  rw [e]
  calc _ ≤ ‖(1 - (h / P.Δz * a + h * b)) • Y‖ +
        ‖(h / P.Δz * a) • Y + h • streamOp P.T P.Δz (muMatrix n) P.D Y‖ + ‖Z‖ :=
        norm_add₃_le
    _ ≤ (1 - (h / P.Δz * a + h * b)) * ‖Y‖ + h / P.Δz * a * ‖Y‖ + h * b * ‖Y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hc0]
        gcongr
    _ = ‖Y‖ := by ring

/-- arXiv 1906.09940, (2.16), not in the paper: **The stability of the full upwind scheme transfers
to the low-rank BUG step** (the note in the header; `LeanDLRA.bug_euler_norm_le`): under the CFL
condition of `norm_euler_op_le`, for any orthonormal `U`, `V` the explicit Euler BUG step of the
source-free scheme is norm-nonincreasing. -/
theorem bug_euler_op_norm_le {a b h : ℝ} (hP : P.IsAdmissible a b) (hh : 0 ≤ h)
    (hcfl : h * (a / P.Δz + b) ≤ 1) {U : 𝐌[m, r]} {V : 𝐌[n, r]} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (u₀ : 𝐌[m, n]) :
    ‖leftProj U (rightProj V (eulerStep P.op h (leftProj U (rightProj V u₀))))‖ ≤ ‖u₀‖ := by
  have h1 := LeanDLRA.bug_euler_norm_le (F := P.op) (h := h) (γ := 1) (isOrthProj_leftProj hU)
    (isOrthProj_rightProj hV) (leftProj_rightProj_comm U V) zero_le_one
    (fun x _ => by simpa [eulerStep] using norm_euler_op_le hP hh hcfl x) u₀
  simpa using h1

/-- arXiv 1906.09940, (2.16), not in the paper: With a source, the full Euler step grows at most by
the source: under the CFL condition of `norm_euler_op_le`, `‖Y + h R(t, Y)‖ ≤ ‖Y‖ + h ‖Q(t)‖`. -/
theorem norm_euler_field_le {a b h : ℝ} (hP : P.IsAdmissible a b) (hh : 0 ≤ h)
    (hcfl : h * (a / P.Δz + b) ≤ 1) (t : ℝ) (Y : 𝐌[m, n]) :
    ‖Y + h • P.field t Y‖ ≤ ‖Y‖ + h * ‖(sourceMat (P.q t) : 𝐌[m, n])‖ := by
  have e : Y + h • P.field t Y = (Y + h • P.op Y) + h • (sourceMat (P.q t) : 𝐌[m, n]) := by
    rw [field, smul_add, add_assoc]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hh]
  gcongr
  exact norm_euler_op_le hP hh hcfl Y

/-- arXiv 1906.09940, (2.16), not in the paper: The BUG step with exact Galerkin S-step is
`L²`-stable for the transport operator without any step size restriction
(`LeanDLRA.bug_norm_le_of_dissipative`). -/
theorem bug_op_norm_le {a b : ℝ} (hP : P.IsAdmissible a b) {U : 𝐌[m, r]} {V : 𝐌[n, r]}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {YS : ℝ → 𝐌[m, n]} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hYS : ODESolution (fun _ x => leftProj U (rightProj V (P.op x))) YS t₀ t₁) {Y₀ : 𝐌[m, n]}
    (h0 : YS t₀ = leftProj U (rightProj V Y₀)) : ‖YS t₁‖ ≤ ‖Y₀‖ :=
  bug_norm_le_of_dissipative (F := fun _ x => P.op x) (isOrthProj_leftProj hU)
    (isOrthProj_rightProj hV) (leftProj_rightProj_comm U V) ht hYS h0
    fun _ x _ => inner_op_nonpos hP x

end TransportProblem

end Transport

/-! ### Explicit Euler KSL is not `L²`-stable for the upwind scheme -/

section KSLInstability

private lemma kslEulerStep_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P₁ Q₀ : E →L[ℝ] E} {F : E → E} {c h : ℝ} {x : E} (h₁ : P₁ x = x) (h₀ : Q₀ x = x)
    (hF : ∀ α : ℝ, F (α • x) = (-(c * α)) • x) :
    kslEulerStep P₁ Q₀ F h x = ((1 - h * c) ^ 2 * (1 + h * c)) • x := by
  have hP : ∀ α : ℝ, P₁ (α • x) = α • x := fun α => by rw [map_smul, h₁]
  have hQ : ∀ α : ℝ, Q₀ (α • x) = α • x := fun α => by rw [map_smul, h₀]
  have hK : kslK Q₀ F h x = (1 - h * c) • x := by
    have h1 := hF 1
    rw [one_smul] at h1
    rw [kslK, h1, hQ]
    module
  have hS : kslS P₁ Q₀ F h ((1 - h * c) • x) = ((1 - h * c) * (1 + h * c)) • x := by
    rw [kslS, hP, hF, hQ, hP]
    module
  have hL : ∀ α : ℝ, kslL P₁ F h (α • x) = (α * (1 - h * c)) • x := by
    intro α
    rw [kslL, hF, hP]
    module
  rw [kslEulerStep, hK, hS, hL]
  congr 1
  ring

open scoped LeanDLRA.Frobenius

variable {n : ℕ}

/-- The normalised odd-even mode `(-1)^i / √(2 p)` on a mesh of `2 p` cells. -/
noncomputable def oddEven (p : ℕ) : 𝐌[2 * p, 1] :=
  Matrix.of fun i _ => (√(2 * (p : ℝ)))⁻¹ * (-1) ^ (i : ℕ)

private lemma neg_one_pow_mod (p x : ℕ) : (-1 : ℝ) ^ (x % (2 * p)) = (-1) ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x (2 * p), pow_add, mul_assoc, pow_mul, pow_mul]
  simp

/-- The odd-even mode is a unit vector. -/
lemma oddEven_orthonormal {p : ℕ} (hp : 0 < p) : (oddEven p)ᵀ * oddEven p = 1 := by
  ext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha hb
  have h2 : (2 * (p : ℝ)) ≠ 0 := by positivity
  have hs : √(2 * (p : ℝ)) * √(2 * (p : ℝ)) = 2 * (p : ℝ) := Real.mul_self_sqrt (by positivity)
  have hs0 : √(2 * (p : ℝ)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hs
    exact h2 hs.symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, oddEven, Matrix.of_apply,
    Matrix.one_apply_eq]
  have e : ∀ i : Fin (2 * p), (√(2 * (p : ℝ)))⁻¹ * (-1) ^ (i : ℕ) *
      ((√(2 * (p : ℝ)))⁻¹ * (-1) ^ (i : ℕ)) = (2 * (p : ℝ))⁻¹ := by
    intro i
    have h1 : ((-1 : ℝ) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]; simp
    field_simp
    nlinarith
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- The periodic shift flips the sign of the odd-even mode. -/
lemma cyclicShift_mul_oddEven (p : ℕ) : cyclicShift (2 * p) * oddEven p = -oddEven p := by
  ext i c
  rw [cyclicShift_mul_apply]
  simp only [oddEven, Matrix.of_apply, Matrix.neg_apply, neg_one_pow_mod]
  rw [pow_succ]
  ring

/-- The inverse periodic shift flips the sign of the odd-even mode. -/
lemma cyclicShift_transpose_mul_oddEven (p : ℕ) :
    (cyclicShift (2 * p))ᵀ * oddEven p = -oddEven p := by
  have h1 : (cyclicShift (2 * p))ᵀ * cyclicShift (2 * p) = 1 :=
    mul_eq_one_comm.1 (cyclicShift_mul_transpose (2 * p))
  have h2 := congrArg (fun X => (cyclicShift (2 * p))ᵀ * X) (cyclicShift_mul_oddEven p)
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_neg] at h2
  exact neg_eq_iff_eq_neg.1 h2.symm

variable [NeZero n]

/-- Pure streaming on a periodic mesh of `2 p` cells: no collisions, no source. -/
noncomputable def streamingProblem (p : ℕ) {Δz : ℝ} (hΔ : 0 < Δz) (D : 𝐌[n, n]) :
    TransportProblem (2 * p) n where
  Δz := Δz
  Δz_pos := hΔ
  T := cyclicShift (2 * p)
  D := D
  σs := 0
  σt := 0
  q := fun _ _ => 0

private lemma sourceMat_zero {m : ℕ} : (sourceMat (0 : Fin m → ℝ) : 𝐌[m, n]) = 0 := by
  ext k l
  simp [sourceMat]

/-- arXiv 1906.09940, Sec. 2.1 and (2.16), not in the paper: The odd-even mode is an eigenfunction
of the stabilised streaming operator: only the stabilisation sees it, `R (α U Vᵀ) = -(2 a / Δz) α U
Vᵀ` for `D V = a V`. -/
theorem streamingProblem_field_mode (p : ℕ) {Δz : ℝ} (hΔ : 0 < Δz) {D : 𝐌[n, n]} (hDs : Dᵀ = D)
    {a : ℝ} {V : 𝐌[n, 1]} (hDV : D * V = a • V) (t α : ℝ) :
    (streamingProblem p hΔ D).field t (α • (oddEven p * Vᵀ)) =
      (-(2 * a / Δz * α)) • (oddEven p * Vᵀ) := by
  have hU := cyclicShift_mul_oddEven p
  have hU' := cyclicShift_transpose_mul_oddEven p
  set U := oddEven p
  set T := cyclicShift (2 * p)
  have e1 : T * (α • (U * Vᵀ)) = (-α) • (U * Vᵀ) := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hU, Matrix.neg_mul, smul_neg, neg_smul]
  have e2 : Tᵀ * (α • (U * Vᵀ)) = (-α) • (U * Vᵀ) := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hU', Matrix.neg_mul, smul_neg, neg_smul]
  have e3 : (U * Vᵀ) * D = a • (U * Vᵀ) := by
    have h := congrArg Matrix.transpose hDV
    rw [Matrix.transpose_mul, hDs, Matrix.transpose_smul] at h
    rw [Matrix.mul_assoc, h, Matrix.mul_smul]
  have hq : (streamingProblem p hΔ D).q t = 0 := rfl
  simp only [TransportProblem.field, TransportProblem.op, hq, sourceMat_zero, add_zero]
  change streamOp T Δz (muMatrix n) D (α • (U * Vᵀ)) +
    (Matrix.diagonal (0 : Fin (2 * p) → ℝ) * (α • (U * Vᵀ)) * isoProj n -
      Matrix.diagonal (0 : Fin (2 * p) → ℝ) * (α • (U * Vᵀ))) = _
  have hd : Matrix.diagonal (0 : Fin (2 * p) → ℝ) = 0 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have key : (T - Tᵀ) * (α • (U * Vᵀ)) * muMatrix n = 0 := by
    rw [Matrix.sub_mul, e1, e2, sub_self, Matrix.zero_mul]
  have key2 : (T + Tᵀ - (2 : ℝ) • 1) * (α • (U * Vᵀ)) = (-(4 * α)) • (U * Vᵀ) := by
    rw [Matrix.sub_mul, Matrix.add_mul, e1, e2, Matrix.smul_mul, Matrix.one_mul]
    module
  have hscal : -(2 * Δz)⁻¹ * (4 * α * a) = -(2 * a / Δz * α) := by
    field_simp
    ring
  rw [hd, Matrix.zero_mul, Matrix.zero_mul, sub_zero, add_zero, streamOp, key,
    key2, Matrix.smul_mul, e3, ← hscal]
  module

/-- **The explicit Euler KSL step of the paper on the odd-even mode** (arXiv 1906.09940, Sec. 2.1,
"first-order explicit integration" of (2.8)-(2.10)): with `ν = h / Δz`, it multiplies `U Vᵀ` by
`(1 - 2 ν a)² (1 + 2 ν a)`, whereas the full Euler step multiplies it by `1 - 2 ν a`. -/
theorem ksl_euler_streaming_mode {p : ℕ} (hp : 0 < p) {Δz : ℝ} (hΔ : 0 < Δz) {D : 𝐌[n, n]}
    (hDs : Dᵀ = D) {a : ℝ} {V : 𝐌[n, 1]} (hV : Vᵀ * V = 1) (hDV : D * V = a • V) (t h : ℝ) :
    kslEulerStep (leftProj (oddEven p)) (rightProj V) ((streamingProblem p hΔ D).field t) h
        (oddEven p * Vᵀ) =
      ((1 - 2 * (h / Δz * a)) ^ 2 * (1 + 2 * (h / Δz * a))) • (oddEven p * Vᵀ) := by
  have h1 := kslEulerStep_eigen (c := 2 * a / Δz) (h := h)
    (P₁ := leftProj (oddEven p)) (Q₀ := rightProj V)
    (F := (streamingProblem p hΔ D).field t) (x := oddEven p * Vᵀ)
    (leftProj_mul_left (oddEven_orthonormal hp) _) (rightProj_mul_transpose hV _)
    (fun α => streamingProblem_field_mode p hΔ hDs hDV t α)
  rw [h1]
  congr 3 <;> ring

/-- arXiv 1906.09940, Sec. 2.1, QR step, not in the paper: on the odd-even mode the K-step result
stays in the span of `U`, so `U` is a QR basis of `K¹` and `kslEulerStep` with `P₁ = U Uᵀ` is the
integrator of the paper (the preconditions of `LeanDLRA.kslEulerStep`). -/
theorem ksl_euler_streaming_capture {p : ℕ} (hp : 0 < p) {Δz : ℝ} (hΔ : 0 < Δz) {D : 𝐌[n, n]}
    (hDs : Dᵀ = D) {a : ℝ} {V : 𝐌[n, 1]} (hV : Vᵀ * V = 1) (hDV : D * V = a • V) (t h : ℝ) :
    rightProj V (oddEven p * Vᵀ) = oddEven p * Vᵀ ∧
      leftProj (oddEven p) (kslK (rightProj V) ((streamingProblem p hΔ D).field t) h
        (oddEven p * Vᵀ)) =
      kslK (rightProj V) ((streamingProblem p hΔ D).field t) h (oddEven p * Vᵀ) := by
  have hQ := rightProj_mul_transpose hV (oddEven p)
  have hP := leftProj_mul_left (oddEven_orthonormal hp) Vᵀ
  have hF := streamingProblem_field_mode p hΔ hDs hDV t 1
  rw [one_smul] at hF
  refine ⟨hQ, ?_⟩
  simp only [kslK, hF, map_add, map_smul, hP, hQ]

omit [NeZero n] in
/-- arXiv 1906.09940, Sec. 2.1 and (2.16), not in the paper: The pure streaming problem is
admissible. -/
theorem isAdmissible_streamingProblem (p : ℕ) {Δz : ℝ} (hΔ : 0 < Δz) {D : 𝐌[n, n]} {a : ℝ}
    (ha : 0 ≤ a) (hS : IsStabilisation (muMatrix n) D a) :
    (streamingProblem p hΔ D).IsAdmissible a 0 where
  shift := isShift_cyclicShift _
  stab := hS
  a_nonneg := ha
  b_nonneg := le_rfl
  σs_nonneg := fun _ => le_rfl
  σs_le := fun _ => le_rfl
  σt_le := fun _ => le_rfl

omit [NeZero n] in
private lemma norm_oddEven_mul {p : ℕ} (hp : 0 < p) {V : 𝐌[n, 1]} (hV : Vᵀ * V = 1) :
    ‖oddEven p * Vᵀ‖ = 1 := by
  rw [Frobenius.norm_mul_of_orthonormal (oddEven_orthonormal hp), Frobenius.norm_transpose]
  have h := Frobenius.norm_mul_of_orthonormal hV (1 : 𝐌[1, 1])
  rw [Matrix.mul_one] at h
  rw [h, Frobenius.norm_def]
  simp

/-- **`L²`-stability does not transfer to the explicit Euler KSL step** (the note in the header; the
concrete form of `kslEulerStep_unstable`, not in arXiv 1906.09940).  Take pure streaming on a
periodic mesh of `2 p` cells, a stabilisation `D ≥ ±C`, `D ≤ a` with a unit eigenvector
`D V = a V`, and the step `h = Δz / a` (CFL number one).  Then the full explicit Euler step is
norm-nonincreasing for **all** `Y`, but the KSL step triples the unit vector `U Vᵀ`. -/
theorem ksl_euler_unstable {p : ℕ} (hp : 0 < p) {Δz : ℝ} (hΔ : 0 < Δz) {D : 𝐌[n, n]}
    (hDs : Dᵀ = D) {a : ℝ} (ha : 0 < a) (hS : IsStabilisation (muMatrix n) D a) {V : 𝐌[n, 1]}
    (hV : Vᵀ * V = 1) (hDV : D * V = a • V) (t : ℝ) :
    (∀ Y, ‖eulerStep ((streamingProblem p hΔ D).field t) (Δz / a) Y‖ ≤ ‖Y‖) ∧
    kslEulerStep (leftProj (oddEven p)) (rightProj V) ((streamingProblem p hΔ D).field t)
        (Δz / a) (oddEven p * Vᵀ) = (3 : ℝ) • (oddEven p * Vᵀ) ∧
    ‖oddEven p * Vᵀ‖ = 1 := by
  have hν : Δz / a / Δz * a = 1 := by
    have := hΔ.ne'
    have := ha.ne'
    field_simp
  refine ⟨fun Y => ?_, ?_, norm_oddEven_mul hp hV⟩
  · have hq : (streamingProblem p hΔ D).q t = 0 := rfl
    have h1 := TransportProblem.norm_euler_op_le (isAdmissible_streamingProblem p hΔ ha.le hS)
      (h := Δz / a) (by positivity) (by
        change Δz / a * (a / Δz + 0) ≤ 1
        have := hΔ.ne'
        have := ha.ne'
        rw [add_zero]
        field_simp
        exact le_rfl) Y
    simpa only [eulerStep, TransportProblem.field, hq, sourceMat_zero, add_zero] using h1
  · rw [ksl_euler_streaming_mode hp hΔ hDs hV hDV, hν]
    norm_num

/-- **The upwind scheme `Σ = |C|` of arXiv 1906.09940, (2.16), with explicit Euler KSL is not
`L²`-stable under the CFL condition of the full scheme** (the note in the header; not in the
paper).  For `n ≥ 2` there are a largest characteristic speed `0 < a ≤ 1` and a unit eigenvector
`V` of `|C|` such that, at CFL number one (`h = Δz / a`), pure streaming on a periodic mesh has a
norm-nonincreasing full Euler step, while the KSL step triples the unit vector `U Vᵀ`. -/
theorem ksl_euler_unstable_upwind (hn : 2 ≤ n) {p : ℕ} (hp : 0 < p) {Δz : ℝ} (hΔ : 0 < Δz)
    (t : ℝ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ V : 𝐌[n, 1], Vᵀ * V = 1 ∧
      (∀ Y, ‖eulerStep ((streamingProblem p hΔ (absSymm (muMatrix_isHermitian n))).field t)
        (Δz / a) Y‖ ≤ ‖Y‖) ∧
      kslEulerStep (leftProj (oddEven p)) (rightProj V)
          ((streamingProblem p hΔ (absSymm (muMatrix_isHermitian n))).field t) (Δz / a)
          (oddEven p * Vᵀ) = (3 : ℝ) • (oddEven p * Vᵀ) ∧
      ‖oddEven p * Vᵀ‖ = 1 := by
  set hC := muMatrix_isHermitian n with hC_def
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => |hC.eigenvalues i|) ⟨0, Finset.mem_univ _⟩
  set a := |hC.eigenvalues j| with ha_def
  have hbound : ∀ i, |hC.eigenvalues i| ≤ a := fun i => hj i (Finset.mem_univ _)
  have hpsd := smul_one_add_sub_of_eigenvalue hC hbound
  have hS : IsStabilisation (muMatrix n) (absSymm hC) a :=
    isStabilisation_absSymm hC hpsd.1 hpsd.2
  have ha1 : a ≤ 1 := by
    have hS1 := isStabilisation_absSymm_muMatrix n
    have h₁ : ((1 : ℝ) • (1 : 𝐌[n, n]) - muMatrix n).PosSemidef := by
      have h := one_add_smul_muMatrix_posSemidef n (s := -1) (by simp)
      simpa [sub_eq_add_neg] using h
    have h₂ : ((1 : ℝ) • (1 : 𝐌[n, n]) + muMatrix n).PosSemidef := by
      have h := one_add_smul_muMatrix_posSemidef n (s := 1) (by simp)
      simpa using h
    exact abs_eigenvalue_le hC h₁ h₂ j
  have ha0 : 0 < a := by
    refine lt_of_le_of_ne (abs_nonneg _) fun h0 => ?_
    have hzero : hC.eigenvalues = 0 := by
      ext i
      have := hbound i
      rw [← h0] at this
      simpa using abs_nonpos_iff.1 this
    have hCzero : muMatrix n = 0 := by
      have hs := spectral hC
      rw [hzero] at hs
      have hd : Matrix.diagonal (0 : Fin n → ℝ) = 0 := by
        ext i i'
        by_cases hii : i = i' <;> simp [hii]
      rw [hd, Matrix.mul_zero, Matrix.zero_mul] at hs
      exact hs
    have h01 : muOff 0 = 0 := by
      simpa [muMatrix_apply] using congrFun (congrFun hCzero ⟨0, by omega⟩) ⟨1, by omega⟩
    have hm : muOff 0 ≠ 0 := by
      simp only [muOff]
      have : 0 < √((2 * ((0 : ℕ) : ℝ) + 1) * (2 * ((0 : ℕ) : ℝ) + 3)) :=
        Real.sqrt_pos.2 (by norm_num)
      positivity
    exact hm h01
  refine ⟨a, ha0, ha1, Matrix.of fun i _ => eigQ hC i j, ?_, ?_⟩
  · ext x y
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Subsingleton.elim _ _
    subst hx hy
    have h := congrFun (congrFun (eigQ_transpose_mul hC) j) j
    simpa [Matrix.mul_apply] using h
  · have hV : (Matrix.of fun i _ => eigQ hC i j : 𝐌[n, 1])ᵀ *
        (Matrix.of fun i _ => eigQ hC i j : 𝐌[n, 1]) = 1 := by
      ext x y
      have hx : x = 0 := Subsingleton.elim _ _
      have hy : y = 0 := Subsingleton.elim _ _
      subst hx hy
      have h := congrFun (congrFun (eigQ_transpose_mul hC) j) j
      simpa [Matrix.mul_apply] using h
    have hDs : (absSymm hC)ᵀ = absSymm hC := by
      have h := hS.posSemidef.isHermitian
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have hDQ : absSymm hC * eigQ hC = eigQ hC * Matrix.diagonal fun i => |hC.eigenvalues i| := by
      rw [absSymm, Matrix.mul_assoc, eigQ_transpose_mul, Matrix.mul_one]
    have hDV : absSymm hC * (Matrix.of fun i _ => eigQ hC i j : 𝐌[n, 1]) =
        a • (Matrix.of fun i _ => eigQ hC i j : 𝐌[n, 1]) := by
      ext i x
      have h := congrFun (congrFun hDQ i) j
      rw [Matrix.mul_diagonal, Matrix.mul_apply] at h
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [h, mul_comm]
    exact ksl_euler_unstable hp hΔ hDs ha0 hS hV hDV t

/-- **The Lax-Friedrichs variant is not stable either** (arXiv 1906.09940 after (2.16), with the
constant `α = 1`; not in the paper): at `h = Δz` the full Euler step is norm-nonincreasing, while
the KSL step triples the unit vector `U e₀ᵀ`. -/
theorem ksl_euler_unstable_laxFriedrichs {p : ℕ} (hp : 0 < p) {Δz : ℝ} (hΔ : 0 < Δz) (t : ℝ) :
    let V : 𝐌[n, 1] := Matrix.of fun l _ => if l = 0 then 1 else 0
    (∀ Y, ‖eulerStep ((streamingProblem p hΔ ((1 : ℝ) • (1 : 𝐌[n, n]))).field t) Δz Y‖ ≤ ‖Y‖) ∧
    kslEulerStep (leftProj (oddEven p)) (rightProj V)
        ((streamingProblem p hΔ ((1 : ℝ) • (1 : 𝐌[n, n]))).field t) Δz (oddEven p * Vᵀ) =
      (3 : ℝ) • (oddEven p * Vᵀ) := by
  intro V
  have hV : Vᵀ * V = 1 := by
    ext x y
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Subsingleton.elim _ _
    subst hx hy
    simp [V, Matrix.mul_apply, Finset.sum_ite_eq']
  have h := ksl_euler_unstable (n := n) hp hΔ (D := (1 : ℝ) • (1 : 𝐌[n, n])) (a := 1) (by simp)
    one_pos
    (isStabilisation_laxFriedrichs le_rfl) hV (by simp) t
  simpa only [div_one] using (⟨h.1, h.2.1⟩ : _ ∧ _)

/-- arXiv 1906.09940, Sec. 2.1 and (2.16), not in the paper: For every CFL number `ν = h a / Δz`
above `(1 + √5) / 4 ≈ 0.809` the KSL amplification of the odd-even mode exceeds `1`, although the
full scheme is stable up to `ν = 1`. -/
theorem ksl_amplification_gt_one {ν : ℝ} (hν : (1 + √5) / 4 < ν) :
    1 < (1 - 2 * ν) ^ 2 * (1 + 2 * ν) := by
  have hs : 0 ≤ 2 * ν := by
    have : 0 ≤ (1 + √5) / 4 := by positivity
    linarith
  have h := (ksl_scalar_amplification_le_one_iff hs).not
  have h2 : ¬ 2 * ν ≤ (1 + √5) / 2 := by linarith
  exact not_le.1 (h.2 h2)

end KSLInstability

/-! ### Conservation and the rescaling of Sec. 2.2 -/

section Conservation

open scoped LeanDLRA.Frobenius

variable {m n r : ℕ}

/-- The function `ψ(z, μ) = ∑_kl Y_kl Z_k(z) P_l(μ)` with coefficient matrix `Y`. -/
noncomputable def expansion (Δz : ℝ) (Y : 𝐌[m, n]) (z μ : ℝ) : ℝ :=
  ∑ k : Fin m, ∑ l : Fin n, cellFn Δz k z * Y k l * nLeg l μ

/-- **Eq. (2.1) of arXiv 1906.09940**: `ψ = ∑_ij X_i S_ij W_j` has the coefficient matrix
`U S Vᵀ`. -/
theorem expansion_factored (Δz : ℝ) (U : 𝐌[m, r]) (S : 𝐌[r, r]) (V : 𝐌[n, r]) (z μ : ℝ) :
    expansion Δz (U * S * Vᵀ) z μ =
      ∑ i : Fin r, ∑ j : Fin r, spatialBasis Δz U i z * S i j * angularBasis V j μ := by
  set a : Fin m → ℝ := fun k => cellFn Δz k z
  set b : Fin n → ℝ := fun l => nLeg l μ
  have hL : expansion Δz (U * S * Vᵀ) z μ = a ⬝ᵥ ((U * S * Vᵀ) *ᵥ b) := by
    simp only [expansion, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [a, b]
    ring
  have hR : ∑ i : Fin r, ∑ j : Fin r, spatialBasis Δz U i z * S i j * angularBasis V j μ =
      (a ᵥ* U) ⬝ᵥ (S *ᵥ (Vᵀ *ᵥ b)) := by
    simp only [spatialBasis, angularBasis, dotProduct, Matrix.vecMul, Matrix.mulVec,
      Matrix.transpose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    simp only [a, b, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hL, hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

variable [NeZero n]

/-- The total number of particles `∫∫ ψ dμ dz` of the coefficient matrix `Y`. -/
noncomputable def particles (Δz : ℝ) (Y : 𝐌[m, n]) : ℝ := √(2 * Δz) * ∑ k, Y k 0

/-- **The particle count of Sec. 2.2 of arXiv 1906.09940** is `√(2 Δz) ∑_k Y_k0`:
`∫₀^{m Δz} ∫₋₁¹ ψ dμ dz = particles Δz Y`. -/
theorem integral_expansion {Δz : ℝ} (hΔ : 0 < Δz) (Y : 𝐌[m, n]) :
    ∫ z in (0 : ℝ)..((m : ℝ) * Δz), ∫ μ in (-1 : ℝ)..1, expansion Δz Y z μ = particles Δz Y := by
  have hinner : ∀ z, ∫ μ in (-1 : ℝ)..1, expansion Δz Y z μ =
      ∑ k : Fin m, (√2 * Y k 0) * cellFn Δz k z := by
    intro z
    have hl : ∀ k ∈ (Finset.univ : Finset (Fin m)), IntervalIntegrable
        (fun μ => ∑ l : Fin n, cellFn Δz k z * Y k l * nLeg l μ) MeasureTheory.volume (-1) 1 := by
      intro k _
      have hc : Continuous fun μ => ∑ l : Fin n, cellFn Δz k z * Y k l * nLeg l μ :=
        continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_nLeg l)
      exact hc.intervalIntegrable _ _
    simp only [expansion]
    rw [intervalIntegral.integral_finsetSum hl]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hl' : ∀ l ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
        (fun μ => cellFn Δz k z * Y k l * nLeg l μ) MeasureTheory.volume (-1) 1 := fun l _ =>
      Continuous.intervalIntegrable (continuous_const.mul (continuous_nLeg l)) _ _
    rw [intervalIntegral.integral_finsetSum hl']
    simp only [intervalIntegral.integral_const_mul, integral_nLeg]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, ite_true]
      ring
    · intro l _ hl0
      have : (l : ℕ) ≠ 0 := fun h => hl0 (Fin.ext (by simpa using h))
      simp [this]
    · simp
  simp_rw [hinner]
  have hI : ∀ k ∈ (Finset.univ : Finset (Fin m)), IntervalIntegrable
      (fun z => (√2 * Y k 0) * cellFn Δz k z) MeasureTheory.volume 0 ((m : ℝ) * Δz) :=
    fun k _ => (cellFn_intervalIntegrable Δz k _ _).const_mul _
  rw [intervalIntegral.integral_finsetSum hI]
  simp only [intervalIntegral.integral_const_mul]
  have hs : √(2 * Δz) = √2 * √Δz := Real.sqrt_mul (by norm_num) _
  rw [particles, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_cellFn hΔ k.2]
  ring

/-- The particle count is additive. -/
lemma particles_add (Δz : ℝ) (X Y : 𝐌[m, n]) :
    particles Δz (X + Y) = particles Δz X + particles Δz Y := by
  simp only [particles, Matrix.add_apply, Finset.sum_add_distrib, mul_add]

/-- The particle count is homogeneous. -/
lemma particles_smul (Δz c : ℝ) (Y : 𝐌[m, n]) : particles Δz (c • Y) = c * particles Δz Y := by
  simp only [particles, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- A grid shift without particle loss at the boundary: `T` has unit row and column sums. -/
structure IsConservativeShift (T : 𝐌[m, m]) : Prop where
  row : ∀ i, ∑ j, T i j = 1
  col : ∀ j, ∑ i, T i j = 1

omit [NeZero n] in
private lemma sum_mul_col {A : 𝐌[m, m]} (hA : ∀ j, ∑ k, A k j = 0) (W : 𝐌[m, n]) (l : Fin n) :
    ∑ k, (A * W) k l = 0 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hA, zero_mul, Finset.sum_const_zero]

/-- arXiv 1906.09940, Sec. 2.2: The periodic shift conserves particles. -/
theorem isConservativeShift_cyclicShift (m : ℕ) : IsConservativeShift (cyclicShift m) := by
  have hrow : ∀ i : Fin m, ∑ j, cyclicShift m i j = 1 := by
    intro i
    rw [Finset.sum_eq_single (⟨(i + 1) % m, Nat.mod_lt _ i.pos⟩ : Fin m)]
    · simp [cyclicShift]
    · intro j _ hj
      have : (j : ℕ) ≠ (i + 1) % m := fun e => hj (Fin.ext e)
      simp [cyclicShift, this]
    · simp
  refine ⟨hrow, fun j => ?_⟩
  have h1 : (cyclicShift m)ᵀ * cyclicShift m = 1 :=
    mul_eq_one_comm.1 (cyclicShift_mul_transpose m)
  have hv : cyclicShift m *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, hrow]
  have h2 : (cyclicShift m)ᵀ *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    conv_lhs => rw [← hv, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have h3 := congrFun h2 j
  simpa [Matrix.mulVec, dotProduct] using h3

namespace TransportProblem

variable {P : TransportProblem m n}

/-- arXiv 1906.09940, Sec. 2.2: **Particle balance of the full scheme**: on a conservative grid,
streaming does not change the particle count; `d/dt N = ∑_k √(2 Δz) (σs_k - σt_k) Y_k0`. -/
theorem particles_op (hT : IsConservativeShift P.T) (Y : 𝐌[m, n]) :
    particles P.Δz (P.op Y) = √(2 * P.Δz) * ∑ k, (P.σs k - P.σt k) * Y k 0 := by
  have h1 : ∀ j, ∑ k, (P.T - P.Tᵀ) k j = 0 := by
    intro j
    simp only [Matrix.sub_apply, Matrix.transpose_apply, Finset.sum_sub_distrib, hT.row, hT.col,
      sub_self]
  have h2 : ∀ j, ∑ k, (P.T + P.Tᵀ - (2 : ℝ) • 1) k j = 0 := by
    intro j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hT.row, hT.col, smul_eq_mul,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    norm_num
  have hs : ∑ k, (streamOp P.T P.Δz (muMatrix n) P.D Y) k 0 = 0 := by
    simp only [streamOp, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Matrix.mul_assoc, sum_mul_col h1, sum_mul_col h2]
    simp
  simp only [particles, op, Matrix.add_apply, Finset.sum_add_distrib, hs, zero_add, coll_apply]
  simp

/-- arXiv 1906.09940, Sec. 2.2: The particle count of the source term: `∑_k √Δz q_k`, where `√Δz
q_k` is the integral of the source over cell `k`. -/
theorem particles_sourceMat (hΔ : 0 < P.Δz) (q : Fin m → ℝ) :
    particles P.Δz (sourceMat q : 𝐌[m, n]) = √P.Δz * ∑ k, q k := by
  have hs : √(2 * P.Δz) = √2 * √P.Δz := Real.sqrt_mul (by norm_num) _
  have h0 : √2 ≠ 0 := by positivity
  simp only [particles, sourceMat, Matrix.of_apply, ite_true, ← Finset.mul_sum, hs]
  field_simp

/-- **The full scheme conserves particles** in a purely scattering medium on a conservative grid
(`σs = σt`, no source): `∑ N(Y + h R Y) = N(Y)`.  This is the target of the rescaling of Sec. 2.2
of arXiv 1906.09940. -/
theorem particles_eulerStep (hT : IsConservativeShift P.T) (hσ : ∀ k, P.σs k = P.σt k)
    (hq : ∀ t k, P.q t k = 0) (t h : ℝ) (Y : 𝐌[m, n]) :
    particles P.Δz (eulerStep (P.field t) h Y) = particles P.Δz Y := by
  have hq' : P.q t = 0 := funext (hq t)
  have h0 : (sourceMat (P.q t) : 𝐌[m, n]) = 0 := by rw [hq']; ext k l; simp [sourceMat]
  rw [eulerStep, particles_add, particles_smul, field, h0, add_zero, particles_op hT]
  simp [hσ]

end TransportProblem

/-- **The rescaling of Sec. 2.2 of arXiv 1906.09940**: `Y ↦ (N₀ / N(Y)) Y` for the target particle
count `N₀`. -/
noncomputable def rescale (Δz N₀ : ℝ) (Y : 𝐌[m, n]) : 𝐌[m, n] := (N₀ / particles Δz Y) • Y

/-- arXiv 1906.09940, Sec. 2.2: Rescaling restores the particle count exactly. -/
theorem particles_rescale {Δz N₀ : ℝ} {Y : 𝐌[m, n]} (h : particles Δz Y ≠ 0) :
    particles Δz (rescale Δz N₀ Y) = N₀ := by
  rw [rescale, particles_smul, div_mul_cancel₀ _ h]

/-- arXiv 1906.09940, Sec. 2.2: Rescaling only changes the core factor `S` of `Y = U S Vᵀ`. -/
theorem rescale_factored (Δz N₀ : ℝ) (U : 𝐌[m, r]) (S : 𝐌[r, r]) (V : 𝐌[n, r]) :
    rescale Δz N₀ (U * S * Vᵀ) =
      U * ((N₀ / particles Δz (U * S * Vᵀ)) • S) * Vᵀ := by
  rw [rescale, Matrix.mul_smul, Matrix.smul_mul]

/-- arXiv 1906.09940, Sec. 2.2: **Rescaling keeps the rank** (Sec. 2.2): if the target `N₀` and the
particle count are nonzero, `rank (rescale Y) = rank Y`. -/
theorem rank_rescale {Δz N₀ : ℝ} {Y : 𝐌[m, n]} (h : particles Δz Y ≠ 0) (hN₀ : N₀ ≠ 0) :
    (rescale Δz N₀ Y).rank = Y.rank := by
  have hc : N₀ / particles Δz Y ≠ 0 := div_ne_zero hN₀ h
  exact Matrix.rank_smul_of_mem_nonZeroDivisors Y (mem_nonZeroDivisors_of_ne_zero hc)

/-- Scaling commutes with the projectors of the KSL step (arXiv 1906.09940, Sec. 2.2). -/
theorem rescale_comm_proj (Δz N₀ : ℝ) (U : 𝐌[m, r]) (V : 𝐌[n, r]) (Y : 𝐌[m, n]) :
    leftProj U (rescale Δz N₀ Y) = (N₀ / particles Δz Y) • leftProj U Y ∧
      rightProj V (rescale Δz N₀ Y) = (N₀ / particles Δz Y) • rightProj V Y := by
  simp only [rescale, map_smul, and_self]

private lemma abs_particles_le {Δz : ℝ} (hΔ : 0 < Δz) (W : 𝐌[m, n]) :
    |particles Δz W| ≤ √(2 * Δz * m) * ‖W‖ := by
  have h1 : (∑ k, W k 0) ^ 2 ≤ m * ∑ k, W k 0 ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => W k 0)
  have h2 : ∑ k, W k 0 ^ 2 ≤ ‖W‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    exact Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := fun l => W k l ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ 0)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h3 : |∑ k, W k 0| ≤ √m * ‖W‖ := by
    have h4 : (∑ k, W k 0) ^ 2 ≤ (√m * ‖W‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hm]
      nlinarith
    exact abs_le_of_sq_le_sq h4 (by positivity)
  rw [particles, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul (by positivity : 0 ≤
    2 * Δz), mul_assoc]
  exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)

/-- **Rescaling does not spoil the accuracy** (not in arXiv 1906.09940, whose Sec. 2.2 gives no
analysis): if the reference `A` has the particle count `N₀ = N(A)` that the rescaling restores,
`‖rescale Y - A‖ ≤ (1 + √(2 Δz m) ‖Y‖ / |N(Y)|) ‖Y - A‖`. -/
theorem norm_rescale_sub_le {Δz : ℝ} (hΔ : 0 < Δz) {Y A : 𝐌[m, n]} (h : particles Δz Y ≠ 0) :
    ‖rescale Δz (particles Δz A) Y - A‖ ≤
      (1 + √(2 * Δz * m) * ‖Y‖ / |particles Δz Y|) * ‖Y - A‖ := by
  have hN : 0 < |particles Δz Y| := abs_pos.2 h
  have e : rescale Δz (particles Δz A) Y - A =
      (Y - A) + (particles Δz A / particles Δz Y - 1) • Y := by
    rw [rescale, sub_smul, one_smul]
    abel
  have hsub : particles Δz A - particles Δz Y = particles Δz (A - Y) := by
    simp only [particles, Matrix.sub_apply, Finset.sum_sub_distrib, mul_sub]
  have hb : |particles Δz A / particles Δz Y - 1| ≤
      √(2 * Δz * m) * ‖Y - A‖ / |particles Δz Y| := by
    rw [div_sub_one h, abs_div, hsub, norm_sub_rev Y A]
    exact div_le_div_of_nonneg_right (abs_particles_le hΔ _) hN.le
  rw [e]
  calc _ ≤ ‖Y - A‖ + ‖(particles Δz A / particles Δz Y - 1) • Y‖ := norm_add_le _ _
    _ = ‖Y - A‖ + |particles Δz A / particles Δz Y - 1| * ‖Y‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖Y - A‖ + √(2 * Δz * m) * ‖Y - A‖ / |particles Δz Y| * ‖Y‖ := by gcongr
    _ = _ := by ring

/-- arXiv 1906.09940, Sec. 2.2: A solution that already has the right particle count is not changed.
-/
theorem rescale_of_particles_eq {Δz N₀ : ℝ} {Y : 𝐌[m, n]} (h : particles Δz Y = N₀)
    (hN₀ : N₀ ≠ 0) : rescale Δz N₀ Y = Y := by
  rw [rescale, h, div_self hN₀, one_smul]

/-- arXiv 1906.09940, Sec. 2.2: Rescaled iterates conserve the particle count at every step: the
scheme of Sec. 2.2. -/
theorem particles_rescale_iterate {Δz N₀ : ℝ} {step : 𝐌[m, n] → 𝐌[m, n]} {Y₀ : 𝐌[m, n]}
    (h : ∀ k, particles Δz ((fun Y => step (rescale Δz N₀ Y))^[k] Y₀) ≠ 0) :
    ∀ k : ℕ, particles Δz (rescale Δz N₀ ((fun Y => step (rescale Δz N₀ Y))^[k] Y₀)) = N₀ :=
  fun k => particles_rescale (h k)

private lemma cyclicShift_one : cyclicShift 1 = 1 := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst hij
  simp [cyclicShift]

/-- A homogeneous purely scattering medium: one periodic cell, `σs = σt = σ`, no source.  Streaming
vanishes on this mesh and the stabilisation is irrelevant. -/
noncomputable def scatteringProblem {Δz : ℝ} (hΔ : 0 < Δz) (D : 𝐌[n, n]) (σ : ℝ) :
    TransportProblem 1 n where
  Δz := Δz
  Δz_pos := hΔ
  T := cyclicShift 1
  D := D
  σs := fun _ => σ
  σt := fun _ => σ
  q := fun _ _ => 0

private lemma scatteringProblem_field {Δz : ℝ} (hΔ : 0 < Δz) (D : 𝐌[n, n]) (σ t : ℝ)
    (Y : 𝐌[1, n]) :
    (scatteringProblem hΔ D σ).field t Y = σ • (Y * isoProj n - Y) := by
  have hq : (scatteringProblem hΔ D σ).q t = 0 := rfl
  have hd : Matrix.diagonal (fun _ : Fin 1 => σ) = σ • (1 : 𝐌[1, 1]) := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    simp
  have hs : (sourceMat (0 : Fin 1 → ℝ) : 𝐌[1, n]) = 0 := sourceMat_zero
  have h2 : (1 : 𝐌[1, 1]) + 1ᵀ - (2 : ℝ) • 1 = 0 := by
    rw [Matrix.transpose_one, two_smul]
    abel
  have h1 : (1 : 𝐌[1, 1]) - 1ᵀ = 0 := by
    rw [Matrix.transpose_one, sub_self]
  simp only [TransportProblem.field, TransportProblem.op, hq, hs, add_zero]
  change streamOp (cyclicShift 1) Δz (muMatrix n) D Y +
    (Matrix.diagonal (fun _ : Fin 1 => σ) * Y * isoProj n -
      Matrix.diagonal (fun _ : Fin 1 => σ) * Y) = _
  rw [cyclicShift_one, streamOp, h1, h2, hd]
  simp only [Matrix.zero_mul, sub_self, smul_zero, zero_add, Matrix.smul_mul, Matrix.one_mul,
    smul_sub]

/-- **Explicit Euler KSL loses particles** (arXiv 1906.09940, Sec. 2.2: "The low-rank algorithm we
have described does not conserve the number of particles").  In a homogeneous scattering medium,
start from `Y₀ = Vᵀ` with a unit vector `V`; then the particle count of one KSL step is
`(1 - g²) N(Y₀)` with `g = h σ (1 - V₀²)`, whereas the full Euler step conserves it. -/
theorem ksl_euler_particles {Δz : ℝ} (hΔ : 0 < Δz) (D : 𝐌[n, n]) (σ t h : ℝ) {V : 𝐌[n, 1]}
    (hV : Vᵀ * V = 1) :
    particles Δz (kslEulerStep (leftProj (1 : 𝐌[1, 1])) (rightProj V)
        ((scatteringProblem hΔ D σ).field t) h Vᵀ) =
      (1 - (h * σ * (1 - V 0 0 ^ 2)) ^ 2) * particles Δz Vᵀ := by
  set F := (scatteringProblem hΔ D σ).field t with hF
  set c := σ * (1 - V 0 0 ^ 2) with hc
  have hE : Vᵀ * isoProj n * V = (V 0 0 ^ 2) • (1 : 𝐌[1, 1]) := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    rw [Matrix.mul_apply]
    simp only [isoProj, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hP : ∀ X : 𝐌[1, n], leftProj (1 : 𝐌[1, 1]) X = X := fun X => by simp
  have hQ : ∀ α : ℝ, rightProj V (F (α • Vᵀ)) = (-(c * α)) • Vᵀ := by
    intro α
    have e1 : (α • Vᵀ) * isoProj n * V = (α * V 0 0 ^ 2) • (1 : 𝐌[1, 1]) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, hE, smul_smul]
    have e2 : (α • Vᵀ) * V = α • (1 : 𝐌[1, 1]) := by
      rw [Matrix.smul_mul, hV]
    rw [hF, scatteringProblem_field, rightProj_apply, Matrix.smul_mul, Matrix.sub_mul, e1, e2,
      Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hc]
    module
  have hK : kslK (rightProj V) F h Vᵀ = (1 - h * c) • Vᵀ := by
    have h1 := hQ 1
    rw [one_smul] at h1
    rw [kslK, h1]
    module
  have hS : kslS (leftProj (1 : 𝐌[1, 1])) (rightProj V) F h ((1 - h * c) • Vᵀ) =
      ((1 - h * c) * (1 + h * c)) • Vᵀ := by
    simp only [kslS, hP]
    rw [hQ]
    module
  have hN : ∀ W : 𝐌[1, n], particles Δz (F W) = 0 := by
    intro W
    rw [hF, scatteringProblem_field, particles_smul]
    have : particles Δz (W * isoProj n - W) = 0 := by
      simp [particles, isoProj, Matrix.mul_diagonal]
    rw [this, mul_zero]
  have hL : particles Δz (kslL (leftProj (1 : 𝐌[1, 1])) F h (((1 - h * c) * (1 + h * c)) • Vᵀ)) =
      ((1 - h * c) * (1 + h * c)) * particles Δz Vᵀ := by
    simp only [kslL, hP]
    rw [particles_add, particles_smul Δz h, hN, mul_zero, add_zero, particles_smul]
  rw [kslEulerStep, hK, hS, hL, hc]
  ring

/-- **Sec. 2.2 of arXiv 1906.09940, the concrete counterexample**: for `n = 2`, `V = (3/5, 4/5)ᵀ`,
`σ h ≠ 0`, one explicit Euler KSL step changes the particle count, while the full Euler step keeps
it. -/
theorem ksl_euler_not_conservative {Δz : ℝ} (hΔ : 0 < Δz) (D : 𝐌[2, 2]) {σ h : ℝ} (hσ : σ ≠ 0)
    (hh : h ≠ 0) (t : ℝ) :
    let V : 𝐌[2, 1] := !![3 / 5; 4 / 5]
    particles Δz (kslEulerStep (leftProj (1 : 𝐌[1, 1])) (rightProj V)
        ((scatteringProblem hΔ D σ).field t) h Vᵀ) ≠ particles Δz Vᵀ ∧
      particles Δz (eulerStep ((scatteringProblem hΔ D σ).field t) h Vᵀ) = particles Δz Vᵀ := by
  intro V
  have hV : Vᵀ * V = 1 := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [V, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  have hV0 : V 0 0 = 3 / 5 := by simp [V]
  have hN : particles Δz Vᵀ ≠ 0 := by
    have : particles Δz Vᵀ = √(2 * Δz) * (3 / 5) := by
      simp [particles, V]
    rw [this]
    have : 0 < √(2 * Δz) := Real.sqrt_pos.2 (by positivity)
    positivity
  refine ⟨?_, ?_⟩
  · rw [ksl_euler_particles hΔ D σ t h hV, hV0]
    intro heq
    have h1 : (1 - (h * σ * (1 - (3 / 5) ^ 2)) ^ 2) = 1 := by
      exact mul_right_cancel₀ hN (by rw [heq, one_mul])
    have h2 : h * σ * (1 - (3 / 5) ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hh hσ) (by norm_num)
    have h3 : (h * σ * (1 - (3 / 5) ^ 2)) ^ 2 ≠ 0 := pow_ne_zero 2 h2
    apply h3
    linarith
  · exact TransportProblem.particles_eulerStep (P := scatteringProblem hΔ D σ)
      (isConservativeShift_cyclicShift 1) (fun _ => rfl) (fun _ _ => rfl) t h Vᵀ

end Conservation

/-! ### The memory count, eq. (2.13) -/

section Memory

/-- The memory (2.13) of the low-rank representation: `2 (m r + r² + n r)` numbers. -/
def lowRankMemory (m n r : ℕ) : ℕ := 2 * (m * r + r ^ 2 + n * r)

/-- The memory `2 m n` of the full-rank solution. -/
def fullMemory (m n : ℕ) : ℕ := 2 * (m * n)

/-- Eq. (2.13) of arXiv 1906.09940 counts the entries of `U`, `S`, `V`, twice. -/
theorem lowRankMemory_eq_card (m n r : ℕ) :
    lowRankMemory m n r =
      2 * Fintype.card ((Fin m × Fin r) ⊕ (Fin r × Fin r) ⊕ (Fin n × Fin r)) := by
  simp only [lowRankMemory, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Exact break-even of arXiv 1906.09940, after (2.13): for `r ≤ m, n` the low-rank form uses less
memory than the full solution iff `2 r² < (m - r) (n - r)`. -/
theorem lowRankMemory_lt_iff {m n r : ℕ} (hm : r ≤ m) (hn : r ≤ n) :
    lowRankMemory m n r < fullMemory m n ↔ 2 * r ^ 2 < (m - r) * (n - r) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [lowRankMemory, fullMemory, Nat.add_sub_cancel_left]
  constructor <;> intro h <;> nlinarith

/-- "For `r ≪ m, n` there will be large memory savings" (arXiv 1906.09940, after (2.13)): if
`r ≤ ρ m` and `r ≤ ρ n`, the memory ratio is at most `2 ρ + ρ²`. -/
theorem lowRankMemory_le_fraction {m n r : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hm : (r : ℝ) ≤ ρ * m)
    (hn : (r : ℝ) ≤ ρ * n) :
    (lowRankMemory m n r : ℝ) ≤ (2 * ρ + ρ ^ 2) * fullMemory m n := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have h1 : (m : ℝ) * r ≤ ρ * (m * n) := by nlinarith
  have h2 : (n : ℝ) * r ≤ ρ * (m * n) := by nlinarith
  have h3 : (r : ℝ) ^ 2 ≤ ρ ^ 2 * (m * n) := by
    have : (r : ℝ) * r ≤ (ρ * m) * (ρ * n) := mul_le_mul hm hn hr0 (by positivity)
    nlinarith
  simp only [lowRankMemory, fullMemory]
  push_cast
  nlinarith

end Memory

/-! ### Galerkin form of the collision terms -/

section Galerkin

variable {m n : ℕ}

/-- arXiv 1906.09940, Sec. 2.1: `C` is the matrix of multiplication by `μ` in the normalised
Legendre basis: `⟨μ (∑_k y_k P_k), P_l⟩_μ = (y C)_l`.  This is the angular part of the `P_N`
streaming term. -/
theorem integral_mu_sum_nLeg (y : Fin n → ℝ) (l : Fin n) :
    ∫ μ in (-1 : ℝ)..1, μ * (∑ k : Fin n, nLeg k μ * y k) * nLeg l μ = (y ᵥ* muMatrix n) l := by
  have e : ∀ μ, μ * (∑ k : Fin n, nLeg k μ * y k) * nLeg l μ =
      ∑ k : Fin n, y k * (μ * nLeg k μ * nLeg l μ) := by
    intro μ
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hI : ∀ k ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
      (fun μ => y k * (μ * nLeg k μ * nLeg l μ)) MeasureTheory.volume (-1) 1 := fun k _ =>
    (nLeg_triple_integrable (fun μ => μ) continuous_id k l).const_mul _
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum hI]
  simp only [intervalIntegral.integral_const_mul, Matrix.vecMul, dotProduct, muMatrix,
    Matrix.of_apply]

variable [NeZero n]

/-- The collision and source operator of (1.1) on a function `ψ(z, μ)`:
`(σs / 2) ∫ ψ dμ' - σt ψ + S / 2`. -/
noncomputable def collisionOp (σs σt S : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ) (z μ : ℝ) : ℝ :=
  σs z / 2 * (∫ μ' in (-1 : ℝ)..1, ψ z μ') - σt z * ψ z μ + S z / 2

/-- **The collision and source terms of the discrete scheme are the Galerkin projection of those
of (1.1)** (arXiv 1906.09940, Secs. 2-2.1): testing `(σs / 2) ∫ ψ dμ' - σt ψ + S / 2` with
`Z_k P_l`, for piecewise constant cross sections and `ψ` with coefficient matrix `Y`, gives
`(diag(σs) Y e₀e₀ᵀ - diag(σt) Y + Q)_kl` with `q_k = ⟨Z_k, S⟩_z`. -/
theorem galerkin_collisionOp {Δz : ℝ} (hΔ : 0 < Δz) (σs σt : Fin m → ℝ) {S : ℝ → ℝ}
    (hS : ∀ k : Fin m, IntervalIntegrable (fun z => cellFn Δz k z * S z) MeasureTheory.volume 0
      ((m : ℝ) * Δz)) (Y : 𝐌[m, n]) (k : Fin m) (l : Fin n) :
    ∫ z in (0 : ℝ)..((m : ℝ) * Δz), ∫ μ in (-1 : ℝ)..1, cellFn Δz k z * nLeg l μ *
        collisionOp (pwConst Δz σs) (pwConst Δz σt) S (expansion Δz Y) z μ =
      (Matrix.diagonal σs * Y * isoProj n - Matrix.diagonal σt * Y +
        (sourceMat fun j : Fin m => ∫ z in (0 : ℝ)..((m : ℝ) * Δz), cellFn Δz j z * S z :
          𝐌[m, n])) k l := by
  have hs0 : √Δz ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  have h20 : √2 ≠ 0 := by positivity
  set δ : ℝ := if l = 0 then 1 else 0 with hδ
  -- the action of cell functions on the expansion
  have hZ : ∀ (c : Fin m → ℝ) (z : ℝ), cellFn Δz k z * ∑ j : Fin m, c j * cellFn Δz j z =
      c k * ((√Δz)⁻¹ * cellFn Δz k z) := by
    intro c z
    rw [Finset.mul_sum, Finset.sum_eq_single k]
    · rw [mul_left_comm, cellFn_mul_self]
    · intro j _ hj
      have hne : (k : ℕ) ≠ j := fun e => hj (Fin.ext e.symm)
      rw [mul_left_comm, cellFn_mul_of_ne hΔ hne, mul_zero]
    · simp
  -- the integral of the expansion
  have hint : ∀ z, ∫ μ in (-1 : ℝ)..1, expansion Δz Y z μ =
      ∑ j : Fin m, (√2 * Y j 0) * cellFn Δz j z := by
    intro z
    have hl : ∀ j ∈ (Finset.univ : Finset (Fin m)), IntervalIntegrable
        (fun μ => ∑ i : Fin n, cellFn Δz j z * Y j i * nLeg i μ) MeasureTheory.volume (-1) 1 := by
      intro j _
      have hc : Continuous fun μ => ∑ i : Fin n, cellFn Δz j z * Y j i * nLeg i μ :=
        continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_nLeg i)
      exact hc.intervalIntegrable _ _
    simp only [expansion]
    rw [intervalIntegral.integral_finsetSum hl]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hl' : ∀ i ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
        (fun μ => cellFn Δz j z * Y j i * nLeg i μ) MeasureTheory.volume (-1) 1 := fun i _ =>
      Continuous.intervalIntegrable (continuous_const.mul (continuous_nLeg i)) _ _
    rw [intervalIntegral.integral_finsetSum hl']
    simp only [intervalIntegral.integral_const_mul, integral_nLeg]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, ite_true]
      ring
    · intro i _ hi0
      have : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext (by simpa using h))
      simp [this]
    · simp
  -- the projection of the expansion on `P_l`
  have hproj : ∀ z, ∫ μ in (-1 : ℝ)..1, nLeg l μ * expansion Δz Y z μ =
      ∑ j : Fin m, Y j l * cellFn Δz j z := by
    intro z
    have e : ∀ μ, nLeg l μ * expansion Δz Y z μ =
        ∑ j : Fin m, ∑ i : Fin n, cellFn Δz j z * Y j i * (nLeg l μ * nLeg i μ) := by
      intro μ
      simp only [expansion, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    simp_rw [e]
    have hl : ∀ j ∈ (Finset.univ : Finset (Fin m)), IntervalIntegrable
        (fun μ => ∑ i : Fin n, cellFn Δz j z * Y j i * (nLeg l μ * nLeg i μ))
        MeasureTheory.volume (-1) 1 := by
      intro j _
      have hc : Continuous fun μ => ∑ i : Fin n, cellFn Δz j z * Y j i * (nLeg l μ * nLeg i μ) :=
        continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_nLeg l).mul (continuous_nLeg i))
      exact hc.intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hl]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hl' : ∀ i ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
        (fun μ => cellFn Δz j z * Y j i * (nLeg l μ * nLeg i μ)) MeasureTheory.volume (-1) 1 :=
      fun i _ => Continuous.intervalIntegrable
        (continuous_const.mul ((continuous_nLeg l).mul (continuous_nLeg i))) _ _
    rw [intervalIntegral.integral_finsetSum hl']
    simp only [intervalIntegral.integral_const_mul, integral_nLeg_mul]
    rw [Finset.sum_eq_single l]
    · simp only [ite_true]
      ring
    · intro i _ hil
      have : (l : ℕ) ≠ i := fun h => hil (Fin.ext h.symm)
      simp [this]
    · simp
  have hmean : ∫ μ in (-1 : ℝ)..1, nLeg l μ = √2 * δ := by
    rw [integral_nLeg, hδ]
    by_cases hl : l = 0
    · simp [hl]
    · have : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext (by simpa using h))
      simp [hl, this]
  -- the inner integral
  have hinner : ∀ z, ∫ μ in (-1 : ℝ)..1, cellFn Δz k z * nLeg l μ *
      collisionOp (pwConst Δz σs) (pwConst Δz σt) S (expansion Δz Y) z μ =
      (√Δz)⁻¹ * (δ * σs k * Y k 0 - σt k * Y k l) * cellFn Δz k z +
        δ * (√2)⁻¹ * (cellFn Δz k z * S z) := by
    intro z
    set φ := ∫ μ' in (-1 : ℝ)..1, expansion Δz Y z μ' with hφ
    have e : ∀ μ, cellFn Δz k z * nLeg l μ *
        collisionOp (pwConst Δz σs) (pwConst Δz σt) S (expansion Δz Y) z μ =
        cellFn Δz k z * (pwConst Δz σs z / 2 * φ + S z / 2) * nLeg l μ -
          cellFn Δz k z * pwConst Δz σt z * (nLeg l μ * expansion Δz Y z μ) := by
      intro μ
      simp only [collisionOp, hφ]
      ring
    simp_rw [e]
    have hc1 : IntervalIntegrable (fun μ => cellFn Δz k z * (pwConst Δz σs z / 2 * φ + S z / 2) *
        nLeg l μ) MeasureTheory.volume (-1) 1 :=
      Continuous.intervalIntegrable (continuous_const.mul (continuous_nLeg l)) _ _
    have hexp : Continuous fun μ => nLeg l μ * expansion Δz Y z μ := by
      simp only [expansion]
      exact (continuous_nLeg l).mul (continuous_finsetSum _ fun j _ =>
        continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_nLeg i))
    have hc2 : IntervalIntegrable (fun μ => cellFn Δz k z * pwConst Δz σt z *
        (nLeg l μ * expansion Δz Y z μ)) MeasureTheory.volume (-1) 1 :=
      Continuous.intervalIntegrable (continuous_const.mul hexp) _ _
    rw [intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hmean, hproj]
    have hs := pwConst_mul_cellFn hΔ σs k z
    have ht := pwConst_mul_cellFn hΔ σt k z
    have hzs : cellFn Δz k z * (pwConst Δz σs z * φ) = σs k * ((√2 * Y k 0) * ((√Δz)⁻¹ *
        cellFn Δz k z)) := by
      rw [← mul_assoc, mul_comm (cellFn Δz k z), hs, mul_assoc, hφ, hint, hZ]
    have hzt : cellFn Δz k z * pwConst Δz σt z * ∑ j : Fin m, Y j l * cellFn Δz j z =
        σt k * (Y k l * ((√Δz)⁻¹ * cellFn Δz k z)) := by
      rw [mul_comm (cellFn Δz k z), ht, mul_assoc, hZ]
    have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have e1 : cellFn Δz k z * (pwConst Δz σs z / 2 * φ + S z / 2) * (√2 * δ) =
        (√2 / 2) * δ * (cellFn Δz k z * (pwConst Δz σs z * φ)) +
          (√2 / 2) * δ * (cellFn Δz k z * S z) := by ring
    rw [e1, hzs, hzt]
    have e2 : √2 / 2 = (√2)⁻¹ := by
      field_simp
      nlinarith
    rw [e2]
    field_simp
    nlinarith
  simp_rw [hinner]
  have hc1 : IntervalIntegrable (fun z => (√Δz)⁻¹ * (δ * σs k * Y k 0 - σt k * Y k l) *
      cellFn Δz k z) MeasureTheory.volume 0 ((m : ℝ) * Δz) :=
    (cellFn_intervalIntegrable Δz k _ _).const_mul _
  rw [intervalIntegral.integral_add hc1 ((hS k).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cellFn hΔ k.2]
  have hfin : (Matrix.diagonal σs * Y * isoProj n - Matrix.diagonal σt * Y +
      (sourceMat fun j : Fin m => ∫ z in (0 : ℝ)..((m : ℝ) * Δz), cellFn Δz j z * S z :
        𝐌[m, n])) k l =
      (δ * σs k * Y k 0 - σt k * Y k l) +
        δ * (√2)⁻¹ * ∫ z in (0 : ℝ)..((m : ℝ) * Δz), cellFn Δz k z * S z := by
    rw [Matrix.add_apply, TransportProblem.coll_apply, hδ]
    by_cases hl : l = 0
    · subst hl
      simp [sourceMat]
      ring
    · simp [sourceMat, hl]
  rw [hfin]
  field_simp

end Galerkin

/-! ### Error bound of the KSL step for the unbounded transport field -/

section KSLTube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {A : ℝ → E} {a b ρ B ε : ℝ}

/-- Not in arXiv 1906.09940; needed since the field of (2.4)-(2.6) is unbounded: One KSL step in the
tube is a step of the extended problem: the KSL analogue of `IsBUGStep.tubeExt`.  If the step starts
at a value `Y₀` with `‖Y₀ - A s‖ + 4 B h < ρ`, then all three substeps stay strictly inside the tube
of radius `ρ` around `A`. -/
theorem kslStep_tubeExt {P₁ Q₀ : E →L[ℝ] E} {Y₀ : E} {YK YS YL : ℝ → E} {s s₁ h : ℝ}
    (hs : IsKSLStep F ε P₁ Q₀ s s₁ Y₀ YK YS YL) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hh : 0 ≤ h) (ha : a ≤ s) (hb : s₁ ≤ b) (ht₁ : s₁ = s + h)
    (hA : ODESolution F A s s₁) (hsmall : ‖Y₀ - A s‖ + 4 * B * h < ρ) :
    IsKSLStep (tubeExt F A a b ρ) ε P₁ Q₀ s s₁ Y₀ YK YS YL := by
  have hd := norm_nonneg (Y₀ - A s)
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hρ : 0 ≤ ρ := by nlinarith
  have hss : s ≤ s₁ := by linarith
  have hFA := hFB.along hρ ha hb
  have hlen : s₁ - s = h := by linarith
  have hPQ : ∀ x, ‖-P₁ (Q₀ x)‖ ≤ ‖x‖ := fun x => by
    rw [norm_neg]
    exact (hs.projP₁.norm_le _).trans (hs.projQ₀.norm_le _)
  -- K-step
  have hKin := tube_trap hA hs.kSol hB hB hFA (hFB.comp_proj ha hb _ hs.projQ₀.norm_le)
    (by rw [hs.kStart, hlen]; nlinarith)
  have hKv := hs.kSol.norm_sub_start_le_of_tube (hFB.comp_proj ha hb _ hs.projQ₀.norm_le) hKin
    s₁ ⟨hss, le_rfl⟩
  rw [hs.kStart, hlen] at hKv
  -- S-step, started at `YK s₁`
  have hS₀ : ‖YS s - A s‖ ≤ ‖Y₀ - A s‖ + B * h := by
    rw [hs.sStart, show YK s₁ - A s = (YK s₁ - Y₀) + (Y₀ - A s) by abel]
    linarith [norm_add_le (YK s₁ - Y₀) (Y₀ - A s)]
  have hSin := tube_trap hA hs.sSol hB hB hFA
    (hFB.comp_proj ha hb (fun x => -P₁ (Q₀ x)) hPQ) (by rw [hlen]; nlinarith)
  have hSv := hs.sSol.norm_sub_start_le_of_tube
    (hFB.comp_proj ha hb (fun x => -P₁ (Q₀ x)) hPQ) hSin s₁ ⟨hss, le_rfl⟩
  rw [hlen] at hSv
  -- L-step, started at `YS s₁`
  have hL₀ : ‖YL s - A s‖ ≤ ‖Y₀ - A s‖ + 2 * (B * h) := by
    rw [hs.lStart, show YS s₁ - A s = (YS s₁ - YS s) + (YS s - A s) by abel]
    linarith [norm_add_le (YS s₁ - YS s) (YS s - A s)]
  have hLin := tube_trap hA hs.lSol hB hB hFA (hFB.comp_proj ha hb _ hs.projP₁.norm_le)
    (by rw [hlen]; nlinarith)
  -- the normal-component point lies in the tube at all times of the step
  have hsub : ∀ t ∈ Icc s s₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hpt : ∀ t ∈ Icc s s₁, ‖YK s₁ - A t‖ ≤ ρ := by
    intro t ht
    have hAt := hA.norm_sub_le hFA t ht
    have hdec : YK s₁ - A t = (YK s₁ - Y₀) + (Y₀ - A s) - (A t - A s) := by abel
    have hle : B * (t - s) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB
    rw [hdec]
    calc _ ≤ ‖(YK s₁ - Y₀) + (Y₀ - A s)‖ + ‖A t - A s‖ := norm_sub_le _ _
      _ ≤ ‖YK s₁ - Y₀‖ + ‖Y₀ - A s‖ + ‖A t - A s‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ρ := by nlinarith
  exact
    { projP₁ := hs.projP₁
      projQ₀ := hs.projQ₀
      kSol := (odeSolution_comp_tubeExt_iff (fun x => Q₀ x) ha hb
        fun t ht => (hKin t (Ico_subset_Icc_self ht)).le).2 hs.kSol
      kStart := hs.kStart
      kCap := hs.kCap
      kNormal := fun t ht => by
        rw [tubeExt_eq (hsub t ht) (hpt t ht)]
        exact hs.kNormal t ht
      sSol := (odeSolution_comp_tubeExt_iff (fun x => -P₁ (Q₀ x)) ha hb
        fun t ht => (hSin t (Ico_subset_Icc_self ht)).le).2 hs.sSol
      sStart := hs.sStart
      lSol := (odeSolution_comp_tubeExt_iff (fun x => P₁ x) ha hb
        fun t ht => (hLin t (Ico_subset_Icc_self ht)).le).2 hs.lSol
      lStart := hs.lStart }

/-- The right-hand side `c₀ δ + c₁ ε + c₂ h` of the robust global bound of the KSL integrator. -/
noncomputable def kslGlobalBound (L B T δ ε h : ℝ) : ℝ :=
  Real.exp (L * T) * δ + T * Real.exp (L * T) * ε + 11 * L * B * T * Real.exp (L * T) * h

/-- Not in arXiv 1906.09940; needed since the field of (2.4)-(2.6) is unbounded: **Robust global
error bound of the KSL integrator for a field that is only bounded on a tube**: the KSL analogue of
`bug_global_error_le_of_tube`.  If the bound `M` of `ksl_global_error_le` satisfies `M + 4 B h < ρ`,
it holds for all steps, with the constants of the tube. -/
theorem ksl_global_error_le_of_tube {L t₀ h : ℝ} {N : ℕ}
    (hFL : IsLipschitzOnTube F A t₀ (t₀ + N * h) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ (t₀ + N * h) ρ B) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YS YL Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsKSLStep F ε (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n) (YL n))
    (hY : ∀ n < N, Y (n + 1) = YL n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ)
    (hNT : N * h ≤ T) (hsmall : kslGlobalBound L B T δ ε h + 4 * B * h < ρ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ kslGlobalBound L B T δ ε h := by
  set M := kslGlobalBound L B T δ ε h with hM
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hM0 : 0 ≤ M := by
    rw [hM, kslGlobalBound]
    positivity
  have hρ : 0 ≤ ρ := by nlinarith
  set G := tubeExt F A t₀ (t₀ + N * h) ρ
  have hGL : IsLipschitzField G L := isLipschitzField_tubeExt hFL hL hρ
  have hGB : IsBoundedField G B := isBoundedField_tubeExt hFB hB hρ
  have hAG : ODESolution G A t₀ (t₀ + N * h) := hA.tubeExt_self hρ
  have hgrid : ∀ n < N, t₀ ≤ t₀ + n * h ∧ t₀ + (n + 1) * h ≤ t₀ + N * h := by
    intro n hn
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    exact ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) n], by nlinarith⟩
  refine bootstrap_of_global (e := fun n => ‖Y n - A (t₀ + n * h)‖) fun m hm hIH => ?_
  have hmN : (m : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hh
  have hAn : ∀ n < m, ODESolution F A (t₀ + n * h) (t₀ + (n + 1) * h) := fun n hn =>
    hA.mono (hgrid n (hn.trans_le hm)).1 (hgrid n (hn.trans_le hm)).2
  have hnear : ∀ n < m, ‖Y n - A (t₀ + n * h)‖ + 4 * B * h < ρ := fun n hn => by
    have := hIH n hn
    linarith
  exact ksl_global_error_le (F := G) hGL hL hGB hε hh (N := m) (A := A)
    (hAG.mono le_rfl (by linarith)) (P := P) (Q := Q) (Y := Y) (YK := YK) (YS := YS) (YL := YL)
    (Φ := Φ)
    (fun n hn => kslStep_tubeExt (hstep n (hn.trans_le hm)) hFB hB hh
      (hgrid n (hn.trans_le hm)).1 (hgrid n (hn.trans_le hm)).2 (by ring) (hAn n hn) (hnear n hn))
    (fun n hn => hY n (hn.trans_le hm))
    (fun n hn => (hΦ n (hn.trans_le hm)).tubeExt_of_near hFB hB hh (hgrid n (hn.trans_le hm)).1
      (hgrid n (hn.trans_le hm)).2 (by ring) (hAn n hn)
      (by rw [hΦ₀ n (hn.trans_le hm)]; nlinarith [hnear n hn]))
    (fun n hn => hΦ₀ n (hn.trans_le hm)) hδ m le_rfl (hmN.trans hNT)

end KSLTube

section TransportError

open scoped LeanDLRA.Frobenius

variable {m n r : ℕ} [NeZero n]

namespace TransportProblem

variable (P : TransportProblem m n)

/-- An explicit Lipschitz constant of the transport field `R` in the Frobenius norm. -/
noncomputable def lip : ℝ :=
  (2 * P.Δz)⁻¹ * (‖P.T - P.Tᵀ‖ * ‖muMatrix n‖ + ‖P.T + P.Tᵀ - (2 : ℝ) • 1‖ * ‖P.D‖) +
    (‖(Matrix.diagonal P.σs : 𝐌[m, m])‖ * ‖isoProj n‖ + ‖(Matrix.diagonal P.σt : 𝐌[m, m])‖)

/-- The Lipschitz constant `lip` is nonnegative. -/
lemma lip_nonneg : 0 ≤ P.lip := by
  have := P.Δz_pos
  unfold lip
  positivity

private lemma op_sub (X Y : 𝐌[m, n]) : P.op X - P.op Y = P.op (X - Y) := by
  simp only [op, streamOp, Matrix.mul_sub, Matrix.sub_mul]
  module

/-- arXiv 1906.09940, (2.4)-(2.6), not in the paper: The linear part of the transport field is
bounded by `lip`. -/
theorem norm_op_le (Y : 𝐌[m, n]) : ‖P.op Y‖ ≤ P.lip * ‖Y‖ := by
  have hΔ := P.Δz_pos
  have h3 : ∀ (A : 𝐌[m, m]) (B : 𝐌[n, n]), ‖A * Y * B‖ ≤ ‖A‖ * ‖B‖ * ‖Y‖ := by
    intro A B
    calc ‖A * Y * B‖ ≤ ‖A * Y‖ * ‖B‖ := Frobenius.norm_mul_le _ _
      _ ≤ ‖A‖ * ‖Y‖ * ‖B‖ := by
        gcongr
        exact Frobenius.norm_mul_le _ _
      _ = _ := by ring
  have hs : ‖streamOp P.T P.Δz (muMatrix n) P.D Y‖ ≤
      (2 * P.Δz)⁻¹ * (‖P.T - P.Tᵀ‖ * ‖muMatrix n‖ + ‖P.T + P.Tᵀ - (2 : ℝ) • 1‖ * ‖P.D‖) * ‖Y‖ := by
    rw [streamOp, norm_smul, norm_neg, Real.norm_of_nonneg (by positivity), mul_assoc]
    gcongr
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add (h3 _ _) (h3 _ _)
      _ = _ := by ring
  have hc : ‖Matrix.diagonal P.σs * Y * isoProj n - Matrix.diagonal P.σt * Y‖ ≤
      (‖(Matrix.diagonal P.σs : 𝐌[m, m])‖ * ‖isoProj n‖ +
        ‖(Matrix.diagonal P.σt : 𝐌[m, m])‖) * ‖Y‖ := by
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add (h3 _ _) (Frobenius.norm_mul_le _ _)
      _ = _ := by ring
  calc ‖P.op Y‖ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hs hc
    _ = P.lip * ‖Y‖ := by rw [lip]; ring

/-- arXiv 1906.09940, (2.4)-(2.6), not in the paper: The transport field `R` is globally Lipschitz
in the Frobenius norm, with constant `lip`.  It is **not** bounded unless `op = 0`, so that
`ksl_global_error_le` does not apply directly. -/
theorem isLipschitzField_field : IsLipschitzField P.field P.lip := fun t x y => by
  have e : P.field t x - P.field t y = P.op (x - y) := by
    rw [field, field, add_sub_add_right_eq_sub, op_sub]
  rw [e]
  exact P.norm_op_le _

/-- arXiv 1906.09940, (2.4)-(2.6), not in the paper: `‖R(t, x)‖ ≤ lip (M + ρ) + Q` on the tube of
radius `ρ` around a curve bounded by `M`, for a source bounded by `Q`. -/
theorem isBoundedOnTube_field {A : ℝ → 𝐌[m, n]} {a b ρ M Q : ℝ}
    (hM : ∀ t ∈ Icc a b, ‖A t‖ ≤ M) (hQ : ∀ t ∈ Icc a b, ‖(sourceMat (P.q t) : 𝐌[m, n])‖ ≤ Q) :
    IsBoundedOnTube P.field A a b ρ (P.lip * (M + ρ) + Q) := fun t ht x hx => by
  have hL := P.lip_nonneg
  have h1 : ‖x‖ ≤ M + ρ := by
    have : ‖x‖ ≤ ‖x - A t‖ + ‖A t‖ := by
      simpa using norm_add_le (x - A t) (A t)
    linarith [hM t ht]
  calc ‖P.field t x‖ ≤ ‖P.op x‖ + ‖(sourceMat (P.q t) : 𝐌[m, n])‖ := norm_add_le _ _
    _ ≤ P.lip * ‖x‖ + Q := add_le_add (P.norm_op_le x) (hQ t ht)
    _ ≤ _ := by gcongr

/-- **Robust error bound of the KSL scheme (2.4)-(2.6) for the transport field** (library form of
Kieri-Lubich-Walach; not in arXiv 1906.09940).  Let `A` solve the full scheme `A' = R(t, A)` with
`‖A‖ ≤ M`, source bounded by `Q`, and let `B = lip (M + ρ) + Q`.  If `Y_k = U_k S_k V_kᵀ` are the
iterates of the exact-substep KSL integrator, the normal component of `R` at the K-step results is
bounded by `ε`, and `c₀ δ + c₁ ε + c₂ h + 4 B h < ρ`, then `‖Y_k - A(t_k)‖ ≤ c₀ δ + c₁ ε + c₂ h`,
with constants independent of the singular values of `Y_k`. -/
theorem ksl_global_error {t₀ h : ℝ} {N : ℕ} {A : ℝ → 𝐌[m, n]} {ρ M Q ε δ T : ℝ}
    (hρ : 0 ≤ ρ) (hM0 : 0 ≤ M) (hQ0 : 0 ≤ Q) (hε0 : 0 ≤ ε) (hh : 0 ≤ h)
    (hA : ODESolution P.field A t₀ (t₀ + N * h))
    (hM : ∀ t ∈ Icc t₀ (t₀ + N * h), ‖A t‖ ≤ M)
    (hQ : ∀ t ∈ Icc t₀ (t₀ + N * h), ‖(sourceMat (P.q t) : 𝐌[m, n])‖ ≤ Q)
    {U U₁ : ℕ → 𝐌[m, r]} {V : ℕ → 𝐌[n, r]} {S Ŝ : ℕ → 𝐌[r, r]} {K : ℕ → ℝ → 𝐌[m, r]}
    {Sf : ℕ → ℝ → 𝐌[r, r]} {Lf : ℕ → ℝ → 𝐌[n, r]} {Φ : ℕ → ℝ → 𝐌[m, n]}
    (hstep : ∀ k < N, MatrixKSL.IsStep P.field (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k)
      (U₁ k) (Ŝ k) (K k) (Sf k) (Lf k))
    (hε : ∀ k < N, ∀ t ∈ Icc (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖(1 - U₁ k * (U₁ k)ᵀ) * P.field t (U₁ k * Ŝ k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hU : ∀ k < N, U (k + 1) = U₁ k)
    (hLQR : ∀ k < N, Lf k (t₀ + (k + 1) * h) = V (k + 1) * (S (k + 1))ᵀ)
    (hΦ : ∀ k < N, ODESolution P.field (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ)
    (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) (hNT : N * h ≤ T)
    (hsmall : kslGlobalBound P.lip (P.lip * (M + ρ) + Q) T δ ε h +
      4 * (P.lip * (M + ρ) + Q) * h < ρ) :
    ∀ k ≤ N, ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      kslGlobalBound P.lip (P.lip * (M + ρ) + Q) T δ ε h := by
  have hL := P.lip_nonneg
  have hB : 0 ≤ P.lip * (M + ρ) + Q := by positivity
  have hLip : IsLipschitzOnTube P.field A t₀ (t₀ + N * h) ρ P.lip :=
    P.isLipschitzField_field.isLipschitzOnTube _ _ _ _
  exact ksl_global_error_le_of_tube (Y := fun k => U k * S k * (V k)ᵀ)
    (P := fun k => leftProj (U₁ k)) (Q := fun k => rightProj (V k))
    (YK := fun k t => K k t * (V k)ᵀ) (YS := fun k t => U₁ k * Sf k t * (V k)ᵀ)
    (YL := fun k t => U₁ k * (Lf k t)ᵀ) hLip hL (P.isBoundedOnTube_field hM hQ) hB hε0 hh hA
    (fun k hk => (hstep k hk).isKSLStep (hε k hk))
    (fun k hk => by
      rw [hU k hk]
      exact (MatrixKSL.IsStep.eq_factored (hLQR k hk)).symm)
    hΦ hΦ₀ hδ hNT hsmall

private lemma exists_sol {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {G : ℝ → E → E} {L a b : ℝ} (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    (hc : ∀ x, Continuous fun t => G t x) (hab : a ≤ b) (y₀ : E) :
    ∃ y, ODESolution G y a b ∧ y a = y₀ := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hc 0).continuousOn
  exact exists_ODESolution_of_linearGrowth hG hL hK (fun x => (hc x).continuousOn) hab y₀

private lemma continuous_sourceMat (hq : Continuous P.q) :
    Continuous fun t => (sourceMat (P.q t) : 𝐌[m, n]) := by
  refine continuous_matrix fun k l => ?_
  simp only [sourceMat, Matrix.of_apply]
  split_ifs
  · exact continuous_const.mul ((continuous_apply k).comp hq)
  · exact continuous_const

/-- **The KSL step for transport is well defined** (arXiv 1906.09940, (2.8)-(2.10) and the QR
factorisations of Sec. 2.1): for a continuous source, `r ≤ m` and orthonormal `V₀`, the three
linear substeps have solutions and the QR step exists, so the hypotheses of `isStep_lift` and
`ksl_global_error` can be met. -/
theorem exists_isStep (hq : Continuous P.q) (hr : r ≤ m) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (U₀ : 𝐌[m, r])
    (S₀ : 𝐌[r, r]) {V₀ : 𝐌[n, r]} (hV : V₀ᵀ * V₀ = 1) :
    ∃ (U₁ : 𝐌[m, r]) (Ŝ₁ : 𝐌[r, r]) (K : ℝ → 𝐌[m, r]) (S : ℝ → 𝐌[r, r]) (Lf : ℝ → 𝐌[n, r]),
      MatrixKSL.IsStep P.field t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf := by
  have hL := P.lip_nonneg
  have hF := P.isLipschitzField_field
  have hFc : ∀ x, Continuous fun t => P.field t x := fun x =>
    continuous_const.add (P.continuous_sourceMat hq)
  -- K-step
  have hKL : IsLipschitzField (MatrixKSL.kField V₀ P.field) P.lip := fun t x y => by
    have e : x * V₀ᵀ - y * V₀ᵀ = (x - y) * V₀ᵀ := (Matrix.sub_mul _ _ _).symm
    calc _ = ‖(P.field t (x * V₀ᵀ) - P.field t (y * V₀ᵀ)) * V₀‖ := by
          simp only [MatrixKSL.kField, Matrix.sub_mul]
      _ ≤ ‖P.field t (x * V₀ᵀ) - P.field t (y * V₀ᵀ)‖ := norm_mul_le_of_orthonormal hV _
      _ ≤ P.lip * ‖x * V₀ᵀ - y * V₀ᵀ‖ := hF t _ _
      _ = P.lip * ‖x - y‖ := by
          rw [e, Frobenius.norm_mul_transpose_of_orthonormal hV]
  obtain ⟨K, hKs, hK0⟩ := exists_sol hKL hL
    (fun x => (Frobenius.rightMulCLM V₀).continuous.comp (hFc (x * V₀ᵀ))) ht (U₀ * S₀)
  obtain ⟨U₁, Ŝ₁, hU, hQR⟩ := MatrixKSL.exists_qr (K t₁) (by simpa using hr)
  -- S-step
  have hSL : IsLipschitzField (MatrixKSL.sField U₁ V₀ P.field) P.lip := fun t x y => by
    have e : U₁ * x * V₀ᵀ - U₁ * y * V₀ᵀ = U₁ * (x - y) * V₀ᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    calc _ = ‖U₁ᵀ * (P.field t (U₁ * x * V₀ᵀ) - P.field t (U₁ * y * V₀ᵀ)) * V₀‖ := by
          simp only [MatrixKSL.sField, Matrix.mul_sub, Matrix.sub_mul]
          rw [← norm_neg]
          congr 1
          abel
      _ ≤ ‖U₁ᵀ * (P.field t (U₁ * x * V₀ᵀ) - P.field t (U₁ * y * V₀ᵀ))‖ :=
          norm_mul_le_of_orthonormal hV _
      _ ≤ ‖P.field t (U₁ * x * V₀ᵀ) - P.field t (U₁ * y * V₀ᵀ)‖ := norm_transpose_mul_le hU _
      _ ≤ P.lip * ‖U₁ * x * V₀ᵀ - U₁ * y * V₀ᵀ‖ := hF t _ _
      _ = P.lip * ‖x - y‖ := by
          rw [e, Frobenius.norm_mul_transpose_of_orthonormal hV,
            Frobenius.norm_mul_of_orthonormal hU]
  obtain ⟨S, hSs, hS0⟩ := exists_sol hSL hL
    (fun x => by
      have h := (Frobenius.leftMulCLM U₁ᵀ).continuous.comp
        ((Frobenius.rightMulCLM V₀).continuous.comp (hFc (U₁ * x * V₀ᵀ)))
      have e : (fun t => MatrixKSL.sField U₁ V₀ P.field t x) =
          fun t => -((Frobenius.leftMulCLM U₁ᵀ) ((Frobenius.rightMulCLM V₀)
            (P.field t (U₁ * x * V₀ᵀ)))) := by
        ext1 t
        simp only [MatrixKSL.sField, Frobenius.leftMulCLM_apply, Frobenius.rightMulCLM_apply,
          Matrix.mul_assoc]
      rw [e]
      exact h.neg) ht Ŝ₁
  -- L-step
  have hLL : IsLipschitzField (MatrixKSL.lField U₁ P.field) P.lip := fun t x y => by
    have e : U₁ * xᵀ - U₁ * yᵀ = U₁ * (x - y)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.mul_sub]
    calc _ = ‖(P.field t (U₁ * xᵀ) - P.field t (U₁ * yᵀ))ᵀ * U₁‖ := by
          simp only [MatrixKSL.lField, Matrix.transpose_sub, Matrix.sub_mul]
      _ ≤ ‖(P.field t (U₁ * xᵀ) - P.field t (U₁ * yᵀ))ᵀ‖ := norm_mul_le_of_orthonormal hU _
      _ = ‖P.field t (U₁ * xᵀ) - P.field t (U₁ * yᵀ)‖ := Frobenius.norm_transpose _
      _ ≤ P.lip * ‖U₁ * xᵀ - U₁ * yᵀ‖ := hF t _ _
      _ = P.lip * ‖x - y‖ := by
          rw [e, Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_transpose]
  obtain ⟨Lf, hLs, hL0⟩ := exists_sol hLL hL
    (fun x => (Frobenius.rightMulCLM U₁).continuous.comp
      (Frobenius.transposeCLM.continuous.comp (hFc (U₁ * xᵀ)))) ht (V₀ * (S t₁)ᵀ)
  exact ⟨U₁, Ŝ₁, K, S, Lf, ⟨hV, hKs, hK0, hU, hQR, hSs, hS0, hLs, hL0⟩⟩

end TransportProblem

/-- arXiv 1906.09940, (2.15)-(2.16): The paper's prefactor of (2.15): for interface *values* `c /
√Δz` of a function with cell coefficients `c`, the factor `1 / √Δz` of `integral_cellFn_deriv`
becomes the factor `1 / Δz` of `streamOp`, which acts on the coefficients. -/
theorem interface_scaling {Δz : ℝ} (hΔ : 0 < Δz) (cp cm : ℝ) :
    (cp / √Δz - cm / √Δz) / √Δz = (cp - cm) / Δz := by
  have hs : √Δz ≠ 0 := (Real.sqrt_pos.2 hΔ).ne'
  have h2 : √Δz * √Δz = Δz := Real.mul_self_sqrt hΔ.le
  rw [← sub_div, div_div, h2]

end TransportError

/-! ### Non-vacuity -/

section Examples

/-- The two-mode recursion matrix: `C = [[0, 1/√3], [1/√3, 0]]`. -/
example : muMatrix 2 = !![0, 1 / √3; 1 / √3, 0] := by
  have h : muOff 0 = 1 / √3 := by norm_num [muOff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [muMatrix_apply, h]

/-- The scheme with zero ghost cells, upwind stabilisation and a purely scattering medium (as in the
plane source problem of arXiv 1906.09940, Sec. 3.1) is admissible. -/
example {m n : ℕ} {Δz : ℝ} (hΔ : 0 < Δz) :
    TransportProblem.IsAdmissible (⟨Δz, hΔ, ghostShift m, absSymm (muMatrix_isHermitian n),
      fun _ => 1, fun _ => 1, fun _ _ => 0⟩ : TransportProblem m n) 1 1 where
  shift := isShift_ghostShift m
  stab := isStabilisation_absSymm_muMatrix n
  a_nonneg := zero_le_one
  b_nonneg := zero_le_one
  σs_nonneg := fun _ => zero_le_one
  σs_le := fun _ => le_rfl
  σt_le := fun _ => le_rfl

end Examples

end LeanDLRA.Literature.P1906_09940
