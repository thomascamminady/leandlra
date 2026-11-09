import Mathlib
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.GaugeODE

/-!
# Results of arXiv 2306.17526: DLRA for kinetic shear Alfven waves

Formalized from the paper (sections 3.2 and 4). Core definitions reused from the library:
`LeanDLRA.tangentProj` (`LeanDLRA/Matrix/Projectors.lean`), `LeanDLRA.tangentProj_eq_self_iff`,
and `LeanDLRA.GaugeODE.hasDerivAt_factorProduct` (`LeanDLRA/Matrix/GaugeODE.lean`). No new
structures are defined; the module adds only the statements below.

* `chargeDensity_span` (Sec. 3.2, the rank statement behind eq. (8)): with
  `rho(x,z) = 1 - int f(x,z,v) dv` and `f = sum_{i,j} X_i(x) S_ij V_j(z,v)`, the charge
  density is a sum of `r+1` products `B_l(x) C_l(z)`. The paper's orthonormalisation of the
  `V_j` is not used, so the factors are not claimed orthonormal. The integrability of each
  `V_j(z,.)` is assumed, since the integrals `int V_j dv` in the paper are assumed to exist.
* `poisson_of_factors` (Sec. 3.2, `(Laplacian) phi = c rho`): if the `r+1` two-dimensional Poisson
  problems `Delta Phi_l = c B_l` are solved, then `phi(x,z) = sum_l Phi_l(x) C_l(z)` solves
  `Delta phi = c rho` for every `z`. Here `Delta` is any linear map on functions of `x`; the paper's
  Laplacian `d_xx + d_yy` is one instance. Solvability of each Poisson problem is not claimed.
* `tangent_velocity_of_rank_curve` (Sec. 4, exactness in linear theory): if a differentiable curve
  `Y(t) = U(t) S(t) V(t)^T` (rank at most `r`) with orthonormal factors at `t` solves
  `Y' = LIN(Y)` at `t`, then `P(Y) LIN(Y) = LIN(Y)` and `Y` solves the DLRA equation at `t`. The
  paper argues from `f` having rank one; the Lean proof gets the tangency of `Y' = LIN(Y)` from the
  product rule, so it holds for every such curve. The paper's global claim (the dispersion
  relation is reproduced) needs the explicit solution of its appendix A and is not formalized here.

Left out:
* Sec. 3.1, eqs. (5)-(7) (the K, S, L equations with frozen coefficients). Not formalized.
* Sec. 3.4, Alg. 4 (second-order Strang KSL). The paper's second-order claim is cited to
  Einkemmer-Ostermann and is not proved here. The library already has the negative result
  `LeanDLRA.Corrections.StrangNotRobust`, which shows the Strang splitting is not robustly second
  order; this module makes no claim about that scheme.
* Uniqueness of the DLRA solution for a state-dependent projector near `A` (the paper's remark).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix
open MeasureTheory

namespace LeanDLRA.Literature.P2306_17526

/-- **Sec. 3.2, rank of the charge density (core of eq. (8)).** Let
`f(x,z,w) = ∑ᵢⱼ Xᵢ(x) Sᵢⱼ Vⱼ(z,w)` and `ρ(x,z) = 1 - ∫ f(x,z,w) dμ(w)`, where `w` is the velocity
variable. Then `ρ` is a sum of `r + 1` products `B_l(x) C_l(z)`. The `r+1` terms are `1` and the
`-∫ Vⱼ dμ`, weighted by the coefficients `∑ᵢ Xᵢ Sᵢⱼ`. Integrability of each `V j z` is assumed,
since the paper's `⟨V_j⟩_v` are integrals. -/
theorem chargeDensity_span {X Z W : Type*} [MeasurableSpace W] (μ : Measure W) (r : ℕ)
    (Xf : Fin r → X → ℝ) (S : Fin r → Fin r → ℝ) (V : Fin r → Z → W → ℝ)
    (hV : ∀ j z, Integrable (V j z) μ) :
    ∃ (B : Fin (r + 1) → X → ℝ) (C : Fin (r + 1) → Z → ℝ), ∀ x z,
      (1 : ℝ) - ∫ w, ∑ i, ∑ j, Xf i x * S i j * V j z w ∂μ = ∑ l, B l x * C l z := by
  refine ⟨fun l x => (Fin.cons (1 : ℝ) (fun j : Fin r => ∑ i, Xf i x * S i j) : Fin (r + 1) → ℝ) l,
    fun l z => (Fin.cons (1 : ℝ) (fun j : Fin r => -∫ w, V j z w ∂μ) : Fin (r + 1) → ℝ) l, ?_⟩
  intro x z
  have hsum : ∀ w, ∑ i, ∑ j, Xf i x * S i j * V j z w
      = ∑ j, (∑ i, Xf i x * S i j) * V j z w := by
    intro w
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  simp only [hsum]
  rw [integral_finsetSum]
  · simp only [integral_const_mul, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_one,
      mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  · intro j _
    exact (hV j z).const_mul _

/-- **Sec. 3.2, Poisson step.** Let `Δ` be a linear operator on functions of `x` (the paper's
`∂ₓₓ + ∂ᵧᵧ` is an instance), and let `ρ(x,z) = ∑ₗ B_l(x) C_l(z)` as in `chargeDensity_span`.
If each of the `r + 1` two-dimensional problems `Δ Φ_l = c B_l` is solved, then
`φ(x,z) = ∑ₗ Φ_l(x) C_l(z)` solves `Δ φ(·,z) = c ρ(·,z)` for every `z`. -/
theorem poisson_of_factors {X Z : Type*} {r : ℕ} (Δ : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (c : ℝ)
    (B : Fin (r + 1) → X → ℝ) (C : Fin (r + 1) → Z → ℝ) (ρ : X → Z → ℝ)
    (hρ : ∀ x z, ρ x z = ∑ l, B l x * C l z)
    (Φ : Fin (r + 1) → X → ℝ) (hΦ : ∀ l, Δ (Φ l) = c • B l) (z : Z) :
    Δ (fun x => ∑ l, Φ l x * C l z) = fun x => c * ρ x z := by
  have hfun : (fun x => ∑ l, Φ l x * C l z) = ∑ l, C l z • Φ l := by
    funext x
    simp [Finset.sum_apply, smul_eq_mul, mul_comm]
  rw [hfun, map_sum]
  funext x
  simp only [map_smul, hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hρ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **Sec. 4, exactness of DLRA in linear theory (core).** Let `Y(τ) = U(τ) S(τ) V(τ)ᵀ` be a
differentiable curve (rank at most `r`) whose factors `U`, `V` are orthonormal at `t`, and let `Y`
solve `Ẏ = LIN(Y)`
at `t`. Then `P(Y(t)) LIN(Y(t)) = LIN(Y(t))`, so `Y` also solves the DLRA velocity equation
`Ẏ = P(Y) LIN(Y)` at `t`. The projector `P(Y(t))` is `LeanDLRA.tangentProj (U t) (V t)`. `LIN` is an
arbitrary map on matrices: linearity of `LIN` is not used. -/
theorem tangent_velocity_of_rank_curve {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq r] {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ}
    {U' : Matrix m r ℝ} {S' : Matrix r r ℝ} {V' : Matrix n r ℝ} {t : ℝ}
    (LIN : Matrix m n ℝ → Matrix m n ℝ)
    (hU : HasDerivAt U U' t) (hS : HasDerivAt S S' t) (hV : HasDerivAt V V' t)
    (hUo : (U t)ᵀ * U t = 1) (hVo : (V t)ᵀ * V t = 1)
    (hode : HasDerivAt (fun τ => U τ * S τ * (V τ)ᵀ) (LIN (U t * S t * (V t)ᵀ)) t) :
    LeanDLRA.tangentProj (U t) (V t) (LIN (U t * S t * (V t)ᵀ)) = LIN (U t * S t * (V t)ᵀ) ∧
      HasDerivAt (fun τ => U τ * S τ * (V τ)ᵀ)
        (LeanDLRA.tangentProj (U t) (V t) (LIN (U t * S t * (V t)ᵀ))) t := by
  have hd := LeanDLRA.GaugeODE.hasDerivAt_factorProduct hU hS hV
  have hF := hode.unique hd
  have hfix : LeanDLRA.tangentProj (U t) (V t) (LIN (U t * S t * (V t)ᵀ))
      = LIN (U t * S t * (V t)ᵀ) := by
    refine (LeanDLRA.tangentProj_eq_self_iff hUo hVo _).2
      ⟨S' * (V t)ᵀ + S t * V'ᵀ, U' * S t, ?_⟩
    rw [hF]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
    abel
  refine ⟨hfix, ?_⟩
  rw [hfix]
  exact hode

end LeanDLRA.Literature.P2306_17526
