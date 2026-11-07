import Mathlib

/-!
# Results of arXiv 2305.11532: Implicit Riemannian low-rank schemes for stiff PDEs

The paper (Sutti and Vandereycken, 2023) states no theorems: it presents algorithms and numerical
experiments. Its one formal claim is in Section 6.3: the implicit Euler step
`W_{k+1} = W_k + h G(W_{k+1})`, with `G = ε(AW + WA) + W - W^{∘3}` (equation (6.6)), is the
first-order optimality condition of the variational problem (6.7). This module proves that claim.

* `implicitStepEnergy ε h D wOld` is the functional (6.7) on coefficient vectors `w : ι → ℝ`:
  `F(w) = -(εh/2) w·(D w) + ∑ᵢ ((1-h)/2 wᵢ² + h/4 wᵢ⁴ - wOldᵢ wᵢ)`, with `D` symmetric.
  The Dirichlet term `εh/2 ‖∇w‖²` equals `-(εh/2) ⟨w, Δw⟩`, so `D` plays the role of the
  paper's operator `W ↦ AW + WA` after vectorization. The theorems hold for every symmetric `D`.
  That the vectorized `W ↦ AW + WA` equals `I ⊗ A + A ⊗ I` and is symmetric is not formalized.
  The discrete functional of Appendix A was not read, so this is a generic discretization of (6.7).
* `implicitStep_stationary_iff`: `w` is stationary for `F` (every coordinate derivative vanishes)
  iff `w_i = wOld_i + h (ε (D w)_i + w_i - w_i³)` for every `i`. This is (6.6) coordinatewise,
  with `W_{k+1} = w` and `W_k = wOld`.
* `implicitStep_example`: non-vacuity, for `D = 0` and constant `w = wOld = 1`.

Core definitions: none are used. The paper's objects are matrices with Frobenius structure and a
functional on them, which `LeanDLRA` does not define, so the file uses local definitions on
`ι → ℝ` with `Matrix.mulVec` and `dotProduct`.

Differences from the paper and omissions:
* The paper minimizes over the fixed-rank manifold `M_r` with the Riemannian gradient `P_X ∇F`
  (Sections 4 and 5). This module treats only the ambient, unconstrained first-order condition.
  The Riemannian version is not formalized.
* Not formalized, because the paper does not state them as results:
  - the energy decrease `F(X_{n+1}) + ‖X_{n+1} - X_n‖²/(2h) ≤ F(X_n)` and the existence of a
    minimizer on `M_{≤ r}`;
  - that a trust-region inner solver removes the step-size restriction `h < 1/L_G`. The paper gives
    this restriction for fixed-point iteration only (quoting Kreiss and Rodgers–Venturi), and gives
    no convergence theorem for the Riemannian trust-region method. Riemannian optimization
    convergence theory is also absent from Mathlib.
-/

open Set Filter Topology Finset
open scoped Matrix

namespace LeanDLRA.Literature.P2305_11532

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The functional (6.7) of the paper on coefficient vectors, with a symmetric operator `D`
(the paper's `W ↦ AW + WA`). The Dirichlet part is `-(εh/2) w·(D w)`. -/
noncomputable def implicitStepEnergy (ε h : ℝ) (D : Matrix ι ι ℝ) (wOld w : ι → ℝ) : ℝ :=
  -(ε * h / 2) * (w ⬝ᵥ (D *ᵥ w)) +
    ∑ i, ((1 - h) / 2 * w i ^ 2 + h / 4 * w i ^ 4 - wOld i * w i)

/-- `w` is stationary for `F` when all coordinate derivatives of `F` at `w` vanish. -/
def IsStationaryAt (F : (ι → ℝ) → ℝ) (w : ι → ℝ) : Prop :=
  ∀ i, deriv (fun t : ℝ => F (w + t • Pi.single i 1)) 0 = 0

/-- The gradient of `implicitStepEnergy` at `w`, coordinatewise. -/
noncomputable def implicitStepGrad (ε h : ℝ) (D : Matrix ι ι ℝ) (wOld w : ι → ℝ) : ι → ℝ :=
  fun i => -(ε * h) * (D *ᵥ w) i + (1 - h) * w i + h * w i ^ 3 - wOld i

omit [DecidableEq ι] in
/-- Expansion of the quadratic form along a line, for symmetric `D`. -/
lemma quad_expand (D : Matrix ι ι ℝ) (hD : Dᵀ = D) (w e : ι → ℝ) (t : ℝ) :
    (w + t • e) ⬝ᵥ (D *ᵥ (w + t • e)) =
      w ⬝ᵥ (D *ᵥ w) + 2 * t * (e ⬝ᵥ (D *ᵥ w)) + t ^ 2 * (e ⬝ᵥ (D *ᵥ e)) := by
  have hsym : ∀ x y : ι → ℝ, x ⬝ᵥ (D *ᵥ y) = y ⬝ᵥ (D *ᵥ x) := by
    intro x y
    have hx : x ᵥ* D = D *ᵥ x := by
      rw [← Matrix.vecMul_transpose, hD]
    rw [Matrix.dotProduct_mulVec, hx, dotProduct_comm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hsym w e]
  ring

omit [DecidableEq ι] in
/-- Directional derivative of `implicitStepEnergy` at `w` along `e`: the gradient paired with
`e`. -/
lemma hasDerivAt_energy (ε h : ℝ) (D : Matrix ι ι ℝ) (hD : Dᵀ = D) (wOld w e : ι → ℝ) :
    HasDerivAt (fun t : ℝ => implicitStepEnergy ε h D wOld (w + t • e))
      (implicitStepGrad ε h D wOld w ⬝ᵥ e) 0 := by
  have hA : HasDerivAt (fun t : ℝ => -(ε * h / 2) * ((w + t • e) ⬝ᵥ (D *ᵥ (w + t • e))))
      (-(ε * h / 2) * (2 * (e ⬝ᵥ (D *ᵥ w)))) 0 := by
    have hpoly : HasDerivAt
        (fun t : ℝ => w ⬝ᵥ (D *ᵥ w) + 2 * t * (e ⬝ᵥ (D *ᵥ w)) + t ^ 2 * (e ⬝ᵥ (D *ᵥ e)))
        (2 * (e ⬝ᵥ (D *ᵥ w))) 0 := by
      have h1 := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (e ⬝ᵥ (D *ᵥ w))).const_add
        (w ⬝ᵥ (D *ᵥ w))
      have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (e ⬝ᵥ (D *ᵥ e))
      exact (h1.add h2).congr_deriv (by simp)
    have hfun : (fun t : ℝ => -(ε * h / 2) * ((w + t • e) ⬝ᵥ (D *ᵥ (w + t • e)))) =
        fun t : ℝ => -(ε * h / 2) *
          (w ⬝ᵥ (D *ᵥ w) + 2 * t * (e ⬝ᵥ (D *ᵥ w)) + t ^ 2 * (e ⬝ᵥ (D *ᵥ e))) :=
      funext fun t => by rw [quad_expand D hD]
    rw [hfun]
    exact hpoly.const_mul _
  have hS : HasDerivAt (fun t : ℝ => ∑ j, ((1 - h) / 2 * (w + t • e) j ^ 2 +
      h / 4 * (w + t • e) j ^ 4 - wOld j * (w + t • e) j))
      (∑ j, ((1 - h) * w j * e j + h * w j ^ 3 * e j - wOld j * e j)) 0 := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    have hj : HasDerivAt (fun t : ℝ => w j + t * e j) (e j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e j)).const_add (w j)
    have := (((hj.pow 2).const_mul ((1 - h) / 2)).add ((hj.pow 4).const_mul (h / 4))).sub
      (hj.const_mul (wOld j))
    exact this.congr_deriv (by norm_num; ring)
  have hsum := hA.add hS
  unfold implicitStepEnergy
  convert hsum using 1
  simp only [implicitStepGrad, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Stationarity of the implicit step** (paper, Section 6.3). For symmetric `D`, `w` is a
stationary point of the discrete functional (6.7) iff `w = wOld + h G(w)` coordinatewise, where
`G(w) = ε D w + w - w³` is the right-hand side of the paper's matrix ODE (6.3) and `wOld` is the
previous time level `W_k`. -/
theorem implicitStep_stationary_iff (ε h : ℝ) (D : Matrix ι ι ℝ) (hD : Dᵀ = D)
    (w wOld : ι → ℝ) :
    IsStationaryAt (implicitStepEnergy ε h D wOld) w ↔
      ∀ i, w i = wOld i + h * (ε * (D *ᵥ w) i + w i - w i ^ 3) := by
  have hgrad : IsStationaryAt (implicitStepEnergy ε h D wOld) w ↔
      ∀ i, implicitStepGrad ε h D wOld w i = 0 := by
    unfold IsStationaryAt
    refine forall_congr' fun i => ?_
    rw [(hasDerivAt_energy ε h D hD wOld w (Pi.single i 1)).deriv, dotProduct_single, mul_one]
  rw [hgrad]
  refine forall_congr' fun i => ?_
  simp only [implicitStepGrad]
  constructor <;> intro h' <;> linear_combination h'

/-- Non-vacuity: for `D = 0` and constant `w = wOld = 1`, the implicit step equation holds, so
the stationarity condition is satisfied. -/
theorem implicitStep_example (ε h : ℝ) :
    IsStationaryAt (implicitStepEnergy ε h (0 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => 1))
      (fun _ => 1) :=
  (implicitStep_stationary_iff ε h 0 (by simp) (fun _ => 1) (fun _ => 1)).2 fun i => by simp

end LeanDLRA.Literature.P2305_11532
