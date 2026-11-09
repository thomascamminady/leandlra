import LeanDLRA.Literature.HighOrder.P2501_06145a
import LeanDLRA.Stability.Energy
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Integrators.EulerBUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2501.06145 (part b): Algorithm 3.3 and the modified energy law (Theorem 3.3)

Continues `LeanDLRA/Literature/HighOrder/P2501_06145a.lean` (the mass-lumped setting `MLFEM`, the
mass product `(·,·)_M`, the linear flow `e^{tℒ}`, Lemmas 2.2–2.4, 3.1, Proposition 3.1 and
Theorem 3.2).  Everything is finite-dimensional: coefficient matrices of the tensor-product finite
element space, with `‖·‖_h = ‖·‖_M`.

## Main definitions

* `MLFEM.IsExpStep`, `MLFEM.IsAugBUGStep`, `MLFEM.IsDLRStep`: Algorithms 3.1, 3.2 and 3.3 in
  relational form.  A generalized QR factorization is a factorization with an `M`-orthonormal
  factor (any number of columns); the truncation is any core of rank `≤ k` within Frobenius
  distance `η` of `S̄₃`, which the SVD truncation of the paper satisfies (`MLFEM.truncation_spec`,
  with the core `EckartYoung.truncation` and the tolerance (3.24)).
* The scaling isometry `MLFEM.half` (`σ(Z) = M_x^{1/2} Z M_y^{1/2}`), the mass norm `MLFEM.mnorm`,
  the `M`-orthogonal Galerkin projector `MLFEM.galProj`, and the conjugated objects `MLFEM.galP`
  (`= leftProj Ũ * rightProj Ṽ`), `MLFEM.conj`, `MLFEM.flowLM`.  They are local because the core
  works with the Frobenius product; `inner_half`, `galP_half`, `isOrthProj_galP`,
  `isLipschitzField_conj_iff` and `galerkinEulerStep_half` bridge them to the core.

## Main results

* `energy_galerkinSSPRK2_le`: an abstract energy law on a real inner product space for a Strang
  step whose nonlinear part is the core Galerkin SSP-RK2 step `w/2 + G(G(w))/2`,
  `G = galerkinEulerStep P N τ` (Shu–Osher form), followed by a truncation.  The proof of
  Theorem 3.3 is this statement; the matrix results are instances through `σ`.
* `mul_galRK_mul` ((3.38)–(3.40)) and `IsDLRStep.galerkin_start` ((3.31)): the matrix form of
  the Galerkin part of Lemma 3.4.
* **Theorem 3.3**: `modEnergy_galerkin_le` and `IsDLRStep.modEnergy_le` with the constants the
  proof gives, `Ẽ^{n+1} + (1/τ - C_g/2) β² ≤ Ẽ^n + (η/τ + (μ₁ + μ₂ + C_N τ μ₁)/2) β`;
  `IsDLRStep.thm_3_3` under the paper's hypotheses (`τ ≤ 1/C_g`, one bound `μ`),
  `IsDLRStep.thm_3_3_of_le_half` in the printed shape with `-β²` (`τ ≤ 1/2`), and
  `IsDLRStep.thm_3_3_classical` for `N(s) = s - s³` with the valid `C_g = 2 + τ`, `τ ≤ 2/5`.
* `IsDLRStep.mass_sub_le`: Theorem 3.2 for Algorithm 3.3 (via part a's `thm_3_2`; its basis
  hypotheses `q_m ∈ range Ū`, `q_n ∈ range V̄` and (3.31) are derived from the step).
* `IsAugBUGStep.half_eq_galerkinEulerStep`: Algorithm 3.2 is the core `galerkinEulerStep` of the
  conjugated problem.  `IsAugBUGStep.mnorm_sub_euler_le` (not in the paper): Algorithm 3.2 deviates
  from the full explicit Euler step by at most `τ` times the doubly `M`-normal component of
  `N(W)`, obtained from the core `matrix_augmentedBug_euler_sub_euler`.
* `not_lipschitz_map_acReaction`: Assumption 3.1 (i), read globally, fails for `s - s³` on every
  nonempty grid.
* Non-vacuity: `oneCell_isDLRStep` and an `example` applying `IsDLRStep.thm_3_3`.

## Differences from the paper

* Theorem 3.3 is proved for a pointwise nonlinearity (the classical equation), as Lemma 2.4 in
  part a.  The conservative equation, whose nonlocal multiplier has no pointwise potential `G`, is
  not covered.  The box bound `|W_{n,1}|, |W_{n+1,1}| ≤ 1` that the definition of `C_g`
  presupposes is a hypothesis.
* The printed (3.36) is `Ẽ^{n+1} ≤ Ẽ^n - β² + (η/τ + (1 + C_N τ) μ/2) β`.  The proof gives the
  quadratic term `-(1/τ - C_g/2) β² ≤ -β²/(2τ)`, which is `≤ -β²` only for `τ ≤ 1/2`; the paper's
  (3.45) has the weaker coefficient `1/(2τ) - g'(ξ)/2`, which `τ ≤ 1/C_g` makes only `≥ 0`, and
  then states `-β²`.  The `μ`-coefficient is `(2 + C_N τ)/2`: Assumption 3.1 (ii) bounds each of
  the two projection errors by `μ`, while the first inequality of the proof uses `μ` for the sum of
  both (the printed constant follows from `IsDLRStep.modEnergy_le` when `μ₁ + μ₂ ≤ μ`).  Whether
  the printed constants hold under the printed hypotheses is not decided here.
* Assumption 3.1 (i) is needed only between the stages `W̄_{n,2} = W_{n,1} + τ P N(W_{n,1})` and
  `W_{n,1} + τ N(W_{n,1})`; its "bounded" part is not used.  Assumption 3.1 (ii) is used at
  `W_{n,1}` and `W̄_{n,2}`, as in the proof.

Not formalized: Lemmas 3.2 and 3.3 (operation counts), the finite element form of Lemma 3.4, and
Remark 3.6 (asymptotic heuristics).
-/

open Set Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2501_06145

open NormedSpace (exp)
open Matrix

/-! ### An abstract energy law for a Strang step with a Galerkin SSP-RK2 substep -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Energy law of a Strang step whose nonlinear part is a Galerkin SSP-RK2 step followed by a
truncation** (the abstract core of arXiv 2501.06145, Theorem 3.3).  On a real inner product space
let `P` be an orthogonal projector with `P w = w` (the Galerkin space contains the start value),
let the SSP-RK2 step in Shu–Osher form be built from the core Galerkin Euler steps,
`W̄₃ = w/2 + G(G(w))/2`, `G = galerkinEulerStep P N τ`, let `W₃` be its truncation with
`‖W̄₃ - W₃‖ ≤ η`, and let `A W' = W₃`, where `A` is linear, symmetric and `A ≥ 1`
(`A = e^{-τε²ℒ}`, so `W' = e^{τε²ℒ} W₃`).  Let `μ₁`, `μ₂` bound the projection errors of `N` at
the two stages, let `N` be `C_N`-Lipschitz between the Galerkin stage `G(w)` and the full stage
`w + τ N(w)`, and let the potential `Φ` satisfy the Taylor bound
`Φ(W') - Φ(w) ≤ (g(w), W' - w) + (C_g/2)‖W' - w‖²` with `g(w) = -(N(w) + N(w + τN(w)))/2`
((2.34)).  Then the modified energy `Ẽ(x) = (1/2τ)((A - 1)x, x) + Φ(x)` satisfies
`Ẽ(W') + (1/τ - C_g/2)‖W' - w‖² ≤ Ẽ(w) + (η/τ + (μ₁ + μ₂ + C_N τ μ₁)/2)‖W' - w‖`. -/
theorem energy_galerkinSSPRK2_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {A : E →ₗ[ℝ] E}
    (hAs : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (hA : ∀ x, ‖x‖ ^ 2 ≤ ⟪A x, x⟫) {N : E → E}
    {CN Cg τ η μ₁ μ₂ : ℝ} (Φ : E → ℝ) (hτ : 0 < τ) (hCN : 0 ≤ CN) {w W₃ w' : E}
    (hw : P w = w)
    (hN : ‖N (galerkinEulerStep P N τ w) - N (eulerStep N τ w)‖ ≤
      CN * ‖galerkinEulerStep P N τ w - eulerStep N τ w‖)
    (hμ₁ : ‖P (N w) - N w‖ ≤ μ₁)
    (hμ₂ : ‖P (N (galerkinEulerStep P N τ w)) - N (galerkinEulerStep P N τ w)‖ ≤ μ₂)
    (htr : ‖(1 / 2 : ℝ) • w + (1 / 2 : ℝ) • galerkinEulerStep P N τ (galerkinEulerStep P N τ w) -
      W₃‖ ≤ η)
    (hback : A w' = W₃)
    (hΦ : Φ w' - Φ w ≤ ⟪-(1 / 2 : ℝ) • (N w + N (eulerStep N τ w)), w' - w⟫ +
      Cg / 2 * ‖w' - w‖ ^ 2) :
    1 / (2 * τ) * ⟪A w' - w', w'⟫ + Φ w' + (1 / τ - Cg / 2) * ‖w' - w‖ ^ 2 ≤
      1 / (2 * τ) * ⟪A w - w, w⟫ + Φ w +
        (η / τ + (μ₁ + μ₂ + CN * τ * μ₁) / 2) * ‖w' - w‖ := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hy : galerkinEulerStep P N τ w = w + τ • P (N w) := by
    rw [galerkinEulerStep, eulerStep, hw, map_add, map_smul, hw]
  set y := galerkinEulerStep P N τ w
  have hPy : P y = y := by rw [hy, map_add, map_smul, hw, hP.idem]
  have hz : galerkinEulerStep P N τ y = y + τ • P (N y) := by
    rw [galerkinEulerStep, eulerStep, hPy, map_add, map_smul, hPy]
  set X := (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • galerkinEulerStep P N τ y with hX
  have hinc : X - w = (τ / 2) • (P (N w) + P (N y)) := by
    rw [hX, hz, hy]; module
  set d := w' - w with hd
  have hw' : w' = w + d := by rw [hd]; abel
  -- the quadratic part
  have hQ : ⟪A w' - w', w'⟫ - ⟪A w - w, w⟫ = 2 * ⟪A w' - w', d⟫ - (⟪A d, d⟫ - ⟪d, d⟫) := by
    have e1 : ⟪A d, w⟫ = ⟪A w, d⟫ := by rw [hAs, real_inner_comm]
    have e2 : ⟪d, w⟫ = ⟪w, d⟫ := real_inner_comm _ _
    rw [hw', map_add]
    simp only [inner_add_left, inner_add_right, inner_sub_left]
    linarith [e1, e2]
  have hX0 : ‖d‖ ^ 2 ≤ ⟪A d, d⟫ := hA d
  have hdd : ⟪d, d⟫ = ‖d‖ ^ 2 := real_inner_self_eq_norm_sq d
  -- testing the step with `d`
  have hsplit : X - w = (X - W₃) + (A w' - w') + d := by rw [hback, hd]; abel
  have hI := congrArg (fun v => ⟪v, d⟫) hsplit
  simp only [inner_add_left] at hI
  rw [hinc, real_inner_smul_left, inner_add_left] at hI
  have hb1 : ⟪P (N w), d⟫ ≤ ⟪N w, d⟫ + μ₁ * ‖d‖ := by
    have h := real_inner_le_norm (P (N w) - N w) d
    rw [inner_sub_left] at h
    linarith [mul_le_mul_of_nonneg_right hμ₁ (norm_nonneg d)]
  have hye : y - eulerStep N τ w = τ • (P (N w) - N w) := by
    rw [hy, eulerStep, smul_sub]; abel
  have hNy : ‖N y - N (eulerStep N τ w)‖ ≤ CN * τ * μ₁ := by
    calc ‖N y - N (eulerStep N τ w)‖ ≤ CN * ‖y - eulerStep N τ w‖ := hN
      _ = CN * (τ * ‖P (N w) - N w‖) := by rw [hye, norm_smul, Real.norm_of_nonneg hτ.le]
      _ ≤ CN * (τ * μ₁) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ₁ hτ.le) hCN
      _ = CN * τ * μ₁ := by ring
  have hb2 : ⟪P (N y), d⟫ ≤ ⟪N (eulerStep N τ w), d⟫ + (μ₂ + CN * τ * μ₁) * ‖d‖ := by
    have h1 := real_inner_le_norm (P (N y) - N y) d
    have h2 := real_inner_le_norm (N y - N (eulerStep N τ w)) d
    rw [inner_sub_left] at h1 h2
    have h3 := mul_le_mul_of_nonneg_right hμ₂ (norm_nonneg d)
    have h4 := mul_le_mul_of_nonneg_right hNy (norm_nonneg d)
    linarith
  have hb3 : -⟪X - W₃, d⟫ ≤ η * ‖d‖ := by
    have h := abs_real_inner_le_norm (X - W₃) d
    have h' := mul_le_mul_of_nonneg_right htr (norm_nonneg d)
    have h'' := neg_le_abs ⟪X - W₃, d⟫
    linarith
  rw [real_inner_smul_left, inner_add_left] at hΦ
  have key : ⟪A w' - w', w'⟫ - ⟪A w - w, w⟫ ≤ τ * (⟪N w, d⟫ + ⟪N (eulerStep N τ w), d⟫) +
      τ * ((μ₁ + μ₂ + CN * τ * μ₁) * ‖d‖) + 2 * (η * ‖d‖) - 2 * ‖d‖ ^ 2 := by
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hτ.le
    linarith
  have hdiv := mul_le_mul_of_nonneg_left key (show 0 ≤ 1 / (2 * τ) by positivity)
  have e : 1 / (2 * τ) * (τ * (⟪N w, d⟫ + ⟪N (eulerStep N τ w), d⟫) +
      τ * ((μ₁ + μ₂ + CN * τ * μ₁) * ‖d‖) + 2 * (η * ‖d‖) - 2 * ‖d‖ ^ 2) =
      (⟪N w, d⟫ + ⟪N (eulerStep N τ w), d⟫) / 2 + (μ₁ + μ₂ + CN * τ * μ₁) / 2 * ‖d‖ +
        η / τ * ‖d‖ - 1 / τ * ‖d‖ ^ 2 := by
    field_simp [hτ0]
  rw [e] at hdiv
  have hms := mul_sub (1 / (2 * τ)) ⟪A w' - w', w'⟫ ⟪A w - w, w⟫
  linarith

end Abstract

namespace MLFEM

/-! ### The mass norm and the scaling isometry `Z ↦ M_x^{1/2} Z M_y^{1/2}` -/

section MassNorm

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (D : MLFEM ι κ)

/-- The mass norm `‖Z‖_M = (Z, Z)_M^{1/2}` (the norm `‖·‖_h` of arXiv 2501.06145). -/
noncomputable def mnorm (Z : Matrix ι κ ℝ) : ℝ := √(D.mip Z Z)

/-- `‖Z‖_M² = (Z, Z)_M`. -/
theorem mnorm_sq (Z : Matrix ι κ ℝ) : D.mnorm Z ^ 2 = D.mip Z Z :=
  Real.sq_sqrt (D.mip_self_nonneg Z)

/-- `‖Z‖_M ≥ 0`. -/
theorem mnorm_nonneg (Z : Matrix ι κ ℝ) : 0 ≤ D.mnorm Z := Real.sqrt_nonneg _

/-- Pointwise second-order Taylor bound for the potential `(G(w), 𝐈)_M` of the modified energy
(the step (A.4)/(3.45) of arXiv 2501.06145): if the entries of `w`, `w'` lie in `[-1, 1]` and
`|g'| ≤ C_g` there, then
`(G(w'), 𝐈)_M ≤ (G(w), 𝐈)_M + (g(w), w' - w)_M + (C_g/2)‖w' - w‖²_M`. -/
theorem mass_map_Gfun_le {n : ℝ → ℝ} (hn : Differentiable ℝ n) (F0 Cg τ : ℝ)
    (hCg : ∀ s ∈ Set.Icc (-1 : ℝ) 1, |deriv (gfun n τ) s| ≤ Cg) {w w' : Matrix ι κ ℝ}
    (h1 : ∀ i j, w i j ∈ Set.Icc (-1 : ℝ) 1) (h2 : ∀ i j, w' i j ∈ Set.Icc (-1 : ℝ) 1) :
    D.mass (w'.map (Gfun n τ F0)) ≤ D.mass (w.map (Gfun n τ F0)) +
      D.mip (w.map (gfun n τ)) (w' - w) + Cg / 2 * D.mip (w' - w) (w' - w) := by
  have hGd : ∀ x, HasDerivAt (Gfun n τ F0) (gfun n τ x) x := hasDerivAt_Gfun hn τ F0
  have hle : ∀ i j, Gfun n τ F0 (w' i j) ≤ Gfun n τ F0 (w i j) +
      gfun n τ (w i j) * (w' - w) i j + Cg / 2 * (w' - w) i j ^ 2 := by
    intro i j
    have := sub_le_taylor hGd (differentiable_gfun hn τ) hCg (h1 i j) (h2 i j)
    rw [Matrix.sub_apply]
    linarith
  calc D.mass (w'.map (Gfun n τ F0))
      = ∑ i, ∑ j, D.mx i * D.my j * Gfun n τ F0 (w' i j) := by
        simp [mass, mip, ones]
    _ ≤ ∑ i, ∑ j, D.mx i * D.my j * (Gfun n τ F0 (w i j) + gfun n τ (w i j) * (w' - w) i j +
          Cg / 2 * (w' - w) i j ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hle i j) (mul_pos (D.mx_pos i) (D.my_pos j)).le
    _ = _ := by
        simp only [mass, mip, ones, of_apply, Matrix.map_apply, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `‖c Z‖_M = |c| ‖Z‖_M`. -/
theorem mnorm_smul (c : ℝ) (Z : Matrix ι κ ℝ) : D.mnorm (c • Z) = |c| * D.mnorm Z := by
  rw [mnorm, mnorm, D.mip_smul_left, D.mip_smul_right, ← mul_assoc, Real.sqrt_mul' _
    (D.mip_self_nonneg Z), Real.sqrt_mul_self_eq_abs]

end MassNorm

section Scaling

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (D : MLFEM ι κ)

omit [DecidableEq κ] in
/-- `M_x^{1/2} = diag(√mx)`. -/
noncomputable def sqx : Matrix ι ι ℝ := diagonal fun i => √(D.mx i)

omit [DecidableEq ι] in
/-- `M_y^{1/2} = diag(√my)`. -/
noncomputable def sqy : Matrix κ κ ℝ := diagonal fun j => √(D.my j)

omit [DecidableEq κ] in
/-- `M_x^{-1/2}`. -/
noncomputable def sqxInv : Matrix ι ι ℝ := diagonal fun i => (√(D.mx i))⁻¹

omit [DecidableEq ι] in
/-- `M_y^{-1/2}`. -/
noncomputable def sqyInv : Matrix κ κ ℝ := diagonal fun j => (√(D.my j))⁻¹

omit [DecidableEq κ] in
/-- `M_x^{1/2} M_x^{1/2} = M_x`. -/
theorem sqx_mul_sqx : D.sqx * D.sqx = D.Mx := by
  rw [sqx, diagonal_mul_diagonal, Mx]
  congr 1
  funext i
  exact Real.mul_self_sqrt (D.mx_pos i).le

omit [DecidableEq ι] in
/-- `M_y^{1/2} M_y^{1/2} = M_y`. -/
theorem sqy_mul_sqy : D.sqy * D.sqy = D.My := by
  rw [sqy, diagonal_mul_diagonal, My]
  congr 1
  funext j
  exact Real.mul_self_sqrt (D.my_pos j).le

omit [DecidableEq κ] in
/-- `M_x^{1/2} (M_x^{1/2} X) = M_x X`. -/
theorem sqx_mul_sqx_mul {α : Type*} (X : Matrix ι α ℝ) : D.sqx * (D.sqx * X) = D.Mx * X := by
  rw [← Matrix.mul_assoc, sqx_mul_sqx]

omit [DecidableEq ι] in
/-- `M_y^{1/2} (M_y^{1/2} X) = M_y X`. -/
theorem sqy_mul_sqy_mul {α : Type*} (X : Matrix κ α ℝ) : D.sqy * (D.sqy * X) = D.My * X := by
  rw [← Matrix.mul_assoc, sqy_mul_sqy]

omit [DecidableEq κ] in
/-- `M_x^{-1/2} M_x^{1/2} = 1`. -/
theorem sqxInv_mul_sqx : D.sqxInv * D.sqx = 1 := by
  rw [sqxInv, sqx, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (D.mx_pos i)).ne'

omit [DecidableEq κ] in
/-- `M_x^{1/2} M_x^{-1/2} = 1`. -/
theorem sqx_mul_sqxInv : D.sqx * D.sqxInv = 1 := by
  rw [sqxInv, sqx, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (D.mx_pos i)).ne'

omit [DecidableEq ι] in
/-- `M_y^{-1/2} M_y^{1/2} = 1`. -/
theorem sqyInv_mul_sqy : D.sqyInv * D.sqy = 1 := by
  rw [sqyInv, sqy, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (D.my_pos j)).ne'

omit [DecidableEq ι] in
/-- `M_y^{1/2} M_y^{-1/2} = 1`. -/
theorem sqy_mul_sqyInv : D.sqy * D.sqyInv = 1 := by
  rw [sqyInv, sqy, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (D.my_pos j)).ne'

omit [DecidableEq κ] in
/-- `M_x^{1/2}` is symmetric. -/
theorem sqx_transpose : D.sqxᵀ = D.sqx := diagonal_transpose _

omit [DecidableEq ι] in
/-- `M_y^{1/2}` is symmetric. -/
theorem sqy_transpose : D.sqyᵀ = D.sqy := diagonal_transpose _

/-- The **mass-scaling isometry** `σ(Z) = M_x^{1/2} Z M_y^{1/2}`: it carries the mass product
`(·,·)_M` to the Frobenius product (`inner_half`), and the `M`-weighted Galerkin projector to the
core Galerkin projector `leftProj * rightProj` (`galP_half`). -/
noncomputable def half (Z : Matrix ι κ ℝ) : Matrix ι κ ℝ := D.sqx * Z * D.sqy

/-- The inverse `σ⁻¹(Z) = M_x^{-1/2} Z M_y^{-1/2}` of the scaling isometry. -/
noncomputable def halfInv (Z : Matrix ι κ ℝ) : Matrix ι κ ℝ := D.sqxInv * Z * D.sqyInv

/-- Entries of `σ(Z)`. -/
theorem half_apply (Z : Matrix ι κ ℝ) (i : ι) (j : κ) :
    D.half Z i j = √(D.mx i) * Z i j * √(D.my j) := by
  rw [half, sqx, sqy, mul_diagonal, diagonal_mul]

/-- `σ⁻¹ σ = id`. -/
theorem halfInv_half (Z : Matrix ι κ ℝ) : D.halfInv (D.half Z) = Z := by
  rw [halfInv, half]
  calc D.sqxInv * (D.sqx * Z * D.sqy) * D.sqyInv =
        (D.sqxInv * D.sqx) * Z * (D.sqy * D.sqyInv) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [sqxInv_mul_sqx, sqy_mul_sqyInv, Matrix.one_mul, Matrix.mul_one]

/-- `σ σ⁻¹ = id`. -/
theorem half_halfInv (Z : Matrix ι κ ℝ) : D.half (D.halfInv Z) = Z := by
  rw [halfInv, half]
  calc D.sqx * (D.sqxInv * Z * D.sqyInv) * D.sqy =
        (D.sqx * D.sqxInv) * Z * (D.sqyInv * D.sqy) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [sqx_mul_sqxInv, sqyInv_mul_sqy, Matrix.one_mul, Matrix.mul_one]

/-- `σ` is additive. -/
theorem half_add (A B : Matrix ι κ ℝ) : D.half (A + B) = D.half A + D.half B := by
  simp only [half, Matrix.mul_add, Matrix.add_mul]

/-- `σ` is subtractive. -/
theorem half_sub (A B : Matrix ι κ ℝ) : D.half (A - B) = D.half A - D.half B := by
  simp only [half, Matrix.mul_sub, Matrix.sub_mul]

/-- `σ` is homogeneous. -/
theorem half_smul (c : ℝ) (A : Matrix ι κ ℝ) : D.half (c • A) = c • D.half A := by
  simp only [half, Matrix.mul_smul, Matrix.smul_mul]

/-- `σ⁻¹` is additive. -/
theorem halfInv_add (A B : Matrix ι κ ℝ) : D.halfInv (A + B) = D.halfInv A + D.halfInv B := by
  simp only [halfInv, Matrix.mul_add, Matrix.add_mul]

/-- `σ⁻¹` is homogeneous. -/
theorem halfInv_smul (c : ℝ) (A : Matrix ι κ ℝ) : D.halfInv (c • A) = c • D.halfInv A := by
  simp only [halfInv, Matrix.mul_smul, Matrix.smul_mul]

variable {p q : Type*} [Fintype p] [Fintype q]

/-- The `M`-orthogonal **Galerkin projector** `Z ↦ Ū Ūᵀ M_x Z M_y V̄ V̄ᵀ` onto `{Ū S V̄ᵀ}`
(arXiv 2501.06145, (3.33), (3.41): `Ū_p Z V̄_p`). -/
noncomputable def galProj (Ub : Matrix ι p ℝ) (Vb : Matrix κ q ℝ) (Z : Matrix ι κ ℝ) :
    Matrix ι κ ℝ :=
  Ub * Ubᵀ * D.Mx * Z * D.My * Vb * Vbᵀ

/-- The Galerkin projector is additive. -/
theorem galProj_add (Ub : Matrix ι p ℝ) (Vb : Matrix κ q ℝ) (A B : Matrix ι κ ℝ) :
    D.galProj Ub Vb (A + B) = D.galProj Ub Vb A + D.galProj Ub Vb B := by
  simp only [galProj, Matrix.mul_add, Matrix.add_mul]

/-- The Galerkin projector is homogeneous. -/
theorem galProj_smul (Ub : Matrix ι p ℝ) (Vb : Matrix κ q ℝ) (c : ℝ) (A : Matrix ι κ ℝ) :
    D.galProj Ub Vb (c • A) = c • D.galProj Ub Vb A := by
  simp only [galProj, Matrix.mul_smul, Matrix.smul_mul]

/-- The Galerkin projector fixes `Ū S V̄ᵀ` for `M`-orthonormal `Ū`, `V̄`. -/
theorem galProj_mul_mul [DecidableEq p] [DecidableEq q] {Ub : Matrix ι p ℝ} {Vb : Matrix κ q ℝ}
    (hUb : Ubᵀ * D.Mx * Ub = 1) (hVb : Vbᵀ * D.My * Vb = 1) (S : Matrix p q ℝ) :
    D.galProj Ub Vb (Ub * S * Vbᵀ) = Ub * S * Vbᵀ := by
  have e : D.galProj Ub Vb (Ub * S * Vbᵀ) =
      Ub * (Ubᵀ * D.Mx * Ub) * S * (Vbᵀ * D.My * Vb)ᵀ * Vbᵀ := by
    simp only [galProj, transpose_mul, transpose_transpose, D.My_transpose, Matrix.mul_assoc]
  rw [e, hUb, hVb, transpose_one, Matrix.mul_one, Matrix.mul_one]

/-- The Galerkin projector is idempotent. -/
theorem galProj_galProj [DecidableEq p] [DecidableEq q] {Ub : Matrix ι p ℝ} {Vb : Matrix κ q ℝ}
    (hUb : Ubᵀ * D.Mx * Ub = 1) (hVb : Vbᵀ * D.My * Vb = 1) (Z : Matrix ι κ ℝ) :
    D.galProj Ub Vb (D.galProj Ub Vb Z) = D.galProj Ub Vb Z := by
  have e : D.galProj Ub Vb Z = Ub * (Ubᵀ * D.Mx * Z * D.My * Vb) * Vbᵀ := by
    simp only [galProj, Matrix.mul_assoc]
  rw [e, D.galProj_mul_mul hUb hVb]

/-- Lifting the Galerkin right-hand side: `Ū (ŪᵀM_x N(ŪSV̄ᵀ) M_y V̄) V̄ᵀ = P(N(ŪSV̄ᵀ))`. -/
theorem mul_galS_mul (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (Ub : Matrix ι p ℝ) (Vb : Matrix κ q ℝ)
    (S : Matrix p q ℝ) : Ub * D.galS N Ub Vb S * Vbᵀ = D.galProj Ub Vb (N (Ub * S * Vbᵀ)) := by
  simp only [galS, galProj, Matrix.mul_assoc]

/-- **(3.38)–(3.40)** (arXiv 2501.06145): the lifted SSP-RK2 Galerkin step
`Ū S̄₃ V̄ᵀ = W/2 + (W̄₂ + τ P N(W̄₂))/2` with `W = Ū S̄₁ V̄ᵀ` and `W̄₂ = W + τ P N(W)`. -/
theorem mul_galRK_mul (τ : ℝ) (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (Ub : Matrix ι p ℝ)
    (Vb : Matrix κ q ℝ) (S : Matrix p q ℝ) :
    Ub * D.galRK τ N Ub Vb S * Vbᵀ =
      (1 / 2 : ℝ) • (Ub * S * Vbᵀ) + (1 / 2 : ℝ) •
        ((Ub * S * Vbᵀ + τ • D.galProj Ub Vb (N (Ub * S * Vbᵀ))) +
          τ • D.galProj Ub Vb (N (Ub * S * Vbᵀ + τ • D.galProj Ub Vb (N (Ub * S * Vbᵀ))))) := by
  have h1 := D.mul_galS_mul N Ub Vb S
  have h2 := D.mul_galS_mul N Ub Vb (S + τ • D.galS N Ub Vb S)
  have h3 : Ub * (S + τ • D.galS N Ub Vb S) * Vbᵀ =
      Ub * S * Vbᵀ + τ • D.galProj Ub Vb (N (Ub * S * Vbᵀ)) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1]
  rw [h3] at h2
  rw [galRK]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, h2]
  module

/-- The nonlinearity conjugated by the scaling isometry, `σ ∘ N ∘ σ⁻¹`. -/
noncomputable def conj (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (X : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  D.half (N (D.halfInv X))

/-- `σ ∘ N ∘ σ⁻¹ ∘ σ = σ ∘ N`. -/
theorem conj_half (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (X : Matrix ι κ ℝ) :
    D.conj N (D.half X) = D.half (N X) := by
  rw [conj, halfInv_half]

/-- The linear flow `e^{tℒ}` conjugated by the scaling isometry, as a linear map. -/
noncomputable def flowLM (t : ℝ) : Matrix ι κ ℝ →ₗ[ℝ] Matrix ι κ ℝ where
  toFun X := D.half (D.flow t (D.halfInv X))
  map_add' X Y := by simp only [halfInv_add, flow_add, half_add]
  map_smul' c X := by simp only [halfInv_smul, flow_smul, half_smul, RingHom.id_apply]

/-- `σ e^{tℒ} σ⁻¹ σ = σ e^{tℒ}`. -/
theorem flowLM_half (t : ℝ) (X : Matrix ι κ ℝ) : D.flowLM t (D.half X) = D.half (D.flow t X) := by
  change D.half (D.flow t (D.halfInv (D.half X))) = _
  rw [halfInv_half]

section Isometry

open scoped LeanDLRA.Frobenius

/-- **The scaling isometry**: `⟪σA, σB⟫_F = (A, B)_M`. -/
theorem inner_half (A B : Matrix ι κ ℝ) : ⟪D.half A, D.half B⟫ = D.mip A B := by
  rw [Frobenius.inner_def, mip]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [half_apply, half_apply]
  have hx := Real.mul_self_sqrt (D.mx_pos i).le
  have hy := Real.mul_self_sqrt (D.my_pos j).le
  calc √(D.mx i) * A i j * √(D.my j) * (√(D.mx i) * B i j * √(D.my j))
      = (√(D.mx i) * √(D.mx i)) * (√(D.my j) * √(D.my j)) * A i j * B i j := by ring
    _ = D.mx i * D.my j * A i j * B i j := by rw [hx, hy]

/-- `‖σA‖_F² = ‖A‖²_M`. -/
theorem norm_half_sq (A : Matrix ι κ ℝ) : ‖D.half A‖ ^ 2 = D.mip A A := by
  rw [← real_inner_self_eq_norm_sq, inner_half]

/-- `‖σA‖_F = ‖A‖_M`. -/
theorem norm_half (A : Matrix ι κ ℝ) : ‖D.half A‖ = D.mnorm A := by
  rw [mnorm, ← norm_half_sq, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq κ] [Fintype p] in
/-- `M`-orthonormal bases become Frobenius-orthonormal after scaling: `(M_x^{1/2}Ū)ᵀ(M_x^{1/2}Ū)
= ŪᵀM_xŪ`. -/
theorem sqx_mul_orthonormal [DecidableEq p] {Ub : Matrix ι p ℝ} (hUb : Ubᵀ * D.Mx * Ub = 1) :
    (D.sqx * Ub)ᵀ * (D.sqx * Ub) = 1 := by
  simp only [transpose_mul, sqx_transpose, Matrix.mul_assoc, sqx_mul_sqx_mul]
  rw [← Matrix.mul_assoc, hUb]

omit [DecidableEq ι] [Fintype q] in
/-- `M`-orthonormal bases become Frobenius-orthonormal after scaling (right factor). -/
theorem sqy_mul_orthonormal [DecidableEq q] {Vb : Matrix κ q ℝ} (hVb : Vbᵀ * D.My * Vb = 1) :
    (D.sqy * Vb)ᵀ * (D.sqy * Vb) = 1 := by
  simp only [transpose_mul, sqy_transpose, Matrix.mul_assoc, sqy_mul_sqy_mul]
  rw [← Matrix.mul_assoc, hVb]

/-- The core Galerkin projector `leftProj Ũ * rightProj Ṽ` (`X ↦ Ũ Ũᵀ X Ṽ Ṽᵀ`) of the scaled
bases `Ũ = M_x^{1/2} Ū`, `Ṽ = M_y^{1/2} V̄`. -/
noncomputable def galP (Ub : Matrix ι p ℝ) (Vb : Matrix κ q ℝ) :
    Matrix ι κ ℝ →L[ℝ] Matrix ι κ ℝ :=
  leftProj (D.sqx * Ub) * rightProj (D.sqy * Vb)

/-- **Bridge to the core projectors**: the scaling isometry conjugates the `M`-weighted Galerkin
projector to the core Galerkin projector,
`σ(Ū ŪᵀM_x Z M_y V̄ V̄ᵀ) = (leftProj Ũ * rightProj Ṽ)(σZ)`. -/
theorem galP_half (Ub : Matrix ι p ℝ) (Vb : Matrix κ q ℝ) (Z : Matrix ι κ ℝ) :
    D.galP Ub Vb (D.half Z) = D.half (D.galProj Ub Vb Z) := by
  rw [galP, mul_apply_eq_comp, leftProj_apply, rightProj_apply, half, half, galProj]
  simp only [transpose_mul, sqx_transpose, sqy_transpose, Matrix.mul_assoc, sqx_mul_sqx_mul,
    sqy_mul_sqy_mul]

/-- The `M`-weighted Galerkin projector is a core orthogonal projector (after scaling). -/
theorem isOrthProj_galP [DecidableEq p] [DecidableEq q] {Ub : Matrix ι p ℝ} {Vb : Matrix κ q ℝ}
    (hUb : Ubᵀ * D.Mx * Ub = 1) (hVb : Vbᵀ * D.My * Vb = 1) : IsOrthProj (D.galP Ub Vb) :=
  isOrthProj_leftProj_mul_rightProj (D.sqx_mul_orthonormal hUb) (D.sqy_mul_orthonormal hVb)

/-- The core Galerkin Euler step of the conjugated problem is the scaled `M`-weighted Galerkin
Euler step: `G(σX) = σ(P(P X + τ N(P X)))`. -/
theorem galerkinEulerStep_half (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (τ : ℝ) (Ub : Matrix ι p ℝ)
    (Vb : Matrix κ q ℝ) (X : Matrix ι κ ℝ) :
    galerkinEulerStep (D.galP Ub Vb) (D.conj N) τ (D.half X) =
      D.half (D.galProj Ub Vb (D.galProj Ub Vb X + τ • N (D.galProj Ub Vb X))) := by
  rw [galerkinEulerStep, eulerStep, galP_half, conj_half, ← half_smul, ← half_add, galP_half]

/-- **Bridge to `IsLipschitzField`**: Assumption 3.1 (i) of arXiv 2501.06145 (Lipschitz
continuity in the mass norm) is exactly the core Lipschitz condition of the conjugated field. -/
theorem isLipschitzField_conj_iff (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (C : ℝ) :
    IsLipschitzField (fun _ => D.conj N) C ↔
      ∀ X Y, D.mnorm (N X - N Y) ≤ C * D.mnorm (X - Y) := by
  constructor
  · intro h X Y
    have this : ‖D.conj N (D.half X) - D.conj N (D.half Y)‖ ≤ C * ‖D.half X - D.half Y‖ :=
      h 0 (D.half X) (D.half Y)
    rwa [conj_half, conj_half, ← half_sub, ← half_sub, norm_half, norm_half] at this
  · intro h t x y
    change ‖D.conj N x - D.conj N y‖ ≤ C * ‖x - y‖
    have := h (D.halfInv x) (D.halfInv y)
    rw [← norm_half, ← norm_half, half_sub, half_sub, half_halfInv, half_halfInv] at this
    exact this

/-- The conjugated flow is symmetric (the linear flow is `M`-self-adjoint, `mip_flow`). -/
theorem inner_flowLM (t : ℝ) (x y : Matrix ι κ ℝ) : ⟪D.flowLM t x, y⟫ = ⟪x, D.flowLM t y⟫ := by
  obtain ⟨X, rfl⟩ : ∃ X, x = D.half X := ⟨D.halfInv x, (D.half_halfInv x).symm⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, y = D.half Y := ⟨D.halfInv y, (D.half_halfInv y).symm⟩
  rw [flowLM_half, flowLM_half, inner_half, inner_half, mip_flow]

/-- The backward conjugated flow dominates the identity (`mip_self_le_mip_flow`). -/
theorem norm_sq_le_inner_flowLM {t : ℝ} (ht : t ≤ 0) (x : Matrix ι κ ℝ) :
    ‖x‖ ^ 2 ≤ ⟪D.flowLM t x, x⟫ := by
  obtain ⟨X, rfl⟩ : ∃ X, x = D.half X := ⟨D.halfInv x, (D.half_halfInv x).symm⟩
  rw [flowLM_half, inner_half, norm_half_sq]
  exact D.mip_self_le_mip_flow ht X

/-- **The modified energy law for one Galerkin SSP-RK2 Strang step** (arXiv 2501.06145,
Theorem 3.3, matrix form, with the constants obtained from the proof).  Let `Ū`, `V̄` be
`M`-orthonormal, `W = Ū S̄₁ V̄ᵀ` (the stage `W_{n,1}`), let `S̄₃ = galRK(S̄₁)` be the SSP-RK2
Galerkin step (3.23), let `T` be its truncation with `‖S̄₃ - T‖_F ≤ η` and
`W' = e^{τε²ℒ}(Ū T V̄ᵀ)` (the stage `W_{n+1,1}`).  Assume, for the pointwise nonlinearity `n`:
`|g'| ≤ C_g` on `[-1, 1]` and the entries of `W`, `W'` in `[-1, 1]` (as in Lemma 2.4), the
Lipschitz bound of Assumption 3.1 (i) between the Galerkin stage
`W̄_{n,2} = W + τ P N(W)` and the full stage `W + τ N(W)` (the only pair at which the proof uses
it), and the projection errors `‖P N(W) - N(W)‖_M ≤ μ₁`, `‖P N(W̄_{n,2}) - N(W̄_{n,2})‖_M ≤ μ₂`
(Assumption 3.1 (ii) at the two stages).  Then
`Ẽ(W') + (1/τ - C_g/2) β² ≤ Ẽ(W) + (η/τ + (μ₁ + μ₂ + C_N τ μ₁)/2) β`, `β = ‖W' - W‖_M`.
Proved by transporting the abstract `energy_galerkinSSPRK2_le` along the scaling isometry. -/
theorem modEnergy_galerkin_le [DecidableEq p] [DecidableEq q] {n : ℝ → ℝ}
    (hn : Differentiable ℝ n) {F0 Cg CN ε τ η μ₁ μ₂ : ℝ} (hτ : 0 < τ) (hCN : 0 ≤ CN)
    (hCg : ∀ s ∈ Set.Icc (-1 : ℝ) 1, |deriv (gfun n τ) s| ≤ Cg) {Ub : Matrix ι p ℝ}
    {Vb : Matrix κ q ℝ} (hUb : Ubᵀ * D.Mx * Ub = 1) (hVb : Vbᵀ * D.My * Vb = 1)
    {S₁ T : Matrix p q ℝ} {w w' : Matrix ι κ ℝ} (hw : w = Ub * S₁ * Vbᵀ)
    (hw' : w' = D.flow (τ * ε ^ 2) (Ub * T * Vbᵀ))
    (hT : √(∑ k, ∑ l, (D.galRK τ (fun W => W.map n) Ub Vb S₁ - T) k l ^ 2) ≤ η)
    (hLip : D.mnorm ((w + τ • D.galProj Ub Vb (w.map n)).map n - (w + τ • w.map n).map n) ≤
      CN * D.mnorm ((w + τ • D.galProj Ub Vb (w.map n)) - (w + τ • w.map n)))
    (hμ₁ : D.mnorm (D.galProj Ub Vb (w.map n) - w.map n) ≤ μ₁)
    (hμ₂ : D.mnorm (D.galProj Ub Vb ((w + τ • D.galProj Ub Vb (w.map n)).map n) -
      (w + τ • D.galProj Ub Vb (w.map n)).map n) ≤ μ₂)
    (h1 : ∀ i j, w i j ∈ Set.Icc (-1 : ℝ) 1) (h2 : ∀ i j, w' i j ∈ Set.Icc (-1 : ℝ) 1) :
    D.modEnergy ε τ (Gfun n τ F0) w' + (1 / τ - Cg / 2) * D.mip (w' - w) (w' - w) ≤
      D.modEnergy ε τ (Gfun n τ F0) w +
        (η / τ + (μ₁ + μ₂ + CN * τ * μ₁) / 2) * D.mnorm (w' - w) := by
  have hgw : D.galProj Ub Vb w = w := by rw [hw, D.galProj_mul_mul hUb hVb]
  have hgY : D.galProj Ub Vb (w + τ • D.galProj Ub Vb (w.map n)) =
      w + τ • D.galProj Ub Vb (w.map n) := by
    rw [galProj_add, galProj_smul, hgw, D.galProj_galProj hUb hVb]
  have hw0 : D.galP Ub Vb (D.half w) = D.half w := by rw [galP_half, hgw]
  have hy0 : galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ (D.half w) =
      D.half (w + τ • D.galProj Ub Vb (w.map n)) := by
    rw [galerkinEulerStep_half, hgw, galProj_add, galProj_smul, hgw]
  have he0 : eulerStep (D.conj fun W => W.map n) τ (D.half w) = D.half (w + τ • w.map n) := by
    rw [eulerStep, conj_half, ← half_smul, ← half_add]
  have hN' : ‖D.conj (fun W => W.map n)
        (galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ (D.half w)) -
      D.conj (fun W => W.map n) (eulerStep (D.conj fun W => W.map n) τ (D.half w))‖ ≤
      CN * ‖galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ (D.half w) -
        eulerStep (D.conj fun W => W.map n) τ (D.half w)‖ := by
    rw [hy0, he0, conj_half, conj_half, ← half_sub, ← half_sub, norm_half, norm_half]
    exact hLip
  have hμ₁' : ‖D.galP Ub Vb (D.conj (fun W => W.map n) (D.half w)) -
      D.conj (fun W => W.map n) (D.half w)‖ ≤ μ₁ := by
    rw [conj_half, galP_half, ← half_sub, norm_half]
    exact hμ₁
  have hμ₂' : ‖D.galP Ub Vb (D.conj (fun W => W.map n)
        (galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ (D.half w))) -
      D.conj (fun W => W.map n)
        (galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ (D.half w))‖ ≤ μ₂ := by
    rw [hy0, conj_half, galP_half, ← half_sub, norm_half]
    exact hμ₂
  have hstep2 : galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ
      (galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ (D.half w)) =
      D.half ((w + τ • D.galProj Ub Vb (w.map n)) +
        τ • D.galProj Ub Vb ((w + τ • D.galProj Ub Vb (w.map n)).map n)) := by
    rw [hy0, galerkinEulerStep_half, hgY, galProj_add, galProj_smul, hgY]
  have hmat : Ub * (D.galRK τ (fun W => W.map n) Ub Vb S₁ - T) * Vbᵀ =
      (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • ((w + τ • D.galProj Ub Vb (w.map n)) +
        τ • D.galProj Ub Vb ((w + τ • D.galProj Ub Vb (w.map n)).map n)) - Ub * T * Vbᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, D.mul_galRK_mul, ← hw]
  have htr' : ‖(1 / 2 : ℝ) • D.half w + (1 / 2 : ℝ) • galerkinEulerStep (D.galP Ub Vb)
      (D.conj fun W => W.map n) τ
        (galerkinEulerStep (D.galP Ub Vb) (D.conj fun W => W.map n) τ (D.half w)) -
      D.half (Ub * T * Vbᵀ)‖ ≤ η := by
    rw [hstep2, ← half_smul, ← half_smul, ← half_add, ← half_sub, ← hmat, norm_half, mnorm,
      D.mip_self_mul_mul Ub Vb hUb hVb]
    exact hT
  have hback' : D.flowLM (-(τ * ε ^ 2)) (D.half w') = D.half (Ub * T * Vbᵀ) := by
    rw [flowLM_half, hw', D.flow_flow, neg_add_cancel, flow_zero]
  have hg : (-(1 / 2 : ℝ)) • (w.map n + (w + τ • w.map n).map n) = w.map (gfun n τ) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, smul_eq_mul, gfun]
    ring
  have hΦ' : (fun X => D.mass ((D.halfInv X).map (Gfun n τ F0))) (D.half w') -
      (fun X => D.mass ((D.halfInv X).map (Gfun n τ F0))) (D.half w) ≤
      ⟪-(1 / 2 : ℝ) • (D.conj (fun W => W.map n) (D.half w) + D.conj (fun W => W.map n)
        (eulerStep (D.conj fun W => W.map n) τ (D.half w))), D.half w' - D.half w⟫ +
        Cg / 2 * ‖D.half w' - D.half w‖ ^ 2 := by
    simp only [halfInv_half]
    rw [he0, conj_half, conj_half, ← half_add, ← half_smul, ← half_sub, inner_half,
      norm_half_sq, hg]
    linarith [D.mass_map_Gfun_le hn F0 Cg τ hCg h1 h2]
  have hA' : ∀ x : Matrix ι κ ℝ, ‖x‖ ^ 2 ≤ ⟪D.flowLM (-(τ * ε ^ 2)) x, x⟫ :=
    D.norm_sq_le_inner_flowLM (neg_nonpos.mpr (mul_nonneg hτ.le (sq_nonneg ε)))
  have key := energy_galerkinSSPRK2_le (D.isOrthProj_galP hUb hVb) (D.inner_flowLM _) hA'
    (fun X => D.mass ((D.halfInv X).map (Gfun n τ F0))) hτ hCN hw0 hN' hμ₁' hμ₂' htr' hback' hΦ'
  simp only [flowLM_half, halfInv_half, ← half_sub, inner_half, norm_half, mnorm_sq] at key
  simp only [modEnergy]
  linarith

/-- **The SVD truncation of Algorithm 3.3** (core `EckartYoung.truncation`) meets the truncation
condition of `IsDLRStep`: if the singular-value tail beyond `k` is at most `η` ((3.24) of
arXiv 2501.06145), the truncated core has rank `≤ k` and Frobenius distance `≤ η`. -/
theorem truncation_spec [DecidableEq q] (A : Matrix p q ℝ) {k : ℕ} {η : ℝ}
    (h : √(∑ i ∈ Finset.Ico k (Fintype.card q), (toEuclideanLin A).singularValues i ^ 2) ≤ η) :
    (EckartYoung.truncation A k).rank ≤ k ∧
      √(∑ i, ∑ j, (A - EckartYoung.truncation A k) i j ^ 2) ≤ η := by
  refine ⟨EckartYoung.rank_truncation_le A k, ?_⟩
  have := EckartYoung.norm_sub_truncation_le_of_tail A h
  rwa [norm_sub_rev, Frobenius.norm_def] at this

end Isometry

end Scaling

end MLFEM

/-! ### Algorithms 3.1, 3.2 and 3.3 -/

/-- If `U R = [A, B]`, then `U R' = A` for a block `R'` of `R`. -/
theorem exists_mul_eq_of_fromCols_left {m p α β : Type*} [Fintype p] {U : Matrix m p ℝ}
    {A : Matrix m α ℝ} {B : Matrix m β ℝ} (h : ∃ R : Matrix p (α ⊕ β) ℝ, U * R = fromCols A B) :
    ∃ R : Matrix p α ℝ, U * R = A := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.submatrix id Sum.inl, ?_⟩
  ext i j
  have := congrFun (congrFun hR i) (Sum.inl j)
  simpa [Matrix.mul_apply] using this

/-- If `U R = [A, B]`, then `U R' = B` for a block `R'` of `R`. -/
theorem exists_mul_eq_of_fromCols_right {m p α β : Type*} [Fintype p] {U : Matrix m p ℝ}
    {A : Matrix m α ℝ} {B : Matrix m β ℝ} (h : ∃ R : Matrix p (α ⊕ β) ℝ, U * R = fromCols A B) :
    ∃ R : Matrix p β ℝ, U * R = B := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.submatrix id Sum.inr, ?_⟩
  ext i j
  have := congrFun (congrFun hR i) (Sum.inr j)
  simpa [Matrix.mul_apply] using this

namespace MLFEM

section Algorithms

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (D : MLFEM ι κ)

/-- **Algorithm 3.1** of arXiv 2501.06145 (exact low-rank integrator for the linear part
`Ẋ = ℒX`, time step `t`), in relational form: the generalized QR factorizations
`U' R = e^{tL_x} U`, `V' P = e^{tL_y} V` with `M`-orthonormal `U'`, `V'` ((3.2)), and the update
`S' = R S Pᵀ` (3.3).  Only the factorization property of the GQR is used, not the triangular
shape of `R`, `P`. -/
structure IsExpStep {r : Type*} [Fintype r] [DecidableEq r] (t : ℝ) (U : Matrix ι r ℝ)
    (S : Matrix r r ℝ) (V : Matrix κ r ℝ) (U' : Matrix ι r ℝ) (S' : Matrix r r ℝ)
    (V' : Matrix κ r ℝ) : Prop where
  /-- `U'ᵀ M_x U' = 1` -/
  orthU : U'ᵀ * D.Mx * U' = 1
  /-- `V'ᵀ M_y V' = 1` -/
  orthV : V'ᵀ * D.My * V' = 1
  /-- the GQR factorizations and the update of the core -/
  gqr : ∃ R P : Matrix r r ℝ, U' * R = exp (t • D.Lx) * U ∧ V' * P = exp (t • D.Ly) * V ∧
    S' = R * S * Pᵀ

/-- **Algorithm 3.2** of arXiv 2501.06145 (one step of the first-order augmented BUG integrator
for `Ż = N(Z)`, time step `τ`, before truncation; Remark 3.1), in relational form, from
`U S Vᵀ`: the explicit Euler K- and L-steps (3.17), (3.18), the `M`-orthonormal augmented bases
with `[K₁, U] = U' R_K`, `[L₁, V] = V' R_L` (the GQR factorizations), and the explicit Euler
Galerkin S-step (3.19) from `S_* = (U'ᵀM_xU) S (V'ᵀM_yV)ᵀ`.  The paper has `2r` new columns; any
number is allowed here. -/
structure IsAugBUGStep {r a : Type*} [Fintype r] [Fintype a] [DecidableEq a] (τ : ℝ)
    (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (U : Matrix ι r ℝ) (S : Matrix r r ℝ) (V : Matrix κ r ℝ)
    (U' : Matrix ι a ℝ) (S' : Matrix a a ℝ) (V' : Matrix κ a ℝ) : Prop where
  /-- `U'ᵀ M_x U' = 1` -/
  orthU : U'ᵀ * D.Mx * U' = 1
  /-- `V'ᵀ M_y V' = 1` -/
  orthV : V'ᵀ * D.My * V' = 1
  /-- K-step (3.17) and `[K₁, U] = U' R_K` -/
  kStep : ∃ R : Matrix a (r ⊕ r) ℝ,
    U' * R = fromCols (U * S + τ • (N (U * S * Vᵀ) * D.My * V)) U
  /-- L-step (3.18) and `[L₁, V] = V' R_L` -/
  lStep : ∃ R : Matrix a (r ⊕ r) ℝ,
    V' * R = fromCols (V * Sᵀ + τ • ((N (U * S * Vᵀ))ᵀ * D.Mx * U)) V
  /-- S-step (3.19) -/
  sStep : S' = (U'ᵀ * D.Mx * U) * S * (V'ᵀ * D.My * V)ᵀ +
    τ • D.galS N U' V' ((U'ᵀ * D.Mx * U) * S * (V'ᵀ * D.My * V)ᵀ)

/-- **Algorithm 3.3** of arXiv 2501.06145 (one step `W_n = Uₙ Sₙ Vₙᵀ ↦ W_{n+1} = U' S' V'ᵀ` of the
second-order DLR-MLFEM), in relational form:

* linear half-step (Algorithm 3.1, `τ/2`): `W_{n,1} = U₁ S₁ V₁ᵀ`;
* trapezoidal approximation (Algorithm 3.2, `τ`): `W_{n,2} = U₂ S₂ V₂ᵀ`;
* Galerkin step: `M`-orthonormal `Ū`, `V̄` with `[q_m, U₁, τN(W_{n,1})V₁, τN(W_{n,2})V₂] = Ū R`,
  `[q_n, V₁, τN(W_{n,1})ᵀU₁, τN(W_{n,2})ᵀU₂] = V̄ R'` ((3.21)), `S̄₁ = (ŪᵀM_xU₁) S₁ (V̄ᵀM_yV₁)ᵀ`
  ((3.22)) and `S̄₃ = galRK(S̄₁)` ((3.23));
* truncation: a core `T` of rank `≤ k` with `‖S̄₃ - T‖_F ≤ η` and `U₃ S₃ V₃ᵀ = Ū T V̄ᵀ`,
  `U₃ = Ū R_k`, `V₃ = V̄ P_k` with orthonormal `R_k`, `P_k` (the SVD truncation of the paper
  satisfies this by `truncation_spec`; any rank-`≤ k` core within `η` is allowed);
* linear half-step (Algorithm 3.1, `τ/2`): `W_{n+1} = U' S' V'ᵀ`. -/
structure IsDLRStep {r a p l : Type*} [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    [Fintype p] [DecidableEq p] [Fintype l] [DecidableEq l] (ε τ η : ℝ)
    (N : Matrix ι κ ℝ → Matrix ι κ ℝ) (k : ℕ)
    (Un : Matrix ι r ℝ) (Sn : Matrix r r ℝ) (Vn : Matrix κ r ℝ)
    (U₁ : Matrix ι r ℝ) (S₁ : Matrix r r ℝ) (V₁ : Matrix κ r ℝ)
    (U₂ : Matrix ι a ℝ) (S₂ : Matrix a a ℝ) (V₂ : Matrix κ a ℝ)
    (Ub : Matrix ι p ℝ) (Vb : Matrix κ p ℝ)
    (U₃ : Matrix ι l ℝ) (S₃ : Matrix l l ℝ) (V₃ : Matrix κ l ℝ)
    (U' : Matrix ι l ℝ) (S' : Matrix l l ℝ) (V' : Matrix κ l ℝ) : Prop where
  /-- first linear half-step -/
  linear₁ : D.IsExpStep (τ * ε ^ 2 / 2) Un Sn Vn U₁ S₁ V₁
  /-- trapezoidal approximation (3.20) -/
  trapezoidal : D.IsAugBUGStep τ N U₁ S₁ V₁ U₂ S₂ V₂
  /-- `ŪᵀM_xŪ = 1` -/
  orthUb : Ubᵀ * D.Mx * Ub = 1
  /-- `V̄ᵀM_yV̄ = 1` -/
  orthVb : Vbᵀ * D.My * Vb = 1
  /-- the augmented left basis (3.21) -/
  spanUb : ∃ R : Matrix p (((Unit ⊕ r) ⊕ r) ⊕ a) ℝ, Ub * R =
    fromCols (fromCols (fromCols (ones : Matrix ι Unit ℝ) U₁) (τ • (N (U₁ * S₁ * V₁ᵀ) * V₁)))
      (τ • (N (U₂ * S₂ * V₂ᵀ) * V₂))
  /-- the augmented right basis (3.21) -/
  spanVb : ∃ R : Matrix p (((Unit ⊕ r) ⊕ r) ⊕ a) ℝ, Vb * R =
    fromCols (fromCols (fromCols (ones : Matrix κ Unit ℝ) V₁) (τ • ((N (U₁ * S₁ * V₁ᵀ))ᵀ * U₁)))
      (τ • ((N (U₂ * S₂ * V₂ᵀ))ᵀ * U₂))
  /-- the truncation step, with tolerance (3.24) -/
  truncation : ∃ T : Matrix p p ℝ, T.rank ≤ k ∧
    √(∑ i, ∑ j,
      (D.galRK τ N Ub Vb ((Ubᵀ * D.Mx * U₁) * S₁ * (Vbᵀ * D.My * V₁)ᵀ) - T) i j ^ 2) ≤ η ∧
    U₃ * S₃ * V₃ᵀ = Ub * T * Vbᵀ
  /-- the truncated bases `U₃ = Ū R_k`, `V₃ = V̄ P_k` -/
  truncBases : ∃ R P : Matrix p l ℝ, U₃ = Ub * R ∧ V₃ = Vb * P ∧ Rᵀ * R = 1 ∧ Pᵀ * P = 1
  /-- second linear half-step -/
  linear₂ : D.IsExpStep (τ * ε ^ 2 / 2) U₃ S₃ V₃ U' S' V'

variable {D}

/-- **Lemma 3.1 for `IsExpStep`**: the exact linear step gives `U' S' V'ᵀ = e^{tℒ}(U S Vᵀ)`. -/
theorem IsExpStep.mul_mul_eq_flow {r : Type*} [Fintype r] [DecidableEq r] {t : ℝ}
    {U : Matrix ι r ℝ} {S : Matrix r r ℝ} {V : Matrix κ r ℝ} {U' : Matrix ι r ℝ}
    {S' : Matrix r r ℝ} {V' : Matrix κ r ℝ} (h : D.IsExpStep t U S V U' S' V') :
    U' * S' * V'ᵀ = D.flow t (U * S * Vᵀ) := by
  obtain ⟨R, P, hR, hP, hS⟩ := h.gqr
  rw [hS]
  exact (D.lemma_3_1 t U S V U' R V' P hR hP).1

variable {r a p l : Type*} [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype p]
  [DecidableEq p] [Fintype l] [DecidableEq l] {ε τ η : ℝ} {N : Matrix ι κ ℝ → Matrix ι κ ℝ}
  {k : ℕ} {Un : Matrix ι r ℝ} {Sn : Matrix r r ℝ} {Vn : Matrix κ r ℝ} {U₁ : Matrix ι r ℝ}
  {S₁ : Matrix r r ℝ} {V₁ : Matrix κ r ℝ} {U₂ : Matrix ι a ℝ} {S₂ : Matrix a a ℝ}
  {V₂ : Matrix κ a ℝ} {Ub : Matrix ι p ℝ} {Vb : Matrix κ p ℝ} {U₃ : Matrix ι l ℝ}
  {S₃ : Matrix l l ℝ} {V₃ : Matrix κ l ℝ} {U' : Matrix ι l ℝ} {S' : Matrix l l ℝ}
  {V' : Matrix κ l ℝ}

/-- `range U₁ ⊆ range Ū` in Algorithm 3.3. -/
theorem IsDLRStep.exists_mul_eq_U₁
    (h : D.IsDLRStep ε τ η N k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S' V') :
    ∃ R : Matrix p r ℝ, Ub * R = U₁ :=
  exists_mul_eq_of_fromCols_right
    (exists_mul_eq_of_fromCols_left (exists_mul_eq_of_fromCols_left h.spanUb))

/-- `range V₁ ⊆ range V̄` in Algorithm 3.3. -/
theorem IsDLRStep.exists_mul_eq_V₁
    (h : D.IsDLRStep ε τ η N k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S' V') :
    ∃ R : Matrix p r ℝ, Vb * R = V₁ :=
  exists_mul_eq_of_fromCols_right
    (exists_mul_eq_of_fromCols_left (exists_mul_eq_of_fromCols_left h.spanVb))

/-- `q_m ∈ range Ū` in Algorithm 3.3. -/
theorem IsDLRStep.exists_mulVec_Ub
    (h : D.IsDLRStep ε τ η N k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S' V') :
    ∃ c, Ub *ᵥ c = 1 := by
  obtain ⟨R, hR⟩ := exists_mul_eq_of_fromCols_left
    (exists_mul_eq_of_fromCols_left (exists_mul_eq_of_fromCols_left h.spanUb))
  refine ⟨fun j => R j (), ?_⟩
  ext i
  have := congrFun (congrFun hR i) ()
  simpa [Matrix.mul_apply, mulVec, dotProduct, ones] using this

/-- `q_n ∈ range V̄` in Algorithm 3.3. -/
theorem IsDLRStep.exists_mulVec_Vb
    (h : D.IsDLRStep ε τ η N k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S' V') :
    ∃ c, Vb *ᵥ c = 1 := by
  obtain ⟨R, hR⟩ := exists_mul_eq_of_fromCols_left
    (exists_mul_eq_of_fromCols_left (exists_mul_eq_of_fromCols_left h.spanVb))
  refine ⟨fun j => R j (), ?_⟩
  ext i
  have := congrFun (congrFun hR i) ()
  simpa [Matrix.mul_apply, mulVec, dotProduct, ones] using this

/-- **(3.31)** (arXiv 2501.06145): the Galerkin step of Algorithm 3.3 starts exactly at the
stage `W_{n,1}`: `Ū S̄₁ V̄ᵀ = U₁ S₁ V₁ᵀ`, because `range U₁ ⊆ range Ū`, `range V₁ ⊆ range V̄`. -/
theorem IsDLRStep.galerkin_start
    (h : D.IsDLRStep ε τ η N k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S' V') :
    Ub * ((Ubᵀ * D.Mx * U₁) * S₁ * (Vbᵀ * D.My * V₁)ᵀ) * Vbᵀ = U₁ * S₁ * V₁ᵀ := by
  obtain ⟨R, hR⟩ := h.exists_mul_eq_U₁
  obtain ⟨P, hP⟩ := h.exists_mul_eq_V₁
  have hU : Ub * (Ubᵀ * D.Mx * U₁) = U₁ := by
    rw [← hR, show Ub * (Ubᵀ * D.Mx * (Ub * R)) = Ub * ((Ubᵀ * D.Mx * Ub) * R) by
      simp only [Matrix.mul_assoc], h.orthUb, Matrix.one_mul]
  have hV : Vb * (Vbᵀ * D.My * V₁) = V₁ := by
    rw [← hP, show Vb * (Vbᵀ * D.My * (Vb * P)) = Vb * ((Vbᵀ * D.My * Vb) * P) by
      simp only [Matrix.mul_assoc], h.orthVb, Matrix.one_mul]
  calc Ub * ((Ubᵀ * D.Mx * U₁) * S₁ * (Vbᵀ * D.My * V₁)ᵀ) * Vbᵀ =
      (Ub * (Ubᵀ * D.Mx * U₁)) * S₁ * (Vb * (Vbᵀ * D.My * V₁))ᵀ := by
        rw [Matrix.transpose_mul Vb]; simp only [Matrix.mul_assoc]
    _ = U₁ * S₁ * V₁ᵀ := by rw [hU, hV]

/-- **Theorem 3.2 for Algorithm 3.3** (arXiv 2501.06145): for a zero-mass nonlinearity
(`(N(Z), 𝐈)_M = 0`, the conservative equation, Corollary 2.1), one step of Algorithm 3.3
conserves the mass up to the truncation tolerance: `|(W_{n+1}, 𝐈)_M - (W_n, 𝐈)_M| ≤ √|Ω| η`.
Derived from `thm_3_2`; the hypotheses on the bases there are proved here from the step. -/
theorem IsDLRStep.mass_sub_le
    (h : D.IsDLRStep ε τ η N k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S' V')
    (hN : ∀ Z, D.mass (N Z) = 0) :
    |D.mass (U' * S' * V'ᵀ) - D.mass (Un * Sn * Vnᵀ)| ≤ √(D.mass ones) * η := by
  obtain ⟨T, -, hT, hT3⟩ := h.truncation
  rw [h.linear₂.mul_mul_eq_flow, hT3]
  exact D.thm_3_2 N hN ε τ η (Un * Sn * Vnᵀ) U₁ S₁ V₁ h.linear₁.mul_mul_eq_flow Ub Vb h.orthUb
    h.orthVb h.exists_mulVec_Ub h.exists_mulVec_Vb T hT

/-- **Theorem 3.3** (arXiv 2501.06145, modified energy law of the DLR-MLFEM), general form with
the constants that the proof gives.  One step of Algorithm 3.3 for a pointwise nonlinearity
`N(W) = n(W)` (entrywise), with `w = W_{n,1} = e^{(τ/2)ε²ℒ} W_n`,
`w' = W_{n+1,1} = e^{(τ/2)ε²ℒ} W_{n+1}`, `β = ‖w' - w‖_M`, `|g'| ≤ C_g` on `[-1, 1]` and the
entries of `w`, `w'` in `[-1, 1]` (as in Lemma 2.4, `modEnergy_step_le`).  Assumption 3.1 enters
as the Lipschitz bound between the two stages `W̄_{n,2} = w + τ P N(w)` and `w + τ N(w)` (the
only pair used) and the projection errors `μ₁` at `W_{n,1}` and `μ₂` at `W̄_{n,2}`.  Then
`Ẽ^{n+1} + (1/τ - C_g/2) β² ≤ Ẽ^n + (η/τ + (μ₁ + μ₂ + C_N τ μ₁)/2) β`. -/
theorem IsDLRStep.modEnergy_le {n : ℝ → ℝ} (hn : Differentiable ℝ n) {F0 Cg CN μ₁ μ₂ : ℝ}
    (hτ : 0 < τ) (hCN : 0 ≤ CN) (hCg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |deriv (gfun n τ) x| ≤ Cg)
    (h : D.IsDLRStep ε τ η (fun W => W.map n) k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S'
      V') {w w' : Matrix ι κ ℝ} (hw : w = D.flow (τ * ε ^ 2 / 2) (Un * Sn * Vnᵀ))
    (hw' : w' = D.flow (τ * ε ^ 2 / 2) (U' * S' * V'ᵀ))
    (hLip : D.mnorm ((w + τ • D.galProj Ub Vb (w.map n)).map n - (w + τ • w.map n).map n) ≤
      CN * D.mnorm ((w + τ • D.galProj Ub Vb (w.map n)) - (w + τ • w.map n)))
    (hμ₁ : D.mnorm (D.galProj Ub Vb (w.map n) - w.map n) ≤ μ₁)
    (hμ₂ : D.mnorm (D.galProj Ub Vb ((w + τ • D.galProj Ub Vb (w.map n)).map n) -
      (w + τ • D.galProj Ub Vb (w.map n)).map n) ≤ μ₂)
    (h1 : ∀ i j, w i j ∈ Set.Icc (-1 : ℝ) 1) (h2 : ∀ i j, w' i j ∈ Set.Icc (-1 : ℝ) 1) :
    D.modEnergy ε τ (Gfun n τ F0) w' + (1 / τ - Cg / 2) * D.mnorm (w' - w) ^ 2 ≤
      D.modEnergy ε τ (Gfun n τ F0) w +
        (η / τ + (μ₁ + μ₂ + CN * τ * μ₁) / 2) * D.mnorm (w' - w) := by
  obtain ⟨T, -, hT, hT3⟩ := h.truncation
  rw [mnorm_sq]
  refine D.modEnergy_galerkin_le hn hτ hCN hCg h.orthUb h.orthVb ?_ ?_ hT hLip hμ₁ hμ₂ h1 h2
  · rw [hw, h.galerkin_start, h.linear₁.mul_mul_eq_flow]
  · rw [hw', h.linear₂.mul_mul_eq_flow, hT3, D.flow_flow,
      show τ * ε ^ 2 / 2 + τ * ε ^ 2 / 2 = τ * ε ^ 2 by ring]

/-- **Theorem 3.3** (arXiv 2501.06145) under the paper's hypotheses: Assumption 3.1 (i) (global
Lipschitz bound in the mass norm), Assumption 3.1 (ii) with one bound `μ` at the two stages, and
the step-size condition `τ ≤ 1/C_g` of Lemma 2.4.  Conclusion:
`Ẽ^{n+1} ≤ Ẽ^n - β²/(2τ) + (η/τ + (2 + C_N τ) μ/2) β`.  Differences from the printed (3.36),
`Ẽ^{n+1} ≤ Ẽ^n - β² + (η/τ + (1 + C_N τ) μ/2) β`: the quadratic term is `-β²/(2τ)`, which is
`≤ -β²` only for `τ ≤ 1/2` (`thm_3_3_of_le_half`); the paper's last step from (3.45), whose
coefficient `1/(2τ) - g'(ξ)/2` is only `≥ 0` under `τ ≤ 1/C_g`, to `-β²` is not justified.  The
`μ`-coefficient is `(2 + C_N τ)/2`: the first inequality of the paper's proof bounds the sum of the
two projection errors by `μ`, although Assumption 3.1 (ii) bounds each of them by `μ`
(`modEnergy_le` keeps `μ₁`, `μ₂` apart; the printed constant follows when `μ₁ + μ₂ ≤ μ`).  For a
pointwise nonlinearity only (as in `modEnergy_step_le`); the box bound on `w`, `w'` is a
hypothesis. -/
theorem IsDLRStep.thm_3_3 {n : ℝ → ℝ} (hn : Differentiable ℝ n) {F0 Cg CN μ : ℝ} (hτ : 0 < τ)
    (hτC : τ ≤ 1 / Cg) (hCg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |deriv (gfun n τ) x| ≤ Cg)
    (hLip : ∀ X Y : Matrix ι κ ℝ, D.mnorm (X.map n - Y.map n) ≤ CN * D.mnorm (X - Y))
    (hCN : 0 ≤ CN)
    (h : D.IsDLRStep ε τ η (fun W => W.map n) k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S'
      V') {w w' : Matrix ι κ ℝ} (hw : w = D.flow (τ * ε ^ 2 / 2) (Un * Sn * Vnᵀ))
    (hw' : w' = D.flow (τ * ε ^ 2 / 2) (U' * S' * V'ᵀ))
    (hμ₁ : D.mnorm (D.galProj Ub Vb (w.map n) - w.map n) ≤ μ)
    (hμ₂ : D.mnorm (D.galProj Ub Vb ((w + τ • D.galProj Ub Vb (w.map n)).map n) -
      (w + τ • D.galProj Ub Vb (w.map n)).map n) ≤ μ)
    (h1 : ∀ i j, w i j ∈ Set.Icc (-1 : ℝ) 1) (h2 : ∀ i j, w' i j ∈ Set.Icc (-1 : ℝ) 1) :
    D.modEnergy ε τ (Gfun n τ F0) w' ≤ D.modEnergy ε τ (Gfun n τ F0) w -
      D.mnorm (w' - w) ^ 2 / (2 * τ) + (η / τ + (2 + CN * τ) * μ / 2) * D.mnorm (w' - w) := by
  have hg := h.modEnergy_le (F0 := F0) hn hτ hCN hCg hw hw' (hLip _ _) hμ₁ hμ₂ h1 h2
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hCpos : 0 < Cg := by
    by_contra hC
    have : 1 / Cg ≤ 0 := one_div_nonpos.mpr (not_lt.mp hC)
    linarith
  have hcoef : 1 / (2 * τ) ≤ 1 / τ - Cg / 2 := by
    have h' : Cg * τ ≤ 1 := by rw [le_div_iff₀ hCpos] at hτC; linarith
    have e : 1 / τ - Cg / 2 - 1 / (2 * τ) = (1 - Cg * τ) / (2 * τ) := by
      field_simp
      ring
    have : 0 ≤ (1 - Cg * τ) / (2 * τ) := div_nonneg (by linarith) (by linarith)
    linarith
  have hβ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (D.mnorm (w' - w)))
  have e2 : D.mnorm (w' - w) ^ 2 / (2 * τ) = 1 / (2 * τ) * D.mnorm (w' - w) ^ 2 := by ring
  rw [e2]
  linarith

/-- **Theorem 3.3 in the printed form (3.36)** for `τ ≤ 1/2` (arXiv 2501.06145):
`Ẽ^{n+1} ≤ Ẽ^n - β² + (η/τ + (2 + C_N τ) μ/2) β`; the `μ`-coefficient differs from the printed
`(1 + C_N τ)/2` as explained in `thm_3_3`. -/
theorem IsDLRStep.thm_3_3_of_le_half {n : ℝ → ℝ} (hn : Differentiable ℝ n) {F0 Cg CN μ : ℝ}
    (hτ : 0 < τ) (hτC : τ ≤ 1 / Cg) (hτh : τ ≤ 1 / 2)
    (hCg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |deriv (gfun n τ) x| ≤ Cg)
    (hLip : ∀ X Y : Matrix ι κ ℝ, D.mnorm (X.map n - Y.map n) ≤ CN * D.mnorm (X - Y))
    (hCN : 0 ≤ CN)
    (h : D.IsDLRStep ε τ η (fun W => W.map n) k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃ V₃ U' S'
      V') {w w' : Matrix ι κ ℝ} (hw : w = D.flow (τ * ε ^ 2 / 2) (Un * Sn * Vnᵀ))
    (hw' : w' = D.flow (τ * ε ^ 2 / 2) (U' * S' * V'ᵀ))
    (hμ₁ : D.mnorm (D.galProj Ub Vb (w.map n) - w.map n) ≤ μ)
    (hμ₂ : D.mnorm (D.galProj Ub Vb ((w + τ • D.galProj Ub Vb (w.map n)).map n) -
      (w + τ • D.galProj Ub Vb (w.map n)).map n) ≤ μ)
    (h1 : ∀ i j, w i j ∈ Set.Icc (-1 : ℝ) 1) (h2 : ∀ i j, w' i j ∈ Set.Icc (-1 : ℝ) 1) :
    D.modEnergy ε τ (Gfun n τ F0) w' ≤ D.modEnergy ε τ (Gfun n τ F0) w -
      D.mnorm (w' - w) ^ 2 + (η / τ + (2 + CN * τ) * μ / 2) * D.mnorm (w' - w) := by
  have h3 := h.thm_3_3 (F0 := F0) hn hτ hτC hCg hLip hCN hw hw' hμ₁ hμ₂ h1 h2
  have h4 : 1 ≤ 1 / (2 * τ) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg (D.mnorm (w' - w)))
  have e2 : D.mnorm (w' - w) ^ 2 / (2 * τ) = 1 / (2 * τ) * D.mnorm (w' - w) ^ 2 := by ring
  linarith

/-- **Theorem 3.3 for the classical Allen–Cahn equation** (arXiv 2501.06145, `N(s) = s - s³`),
with the valid constant `C_g = 2 + τ` (`abs_deriv_gfun_ac_le`; the printed `C_g = 1/2` is false,
`not_Cg_half`) and `0 < τ ≤ 2/5`, which gives `τ ≤ 1/C_g` and `τ ≤ 1/2`:
`Ẽ^{n+1} ≤ Ẽ^n - β² + (η/τ + (2 + C_N τ) μ/2) β`.  The Lipschitz bound is assumed only between
the two stages, since Assumption 3.1 (i) cannot hold globally for the cubic
(`not_lipschitz_map_acReaction`). -/
theorem IsDLRStep.thm_3_3_classical {F0 CN μ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 2 / 5) (hCN : 0 ≤ CN)
    (h : D.IsDLRStep ε τ η (fun W => W.map acReaction) k Un Sn Vn U₁ S₁ V₁ U₂ S₂ V₂ Ub Vb U₃ S₃
      V₃ U' S' V') {w w' : Matrix ι κ ℝ} (hw : w = D.flow (τ * ε ^ 2 / 2) (Un * Sn * Vnᵀ))
    (hw' : w' = D.flow (τ * ε ^ 2 / 2) (U' * S' * V'ᵀ))
    (hLip : D.mnorm ((w + τ • D.galProj Ub Vb (w.map acReaction)).map acReaction -
        (w + τ • w.map acReaction).map acReaction) ≤
      CN * D.mnorm ((w + τ • D.galProj Ub Vb (w.map acReaction)) - (w + τ • w.map acReaction)))
    (hμ₁ : D.mnorm (D.galProj Ub Vb (w.map acReaction) - w.map acReaction) ≤ μ)
    (hμ₂ : D.mnorm (D.galProj Ub Vb ((w + τ • D.galProj Ub Vb (w.map acReaction)).map acReaction) -
      (w + τ • D.galProj Ub Vb (w.map acReaction)).map acReaction) ≤ μ)
    (h1 : ∀ i j, w i j ∈ Set.Icc (-1 : ℝ) 1) (h2 : ∀ i j, w' i j ∈ Set.Icc (-1 : ℝ) 1) :
    D.modEnergy ε τ (Gfun acReaction τ F0) w' ≤ D.modEnergy ε τ (Gfun acReaction τ F0) w -
      D.mnorm (w' - w) ^ 2 + (η / τ + (2 + CN * τ) * μ / 2) * D.mnorm (w' - w) := by
  have hg := h.modEnergy_le (F0 := F0) differentiable_acReaction hτ hCN
    (fun x hx => abs_deriv_gfun_ac_le hτ.le (by linarith) hx) hw hw' hLip hμ₁ hμ₂ h1 h2
  have hc : 1 ≤ 1 / τ - (2 + τ) / 2 := by
    have : 5 / 2 ≤ 1 / τ := by rw [le_div_iff₀ hτ]; linarith
    linarith
  have hβ := mul_le_mul_of_nonneg_right hc (sq_nonneg (D.mnorm (w' - w)))
  linarith

end Algorithms

/-! ### Assumption 3.1 (i) and the classical nonlinearity -/

section Lipschitz

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (D : MLFEM ι κ)

/-- **Assumption 3.1 (i) of arXiv 2501.06145 fails for the classical Allen–Cahn nonlinearity**:
on a nonempty grid no constant `C_N` makes `W ↦ W - W³` (entrywise) globally Lipschitz in the
mass norm (test with the constants `a 𝐈`, `a = |C_N| + 2`).  Read literally, Theorem 3.3 is
therefore vacuous for the classical equation; `IsDLRStep.thm_3_3_classical` assumes the bound only
between the two stages where the proof uses it. -/
theorem not_lipschitz_map_acReaction [Nonempty ι] [Nonempty κ] (CN : ℝ) :
    ¬ ∀ X Y : Matrix ι κ ℝ,
      D.mnorm (X.map acReaction - Y.map acReaction) ≤ CN * D.mnorm (X - Y) := by
  intro h
  have hpos : 0 < D.mnorm ones := Real.sqrt_pos.mpr D.mass_ones_pos
  have ha0 : 0 < |CN| + 2 := by positivity
  have h0 := h ((|CN| + 2) • ones) 0
  have hz : (0 : Matrix ι κ ℝ).map acReaction = 0 := by ext i j; simp [acReaction]
  rw [hz, sub_zero, sub_zero, map_smul_ones, D.mnorm_smul, D.mnorm_smul, abs_of_pos ha0] at h0
  have h1 : |acReaction (|CN| + 2)| ≤ CN * (|CN| + 2) :=
    le_of_mul_le_mul_right (by linarith [h0] :
      |acReaction (|CN| + 2)| * D.mnorm ones ≤ CN * (|CN| + 2) * D.mnorm ones) hpos
  have h2 : (|CN| + 2) ^ 3 - (|CN| + 2) ≤ |acReaction (|CN| + 2)| := by
    rw [acReaction, abs_sub_comm]; exact le_abs_self _
  have h3 : CN * (|CN| + 2) ≤ |CN| * (|CN| + 2) := mul_le_mul_of_nonneg_right (le_abs_self CN)
    ha0.le
  nlinarith [abs_nonneg CN, mul_nonneg (abs_nonneg CN) (abs_nonneg CN),
    pow_nonneg (abs_nonneg CN) 3]

end Lipschitz

/-! ### Algorithm 3.2 as a core Galerkin Euler step -/

section AugBUG

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {D : MLFEM ι κ}
variable {r a : Type*} [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] {τ : ℝ}
  {N : Matrix ι κ ℝ → Matrix ι κ ℝ} {U : Matrix ι r ℝ} {S : Matrix r r ℝ} {V : Matrix κ r ℝ}
  {U' : Matrix ι a ℝ} {S' : Matrix a a ℝ} {V' : Matrix κ a ℝ}

open scoped LeanDLRA.Frobenius

omit [DecidableEq r] in
/-- **Algorithm 3.2 is the core explicit-Euler Galerkin step** (arXiv 2501.06145, (3.19)): after
the scaling isometry, one first-order augmented BUG step is
`σ(U' S' V'ᵀ) = galerkinEulerStep (leftProj Ũ' * rightProj Ṽ') (σ ∘ N ∘ σ⁻¹) τ (σ(U S Vᵀ))`. -/
theorem IsAugBUGStep.half_eq_galerkinEulerStep (h : D.IsAugBUGStep τ N U S V U' S' V') :
    D.half (U' * S' * V'ᵀ) =
      galerkinEulerStep (D.galP U' V') (D.conj N) τ (D.half (U * S * Vᵀ)) := by
  have e1 : D.galProj U' V' (U * S * Vᵀ) =
      U' * ((U'ᵀ * D.Mx * U) * S * (V'ᵀ * D.My * V)ᵀ) * V'ᵀ := by
    simp only [galProj, transpose_mul, transpose_transpose, D.My_transpose, Matrix.mul_assoc]
  rw [galerkinEulerStep_half, e1, galProj_add, galProj_smul, D.galProj_mul_mul h.orthU h.orthV,
    h.sStep, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_galS_mul]

/-- **Algorithm 3.2 versus the full Euler step** (not stated in arXiv 2501.06145; obtained from
the core bound `matrix_augmentedBug_euler_sub_euler`, OP-ST-01, through the scaling isometry).
From `M`-orthonormal `U`, `V` and for `τ > 0`, the first-order augmented BUG step deviates from
the full explicit Euler step `W + τ N(W)`, `W = U S Vᵀ`, by at most `τ` times the doubly
`M`-normal component of `N(W)`:
`‖U' S' V'ᵀ - (W + τ N(W))‖_M ≤ τ ‖(1 - U UᵀM_x) N(W) (1 - M_y V Vᵀ)‖_M`. -/
theorem IsAugBUGStep.mnorm_sub_euler_le (h : D.IsAugBUGStep τ N U S V U' S' V') (hτ : 0 < τ)
    (hU : Uᵀ * D.Mx * U = 1) (hV : Vᵀ * D.My * V = 1) :
    D.mnorm (U' * S' * V'ᵀ - (U * S * Vᵀ + τ • N (U * S * Vᵀ))) ≤
      τ * D.mnorm ((1 - U * Uᵀ * D.Mx) * N (U * S * Vᵀ) * (1 - D.My * V * Vᵀ)) := by
  obtain ⟨RK, hRK⟩ := h.kStep
  obtain ⟨RL, hRL⟩ := h.lStep
  obtain ⟨R₁, hR₁⟩ := exists_mul_eq_of_fromCols_left ⟨RK, hRK⟩
  obtain ⟨R₂, hR₂⟩ := exists_mul_eq_of_fromCols_right ⟨RK, hRK⟩
  obtain ⟨P₁, hP₁⟩ := exists_mul_eq_of_fromCols_left ⟨RL, hRL⟩
  obtain ⟨P₂, hP₂⟩ := exists_mul_eq_of_fromCols_right ⟨RL, hRL⟩
  have capU : ∀ R : Matrix a r ℝ, U' * U'ᵀ * D.Mx * (U' * R) = U' * R := fun R => by
    rw [show U' * U'ᵀ * D.Mx * (U' * R) = U' * (U'ᵀ * D.Mx * U') * R by
      simp only [Matrix.mul_assoc], h.orthU, Matrix.mul_one]
  have capV : ∀ P : Matrix a r ℝ, V' * V'ᵀ * D.My * (V' * P) = V' * P := fun P => by
    rw [show V' * V'ᵀ * D.My * (V' * P) = V' * (V'ᵀ * D.My * V') * P by
      simp only [Matrix.mul_assoc], h.orthV, Matrix.mul_one]
  have hUU' : U' * U'ᵀ * D.Mx * U = U := by rw [← hR₂, capU]
  have hVV' : V' * V'ᵀ * D.My * V = V := by rw [← hP₂, capV]
  have hFV : N (U * S * Vᵀ) * D.My * V = U' * ((1 / τ) • (R₁ - R₂ * S)) := by
    rw [Matrix.mul_smul, Matrix.mul_sub, hR₁, ← Matrix.mul_assoc U' R₂, hR₂, add_sub_cancel_left,
      smul_smul, one_div_mul_cancel hτ.ne', one_smul]
  have hFU : (N (U * S * Vᵀ))ᵀ * D.Mx * U = V' * ((1 / τ) • (P₁ - P₂ * Sᵀ)) := by
    rw [Matrix.mul_smul, Matrix.mul_sub, hP₁, ← Matrix.mul_assoc V' P₂, hP₂, add_sub_cancel_left,
      smul_smul, one_div_mul_cancel hτ.ne', one_smul]
  have liftU : ∀ X : Matrix ι r ℝ, U' * U'ᵀ * D.Mx * X = X →
      D.sqx * U' * (D.sqx * U')ᵀ * (D.sqx * X) = D.sqx * X := by
    intro X hX
    calc D.sqx * U' * (D.sqx * U')ᵀ * (D.sqx * X) = D.sqx * (U' * U'ᵀ * D.Mx * X) := by
          simp only [transpose_mul, sqx_transpose, Matrix.mul_assoc, sqx_mul_sqx_mul]
      _ = D.sqx * X := by rw [hX]
  have liftV : ∀ X : Matrix κ r ℝ, V' * V'ᵀ * D.My * X = X →
      D.sqy * V' * (D.sqy * V')ᵀ * (D.sqy * X) = D.sqy * X := by
    intro X hX
    calc D.sqy * V' * (D.sqy * V')ᵀ * (D.sqy * X) = D.sqy * (V' * V'ᵀ * D.My * X) := by
          simp only [transpose_mul, sqy_transpose, Matrix.mul_assoc, sqy_mul_sqy_mul]
      _ = D.sqy * X := by rw [hX]
  have hFV0 : D.half (N (U * S * Vᵀ)) * (D.sqy * V) = D.sqx * (N (U * S * Vᵀ) * D.My * V) := by
    rw [half]; simp only [Matrix.mul_assoc, sqy_mul_sqy_mul]
  have hFU0 : (D.half (N (U * S * Vᵀ)))ᵀ * (D.sqx * U) =
      D.sqy * ((N (U * S * Vᵀ))ᵀ * D.Mx * U) := by
    rw [half]
    simp only [transpose_mul, sqx_transpose, sqy_transpose, Matrix.mul_assoc, sqx_mul_sqx_mul]
  have hK : D.sqx * U' * (D.sqx * U')ᵀ * (D.half (N (U * S * Vᵀ)) * (D.sqy * V)) =
      D.half (N (U * S * Vᵀ)) * (D.sqy * V) := by
    rw [hFV0]; exact liftU _ (by rw [hFV, capU])
  have hL : D.sqy * V' * (D.sqy * V')ᵀ * ((D.half (N (U * S * Vᵀ)))ᵀ * (D.sqx * U)) =
      (D.half (N (U * S * Vᵀ)))ᵀ * (D.sqx * U) := by
    rw [hFU0]; exact liftV _ (by rw [hFU, capV])
  have key := matrix_augmentedBug_euler_sub_euler (D.sqx_mul_orthonormal hU)
    (D.sqy_mul_orthonormal hV) (D.sqx_mul_orthonormal h.orthU) (D.sqy_mul_orthonormal h.orthV)
    (liftU U hUU') (liftV V hVV') S (D.half (N (U * S * Vᵀ))) hK hL hτ.le
  -- translate back to the mass norm
  have hW0 : D.sqx * U * S * (D.sqy * V)ᵀ = D.half (U * S * Vᵀ) := by
    rw [half]; simp only [transpose_mul, sqy_transpose, Matrix.mul_assoc]
  have hP : ∀ Y : Matrix ι κ ℝ, D.sqx * U' * (D.sqx * U')ᵀ * D.half Y * (D.sqy * V') *
      (D.sqy * V')ᵀ = D.half (D.galProj U' V' Y) := fun Y => by
    rw [half, half, galProj]
    simp only [transpose_mul, sqx_transpose, sqy_transpose, Matrix.mul_assoc, sqx_mul_sqx_mul,
      sqy_mul_sqy_mul]
  have hgW : D.galProj U' V' (U * S * Vᵀ) = U * S * Vᵀ := by
    rw [show D.galProj U' V' (U * S * Vᵀ) = (U' * U'ᵀ * D.Mx * U) * S * (V' * V'ᵀ * D.My * V)ᵀ by
      simp only [galProj, transpose_mul, transpose_transpose, D.My_transpose, Matrix.mul_assoc],
      hUU', hVV']
  have e1 : U' * ((U'ᵀ * D.Mx * U) * S * (V'ᵀ * D.My * V)ᵀ) * V'ᵀ = U * S * Vᵀ := by
    rw [← hgW]
    simp only [galProj, transpose_mul, transpose_transpose, D.My_transpose, Matrix.mul_assoc]
  have hS'eq : D.galProj U' V' (U * S * Vᵀ + τ • N (U * S * Vᵀ)) = U' * S' * V'ᵀ := by
    rw [h.sStep, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_galS_mul,
      e1, galProj_add, galProj_smul, hgW]
  have hA : (1 - D.sqx * U * (D.sqx * U)ᵀ) * D.sqx = D.sqx * (1 - U * Uᵀ * D.Mx) := by
    simp only [transpose_mul, sqx_transpose, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, sqx_mul_sqx]
  have hB : D.sqy * (1 - D.sqy * V * (D.sqy * V)ᵀ) = (1 - D.My * V * Vᵀ) * D.sqy := by
    simp only [transpose_mul, sqy_transpose, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, sqy_mul_sqy_mul]
  have hnorm : (1 - D.sqx * U * (D.sqx * U)ᵀ) * D.half (N (U * S * Vᵀ)) *
      (1 - D.sqy * V * (D.sqy * V)ᵀ) =
      D.half ((1 - U * Uᵀ * D.Mx) * N (U * S * Vᵀ) * (1 - D.My * V * Vᵀ)) := by
    calc (1 - D.sqx * U * (D.sqx * U)ᵀ) * D.half (N (U * S * Vᵀ)) *
          (1 - D.sqy * V * (D.sqy * V)ᵀ) =
        ((1 - D.sqx * U * (D.sqx * U)ᵀ) * D.sqx) * N (U * S * Vᵀ) *
          (D.sqy * (1 - D.sqy * V * (D.sqy * V)ᵀ)) := by
          rw [half]; simp only [Matrix.mul_assoc]
      _ = D.sqx * (1 - U * Uᵀ * D.Mx) * N (U * S * Vᵀ) * ((1 - D.My * V * Vᵀ) * D.sqy) := by
          rw [hA, hB]
      _ = _ := by rw [half]; simp only [Matrix.mul_assoc]
  rw [hW0, ← half_smul, ← half_add, hP, hS'eq, ← half_sub, norm_half, hnorm, norm_half] at key
  exact key

end AugBUG

/-! ### Non-vacuity -/

/-- A one-cell mass-lumped setting (`M_x = M_y = 1`, no diffusion), used to show that the
hypotheses of Algorithm 3.3 and Theorem 3.3 can be met. -/
noncomputable def oneCell : MLFEM (Fin 1) (Fin 1) where
  mx := fun _ => 1
  my := fun _ => 1
  Ax := 0
  Ay := 0
  mx_pos := fun _ => one_pos
  my_pos := fun _ => one_pos
  Ax_symm := transpose_zero
  Ay_symm := transpose_zero
  Ax_psd := fun u => by simp
  Ay_psd := fun u => by simp
  Ax_one := zero_mulVec _
  Ay_one := zero_mulVec _

/-- `M_x = 1` on `oneCell`. -/
theorem oneCell_Mx : oneCell.Mx = 1 := by
  simp [Mx, oneCell]

/-- `M_y = 1` on `oneCell`. -/
theorem oneCell_My : oneCell.My = 1 := by
  simp [My, oneCell]

/-- `L_x = 0` on `oneCell`. -/
theorem oneCell_Lx : oneCell.Lx = 0 := by
  simp [Lx, gen, oneCell]

/-- `L_y = 0` on `oneCell`. -/
theorem oneCell_Ly : oneCell.Ly = 0 := by
  simp [Ly, gen, oneCell]

/-- On `oneCell` the linear flow is the identity. -/
theorem oneCell_flow (t : ℝ) (W : Matrix (Fin 1) (Fin 1) ℝ) : oneCell.flow t W = W := by
  rw [flow, oneCell_Lx, oneCell_Ly, smul_zero, NormedSpace.exp_zero]
  simp

/-- The zero nonlinearity, written as a pointwise map. -/
theorem map_zero_fun (X : Matrix (Fin 1) (Fin 1) ℝ) : X.map (fun _ : ℝ => (0 : ℝ)) = 0 := by
  ext i j; simp

/-- Algorithm 3.1 on `oneCell` with trivial factors. -/
theorem oneCell_isExpStep (t : ℝ) (S : Matrix (Fin 1) (Fin 1) ℝ) :
    oneCell.IsExpStep t 1 S 1 1 S 1 where
  orthU := by rw [oneCell_Mx]; simp
  orthV := by rw [oneCell_My]; simp
  gqr := ⟨1, 1, by rw [oneCell_Lx, smul_zero, NormedSpace.exp_zero],
    by rw [oneCell_Ly, smul_zero, NormedSpace.exp_zero], by simp⟩

/-- **Non-vacuity of `IsDLRStep`**: one step of Algorithm 3.3 on `oneCell` with `N = 0`. -/
theorem oneCell_isDLRStep (ε τ : ℝ) (S : Matrix (Fin 1) (Fin 1) ℝ) :
    oneCell.IsDLRStep ε τ 0 (fun W => W.map fun _ => 0) 1 1 S 1 1 S 1 1 S 1
      (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 S 1 1 S 1 where
  linear₁ := oneCell_isExpStep _ S
  trapezoidal :=
    { orthU := by rw [oneCell_Mx]; simp
      orthV := by rw [oneCell_My]; simp
      kStep := ⟨fromCols S 1, by simp [map_zero_fun]⟩
      lStep := ⟨fromCols Sᵀ 1, by simp [map_zero_fun]⟩
      sStep := by simp [oneCell_Mx, oneCell_My, galS, map_zero_fun] }
  orthUb := by rw [oneCell_Mx]; simp
  orthVb := by rw [oneCell_My]; simp
  spanUb := ⟨_, Matrix.one_mul _⟩
  spanVb := ⟨_, Matrix.one_mul _⟩
  truncation := by
    refine ⟨S, rank_le_width S, ?_, by simp⟩
    have hRK : oneCell.galRK τ (fun W => W.map fun _ => 0) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * oneCell.Mx *
          (1 : Matrix (Fin 1) (Fin 1) ℝ)) * S * ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * oneCell.My *
          (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ) = S := by
      rw [galRK]
      simp only [galS, oneCell_Mx, oneCell_My, transpose_one, Matrix.one_mul, Matrix.mul_one,
        map_zero_fun, Matrix.mul_zero, smul_zero, add_zero]
      module
    rw [hRK, sub_self]
    simp
  truncBases := ⟨1, 1, by simp, by simp, by simp, by simp⟩
  linear₂ := oneCell_isExpStep _ S

/-- **Non-vacuity of `IsDLRStep.thm_3_3`**: all its hypotheses hold for one step of
Algorithm 3.3 on `oneCell` with `N = 0`, `τ = 1/2`, `C_g = 1`, `C_N = μ = η = 0` and a state
`c 𝐈`, `|c| ≤ 1`. -/
example (ε F0 c : ℝ) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    oneCell.modEnergy ε (1 / 2) (Gfun (fun _ => 0) (1 / 2) F0) (of fun _ _ => c) ≤
      oneCell.modEnergy ε (1 / 2) (Gfun (fun _ => 0) (1 / 2) F0) (of fun _ _ => c) -
        oneCell.mnorm ((of fun _ _ => c) - of fun _ _ => c) ^ 2 / (2 * (1 / 2)) +
        (0 / (1 / 2) + (2 + 0 * (1 / 2)) * 0 / 2) *
          oneCell.mnorm ((of fun _ _ => c) - of fun _ _ => c) := by
  have hg : gfun (fun _ : ℝ => (0 : ℝ)) (1 / 2) = fun _ => 0 := funext fun x => by simp [gfun]
  refine (oneCell_isDLRStep ε (1 / 2) (of fun _ _ => c)).thm_3_3 (Cg := 1) (CN := 0)
    (differentiable_const 0) (by norm_num) (by norm_num) (fun x _ => by rw [hg]; simp)
    (fun X Y => by simp [map_zero_fun, mnorm, mip]) le_rfl ?_ ?_ ?_ ?_ ?_ ?_
  · rw [oneCell_flow]; simp
  · rw [oneCell_flow]; simp
  · simp [map_zero_fun, galProj, mnorm, mip]
  · simp [map_zero_fun, galProj, mnorm, mip]
  · intro i j; simpa using hc
  · intro i j; simpa using hc

end MLFEM

end LeanDLRA.Literature.P2501_06145
