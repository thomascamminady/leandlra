import LeanDLRA.HighOrder.RungeKuttaBUG
import LeanDLRA.Stability.Energy
import LeanDLRA.Foundations.Galerkin
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# Algebraic stability of Galerkin Runge–Kutta steps, and its loss under stage-dependent bases

Open problem OP-SB-54 of `docs/catalogue/survey/open-problems.json` (stability of higher-order
low-rank
integrators: high-order DIRK/IMEX BUG and RAIL, 2311.15143; Strang PSI, 2006.05211, 2507.15192).
This module settles the DIRK/implicit Runge–Kutta part in the abstract
framework of the library (orthogonal projectors `P` on a real inner product space standing for
the low-rank basis projectors), with one positive and two negative results.

## Positive result: a fixed Galerkin space inherits algebraic stability

* `rk_energy_identity`: for any tableau `(a, b)`, any `y₀`, any stage vectors `G i`,
  `‖y₀ + h ∑ bᵢ Gᵢ‖² = ‖y₀‖² + 2h ∑ bᵢ ⟪Gᵢ, Yᵢ⟫ - h² ∑ Mᵢⱼ ⟪Gᵢ, Gⱼ⟫`, with
  `Yᵢ = y₀ + h ∑ aᵢⱼ Gⱼ` and the Burrage–Butcher matrix `M = B A + Aᵀ B - b bᵀ`.
* `galerkinRK_norm_le`, `galerkinRK_contractive`, `galerkinRK_iter_norm_le`: if the tableau is
  algebraically stable (`b ≥ 0`, `M ⪰ 0`) and all stages and the result are computed in one
  Galerkin space `range P` (`IsGalerkinRKStep` with constant projector), then for every `h ≥ 0`
  the step is norm-nonincreasing for dissipative `F` and contractive for monotone `F`
  (B-stability), for arbitrary bases and any number of steps with step-dependent bases.  This
  covers Gauss, Radau IIA, Lobatto IIIC and the algebraically stable SDIRK methods
  (`sdirk_isAlgebraicallyStable`) in the augmented BUG space.

## Negative results: stage-dependent (nested) bases do not inherit stability

RAIL (2311.15143) and stage-wise BUG schemes compute stage `i` in its own augmented space
`range Pᵢ ⊇ range Pᵢ₋₁ ∋ y`.  Even with nested spaces and the full space at the last stage:

* `sdirk_nested_unbounded`: for the algebraically stable, A-stable, second-order SDIRK family
  `a = [[γ, 0], [1 - 2γ, γ]]`, `b = (1/2, 1/2)`, `1/2 ≤ γ ≤ 1`, with the final `b`-combination
  computed in the full space, the amplification factor is **unbounded**: for every `n ≥ 0` there
  is a symmetric negative semidefinite rank-one field `F(x) = -⟪v, x⟫ v` on `ℝ²` and a nested
  pair `P₀ ⊂ P₁ = 1` with `‖y₁‖ ≥ (n/4) ‖y‖`.  Mechanism: `F(Y₀)` of the projected stage enters
  the final combination explicitly, with its component outside `range P₀` undamped.
* `alexander_nested_not_stable`, `alexander_nested_not_stable_sqrt`: for the stiffly accurate
  family `a = [[γ, 0], [1 - γ, γ]]`, `b = (1 - γ, γ)`, `0 ≤ γ ≤ 3/10`, including Alexander's
  L-stable second-order SDIRK `γ = 1 - √2/2` (the DIRK2 of RAIL), the step with nested bases
  `P₀ ⊂ P₁ = 1` increases the norm for a symmetric negative semidefinite field on `ℝ²`:
  `‖Y₁‖ > ‖y‖`, whereas the same step with both stages in the full space is contractive
  (`alexander_full_space_contractive`).  So the unconditional `L²`-stability of first-order
  RAIL (2311.15143, Theorem 2, backward Euler) does not extend to the second-order scheme with
  stage-dependent bases; the change of Galerkin space between the stages is the cause.

What changed from the problem statement: the "proof idea" (stage-wise Galerkin projections
preserve the algebraic-stability argument) is correct exactly when all stages share one Galerkin
space, and false otherwise.  The Strang projector-splitting and IMEX parts remain open.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Novel.OpSB54

open LeanDLRA.RungeKuttaBUG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Algebraic stability -/

section AlgebraicStability

/-- The **Burrage–Butcher matrix** `M = B A + Aᵀ B - b bᵀ` of a Runge–Kutta tableau,
`Mᵢⱼ = bᵢ aᵢⱼ + bⱼ aⱼᵢ - bᵢ bⱼ`. -/
def algStabMatrix {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun i j => b i * a i j + b j * a j i - b i * b j

/-- A tableau is **algebraically stable** if `b ≥ 0` and `M ⪰ 0` (Burrage–Butcher, Crouzeix). -/
def IsAlgebraicallyStable {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧ (algStabMatrix a b).PosSemidef

/-- For a positive semidefinite `M` and any vectors `Gᵢ`, `∑ᵢⱼ Mᵢⱼ ⟪Gᵢ, Gⱼ⟫ ≥ 0` (Schur product
of `M` with the Gram matrix of the `Gᵢ`). -/
lemma sum_posSemidef_inner_nonneg {s : ℕ} {M : Matrix (Fin s) (Fin s) ℝ} (hM : M.PosSemidef)
    (G : Fin s → E) : 0 ≤ ∑ i, ∑ j, M i j * ⟪G i, G j⟫ := by
  have := (hM.hadamard (Matrix.posSemidef_gram ℝ G)).dotProduct_mulVec_nonneg (fun _ => 1)
  simpa [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.gram_apply] using this

/-- **Runge–Kutta energy identity** (the algebraic-stability identity of Burrage–Butcher, in an
inner product space, for arbitrary stage vectors `Gᵢ` not assumed to be field values): with
`Yᵢ = y₀ + h ∑ⱼ aᵢⱼ Gⱼ` and `y₁ = y₀ + h ∑ᵢ bᵢ Gᵢ`,
`‖y₁‖² = ‖y₀‖² + 2h ∑ᵢ bᵢ ⟪Gᵢ, Yᵢ⟫ - h² ∑ᵢⱼ Mᵢⱼ ⟪Gᵢ, Gⱼ⟫`. -/
theorem rk_energy_identity {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (h : ℝ) (y₀ : E)
    (G : Fin s → E) :
    ‖y₀ + h • ∑ i, b i • G i‖ ^ 2 =
      ‖y₀‖ ^ 2 + 2 * h * ∑ i, b i * ⟪G i, y₀ + h • ∑ j, a i j • G j⟫
        - h ^ 2 * ∑ i, ∑ j, algStabMatrix a b i j * ⟪G i, G j⟫ := by
  have key : ∑ i, ∑ j, b j * a j i * ⟪G i, G j⟫ = ∑ i, ∑ j, b i * a i j * ⟪G i, G j⟫ := by
    rw [Finset.sum_comm]
    simp_rw [real_inner_comm]
  have hL : ‖y₀ + h • ∑ i, b i • G i‖ ^ 2 = ‖y₀‖ ^ 2 + 2 * h * ∑ i, b i * ⟪G i, y₀⟫
      + h ^ 2 * ∑ i, ∑ j, b i * b j * ⟪G i, G j⟫ := by
    rw [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right,
      inner_sum, ← real_inner_self_eq_norm_sq (∑ i, b i • G i), sum_inner]
    simp only [real_inner_smul_right, inner_sum, real_inner_smul_left, Finset.mul_sum]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm]
      ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  have hmid : ∑ i, b i * ⟪G i, y₀ + h • ∑ j, a i j • G j⟫ =
      ∑ i, b i * ⟪G i, y₀⟫ + h * ∑ i, ∑ j, b i * a i j * ⟪G i, G j⟫ := by
    simp only [inner_add_right, real_inner_smul_right, inner_sum, mul_add, Finset.mul_sum,
      Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hM : ∑ i, ∑ j, algStabMatrix a b i j * ⟪G i, G j⟫ =
      2 * ∑ i, ∑ j, b i * a i j * ⟪G i, G j⟫ - ∑ i, ∑ j, b i * b j * ⟪G i, G j⟫ := by
    simp only [algStabMatrix, Matrix.of_apply, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [key]
    ring
  rw [hL, hmid, hM]
  ring

/-- **Algebraic stability in an inner product space**: if `b ≥ 0`, `M ⪰ 0`, `h ≥ 0` and the
stage vectors satisfy `⟪Gᵢ, Yᵢ⟫ ≤ 0`, then `‖y₀ + h ∑ bᵢ Gᵢ‖ ≤ ‖y₀‖`. -/
theorem rk_norm_le_of_isAlgebraicallyStable {s : ℕ} {a : Fin s → Fin s → ℝ} {b : Fin s → ℝ}
    (hab : IsAlgebraicallyStable a b) {h : ℝ} (hh : 0 ≤ h) (y₀ : E) (G : Fin s → E)
    (hG : ∀ i, ⟪G i, y₀ + h • ∑ j, a i j • G j⟫ ≤ 0) :
    ‖y₀ + h • ∑ i, b i • G i‖ ≤ ‖y₀‖ := by
  have hid := rk_energy_identity a b h y₀ G
  have hsum : ∑ i, b i * ⟪G i, y₀ + h • ∑ j, a i j • G j⟫ ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hab.1 i) (hG i)
  have h1 : 2 * h * ∑ i, b i * ⟪G i, y₀ + h • ∑ j, a i j • G j⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hsum
  have h2 : 0 ≤ h ^ 2 * ∑ i, ∑ j, algStabMatrix a b i j * ⟪G i, G j⟫ :=
    mul_nonneg (sq_nonneg h) (sum_posSemidef_inner_nonneg hab.2 G)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- **A fixed Galerkin space inherits algebraic stability (dissipative fields).**  Let the
tableau `(a, b, c)` be algebraically stable and let all stages and the result of a Galerkin
Runge–Kutta step be computed in one space `range P` (`IsGalerkinRKStep` with constant
projector `P`: this is a DIRK/implicit RK step of the BUG type performed in the augmented
space).  If `⟪F(tᵢ, Yᵢ), Yᵢ⟫ ≤ 0` at the stages, then `‖y₁‖ ≤ ‖P y‖ ≤ ‖y‖` for every `h ≥ 0`,
for arbitrary bases.  This is the Galerkin counterpart of the Burrage–Butcher theorem and
extends `implicitGalerkin_norm_le` (backward Euler) to every algebraically stable method; see
OP-SB-54. -/
theorem galerkinRK_norm_le {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (hab : IsAlgebraicallyStable a b) {P : E →L[ℝ] E} (hP : IsOrthProj P) {t h : ℝ} (hh : 0 ≤ h)
    {y y₁ : E} {Y : Fin s → E} (hG : IsGalerkinRKStep F a b c (fun _ => P) P t h y Y y₁)
    (hF : ∀ i, ⟪F (t + c i * h) (Y i), Y i⟫ ≤ 0) : ‖y₁‖ ≤ ‖P y‖ ∧ ‖y₁‖ ≤ ‖y‖ := by
  set G : Fin s → E := fun i => P (F (t + c i * h) (Y i)) with hGdef
  have hY : ∀ i, Y i = P y + h • ∑ j, a i j • G j := by
    intro i
    rw [hG.1 i, map_add, map_smul, map_sum]
    simp_rw [map_smul]
    rfl
  have hy₁ : y₁ = P y + h • ∑ i, b i • G i := by
    rw [hG.2, map_add, map_smul, map_sum]
    simp_rw [map_smul]
    rfl
  have hPY : ∀ i, P (Y i) = Y i := fun i => by rw [hG.1 i, hP.idem]
  have hin : ∀ i, ⟪G i, P y + h • ∑ j, a i j • G j⟫ ≤ 0 := by
    intro i
    rw [← hY i]
    change ⟪P (F (t + c i * h) (Y i)), Y i⟫ ≤ 0
    rw [hP.inner_apply_left_of_mem _ (hPY i)]
    exact hF i
  have h1 : ‖y₁‖ ≤ ‖P y‖ := by
    rw [hy₁]
    exact rk_norm_le_of_isAlgebraicallyStable hab hh (P y) G hin
  exact ⟨h1, h1.trans (hP.norm_le y)⟩

/-- **B-stability of Galerkin Runge–Kutta steps in a fixed space.**  Two Galerkin steps with the
same algebraically stable tableau and the same projector `P`, from `u` and `v`, for a monotone
field (`⟪F(t, x) - F(t, x'), x - x'⟫ ≤ 0` at the stages), satisfy
`‖u₁ - v₁‖ ≤ ‖P u - P v‖ ≤ ‖u - v‖` for every `h ≥ 0`. -/
theorem galerkinRK_contractive {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (hab : IsAlgebraicallyStable a b) {P : E →L[ℝ] E} (hP : IsOrthProj P) {t h : ℝ} (hh : 0 ≤ h)
    {u v u₁ v₁ : E} {U V : Fin s → E} (hU : IsGalerkinRKStep F a b c (fun _ => P) P t h u U u₁)
    (hV : IsGalerkinRKStep F a b c (fun _ => P) P t h v V v₁)
    (hF : ∀ i, ⟪F (t + c i * h) (U i) - F (t + c i * h) (V i), U i - V i⟫ ≤ 0) :
    ‖u₁ - v₁‖ ≤ ‖P u - P v‖ ∧ ‖u₁ - v₁‖ ≤ ‖u - v‖ := by
  set G : Fin s → E := fun i => P (F (t + c i * h) (U i) - F (t + c i * h) (V i)) with hGdef
  have hY : ∀ i, U i - V i = (P u - P v) + h • ∑ j, a i j • G j := by
    intro i
    rw [hU.1 i, hV.1 i]
    simp only [hGdef, map_add, map_smul, map_sum, map_sub, smul_sub, Finset.sum_sub_distrib]
    abel
  have hy₁ : u₁ - v₁ = (P u - P v) + h • ∑ i, b i • G i := by
    rw [hU.2, hV.2]
    simp only [hGdef, map_add, map_smul, map_sum, map_sub, smul_sub, Finset.sum_sub_distrib]
    abel
  have hPY : ∀ i, P (U i - V i) = U i - V i := fun i => by
    rw [map_sub, hU.1 i, hV.1 i, hP.idem, hP.idem]
  have hin : ∀ i, ⟪G i, (P u - P v) + h • ∑ j, a i j • G j⟫ ≤ 0 := by
    intro i
    rw [← hY i]
    change ⟪P (F (t + c i * h) (U i) - F (t + c i * h) (V i)), U i - V i⟫ ≤ 0
    rw [hP.inner_apply_left_of_mem _ (hPY i)]
    exact hF i
  have h1 : ‖u₁ - v₁‖ ≤ ‖P u - P v‖ := by
    rw [hy₁]
    exact rk_norm_le_of_isAlgebraicallyStable hab hh (P u - P v) G hin
  refine ⟨h1, h1.trans ?_⟩
  rw [← map_sub]
  exact hP.norm_le _

/-- **Unconditional `L²`-stability over many steps** of an algebraically stable Galerkin
Runge–Kutta integrator with step-dependent Galerkin spaces `range Pₙ` (one space per step) for a
dissipative field: `‖yₙ‖ ≤ ‖y₀‖` for all `n` and all `h ≥ 0`. -/
theorem galerkinRK_iter_norm_le {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ}
    {b c : Fin s → ℝ} (hab : IsAlgebraicallyStable a b) {P : ℕ → E →L[ℝ] E}
    (hP : ∀ n, IsOrthProj (P n)) {h : ℝ} (hh : 0 ≤ h) {t : ℕ → ℝ} {y : ℕ → E}
    {Y : ℕ → Fin s → E}
    (hstep : ∀ n, IsGalerkinRKStep F a b c (fun _ => P n) (P n) (t n) h (y n) (Y n) (y (n + 1)))
    (hF : ∀ τ x, ⟪F τ x, x⟫ ≤ 0) : ∀ n, ‖y n‖ ≤ ‖y 0‖ := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact ((galerkinRK_norm_le hab (hP n) hh (hstep n) fun i => hF _ _).2).trans ih

/-- The two-stage SDIRK family `a = [[γ, 0], [1 - 2γ, γ]]`, `b = (1/2, 1/2)` (second order for
all `γ`, third order for `γ = (3 ± √3)/6`) is algebraically stable iff `γ ≥ 1/4`:
`M = (γ - 1/4) [[1, -1], [-1, 1]]`. -/
theorem sdirk_isAlgebraicallyStable {γ : ℝ} (hγ : 1 / 4 ≤ γ) :
    IsAlgebraicallyStable ![![γ, 0], ![1 - 2 * γ, γ]] ![1 / 2, 1 / 2] := by
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [algStabMatrix]
  · simp [algStabMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    nlinarith [mul_nonneg (sub_nonneg.2 hγ) (sq_nonneg (x 0 - x 1))]

/-- Backward Euler (`M = 1`) and the implicit midpoint rule (`M = 0`) are algebraically
stable. -/
example : IsAlgebraicallyStable ![![(1 : ℝ)]] ![1] ∧
    IsAlgebraicallyStable ![![(1 / 2 : ℝ)]] ![1] := by
  constructor <;>
  · refine ⟨fun i => by fin_cases i; norm_num, ?_⟩
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j; fin_cases i; fin_cases j; simp [algStabMatrix]
    · simp [algStabMatrix, dotProduct, Matrix.mulVec]
      nlinarith [sq_nonneg (x 0)]

end AlgebraicStability

/-! ### Stage-dependent nested bases: counterexamples in `ℝ²` -/

section Counterexamples

open LeanDLRA.EnergyExamples

/-- The symmetric negative semidefinite rank-one linear field `F(t, x) = -⟪v, x⟫ v`
(`F = -v vᵀ`, the model of the symmetric negative semidefinite operators of 2311.15143,
Theorem 2). -/
noncomputable def rankOneField (v : E2) : ℝ → E2 → E2 := fun _ x => -(⟪v, x⟫ • v)

lemma rankOneField_dissipative (v : E2) (t : ℝ) (x : E2) : ⟪rankOneField v t x, x⟫ ≤ 0 := by
  simp only [rankOneField, inner_neg_left, real_inner_smul_left]
  nlinarith [sq_nonneg ⟪v, x⟫]

lemma rankOneField_monotone (v : E2) (t : ℝ) (x y : E2) :
    ⟪rankOneField v t x - rankOneField v t y, x - y⟫ ≤ 0 := by
  have : rankOneField v t x - rankOneField v t y = rankOneField v t (x - y) := by
    simp only [rankOneField, inner_sub_right, sub_smul]
    abel
  rw [this]
  exact rankOneField_dissipative v t (x - y)

/-- The vector `v = e₀ + q e₁`. -/
noncomputable def vq (q : ℝ) : E2 := e 0 + q • e 1

lemma inner_e (i : Fin 2) (x : E2) : ⟪e i, x⟫ = x i := by
  simp [e, EuclideanSpace.inner_single_left]

lemma inner_vq (q : ℝ) (x : E2) : ⟪vq q, x⟫ = x 0 + q * x 1 := by
  simp only [vq, inner_add_left, real_inner_smul_left, inner_e]

lemma e_apply (i j : Fin 2) : e i j = if j = i then 1 else 0 := by
  simp [e]

lemma vq_apply (q : ℝ) (j : Fin 2) : vq q j = if j = 0 then 1 else q := by
  fin_cases j <;> simp [vq, e_apply]

/-- **Unbounded amplification of an algebraically stable SDIRK step with nested stage bases.**
Tableau `a = [[γ, 0], [1 - 2γ, γ]]`, `b = (1/2, 1/2)`, `c = (γ, 1 - γ)`, `1/2 ≤ γ ≤ 1`
(algebraically stable, `sdirk_isAlgebraicallyStable`; A-stable; second order); field
`F(x) = -⟪v, x⟫ v` with `v = e₀ + n e₁` (symmetric negative semidefinite, hence dissipative and
monotone); `h = 1`; initial value `y = e₀`; stage projectors `P₀ = e₀ e₀ᵀ ∋ y` and `P₁ = 1`
(nested), final projector `1`.  The Galerkin Runge–Kutta step exists and satisfies
`‖y₁‖ ≥ (n / 4) ‖y‖`: no bound of the form `‖y₁‖ ≤ C ‖y‖` holds uniformly in the field, in
contrast with `galerkinRK_norm_le` for one common space.  (The explicit stages are
`Y₀ = e₀/(1 + γ)`, `Y₁ = e₀ - μ v`, `y₁ = e₀ - κ v` with `μ = (1 - γ + γ²)/((1 + γ)(1 + γ S))`,
`S = 1 + n²`, `κ = (1/(1 + γ) + 1 - μ S)/2 ≥ 1/4`.)  See OP-SB-54. -/
theorem sdirk_nested_unbounded {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {n : ℝ} (hn : 0 ≤ n) :
    ∃ (Y : Fin 2 → E2) (y₁ : E2),
      IsGalerkinRKStep (rankOneField (vq n)) ![![γ, 0], ![1 - 2 * γ, γ]] ![1 / 2, 1 / 2]
        ![γ, 1 - γ] ![lineProj 0, 1] 1 0 1 (e 0) Y y₁ ∧
      lineProj 0 (e 0) = e 0 ∧ n / 4 * ‖e 0‖ ≤ ‖y₁‖ := by
  have hγ0 : 0 < 1 + γ := by linarith
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = 1 + n ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 < 1 + γ * S := by rw [hS]; positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (1 - γ + γ ^ 2) / ((1 + γ) * (1 + γ * S)) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 / (1 + γ) + 1 - μ * S) / 2 := ⟨_, rfl⟩
  have hμS : 1 - μ * S = (1 + γ + (2 * γ - 1) * S) / ((1 + γ) * (1 + γ * S)) := by
    rw [hμ]; field_simp; ring
  have hκ4 : 1 / 4 ≤ κ := by
    have h1 : 0 ≤ 1 - μ * S := by
      rw [hμS]; apply div_nonneg <;> nlinarith
    have h2 : 1 / 2 ≤ 1 / (1 + γ) := by
      rw [div_le_div_iff₀ (by norm_num) hγ0]; linarith
    rw [hκ]; linarith
  have hμ' : μ * ((1 + γ) * (1 + γ * S)) = 1 - γ + γ ^ 2 := by
    rw [hμ]; field_simp
  have hκ' : κ * 2 * (1 + γ) = 1 + (1 + γ) * (1 - μ * S) := by
    rw [hκ]; field_simp; ring
  subst hS
  refine ⟨![(1 / (1 + γ)) • e 0, (1 - μ) • e 0 + (-(μ * n)) • e 1],
    (1 - κ) • e 0 + (-(κ * n)) • e 1, ⟨fun i => ?_, ?_⟩, lineProj_self 0, ?_⟩
  · fin_cases i
    · ext j
      fin_cases j
      · simp [Fin.sum_univ_two, rankOneField, lineProj_apply, inner_e, inner_vq, e_apply, vq_apply]
        field_simp
        ring
      · simp [Fin.sum_univ_two, rankOneField, lineProj_apply, inner_e, inner_vq, e_apply, vq_apply]
    · ext j
      fin_cases j
      · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
        field_simp
        linear_combination (-1) * hμ'
      · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
        field_simp
        linear_combination (-n) * hμ'
  · ext j
    fin_cases j
    · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
      field_simp
      linear_combination (-1) * hκ'
    · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
      field_simp
      linear_combination (-n) * hκ'
  · rw [norm_e, mul_one]
    have hsq : ‖(1 - κ) • e 0 + (-(κ * n)) • e 1‖ ^ 2 = (1 - κ) ^ 2 + (κ * n) ^ 2 := by
      rw [norm_comb_sq]; ring
    have h1 : n / 4 ≤ κ * n := by nlinarith
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [hsq]
    nlinarith [sq_nonneg (1 - κ)]

/-- **The stiffly accurate SDIRK family with nested stage bases is not `L²`-stable for symmetric
negative semidefinite fields.**  Tableau `a = [[γ, 0], [1 - γ, γ]]`, `b = (1 - γ, γ)`,
`c = (γ, 1)` for `0 ≤ γ ≤ 3/10` (this contains Alexander's L-stable second-order SDIRK
`γ = 1 - √2/2 ≈ 0.293`, the DIRK2 used by RAIL, `alexander_nested_not_stable_sqrt`); field
`F(x) = -⟪v, x⟫ v`, `v = e₀ + 4 e₁`; `h = 1`; `y = e₀`; stage projectors `P₀ = e₀ e₀ᵀ ∋ y` and
`P₁ = 1`, final projector `1`, result `y₁ = Y₁` (stiffly accurate).  Then `‖Y₁‖ > ‖y‖`.  The
same step with both stages in the full space is contractive (`alexander_full_space_contractive`
for `γ ≥ 1/4`), so the loss of stability is caused by the change of Galerkin space between the
stages: first-order RAIL (2311.15143, Theorem 2) is unconditionally stable, second-order RAIL
with stage-dependent bases is not.
(Explicitly `Y₀ = e₀/(1 + γ)`, `Y₁ = (2γ(8γ + 9) e₀ - 4(1 + γ²) e₁)/((1 + γ)(1 + 17γ))`,
`‖Y₁‖² - 1 = (15 - 36γ - 2γ² - 36γ³ - 17γ⁴)/((1 + γ)(1 + 17γ))²`, amplification `≈ 1.027` at
Alexander's `γ`.)  See OP-SB-54. -/
theorem alexander_nested_not_stable {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 3 / 10) :
    ∃ Y : Fin 2 → E2,
      IsGalerkinRKStep (rankOneField (vq 4)) ![![γ, 0], ![1 - γ, γ]] ![1 - γ, γ] ![γ, 1]
        ![lineProj 0, 1] 1 0 1 (e 0) Y (Y 1) ∧
      lineProj 0 (e 0) = e 0 ∧ ‖e 0‖ < ‖Y 1‖ := by
  have hγ1 : 0 < 1 + γ := by linarith
  have hD : 0 < (1 + γ) * (1 + 17 * γ) := by positivity
  set D : ℝ := (1 + γ) * (1 + 17 * γ) with hDdef
  refine ⟨![(1 / (1 + γ)) • e 0, (2 * γ * (8 * γ + 9) / D) • e 0 + (-(4 * (1 + γ ^ 2)) / D) • e 1],
    ⟨fun i => ?_, ?_⟩, lineProj_self 0, ?_⟩
  · fin_cases i
    · ext j
      fin_cases j
      · simp [Fin.sum_univ_two, rankOneField, lineProj_apply, inner_e, inner_vq, e_apply, vq_apply]
        field_simp
        ring
      · simp [Fin.sum_univ_two, rankOneField, lineProj_apply, inner_e, inner_vq, e_apply, vq_apply]
    · ext j
      fin_cases j <;> simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply, hDdef] <;>
        field_simp <;> ring
  · ext j
    fin_cases j <;> simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply, hDdef] <;>
      field_simp <;> ring
  · rw [norm_e]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [norm_comb_sq, one_pow, div_pow, div_pow, ← add_div, lt_div_iff₀ (by positivity)]
    rw [hDdef]
    nlinarith [mul_nonneg hγ0 hγ0, mul_nonneg (mul_nonneg hγ0 hγ0) hγ0,
      mul_nonneg (mul_nonneg hγ0 hγ0) (mul_nonneg hγ0 hγ0)]

/-- Alexander's SDIRK parameter `γ = 1 - √2/2` lies in `[0, 3/10]`, so
`alexander_nested_not_stable` applies to the L-stable second-order DIRK2 of RAIL. -/
theorem alexander_nested_not_stable_sqrt :
    ∃ Y : Fin 2 → E2,
      IsGalerkinRKStep (rankOneField (vq 4)) ![![1 - √2 / 2, 0], ![1 - (1 - √2 / 2), 1 - √2 / 2]]
        ![1 - (1 - √2 / 2), 1 - √2 / 2] ![1 - √2 / 2, 1] ![lineProj 0, 1] 1 0 1 (e 0) Y (Y 1) ∧
      lineProj 0 (e 0) = e 0 ∧ ‖e 0‖ < ‖Y 1‖ := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have h1 : √2 ≤ 2 := by nlinarith
  have h3 : 7 / 5 ≤ √2 := by nlinarith
  exact alexander_nested_not_stable (by linarith) (by linarith)

/-- **Control: the same step in one Galerkin space is contractive.**  Same tableau
(`γ ≥ 1/4`, the A-stable range), same field `F(x) = -⟪v, x⟫ v`, `v = e₀ + 4 e₁`, same
data `y = e₀`, `h = 1`, but both stages in the full space (`P₀ = P₁ = 1`): then `‖Y₁‖ ≤ ‖y‖`
(explicitly `Y₁ = e₀ - ρ v`, `ρ = (1 + 17γ²)/(1 + 17γ)²`, i.e. `Y₁ = R(-17 h)` on the
`v`-component).  Together with `alexander_nested_not_stable` this isolates the change of
Galerkin space between the stages as the cause of the instability. -/
theorem alexander_full_space_contractive {γ : ℝ} (hγ0 : 1 / 4 ≤ γ) :
    ∃ Y : Fin 2 → E2,
      IsGalerkinRKStep (rankOneField (vq 4)) ![![γ, 0], ![1 - γ, γ]] ![1 - γ, γ] ![γ, 1]
        ![1, 1] 1 0 1 (e 0) Y (Y 1) ∧ ‖Y 1‖ ≤ ‖e 0‖ := by
  have hγ1 : 0 < 1 + 17 * γ := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 + 17 * γ ^ 2) / (1 + 17 * γ) ^ 2 := ⟨_, rfl⟩
  have hρ' : ρ * (1 + 17 * γ) ^ 2 = 1 + 17 * γ ^ 2 := by
    rw [hρ]; field_simp
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ2 : ρ ≤ 2 / 17 := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨![((1 + 16 * γ) / (1 + 17 * γ)) • e 0 + (-(4 * γ / (1 + 17 * γ))) • e 1,
    (1 - ρ) • e 0 + (-(4 * ρ)) • e 1], ⟨fun i => ?_, ?_⟩, ?_⟩
  · fin_cases i
    · ext j
      fin_cases j
      · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
        field_simp
        ring
      · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
        field_simp
        ring
    · ext j
      fin_cases j
      · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
        field_simp
        linear_combination (-1) * hρ'
      · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
        field_simp
        linear_combination (-1) * hρ'
  · ext j
    fin_cases j
    · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
      field_simp
      linear_combination (-1) * hρ'
    · simp [Fin.sum_univ_two, rankOneField, inner_vq, e_apply, vq_apply]
      field_simp
      linear_combination (-1) * hρ'
  · rw [norm_e]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    refine le_of_sq_le_sq ?_ zero_le_one
    rw [norm_comb_sq, one_pow]
    nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hρ2)]

end Counterexamples

end LeanDLRA.Novel.OpSB54
