import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Integrators.BUG
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Stability.Energy
import LeanDLRA.Stability.Conservation
import LeanDLRA.Integrators.Exactness

/-!
# Galerkin–Runge–Kutta BUG: exactness, stage span, robust order `p`, relaxed exactness, SSP/RK4

High-order basis-update & Galerkin (BUG) integrators replace the exact Galerkin S-flow by an
explicit Runge–Kutta (RK) method whose stages live on (augmented) low-rank bases (Nobile–Riffaud,
[NobileRiffaud2025]; BUG-p, [HauckKuschSchotthofer2026]). Everything is abstract: `E` is a real
inner product space and bases are orthogonal projectors (`IsOrthProj`). All declarations live in the
namespace `LeanDLRA.RungeKuttaBUG`.

## Main results

### Exactness and stage span (OP-HO-15)
* `IsGalerkinRKStep`: relational Galerkin RK step (stage projectors `R i`, final projector `Rf`).
* `galerkinRK_eq_rk` (OP-HO-15 (a), fully proved): for an explicit tableau, if the projectors fix
  `y` and the stage derivatives of the full RK step that enter with nonzero weight, the Galerkin RK
  step **equals** the full RK step (stages and result). Strong induction over the stages; the
  one-stage case is `projEuler_eq`.
* `rk_stage_mem`, `rk_result_mem` ([HauckKuschSchotthofer2026, Lemma 1] and property P2): every full
  RK stage and the result lie in the range of any projector fixing `y` and the relevant stage
  derivatives; `galerkinRK_stage_mem_of_nested`: with nested stage bases all Galerkin stages lie in
  the later and the final bases. Not done: OP-HO-15 (b), the explicit check that the low-storage
  SSPRK final combination of 2608.27749 lies in `span(U_n, U⁽⁴⁾, F⁽⁴⁾V⁽⁴⁾, U⁽⁹⁾, F⁽⁹⁾V⁽⁹⁾)` (a
  finite Shu–Osher-to-Butcher computation for that particular tableau); `rk_result_mem` reduces it
  to the span membership of `y` and the weighted stage derivatives.
* `IsShuOsherStep`, `galerkinShuOsher_eq` (OP-HO-15 (a) in Shu–Osher form): a Galerkin Shu–Osher
  step whose stage projectors fix the full stages and stage derivatives entering with nonzero weight
  equals the full Shu–Osher step.

### Robust order `p` of RK-BUG ([NobileRiffaud2025, Lemma 4] and Thms 1–2; OP-RA-12)
* `IsRKBUGStep`: RK-BUG step with normal components `≤ ε` and stage/final truncations `≤ h γ`.
* `IsRKBUGStep.norm_sub_rk_le` / `IsRKBUGStep.sub_rk_le`: one RK-BUG step
  deviates from the full RK step by `≤ C h (ε + γ)`, with the explicit constant
  `rkConst a b L H = (1 + H⁺L⁺Mκ^s)(M + 1)` depending only on the tableau, `L` and `H`.
* `rkBUG_global_error_le` / `rkBUG_global_error`: if the underlying RK
  method has local error `K h^{p+1}`, then `‖Y n - A tₙ‖ ≤ C (δ + ε + γ + K h^p)`.
* `rkBUG_global_error_of_tol` (OP-RA-12 (i)): with step tolerance `α h^{p+1}` for every stage and
  final truncation (rank-adaptive variant, bases and ranks changing from step to step) the order
  `p` is kept: `C (δ + ε + (α + K) h^p)`.  For OP-RA-12 (ii) (untruncated constructor) take
  `γ = 0`: the hypothesis `normalR` of `IsRKBUGStep` is then exactly the normal-component bound
  at every stage basis (rank up to `2^{s-1} r`), which is recorded as a hypothesis, not proved.
* `bugP_local_error` ([HauckKuschSchotthofer2026], P1–P2 and Thm 1): interior capture `ρ`, endpoint
  capture `θ` and an S-solver of endpoint accuracy `η` give local error `(e^{L h} - 1) ρ + θ + η`;
  `bugP_global_error`: the robust global bound `e^{LT}(δ + T(L e^{LH} ρ + θ' + η'))`.
* `bugP_local_error_of_le` (OP-HO-12 (c)): extra augmentation of the basis (conservative RK-BUG,
  `X̄ ⊇ X̂`) only decreases the capture errors, so the bounds hold verbatim.

### Relaxed exactness ([ZhangHu2026b], Thms 4.1, 4.3, 5.1)
* `relaxed_exactness`: `Y₁ = P X`, `P (M X) = M X`, `M Y⋆ = Y⋆`, `‖M‖ ≤ Λ` give
  `‖Y₁ - Y⋆‖ ≤ (1 + Λ)‖X - Y⋆‖` (for the reduced K–L step: `P = U₁U₁ᵀ`, `X = Y₀ + ΔA`,
  `M Z = Z V₀ Q`).
* `relaxed_global_error`: global error `e^{LT}(δ + T((1 + Λ) d/h + (2 + Λ) c ε))` from the
  increment error `d`; the comparison curve of Lemma 4.2 (`‖Q‖₂ ≤ 3`) is a hypothesis.

### SSP and RK4 stability (OP-HO-09, OP-SB-06)
* `shuOsher_norm_le`, `sspGalerkin_norm_le` (OP-HO-09 (a), OP-SB-06 nonlinear part): Shu–Osher
  stages built from Galerkin forward-Euler steps (`galerkinEulerStep`) and norm-nonincreasing
  truncations are norm-nonincreasing whenever `h βᵢₖ ≤ αᵢₖ τ_CFL` (`h ≤ c_SSP τ_CFL`).
* `sspLowRank_norm_le` (OP-HO-09 (a), projection after each stage).
* `shuOsher_perturb_le` (OP-HO-09 (b), partial): with `Λ`-Lipschitz stage maps, per-stage
  truncation errors `δ` add up to at most `s Λ^s δ`.  `perturbedRK_le` (OP-HO-09 (b), Butcher
  form): per-stage errors `ηᵢ` and final error `η₁` give
  `‖y₁ - z₁‖ ≤ η₁ + C h ∑ ηᵢ`, `C = L⁺ M κ^s`.  So stage tolerances `O(h^{p+1})` keep order `p`
  *relative to the underlying RK method*; not done: the order-`p` statement when the tolerances
  are the actual rank-`r` truncation errors (generically only `O(h² + h ε)` per stage, OP-HO-21).
* `rk4Lin_eq`: the classical RK4 step for `x' = B x` equals
  `3/8 + 1/3 G + 1/4 G² + 1/24 G⁴` with `G = 1 + hB` (the identity `R(z) = ∑ cₖ (1+z)^k`,
  `c = (3/8, 1/3, 1/4, 0, 1/24)`); `rk4Lin_norm_le`, `galerkinRK4_norm_le` (OP-SB-06, linear
  part): if `‖x + h A x‖ ≤ ‖x‖` on `range P`, the RK4 step of the Galerkin operator `P A P` is
  norm-nonincreasing on `range P`.  `galerkin_ssp_linear_norm_le` (general absolutely monotonic
  polynomial `∑ cₖ (1 + z)^k`, `cₖ ≥ 0`), `galerkin_rk4_taylor_norm_le` (RK4 in Taylor form) and
  `galerkin_sspRK2_norm_le` (nonlinear Heun) prove the three OP-SB-06 statements, with contractivity
  assumed only on `range P`. Not done: the numerical-range (disk) condition for operators with `‖I +
  hA‖ > 1`.

## What remains open
OP-HO-15 (b) (specific low-storage tableau), OP-HO-09 (b) full order `p` for SSP-BUG with
actual rank-`r` stage truncation (only a reduction to stage tolerances is proved), OP-RA-12 (ii)
proof of the normal-component bounds at rank `2^{s-1} r`, (iii)
dropped pre-augmented directions, (iv) the `r₀` heuristic, (v) the accuracy comparison,
and OP-HO-12 (a), (b), (d).
-/

open Set Finset

universe u

namespace LeanDLRA.RungeKuttaBUG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A (Galerkin) **Runge–Kutta step** in relational form: tableau `(a, b, c)` with `s` stages,
stage projectors `R i`, final projector `Rf`, stages `Y i = R i (y + h ∑ⱼ aᵢⱼ F(t + cⱼ h, Y j))`
and result `y₁ = Rf (y + h ∑ᵢ bᵢ F(t + cᵢ h, Y i))`. With `R i = 1`, `Rf = 1` this is the full
Runge–Kutta step (explicit when `a` is strictly lower triangular). -/
def IsGalerkinRKStep {s : ℕ} (F : ℝ → E → E) (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (R : Fin s → E →L[ℝ] E) (Rf : E →L[ℝ] E) (t h : ℝ) (y : E) (Y : Fin s → E) (y₁ : E) :
    Prop :=
  (∀ i, Y i = R i (y + h • ∑ j, a i j • F (t + c j * h) (Y j))) ∧
    y₁ = Rf (y + h • ∑ i, b i • F (t + c i * h) (Y i))

/-- A projector fixing `y` and the directions `v j` with nonzero weight maps the combination
`y + h ∑ wⱼ vⱼ` to itself. -/
lemma proj_comb_eq {s : ℕ} {R : E →L[ℝ] E} {y : E} (hy : R y = y) {w : Fin s → ℝ}
    {v : Fin s → E} (hv : ∀ j, w j ≠ 0 → R (v j) = v j) (h : ℝ) :
    R (y + h • ∑ j, w j • v j) = y + h • ∑ j, w j • v j := by
  rw [map_add, map_smul, map_sum, hy]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hw : w j = 0
  · simp [hw]
  · rw [map_smul, hv j hw]

/-- **Galerkin–Runge–Kutta exactness** (OP-HO-15 (a); [YeYang2025], [HauckKuschSchotthofer2026]).
For an explicit tableau, if the stage and final projectors fix `y` and every stage derivative of
the full Runge–Kutta step that enters with a nonzero weight, the Galerkin Runge–Kutta step
coincides with the full one (stages and result). The one-stage case is `projEuler_eq`. -/
theorem galerkinRK_eq_rk {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E} {t h : ℝ} {y : E}
    {Y Z : Fin s → E} {y₁ z₁ : E} (hG : IsGalerkinRKStep F a b c R Rf t h y Y y₁)
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁) (hRy : ∀ i, R i y = y)
    (hRfy : Rf y = y)
    (hRF : ∀ i j, a i j ≠ 0 → R i (F (t + c j * h) (Z j)) = F (t + c j * h) (Z j))
    (hRfF : ∀ i, b i ≠ 0 → Rf (F (t + c i * h) (Z i)) = F (t + c i * h) (Z i)) :
    Y = Z ∧ y₁ = z₁ := by
  have key : ∀ k : ℕ, ∀ i : Fin s, i.val < k → Y i = Z i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      have hsum : ∑ j, a i j • F (t + c j * h) (Y j) = ∑ j, a i j • F (t + c j * h) (Z j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hw : a i j = 0
        · simp [hw]
        · have hji : j < i := lt_of_not_ge fun hij => hw (ha i j hij)
          rw [ih j (by have : j.val < i.val := hji; omega)]
      rw [hG.1 i, hZ.1 i, hsum, proj_comb_eq (hRy i) (hRF i) h]
      simp
  have hYZ : Y = Z := funext fun i => key s i i.isLt
  refine ⟨hYZ, ?_⟩
  rw [hG.2, hZ.2, hYZ, proj_comb_eq hRfy hRfF h]
  simp

/-! ### Perturbation of Galerkin Runge–Kutta steps -/

/-- Perturbation of one projected Runge–Kutta combination: if `R` fixes `y` and the directions
`u j` with nonzero weight are captured up to `ε`, then
`‖R (y + h ∑ wⱼ uⱼ) - (y + h ∑ wⱼ vⱼ)‖ ≤ h ∑ |wⱼ| (‖uⱼ - vⱼ‖ + ε)`. -/
lemma norm_proj_comb_sub_le {s : ℕ} {R : E →L[ℝ] E} {y : E} (hy : R y = y) {w : Fin s → ℝ}
    {u v : Fin s → E} {ε h : ℝ} (hh : 0 ≤ h) (hu : ∀ j, w j ≠ 0 → ‖(1 - R) (u j)‖ ≤ ε) :
    ‖R (y + h • ∑ j, w j • u j) - (y + h • ∑ j, w j • v j)‖ ≤
      h * ∑ j, |w j| * (‖u j - v j‖ + ε) := by
  have hrw : R (y + h • ∑ j, w j • u j) - (y + h • ∑ j, w j • v j) =
      h • ∑ j, w j • (R (u j) - v j) := by
    rw [map_add, map_smul, map_sum, hy]
    simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [hrw, norm_smul, Real.norm_of_nonneg hh]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)) hh
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hw : w j = 0
  · simp [hw]
  · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hsplit : R (u j) - v j = (u j - v j) - (1 - R) (u j) := by
      simp only [sub_apply, one_apply_eq_self]
      abel
    rw [hsplit]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hu j hw))

/-- One step of the **Runge–Kutta BUG integrator** (Nobile–Riffaud, [NobileRiffaud2025],
Algorithm 2) in abstract form: Galerkin Runge–Kutta stages on augmented bases (projectors
`R i`, `Rf` fixing `y` and capturing the stage derivatives with nonzero weight up to `ε`), each
stage and the result computed up to a truncation error `h γ`. -/
structure IsRKBUGStep {s : ℕ} (F : ℝ → E → E) (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (ε γ : ℝ) (R : Fin s → E →L[ℝ] E) (Rf : E →L[ℝ] E) (t h : ℝ) (y : E) (Y : Fin s → E)
    (y₁ : E) : Prop where
  projR : ∀ i, IsOrthProj (R i)
  projRf : IsOrthProj Rf
  fixR : ∀ i, R i y = y
  fixRf : Rf y = y
  normalR : ∀ i j, a i j ≠ 0 → ‖(1 - R i) (F (t + c j * h) (Y j))‖ ≤ ε
  normalRf : ∀ i, b i ≠ 0 → ‖(1 - Rf) (F (t + c i * h) (Y i))‖ ≤ ε
  /-- Stage truncation (`γ = 0`: no internal truncation). -/
  stage : ∀ i, ‖Y i - R i (y + h • ∑ j, a i j • F (t + c j * h) (Y j))‖ ≤ h * γ
  /-- Final truncation. -/
  final : ‖y₁ - Rf (y + h • ∑ i, b i • F (t + c i * h) (Y i))‖ ≤ h * γ

/-- Total absolute weight `∑ᵢⱼ |aᵢⱼ| + ∑ᵢ |bᵢ|` of a tableau. -/
def tabWeight {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) : ℝ :=
  ∑ i, ∑ j, |a i j| + ∑ i, |b i|

/-- Stage amplification factor `κ = 1 + H⁺ L⁺ M` of an explicit tableau. -/
def tabKappa {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L H : ℝ) : ℝ :=
  1 + max H 0 * max L 0 * tabWeight a b

/-- The explicit constant of `IsRKBUGStep.norm_sub_rk_le`:
`(1 + H⁺ L⁺ M κ^s) (M + 1)`; it depends only on the tableau, `L` and `H`. -/
def rkConst {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L H : ℝ) : ℝ :=
  (1 + max H 0 * max L 0 * tabWeight a b * tabKappa a b L H ^ s) * (tabWeight a b + 1)

lemma tabWeight_nonneg {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) : 0 ≤ tabWeight a b :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma row_le_tabWeight {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (i : Fin s) :
    ∑ j, |a i j| ≤ tabWeight a b := by
  have h1 : ∑ j, |a i j| ≤ ∑ i, ∑ j, |a i j| :=
    Finset.single_le_sum (f := fun i => ∑ j, |a i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold tabWeight; linarith

lemma b_le_tabWeight {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) :
    ∑ i, |b i| ≤ tabWeight a b := by
  have h2 : 0 ≤ ∑ i, ∑ j, |a i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold tabWeight; linarith

lemma one_le_tabKappa {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L H : ℝ) :
    1 ≤ tabKappa a b L H := by
  have := tabWeight_nonneg a b
  unfold tabKappa
  have : 0 ≤ max H 0 * max L 0 * tabWeight a b :=
    mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) this
  linarith

lemma rkConst_nonneg {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L H : ℝ) :
    0 ≤ rkConst a b L H := by
  have hM := tabWeight_nonneg a b
  have hκ := one_le_tabKappa a b L H
  unfold rkConst
  refine mul_nonneg ?_ (by linarith)
  have : 0 ≤ max H 0 * max L 0 * tabWeight a b * tabKappa a b L H ^ s :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) hM)
      (pow_nonneg (by linarith) _)
  linarith

/-- Weighted row sums are bounded by the tableau weight times the uniform bound. -/
lemma sum_abs_mul_le {s : ℕ} {w : Fin s → ℝ} {D : Fin s → ℝ} {X M : ℝ} (hX : 0 ≤ X)
    (hD : ∀ j, w j ≠ 0 → D j ≤ X) (hw : ∑ j, |w j| ≤ M) : ∑ j, |w j| * D j ≤ M * X := by
  calc ∑ j, |w j| * D j ≤ ∑ j, |w j| * X := Finset.sum_le_sum fun j _ => by
        by_cases h0 : w j = 0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (hD j h0) (abs_nonneg _)
    _ = (∑ j, |w j|) * X := by rw [Finset.sum_mul]
    _ ≤ M * X := mul_le_mul_of_nonneg_right hw hX

/-- **RK-BUG versus full Runge–Kutta, explicit constant** ([NobileRiffaud2025, Lemma 4] and (39) in
the proof of Thm 1). For an explicit tableau and `0 ≤ h ≤ H`, one RK-BUG step deviates from the
full Runge–Kutta step from the same starting value by `≤ rkConst a b L H · h (ε + γ)`, where
`rkConst a b L H = (1 + H⁺ L⁺ M κ^s)(M + 1)`, `M = ∑|aᵢⱼ| + ∑|bᵢ|`, `κ = 1 + H⁺ L⁺ M`
(independent of `E`, the rank and singular values).  The proof is a stage-wise perturbation
estimate (`norm_proj_comb_sub_le`) and an induction over the stages giving
`‖Yᵢ - Zᵢ‖ ≤ κ^{i+1} h (γ + M ε)`. -/
theorem IsRKBUGStep.norm_sub_rk_le {s : ℕ} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {L H : ℝ} {F : ℝ → E → E} {ε γ t h : ℝ}
    {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E} {y y₁ z₁ : E} {Y Z : Fin s → E}
    (hF : IsLipschitzField F L) (hh : 0 ≤ h) (hH : h ≤ H) (hε : 0 ≤ ε)
    (hS : IsRKBUGStep F a b c ε γ R Rf t h y Y y₁)
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁) :
    ‖y₁ - z₁‖ ≤ rkConst a b L H * h * (ε + γ) := by
  set M := tabWeight a b with hMdef
  set κ := tabKappa a b L H with hκdef
  have hM : 0 ≤ M := tabWeight_nonneg a b
  have hκ : 1 ≤ κ := one_le_tabKappa a b L H
  have hLp : 0 ≤ max L 0 := le_max_right _ _
  have hHp : h ≤ max H 0 := hH.trans (le_max_left _ _)
  have hhγ : 0 ≤ h * γ := (norm_nonneg _).trans hS.final
  have hhε : 0 ≤ h * ε := mul_nonneg hh hε
  set e := h * γ + h * (M * ε) with he
  have he0 : 0 ≤ e := add_nonneg hhγ (by nlinarith)
  have hLip : ∀ t x z, ‖F t x - F t z‖ ≤ max L 0 * ‖x - z‖ := fun t x z =>
    (hF t x z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hZi : ∀ i, Z i = y + h • ∑ j, a i j • F (t + c j * h) (Z j) := fun i => by
    rw [hZ.1 i]; rfl
  have hz₁ : z₁ = y + h • ∑ i, b i • F (t + c i * h) (Z i) := by rw [hZ.2]; rfl
  -- generic step: a combination whose inputs are within `X` produces an error `≤ e + h M L⁺ X`
  have hgen : ∀ (Rp : E →L[ℝ] E) (w : Fin s → ℝ) (u : E) (X : ℝ), 0 ≤ X → Rp y = y →
      (∀ j, w j ≠ 0 → ‖(1 - Rp) (F (t + c j * h) (Y j))‖ ≤ ε) →
      (∀ j, w j ≠ 0 → ‖Y j - Z j‖ ≤ X) → ∑ j, |w j| ≤ M →
      ‖u - Rp (y + h • ∑ j, w j • F (t + c j * h) (Y j))‖ ≤ h * γ →
      ‖u - (y + h • ∑ j, w j • F (t + c j * h) (Z j))‖ ≤ e + max H 0 * max L 0 * M * X := by
    intro Rp w u X hX hRy hcap hD hw htr
    have h1 := norm_proj_comb_sub_le (v := fun j => F (t + c j * h) (Z j)) hRy hh hcap
    have h2 : ∑ j, |w j| * (‖F (t + c j * h) (Y j) - F (t + c j * h) (Z j)‖ + ε) ≤
        M * (max L 0 * X + ε) :=
      sum_abs_mul_le (by positivity) (fun j hj => by
        have := hLip (t + c j * h) (Y j) (Z j)
        have := mul_le_mul_of_nonneg_left (hD j hj) hLp
        linarith) hw
    have h3 : h * (M * (max L 0 * X + ε)) ≤ h * γ * 0 + h * (M * ε) +
        max H 0 * max L 0 * M * X := by
      have : h * (M * (max L 0 * X)) ≤ max H 0 * (M * (max L 0 * X)) :=
        mul_le_mul_of_nonneg_right hHp (by positivity)
      nlinarith
    calc ‖u - (y + h • ∑ j, w j • F (t + c j * h) (Z j))‖
        ≤ ‖u - Rp (y + h • ∑ j, w j • F (t + c j * h) (Y j))‖ +
          ‖Rp (y + h • ∑ j, w j • F (t + c j * h) (Y j)) -
            (y + h • ∑ j, w j • F (t + c j * h) (Z j))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ h * γ + h * (M * (max L 0 * X + ε)) :=
          add_le_add htr (h1.trans (mul_le_mul_of_nonneg_left h2 hh))
      _ ≤ e + max H 0 * max L 0 * M * X := by rw [he]; linarith
  have key : ∀ k : ℕ, ∀ i : Fin s, i.val < k → ‖Y i - Z i‖ ≤ κ ^ k * e := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      have hX : 0 ≤ κ ^ k * e := mul_nonneg (pow_nonneg (by linarith) _) he0
      have hstep := hgen (R i) (a i) (Y i) (κ ^ k * e) hX (hS.fixR i) (hS.normalR i)
        (fun j hj => ih j (by
          have hji : j < i := lt_of_not_ge fun hij => hj (ha i j hij)
          have : j.val < i.val := hji
          omega)) (row_le_tabWeight a b i) (hS.stage i)
      rw [← hZi i] at hstep
      have hκk : 1 ≤ κ ^ k := one_le_pow₀ hκ
      calc ‖Y i - Z i‖ ≤ e + max H 0 * max L 0 * M * (κ ^ k * e) := hstep
        _ ≤ κ ^ k * e + max H 0 * max L 0 * M * (κ ^ k * e) := by nlinarith
        _ = κ ^ (k + 1) * e := by rw [hκdef, tabKappa, ← hMdef]; ring
  have hX : 0 ≤ κ ^ s * e := mul_nonneg (pow_nonneg (by linarith) _) he0
  have hfin := hgen Rf b y₁ (κ ^ s * e) hX hS.fixRf hS.normalRf
    (fun i _ => key s i i.isLt) (b_le_tabWeight a b) hS.final
  rw [← hz₁] at hfin
  have heM : e ≤ (M + 1) * h * (ε + γ) := by rw [he]; nlinarith
  have hA : 0 ≤ 1 + max H 0 * max L 0 * M * κ ^ s := by
    have : 0 ≤ max H 0 * max L 0 * M * κ ^ s :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) hLp) hM) (pow_nonneg (by linarith) _)
    linarith
  calc ‖y₁ - z₁‖ ≤ e + max H 0 * max L 0 * M * (κ ^ s * e) := hfin
    _ = (1 + max H 0 * max L 0 * M * κ ^ s) * e := by ring
    _ ≤ (1 + max H 0 * max L 0 * M * κ ^ s) * ((M + 1) * h * (ε + γ)) :=
        mul_le_mul_of_nonneg_left heM hA
    _ = rkConst a b L H * h * (ε + γ) := by rw [rkConst, ← hMdef, ← hκdef]; ring

/-- **RK-BUG versus full Runge–Kutta** in robust `∃ C` form ([NobileRiffaud2025, Lemma 4]): the
constant is `rkConst a b L H` and depends only on the tableau, `L` and `H` (it is chosen before
the space `E`). -/
theorem IsRKBUGStep.sub_rk_le {s : ℕ} (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (ha : ∀ i j, i ≤ j → a i j = 0) (L H : ℝ) :
    ∃ C : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
      {ε γ t h : ℝ} {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E} {y y₁ z₁ : E} {Y Z : Fin s → E},
      IsLipschitzField F L → 0 ≤ h → h ≤ H → 0 ≤ ε →
      IsRKBUGStep F a b c ε γ R Rf t h y Y y₁ →
      IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁ →
      ‖y₁ - z₁‖ ≤ C * h * (ε + γ) :=
  ⟨rkConst a b L H, fun hF hh hH hε hS hZ => hS.norm_sub_rk_le ha hF hh hH hε hZ⟩

/-- The explicit constant of `rkBUG_global_error_le`: `e^{L T} (1 + T⁺ (rkConst + 1))`. -/
noncomputable def rkGlobalConst {s : ℕ} (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L T H : ℝ) : ℝ :=
  Real.exp (L * T) * (1 + max T 0 * (rkConst a b L H + 1))

/-- **Robust order `p` of the RK-BUG integrator, explicit constant** ([NobileRiffaud2025, Thm. 2];
reduces OP-HO-21 (i) to the truncation hypothesis: the bound `h γ ≲ h (ε + h^p)` on the stage and
final truncations is assumed, not derived from Eckart–Young here). If the underlying explicit
Runge–Kutta method has local error `≤ K h^{p+1}` along
the exact flows `Φ n` started at the iterates, the RK-BUG iterates satisfy
`‖Y n - A tₙ‖ ≤ rkGlobalConst · (‖Y 0 - A t₀‖ + ε + γ + K h^p)` for `n h ≤ T`.  With exact stages
(`γ = 0`) this is robust order `p` up to the normal components `ε`; with a truncation tolerance
`h γ = α h^{p+1}` it is still order `p` (`rkBUG_global_error_of_tol`). -/
theorem rkBUG_global_error_le {s : ℕ} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {L T H : ℝ} {F : ℝ → E → E}
    {ε γ K t₀ h : ℝ} {p N : ℕ} {A : ℝ → E} {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hH : h ≤ H) (hε : 0 ≤ ε)
    (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hstep : ∀ n < N, ∃ (R : Fin s → E →L[ℝ] E) (Rf : E →L[ℝ] E) (Ys Zs : Fin s → E) (z₁ : E),
      IsRKBUGStep F a b c ε γ R Rf (t₀ + n * h) h (Y n) Ys (Y (n + 1)) ∧
      IsGalerkinRKStep F a b c (fun _ => 1) 1 (t₀ + n * h) h (Y n) Zs z₁ ∧
      ‖z₁ - Φ n (t₀ + (n + 1) * h)‖ ≤ K * h ^ (p + 1)) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ rkGlobalConst a b L T H * (‖Y 0 - A t₀‖ + ε + γ + K * h ^ p) := by
  set C₁ := rkConst a b L H with hC₁
  have hC₁0 : 0 ≤ C₁ := rkConst_nonneg a b L H
  have hhp : 0 ≤ h ^ p := pow_nonneg hh p
  have hg : 0 ≤ C₁ * (ε + γ) + K * h ^ p :=
    add_nonneg (mul_nonneg hC₁0 (add_nonneg hε hγ)) (mul_nonneg hK hhp)
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * (C₁ * (ε + γ) + K * h ^ p) := by
    intro n hn
    obtain ⟨R, Rf, Ys, Zs, z₁, hS, hZ, hz⟩ := hstep n hn
    have h1 := hS.norm_sub_rk_le ha hF hh hH hε hZ
    calc ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖
        ≤ ‖Y (n + 1) - z₁‖ + ‖z₁ - Φ n (t₀ + (n + 1) * h)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C₁ * h * (ε + γ) + K * h ^ (p + 1) := add_le_add h1 hz
      _ = h * (C₁ * (ε + γ) + K * h ^ p) := by ring
  intro n hn hT
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg n) hh).trans hT
  have hmain := lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc n hn hT
  have hX := norm_nonneg (Y 0 - A t₀)
  have hKh := mul_nonneg hK hhp
  have hbr : ‖Y 0 - A t₀‖ + T * (C₁ * (ε + γ) + K * h ^ p) ≤
      (1 + max T 0 * (C₁ + 1)) * (‖Y 0 - A t₀‖ + ε + γ + K * h ^ p) := by
    rw [max_eq_left hT0]
    nlinarith [mul_nonneg hT0 hX, mul_nonneg (mul_nonneg hT0 hC₁0) hX, mul_nonneg hT0 hε,
      mul_nonneg hT0 hγ, mul_nonneg (mul_nonneg hT0 hC₁0) hKh, mul_nonneg hT0 hKh]
  calc ‖Y n - A (t₀ + n * h)‖
      ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (C₁ * (ε + γ) + K * h ^ p)) := hmain
    _ ≤ Real.exp (L * T) * ((1 + max T 0 * (C₁ + 1)) * (‖Y 0 - A t₀‖ + ε + γ + K * h ^ p)) :=
        mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le
    _ = rkGlobalConst a b L T H * (‖Y 0 - A t₀‖ + ε + γ + K * h ^ p) := by
        rw [rkGlobalConst, ← hC₁]; ring

/-- **Robust order `p` of the RK-BUG integrator** in robust `∃ C` form ([NobileRiffaud2025, Thm. 2];
OP-HO-21 (i) modulo the truncation hypothesis, see `rkBUG_global_error_le`); `C = rkGlobalConst a b
L T H` depends only on the tableau, `L`, `T`, `H`. -/
theorem rkBUG_global_error {s : ℕ} (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (ha : ∀ i j, i ≤ j → a i j = 0) (L T H : ℝ) :
    ∃ C : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
      {ε γ K t₀ h : ℝ} {p N : ℕ} {A : ℝ → E} {Y : ℕ → E} {Φ : ℕ → ℝ → E},
      IsLipschitzField F L → 0 ≤ L → 0 ≤ h → h ≤ H → 0 ≤ ε → 0 ≤ γ → 0 ≤ K →
      ODESolution F A t₀ (t₀ + N * h) →
      (∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h)) →
      (∀ n < N, Φ n (t₀ + n * h) = Y n) →
      (∀ n < N, ∃ (R : Fin s → E →L[ℝ] E) (Rf : E →L[ℝ] E) (Ys Zs : Fin s → E) (z₁ : E),
        IsRKBUGStep F a b c ε γ R Rf (t₀ + n * h) h (Y n) Ys (Y (n + 1)) ∧
        IsGalerkinRKStep F a b c (fun _ => 1) 1 (t₀ + n * h) h (Y n) Zs z₁ ∧
        ‖z₁ - Φ n (t₀ + (n + 1) * h)‖ ≤ K * h ^ (p + 1)) →
      ∀ n ≤ N, (n : ℝ) * h ≤ T →
        ‖Y n - A (t₀ + n * h)‖ ≤ C * (‖Y 0 - A t₀‖ + ε + γ + K * h ^ p) :=
  ⟨rkGlobalConst a b L T H, fun hF hL hh hH hε hγ hK hA hΦ hΦ₀ hstep =>
    rkBUG_global_error_le ha hF hL hh hH hε hγ hK hA hΦ hΦ₀ hstep⟩

/-- **Rank-adaptive RK-BUG with step tolerance `α h^{p+1}` keeps order `p`** (OP-RA-12 (i);
[NobileRiffaud2025, Sec. 3], tolerance strategy). If every stage and the final truncation of each
step are accurate to `α h^{p+1}` (i.e. `γ = α h^p` in `IsRKBUGStep`; the bases `R`, `Rf` and hence
the ranks may change from step to step), then
`‖Y n - A tₙ‖ ≤ C (‖Y 0 - A t₀‖ + ε + (α + K) h^p)`.  The relative `β`-term of the tolerance and
the conservative variant are not covered. -/
theorem rkBUG_global_error_of_tol {s : ℕ} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {L T H : ℝ} {F : ℝ → E → E}
    {ε α K t₀ h : ℝ} {p N : ℕ} {A : ℝ → E} {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hH : h ≤ H) (hε : 0 ≤ ε)
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hstep : ∀ n < N, ∃ (R : Fin s → E →L[ℝ] E) (Rf : E →L[ℝ] E) (Ys Zs : Fin s → E) (z₁ : E),
      IsRKBUGStep F a b c ε (α * h ^ p) R Rf (t₀ + n * h) h (Y n) Ys (Y (n + 1)) ∧
      IsGalerkinRKStep F a b c (fun _ => 1) 1 (t₀ + n * h) h (Y n) Zs z₁ ∧
      ‖z₁ - Φ n (t₀ + (n + 1) * h)‖ ≤ K * h ^ (p + 1)) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        rkGlobalConst a b L T H * (‖Y 0 - A t₀‖ + ε + (α + K) * h ^ p) := by
  intro n hn hT
  have := rkBUG_global_error_le ha hF hL hh hH hε (mul_nonneg hα (pow_nonneg hh p)) hK hA hΦ hΦ₀
    hstep n hn hT
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The hypotheses of `IsRKBUGStep` are satisfiable with a nonzero normal component and a
nonzero truncation: on `ℝ`, the two-stage tableau `a₁₀ = 1`, `b = (0, 1)` (explicit Euler
twice), field `F(t, x) = x + 1`, stage projectors `0` (which do not capture `F(Y₀) = 1`, so
`ε = 1`), final projector `1`, `y = 0`, `h = 1`, and a result `y₁ = 3/2` that is off by the
truncation `h γ = 1/2`. -/
example : IsRKBUGStep (E := ℝ) (s := 2) (fun _ x => x + 1) ![![0, 0], ![1, 0]] ![0, 1] 0 1 (1 / 2)
    (fun _ => 0) 1 0 1 0 (fun _ => 0) (3 / 2) where
  projR _ := ⟨fun _ => rfl, fun _ _ => by simp⟩
  projRf := ⟨fun _ => rfl, fun _ _ => rfl⟩
  fixR _ := rfl
  fixRf := rfl
  normalR i j _ := by simp
  normalRf i _ := by simp
  stage i := by simp
  final := by
    simp [Fin.sum_univ_two]
    norm_num

/-! ### Stage-span lemmas ([HauckKuschSchotthofer2026, Lemma 1]) -/

/-- **Stage-span of the full Runge–Kutta step** ([HauckKuschSchotthofer2026, Lemma 1]): the `i`-th
stage `Zᵢ = y + h ∑ⱼ aᵢⱼ F(Zⱼ)` lies in the range of every linear projector that fixes `y` and the
stage derivatives `F(Zⱼ)` entering it with nonzero weight. -/
theorem rk_stage_mem {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    {t h : ℝ} {y z₁ : E} {Z : Fin s → E}
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁) {P : E →L[ℝ] E} (hy : P y = y)
    (i : Fin s) (hF : ∀ j, a i j ≠ 0 → P (F (t + c j * h) (Z j)) = F (t + c j * h) (Z j)) :
    P (Z i) = Z i := by
  have hZi : Z i = y + h • ∑ j, a i j • F (t + c j * h) (Z j) := by rw [hZ.1 i]; rfl
  rw [hZi]
  exact proj_comb_eq hy hF h

/-- **Result-span of the full Runge–Kutta step**: the result `z₁ = y + h ∑ᵢ bᵢ F(Zᵢ)` lies in
the range of every linear projector fixing `y` and the stage derivatives with `bᵢ ≠ 0`. This is
the admissibility property P2 of [HauckKuschSchotthofer2026] (Sec. 3.1) for a single final basis. -/
theorem rk_result_mem {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    {t h : ℝ} {y z₁ : E} {Z : Fin s → E}
    (hZ : IsGalerkinRKStep F a b c (fun _ => 1) 1 t h y Z z₁) {P : E →L[ℝ] E} (hy : P y = y)
    (hF : ∀ i, b i ≠ 0 → P (F (t + c i * h) (Z i)) = F (t + c i * h) (Z i)) :
    P z₁ = z₁ := by
  have hz : z₁ = y + h • ∑ i, b i • F (t + c i * h) (Z i) := by rw [hZ.2]; rfl
  rw [hz]
  exact proj_comb_eq hy hF h

/-- **Nested Galerkin stages** ([HauckKuschSchotthofer2026, Lemma 1], BUG-p bases): if the stage
projectors are nested (`R k (R i x) = R i x` for `i ≤ k`, i.e. `range R i ⊆ range R k`) and the
final projector contains all of them, every Galerkin stage `Yᵢ` lies in `range R k` for `k ≥ i`
and in `range Rf`. -/
theorem galerkinRK_stage_mem_of_nested {s : ℕ} {F : ℝ → E → E} {a : Fin s → Fin s → ℝ}
    {b c : Fin s → ℝ} {R : Fin s → E →L[ℝ] E} {Rf : E →L[ℝ] E} {t h : ℝ} {y y₁ : E}
    {Y : Fin s → E} (hG : IsGalerkinRKStep F a b c R Rf t h y Y y₁)
    (hnest : ∀ i k, i ≤ k → ∀ x, R k (R i x) = R i x) (hfin : ∀ i x, Rf (R i x) = R i x) :
    (∀ i k, i ≤ k → R k (Y i) = Y i) ∧ (∀ i, Rf (Y i) = Y i) := by
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [hG.1 i]; exact hnest i k hik _
  · rw [hG.1 i]; exact hfin i _

/-! ### SSP Runge–Kutta methods in Shu–Osher form (OP-HO-09, OP-SB-06) -/

/-- **SSP inheritance for Shu–Osher schemes** (OP-HO-09 (a), OP-SB-06, nonlinear part).  Stages
`u (i+1) = ∑_{k ≤ i} αᵢₖ Tᵢₖ (u k)` with `αᵢₖ ≥ 0`, `∑ₖ αᵢₖ = 1` and maps `Tᵢₖ` that are
norm-nonincreasing whenever `αᵢₖ ≠ 0`: every stage satisfies `‖u i‖ ≤ ‖u 0‖`.  The maps are
arbitrary (in the low-rank schemes: Galerkin Euler steps followed by truncations or
corrections, `sspGalerkin_norm_le`). -/
theorem shuOsher_norm_le {s : ℕ} {u : ℕ → E} {α : ℕ → ℕ → ℝ} {T : ℕ → ℕ → E → E}
    (hα : ∀ i k, 0 ≤ α i k) (hsum : ∀ i < s, ∑ k ∈ range (i + 1), α i k = 1)
    (hT : ∀ i < s, ∀ k ≤ i, α i k ≠ 0 → ∀ z, ‖T i k z‖ ≤ ‖z‖)
    (hu : ∀ i < s, u (i + 1) = ∑ k ∈ range (i + 1), α i k • T i k (u k)) :
    ∀ i ≤ s, ‖u i‖ ≤ ‖u 0‖ := by
  have key : ∀ m : ℕ, ∀ i ≤ m, i ≤ s → ‖u i‖ ≤ ‖u 0‖ := by
    intro m
    induction m with
    | zero => intro i hi _; rw [Nat.le_zero.1 hi]
    | succ m ih =>
      intro i hi his
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · exact ih i (by omega) his
      · have him : i = m + 1 := by omega
        subst him
        have hms : m < s := by omega
        rw [hu m hms]
        calc ‖∑ k ∈ range (m + 1), α m k • T m k (u k)‖
            ≤ ∑ k ∈ range (m + 1), ‖α m k • T m k (u k)‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ range (m + 1), α m k * ‖u 0‖ := Finset.sum_le_sum fun k hk => by
              rw [norm_smul, Real.norm_of_nonneg (hα m k)]
              have hkm : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
              by_cases h0 : α m k = 0
              · simp [h0]
              · exact mul_le_mul_of_nonneg_left
                  ((hT m hms k hkm h0 _).trans (ih k hkm (by omega))) (hα m k)
          _ = ‖u 0‖ := by rw [← Finset.sum_mul, hsum m hms, one_mul]
  exact fun i hi => key i i le_rfl hi

/-- **SSP Runge–Kutta low-rank schemes are `L²`-stable under the forward-Euler CFL condition**
(OP-HO-09 (a); [HauckSchnake2023] Sec. 7, [LiEtAl2026a] Sec. 6, [UschmajewZeiser2026] Sec. 6).
Shu–Osher stages `u (i+1) = ∑_{k ≤ i} αᵢₖ Θᵢₖ(Pᵢₖ (Pᵢₖ u k + τᵢₖ F(Pᵢₖ u k)))` with Euler step
sizes `τᵢₖ = h βᵢₖ / αᵢₖ`, Galerkin projectors `Pᵢₖ` (arbitrary, step- and stage-dependent) and
norm-nonincreasing truncations/corrections `Θᵢₖ`.  If the full forward-Euler step
`x ↦ x + τ F(x)` is norm-nonincreasing on the Galerkin ranges for `0 ≤ τ ≤ τ_CFL`, and
`h βᵢₖ ≤ αᵢₖ τ_CFL` (that is, `h ≤ c_SSP τ_CFL` with `c_SSP = min αᵢₖ / βᵢₖ`), then every stage
satisfies `‖u i‖ ≤ ‖u 0‖`. -/
theorem sspGalerkin_norm_le {s : ℕ} {u : ℕ → E} {α β : ℕ → ℕ → ℝ} {h τCFL : ℝ}
    {P : ℕ → ℕ → E →L[ℝ] E} {F : ℕ → ℕ → E → E} {Θ : ℕ → ℕ → E → E}
    (hP : ∀ i k, IsOrthProj (P i k)) (hα : ∀ i k, 0 ≤ α i k) (hβ : ∀ i k, 0 ≤ β i k)
    (hh : 0 ≤ h) (hsum : ∀ i < s, ∑ k ∈ range (i + 1), α i k = 1)
    (hCFL : ∀ i k, h * β i k ≤ α i k * τCFL)
    (hEuler : ∀ i k τ, 0 ≤ τ → τ ≤ τCFL → ∀ x, P i k x = x → ‖eulerStep (F i k) τ x‖ ≤ ‖x‖)
    (hΘ : ∀ i k z, ‖Θ i k z‖ ≤ ‖z‖)
    (hu : ∀ i < s, u (i + 1) = ∑ k ∈ range (i + 1),
      α i k • Θ i k (galerkinEulerStep (P i k) (F i k) (h * β i k / α i k) (u k))) :
    ∀ i ≤ s, ‖u i‖ ≤ ‖u 0‖ := by
  refine shuOsher_norm_le (T := fun i k z =>
    Θ i k (galerkinEulerStep (P i k) (F i k) (h * β i k / α i k) z)) hα hsum
    (fun i _ k _ h0 z => ?_) hu
  have hpos : 0 < α i k := lt_of_le_of_ne (hα i k) (Ne.symm h0)
  have hτ0 : 0 ≤ h * β i k / α i k := div_nonneg (mul_nonneg hh (hβ i k)) hpos.le
  have hτ : h * β i k / α i k ≤ τCFL := by
    rw [div_le_iff₀ hpos]; linarith [hCFL i k]
  refine (hΘ i k _).trans ?_
  have := galerkinEulerStep_norm_le (hP i k) zero_le_one
    (fun x hx => by simpa using hEuler i k _ hτ0 hτ x hx) z
  simpa using this

/-- **Stage truncation errors add up** (OP-HO-09 (b), partial).  Let exact Shu–Osher stages
`u (i+1) = ∑ αᵢₖ Tᵢₖ (u k)` be computed with maps `Tᵢₖ` that are `Λ`-Lipschitz (`Λ ≥ 1`; e.g.
`Λ = 1 + τ L` for Euler steps) and perturbed stages `ũ` with per-stage errors
`‖ũ (i+1) - ∑ αᵢₖ Tᵢₖ (ũ k)‖ ≤ δ` (truncation/correction) from the same start.  Then
`‖ũ i - u i‖ ≤ i Λ^i δ`: an `s`-stage step adds at most `s Λ^s δ` to the local error. -/
theorem shuOsher_perturb_le {s : ℕ} {u v : ℕ → E} {α : ℕ → ℕ → ℝ} {T : ℕ → ℕ → E → E}
    {Λ δ : ℝ} (hΛ : 1 ≤ Λ) (hδ : 0 ≤ δ)
    (hα : ∀ i k, 0 ≤ α i k) (hsum : ∀ i < s, ∑ k ∈ range (i + 1), α i k = 1)
    (hT : ∀ i < s, ∀ k ≤ i, ∀ z w, ‖T i k z - T i k w‖ ≤ Λ * ‖z - w‖)
    (hu : ∀ i < s, u (i + 1) = ∑ k ∈ range (i + 1), α i k • T i k (u k))
    (hv : ∀ i < s, ‖v (i + 1) - ∑ k ∈ range (i + 1), α i k • T i k (v k)‖ ≤ δ)
    (h0 : v 0 = u 0) :
    ∀ i ≤ s, ‖v i - u i‖ ≤ i * Λ ^ i * δ := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have key : ∀ m : ℕ, ∀ i ≤ m, i ≤ s → ‖v i - u i‖ ≤ m * Λ ^ m * δ := by
    intro m
    induction m with
    | zero => intro i hi _; rw [Nat.le_zero.1 hi, h0]; simp
    | succ m ih =>
      have hmono : (m : ℝ) * Λ ^ m * δ ≤ ((m + 1 : ℕ) : ℝ) * Λ ^ (m + 1) * δ := by
        have h1 : Λ ^ m ≤ Λ ^ (m + 1) := pow_le_pow_right₀ hΛ (Nat.le_succ m)
        have h2 : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul h2 h1 (pow_nonneg hΛ0 _) (Nat.cast_nonneg _)) hδ
      intro i hi his
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · exact (ih i (by omega) his).trans hmono
      · have him : i = m + 1 := by omega
        subst him
        have hms : m < s := by omega
        have hX : 0 ≤ (m : ℝ) * Λ ^ m * δ :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hΛ0 _)) hδ
        have hcomb : ‖∑ k ∈ range (m + 1), α m k • T m k (v k) -
            ∑ k ∈ range (m + 1), α m k • T m k (u k)‖ ≤ Λ * ((m : ℝ) * Λ ^ m * δ) := by
          rw [← Finset.sum_sub_distrib]
          calc ‖∑ k ∈ range (m + 1), (α m k • T m k (v k) - α m k • T m k (u k))‖
              ≤ ∑ k ∈ range (m + 1), ‖α m k • T m k (v k) - α m k • T m k (u k)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ k ∈ range (m + 1), α m k * (Λ * ((m : ℝ) * Λ ^ m * δ)) :=
                Finset.sum_le_sum fun k hk => by
                  have hkm : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
                  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hα m k)]
                  exact mul_le_mul_of_nonneg_left ((hT m hms k hkm _ _).trans
                    (mul_le_mul_of_nonneg_left (ih k hkm (by omega)) hΛ0)) (hα m k)
            _ = Λ * ((m : ℝ) * Λ ^ m * δ) := by rw [← Finset.sum_mul, hsum m hms, one_mul]
        calc ‖v (m + 1) - u (m + 1)‖
            ≤ ‖v (m + 1) - ∑ k ∈ range (m + 1), α m k • T m k (v k)‖ +
              ‖∑ k ∈ range (m + 1), α m k • T m k (v k) - u (m + 1)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ δ + Λ * ((m : ℝ) * Λ ^ m * δ) := by
              rw [hu m hms]; exact add_le_add (hv m hms) hcomb
          _ ≤ ((m + 1 : ℕ) : ℝ) * Λ ^ (m + 1) * δ := by
              have h1 : δ ≤ Λ ^ (m + 1) * δ :=
                le_mul_of_one_le_left hδ (one_le_pow₀ hΛ)
              have h2 : Λ * ((m : ℝ) * Λ ^ m * δ) = m * Λ ^ (m + 1) * δ := by ring
              push_cast
              linarith [h1]
  exact fun i hi => key i i le_rfl hi

/-! ### Classical RK4 for linear Galerkin substeps (OP-SB-06) -/

/-- One step of the classical **RK4 method** for the linear ODE `x' = B x`:
`k₁ = Bx`, `k₂ = B(x + h/2 k₁)`, `k₃ = B(x + h/2 k₂)`, `k₄ = B(x + h k₃)`,
`x₁ = x + h/6 (k₁ + 2k₂ + 2k₃ + k₄)`. -/
noncomputable def rk4Lin (B : E →L[ℝ] E) (h : ℝ) (x : E) : E :=
  let k₁ := B x
  let k₂ := B (x + (h / 2) • k₁)
  let k₃ := B (x + (h / 2) • k₂)
  let k₄ := B (x + h • k₃)
  x + (h / 6) • (k₁ + (2 : ℝ) • k₂ + (2 : ℝ) • k₃ + k₄)

/-- The forward-Euler map `G x = x + h B x` of the linear ODE. -/
def eulerLin (B : E →L[ℝ] E) (h : ℝ) (x : E) : E := x + h • B x

/-- **Absolutely monotonic representation of RK4** (OP-SB-06): the RK4 step is the convex
combination `R(hB) = 3/8 + 1/3 G + 1/4 G² + 0 G³ + 1/24 G⁴` of powers of the forward-Euler map
`G = 1 + hB` (the stability polynomial identity `R(z) = ∑ₖ cₖ (1+z)^k`, `c = (3/8, 1/3, 1/4, 0,
1/24)`, `∑ cₖ = 1`). -/
theorem rk4Lin_eq (B : E →L[ℝ] E) (h : ℝ) (x : E) :
    rk4Lin B h x = (3 / 8 : ℝ) • x + (1 / 3 : ℝ) • eulerLin B h x +
      (1 / 4 : ℝ) • eulerLin B h (eulerLin B h x) +
      (1 / 24 : ℝ) • eulerLin B h (eulerLin B h (eulerLin B h (eulerLin B h x))) := by
  simp only [rk4Lin, eulerLin, map_add, map_smul, smul_add, smul_smul]
  module

/-- Powers of a norm-nonincreasing forward-Euler map that preserves `range P`. -/
lemma eulerLin_iter {B : E →L[ℝ] E} {h : ℝ} {P : E →L[ℝ] E}
    (hinv : ∀ x, P x = x → P (B x) = B x) (hstab : ∀ x, P x = x → ‖eulerLin B h x‖ ≤ ‖x‖)
    {x : E} (hx : P x = x) : P (eulerLin B h x) = eulerLin B h x ∧ ‖eulerLin B h x‖ ≤ ‖x‖ := by
  refine ⟨?_, hstab x hx⟩
  simp only [eulerLin, map_add, map_smul, hx, hinv x hx]

/-- **RK4 inherits forward-Euler contractivity** (OP-SB-06, linear case; [StammerEtAl2026],
Sec. 3.3.3).  If the linear operator `B` maps `range P` into itself and the forward-Euler map
`x ↦ x + h B x` is norm-nonincreasing on `range P`, then so is the classical RK4 step. -/
theorem rk4Lin_norm_le {B : E →L[ℝ] E} {h : ℝ} {P : E →L[ℝ] E}
    (hinv : ∀ x, P x = x → P (B x) = B x) (hstab : ∀ x, P x = x → ‖eulerLin B h x‖ ≤ ‖x‖)
    {x : E} (hx : P x = x) : ‖rk4Lin B h x‖ ≤ ‖x‖ := by
  obtain ⟨h1, n1⟩ := eulerLin_iter hinv hstab hx
  obtain ⟨h2, n2⟩ := eulerLin_iter hinv hstab h1
  obtain ⟨h3, n3⟩ := eulerLin_iter hinv hstab h2
  obtain ⟨_, n4⟩ := eulerLin_iter hinv hstab h3
  rw [rk4Lin_eq]
  refine norm_add₄_le.trans ?_
  simp only [norm_smul, Real.norm_eq_abs]
  norm_num
  linarith

/-- **Galerkin RK4 substeps are norm-nonincreasing** (OP-SB-06; [StammerEtAl2026] uses RK4 in the
K-, L- and S-substeps of BUG).  For a linear field `A` and an orthogonal projector `P` (the K-,
L- or S-step projector), if the full forward-Euler step satisfies `‖x + h A x‖ ≤ ‖x‖` on
`range P`, then the RK4 step for the Galerkin operator `P A P` is norm-nonincreasing on
`range P`.  The K- and L-substeps only build the bases; the solution is advanced by the
S-substep, so `rk4BUG_norm_le` gives the stability of the RK4-BUG step.  Not covered: the
numerical-range (disk) condition needed when
`‖I + hA‖ ≤ 1` fails (e.g. second-order upwind). -/
theorem galerkinRK4_norm_le {A P : E →L[ℝ] E} (hP : IsOrthProj P) {h : ℝ}
    (hEuler : ∀ x, P x = x → ‖x + h • A x‖ ≤ ‖x‖) {x : E} (hx : P x = x) :
    ‖rk4Lin (P.comp (A.comp P)) h x‖ ≤ ‖x‖ := by
  refine rk4Lin_norm_le (P := P) (fun y _ => ?_) (fun y hy => ?_) hx
  · simp [hP.idem]
  · have : eulerLin (P.comp (A.comp P)) h y = P (y + h • A y) := by
      simp [eulerLin, hy]
    rw [this]
    exact (hP.norm_le _).trans (hEuler y hy)

/-- **RK4-BUG step is norm-nonincreasing up to truncation** (OP-SB-06; [StammerEtAl2026]).  The
S-substep starts from `P y` (`P` the augmented-basis projector), applies RK4 to the Galerkin
operator `P A P`, and a norm-nonincreasing truncation `Θ` follows; if the full forward-Euler step
is norm-nonincreasing on `range P`, then `‖Θ(RK4(P y))‖ ≤ ‖y‖`. -/
theorem rk4BUG_norm_le {A P : E →L[ℝ] E} (hP : IsOrthProj P) {h : ℝ}
    (hEuler : ∀ x, P x = x → ‖x + h • A x‖ ≤ ‖x‖) {Θ : E → E} (hΘ : ∀ z, ‖Θ z‖ ≤ ‖z‖)
    (y : E) : ‖Θ (rk4Lin (P.comp (A.comp P)) h (P y))‖ ≤ ‖y‖ :=
  (hΘ _).trans ((galerkinRK4_norm_le hP hEuler (hP.idem y)).trans (hP.norm_le y))

/-- The RK4 inheritance is not vacuous: on `ℝ` with `B = -1` (the decay equation `x' = -x`) and
`h = 1`, the forward-Euler map is `x ↦ 0`, and the RK4 step `x ↦ (3/8) x` is a strict
contraction. -/
example : rk4Lin (-1 : ℝ →L[ℝ] ℝ) 1 1 = 3 / 8 := by
  simp [rk4Lin]
  norm_num

/-! ### BUG-p local and global error with interior capture ([HauckKuschSchotthofer2026], 2502.07040)
-/

/-- **BUG-p local error** ([HauckKuschSchotthofer2026, Sec. 3.1] properties P1–P2 and Thm 1;
[NobileRiffaud2025, Thm. 1]). Let the Galerkin projector `R` fix the starting value `y₀` (P1),
capture the exact solution `A` (`A t₀ = y₀`) to `ρ` on the step and to `θ` at the endpoint, and let
the S-solver (e.g. an `s`-stage Runge–Kutta method) reproduce the Galerkin flow `YS' = R F(t, YS)`,
`YS t₀ = y₀`, up to `η` at the endpoint. Then the local error is `≤ (e^{L h} - 1) ρ + θ + η`. For
BUG-p, `ρ = O(h^p)`-interior capture, `θ = O(h (ε + h^p))` endpoint capture and an order-`p`
S-solver (`η = O(h^{p+1})`) give local error `O(h (ε + h^p))`. -/
theorem bugP_local_error {F : ℝ → E → E} {L ρ θ η h t₀ : ℝ} {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) {y₀ y₁ : E} (hy₀ : R y₀ = y₀)
    {A YS : ℝ → E} (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = y₀)
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ (t₀ + h)) (hS₀ : YS t₀ = y₀)
    (hρ : ∀ t ∈ Icc t₀ (t₀ + h), ‖A t - R (A t)‖ ≤ ρ) (hθ : ‖A (t₀ + h) - R (A (t₀ + h))‖ ≤ θ)
    (hη : ‖y₁ - YS (t₀ + h)‖ ≤ η) :
    ‖y₁ - A (t₀ + h)‖ ≤ (Real.exp (L * h) - 1) * ρ + θ + η := by
  have hle : t₀ ≤ t₀ + h := by linarith
  have hfL : IsLipschitzField (fun t x => R (F t x)) L := hF.comp_contraction R hR.norm_le
  have hZc : ContinuousOn (fun t => R (A t)) (Icc t₀ (t₀ + h)) :=
    R.continuous.comp_continuousOn hA.cont
  have hZd : ∀ t ∈ Ico t₀ (t₀ + h),
      HasDerivWithinAt (fun t => R (A t)) (R (F t (A t))) (Ici t) t :=
    fun t ht => R.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
  have hdef : ∀ t ∈ Ico t₀ (t₀ + h), ‖R (F t (A t)) - R (F t (R (A t)))‖ ≤ L * ρ := by
    intro t ht
    calc ‖R (F t (A t)) - R (F t (R (A t)))‖ ≤ L * ‖A t - R (A t)‖ := hfL t _ _
      _ ≤ L * ρ := mul_le_mul_of_nonneg_left (hρ t (Ico_subset_Icc_self ht)) hL
  have hgr := norm_sub_le_gronwallBound hfL hL (y := YS) (z := fun t => R (A t))
    (u := fun t => R (F t (YS t))) (w := fun t => R (F t (A t))) (ηy := 0)
    (ηz := L * ρ) (δ := 0) hS.cont hS.deriv (fun _ _ => by simp) hZc hZd hdef
    (by simp [hS₀, hA₀, hy₀]) (t₀ + h) ⟨hle, le_rfl⟩
  rw [zero_add, show t₀ + h - t₀ = h by ring, gronwallBound_zero_mul] at hgr
  calc ‖y₁ - A (t₀ + h)‖
      ≤ ‖y₁ - YS (t₀ + h)‖ + ‖YS (t₀ + h) - R (A (t₀ + h))‖ + ‖R (A (t₀ + h)) - A (t₀ + h)‖ := by
        have h1 := norm_sub_le_norm_sub_add_norm_sub y₁ (YS (t₀ + h)) (A (t₀ + h))
        have h2 := norm_sub_le_norm_sub_add_norm_sub (YS (t₀ + h)) (R (A (t₀ + h))) (A (t₀ + h))
        linarith
    _ ≤ η + (Real.exp (L * h) - 1) * ρ + θ := by
        rw [norm_sub_rev (R (A (t₀ + h)))]
        exact add_le_add (add_le_add hη hgr) hθ
    _ = _ := by ring

/-- **Conservative (extra-augmented) BUG-p keeps the error bound** (OP-HO-12 (c);
[EinkemmerKuschSchotthofer2023, Sec. 5]). If the conservative basis contains the BUG-p basis
(`Pe (Pa x) = Pa x`, `X̄ = [X̂, X̄⋆]` with the RK flux moments), then all hypotheses of
`bugP_local_error` for `Pa` transfer to `Pe` (`norm_sub_apply_le_of_le`), so the conservative
Galerkin step has the same local error bound `(e^{L h} - 1) ρ + θ + η`; global bounds follow
verbatim (`bugP_global_error`). Items (a), (b), (d) of OP-HO-12 are not addressed here. -/
theorem bugP_local_error_of_le {F : ℝ → E → E} {L ρ θ η h t₀ : ℝ} {Pa Pe : E →L[ℝ] E}
    (hPe : IsOrthProj Pe) (hle : ∀ x, Pe (Pa x) = Pa x) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hh : 0 ≤ h) {y₀ y₁ : E} (hy₀ : Pa y₀ = y₀) {A YS : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = y₀)
    (hS : ODESolution (fun t x => Pe (F t x)) YS t₀ (t₀ + h)) (hS₀ : YS t₀ = y₀)
    (hρ : ∀ t ∈ Icc t₀ (t₀ + h), ‖A t - Pa (A t)‖ ≤ ρ)
    (hθ : ‖A (t₀ + h) - Pa (A (t₀ + h))‖ ≤ θ) (hη : ‖y₁ - YS (t₀ + h)‖ ≤ η) :
    ‖y₁ - A (t₀ + h)‖ ≤ (Real.exp (L * h) - 1) * ρ + θ + η := by
  have hy₀' : Pe y₀ = y₀ := by rw [← hy₀, hle]
  exact bugP_local_error hPe hF hL hh hy₀' hA hA₀ hS hS₀
    (fun t ht => (norm_sub_apply_le_of_le hPe hle _).trans (hρ t ht))
    ((norm_sub_apply_le_of_le hPe hle _).trans hθ) hη

/-- **BUG-p global error** ([HauckKuschSchotthofer2026, Thm. 2]; [NobileRiffaud2025, Thm. 2]). In
every step the Galerkin projector `R n` fixes `Y n`, captures the local exact flow `Φ n` (started at
`Y n`) to `ρ` on the step and to `h θ'` at the endpoint, and the S-solver reproduces the Galerkin
flow `YS n` up to `h η'`. Then for `n h ≤ T`, `h ≤ H`:
`‖Y n - A tₙ‖ ≤ e^{L T} (‖Y 0 - A t₀‖ + T (L e^{L H} ρ + θ' + η'))`. With `ρ = O(h^p)`,
`θ' = O(ε + h^p)` and an order-`p` S-solver (`η' = O(h^p)`) this is the robust bound
`O(δ + ε + h^p)`. -/
theorem bugP_global_error {F : ℝ → E → E} {L ρ θ' η' t₀ h H T : ℝ} {N : ℕ} {A : ℝ → E}
    {Y : ℕ → E} {Φ YS : ℕ → ℝ → E} {R : ℕ → E →L[ℝ] E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 ≤ h) (hH : h ≤ H) (hρ0 : 0 ≤ ρ)
    (hθ0 : 0 ≤ θ') (hη0 : 0 ≤ η') (hA : ODESolution F A t₀ (t₀ + N * h))
    (hR : ∀ n < N, IsOrthProj (R n)) (hRY : ∀ n < N, R n (Y n) = Y n)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + n * h + h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hS : ∀ n < N, ODESolution (fun t x => R n (F t x)) (YS n) (t₀ + n * h) (t₀ + n * h + h))
    (hS₀ : ∀ n < N, YS n (t₀ + n * h) = Y n)
    (hρ : ∀ n < N, ∀ t ∈ Icc (t₀ + n * h) (t₀ + n * h + h), ‖Φ n t - R n (Φ n t)‖ ≤ ρ)
    (hθ : ∀ n < N, ‖Φ n (t₀ + n * h + h) - R n (Φ n (t₀ + n * h + h))‖ ≤ h * θ')
    (hη : ∀ n < N, ‖Y (n + 1) - YS n (t₀ + n * h + h)‖ ≤ h * η') :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (L * Real.exp (L * H) * ρ + θ' + η')) := by
  have hend : ∀ n : ℕ, t₀ + (n + 1) * h = t₀ + n * h + h := fun n => by ring
  have hg : 0 ≤ L * Real.exp (L * H) * ρ + θ' + η' := by positivity
  refine lady_windermere_of_le hF hL hh hA (fun n hn => by rw [hend]; exact hΦ n hn) hΦ₀ hg
    (fun n hn => ?_)
  rw [hend]
  have hloc := bugP_local_error (hR n hn) hF hL hh (hRY n hn) (hΦ n hn) (hΦ₀ n hn) (hS n hn)
    (hS₀ n hn) (hρ n hn) (hθ n hn) (hη n hn)
  have he : Real.exp (L * h) - 1 ≤ h * (L * Real.exp (L * H)) := by
    have h1 := exp_sub_one_le_mul_exp (L * h)
    have h2 : Real.exp (L * h) ≤ Real.exp (L * H) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hH hL)
    have h3 : L * h * Real.exp (L * h) ≤ L * h * Real.exp (L * H) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hL hh)
    linarith
  calc ‖Y (n + 1) - Φ n (t₀ + n * h + h)‖
      ≤ (Real.exp (L * h) - 1) * ρ + h * θ' + h * η' := hloc
    _ ≤ h * (L * Real.exp (L * H)) * ρ + h * θ' + h * η' := by
        gcongr
    _ = h * (L * Real.exp (L * H) * ρ + θ' + η') := by ring

/-! ### Relaxed exactness of the reduced K–L step ([ZhangHu2026b]) -/

/-- **Relaxed exactness** ([ZhangHu2026b, Thm. 4.1], abstract form).  Let the step return
`Y₁ = P X` with an orthogonal projector `P` (`P = U₁U₁ᵀ`, `X = Y₀ + ΔA`: the reduced K–L step
`Y₁ = U₁U₁ᵀ (Y₀ + ΔA)`, cf. `ksl_eq_proj`) such that `P (M X) = M X` (the K-step capture
`U₁U₁ᵀ (Y₀ + ΔA) V₀ = (Y₀ + ΔA) V₀`, for `M Z = Z V₀ Q`), and let `Y⋆` satisfy the row-space
overlap condition `M Y⋆ = Y⋆` (`Y⋆ = (Y⋆ V₀) Q`) with `‖M z‖ ≤ Λ ‖z‖` (`Λ = ‖Q‖₂`).  Then
`‖Y₁ - Y⋆‖ ≤ (1 + Λ) ‖X - Y⋆‖`. -/
theorem relaxed_exactness {P M : E →L[ℝ] E} (hP : IsOrthProj P) {Λ : ℝ}
    (hM : ∀ z, ‖M z‖ ≤ Λ * ‖z‖) {X Ys : E} (hstar : M Ys = Ys) (hX : P (M X) = M X) :
    ‖P X - Ys‖ ≤ (1 + Λ) * ‖X - Ys‖ := by
  set w := M (Ys - X) with hw
  have hrw : P X - Ys = P (X - Ys) - (w - P w) := by
    rw [hw, map_sub, map_sub, map_sub, hstar, hX]
    abel
  rw [hrw]
  calc ‖P (X - Ys) - (w - P w)‖ ≤ ‖P (X - Ys)‖ + ‖w - P w‖ := norm_sub_le _ _
    _ ≤ ‖X - Ys‖ + Λ * ‖X - Ys‖ := by
        refine add_le_add (hP.norm_le _) ((hP.norm_sub_le w).trans ?_)
        rw [hw, norm_sub_rev X Ys]
        exact hM _
    _ = (1 + Λ) * ‖X - Ys‖ := by ring

/-- **Global error from the increment error** ([ZhangHu2026b], Thms 4.3 and 5.1, abstract
form).  In step `n` the method returns `Y (n+1) = P n (X n)` (`X n = Y n + ΔAₙ`) with the
hypotheses of `relaxed_exactness` for a comparison point `Ys n` that is `h c ε`-close to the
local exact flow (the rank-`r` comparison curve of Lemma 4.2, with `‖Q‖₂ ≤ Λ`; its existence is
taken as a hypothesis here), and the increment error is `‖X n - Φ n tₙ₊₁‖ ≤ d`.  Then, for
`h > 0` and `n h ≤ T`,
`‖Y n - A tₙ‖ ≤ e^{L T} (‖Y 0 - A t₀‖ + T ((1 + Λ) d / h + (2 + Λ) c ε))`,
i.e. the bound `C_T (δ + ε_r + d_h / h)` of Thm 5.1. -/
theorem relaxed_global_error {F : ℝ → E → E} {L Λ d c ε t₀ h T : ℝ} {N : ℕ} {A : ℝ → E}
    {Y X Ys : ℕ → E} {Φ : ℕ → ℝ → E} {P M : ℕ → E →L[ℝ] E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 < h) (hΛ : 0 ≤ Λ) (hd : 0 ≤ d)
    (hcε : 0 ≤ c * ε) (hA : ODESolution F A t₀ (t₀ + N * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hP : ∀ n < N, IsOrthProj (P n)) (hY : ∀ n < N, Y (n + 1) = P n (X n))
    (hM : ∀ n < N, ∀ z, ‖M n z‖ ≤ Λ * ‖z‖) (hstar : ∀ n < N, M n (Ys n) = Ys n)
    (hX : ∀ n < N, P n (M n (X n)) = M n (X n))
    (hcmp : ∀ n < N, ‖Ys n - Φ n (t₀ + (n + 1) * h)‖ ≤ h * (c * ε))
    (hinc : ∀ n < N, ‖X n - Φ n (t₀ + (n + 1) * h)‖ ≤ d) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * ((1 + Λ) * d / h + (2 + Λ) * (c * ε))) := by
  have hg : 0 ≤ (1 + Λ) * d / h + (2 + Λ) * (c * ε) := by positivity
  refine lady_windermere_of_le hF hL hh.le hA hΦ hΦ₀ hg (fun n hn => ?_)
  set φ := Φ n (t₀ + (n + 1) * h)
  have h1 := relaxed_exactness (hP n hn) (hM n hn) (hstar n hn) (hX n hn)
  have h2 : ‖X n - Ys n‖ ≤ d + h * (c * ε) := by
    calc ‖X n - Ys n‖ ≤ ‖X n - φ‖ + ‖φ - Ys n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ d + h * (c * ε) := add_le_add (hinc n hn) (by rw [norm_sub_rev]; exact hcmp n hn)
  rw [hY n hn]
  calc ‖P n (X n) - φ‖ ≤ ‖P n (X n) - Ys n‖ + ‖Ys n - φ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 + Λ) * (d + h * (c * ε)) + h * (c * ε) :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))) (hcmp n hn)
    _ = h * ((1 + Λ) * d / h + (2 + Λ) * (c * ε)) := by
        field_simp
        ring

/-! ### SSP/RK4 substeps, Shu–Osher exactness, perturbed RK (OP-SB-06,
OP-HO-09, OP-HO-15) -/

/-- Powers of the Galerkin forward-Euler operator `G = 1 + h P A` preserve `range P` and are
norm-nonincreasing there when the full forward-Euler step is. -/
lemma galerkinEulerPow_mem_norm_le {P A : E →L[ℝ] E} (hP : IsOrthProj P) {h : ℝ}
    (hFE : ∀ x, P x = x → ‖x + h • A x‖ ≤ ‖x‖) (k : ℕ) {x : E} (hx : P x = x) :
    P (((1 + h • (P.comp A)) ^ k) x) = ((1 + h • (P.comp A)) ^ k) x ∧
      ‖((1 + h • (P.comp A)) ^ k) x‖ ≤ ‖x‖ := by
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    set z := ((1 + h • (P.comp A)) ^ k) x
    have hG : ((1 + h • (P.comp A)) ^ (k + 1)) x = P (z + h • A z) := by
      rw [pow_succ']
      change (1 + h • P.comp A) z = _
      simp [map_add, map_smul, h1]
    rw [hG]
    exact ⟨hP.idem _, (hP.norm_le _).trans ((hFE z h1).trans h2)⟩

/-- **Absolutely monotonic linear Runge–Kutta substeps are norm-nonincreasing** (OP-SB-06,
general linear part; [StammerEtAl2026]).  If the stability polynomial is written as
`R(z) = ∑ₖ cₖ (1 + z)^k` with `cₖ ≥ 0`, `∑ cₖ = 1`, and the full forward-Euler step is
norm-nonincreasing on `range P`, then the Galerkin Runge–Kutta step `R(h P A)` is
norm-nonincreasing on `range P`.  This proves (with a weaker hypothesis: contractivity only on
`range P`) the statement `galerkin_ssp_linear_norm_le`. -/
theorem galerkin_ssp_linear_norm_le {P : E →L[ℝ] E} (hP : IsOrthProj P) (A : E →L[ℝ] E)
    {h : ℝ} (hFE : ∀ x, P x = x → ‖x + h • A x‖ ≤ ‖x‖) (K : ℕ) (c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hsum : ∑ k ∈ range (K + 1), c k = 1) {x : E} (hx : P x = x) :
    ‖∑ k ∈ range (K + 1), c k • ((1 + h • (P.comp A)) ^ k) x‖ ≤ ‖x‖ := by
  calc ‖∑ k ∈ range (K + 1), c k • ((1 + h • (P.comp A)) ^ k) x‖
      ≤ ∑ k ∈ range (K + 1), ‖c k • ((1 + h • (P.comp A)) ^ k) x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (K + 1), c k * ‖x‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_smul, Real.norm_of_nonneg (hc k)]
        exact mul_le_mul_of_nonneg_left (galerkinEulerPow_mem_norm_le hP hFE k hx).2 (hc k)
    _ = ‖x‖ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **Classical RK4 Galerkin substep in Taylor form is norm-nonincreasing** (OP-SB-06;
[StammerEtAl2026]). With `M = P A`, the RK4 step `x + h M x + h²/2 M² x + h³/6 M³ x + h⁴/24 M⁴ x` is
norm-nonincreasing on `range P` whenever the full forward-Euler step is (only on `range P` is
needed). It is `rk4Lin (P A) h x`, and `rk4Lin_norm_le` applies. -/
theorem galerkin_rk4_taylor_norm_le {P : E →L[ℝ] E} (hP : IsOrthProj P) (A : E →L[ℝ] E)
    {h : ℝ} (hFE : ∀ x, P x = x → ‖x + h • A x‖ ≤ ‖x‖) {x : E} (hx : P x = x) :
    let M : E → E := fun y => P (A y)
    ‖x + h • M x + (h ^ 2 / 2) • M (M x) + (h ^ 3 / 6) • M (M (M x)) +
      (h ^ 4 / 24) • M (M (M (M x)))‖ ≤ ‖x‖ := by
  intro M
  have heq : x + h • M x + (h ^ 2 / 2) • M (M x) + (h ^ 3 / 6) • M (M (M x)) +
      (h ^ 4 / 24) • M (M (M (M x))) = rk4Lin (P.comp A) h x := by
    simp only [M, rk4Lin, ContinuousLinearMap.comp_apply, map_add, map_smul, smul_add, smul_smul]
    module
  rw [heq]
  refine rk4Lin_norm_le (P := P) (fun y _ => by simp [hP.idem]) (fun y hy => ?_) hx
  have : eulerLin (P.comp A) h y = P (y + h • A y) := by simp [eulerLin, hy]
  rw [this]
  exact (hP.norm_le _).trans (hFE y hy)

/-- **Galerkin SSP-RK2 (Heun) substep is norm-nonincreasing** (OP-SB-06, nonlinear part;
[StammerEtAl2026], Shu–Osher form). `y = x + h P F(x)`, `x' = x/2 + (y + h P F(y))/2` satisfies
`‖x'‖ ≤ ‖x‖` on `range P` if the full forward-Euler step is norm-nonincreasing on `range P`. This
proves the statement `galerkin_sspRK2_norm_le`; the general Shu–Osher case is `sspGalerkin_norm_le`.
-/
theorem galerkin_sspRK2_norm_le {P : E →L[ℝ] E} (hP : IsOrthProj P) {F : E → E} {h : ℝ}
    (hFE : ∀ z, P z = z → ‖z + h • F z‖ ≤ ‖z‖) {x : E} (hx : P x = x) :
    let y := x + h • P (F x)
    ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (y + h • P (F y))‖ ≤ ‖x‖ := by
  intro y
  have hy : y = P (x + h • F x) := by simp [y, map_add, map_smul, hx]
  have hPy : P y = y := by rw [hy, hP.idem]
  have hny : ‖y‖ ≤ ‖x‖ := by rw [hy]; exact (hP.norm_le _).trans (hFE x hx)
  have hz : y + h • P (F y) = P (y + h • F y) := by simp [map_add, map_smul, hPy]
  have hnz : ‖y + h • P (F y)‖ ≤ ‖x‖ := by
    rw [hz]; exact (hP.norm_le _).trans ((hFE y hPy).trans hny)
  calc ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (y + h • P (F y))‖
      ≤ ‖(1 / 2 : ℝ) • x‖ + ‖(1 / 2 : ℝ) • (y + h • P (F y))‖ := norm_add_le _ _
    _ = 1 / 2 * ‖x‖ + 1 / 2 * ‖y + h • P (F y)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num)]
    _ ≤ ‖x‖ := by linarith

/-- **SSP low-rank schemes with a projection after each stage are norm-stable** (OP-HO-09 (a),
second formulation; [HauckSchnake2023] Sec. 7, 2602.12337 Sec. 6, 2609.02721 Sec. 6).  Shu–Osher
stages `uᵢ = Tᵢ(Pᵢ ∑ₖ (αᵢₖ uₖ + βᵢₖ τ F uₖ))` (explicit, `α, β ≥ 0`, `∑ₖ αᵢₖ = 1`), orthogonal
projectors `Pᵢ`, nonexpansive truncations `Tᵢ`, forward-Euler stable for `0 ≤ σ ≤ τ₀` and
`βᵢₖ τ ≤ αᵢₖ τ₀` (`τ ≤ c_SSP τ₀`): every stage satisfies `‖uᵢ‖ ≤ ‖u₀‖`.  This proves the
statement `sspLowRank_norm_le`. -/
theorem sspLowRank_norm_le {s : ℕ} {F : E → E} {τ₀ τ : ℝ} (hτ : 0 ≤ τ)
    (hF : ∀ x, ∀ σ ∈ Icc 0 τ₀, ‖x + σ • F x‖ ≤ ‖x‖)
    {α β : Fin (s + 1) → Fin (s + 1) → ℝ} (hα : ∀ i k, 0 ≤ α i k) (hβ : ∀ i k, 0 ≤ β i k)
    (hlow : ∀ i k, i ≤ k → α i k = 0 ∧ β i k = 0) (hsum : ∀ i, i ≠ 0 → ∑ k, α i k = 1)
    (hcfl : ∀ i k, β i k * τ ≤ α i k * τ₀) {P : Fin (s + 1) → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) {T : Fin (s + 1) → E → E} (hT : ∀ i x, ‖T i x‖ ≤ ‖x‖)
    {u : Fin (s + 1) → E}
    (hu : ∀ i, i ≠ 0 → u i = T i (P i (∑ k, (α i k • u k + (β i k * τ) • F (u k))))) :
    ∀ i, ‖u i‖ ≤ ‖u 0‖ := by
  have key : ∀ m : ℕ, ∀ i : Fin (s + 1), i.val < m → ‖u i‖ ≤ ‖u 0‖ := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      by_cases hi0 : i = 0
      · rw [hi0]
      rw [hu i hi0]
      refine (hT i _).trans ((hP i).norm_le _ |>.trans ?_)
      calc ‖∑ k, (α i k • u k + (β i k * τ) • F (u k))‖
          ≤ ∑ k, ‖α i k • u k + (β i k * τ) • F (u k)‖ := norm_sum_le _ _
        _ ≤ ∑ k, α i k * ‖u 0‖ := Finset.sum_le_sum fun k _ => by
            by_cases h0 : α i k = 0
            · have hb : β i k * τ = 0 :=
                le_antisymm (by simpa [h0] using hcfl i k) (mul_nonneg (hβ i k) hτ)
              simp [h0, hb]
            · have hpos : 0 < α i k := lt_of_le_of_ne (hα i k) (Ne.symm h0)
              have hki : k < i := lt_of_not_ge fun hik => h0 (hlow i k hik).1
              have hσ : β i k * τ / α i k ∈ Icc 0 τ₀ :=
                ⟨div_nonneg (mul_nonneg (hβ i k) hτ) hpos.le,
                  by rw [div_le_iff₀ hpos]; linarith [hcfl i k]⟩
              have hrw : α i k • u k + (β i k * τ) • F (u k) =
                  α i k • (u k + (β i k * τ / α i k) • F (u k)) := by
                rw [smul_add, smul_smul, mul_div_cancel₀ _ h0]
              rw [hrw, norm_smul, Real.norm_of_nonneg hpos.le]
              exact mul_le_mul_of_nonneg_left ((hF _ _ hσ).trans
                (ih k (by have : k.val < i.val := hki; omega))) hpos.le
        _ = ‖u 0‖ := by rw [← Finset.sum_mul, hsum i hi0, one_mul]
  exact fun i => key (s + 1) i i.isLt

/-- An explicit Runge–Kutta step in **Shu–Osher form** with Galerkin projections: stages
`u₀ = y`, `uᵢ = Rᵢ (∑ₖ αᵢₖ uₖ + h βᵢₖ F(t + cₖ h, uₖ))` (`Rᵢ = 1`: the full method).  The
low-storage SSPRK BUG of [HauckKuschSchotthofer2026] (Sec. 8.2) is of this form with `Rᵢ` the
projectors onto the augmented bases. -/
def IsShuOsherStep {s : ℕ} (F : ℝ → E → E) (α β : Fin (s + 1) → Fin (s + 1) → ℝ)
    (c : Fin (s + 1) → ℝ) (R : Fin (s + 1) → E →L[ℝ] E) (t h : ℝ) (y : E)
    (u : Fin (s + 1) → E) : Prop :=
  u 0 = y ∧ ∀ i, i ≠ 0 → u i = R i (∑ k, (α i k • u k + (h * β i k) • F (t + c k * h) (u k)))

/-- **Galerkin Shu–Osher exactness** (OP-HO-15 (a), Shu–Osher form; [YeYang2025],
[HauckKuschSchotthofer2026] Remark 1). If every stage projector fixes the full-method stages `vₖ`
entering with `αᵢₖ ≠ 0` and the stage derivatives `F(t + cₖ h, vₖ)` entering with `βᵢₖ ≠ 0`, the
Galerkin Shu–Osher step coincides with the full one (all stages, hence the result). This proves the
statement `galerkinShuOsher_eq`. -/
theorem galerkinShuOsher_eq {s : ℕ} {F : ℝ → E → E} {α β : Fin (s + 1) → Fin (s + 1) → ℝ}
    {c : Fin (s + 1) → ℝ} (hlow : ∀ i k, i ≤ k → α i k = 0 ∧ β i k = 0)
    {R : Fin (s + 1) → E →L[ℝ] E} {t h : ℝ} {y : E} {u v : Fin (s + 1) → E}
    (hu : IsShuOsherStep F α β c R t h y u) (hv : IsShuOsherStep F α β c (fun _ => 1) t h y v)
    (hRu : ∀ i k, α i k ≠ 0 → R i (v k) = v k)
    (hRF : ∀ i k, β i k ≠ 0 → R i (F (t + c k * h) (v k)) = F (t + c k * h) (v k)) :
    u = v := by
  have key : ∀ m : ℕ, ∀ i : Fin (s + 1), i.val < m → u i = v i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      by_cases hi0 : i = 0
      · rw [hi0, hu.1, hv.1]
      rw [hu.2 i hi0, hv.2 i hi0]
      have hsum : ∑ k, (α i k • u k + (h * β i k) • F (t + c k * h) (u k)) =
          ∑ k, (α i k • v k + (h * β i k) • F (t + c k * h) (v k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k < i
        · rw [ih k (by have : k.val < i.val := hk; omega)]
        · obtain ⟨ha, hb⟩ := hlow i k (not_lt.1 hk)
          simp [ha, hb]
      rw [hsum, map_sum]
      simp only [one_apply_eq_self]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_add, map_smul, map_smul]
      congr 1
      · by_cases ha : α i k = 0
        · simp [ha]
        · rw [hRu i k ha]
      · by_cases hb : β i k = 0
        · simp [hb]
        · rw [hRF i k hb]
  exact funext fun i => key (s + 1) i i.isLt

/-- **Perturbed explicit Runge–Kutta step** (OP-HO-09 (b), per-stage form; [HauckSchnake2023]
Sec. 7, 2502.07040 Lemma 4).  If the stages and the result of an explicit Runge–Kutta step are
computed up to per-stage errors `ηᵢ` and a final error `η₁`, the result deviates from the exact
step by `≤ η₁ + C h ∑ᵢ ηᵢ` with `C = L⁺ M κ^s` (`M = ∑|aᵢⱼ| + ∑|bᵢ|`, `κ = 1 + H⁺ L⁺ M`),
depending only on the tableau, `L` and `H ≥ h`.  This proves the statement
`perturbedRK_le`. -/
theorem perturbedRK_le {s : ℕ} (a : Fin s → Fin s → ℝ) (b c : Fin s → ℝ)
    (ha : ∀ i j, i ≤ j → a i j = 0) (L H : ℝ) :
    ∃ C : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
      {t h η₁ : ℝ} {η : Fin s → ℝ} {y y₁ z₁ : E} {Y Z : Fin s → E},
      IsLipschitzField F L → 0 ≤ h → h ≤ H →
      (∀ i, Z i = y + h • ∑ j, a i j • F (t + c j * h) (Z j)) →
      z₁ = y + h • ∑ i, b i • F (t + c i * h) (Z i) →
      (∀ i, ‖Y i - (y + h • ∑ j, a i j • F (t + c j * h) (Y j))‖ ≤ η i) →
      ‖y₁ - (y + h • ∑ i, b i • F (t + c i * h) (Y i))‖ ≤ η₁ →
      ‖y₁ - z₁‖ ≤ η₁ + C * h * ∑ i, η i := by
  refine ⟨max L 0 * tabWeight a b * tabKappa a b L H ^ s, ?_⟩
  intro E _ _ F t h η₁ η y y₁ z₁ Y Z hF hh hH hZ hz₁ hY hy₁
  set M := tabWeight a b with hMdef
  set κ := tabKappa a b L H with hκdef
  have hM : 0 ≤ M := tabWeight_nonneg a b
  have hκ : 1 ≤ κ := one_le_tabKappa a b L H
  have hLp : 0 ≤ max L 0 := le_max_right _ _
  have hHp : h ≤ max H 0 := hH.trans (le_max_left _ _)
  have hη : ∀ i, 0 ≤ η i := fun i => (norm_nonneg _).trans (hY i)
  set S := ∑ i, η i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hη i
  have hηS : ∀ i, η i ≤ S := fun i =>
    Finset.single_le_sum (f := η) (fun j _ => hη j) (Finset.mem_univ i)
  have hLip : ∀ t x z, ‖F t x - F t z‖ ≤ max L 0 * ‖x - z‖ := fun t x z =>
    (hF t x z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- a combination whose inputs are within `X` differs by `≤ h M L⁺ X`
  have hcomb : ∀ (w : Fin s → ℝ) (X : ℝ), 0 ≤ X → (∀ j, w j ≠ 0 → ‖Y j - Z j‖ ≤ X) →
      ∑ j, |w j| ≤ M →
      ‖(y + h • ∑ j, w j • F (t + c j * h) (Y j)) - (y + h • ∑ j, w j • F (t + c j * h) (Z j))‖
        ≤ h * (M * (max L 0 * X)) := by
    intro w X hX hD hw
    have h1 := norm_proj_comb_sub_le (R := 1) (y := y) (w := w)
      (u := fun j => F (t + c j * h) (Y j)) (v := fun j => F (t + c j * h) (Z j)) (ε := 0)
      rfl hh (fun j _ => by simp)
    simp only [one_apply_eq_self, add_zero] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (sum_abs_mul_le (by positivity) (fun j hj => ?_)
      hw) hh)
    exact (hLip _ _ _).trans (mul_le_mul_of_nonneg_left (hD j hj) hLp)
  have key : ∀ k : ℕ, ∀ i : Fin s, i.val < k → ‖Y i - Z i‖ ≤ κ ^ k * S := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      have hX : 0 ≤ κ ^ k * S := mul_nonneg (pow_nonneg (by linarith) _) hS0
      have h2 := hcomb (a i) (κ ^ k * S) hX (fun j hj => ih j (by
          have hji : j < i := lt_of_not_ge fun hij => hj (ha i j hij)
          have : j.val < i.val := hji
          omega)) (row_le_tabWeight a b i)
      rw [← hZ i] at h2
      have h3 : h * (M * (max L 0 * (κ ^ k * S))) ≤
          max H 0 * max L 0 * M * (κ ^ k * S) := by
        have := mul_le_mul_of_nonneg_right hHp
          (show 0 ≤ M * (max L 0 * (κ ^ k * S)) by positivity)
        linarith
      have hκk : 1 ≤ κ ^ k := one_le_pow₀ hκ
      calc ‖Y i - Z i‖
          ≤ ‖Y i - (y + h • ∑ j, a i j • F (t + c j * h) (Y j))‖ +
            ‖(y + h • ∑ j, a i j • F (t + c j * h) (Y j)) - Z i‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ S + max H 0 * max L 0 * M * (κ ^ k * S) := by
            linarith [hY i, hηS i]
        _ ≤ κ ^ k * S + max H 0 * max L 0 * M * (κ ^ k * S) := by nlinarith
        _ = κ ^ (k + 1) * S := by rw [hκdef, tabKappa, ← hMdef]; ring
  have hX : 0 ≤ κ ^ s * S := mul_nonneg (pow_nonneg (by linarith) _) hS0
  have hfin := hcomb b (κ ^ s * S) hX (fun i _ => key s i i.isLt) (b_le_tabWeight a b)
  rw [← hz₁] at hfin
  calc ‖y₁ - z₁‖
      ≤ ‖y₁ - (y + h • ∑ i, b i • F (t + c i * h) (Y i))‖ +
        ‖(y + h • ∑ i, b i • F (t + c i * h) (Y i)) - z₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η₁ + h * (M * (max L 0 * (κ ^ s * S))) := add_le_add hy₁ hfin
    _ = η₁ + max L 0 * M * κ ^ s * h * S := by ring

end LeanDLRA.RungeKuttaBUG
