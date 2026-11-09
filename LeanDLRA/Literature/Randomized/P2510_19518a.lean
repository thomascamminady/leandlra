import LeanDLRA.Matrix.Interpolation
import LeanDLRA.HighOrder.RungeKuttaBUG

/-!
# Results of arXiv 2510.19518: interpolatory DLRA (DLRA-DEIM), Lemma 7, Lemma 13, Theorem 14

Carrel–Kressner–Nobile–Vandereycken, *Interpolatory dynamical low-rank approximation:
theoretical foundations and algorithms*, arXiv 2510.19518.  Most results of the paper were already
proved in `LeanDLRA.Matrix.Interpolation`; this module proves the remaining ones in scope (the
uniqueness half of Lemma 7, Lemma 13 and Theorem 14) on top of that module, of the core
Runge–Kutta step `RungeKuttaBUG.IsGalerkinRKStep` and of the core ODE / Grönwall lemmas.

## Already in the library (not duplicated here)

* eq. (6): `LeanDLRA.IsObliqueProj.norm_sub_le_opNorm` (abstract) and
  `LeanDLRA.norm_sub_obliqueProj_mul_le_of_orthonormal` (matrices);
* eqs. (12)–(13) and §3.1: `LeanDLRA.obliqueProj`, `LeanDLRA.obliqueTangentProj`,
  `LeanDLRA.isObliqueProj_obliqueTangentProj` (oblique projector onto `T_Y ℳ_r`),
  `LeanDLRA.transpose_mul_obliqueTangentProj_mul` (interpolation property);
* eq. (14): `LeanDLRA.IsObliqueProj.sub_apply_eq`, `LeanDLRA.one_sub_obliqueProj_mul`;
* Lemma 4 and eq. (15): `LeanDLRA.IsObliqueProj.norm_sub_tangent_le_opNorm`,
  `LeanDLRA.IsObliqueProj.opNorm_tangent_le`, `LeanDLRA.IsObliqueProj.opNorm_one_sub_tangent_eq`,
  `LeanDLRA.norm_sub_obliqueTangentProj_le_of_orthonormal`,
  `LeanDLRA.opNorm_obliqueTangentProj_le_of_orthonormal`,
  `LeanDLRA.opNorm_one_sub_obliqueTangentProj_eq`;
* eq. (16): `LeanDLRA.filippov`;
* Lemma 7, existence half (tangency of `Ȧ` as a hypothesis): `LeanDLRA.mem_filippov_of_mem_range`,
  `LeanDLRA.ODESolution.oblique_of_mem_range`;
* Corollary 9: `LeanDLRA.norm_sub_le_of_mem_filippov` (with `LeanDLRA.norm_obliqueField_sub_le`);
* Theorem 10: `LeanDLRA.norm_sub_le_of_filippov`, `LeanDLRA.norm_sub_le_of_oblique`;
* Lemma 11 and Theorem 12: `LeanDLRA.norm_projEulerDEIM_sub_le`,
  `LeanDLRA.norm_projEulerDEIM_sub_le_global`, `LeanDLRA.norm_projEulerDEIM_sub_le_global_of_dlra`;
* Theorem 1 (DLRA accuracy, quoted from Kieri–Vandereycken):
  `LeanDLRA.ODESolution.norm_sub_le_of_perturbed`.

## Main results of this module

* `IsPRKDEIMStep`: one step of PRK-DEIM, eq. (23), in abstract form; `isPRKDEIMStep_id_iff`
  identifies it, for `T = id` and `P^∠ = I`, with the core classical RK step.
* `prkDEIM_stage_error` (**Lemma 13**), `prkDEIM_local_error`, `prkDEIM_global_error`
  (**Theorem 14**), all with explicit constants (`prkGamma`, `prkConst`) and conditional on the
  closeness of the exact flow to `ℳ`; `exists_mem_near_flow_of_dlra` and
  `prkDEIM_global_error_of_dlra` discharge that closeness from DLRA trajectories, as the paper
  does with eq. (5).  `admissible_min_q₂` gives the printed order `q = min{p, q₂ + 1}`;
  `admissible_of_b₂_eq_zero` gives `min{p, q₃ + 1, q₂ + 2}` when `b₂ = 0`.
* `lemma7_uniqueness_counterexample`: the uniqueness half of **Lemma 7** is false as printed
  (`F` only continuous): an explicit continuous, bounded field on `ℝ^{2×2}` whose full model
  has the unique solution `A ≡ e₁e₁ᵀ ∈ ℳ₁`, while DLRA-DEIM with any DEIM selection (QDEIM
  included) has a second differentiable solution `(1 + t²/4) e₁e₁ᵀ`.
* `lemma7_of_lipschitz` (**Lemma 7, corrected**): with `F` Lipschitz (Assumption 1), both halves
  hold for any DEIM selection with bounded projectors, given the curvature bounds of `ℳ` along
  `A` (proved for `ℳ_r` in `LeanDLRA.Matrix.Curvature`); built from `tangent_of_mem` (tangency
  of `Ȧ` derived from `A(t) ∈ ℳ`), `norm_sub_le_of_mem_filippov_of_tangent` and
  `eq_of_filippov_of_lipschitz`.

## Deviations from the paper

* Abstract setting: a real inner product space `E` (the paper: `ℝ^{m×n}` with the Frobenius
  norm), a set `ℳ` (`ℳ_r`), point-dependent tangent projectors `P(z)` and DEIM projectors
  `P^∠(z)` with `IsObliqueProj (P^∠ z) (P z)` and `‖P^∠ z‖ ≤ C` on `ℳ` (Lemma 4 gives
  `C = C_{m,r} C_{n,r}` for `obliqueTangentProj`), and a truncation `T` that enters only through
  the quasi-best approximation property `‖T x - x‖ ≤ κ ‖z - x‖`, `z ∈ ℳ` (`κ = 1` for `T_r`).
  The PRK-DEIM stage points `T(Z_j)` are assumed to lie in `ℳ` (so that `P^∠` is defined there),
  and so are the iterates `Y_n`, as in the paper (`T_r : ℝ^{m×n} → ℳ_r`).
* Runge–Kutta orders enter through their definitions: the classical step has local error
  `≤ K h^{p+1}` and stage `j` is `K h^{q_j+1}`-close to `φ_F^{c_j h}(y)`; the stage orders of
  concrete tableaux (e.g. PRK3: `q₂ = 1`, `q₃ = 2`, `p = 3`) are not derived here.
* The constants are explicit, `h ≤ 1` replaces `h < h₀`, and `C ε` and the DLRA defect `ε_d`
  (or `g`) are kept separate instead of being absorbed into `c C_{m,r} C_{n,r} ε_r`.  The DLRA
  bound (5) is used with the Lipschitz constant `L` (factor `e^{L h}`) instead of the one-sided
  constant `ℓ` (factor `max{1, e^{ℓ c_j h}}`), so Assumption 2 is not needed.
* Theorem 14, case `b₂ = 0`: the printed order `min{p, q₃ + 1, q₂ + 1}` equals `min{p, q₂ + 1}`
  (since `q₃ ≥ q₂`), so the case distinction is void as printed, and it would give only order 2 for
  PRK3, whose full order 3 the paper asserts right after the theorem.  The proof yields
  `min{p, q₃ + 1, q₂ + 2}` (`admissible_of_b₂_eq_zero`), which gives order 3 for PRK3; the
  printed exponent follows from `admissible_min_q₂`.  We read `q₂ + 1` as a typo for `q₂ + 2`.
* Lemma 7: the printed uniqueness claim is refuted (`lemma7_uniqueness_counterexample`); the
  corrected `lemma7_of_lipschitz` assumes Assumption 1 and the curvature bounds of `ℳ` (abstract
  hypotheses here, theorems for `ℳ_r`), and works for any DEIM procedure.  Solutions of the
  inclusion are taken with right derivatives at every time of `[a, b)` (as for Theorem 10 in the
  library), not absolutely continuous solutions a.e.
* Not covered: Theorem 2 and Lemma 3 (continuity and limit selections of QDEIM), Lemmas 5–6 (the
  structure of the Filippov set under QDEIM), Theorem 8 (existence for (17)), Section 5 (Tucker
  format, Lemmas 15–16, Algorithm 2) and the appendix lemmas.

Core definitions used: `IsObliqueProj`, `IsOrthProj`, `filippov`, `obliqueProj`,
`obliqueTangentProj`, `ODESolution`, `IsLipschitzField`, `IsOneSidedLipschitzField`,
`RungeKuttaBUG.IsGalerkinRKStep`, `RungeKuttaBUG.tabWeight`.  Local definitions: `IsPRKDEIMStep`
(bridged by `isPRKDEIMStep_id_iff`; the core RK step has linear projectors applied to the whole
stage, PRK-DEIM applies a nonlinear truncation and point-dependent projectors to each stage
derivative), the constants `prkGamma`, `prkConst`, and the data of the counterexample in
`Lemma7Counterexample`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2510_19518

open LeanDLRA LeanDLRA.RungeKuttaBUG

section PRKDEIM

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℕ}

/-- One step of the **projected Runge–Kutta DEIM method** (PRK-DEIM, arXiv 2510.19518,
eq. (23)) in abstract form: for an `s`-stage tableau `(a, b)`, a truncation `T` (the rank-`r`
truncation `T_r`) and point-dependent oblique (DEIM) tangent projectors `Pob z = P^∠_z`,
`Z_j = y + h ∑_ℓ a_{jℓ} P^∠_{T(Z_ℓ)} F(T(Z_ℓ))` and
`y₁ = T(y + h ∑_j b_j P^∠_{T(Z_j)} F(T(Z_j)))`. -/
def IsPRKDEIMStep (F : E → E) (T : E → E) (Pob : E → E →L[ℝ] E) (a : Fin s → Fin s → ℝ)
    (b : Fin s → ℝ) (h : ℝ) (y : E) (Z : Fin s → E) (y₁ : E) : Prop :=
  (∀ j, Z j = y + h • ∑ l, a j l • Pob (T (Z l)) (F (T (Z l)))) ∧
    y₁ = T (y + h • ∑ j, b j • Pob (T (Z j)) (F (T (Z j))))

/-- **Bridge to the core Runge–Kutta step.**  Without truncation and projection (`T = id`,
`P^∠ = I`) a PRK-DEIM step is the classical explicit Runge–Kutta step (21), i.e. the core
`RungeKuttaBUG.IsGalerkinRKStep` with identity projectors. -/
theorem isPRKDEIMStep_id_iff {F : E → E} {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ} {t h : ℝ}
    {y y₁ : E} {Z : Fin s → E} :
    IsPRKDEIMStep F id (fun _ => 1) a b h y Z y₁ ↔
      IsGalerkinRKStep (fun _ => F) a b c (fun _ => 1) 1 t h y Z y₁ := by
  simp [IsPRKDEIMStep, IsGalerkinRKStep]

/-- The stage growth factor `γ = 1 + L κ + L (1 + κ) α` of the PRK-DEIM stage analysis, where
`α = tabWeight a b` bounds the row sums `∑_ℓ |a_{jℓ}|` and the weights `∑_j |b_j|`. -/
noncomputable def prkGamma (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L κ : ℝ) : ℝ :=
  1 + L * κ + L * (1 + κ) * tabWeight a b

/-- `γ ≥ 1`. -/
lemma one_le_prkGamma (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) {L κ : ℝ} (hL : 0 ≤ L)
    (hκ : 0 ≤ κ) : 1 ≤ prkGamma a b L κ := by
  have := tabWeight_nonneg a b
  unfold prkGamma
  have : 0 ≤ L * κ := mul_nonneg hL hκ
  have : 0 ≤ L * (1 + κ) * tabWeight a b := by positivity
  linarith

/-- **Lemma 13 of arXiv 2510.19518** (local error of the PRK-DEIM stages), abstract form,
explicit constants, *conditional on the closeness hypothesis `hM`*.

Setting: `F` is `L`-Lipschitz (Assumption 1); on `ℳ` the DEIM projectors `P^∠(z)` are oblique
projectors onto nonzero orthogonal (tangent) projectors `P(z)` with `‖P^∠(z)‖ ≤ C`
(`C = C_{m,r} C_{n,r}`, Lemma 4) and the normal component is `‖F(z) - P(z) F(z)‖ ≤ ε`
(Assumption 3, `ε = ε_r`); `T` is a quasi-best approximation onto `ℳ`
(`‖T x - x‖ ≤ κ ‖z - x‖`, `z ∈ ℳ`; `κ = 1` for the truncated SVD `T_r`).  Let `Z` be the
PRK-DEIM stages from `y ∈ ℳ` (`IsPRKDEIMStep`, with `T(Z_j) ∈ ℳ`, so that `P^∠_{T(Z_j)}` is
defined) and `Z̃` the classical explicit RK stages (`IsGalerkinRKStep` with identity projectors).
The stage orders enter through their definition: `‖Z̃_j - w_j‖ ≤ K h^{q_j + 1}` for the exact
flow values `w_j = φ_F^{c_j h}(y)` (`hw`), and `q₂ ≤ q_j` for the stages `j ≥ 2` (the paper's
`q₂ ≤ … ≤ q_s`).  The hypothesis `hM` says that `w_j` is `h g`-close to `ℳ`; the paper gets this
from the DLRA bound (5) with `g = ε_r max{1, e^{ℓ c_j h}}`, and
`exists_mem_near_flow_of_dlra` derives it from a DLRA trajectory (see
`prkDEIM_global_error_of_dlra`).  Then, for `0 ≤ h ≤ 1` and `γ = prkGamma a b L κ`,
`α = tabWeight a b` (1-based stage numbers as in the paper, `j.val = 0` is stage 1):

* stage 1: `Z₁ = Z̃₁` and `‖P^∠_{T(Z₁)} F(T(Z₁)) - F(Z̃₁)‖ ≤ C ε`;
* stages `j ≥ 2`: `‖Z_j - Z̃_j‖ ≤ α γ^s h (C ε + g + K h^{q₂ + 1})` and
  `‖P^∠_{T(Z_j)} F(T(Z_j)) - F(Z̃_j)‖ ≤ γ^s (C ε + g + K h^{q̃_j + 1})`,
  `q̃_j = min(q_j, q₂ + 1)`.

This is the printed statement with `c₁ = α γ^s`, `c₂ = γ^s`, and `c₃ C_{m,r}C_{n,r} ε_r`
replaced by the explicit `C ε + g` (the paper absorbs `g ≈ ε_r` into `c₃ C_{m,r}C_{n,r} ε_r`
using `C_{m,r}C_{n,r} ≥ 1`) and `h^{…}` by `K h^{…}`.  The paper's `h < h₀` is `h ≤ 1`. -/
theorem prkDEIM_stage_error {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {F : E → E} {L : ℝ}
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {T : E → E} {M : Set E} {κ : ℝ} (hT : ∀ x, ∀ z ∈ M, ‖T x - x‖ ≤ κ * ‖z - x‖) (hκ : 0 ≤ κ)
    {Pob P : E → E →L[ℝ] E} {C ε : ℝ} (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z))
    (hP0 : ∀ z ∈ M, P z ≠ 0) (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C)
    (hε : ∀ z ∈ M, ‖F z - P z (F z)‖ ≤ ε)
    {t h g K : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hg : 0 ≤ g) (hK : 0 ≤ K)
    {y y₁ zt : E} {Z Zt w : Fin s → E} (hy : y ∈ M)
    (hZ : IsPRKDEIMStep F T Pob a b h y Z y₁)
    (hZt : IsGalerkinRKStep (fun _ => F) a b c (fun _ => 1) 1 t h y Zt zt)
    (hTM : ∀ j, T (Z j) ∈ M) {q : Fin s → ℕ} {q₂ : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j)
    (hw : ∀ j : Fin s, 0 < j.val → ‖Zt j - w j‖ ≤ K * h ^ (q j + 1))
    (hM : ∀ j : Fin s, 0 < j.val → ∃ z ∈ M, ‖z - w j‖ ≤ h * g) (j : Fin s) :
    (j.val = 0 → Z j = Zt j ∧ ‖Pob (T (Z j)) (F (T (Z j))) - F (Zt j)‖ ≤ C * ε) ∧
    (0 < j.val →
      ‖Z j - Zt j‖ ≤
        tabWeight a b * prkGamma a b L κ ^ s * h * (C * ε + g + K * h ^ (q₂ + 1)) ∧
      ‖Pob (T (Z j)) (F (T (Z j))) - F (Zt j)‖ ≤
        prkGamma a b L κ ^ s * (C * ε + g + K * h ^ (min (q j) (q₂ + 1) + 1))) := by
  set γ := prkGamma a b L κ with hγdef
  set α := tabWeight a b with hαdef
  have hγ : 1 ≤ γ := one_le_prkGamma a b hL hκ
  have hα : 0 ≤ α := tabWeight_nonneg a b
  have hfield := norm_obliqueField_sub_le hP hP0 hC hε
  have hCε : 0 ≤ C * ε := (norm_nonneg _).trans (hfield y hy)
  have hZt' : ∀ j, Zt j = y + h • ∑ l, a j l • F (Zt l) := fun j => by
    rw [hZt.1 j]; simp
  set e : Fin s → E := fun j => Pob (T (Z j)) (F (T (Z j))) with he
  have hZ' : ∀ j, Z j = y + h • ∑ l, a j l • e l := hZ.1
  have hfirst : ∀ j : Fin s, j.val = 0 → Z j = y ∧ Zt j = y := by
    intro j hj
    have h0 : ∀ l, a j l = 0 := fun l =>
      ha j l (by rw [Fin.le_iff_val_le_val, hj]; exact Nat.zero_le _)
    exact ⟨by rw [hZ' j]; simp [h0], by rw [hZt' j]; simp [h0]⟩
  have hTy : T y = y := by
    have := hT y y hy
    rw [sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hE0 : ∀ j : Fin s, j.val = 0 → ‖e j - F (Zt j)‖ ≤ C * ε := by
    intro j hj
    obtain ⟨hZy, hZty⟩ := hfirst j hj
    simp only [he]
    rw [hZy, hZty, hTy]
    exact hfield y hy
  have hdiff : ∀ j, ‖Z j - Zt j‖ ≤ h * ∑ l, |a j l| * ‖e l - F (Zt l)‖ := by
    intro j
    have : Z j - Zt j = h • ∑ l, a j l • (e l - F (Zt l)) := by
      rw [hZ' j, hZt' j]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [this, norm_smul, Real.norm_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)) hh
    rw [norm_smul, Real.norm_eq_abs]
  have hE : ∀ j : Fin s, 0 < j.val → ‖e j - F (Zt j)‖ ≤
      C * ε + L * (κ * (h * g + K * h ^ (q j + 1)) + (1 + κ) * ‖Z j - Zt j‖) := by
    intro j hj
    obtain ⟨z, hz, hzw⟩ := hM j hj
    have h1 : ‖e j - F (T (Z j))‖ ≤ C * ε := hfield _ (hTM j)
    have hzZ : ‖z - Z j‖ ≤ h * g + K * h ^ (q j + 1) + ‖Z j - Zt j‖ := by
      have h2 : ‖w j - Zt j‖ ≤ K * h ^ (q j + 1) := by rw [norm_sub_rev]; exact hw j hj
      calc ‖z - Z j‖ ≤ ‖z - Zt j‖ + ‖Zt j - Z j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (‖z - w j‖ + ‖w j - Zt j‖) + ‖Zt j - Z j‖ :=
            add_le_add (norm_sub_le_norm_sub_add_norm_sub _ _ _) le_rfl
        _ ≤ h * g + K * h ^ (q j + 1) + ‖Z j - Zt j‖ := by
            rw [norm_sub_rev (Zt j)]; linarith
    have h2 : ‖T (Z j) - Zt j‖ ≤
        κ * (h * g + K * h ^ (q j + 1)) + (1 + κ) * ‖Z j - Zt j‖ := by
      calc ‖T (Z j) - Zt j‖ ≤ ‖T (Z j) - Z j‖ + ‖Z j - Zt j‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ κ * ‖z - Z j‖ + ‖Z j - Zt j‖ := add_le_add (hT _ z hz) le_rfl
        _ ≤ κ * (h * g + K * h ^ (q j + 1) + ‖Z j - Zt j‖) + ‖Z j - Zt j‖ := by gcongr
        _ = _ := by ring
    calc ‖e j - F (Zt j)‖ ≤ ‖e j - F (T (Z j))‖ + ‖F (T (Z j)) - F (Zt j)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * ε + L * ‖T (Z j) - Zt j‖ := add_le_add h1 (hF _ _)
      _ ≤ _ := by gcongr
  set X := C * ε + g + K * h ^ (q₂ + 1) with hXdef
  have hX0 : 0 ≤ X := add_nonneg (add_nonneg hCε hg) (mul_nonneg hK (pow_nonneg hh _))
  -- one stage, given the bounds of the earlier stages
  have hstep : ∀ j : Fin s, 0 < j.val →
      (∀ l : Fin s, l < j → ‖e l - F (Zt l)‖ ≤ γ ^ l.val * X) →
      ‖Z j - Zt j‖ ≤ α * γ ^ (j.val - 1) * h * X ∧
      ‖e j - F (Zt j)‖ ≤ γ ^ j.val * (C * ε + g + K * h ^ (min (q j) (q₂ + 1) + 1)) := by
    intro j hj IH
    have hd : ‖Z j - Zt j‖ ≤ α * γ ^ (j.val - 1) * h * X := by
      refine (hdiff j).trans ?_
      have hs := sum_abs_mul_le (w := a j) (D := fun l => ‖e l - F (Zt l)‖)
        (X := γ ^ (j.val - 1) * X) (mul_nonneg (pow_nonneg (by linarith) _) hX0)
        (fun l hl => by
          have hlj : l < j := lt_of_not_ge fun hjl => hl (ha j l hjl)
          refine (IH l hlj).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hγ ?_) hX0)
          have : l.val < j.val := hlj
          omega) (row_le_tabWeight a b j)
      calc h * ∑ l, |a j l| * ‖e l - F (Zt l)‖ ≤ h * (α * (γ ^ (j.val - 1) * X)) :=
            mul_le_mul_of_nonneg_left hs hh
        _ = α * γ ^ (j.val - 1) * h * X := by ring
    refine ⟨hd, ?_⟩
    set qt := min (q j) (q₂ + 1) with hqt
    set Xj := C * ε + g + K * h ^ (qt + 1) with hXj
    have hpow1 : h ^ (q j + 1) ≤ h ^ (qt + 1) :=
      pow_le_pow_of_le_one hh hh1 (by omega)
    have hpow2 : h * h ^ (q₂ + 1) ≤ h ^ (qt + 1) := by
      rw [← pow_succ']
      exact pow_le_pow_of_le_one hh hh1 (by omega)
    have hhX : h * X ≤ Xj := by
      have h1 : h * (C * ε) ≤ C * ε := mul_le_of_le_one_left hCε hh1
      have h2 : h * g ≤ g := mul_le_of_le_one_left hg hh1
      have h3 : h * (K * h ^ (q₂ + 1)) ≤ K * h ^ (qt + 1) := by
        rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hpow2 hK
      rw [hXdef, hXj]
      nlinarith
    have hXj0 : 0 ≤ Xj := add_nonneg (add_nonneg hCε hg) (mul_nonneg hK (pow_nonneg hh _))
    have hγj : γ ^ (j.val - 1) * γ = γ ^ j.val := by
      rw [← pow_succ]; congr 1; omega
    have hγj1 : 1 ≤ γ ^ (j.val - 1) := one_le_pow₀ hγ
    have hd' : (1 + κ) * ‖Z j - Zt j‖ ≤ (1 + κ) * (α * γ ^ (j.val - 1) * Xj) := by
      refine mul_le_mul_of_nonneg_left (hd.trans ?_) (by linarith)
      have : 0 ≤ α * γ ^ (j.val - 1) := mul_nonneg hα (by positivity)
      calc α * γ ^ (j.val - 1) * h * X = α * γ ^ (j.val - 1) * (h * X) := by ring
        _ ≤ α * γ ^ (j.val - 1) * Xj := mul_le_mul_of_nonneg_left hhX this
    have hκg : κ * (h * g + K * h ^ (q j + 1)) ≤ κ * Xj := by
      refine mul_le_mul_of_nonneg_left ?_ hκ
      have h2 : h * g ≤ g := mul_le_of_le_one_left hg hh1
      have h3 : K * h ^ (q j + 1) ≤ K * h ^ (qt + 1) := mul_le_mul_of_nonneg_left hpow1 hK
      rw [hXj]; linarith
    calc ‖e j - F (Zt j)‖
        ≤ C * ε + L * (κ * (h * g + K * h ^ (q j + 1)) + (1 + κ) * ‖Z j - Zt j‖) := hE j hj
      _ ≤ Xj + L * (κ * Xj + (1 + κ) * (α * γ ^ (j.val - 1) * Xj)) := by
          have : C * ε ≤ Xj := by
            rw [hXj]; have := mul_nonneg hK (pow_nonneg hh (qt + 1)); linarith
          gcongr
      _ = (1 + L * κ + L * (1 + κ) * α * γ ^ (j.val - 1)) * Xj := by ring
      _ ≤ (γ ^ (j.val - 1) * (1 + L * κ + L * (1 + κ) * α)) * Xj := by
          refine mul_le_mul_of_nonneg_right ?_ hXj0
          have hLκ : 0 ≤ L * κ := mul_nonneg hL hκ
          nlinarith
      _ = γ ^ j.val * Xj := by rw [← hγj, hγdef, prkGamma, ← hαdef]
  -- all stages
  have hall : ∀ k : ℕ, ∀ i : Fin s, i.val < k → ‖e i - F (Zt i)‖ ≤ γ ^ i.val * X := by
    intro k
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi
      rcases Nat.eq_zero_or_pos i.val with h0 | hpos
      · rw [h0, pow_zero, one_mul]
        have := mul_nonneg hK (pow_nonneg hh (q₂ + 1))
        linarith [hE0 i h0]
      · have hs := (hstep i hpos fun l hl => ih l (by have : l.val < i.val := hl; omega)).2
        refine hs.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _))
        have : h ^ (min (q i) (q₂ + 1) + 1) ≤ h ^ (q₂ + 1) :=
          pow_le_pow_of_le_one hh hh1 (by have := hq i hpos; omega)
        have := mul_le_mul_of_nonneg_left this hK
        linarith
  refine ⟨fun hj => ⟨(hfirst j hj).1.trans (hfirst j hj).2.symm, hE0 j hj⟩, fun hj => ?_⟩
  obtain ⟨hd, hEj⟩ := hstep j hj fun l _ => hall s l l.isLt
  have hjs : j.val ≤ s := j.isLt.le
  constructor
  · refine hd.trans ?_
    have : γ ^ (j.val - 1) ≤ γ ^ s := pow_le_pow_right₀ hγ (by omega)
    have := mul_le_mul_of_nonneg_left this hα
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hh hX0)
    nlinarith
  · refine hEj.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hγ hjs) ?_)
    exact add_nonneg (add_nonneg hCε hg) (mul_nonneg hK (pow_nonneg hh _))

/-- The constant `(1 + κ) (α γ^s + 2)` of the PRK-DEIM local error (`prkDEIM_local_error`). -/
noncomputable def prkConst (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L κ : ℝ) : ℝ :=
  (1 + κ) * (tabWeight a b * prkGamma a b L κ ^ s + 2)

/-- The local-error constant is nonnegative. -/
lemma prkConst_nonneg (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) {L κ : ℝ} (hL : 0 ≤ L)
    (hκ : 0 ≤ κ) : 0 ≤ prkConst a b L κ := by
  have := tabWeight_nonneg a b
  have := one_le_prkGamma a b hL hκ
  unfold prkConst
  positivity

/-- **Local error of one PRK-DEIM step** (the local estimate behind Theorem 14 of
arXiv 2510.19518, whose proof refers to Kieri–Vandereycken, Thm 6, and Lemma 13), *conditional
on the closeness hypotheses `hM`, `hMf`*.  In the setting of `prkDEIM_stage_error`, if the
classical RK step has order `p` (`‖z̃ - φ_F^h(y)‖ ≤ K h^{p+1}`, `wf = φ_F^h(y)`), `wf` is
`h g`-close to `ℳ`, and `q' ≤ p` and `q' ≤ q̃_j + 1` for every stage `j ≥ 2` with `b_j ≠ 0`, then
the PRK-DEIM step `y₁` satisfies `‖y₁ - φ_F^h(y)‖ ≤ h · prkConst · (C ε + g + K h^{q'})`. -/
theorem prkDEIM_local_error {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {F : E → E} {L : ℝ}
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {T : E → E} {M : Set E} {κ : ℝ} (hT : ∀ x, ∀ z ∈ M, ‖T x - x‖ ≤ κ * ‖z - x‖) (hκ : 0 ≤ κ)
    {Pob P : E → E →L[ℝ] E} {C ε : ℝ} (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z))
    (hP0 : ∀ z ∈ M, P z ≠ 0) (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C)
    (hε : ∀ z ∈ M, ‖F z - P z (F z)‖ ≤ ε)
    {t h g K : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hg : 0 ≤ g) (hK : 0 ≤ K)
    {y y₁ zt wf : E} {Z Zt w : Fin s → E} (hy : y ∈ M)
    (hZ : IsPRKDEIMStep F T Pob a b h y Z y₁)
    (hZt : IsGalerkinRKStep (fun _ => F) a b c (fun _ => 1) 1 t h y Zt zt)
    (hTM : ∀ j, T (Z j) ∈ M) {q : Fin s → ℕ} {q₂ p q' : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j)
    (hw : ∀ j : Fin s, 0 < j.val → ‖Zt j - w j‖ ≤ K * h ^ (q j + 1))
    (hM : ∀ j : Fin s, 0 < j.val → ∃ z ∈ M, ‖z - w j‖ ≤ h * g)
    (hp : ‖zt - wf‖ ≤ K * h ^ (p + 1)) (hMf : ∃ z ∈ M, ‖z - wf‖ ≤ h * g)
    (hqp : q' ≤ p) (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1) :
    ‖y₁ - wf‖ ≤ h * (prkConst a b L κ * (C * ε + g + K * h ^ q')) := by
  set γ := prkGamma a b L κ with hγdef
  set α := tabWeight a b with hαdef
  have hγ : 1 ≤ γ := one_le_prkGamma a b hL hκ
  have hα : 0 ≤ α := tabWeight_nonneg a b
  have hCε : 0 ≤ C * ε := (norm_nonneg _).trans (norm_obliqueField_sub_le hP hP0 hC hε y hy)
  set Y' := C * ε + g + K * h ^ q' with hY'
  have hY'0 : 0 ≤ Y' := add_nonneg (add_nonneg hCε hg) (mul_nonneg hK (pow_nonneg hh _))
  have hst := prkDEIM_stage_error ha hF hL hT hκ hP hP0 hC hε hh hh1 hg hK hy hZ hZt hTM hq hw hM
  set e : Fin s → E := fun j => Pob (T (Z j)) (F (T (Z j))) with he
  -- every weighted stage derivative is `γ^s Y'`-accurate
  have hEb : ∀ j, b j ≠ 0 → ‖e j - F (Zt j)‖ ≤ γ ^ s * Y' := by
    intro j hbj
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · refine ((hst j).1 h0).2.trans ?_
      have : Y' ≤ γ ^ s * Y' := le_mul_of_one_le_left hY'0 (one_le_pow₀ hγ)
      have := mul_nonneg hK (pow_nonneg hh q')
      linarith
    · refine ((hst j).2 hpos).2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : h ^ (min (q j) (q₂ + 1) + 1) ≤ h ^ q' := pow_le_pow_of_le_one hh hh1 (hqb j hpos hbj)
      have := mul_le_mul_of_nonneg_left this hK
      linarith
  have hzt : zt = y + h • ∑ j, b j • F (Zt j) := by rw [hZt.2]; simp
  set x := y + h • ∑ j, b j • e j with hx
  have hxzt : ‖x - zt‖ ≤ h * (α * (γ ^ s * Y')) := by
    have : x - zt = h • ∑ j, b j • (e j - F (Zt j)) := by
      rw [hx, hzt]; simp only [smul_sub, Finset.sum_sub_distrib]; abel
    rw [this, norm_smul, Real.norm_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left ?_ hh
    calc ‖∑ j, b j • (e j - F (Zt j))‖ ≤ ∑ j, ‖b j • (e j - F (Zt j))‖ := norm_sum_le _ _
      _ = ∑ j, |b j| * ‖e j - F (Zt j)‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ α * (γ ^ s * Y') := sum_abs_mul_le (by positivity) hEb (b_le_tabWeight a b)
  have hxw : ‖x - wf‖ ≤ h * ((α * γ ^ s + 1) * Y') := by
    have hp' : K * h ^ (p + 1) ≤ h * (K * h ^ q') := by
      rw [pow_succ, mul_comm (h ^ p) h, ← mul_assoc, mul_comm K h, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hh hh1 hqp) hK) hh
    have : K * h ^ q' ≤ Y' := by rw [hY']; linarith
    calc ‖x - wf‖ ≤ ‖x - zt‖ + ‖zt - wf‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ h * (α * (γ ^ s * Y')) + h * (K * h ^ q') := add_le_add hxzt (hp.trans hp')
      _ ≤ h * (α * (γ ^ s * Y')) + h * Y' := by gcongr
      _ = h * ((α * γ ^ s + 1) * Y') := by ring
  obtain ⟨z, hz, hzw⟩ := hMf
  have hy₁ : y₁ = T x := hZ.2
  have hgY : g ≤ Y' := by rw [hY']; have := mul_nonneg hK (pow_nonneg hh q'); linarith
  calc ‖y₁ - wf‖ = ‖T x - wf‖ := by rw [hy₁]
    _ ≤ ‖T x - x‖ + ‖x - wf‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ κ * ‖z - x‖ + ‖x - wf‖ := add_le_add (hT x z hz) le_rfl
    _ ≤ κ * (h * g + ‖x - wf‖) + ‖x - wf‖ := by
        gcongr
        calc ‖z - x‖ ≤ ‖z - wf‖ + ‖wf - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = ‖z - wf‖ + ‖x - wf‖ := by rw [norm_sub_rev wf]
          _ ≤ h * g + ‖x - wf‖ := by linarith
    _ = κ * (h * g) + (1 + κ) * ‖x - wf‖ := by ring
    _ ≤ κ * (h * Y') + (1 + κ) * (h * ((α * γ ^ s + 1) * Y')) := by gcongr
    _ ≤ h * ((1 + κ) * (α * γ ^ s + 2) * Y') := by
        have : κ * (h * Y') ≤ (1 + κ) * (h * Y') :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hh hY'0)
        nlinarith
    _ = h * (prkConst a b L κ * Y') := by rw [prkConst, ← hαdef, ← hγdef]

/-- **Theorem 14 of arXiv 2510.19518** (global error of PRK-DEIM), abstract form with an
explicit constant and a general admissible order `q'`, *conditional on the closeness hypotheses*
(`hM` inside `hstep` for the stage flows, `hMf` for the step flows; discharged from DLRA
trajectories in `prkDEIM_global_error_of_dlra`).  With `Y_{n+1}` a PRK-DEIM step from
`Y_n ∈ ℳ`, `Φ_n` the exact flow from `Y_n`, the hypotheses of `prkDEIM_stage_error` and
`prkDEIM_local_error` at every step, and `n h ≤ T_f`:
`‖Y_n - A(t_n)‖ ≤ e^{L T_f} (‖Y_0 - A(t_0)‖ + T_f · prkConst · (C ε + g + K h^{q'}))`,
i.e. `c_{1,2}(δ + c_{3,4} C_{m,r}C_{n,r} ε_r + h^q)` with explicit constants.  The printed
order `q = min{p, q₂ + 1}` is admissible for every tableau (`admissible_min_q₂`); for `b₂ = 0`
the proof gives the larger `min{p, q₃ + 1, q₂ + 2}` (`admissible_of_b₂_eq_zero`). -/
theorem prkDEIM_global_error {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) {F : E → E} {L : ℝ}
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {T : E → E} {M : Set E} {κ : ℝ} (hT : ∀ x, ∀ z ∈ M, ‖T x - x‖ ≤ κ * ‖z - x‖) (hκ : 0 ≤ κ)
    {Pob P : E → E →L[ℝ] E} {C ε : ℝ} (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z))
    (hP0 : ∀ z ∈ M, P z ≠ 0) (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C)
    (hε : ∀ z ∈ M, ‖F z - P z (F z)‖ ≤ ε) (hC0 : 0 ≤ C) (hε0 : 0 ≤ ε) {t₀ h g K : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1)
    (hg : 0 ≤ g) (hK : 0 ≤ K) {q : Fin s → ℕ} {q₂ p q' : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1)
    {N : ℕ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution (fun _ => F) (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) (hYM : ∀ n < N, Y n ∈ M)
    (hstep : ∀ n < N, ∃ (Z Zt w : Fin s → E) (zt : E),
      IsPRKDEIMStep F T Pob a b h (Y n) Z (Y (n + 1)) ∧
      IsGalerkinRKStep (fun _ => F) a b c (fun _ => 1) 1 (t₀ + n * h) h (Y n) Zt zt ∧
      (∀ j, T (Z j) ∈ M) ∧
      (∀ j : Fin s, 0 < j.val → ‖Zt j - w j‖ ≤ K * h ^ (q j + 1)) ∧
      (∀ j : Fin s, 0 < j.val → ∃ z ∈ M, ‖z - w j‖ ≤ h * g) ∧
      ‖zt - Φ n (t₀ + (n + 1) * h)‖ ≤ K * h ^ (p + 1))
    (hMf : ∀ n < N, ∃ z ∈ M, ‖z - Φ n (t₀ + (n + 1) * h)‖ ≤ h * g) {Tf : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ Tf →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * Tf) *
        (‖Y 0 - A t₀‖ + Tf * (prkConst a b L κ * (C * ε + g + K * h ^ q'))) := by
  have hFL : IsLipschitzField (fun _ : ℝ => F) L := fun _ x y => hF x y
  have hCε0 : 0 ≤ C * ε := mul_nonneg hC0 hε0
  refine lady_windermere_of_le hFL hL hh hA hΦ hΦ₀
    (mul_nonneg (prkConst_nonneg a b hL hκ)
      (add_nonneg (add_nonneg hCε0 hg) (mul_nonneg hK (pow_nonneg hh _)))) fun n hn => ?_
  obtain ⟨Z, Zt, w, zt, hZ, hZt, hTM, hw, hM, hp⟩ := hstep n hn
  exact prkDEIM_local_error ha hF hL hT hκ hP hP0 hC hε hh hh1 hg hK (hYM n hn) hZ hZt hTM hq
    hw hM hp (hMf n hn) hqp hqb

/-- The printed exponent of Theorem 14, `q = min{p, q₂ + 1}`, is admissible for
`prkDEIM_global_error` whatever the weights `b` (the printed `b₂ = 0` case
`min{p, q₃ + 1, q₂ + 1}` equals it, since `q₃ ≥ q₂`). -/
lemma admissible_min_q₂ {b : Fin s → ℝ} {q : Fin s → ℕ} {q₂ p : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) :
    ∀ j : Fin s, 0 < j.val → b j ≠ 0 → min p (q₂ + 1) ≤ min (q j) (q₂ + 1) + 1 := by
  intro j hj _
  have := hq j hj
  omega

/-- **The `b₂ = 0` case of Theorem 14 with the exponent of its proof**: if the second stage has
weight `b₂ = 0` and the later stages have order `≥ q₃`, then `q = min{p, q₃ + 1, q₂ + 2}` is
admissible for `prkDEIM_global_error`.  (The printed formula has `q₂ + 1` in place of `q₂ + 2`;
only `q₂ + 2` gives the full order `3` claimed for PRK3, whose stage orders are `q₂ = 1`,
`q₃ = 2`.) -/
lemma admissible_of_b₂_eq_zero {b : Fin s → ℝ} {q : Fin s → ℕ} {q₂ q₃ p : ℕ}
    (hb : ∀ j : Fin s, j.val = 1 → b j = 0) (hq₃ : ∀ j : Fin s, 2 ≤ j.val → q₃ ≤ q j) :
    ∀ j : Fin s, 0 < j.val → b j ≠ 0 → min p (min (q₃ + 1) (q₂ + 2)) ≤ min (q j) (q₂ + 1) + 1 := by
  intro j hj hbj
  have h2 : 2 ≤ j.val := by
    by_contra h
    exact hbj (hb j (by omega))
  have := hq₃ j h2
  omega

/-- **Closeness of the exact flow to `ℳ` from the DLRA error bound** (eq. (5) of
arXiv 2510.19518, as used in the proofs of Lemmas 11 and 13): if the exact flow `Φ` and a
perturbed trajectory `Ψ` (e.g. the DLRA solution `Ψ' = P(Ψ) F(Ψ)`, defect = normal component
`≤ ε_r`) start at the same point and `Ψ` ends in `ℳ`, then the end point of `Φ` is
`(b - a) ε_d e^{L (b - a)}`-close to `ℳ`. -/
theorem exists_mem_near_flow_of_dlra {F : E → E} {L : ℝ}
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) {M : Set E} {G : ℝ → E → E}
    {Φ Ψ : ℝ → E} {a b εd : ℝ} (hab : a ≤ b) (hεd : 0 ≤ εd)
    (hΦ : ODESolution (fun _ => F) Φ a b) (hΨ : ODESolution G Ψ a b) (h0 : Ψ a = Φ a)
    (hΨM : Ψ b ∈ M) (hG : ∀ r ∈ Ico a b, ‖G r (Ψ r) - F (Ψ r)‖ ≤ εd) :
    ∃ z ∈ M, ‖z - Φ b‖ ≤ (b - a) * (εd * Real.exp (L * (b - a))) := by
  have hFo : IsOneSidedLipschitzField (fun _ : ℝ => F) L :=
    IsLipschitzField.isOneSidedLipschitzField fun _ x y => hF x y
  refine ⟨Ψ b, hΨM, ?_⟩
  have h1 := hΦ.norm_sub_le_of_perturbed_max hΨ hFo hεd hG b ⟨hab, le_rfl⟩
  rw [h0, sub_self, norm_zero, mul_zero, zero_add,
    max_eq_right (Real.one_le_exp (mul_nonneg hL (sub_nonneg.2 hab)))] at h1
  calc ‖Ψ b - Φ b‖ ≤ εd * (b - a) * Real.exp (L * (b - a)) := h1
    _ = (b - a) * (εd * Real.exp (L * (b - a))) := by ring

/-- **Theorem 14 of arXiv 2510.19518 with the closeness hypotheses discharged by DLRA.**  As
`prkDEIM_global_error`, but the closeness of the exact stage and step flows to `ℳ` is derived
(`exists_mem_near_flow_of_dlra`, the paper's use of the DLRA bound (5)) from trajectories
`Ψ` that start at `Y_n`, end in `ℳ` and solve a perturbed problem with defect `≤ ε_d` (the
orthogonal DLRA `Ψ' = P(Ψ) F(Ψ)` on `ℳ_r` has `ε_d = ε_r` by Assumption 3), with stage nodes
`0 ≤ c_j ≤ 1`.  The bound becomes
`e^{L T_f}(‖Y_0 - A(t_0)‖ + T_f · prkConst · (C ε + ε_d e^{L h} + K h^{q'}))`.  The existence of
these DLRA trajectories on `ℳ` for one step is a hypothesis, as in the paper (Theorem 1 / eq. (5)
presuppose them). -/
theorem prkDEIM_global_error_of_dlra {a : Fin s → Fin s → ℝ} {b c : Fin s → ℝ}
    (ha : ∀ i j, i ≤ j → a i j = 0) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) {F : E → E} {L : ℝ}
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {T : E → E} {M : Set E} {κ : ℝ} (hT : ∀ x, ∀ z ∈ M, ‖T x - x‖ ≤ κ * ‖z - x‖) (hκ : 0 ≤ κ)
    {Pob P : E → E →L[ℝ] E} {C ε : ℝ} (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z))
    (hP0 : ∀ z ∈ M, P z ≠ 0) (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C)
    (hε : ∀ z ∈ M, ‖F z - P z (F z)‖ ≤ ε) (hC0 : 0 ≤ C) (hε0 : 0 ≤ ε) {t₀ h εd K : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hεd : 0 ≤ εd) (hK : 0 ≤ K) {q : Fin s → ℕ} {q₂ p q' : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1)
    {N : ℕ} {A : ℝ → E} (hA : ODESolution (fun _ => F) A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution (fun _ => F) (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) (hYM : ∀ n < N, Y n ∈ M)
    (hstep : ∀ n < N, ∃ (Z Zt : Fin s → E) (zt : E) (Φs Ψs : Fin s → ℝ → E)
      (Gs : Fin s → ℝ → E → E),
      IsPRKDEIMStep F T Pob a b h (Y n) Z (Y (n + 1)) ∧
      IsGalerkinRKStep (fun _ => F) a b c (fun _ => 1) 1 (t₀ + n * h) h (Y n) Zt zt ∧
      (∀ j, T (Z j) ∈ M) ∧
      (∀ j : Fin s, 0 < j.val →
        ODESolution (fun _ => F) (Φs j) (t₀ + n * h) (t₀ + n * h + c j * h) ∧
        Φs j (t₀ + n * h) = Y n ∧
        ‖Zt j - Φs j (t₀ + n * h + c j * h)‖ ≤ K * h ^ (q j + 1) ∧
        ODESolution (Gs j) (Ψs j) (t₀ + n * h) (t₀ + n * h + c j * h) ∧
        Ψs j (t₀ + n * h) = Y n ∧ Ψs j (t₀ + n * h + c j * h) ∈ M ∧
        ∀ r ∈ Ico (t₀ + n * h) (t₀ + n * h + c j * h), ‖Gs j r (Ψs j r) - F (Ψs j r)‖ ≤ εd) ∧
      ‖zt - Φ n (t₀ + (n + 1) * h)‖ ≤ K * h ^ (p + 1))
    {G : ℕ → ℝ → E → E} {Ψ : ℕ → ℝ → E}
    (hΨ : ∀ n < N, ODESolution (G n) (Ψ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΨ₀ : ∀ n < N, Ψ n (t₀ + n * h) = Y n) (hΨM : ∀ n < N, Ψ n (t₀ + (n + 1) * h) ∈ M)
    (hG : ∀ n < N, ∀ r ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h), ‖G n r (Ψ n r) - F (Ψ n r)‖ ≤ εd)
    {Tf : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ Tf →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * Tf) * (‖Y 0 - A t₀‖ +
        Tf * (prkConst a b L κ * (C * ε + εd * Real.exp (L * h) + K * h ^ q'))) := by
  have hg : 0 ≤ εd * Real.exp (L * h) := mul_nonneg hεd (Real.exp_pos _).le
  -- shrinking the closeness bound from `τ ≤ h` to `h`
  have hshrink : ∀ τ : ℝ, 0 ≤ τ → τ ≤ h →
      τ * (εd * Real.exp (L * τ)) ≤ h * (εd * Real.exp (L * h)) := fun τ hτ hτh =>
    mul_le_mul hτh (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτh hL)) hεd) (by positivity) hh
  refine prkDEIM_global_error (c := c) ha hF hL hT hκ hP hP0 hC hε hC0 hε0 hh hh1 hg hK hq hqp
    hqb hA hΦ hΦ₀ hYM (fun n hn => ?_) (fun n hn => ?_)
  · obtain ⟨Z, Zt, zt, Φs, Ψs, Gs, hZ, hZt, hTM, hst, hp⟩ := hstep n hn
    refine ⟨Z, Zt, fun j => Φs j (t₀ + n * h + c j * h), zt, hZ, hZt, hTM,
      fun j hj => (hst j hj).2.2.1, fun j hj => ?_, hp⟩
    obtain ⟨hΦj, hΦj0, -, hΨj, hΨj0, hΨjM, hGj⟩ := hst j hj
    have hcj := hc j
    have hτ0 : 0 ≤ c j * h := mul_nonneg hcj.1 hh
    obtain ⟨z, hz, hzd⟩ := exists_mem_near_flow_of_dlra hF hL (by linarith) hεd hΦj hΨj
      (hΨj0.trans hΦj0.symm) hΨjM hGj
    refine ⟨z, hz, hzd.trans ?_⟩
    rw [add_sub_cancel_left]
    exact hshrink _ hτ0 (mul_le_of_le_one_left hh hcj.2)
  · have hab : t₀ + n * h ≤ t₀ + (n + 1) * h := by nlinarith
    obtain ⟨z, hz, hzd⟩ := exists_mem_near_flow_of_dlra hF hL hab hεd (hΦ n hn) (hΨ n hn)
      ((hΨ₀ n hn).trans (hΦ₀ n hn).symm) (hΨM n hn) (hG n hn)
    refine ⟨z, hz, hzd.trans ?_⟩
    have hstep' : t₀ + (n + 1) * h - (t₀ + n * h) = h := by ring
    rw [hstep']

/-- Sanity check: a two-stage PRK-DEIM step (PRK2: `a₂₁ = 1`, `b = (1/2, 1/2)`) with
`T = id`, `P^∠ = I` and `F(x) = x` on `ℝ`, from `y = 1` with `h = 1/2`: stages `(1, 3/2)`,
result `13/8`. -/
example : IsPRKDEIMStep (E := ℝ) (s := 2) (fun x => x) id (fun _ => 1) ![![0, 0], ![1, 0]]
    ![1 / 2, 1 / 2] (1 / 2) 1 ![1, 3 / 2] (13 / 8) := by
  unfold IsPRKDEIMStep
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

/-- Sanity check: all hypotheses of `prkDEIM_global_error` hold together for PRK2 applied to
`ẏ = 1` on `ℝ` (`T = id`, `ℳ = ℝ`, `P^∠ = P = I`, `h = 1`, iterates `Y n = n`, exact flows
`Φ n t = t`, stage orders `q₂ = 1`); the scheme is exact here.  Genuinely oblique projectors
enter only through `IsObliqueProj` and `‖P^∠‖ ≤ C`, which the matrix examples of
`LeanDLRA.Matrix.Interpolation` exhibit. -/
example : ∀ n : ℕ, n ≤ 2 → (n : ℝ) * 1 ≤ 2 →
    ‖(n : ℝ) - (0 + n * 1)‖ ≤ Real.exp (0 * 2) * (‖((0 : ℕ) : ℝ) - 0‖ +
      2 * (prkConst (s := 2) ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] 0 1 *
        (1 * 0 + 0 + 0 * 1 ^ 2))) := by
  refine prkDEIM_global_error (E := ℝ) (s := 2) (a := ![![0, 0], ![1, 0]])
    (b := ![1 / 2, 1 / 2]) (c := ![0, 1]) (F := fun _ => 1) (L := 0) (T := id) (M := univ)
    (κ := 1) (Pob := fun _ => 1) (P := fun _ => 1) (C := 1) (ε := 0) (t₀ := 0) (h := 1)
    (g := 0) (K := 0) (q := fun _ => 1) (q₂ := 1) (p := 2) (q' := 2) (N := 2)
    (A := fun t => t) (Y := fun n => (n : ℝ)) (Φ := fun _ t => t) (Tf := 2) ?_
    (fun _ _ => by simp) le_rfl (fun _ _ _ => by simp) zero_le_one
    (fun _ _ => IsOrthProj.one.isObliqueProj) (fun _ _ => one_ne_zero)
    (fun _ _ => ContinuousLinearMap.norm_id_le) (fun _ _ => by simp)
    zero_le_one le_rfl zero_le_one le_rfl le_rfl le_rfl (fun _ _ => le_rfl) le_rfl
    (fun _ _ _ => by simp) ⟨continuousOn_id, fun t _ => hasDerivWithinAt_id t _⟩
    (fun _ _ => ⟨continuousOn_id, fun t _ => hasDerivWithinAt_id t _⟩) (fun _ _ => by simp)
    (fun _ _ => mem_univ _) (fun n _ => ?_) (fun n _ => ⟨0 + (n + 1) * 1, mem_univ _, by simp⟩)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · refine ⟨![(n : ℝ), n + 1], ![(n : ℝ), n + 1], ![(n : ℝ), n + 1], n + 1, ?_, ?_,
      fun _ => mem_univ _, fun _ _ => by simp,
      fun j _ => ⟨![(n : ℝ), n + 1] j, mem_univ _, by simp⟩, ?_⟩
    · unfold IsPRKDEIMStep
      refine ⟨fun j => ?_, ?_⟩
      · fin_cases j <;> simp [Fin.sum_univ_two]
      · simp [Fin.sum_univ_two]; try ring
    · unfold IsGalerkinRKStep
      refine ⟨fun j => ?_, ?_⟩
      · fin_cases j <;> simp [Fin.sum_univ_two]
      · simp [Fin.sum_univ_two]; try ring
    · simp

end PRKDEIM

section Lemma7

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Filippov velocities near a tangent trajectory point** (the estimate behind the corrected
uniqueness half of Lemma 7 of arXiv 2510.19518).  Let `F` be `L`-Lipschitz, let the oblique
projectors `P^∠(z)` onto the nonzero orthogonal (tangent) projectors `P(z)` have norm `≤ C` on
`ℳ`, and let `x` be a point where `F(x)` is tangent (`P(x) F(x) = F(x)`) and around which the
tangent projectors vary Lipschitz-continuously on `ℳ`:
`‖(P(z) - P(x)) w‖ ≤ κ ‖z - x‖ ‖w‖` (curvature bound; for `ℳ_r` this is
`Curvature.koch_lubich_tangent_frob` with `κ = 2 / σ_r(x)`).  Then every element `v` of the
Filippov set of the interpolatory field `z ↦ P^∠(z) F(z)` at any `y` satisfies
`‖v - F(x)‖ ≤ (C (L + κ ‖F(x)‖) + L) ‖y - x‖`. -/
theorem norm_sub_le_of_mem_filippov_of_tangent {F : E → E} {M : Set E}
    {Pob P : E → E →L[ℝ] E} {L C κ : ℝ} (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    (hκ : 0 ≤ κ) (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z)) (hP0 : ∀ z ∈ M, P z ≠ 0)
    (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C) (hC0 : 0 ≤ C) {x y v : E} (hTx : P x (F x) = F x)
    (hcurv : ∀ z ∈ M, ∀ w, ‖P z w - P x w‖ ≤ κ * ‖z - x‖ * ‖w‖)
    (hv : v ∈ filippov (fun z => Pob z (F z)) M y) :
    ‖v - F x‖ ≤ (C * (L + κ * ‖F x‖) + L) * ‖y - x‖ := by
  set K := C * (L + κ * ‖F x‖) + L with hK
  have hK0 : 0 ≤ K := by positivity
  have hz : ∀ z ∈ M, ‖Pob z (F z) - F x‖ ≤ K * ‖z - x‖ := by
    intro z hz
    have hn : ‖F z - P z (F z)‖ ≤ (L + κ * ‖F x‖) * ‖z - x‖ := by
      have hsplit : F z - P z (F z) =
          ((F z - F x) - P z (F z - F x)) + (P x (F x) - P z (F x)) := by
        rw [hTx, map_sub]; abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖(F z - F x) - P z (F z - F x)‖ ≤ L * ‖z - x‖ :=
        ((hP z hz).orth.norm_sub_le _).trans (hF z x)
      have h2 : ‖P x (F x) - P z (F x)‖ ≤ κ * ‖z - x‖ * ‖F x‖ := by
        rw [norm_sub_rev]; exact hcurv z hz (F x)
      nlinarith
    have hob : ‖F z - Pob z (F z)‖ ≤ C * ((L + κ * ‖F x‖) * ‖z - x‖) :=
      (hP z hz).norm_sub_le_of_normal (hP0 z hz) hn (hC z hz)
    calc ‖Pob z (F z) - F x‖ ≤ ‖Pob z (F z) - F z‖ + ‖F z - F x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * ((L + κ * ‖F x‖) * ‖z - x‖) + L * ‖z - x‖ := by
          rw [norm_sub_rev]; exact add_le_add hob (hF z x)
      _ = K * ‖z - x‖ := by rw [hK]; ring
  refine le_of_forall_pos_le_add fun η hη => ?_
  set δ := η / (K + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη (by linarith)
  have hKδ : K * δ ≤ η := by
    rw [hδ, mul_div_assoc']
    exact (div_le_iff₀ (by linarith)).2 (by nlinarith)
  have hsub : (fun z => Pob z (F z)) '' (Metric.ball y δ ∩ M) ⊆
      Metric.closedBall (F x) (K * (‖y - x‖ + δ)) := by
    rintro _ ⟨z, ⟨hzb, hzM⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (hz z hzM).trans (mul_le_mul_of_nonneg_left ?_ hK0)
    have : ‖z - y‖ < δ := by rw [← dist_eq_norm]; exact Metric.mem_ball.1 hzb
    calc ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖y - x‖ + δ := by linarith
  have hv' := mem_iInter₂.1 hv δ hδ0
  have hcl := closure_minimal (convexHull_min hsub (convex_closedBall _ _))
    Metric.isClosed_closedBall hv'
  rw [Metric.mem_closedBall, dist_eq_norm] at hcl
  nlinarith

/-- **Lemma 7 of arXiv 2510.19518, uniqueness half, corrected** (Assumption 1, `F` Lipschitz,
instead of mere continuity; the printed version is false, see
`lemma7_uniqueness_counterexample`).  Let `A` solve the full model `Ȧ = F(A)` with tangent
velocity `P(A) F(A) = F(A)` (derived from `A(t) ∈ ℳ` in `lemma7_of_lipschitz`), let the tangent
projectors satisfy the curvature bound `‖(P(z) - P(A(t))) w‖ ≤ κ ‖z - A(t)‖ ‖w‖` on `ℳ`, and let
the DEIM projectors be uniformly bounded on `ℳ` (`‖P^∠‖ ≤ C`; any DEIM selection with a bound
`C_{m,r} C_{n,r}`, QDEIM included, but QDEIM is not needed).  Then every solution `Y` of the
DLRA-DEIM inclusion (17) (continuous, right derivative in the Filippov set at every time of
`[a, b)`) with `Y(a) = A(a)` equals `A` on `[a, b]`.  The proof bounds the Filippov velocities by
`norm_sub_le_of_mem_filippov_of_tangent` and applies Grönwall; the paper instead argues via
Lemma 6 only at the points `A(t)`. -/
theorem eq_of_filippov_of_lipschitz {F : E → E} {M : Set E} {Pob P : E → E →L[ℝ] E}
    {L C κ B a b : ℝ} (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z)) (hP0 : ∀ z ∈ M, P z ≠ 0)
    (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C) (hC0 : 0 ≤ C) {A Y u : ℝ → E}
    (hA : ODESolution (fun _ => F) A a b) (hT : ∀ t ∈ Ico a b, P (A t) (F (A t)) = F (A t))
    (hcurv : ∀ t ∈ Ico a b, ∀ z ∈ M, ∀ w, ‖P z w - P (A t) w‖ ≤ κ * ‖z - A t‖ * ‖w‖)
    (hB : ∀ t ∈ Ico a b, ‖F (A t)‖ ≤ B)
    (hYc : ContinuousOn Y (Icc a b)) (hY : ∀ t ∈ Ico a b, HasDerivWithinAt Y (u t) (Ici t) t)
    (hu : ∀ t ∈ Ico a b, u t ∈ filippov (fun z => Pob z (F z)) M (Y t)) (h0 : Y a = A a) :
    ∀ t ∈ Icc a b, Y t = A t := by
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => Y t - A t)
    (f' := fun t => u t - F (A t)) (δ := 0) (K := C * (L + κ * B) + L) (ε := 0)
    (hYc.sub hA.cont) (fun t ht => (hY t ht).sub (hA.deriv t ht))
    (by simp [h0]) (fun t ht => by
      have h1 := norm_sub_le_of_mem_filippov_of_tangent hF hL hκ hP hP0 hC hC0 (hT t ht)
        (hcurv t ht) (hu t ht)
      refine h1.trans ?_
      rw [add_zero]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := mul_le_mul_of_nonneg_left (hB t ht) hκ
      nlinarith)
  intro t ht
  have := hg t ht
  rw [gronwallBound_ε0_δ0] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- **Velocities of curves in `ℳ` are tangent** (first step of the proof of Lemma 7 of
arXiv 2510.19518: `A(t) ∈ ℳ_r` for all `t` gives `Ȧ(t) ∈ T_{A(t)} ℳ_r`).  Abstract form: if the
chords `A(s) - A(t)`, `s ∈ [t, b]`, have quadratically small normal component at `A(t)`,
`‖(A(s) - A(t)) - P (A(s) - A(t))‖ ≤ c ‖A(s) - A(t)‖²`, and `A` has right derivative `v` at
`t < b`, then `v` is tangent: `P v = v`.  For a curve in `ℳ_r` and the tangent projector `P` at
`A(t)`, `Curvature.norm_normal_sub_le` (with the generalized inverse `G = A(s)⁺`) gives the chord
bound with `c = max_{s ∈ [t, b]} 1/σ_r(A(s))`. -/
theorem tangent_of_mem {P : E →L[ℝ] E} {c : ℝ} {A : ℝ → E} {v : E} {t b : ℝ}
    (htb : t < b) (hA : HasDerivWithinAt A v (Ici t) t)
    (hnc : ∀ s ∈ Icc t b, ‖(A s - A t) - P (A s - A t)‖ ≤ c * ‖A s - A t‖ ^ 2) : P v = v := by
  set Q : E →L[ℝ] E := 1 - P with hQ
  have hQx : ∀ x, Q x = x - P x := fun x => by simp [hQ]
  have hg := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1
    (Q.hasFDerivAt.comp_hasDerivWithinAt t (hA.sub_const (A t))).Ioi_of_Ici
  have hAs := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hA.Ioi_of_Ici
  have hcont : Tendsto (fun s => ‖A s - A t‖) (𝓝[>] t) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      ((hA.continuousWithinAt.mono Ioi_subset_Ici_self).tendsto)
  have hlim : Tendsto (fun s => c * ‖A s - A t‖ * ‖slope A t s‖) (𝓝[>] t) (𝓝 0) := by
    have := (tendsto_const_nhds (x := c)).mul hcont |>.mul hAs.norm
    simpa using this
  have hbound : ∀ᶠ s in 𝓝[>] t,
      ‖slope (fun s => Q (A s - A t)) t s‖ ≤ c * ‖A s - A t‖ * ‖slope A t s‖ := by
    filter_upwards [Ioo_mem_nhdsGT htb] with s hs
    rw [slope_def_module, slope_def_module, sub_self, map_zero, sub_zero, norm_smul, norm_smul]
    have h1 : ‖Q (A s - A t)‖ ≤ c * ‖A s - A t‖ ^ 2 := by
      rw [hQx]; exact hnc s ⟨hs.1.le, hs.2.le⟩
    calc ‖(s - t)⁻¹‖ * ‖Q (A s - A t)‖ ≤ ‖(s - t)⁻¹‖ * (c * ‖A s - A t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c * ‖A s - A t‖ * (‖(s - t)⁻¹‖ * ‖A s - A t‖) := by ring
  have h0 := tendsto_nhds_unique hg (squeeze_zero_norm' hbound hlim)
  rw [hQx, sub_eq_zero] at h0
  exact h0.symm

/-- **Lemma 7 of arXiv 2510.19518, corrected** (both halves, from `A(t) ∈ ℳ`).  Let `F` be
`L`-Lipschitz (Assumption 1, replacing the printed "F continuous") and let `A` solve the full model
on `[a, b]` with `A(t) ∈ ℳ`.  Assume the two curvature bounds of `ℳ` along `A` (for `ℳ_r` both
follow from `LeanDLRA.Matrix.Curvature`: `norm_normal_sub_le` gives the chord bound `hnc` with
`c = max_s 1/σ_r(A(s))`, `koch_lubich_tangent_frob` gives `hcurv` with
`κ = 2 / min_t σ_r(A(t))`) and DEIM
projectors that are oblique projectors onto `P(z)` with `‖P^∠(z)‖ ≤ C` on `ℳ`.  Then
(existence) `A` solves the DLRA-DEIM inclusion (17): `Ȧ(t) = F(A(t)) ∈ 𝓕(A(t))`; and
(uniqueness) every solution of (17) starting at `A(a)` equals `A`.  Tangency `Ȧ ∈ T_A ℳ` is
derived (`tangent_of_mem`), not assumed; the bound on `‖F(A(t))‖` comes from compactness.
Solutions are understood with right derivatives at every time (the library's ODE convention),
not almost everywhere. -/
theorem lemma7_of_lipschitz {F : E → E} {M : Set E} {Pob P : E → E →L[ℝ] E}
    {L C κ c a b : ℝ} (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hP : ∀ z ∈ M, IsObliqueProj (Pob z) (P z)) (hP0 : ∀ z ∈ M, P z ≠ 0)
    (hC : ∀ z ∈ M, ‖Pob z‖ ≤ C) (hC0 : 0 ≤ C) {A : ℝ → E}
    (hA : ODESolution (fun _ => F) A a b) (hAM : ∀ t ∈ Icc a b, A t ∈ M)
    (hnc : ∀ t ∈ Ico a b, ∀ s ∈ Icc t b,
      ‖(A s - A t) - P (A t) (A s - A t)‖ ≤ c * ‖A s - A t‖ ^ 2)
    (hcurv : ∀ t ∈ Ico a b, ∀ z ∈ M, ∀ w, ‖P z w - P (A t) w‖ ≤ κ * ‖z - A t‖ * ‖w‖) :
    (∀ t ∈ Ico a b, F (A t) ∈ filippov (fun z => Pob z (F z)) M (A t)) ∧
    ∀ (Y u : ℝ → E), ContinuousOn Y (Icc a b) →
      (∀ t ∈ Ico a b, HasDerivWithinAt Y (u t) (Ici t) t) →
      (∀ t ∈ Ico a b, u t ∈ filippov (fun z => Pob z (F z)) M (Y t)) → Y a = A a →
      ∀ t ∈ Icc a b, Y t = A t := by
  have hT : ∀ t ∈ Ico a b, P (A t) (F (A t)) = F (A t) := fun t ht =>
    tangent_of_mem ht.2 (hA.deriv t ht) (hnc t ht)
  refine ⟨fun t ht => mem_filippov_of_mem_range (hAM t (Ico_subset_Icc_self ht))
    (hP _ (hAM t (Ico_subset_Icc_self ht))) (hT t ht), fun Y u hYc hY hu h0 => ?_⟩
  have hFc : Continuous F := (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm]; exact hF x y : LipschitzWith ⟨L, hL⟩ F).continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hFc.comp_continuousOn hA.cont)
  exact eq_of_filippov_of_lipschitz hF hL hκ hP hP0 hC hC0 hA hT hcurv
    (fun t ht => hB t (Ico_subset_Icc_self ht)) hYc hY hu h0

/-! ### The printed uniqueness claim of Lemma 7 fails for continuous `F` -/

namespace Lemma7Counterexample

open Matrix
open scoped LeanDLRA.Frobenius

/-- `A₀ = e₁ e₁ᵀ`, a rank-one `2 × 2` matrix. -/
def A₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The first unit vector `e₁ ∈ ℝ^{2 × 1}`. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The selection matrix `e_i ∈ ℝ^{2 × 1}` (one DEIM index). -/
def sel (i : Fin 2) : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun k _ => if k = i then 1 else 0

/-- `X ↦ X₂₂ - X₁₁` (1-based entries) as a continuous linear functional. -/
noncomputable def diagDiff : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X 1 1 - X 0 0
      map_add' := fun X Y => by simp only [Matrix.add_apply]; ring
      map_smul' := fun c X => by
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

/-- Value of `diagDiff`. -/
lemma diagDiff_apply (X : Matrix (Fin 2) (Fin 2) ℝ) : diagDiff X = X 1 1 - X 0 0 := rfl

/-- The field `F(X) = √(min(|1 - X₁₁ + X₂₂|, 1)) I`: continuous and bounded, but not Lipschitz. -/
noncomputable def F (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.sqrt (min |1 + diagDiff X| 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The second solution `Y(t) = (1 + t²/4) e₁ e₁ᵀ`. -/
noncomputable def Y (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (1 + t ^ 2 / 4) • A₀

/-- `F(X)` is a multiple of `I`, so `diagDiff (F X) = 0`. -/
lemma diagDiff_F (X : Matrix (Fin 2) (Fin 2) ℝ) : diagDiff (F X) = 0 := by
  simp [F, diagDiff_apply]

/-- `F` is continuous. -/
lemma continuous_F : Continuous F :=
  (Real.continuous_sqrt.comp
    ((continuous_abs.comp (continuous_const.add diagDiff.continuous)).min continuous_const)).smul
    continuous_const

/-- `F` is bounded (Assumption 4 of arXiv 2510.19518). -/
lemma norm_F_le (X : Matrix (Fin 2) (Fin 2) ℝ) : ‖F X‖ ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
  rw [F, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have : Real.sqrt (min |1 + diagDiff X| 1) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact min_le_right _ _
  exact mul_le_of_le_one_left (norm_nonneg _) this

/-- `F(A₀) = 0`. -/
lemma F_A₀ : F A₀ = 0 := by
  simp [F, A₀, diagDiff_apply]

/-- `A ≡ A₀` solves the full model `Ȧ = F(A)`. -/
lemma odeSolution_A₀ (T : ℝ) : ODESolution (fun _ => F) (fun _ => A₀) 0 T where
  cont := continuousOn_const
  deriv t _ := by rw [F_A₀]; exact hasDerivWithinAt_const _ _ _

/-- The full model `Ȧ = F(A)`, `A(0) = A₀`, has the unique solution `A ≡ A₀`: `X₂₂ - X₁₁` is
conserved (`F(X)` is a multiple of `I`), so `1 - X₁₁ + X₂₂ ≡ 0` and `F(X(t)) = 0`. -/
lemma full_unique {T : ℝ} {X : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hX : ODESolution (fun _ => F) X 0 T)
    (h0 : X 0 = A₀) : ∀ t ∈ Icc 0 T, X t = A₀ := by
  have hd := constant_of_has_deriv_right_zero (diagDiff.continuous.comp_continuousOn hX.cont)
    (fun t ht => by
      have := diagDiff.hasFDerivAt.comp_hasDerivWithinAt t (hX.deriv t ht)
      simpa [diagDiff_F] using this)
  have hF0 : ∀ t ∈ Icc 0 T, F (X t) = 0 := fun t ht => by
    have h1 : diagDiff (X t) = -1 := by
      have := hd t ht
      simp only [Function.comp] at this
      rw [this, h0]; simp [diagDiff_apply, A₀]
    simp [F, h1]
  have hc := constant_of_has_deriv_right_zero hX.cont
    (fun t ht => by
      have := hX.deriv t ht
      rwa [hF0 t (Ico_subset_Icc_self ht)] at this)
  intro t ht
  rw [hc t ht, h0]

/-- `c e₁e₁ᵀ` has rank one for `c ≠ 0`. -/
lemma rank_smul_A₀ {c : ℝ} (hc : c ≠ 0) : (c • A₀).rank = 1 := by
  have : c • A₀ = Matrix.diagonal ![c, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A₀]
  rw [this, Matrix.rank_diagonal]
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, by simpa using hc⟩, fun ⟨i, hi⟩ => ?_⟩
  fin_cases i
  · rfl
  · simp at hi

/-- `A₀ ∈ ℳ₁`. -/
lemma rank_A₀ : A₀.rank = 1 := by
  simpa using rank_smul_A₀ (c := 1) one_ne_zero

/-- `Y(0) = A₀`. -/
lemma Y_zero : Y 0 = A₀ := by simp [Y]

/-- `Y` leaves `A₀`. -/
lemma Y_two_ne : Y 2 ≠ A₀ := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [Y, A₀] at this

/-- `Ẏ(t) = (t/2) e₁e₁ᵀ`. -/
lemma hasDerivAt_Y (t : ℝ) : HasDerivAt Y ((t / 2) • A₀) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2 / 4) (t / 2) t := by
    have := ((hasDerivAt_pow 2 t).div_const 4).const_add 1
    convert this using 1; push_cast; ring
  exact h1.smul_const A₀

/-- `Y(t) ∈ ℳ₁`. -/
lemma rank_Y (t : ℝ) : (Y t).rank = 1 :=
  rank_smul_A₀ (by positivity)

/-- `F(Y(t)) = (t/2) I` for `t ∈ [0, 2]`. -/
lemma F_Y {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    F (Y t) = (t / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h1 : 1 + diagDiff (Y t) = -(t ^ 2 / 4) := by
    simp [diagDiff_apply, Y, A₀]
  have h2 : t ^ 2 / 4 ≤ 1 := by nlinarith [ht.1, ht.2]
  have h3 : Real.sqrt (t ^ 2 / 4) = t / 2 := by
    rw [show t ^ 2 / 4 = (t / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith [ht.1])
  rw [F, h1, abs_neg, abs_of_nonneg (by positivity), min_eq_left h2, h3]

/-- `e₁ᵀ e₁ = 1`. -/
lemma transpose_e₁_mul_e₁ : e₁ᵀ * e₁ = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [e₁, Matrix.mul_apply]

/-- `e₁ e₁ᵀ = A₀`. -/
lemma e₁_mul_transpose : e₁ * e₁ᵀ = A₀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, A₀, Matrix.mul_apply]

/-- **Every DEIM selection at `Y(t)` is the first index**: for any basis `U = e₁ R` of the
column space of `Y(t)` and any selection matrix `S = e_i` with `SᵀU` invertible (the requirement
of every DEIM procedure, QDEIM included), the oblique projector is `U (SᵀU)⁻¹ Sᵀ = e₁ e₁ᵀ`. -/
lemma obliqueProj_eq_A₀ {R : Matrix (Fin 1) (Fin 1) ℝ} (hR : IsUnit R.det) {i : Fin 2}
    (hSU : IsUnit ((sel i)ᵀ * (e₁ * R)).det) : obliqueProj (e₁ * R) (sel i) = A₀ := by
  have hi : i = 0 := by
    by_contra hne
    have h1 : i = 1 := by
      fin_cases i
      · exact absurd rfl hne
      · rfl
    subst h1
    have h0 : (sel 1)ᵀ * e₁ = 0 := by
      ext a b; fin_cases a; fin_cases b; simp [sel, e₁, Matrix.mul_apply]
    rw [← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.det_zero] at hSU
    exact not_isUnit_zero hSU
  subst hi
  have hsel : sel 0 = e₁ := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [sel, e₁]
  rw [obliqueProj_mul_right hR, hsel,
    obliqueProj_self_of_orthonormal transpose_e₁_mul_e₁, e₁_mul_transpose]

/-- `A₀` is symmetric. -/
lemma transpose_A₀ : A₀ᵀ = A₀ := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `A₀` is idempotent. -/
lemma A₀_mul_A₀ : A₀ * A₀ = A₀ := by
  rw [← e₁_mul_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc e₁ᵀ, transpose_e₁_mul_e₁,
    Matrix.one_mul]

/-- The DEIM tangent projector at `Y(t)` maps `c I` to `c e₁ e₁ᵀ`. -/
lemma obliqueTangentProj_smul_one {U V SU SV : Matrix (Fin 2) (Fin 1) ℝ}
    (hU : obliqueProj U SU = A₀) (hV : obliqueProj V SV = A₀) (c : ℝ) :
    obliqueTangentProj U SU V SV (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = c • A₀ := by
  rw [obliqueTangentProj_apply, hU, hV, transpose_A₀]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, A₀_mul_A₀]
  abel

end Lemma7Counterexample

open Lemma7Counterexample LeanDLRA.Frobenius in
/-- **The uniqueness claim of Lemma 7 of arXiv 2510.19518 fails as printed.**  Lemma 7 states:
if the full model has a unique solution with `A(t) ∈ ℳ_r` and `F` is continuous, then `A` is the
unique differentiable solution of the DLRA-DEIM inclusion (17) when QDEIM is used.  On
`ℝ^{2×2}`, `r = 1`, take `F(X) = √(min(|1 - X₁₁ + X₂₂|, 1)) I`: it is continuous and bounded
(Assumption 4 holds), and the full model from `A₀ = e₁e₁ᵀ ∈ ℳ₁` has the unique solution
`A ≡ A₀` (`X₂₂ - X₁₁` is conserved).  Yet `Y(t) = (1 + t²/4) e₁e₁ᵀ ∈ ℳ₁` is a second
differentiable solution of (17) on `[0, 2]`: for every DEIM projector at `Y(t)` (built from any
basis `U = e₁R`, `V = e₁R'` of its column/row space and any admissible selection; QDEIM selects
the first row and column), `P^∠(Y(t)) F(Y(t)) = (t/2) e₁e₁ᵀ = Ẏ(t)`, which lies in the
Filippov set.  The corrected statement under Assumption 1 is `lemma7_of_lipschitz`. -/
theorem lemma7_uniqueness_counterexample :
    Continuous F ∧ (∀ X, ‖F X‖ ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) ∧
    (∀ T, ODESolution (fun _ => F) (fun _ => A₀) 0 T) ∧
    (∀ T (X : ℝ → Matrix (Fin 2) (Fin 2) ℝ), ODESolution (fun _ => F) X 0 T → X 0 = A₀ →
      ∀ t ∈ Icc 0 T, X t = A₀) ∧
    A₀.rank = 1 ∧ Y 0 = A₀ ∧ Y 2 ≠ A₀ ∧
    ∀ Pob : Matrix (Fin 2) (Fin 2) ℝ → (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ),
      (∀ t ∈ Icc (0 : ℝ) 2, ∃ (R R' : Matrix (Fin 1) (Fin 1) ℝ) (i j : Fin 2),
        IsUnit R.det ∧ IsUnit R'.det ∧ IsUnit ((sel i)ᵀ * (e₁ * R)).det ∧
        IsUnit ((sel j)ᵀ * (e₁ * R')).det ∧
        Pob (Y t) = obliqueTangentProj (e₁ * R) (sel i) (e₁ * R') (sel j)) →
      ∀ t ∈ Icc (0 : ℝ) 2, (Y t).rank = 1 ∧ HasDerivAt Y ((t / 2) • A₀) t ∧
        (t / 2) • A₀ ∈ filippov (fun z => Pob z (F z)) {X | X.rank = 1} (Y t) := by
  refine ⟨continuous_F, norm_F_le, odeSolution_A₀, fun T X hX h0 => full_unique hX h0, rank_A₀,
    Y_zero, Y_two_ne, fun Pob hPob t ht => ⟨rank_Y t, hasDerivAt_Y t, ?_⟩⟩
  obtain ⟨R, R', i, j, hR, hR', hi, hj, hP⟩ := hPob t ht
  have hf : (fun z => Pob z (F z)) (Y t) = (t / 2) • A₀ := by
    simp only
    rw [hP, F_Y ht]
    exact obliqueTangentProj_smul_one (obliqueProj_eq_A₀ hR hi) (obliqueProj_eq_A₀ hR' hj) _
  rw [← hf]
  exact mem_filippov_self (rank_Y t)

open Lemma7Counterexample LeanDLRA.Frobenius in
/-- The hypothesis on `Pob` in `lemma7_uniqueness_counterexample` is satisfiable: QDEIM (or any
DEIM procedure) at `Y(t) = (1 + t²/4) e₁ e₁ᵀ` with the SVD factors `U = V = e₁` selects the first
row and column, giving `P^∠(Y(t)) = obliqueTangentProj e₁ e₁ e₁ e₁`. -/
example : ∀ t ∈ Icc (0 : ℝ) 2, ∃ (R R' : Matrix (Fin 1) (Fin 1) ℝ) (i j : Fin 2),
    IsUnit R.det ∧ IsUnit R'.det ∧ IsUnit ((sel i)ᵀ * (e₁ * R)).det ∧
    IsUnit ((sel j)ᵀ * (e₁ * R')).det ∧
    (fun _ => obliqueTangentProj e₁ e₁ e₁ e₁ :
      Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) (Y t) =
      obliqueTangentProj (e₁ * R) (sel i) (e₁ * R') (sel j) := by
  intro t _
  have hsel : sel 0 = e₁ := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [sel, e₁]
  refine ⟨1, 1, 0, 0, by simp, by simp, ?_, ?_, by simp [hsel]⟩ <;>
    rw [Matrix.mul_one, hsel, transpose_e₁_mul_e₁] <;> simp

end Lemma7

end LeanDLRA.Literature.P2510_19518
