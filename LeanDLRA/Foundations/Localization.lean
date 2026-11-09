import LeanDLRA.Foundations.Existence
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Analysis.Defs

/-!
# Localisation: tube hypotheses, global extension, bootstrap and continuation

The robust error analyses of dynamical low-rank integrators (Kieri–Lubich–Walach 2016;
Ceruti–Lubich, arXiv 2010.02022; Ceruti–Kusch–Lubich, arXiv 2104.05247, 2304.05660) assume
that the right-hand side `F(t, Y)` is Lipschitz and bounded **globally**.  For almost every
PDE application (cubic nonlinearities, Vlasov, Burgers, ...) these constants only exist on a
neighbourhood of the exact solution, and the literature delegates the localisation to a
remark.  This file provides the localisation machinery and addresses the open problems
**OP-EX-01** (bootstrap keeping iterates in the tube), **OP-OT-10** (cubic nonlinearity) and
**OP-EX-04** (continuation principle, counterexample to global existence on the manifold).

## Main results

* `IsLipschitzOnTube F A a b ρ L`, `IsBoundedOnTube F A a b ρ B`: Lipschitz/bound hypotheses
  only on the tube `{(t, x) | t ∈ [a, b], ‖x - A t‖ ≤ ρ}` (arXiv 2010.05249, Property 1(b)).
* `norm_radialRetract_sub_le`, `norm_ballRetract_sub_le`: the radial retraction onto a closed
  ball is `1`-Lipschitz (metric projection onto a convex set, via its variational inequality).
* `tubeExt`: the **global extension** `F̃ t x = F t (r_t x)` (`r_t` the retraction onto the
  ball of radius `ρ` around `A t`).  It agrees with `F` on the tube and is globally
  `L`-Lipschitz (`isLipschitzField_tubeExt`) and `B`-bounded (`isBoundedField_tubeExt`) with the
  **same** constants, and continuous in time (`continuousOn_tubeExt`).
* `odeSolution_comp_tubeExt_iff`: trajectories (also of projected fields `Ψ ∘ F`) that stay in
  the tube solve the extended problem iff they solve the original one.
* `tube_trap`, `norm_sub_le_of_tube_trap`: **trapping lemma** (first-exit argument): a
  trajectory of a field bounded by `By` on the tube, started `d`-close to `A`, stays strictly
  inside as long as `d + (Ba + By)(t - s) < ρ`.
* `bootstrap_of_global`: the generic bootstrap pattern (reusable for KSL, parallel BUG, Tucker).
* `IsBUGStep.tubeExt`, `bug_global_error_le_of_tube`: **OP-EX-01 for the BUG integrator**:
  if `c₀ δ + c₁ ε + c₂ h + 4 B h < ρ`, every iterate and substep stays in the tube and the
  robust global bound of Ceruti–Lubich (arXiv 2010.02022, Theorem 4) holds with the same
  constants for the locally Lipschitz field.
* Continuation (OP-EX-04 (b), abstract form): `exists_ODESolution_of_apriori` (an a priori
  bound for the extended problem gives a solution of the original problem on the whole
  interval), `eqOn_of_tube` (uniqueness inside the tube), `exists_ODESolution_near` (global
  existence for initial values near a solution), `exists_ODESolution_of_linearGrowth` (global
  existence for globally Lipschitz **unbounded** fields, which Mathlib's Picard–Lindelöf and
  `Foundations/Existence` do not cover).
* `isLipschitzField_reducedFlux`, `existsUnique_reducedFlux`: Billaud-Friess–Nouy,
  arXiv 1604.05706, Remark 1 — the reduced flux with a moving orthonormal basis is
  `(L + sup ‖Vᵀ V'‖)`-Lipschitz, and the reduced system is uniquely solvable on `[a, b]`.
* `isUnit_det_coeff_of_near`: Weyl-type lemma without SVD (OP-EX-04 (b)): if `A = U S Vᵀ`,
  `‖S⁻¹‖_F ≤ γ` and `γ ‖Y - A‖_F ≤ θ < 1`, then `Uᵀ Y V` is invertible with
  `‖(Uᵀ Y V)⁻¹‖_F ≤ γ / (1 - θ)`, so `Y` keeps rank `≥ k`.
* `not_exists_odeSolution_mem_manifold`: the counterexample of OP-EX-04: for
  `A(t) = diag(1, 1 - t)` the DLRA solution leaves `M₂` at `t = 1`.
* Cubic nonlinearity (OP-OT-10, arXiv 2010.05249, Property 1(b)): `norm_cubic_sub_le`
  (`‖|u|²u - |v|²v‖ ≤ (|u|² + |u||v| + |v|²) ‖u - v‖` in any real normed space),
  `norm_complex_cubic_sub_le`, the Frobenius tube constants `isLipschitzOnTube_entrywiseCubic`,
  `isBoundedOnTube_entrywiseCubic`, and the robust BUG bound for the cubic field
  `bug_global_error_le_entrywiseCubic`.
* Gram-inverse ball (Kazashi–Nobile–Zoccolan, arXiv 2308.11581, Prop. A.1 = arXiv 2609.20307,
  Prop. 2.2): `gramMatrix_inv_ball`; with the Frobenius perturbation lemmas
  `isUnit_det_add_of_norm_le`, `norm_inv_add_le`.

## Deviations from the literature and what remains open

* The retraction is the metric projection onto a ball around `A t`, so no Kirszbraun-type
  extension is needed and the constants are not inflated (`L`, not `2 L`).
* In OP-EX-01 the margin is `4 B h` instead of `2 B h`: the Galerkin substep starts at
  `P₁ Q₁ Yₙ`, which is up to `2 B h` away from `Yₙ`.  The strict inequality is necessary in
  general (`tube_trap`).
* OP-EX-01 is resolved here for the (abstract, hence matrix) BUG integrator; the KSL, parallel,
  rank-adaptive and Tucker/tree-tensor versions follow the same pattern (`bootstrap_of_global`
  plus a step-conversion lemma like `IsBUGStep.tubeExt`) but are not stated here.
* OP-EX-04: the blow-up alternative (a) is not formalised; for (b) the abstract continuation
  principle and the Weyl-type invertibility certificate are proved, but their combination with
  local Lipschitz continuity of the DLRA field `P(Y) F` on `{σ_r ≥ ρ}` (which needs a tube
  inside the manifold, not a ball in `E`) is not; part (c) (generalised global solutions) is
  open.
* OP-OT-10: the RK4 inner solves of the projector-splitting substeps are not covered (they are
  the subject of the inexact-substep entry).
-/

open Set Metric
open scoped RealInnerProductSpace NNReal

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Tube hypotheses -/

section Tube

omit [InnerProductSpace ℝ E] in
/-- Global hypotheses imply the tube hypotheses. -/
lemma IsLipschitzField.isLipschitzOnTube {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    (A : ℝ → E) (a b ρ : ℝ) : IsLipschitzOnTube F A a b ρ L :=
  fun t _ x y _ _ => hF t x y

omit [InnerProductSpace ℝ E] in
/-- Global hypotheses imply the tube hypotheses. -/
lemma IsBoundedField.isBoundedOnTube {F : ℝ → E → E} {B : ℝ} (hF : IsBoundedField F B)
    (A : ℝ → E) (a b ρ : ℝ) : IsBoundedOnTube F A a b ρ B :=
  fun t _ x _ => hF t x

omit [InnerProductSpace ℝ E] in
/-- Tube hypotheses are inherited by smaller tubes and subintervals. -/
lemma IsLipschitzOnTube.mono {F : ℝ → E → E} {A : ℝ → E} {a b ρ L a' b' ρ' : ℝ}
    (hF : IsLipschitzOnTube F A a b ρ L) (ha : a ≤ a') (hb : b' ≤ b) (hρ : ρ' ≤ ρ) :
    IsLipschitzOnTube F A a' b' ρ' L := fun t ht x y hx hy =>
  hF t ⟨ha.trans ht.1, ht.2.trans hb⟩ x y (hx.trans hρ) (hy.trans hρ)

omit [InnerProductSpace ℝ E] in
/-- Tube hypotheses are inherited by smaller tubes and subintervals. -/
lemma IsBoundedOnTube.mono {F : ℝ → E → E} {A : ℝ → E} {a b ρ B a' b' ρ' : ℝ}
    (hF : IsBoundedOnTube F A a b ρ B) (ha : a ≤ a') (hb : b' ≤ b) (hρ : ρ' ≤ ρ) :
    IsBoundedOnTube F A a' b' ρ' B := fun t ht x hx =>
  hF t ⟨ha.trans ht.1, ht.2.trans hb⟩ x (hx.trans hρ)

end Tube

/-! ### The radial retraction onto a closed ball -/

section Retraction

lemma radialRetract_of_norm_le {ρ : ℝ} {z : E} (hz : ‖z‖ ≤ ρ) : radialRetract ρ z = z := by
  unfold radialRetract
  rcases (norm_nonneg z).eq_or_lt with h0 | hpos
  · rw [norm_eq_zero.1 h0.symm, smul_zero]
  · rw [min_eq_left ((one_le_div hpos).2 hz), one_smul]

omit [InnerProductSpace ℝ E] in
lemma radialRetract_coeff_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (z : E) : 0 ≤ min 1 (ρ / ‖z‖) :=
  le_min zero_le_one (div_nonneg hρ (norm_nonneg z))

lemma norm_radialRetract_le {ρ : ℝ} (hρ : 0 ≤ ρ) (z : E) : ‖radialRetract ρ z‖ ≤ ρ := by
  unfold radialRetract
  rw [norm_smul, Real.norm_of_nonneg (radialRetract_coeff_nonneg hρ z)]
  rcases (norm_nonneg z).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact hρ
  · calc min 1 (ρ / ‖z‖) * ‖z‖ ≤ ρ / ‖z‖ * ‖z‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg z)
      _ = ρ := div_mul_cancel₀ ρ hpos.ne'

lemma norm_radialRetract_le_norm {ρ : ℝ} (hρ : 0 ≤ ρ) (z : E) : ‖radialRetract ρ z‖ ≤ ‖z‖ := by
  unfold radialRetract
  rw [norm_smul, Real.norm_of_nonneg (radialRetract_coeff_nonneg hρ z)]
  exact mul_le_of_le_one_left (norm_nonneg z) (min_le_left _ _)

/-- The variational inequality characterising the metric projection onto the ball:
`⟪z - R z, w - R z⟫ ≤ 0` for every `w` in the ball. -/
lemma inner_sub_radialRetract_le {ρ : ℝ} (hρ : 0 ≤ ρ) (z w : E) (hw : ‖w‖ ≤ ρ) :
    ⟪z - radialRetract ρ z, w - radialRetract ρ z⟫ ≤ 0 := by
  by_cases hz : ‖z‖ ≤ ρ
  · rw [radialRetract_of_norm_le hz, sub_self, inner_zero_left]
  rw [not_le] at hz
  have hpos : 0 < ‖z‖ := hρ.trans_lt hz
  set s := ρ / ‖z‖ with hs
  have hs1 : s < 1 := (div_lt_one hpos).2 hz
  have hs0 : 0 ≤ s := div_nonneg hρ hpos.le
  have hR : radialRetract ρ z = s • z := by
    unfold radialRetract; rw [min_eq_right hs1.le]
  have hsz : s * ‖z‖ = ρ := div_mul_cancel₀ ρ hpos.ne'
  rw [hR]
  have e1 : z - s • z = (1 - s) • z := by rw [sub_smul, one_smul]
  rw [e1, inner_smul_left, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  have hcs : ⟪z, w⟫ ≤ ‖z‖ * ‖w‖ := real_inner_le_norm z w
  have h1 : 0 ≤ 1 - s := by linarith
  have h2 : ⟪z, w⟫ - s * ‖z‖ ^ 2 ≤ 0 := by
    have : s * ‖z‖ ^ 2 = ρ * ‖z‖ := by rw [sq, ← mul_assoc, hsz]
    rw [this]; nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- **The radial retraction is `1`-Lipschitz** (non-expansive), as the metric projection onto a
closed convex set of a real inner product space. -/
lemma norm_radialRetract_sub_le {ρ : ℝ} (hρ : 0 ≤ ρ) (x y : E) :
    ‖radialRetract ρ x - radialRetract ρ y‖ ≤ ‖x - y‖ := by
  set a := radialRetract ρ x
  set b := radialRetract ρ y
  have hx := inner_sub_radialRetract_le hρ x b (norm_radialRetract_le hρ y)
  have hy := inner_sub_radialRetract_le hρ y a (norm_radialRetract_le hρ x)
  have hdec : x - y = (a - b) + ((x - a) - (y - b)) := by abel
  have hinner : 0 ≤ ⟪a - b, (x - a) - (y - b)⟫ := by
    have e1 : ⟪a - b, (x - a) - (y - b)⟫ = -⟪x - a, b - a⟫ - ⟪y - b, a - b⟫ := by
      rw [inner_sub_right, real_inner_comm (x - a), real_inner_comm (y - b)]
      have : b - a = -(a - b) := by abel
      rw [this, inner_neg_right]; ring
    rw [e1]; linarith
  have hsq : ‖a - b‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [hdec, norm_add_sq_real]
    nlinarith [sq_nonneg ‖(x - a) - (y - b)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

lemma ballRetract_of_mem {c x : E} {ρ : ℝ} (hx : ‖x - c‖ ≤ ρ) : ballRetract c ρ x = x := by
  rw [ballRetract_eq, radialRetract_of_norm_le hx]; abel

lemma norm_ballRetract_sub_center_le {ρ : ℝ} (hρ : 0 ≤ ρ) (c x : E) :
    ‖ballRetract c ρ x - c‖ ≤ ρ := by
  rw [ballRetract_eq, add_sub_cancel_left]; exact norm_radialRetract_le hρ _

lemma norm_ballRetract_sub_center_le_norm {ρ : ℝ} (hρ : 0 ≤ ρ) (c x : E) :
    ‖ballRetract c ρ x - c‖ ≤ ‖x - c‖ := by
  rw [ballRetract_eq, add_sub_cancel_left]; exact norm_radialRetract_le_norm hρ _

/-- **The retraction onto a ball is `1`-Lipschitz.** -/
lemma norm_ballRetract_sub_le {ρ : ℝ} (hρ : 0 ≤ ρ) (c x y : E) :
    ‖ballRetract c ρ x - ballRetract c ρ y‖ ≤ ‖x - y‖ := by
  rw [ballRetract_eq, ballRetract_eq, add_sub_add_left_eq_sub]
  calc _ ≤ ‖(x - c) - (y - c)‖ := norm_radialRetract_sub_le hρ _ _
    _ = ‖x - y‖ := by rw [sub_sub_sub_cancel_right]

/-- The retraction depends `2`-Lipschitz on the centre. -/
lemma norm_ballRetract_sub_center_sub_le {ρ : ℝ} (hρ : 0 ≤ ρ) (c d x : E) :
    ‖ballRetract c ρ x - ballRetract d ρ x‖ ≤ 2 * ‖c - d‖ := by
  rw [ballRetract_eq, ballRetract_eq]
  have h := norm_radialRetract_sub_le hρ (x - c) (x - d)
  have e : x - c - (x - d) = -(c - d) := by abel
  rw [e, norm_neg] at h
  have e2 : c + radialRetract ρ (x - c) - (d + radialRetract ρ (x - d))
      = (c - d) + (radialRetract ρ (x - c) - radialRetract ρ (x - d)) := by abel
  rw [e2]
  linarith [norm_add_le (c - d) (radialRetract ρ (x - c) - radialRetract ρ (x - d))]

lemma lipschitzWith_ballRetract_center {ρ : ℝ} (hρ : 0 ≤ ρ) (x : E) :
    LipschitzWith 2 (fun c : E => ballRetract c ρ x) :=
  LipschitzWith.of_dist_le_mul fun c d => by
    rw [dist_eq_norm, dist_eq_norm]
    exact_mod_cast norm_ballRetract_sub_center_sub_le hρ c d x

end Retraction

/-! ### The global extension of a field from a tube -/

section Extension

variable {F : ℝ → E → E} {A : ℝ → E} {a b ρ L B : ℝ}

lemma tubeExt_of_mem {t : ℝ} (ht : t ∈ Icc a b) (x : E) :
    tubeExt F A a b ρ t x = F t (ballRetract (A t) ρ x) := by
  simp [tubeExt, ht]

/-- The extension agrees with `F` on the tube. -/
lemma tubeExt_eq {t : ℝ} (ht : t ∈ Icc a b) {x : E} (hx : ‖x - A t‖ ≤ ρ) :
    tubeExt F A a b ρ t x = F t x := by
  rw [tubeExt_of_mem ht, ballRetract_of_mem hx]

/-- **The extension is globally Lipschitz with the tube constant.** -/
lemma isLipschitzField_tubeExt (hF : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) :
    IsLipschitzField (tubeExt F A a b ρ) L := by
  intro t x y
  by_cases ht : t ∈ Icc a b
  · rw [tubeExt_of_mem ht, tubeExt_of_mem ht]
    refine (hF t ht _ _ (norm_ballRetract_sub_center_le hρ _ _)
      (norm_ballRetract_sub_center_le hρ _ _)).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_ballRetract_sub_le hρ _ _ _) hL
  · simp only [tubeExt, ht, ite_false, sub_self, norm_zero]
    positivity

/-- **The extension is globally bounded by the tube bound.** -/
lemma isBoundedField_tubeExt (hF : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) :
    IsBoundedField (tubeExt F A a b ρ) B := by
  intro t x
  by_cases ht : t ∈ Icc a b
  · rw [tubeExt_of_mem ht]; exact hF t ht _ (norm_ballRetract_sub_center_le hρ _ _)
  · simp only [tubeExt, ht, ite_false, norm_zero]; exact hB

/-- **Time continuity of the extension**, if `F` is jointly continuous on the tube and `A` is
continuous on `[a, b]`. -/
lemma continuousOn_tubeExt (hFc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hA : ContinuousOn A (Icc a b)) (hρ : 0 ≤ ρ) (x : E) :
    ContinuousOn (fun t => tubeExt F A a b ρ t x) (Icc a b) := by
  have hr : ContinuousOn (fun t => ballRetract (A t) ρ x) (Icc a b) :=
    (lipschitzWith_ballRetract_center hρ x).continuous.comp_continuousOn hA
  have hcomp : ContinuousOn (fun t => Function.uncurry F (t, ballRetract (A t) ρ x)) (Icc a b) :=
    hFc.comp (continuousOn_id.prodMk hr) fun t ht =>
      ⟨ht, norm_ballRetract_sub_center_le hρ _ _⟩
  exact hcomp.congr fun t ht => tubeExt_of_mem ht x

end Extension

/-! ### Solutions inside the tube -/

section Congr

/-- A solution of `y' = f(t, y)` is a solution of `y' = g(t, y)` if `f` and `g` agree along the
trajectory. -/
lemma ODESolution.congr_field {f g : ℝ → E → E} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution f y a b) (h : ∀ t ∈ Ico a b, f t (y t) = g t (y t)) :
    ODESolution g y a b where
  cont := hy.cont
  deriv t ht := by rw [← h t ht]; exact hy.deriv t ht

variable {F : ℝ → E → E} {A : ℝ → E} {a b ρ : ℝ}

/-- **Solutions of the extended problem that stay in the tube solve the original problem**,
also for post-composed fields `Ψ ∘ F` (projected substeps `Q₀ F`, `P₁ Q₁ F`, ...), and
conversely. -/
lemma odeSolution_comp_tubeExt_iff (Ψ : E → E) {y : ℝ → E} {s s' : ℝ} (ha : a ≤ s)
    (hb : s' ≤ b) (hy : ∀ t ∈ Ico s s', ‖y t - A t‖ ≤ ρ) :
    ODESolution (fun t x => Ψ (tubeExt F A a b ρ t x)) y s s' ↔
      ODESolution (fun t x => Ψ (F t x)) y s s' := by
  have h : ∀ t ∈ Ico s s', Ψ (tubeExt F A a b ρ t (y t)) = Ψ (F t (y t)) := fun t ht => by
    rw [tubeExt_eq ⟨ha.trans ht.1, ht.2.le.trans hb⟩ (hy t ht)]
  exact ⟨fun hs => hs.congr_field h, fun hs => hs.congr_field fun t ht => (h t ht).symm⟩

/-- Unprojected version of `odeSolution_comp_tubeExt_iff`. -/
lemma odeSolution_tubeExt_iff {y : ℝ → E} {s s' : ℝ} (ha : a ≤ s) (hb : s' ≤ b)
    (hy : ∀ t ∈ Ico s s', ‖y t - A t‖ ≤ ρ) :
    ODESolution (tubeExt F A a b ρ) y s s' ↔ ODESolution F y s s' :=
  odeSolution_comp_tubeExt_iff (F := F) id ha hb hy

/-- The reference curve itself: if `A` solves `A' = F(t, A)`, it solves the extended problem. -/
lemma ODESolution.tubeExt_self (hA : ODESolution F A a b) (hρ : 0 ≤ ρ) :
    ODESolution (tubeExt F A a b ρ) A a b :=
  (odeSolution_tubeExt_iff le_rfl le_rfl fun t _ => by simpa using hρ).2 hA

end Congr

/-! ### The trapping lemma -/

section Trap

/-- **Trapping lemma (first-exit argument).**  Let `A` solve `A' = f(t, A)` on `[s, s₁]` with
`‖f(t, A t)‖ ≤ Ba`, and let `y` solve `y' = g(t, y)` where `g` is only known to be bounded by
`By` on the closed tube `‖x - A t‖ ≤ ρ`.  If `‖y s - A s‖ + (Ba + By) (s₁ - s) < ρ`, then `y`
never reaches the boundary of the tube: `‖y t - A t‖ < ρ` on `[s, s₁]`.

(Proof: fencing with the barrier `d + (Ba + By + η)(t - s)` for a small `η > 0`, Mathlib's
`image_norm_le_of_norm_deriv_right_lt_deriv_boundary'`.)  The strict inequality cannot be
relaxed in general: with a non-Lipschitz field outside the tube a solution starting on the
boundary may leave it. -/
theorem tube_trap {f g : ℝ → E → E} {A y : ℝ → E} {s s₁ ρ Ba By : ℝ}
    (hA : ODESolution f A s s₁) (hy : ODESolution g y s s₁) (hBa : 0 ≤ Ba) (hBy : 0 ≤ By)
    (hfA : ∀ t ∈ Ico s s₁, ‖f t (A t)‖ ≤ Ba)
    (hg : ∀ t ∈ Ico s s₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖g t x‖ ≤ By)
    (hlt : ‖y s - A s‖ + (Ba + By) * (s₁ - s) < ρ) :
    ∀ t ∈ Icc s s₁, ‖y t - A t‖ < ρ := by
  intro t ht
  have hss : s ≤ s₁ := ht.1.trans ht.2
  set d := ‖y s - A s‖ with hd
  set C := Ba + By with hCdef
  have hC : 0 ≤ C := add_nonneg hBa hBy
  have hpos : 0 < s₁ - s + 1 := by linarith
  set η := (ρ - d - C * (s₁ - s)) / (s₁ - s + 1) with hη
  have hη0 : 0 < η := div_pos (by linarith) hpos
  have hηmul : η * (s₁ - s + 1) = ρ - d - C * (s₁ - s) := div_mul_cancel₀ _ hpos.ne'
  have hβlt : ∀ x ∈ Icc s s₁, d + (C + η) * (x - s) < ρ := by
    intro x hx
    have h1 : (C + η) * (x - s) ≤ (C + η) * (s₁ - s) :=
      mul_le_mul_of_nonneg_left (by linarith [hx.2]) (by linarith)
    nlinarith
  have hfence := image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
    (f := fun t => y t - A t) (f' := fun t => g t (y t) - f t (A t))
    (B := fun t => d + (C + η) * (t - s)) (B' := fun _ => C + η)
    (hy.cont.sub hA.cont) (fun t ht => (hy.deriv t ht).sub (hA.deriv t ht))
    (by simp [hd]) (by fun_prop)
    (fun t _ => by
      have := ((hasDerivAt_id t).sub_const s).const_mul (C + η)
      simpa using (this.const_add d).hasDerivWithinAt)
    (fun t ht hEq => by
      have hin : ‖y t - A t‖ ≤ ρ := by
        rw [hEq]; exact (hβlt t (Ico_subset_Icc_self ht)).le
      calc ‖g t (y t) - f t (A t)‖ ≤ ‖g t (y t)‖ + ‖f t (A t)‖ := norm_sub_le _ _
        _ ≤ By + Ba := add_le_add (hg t ht _ hin) (hfA t ht)
        _ < C + η := by rw [hCdef]; linarith)
  exact (hfence ht).trans_lt (hβlt t ht)

/-- **Sharp form of the trapping lemma**: under the hypotheses of `tube_trap`,
`‖y t - A t‖ ≤ ‖y s - A s‖ + (Ba + By) (t - s)` on `[s, s₁]`. -/
theorem norm_sub_le_of_tube_trap {f g : ℝ → E → E} {A y : ℝ → E} {s s₁ ρ Ba By : ℝ}
    (hA : ODESolution f A s s₁) (hy : ODESolution g y s s₁) (hBa : 0 ≤ Ba) (hBy : 0 ≤ By)
    (hfA : ∀ t ∈ Ico s s₁, ‖f t (A t)‖ ≤ Ba)
    (hg : ∀ t ∈ Ico s s₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖g t x‖ ≤ By)
    (hlt : ‖y s - A s‖ + (Ba + By) * (s₁ - s) < ρ) :
    ∀ t ∈ Icc s s₁, ‖y t - A t‖ ≤ ‖y s - A s‖ + (Ba + By) * (t - s) := by
  have hin := tube_trap hA hy hBa hBy hfA hg hlt
  intro t ht
  have hyv := hy.norm_sub_le (B := By)
    (fun u hu => hg u hu _ (hin u (Ico_subset_Icc_self hu)).le) t ht
  have hAv := hA.norm_sub_le hfA t ht
  have hdec : y t - A t = (y t - y s) + (y s - A s) - (A t - A s) := by abel
  rw [hdec]
  calc _ ≤ ‖(y t - y s) + (y s - A s)‖ + ‖A t - A s‖ := norm_sub_le _ _
    _ ≤ ‖y t - y s‖ + ‖y s - A s‖ + ‖A t - A s‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by nlinarith

/-- Speed bound inside the tube: a trajectory of `g` that stays in the tube, where `‖g‖ ≤ By`,
moves at most `By (t - s)`. -/
lemma ODESolution.norm_sub_start_le_of_tube {g : ℝ → E → E} {A y : ℝ → E} {s s₁ ρ By : ℝ}
    (hy : ODESolution g y s s₁) (hg : ∀ t ∈ Ico s s₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖g t x‖ ≤ By)
    (hin : ∀ t ∈ Icc s s₁, ‖y t - A t‖ < ρ) : ∀ t ∈ Icc s s₁, ‖y t - y s‖ ≤ By * (t - s) :=
  hy.norm_sub_le fun u hu => hg u hu _ (hin u (Ico_subset_Icc_self hu)).le

end Trap

/-! ### Bootstrap -/

section Bootstrap

/-- **The bootstrap pattern** (generic form, reusable for every integrator).  If for every
`m ≤ N` the error bound `e m ≤ M` follows from the bounds `e k ≤ M` at all earlier steps
`k < m` (typically: the earlier bounds keep all substeps of steps `k < m` in the tube where the
local constants hold, so the *global* error theorem for the extended field applies to the first
`m` steps), then `e n ≤ M` for all `n ≤ N`. -/
theorem bootstrap_of_global {N : ℕ} {e : ℕ → ℝ} {M : ℝ}
    (hglob : ∀ m ≤ N, (∀ k < m, e k ≤ M) → e m ≤ M) : ∀ n ≤ N, e n ≤ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact fun hn => hglob n hn fun k hk => ih k hk (hk.le.trans hn)

variable {F : ℝ → E → E} {A : ℝ → E} {a b ρ B ε : ℝ}

omit [InnerProductSpace ℝ E] in
lemma IsBoundedOnTube.along {s s₁ : ℝ} (hFB : IsBoundedOnTube F A a b ρ B) (hρ : 0 ≤ ρ)
    (ha : a ≤ s) (hb : s₁ ≤ b) : ∀ t ∈ Ico s s₁, ‖F t (A t)‖ ≤ B := fun t ht =>
  hFB t ⟨ha.trans ht.1, ht.2.le.trans hb⟩ _ (by simpa using hρ)

omit [InnerProductSpace ℝ E] in
lemma IsBoundedOnTube.comp_proj {s s₁ : ℝ} (hFB : IsBoundedOnTube F A a b ρ B) (ha : a ≤ s)
    (hb : s₁ ≤ b) (Ψ : E → E) (hΨ : ∀ x, ‖Ψ x‖ ≤ ‖x‖) :
    ∀ t ∈ Ico s s₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖Ψ (F t x)‖ ≤ B := fun t ht x hx =>
  (hΨ _).trans (hFB t ⟨ha.trans ht.1, ht.2.le.trans hb⟩ x hx)

/-- An exact flow `Φ` of the original problem started `ρ - 2 B h`-close to `A` stays in the tube
and is a flow of the extended problem. -/
lemma ODESolution.tubeExt_of_near {Φ : ℝ → E} {s s₁ h : ℝ} (hΦ : ODESolution F Φ s s₁)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (hh : 0 ≤ h) (ha : a ≤ s) (hb : s₁ ≤ b)
    (ht₁ : s₁ = s + h) (hA : ODESolution F A s s₁) (hsmall : ‖Φ s - A s‖ + 2 * B * h < ρ) :
    ODESolution (tubeExt F A a b ρ) Φ s s₁ := by
  have hρ : 0 ≤ ρ := by nlinarith [norm_nonneg (Φ s - A s)]
  have hin := tube_trap hA hΦ hB hB (hFB.along hρ ha hb) (hFB.comp_proj ha hb id fun _ => le_rfl)
    (by rw [ht₁]; linarith)
  exact (odeSolution_tubeExt_iff ha hb fun t ht => (hin t (Ico_subset_Icc_self ht)).le).2 hΦ

/-- **One BUG step in the tube is a step of the extended problem.**  If the step starts at a
value `Y₀` with `‖Y₀ - A s‖ + 4 B h < ρ`, then all three substeps (K, L and the Galerkin
S-step, which starts at `P₁ Q₁ Y₀`) stay strictly inside the tube, the normal-component points
`YK s₁`, `YL s₁` lie in the tube at all times of the step, and the step is an `IsBUGStep` for the
extended field `tubeExt F A a b ρ`. -/
theorem IsBUGStep.tubeExt {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E} {s s₁ h : ℝ}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ s s₁ Y₀ YK YL YS) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hh : 0 ≤ h) (ha : a ≤ s) (hb : s₁ ≤ b) (ht₁ : s₁ = s + h)
    (hA : ODESolution F A s s₁) (hsmall : ‖Y₀ - A s‖ + 4 * B * h < ρ) :
    IsBUGStep (tubeExt F A a b ρ) ε P₀ Q₀ P₁ Q₁ s s₁ Y₀ YK YL YS := by
  have hd := norm_nonneg (Y₀ - A s)
  have hρ : 0 ≤ ρ := by nlinarith
  have hss : s ≤ s₁ := by linarith
  have hFA := hFB.along hρ ha hb
  have hlen : s₁ - s = h := by linarith
  -- the K- and L-substeps stay in the tube
  have hKin := tube_trap hA hs.kSol hB hB hFA (hFB.comp_proj ha hb _ hs.projQ₀.norm_le)
    (by rw [hs.kStart, hlen]; nlinarith)
  have hLin := tube_trap hA hs.lSol hB hB hFA (hFB.comp_proj ha hb _ hs.projP₀.norm_le)
    (by rw [hs.lStart, hlen]; nlinarith)
  have hKv := hs.kSol.norm_sub_start_le_of_tube (hFB.comp_proj ha hb _ hs.projQ₀.norm_le) hKin
    s₁ ⟨hss, le_rfl⟩
  have hLv := hs.lSol.norm_sub_start_le_of_tube (hFB.comp_proj ha hb _ hs.projP₀.norm_le) hLin
    s₁ ⟨hss, le_rfl⟩
  rw [hs.kStart, hlen] at hKv
  rw [hs.lStart, hlen] at hLv
  -- the points `YK s₁`, `YL s₁` lie in the tube at all times of the step
  have hpt : ∀ z : E, ‖z - Y₀‖ ≤ B * h → ∀ t ∈ Icc s s₁, ‖z - A t‖ ≤ ρ := by
    intro z hz t ht
    have hAt := hA.norm_sub_le hFA t ht
    have hdec : z - A t = (z - Y₀) + (Y₀ - A s) - (A t - A s) := by abel
    rw [hdec]
    have : B * (t - s) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB
    calc _ ≤ ‖(z - Y₀) + (Y₀ - A s)‖ + ‖A t - A s‖ := norm_sub_le _ _
      _ ≤ ‖z - Y₀‖ + ‖Y₀ - A s‖ + ‖A t - A s‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ρ := by nlinarith
  have hsub : ∀ t ∈ Icc s s₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  -- the Galerkin substep starts `2 B h`-close to `Y₀`
  have hS₀ : ‖P₁ (Q₁ Y₀) - A s‖ ≤ ‖Y₀ - A s‖ + 2 * B * h := by
    have hcapP : ‖(1 - P₁) Y₀‖ ≤ B * h := by
      have e : (1 - P₁) Y₀ = (Y₀ - YK s₁) - P₁ (Y₀ - YK s₁) := by
        rw [map_sub, hs.kCap]; simp
      rw [e]; refine (hs.projP₁.norm_sub_le _).trans ?_
      rw [norm_sub_rev]; exact hKv
    have hcapQ : ‖(1 - Q₁) Y₀‖ ≤ B * h := by
      have e : (1 - Q₁) Y₀ = (Y₀ - YL s₁) - Q₁ (Y₀ - YL s₁) := by
        rw [map_sub, hs.lCap]; simp
      rw [e]; refine (hs.projQ₁.norm_sub_le _).trans ?_
      rw [norm_sub_rev]; exact hLv
    have h3 := norm_sub_apply_apply_le (Q := Q₁) hs.projP₁ Y₀
    have hdec : P₁ (Q₁ Y₀) - A s = (Y₀ - A s) - (Y₀ - P₁ (Q₁ Y₀)) := by abel
    rw [hdec]
    calc _ ≤ ‖Y₀ - A s‖ + ‖Y₀ - P₁ (Q₁ Y₀)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hPQ : ∀ x, ‖P₁ (Q₁ x)‖ ≤ ‖x‖ := fun x =>
    (hs.projP₁.norm_le _).trans (hs.projQ₁.norm_le _)
  have hSin := tube_trap hA hs.sSol hB hB hFA (hFB.comp_proj ha hb (fun x => P₁ (Q₁ x)) hPQ)
    (by rw [hs.sStart, hlen]; nlinarith)
  exact
    { projP₀ := hs.projP₀
      projQ₀ := hs.projQ₀
      projP₁ := hs.projP₁
      projQ₁ := hs.projQ₁
      comm₁ := hs.comm₁
      kSol := (odeSolution_comp_tubeExt_iff (fun x => Q₀ x) ha hb
        fun t ht => (hKin t (Ico_subset_Icc_self ht)).le).2 hs.kSol
      kStart := hs.kStart
      kCap := hs.kCap
      kNormal := fun t ht => by
        rw [tubeExt_eq (hsub t ht) (hpt _ hKv t ht)]
        exact hs.kNormal t ht
      lSol := (odeSolution_comp_tubeExt_iff (fun x => P₀ x) ha hb
        fun t ht => (hLin t (Ico_subset_Icc_self ht)).le).2 hs.lSol
      lStart := hs.lStart
      lCap := hs.lCap
      lNormal := fun t ht => by
        rw [tubeExt_eq (hsub t ht) (hpt _ hLv t ht)]
        exact hs.lNormal t ht
      sSol := (odeSolution_comp_tubeExt_iff (fun x => P₁ (Q₁ x)) ha hb
        fun t ht => (hSin t (Ico_subset_Icc_self ht)).le).2 hs.sSol
      sStart := hs.sStart }

/-- The constant `c₀ δ + c₁ ε + c₂ h` of the robust global error bound of the BUG integrator
(`bug_global_error_le`): `c₀ = e^{L T}`, `c₁ = T e^{L T} bugC₁ L H`,
`c₂ = T e^{L T} bugC₂ L B H`. -/
noncomputable def bugGlobalBound (L B H T δ ε h : ℝ) : ℝ :=
  Real.exp (L * T) * δ + T * Real.exp (L * T) * bugC₁ L H * ε
    + T * Real.exp (L * T) * bugC₂ L B H * h

lemma bugGlobalBound_nonneg {L B H T δ ε h : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hh : 0 ≤ h) : 0 ≤ bugGlobalBound L B H T δ ε h := by
  unfold bugGlobalBound
  have := bugC₁_nonneg hL hH
  have := bugC₂_nonneg hL hB hH
  positivity

/-- **Robust global error bound of the BUG integrator under tube-localised hypotheses**
(resolves OP-EX-01 for the BUG integrator; Ceruti–Lubich, arXiv 2010.02022, Theorem 4, with the
standing global hypotheses replaced by local ones).

Let `F` be `L`-Lipschitz and bounded by `B` **only on the tube** of radius `ρ` around the exact
solution `A` on `[t₀, t₀ + N h]`.  Let `Y n` be the BUG approximations (all substeps are
`IsBUGStep`s for the *original* field `F`; the normal-component bound `ε` is only required at
the points `YK n tₙ₊₁`, `YL n tₙ₊₁`), and `Φ n` exact flows of `F` from `Y n`.  If the robust
global bound `M = c₀ δ + c₁ ε + c₂ h` of `bug_global_error_le` satisfies the smallness condition

    M + 4 B h < ρ,

then the bound holds for all `n ≤ N` with the **same constants**:
`‖Y n - A tₙ‖ ≤ c₀ δ + c₁ ε + c₂ h`.

(Proof: extend `F` by `tubeExt`, which is globally `L`-Lipschitz and `B`-bounded and agrees
with `F` on the tube; by `bootstrap_of_global`, the bound at the steps `k < m` keeps every substep
of these steps in the tube (`IsBUGStep.tubeExt`), so `bug_global_error_le` for the extended field
gives the bound at step `m`.)  The margin `4 B h` (instead of `2 B h` in the formulation of
OP-EX-01) accounts for the Galerkin substep, which starts at `P₁ Q₁ Y n`, up to `2 B h` away from
`Y n`. -/
theorem bug_global_error_le_of_tube {L H t₀ h : ℝ} {N : ℕ}
    (hFL : IsLipschitzOnTube F A t₀ (t₀ + N * h) ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ (t₀ + N * h) ρ B) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsBUGStep F ε (P n) (Q n) (P (n + 1)) (Q (n + 1)) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ)
    (hNT : N * h ≤ T) (hsmall : bugGlobalBound L B H T δ ε h + 4 * B * h < ρ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ bugGlobalBound L B H T δ ε h := by
  set M := bugGlobalBound L B H T δ ε h with hM
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNT
  have hM0 : 0 ≤ M := bugGlobalBound_nonneg hL hB (hh.trans hhH) hT
    ((norm_nonneg _).trans hδ) hε hh
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
  have hmN : (m : ℝ) * h ≤ N * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hh
  have hAn : ∀ n < m, ODESolution F A (t₀ + n * h) (t₀ + (n + 1) * h) := fun n hn =>
    hA.mono (hgrid n (hn.trans_le hm)).1 (hgrid n (hn.trans_le hm)).2
  have hnear : ∀ n < m, ‖Y n - A (t₀ + n * h)‖ + 4 * B * h < ρ := fun n hn => by
    have := hIH n hn; linarith
  have key := bug_global_error_le (F := G) hGL hL hGB hε hh hhH (N := m) (A := A)
    (hAG.mono le_rfl (by linarith)) (P := P) (Q := Q) (Y := Y) (YK := YK) (YL := YL) (YS := YS)
    (Φ := Φ)
    (fun n hn => (hstep n (hn.trans_le hm)).tubeExt hFB hB hh (hgrid n (hn.trans_le hm)).1
      (hgrid n (hn.trans_le hm)).2 (by ring) (hAn n hn) (hnear n hn))
    (fun n hn => hY n (hn.trans_le hm))
    (fun n hn => (hΦ n (hn.trans_le hm)).tubeExt_of_near hFB hB hh (hgrid n (hn.trans_le hm)).1
      (hgrid n (hn.trans_le hm)).2 (by ring) (hAn n hn)
      (by rw [hΦ₀ n (hn.trans_le hm)]; nlinarith [hnear n hn]))
    (fun n hn => hΦ₀ n (hn.trans_le hm)) hδ m le_rfl (hmN.trans hNT)
  exact key

end Bootstrap

/-! ### Continuation: a priori bounds give global solutions of the original problem -/

section Continuation

omit [InnerProductSpace ℝ E] in
/-- Joint continuity of a field that is Lipschitz in the state uniformly in time and continuous
in time. -/
lemma IsLipschitzField.continuousOn_uncurry {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) {S : Set ℝ} (hc : ∀ x, ContinuousOn (fun t => F t x) S) :
    ContinuousOn (Function.uncurry F) (S ×ˢ univ) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith' (Function.uncurry F) ⟨L, hL⟩
    (fun t _ => (hF.lipschitzWith hL t).lipschitzOnWith) (fun x _ => hc x)

variable [CompleteSpace E] {F : ℝ → E → E} {A : ℝ → E} {a b ρ L B : ℝ}

/-- **Global existence for the extended problem.**  Under the tube hypotheses (and joint
continuity of `F` on the tube), the extended problem `y' = tubeExt F A a b ρ (t, y)` has a
solution on all of `[a, b]` for every initial value. -/
theorem exists_ODESolution_tubeExt (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hFc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ)) (hAc : ContinuousOn A (Icc a b))
    (hab : a ≤ b) (y₀ : E) : ∃ y, ODESolution (tubeExt F A a b ρ) y a b ∧ y a = y₀ :=
  exists_ODESolution_of_continuousOn (isLipschitzField_tubeExt hFL hL hρ)
    (isBoundedField_tubeExt hFB hB hρ) (continuousOn_tubeExt hFc hAc hρ) hab y₀

/-- **Continuation principle (abstract form of OP-EX-04 (b)).**  Let `F` be Lipschitz and
bounded only on the tube of radius `ρ` around a continuous curve `A` (not necessarily a
solution).  If an *a priori bound* keeps every solution of the extended problem with initial
value `y₀` inside the tube, then the original problem `y' = F(t, y)`, `y a = y₀` has a solution
on the **whole** interval `[a, b]`; no local existence/continuation argument is needed. -/
theorem exists_ODESolution_of_apriori (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hFc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ)) (hAc : ContinuousOn A (Icc a b))
    (hab : a ≤ b) (y₀ : E)
    (hapriori : ∀ y, ODESolution (tubeExt F A a b ρ) y a b → y a = y₀ →
      ∀ t ∈ Ico a b, ‖y t - A t‖ ≤ ρ) :
    ∃ y, ODESolution F y a b ∧ y a = y₀ := by
  obtain ⟨y, hy, hy0⟩ := exists_ODESolution_tubeExt hFL hL hFB hB hρ hFc hAc hab y₀
  exact ⟨y, (odeSolution_tubeExt_iff le_rfl le_rfl (hapriori y hy hy0)).1 hy, hy0⟩

omit [CompleteSpace E] in
/-- **Uniqueness inside the tube**: two solutions of the original problem that stay in the tube
(where `F` is Lipschitz) and agree initially coincide on `[a, b]`. -/
theorem eqOn_of_tube (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    {y z : ℝ → E} (hy : ODESolution F y a b) (hz : ODESolution F z a b)
    (hyin : ∀ t ∈ Ico a b, ‖y t - A t‖ ≤ ρ) (hzin : ∀ t ∈ Ico a b, ‖z t - A t‖ ≤ ρ)
    (h0 : y a = z a) : EqOn y z (Icc a b) :=
  ((odeSolution_tubeExt_iff le_rfl le_rfl hyin).2 hy).eqOn
    ((odeSolution_tubeExt_iff le_rfl le_rfl hzin).2 hz) (isLipschitzField_tubeExt hFL hL hρ) hL h0

/-- **Global existence near a solution (stability of existence under perturbation of the
initial value).**  Let `A` solve `A' = F(t, A)` on `[a, b]`, and let `F` be Lipschitz and
bounded by `B` only on the tube of radius `ρ` around `A`.  For every `y₀` with
`‖y₀ - A a‖ + 2 B (b - a) < ρ` there is a solution with `y a = y₀` on all of `[a, b]`, and it
satisfies `‖y t - A t‖ ≤ ‖y₀ - A a‖ + 2 B (t - a)`. -/
theorem exists_ODESolution_near (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (hFc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ)) (hA : ODESolution F A a b)
    (hab : a ≤ b) (y₀ : E) (hsmall : ‖y₀ - A a‖ + 2 * B * (b - a) < ρ) :
    ∃ y, ODESolution F y a b ∧ y a = y₀ ∧
      ∀ t ∈ Icc a b, ‖y t - A t‖ ≤ ‖y₀ - A a‖ + 2 * B * (t - a) := by
  have hρ : 0 ≤ ρ := by nlinarith [norm_nonneg (y₀ - A a)]
  have hGB := isBoundedField_tubeExt hFB hB hρ
  have hAG := hA.tubeExt_self hρ
  have htrap : ∀ y, ODESolution (tubeExt F A a b ρ) y a b → y a = y₀ →
      ∀ t ∈ Icc a b, ‖y t - A t‖ < ρ := fun y hy hy0 =>
    tube_trap hAG hy hB hB (fun t _ => hGB t _) (fun t _ x _ => hGB t x)
      (by rw [hy0]; linarith)
  obtain ⟨y, hy, hy0⟩ := exists_ODESolution_tubeExt hFL hL hFB hB hρ hFc hA.cont hab y₀
  have hin := htrap y hy hy0
  refine ⟨y, (odeSolution_tubeExt_iff le_rfl le_rfl fun t ht =>
    (hin t (Ico_subset_Icc_self ht)).le).1 hy, hy0, fun t ht => ?_⟩
  have := norm_sub_le_of_tube_trap hAG hy hB hB (fun t _ => hGB t _) (fun t _ x _ => hGB t x)
    (by rw [hy0]; linarith) t ht
  rw [hy0] at this
  linarith

/-- **Global existence for globally Lipschitz fields of linear growth** (no boundedness
assumption).  If `F` is `L`-Lipschitz in the state (uniformly in time), `‖F t 0‖ ≤ K` and `F` is
continuous in time on `[a, b]`, then `y' = F(t, y)`, `y a = y₀` has a solution on `[a, b]`.

This removes the boundedness hypothesis of `exists_ODESolution` (Mathlib's Picard–Lindelöf needs
a bounded field).  Proof: continuation principle `exists_ODESolution_of_apriori` with the tube
of radius `R = e^{L (b-a)} (‖y₀‖ + K (b - a))` around `0`, on which `‖F‖ ≤ K + L R`; the a priori
bound `‖y t‖ ≤ R` for the extended problem is Grönwall's inequality, since the retraction does
not increase norms. -/
theorem exists_ODESolution_of_linearGrowth {K : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hK : ∀ t ∈ Icc a b, ‖F t 0‖ ≤ K) (hc : ∀ x, ContinuousOn (fun t => F t x) (Icc a b))
    (hab : a ≤ b) (y₀ : E) : ∃ y, ODESolution F y a b ∧ y a = y₀ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK a ⟨le_rfl, hab⟩)
  set R := Real.exp (L * (b - a)) * (‖y₀‖ + K * (b - a)) with hR
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have hR0 : 0 ≤ R := by positivity
  have hgrowth : ∀ t ∈ Icc a b, ∀ x, ‖F t x‖ ≤ K + L * ‖x‖ := fun t ht x => by
    have := hF t x 0
    rw [sub_zero] at this
    linarith [norm_sub_norm_le (F t x) (F t 0), hK t ht]
  have hFB : IsBoundedOnTube F (fun _ => 0) a b R (K + L * R) := fun t ht x hx => by
    rw [sub_zero] at hx
    exact (hgrowth t ht x).trans (by gcongr)
  refine exists_ODESolution_of_apriori (hF.isLipschitzOnTube _ a b R) hL hFB (by positivity) hR0
    ((hF.continuousOn_uncurry hL hc).mono fun p hp => ⟨hp.1, mem_univ _⟩) continuousOn_const
    hab y₀ fun y hy hy0 t ht => ?_
  have hbound : ∀ s ∈ Ico a b, ‖tubeExt F (fun _ => 0) a b R s (y s)‖ ≤ L * ‖y s‖ + K := by
    intro s hs
    have hsI : s ∈ Icc a b := Ico_subset_Icc_self hs
    rw [tubeExt_of_mem hsI]
    have hr := norm_ballRetract_sub_center_le_norm hR0 (0 : E) (y s)
    simp only [sub_zero] at hr
    have := hgrowth s hsI (ballRetract 0 R (y s))
    nlinarith
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hy.cont hy.deriv
    (by rw [hy0]) hbound t (Ico_subset_Icc_self ht)
  have hexp := gronwallBound_le_exp_mul (δ := ‖y₀‖) (x := t - a) hL hK0
  have hmono : Real.exp (L * (t - a)) * (‖y₀‖ + K * (t - a)) ≤ R := by
    rw [hR]
    have h1 : t - a ≤ b - a := by linarith [ht.2]
    have h2 : 0 ≤ t - a := by linarith [ht.1]
    gcongr
  rw [sub_zero]
  linarith

/-- **Existence and uniqueness for globally Lipschitz fields of linear growth.** -/
theorem existsUnique_ODESolution_of_linearGrowth {K : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hK : ∀ t ∈ Icc a b, ‖F t 0‖ ≤ K)
    (hc : ∀ x, ContinuousOn (fun t => F t x) (Icc a b)) (hab : a ≤ b) (y₀ : E) :
    ∃ y, (ODESolution F y a b ∧ y a = y₀) ∧
      ∀ z, ODESolution F z a b → z a = y₀ → EqOn z y (Icc a b) := by
  obtain ⟨y, hy, hy0⟩ := exists_ODESolution_of_linearGrowth hF hL hK hc hab y₀
  exact ⟨y, ⟨hy, hy0⟩, fun z hz hz0 => hz.eqOn hy hF hL (hz0.trans hy0.symm)⟩

end Continuation

/-! ### Reduced-order models with a moving basis -/

section ROM

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-- **Lipschitz constant of the reduced flux with a moving basis** (Billaud-Friess–Nouy,
arXiv 1604.05706, eq. (9) and Remark 1, abstract form).
For a full field `f` that is `L`-Lipschitz, a basis map `V t : E' →L E` and its transpose
`W t : E →L E'` with `‖V t‖, ‖W t‖ ≤ 1` (orthonormal basis), and the moving-basis term
`M t = Vᵀ(t) V'(t)` with `‖M t‖ ≤ c`, the reduced flux
`f_r(t, α) = W t (f t (V t α)) - M t α` is `(L + c)`-Lipschitz. -/
theorem isLipschitzField_reducedFlux {f : ℝ → E → E} {L c : ℝ} (hf : IsLipschitzField f L)
    (hL : 0 ≤ L) (V : ℝ → E' →L[ℝ] E) (W : ℝ → E →L[ℝ] E') (M : ℝ → E' →L[ℝ] E')
    (hV : ∀ t, ‖V t‖ ≤ 1) (hW : ∀ t, ‖W t‖ ≤ 1) (hM : ∀ t, ‖M t‖ ≤ c) :
    IsLipschitzField (fun t α => W t (f t (V t α)) - M t α) (L + c) := by
  intro t α β
  have h1 : ‖W t (f t (V t α)) - W t (f t (V t β))‖ ≤ L * ‖α - β‖ := by
    rw [← map_sub]
    calc _ ≤ ‖W t‖ * ‖f t (V t α) - f t (V t β)‖ := (W t).le_opNorm _
      _ ≤ 1 * (L * ‖V t α - V t β‖) := by
          gcongr
          · exact hW t
          · exact hf t _ _
      _ ≤ 1 * (L * (‖V t‖ * ‖α - β‖)) := by
          rw [← map_sub]; gcongr; exact (V t).le_opNorm _
      _ ≤ 1 * (L * (1 * ‖α - β‖)) := by gcongr; exact hV t
      _ = L * ‖α - β‖ := by ring
  have h2 : ‖M t α - M t β‖ ≤ c * ‖α - β‖ := by
    rw [← map_sub]
    exact ((M t).le_opNorm _).trans (by gcongr; exact hM t)
  have hdec : W t (f t (V t α)) - M t α - (W t (f t (V t β)) - M t β)
      = (W t (f t (V t α)) - W t (f t (V t β))) - (M t α - M t β) := by abel
  rw [hdec]
  calc _ ≤ ‖W t (f t (V t α)) - W t (f t (V t β))‖ + ‖M t α - M t β‖ := norm_sub_le _ _
    _ ≤ L * ‖α - β‖ + c * ‖α - β‖ := add_le_add h1 h2
    _ = (L + c) * ‖α - β‖ := by ring

/-- **Well-posedness of the reduced dynamical system** (Billaud-Friess–Nouy, arXiv 1604.05706,
Remark 1).  Under the hypotheses of `isLipschitzField_reducedFlux`, if moreover `f` is
continuous in time, `‖f t 0‖ ≤ K` on `[a, b]`, and `V`, `W`, `M` are continuous on `[a, b]`
(e.g. `V` continuously differentiable), then the reduced system `α' = f_r(t, α)`,
`α a = α₀`, has a **unique** solution on the whole interval `[a, b]`.

The reduced flux is unbounded (it grows linearly in `α`), so this uses
`exists_ODESolution_of_linearGrowth` rather than the bounded-field existence theorem. -/
theorem existsUnique_reducedFlux [CompleteSpace E'] {f : ℝ → E → E} {L c K a b : ℝ}
    (hf : IsLipschitzField f L) (hL : 0 ≤ L) (V : ℝ → E' →L[ℝ] E) (W : ℝ → E →L[ℝ] E')
    (M : ℝ → E' →L[ℝ] E') (hV : ∀ t, ‖V t‖ ≤ 1) (hW : ∀ t, ‖W t‖ ≤ 1) (hM : ∀ t, ‖M t‖ ≤ c)
    (hc : 0 ≤ c) (hK : ∀ t ∈ Icc a b, ‖f t 0‖ ≤ K)
    (hfc : ∀ x, ContinuousOn (fun t => f t x) (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hWc : ContinuousOn W (Icc a b)) (hMc : ContinuousOn M (Icc a b)) (hab : a ≤ b) (α₀ : E') :
    ∃ α : ℝ → E', (ODESolution (fun t α => W t (f t (V t α)) - M t α) α a b ∧ α a = α₀) ∧
      ∀ β, ODESolution (fun t α => W t (f t (V t α)) - M t α) β a b → β a = α₀ →
        EqOn β α (Icc a b) := by
  have hLip := isLipschitzField_reducedFlux hf hL V W M hV hW hM
  have hjoint := hf.continuousOn_uncurry hL hfc
  refine existsUnique_ODESolution_of_linearGrowth (E := E') hLip (by positivity)
    (K := K) (fun t ht => ?_) (fun x => ?_) hab α₀
  · simp only [map_zero, sub_zero]
    exact ((W t).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hW t)).trans
      (hK t ht))
  · have hin : ContinuousOn (fun t => f t (V t x)) (Icc a b) :=
      hjoint.comp (f := fun t => (t, V t x)) (continuousOn_id.prodMk
        (hVc.clm_apply continuousOn_const)) fun t ht => ⟨ht, mem_univ _⟩
    exact (hWc.clm_apply hin).sub (hMc.clm_apply continuousOn_const)

end ROM

/-! ### Counterexample: DLRA solutions need not exist globally on the manifold -/

section Counterexample

open scoped LeanDLRA.Frobenius Matrix

/-- The constant field `Ȧ = diag(0, -1)` of `A(t) = diag(1, 1 - t)`. -/
def diagDeriv : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -1]

lemma odeSolution_diag (T : ℝ) :
    ODESolution (fun _ _ => diagDeriv) (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • diagDeriv)
      0 T := by
  refine ⟨by fun_prop, fun t _ => ?_⟩
  have := ((hasDerivAt_id t).smul_const diagDeriv).const_add (1 : Matrix (Fin 2) (Fin 2) ℝ)
  simpa using this.hasDerivWithinAt

lemma det_one_add_smul_diagDeriv (t : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) + t • diagDeriv).det = 1 - t := by
  simp [diagDeriv, Matrix.det_fin_two]
  ring

/-- **Global existence on the low-rank manifold fails in general** (the counterexample in
OP-EX-04).  Take `r = n = 2`, so that the rank-`2` manifold `M₂` is the open set of invertible
`2 × 2` matrices, the tangent projector is the identity and the DLRA equation `Ẏ = P(Y) F(t, Y)`
is the full equation `Ẏ = F(t, Y)`; take `F = Ȧ` with `A(t) = diag(1, 1 - t)`.  For `T ≥ 1`
there is **no** solution on `[0, T]` with `Y 0 = I` that stays in `M₂`: the unique solution is
`A`, and `det A(1) = 0` (`σ₂(A(t)) = 1 - t → 0`, the blow-up alternative). -/
theorem not_exists_odeSolution_mem_manifold {T : ℝ} (hT : 1 ≤ T) :
    ¬ ∃ Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ, ODESolution (fun _ _ => diagDeriv) Y 0 T ∧ Y 0 = 1 ∧
      ∀ t ∈ Icc 0 T, (Y t).det ≠ 0 := by
  rintro ⟨Y, hY, hY0, hdet⟩
  have heq := hY.eqOn (odeSolution_diag T) (L := 0) (fun _ _ _ => by simp) le_rfl
    (by simp [hY0])
  have h1 : (1 : ℝ) ∈ Icc 0 T := ⟨zero_le_one, hT⟩
  apply hdet 1 h1
  rw [heq h1, det_one_add_smul_diagDeriv, sub_self]

/-- Before `t = 1` the solution exists on the manifold: for `T < 1`, `A(t) = diag(1, 1 - t)`
solves the problem on `[0, T]` and stays invertible. -/
theorem exists_odeSolution_mem_manifold {T : ℝ} (hT : T < 1) :
    ∃ Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ, ODESolution (fun _ _ => diagDeriv) Y 0 T ∧ Y 0 = 1 ∧
      ∀ t ∈ Icc 0 T, (Y t).det ≠ 0 :=
  ⟨_, odeSolution_diag T, by simp, fun t ht => by
    rw [det_one_add_smul_diagDeriv]; linarith [ht.2]⟩

end Counterexample

/-! ### The cubic nonlinearity -/

section Cubic

/-- **Local Lipschitz estimate of the cubic nonlinearity** `G(u) = |u|² u` in any real normed
space (in particular `ℝ` and `ℂ`):
`‖|u|² u - |v|² v‖ ≤ (|u|² + |u| |v| + |v|²) ‖u - v‖`. -/
theorem norm_cubic_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (u v : V) :
    ‖‖u‖ ^ 2 • u - ‖v‖ ^ 2 • v‖ ≤ (‖u‖ ^ 2 + ‖u‖ * ‖v‖ + ‖v‖ ^ 2) * ‖u - v‖ := by
  have hdec : ‖u‖ ^ 2 • u - ‖v‖ ^ 2 • v = ‖u‖ ^ 2 • (u - v) + (‖u‖ ^ 2 - ‖v‖ ^ 2) • v := by
    rw [smul_sub, sub_smul]; abel
  have hdiff : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
  have hsq : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
    rw [show ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ + ‖v‖) * (‖u‖ - ‖v‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u‖ + ‖v‖)]
    exact mul_le_mul_of_nonneg_left hdiff (by positivity)
  rw [hdec]
  calc _ ≤ ‖‖u‖ ^ 2 • (u - v)‖ + ‖(‖u‖ ^ 2 - ‖v‖ ^ 2) • v‖ := norm_add_le _ _
    _ = ‖u‖ ^ 2 * ‖u - v‖ + |‖u‖ ^ 2 - ‖v‖ ^ 2| * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u‖ ^ 2)]
    _ ≤ ‖u‖ ^ 2 * ‖u - v‖ + (‖u‖ + ‖v‖) * ‖u - v‖ * ‖v‖ := by gcongr
    _ = _ := by ring

/-- **arXiv 2010.05249, Property 1(b), scalar core** (OP-OT-10 (a)):
`‖|u|² u - |v|² v‖ ≤ 3 max(|u|, |v|)² ‖u - v‖`. -/
theorem norm_cubic_sub_le_max {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u v : V) :
    ‖‖u‖ ^ 2 • u - ‖v‖ ^ 2 • v‖ ≤ 3 * max ‖u‖ ‖v‖ ^ 2 * ‖u - v‖ := by
  refine (norm_cubic_sub_le u v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hu := le_max_left ‖u‖ ‖v‖
  have hv := le_max_right ‖u‖ ‖v‖
  have h0 := norm_nonneg u
  have h1 := norm_nonneg v
  nlinarith [mul_le_mul hu hv h1 (h0.trans hu)]

/-- The complex cubic nonlinearity `u ↦ |u|² u` of the (fractional) Ginzburg–Landau and
nonlinear Schrödinger equations satisfies `||u|² u - |v|² v| ≤ 3 max(|u|, |v|)² |u - v|`
(arXiv 2010.05249, Property 1(b), entrywise). -/
theorem norm_complex_cubic_sub_le (u v : ℂ) :
    ‖(‖u‖ ^ 2 : ℂ) * u - (‖v‖ ^ 2 : ℂ) * v‖ ≤ 3 * max ‖u‖ ‖v‖ ^ 2 * ‖u - v‖ := by
  have := norm_cubic_sub_le_max (V := ℂ) u v
  simpa [Complex.real_smul] using this

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

lemma abs_cube_sub_cube_le {x y R : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 3 - y ^ 3| ≤ 3 * R ^ 2 * |x - y| := by
  have h := norm_cubic_sub_le_max (V := ℝ) x y
  simp only [Real.norm_eq_abs, smul_eq_mul, sq_abs] at h
  have e1 : x ^ 2 * x = x ^ 3 := by ring
  have e2 : y ^ 2 * y = y ^ 3 := by ring
  rw [e1, e2] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have hm : max |x| |y| ≤ R := max_le hx hy
  have hm0 : 0 ≤ max |x| |y| := (abs_nonneg x).trans (le_max_left _ _)
  nlinarith

/-- Frobenius-norm comparison from entrywise bounds. -/
lemma norm_le_of_abs_apply_le {X Y : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |X i j| ≤ c * |Y i j|) : ‖X‖ ≤ c * ‖Y‖ := by
  have hsq : ‖X‖ ^ 2 ≤ (c * ‖Y‖) ^ 2 := by
    rw [mul_pow, LeanDLRA.Frobenius.norm_sq_eq_sum, LeanDLRA.Frobenius.norm_sq_eq_sum,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := h i j
    have h2 : |X i j| ^ 2 ≤ (c * |Y i j|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    exact h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **The entrywise cubic nonlinearity is Frobenius-Lipschitz on max-norm balls**:
if all entries of `X`, `Y` are bounded by `R`, then `‖G X - G Y‖ ≤ 3 R² ‖X - Y‖`. -/
theorem norm_entrywiseCubic_sub_le {X Y : Matrix m n ℝ} {R : ℝ} (hX : ∀ i j, |X i j| ≤ R)
    (hY : ∀ i j, |Y i j| ≤ R) :
    ‖entrywiseCubic X - entrywiseCubic Y‖ ≤ 3 * R ^ 2 * ‖X - Y‖ :=
  norm_le_of_abs_apply_le (by positivity) fun i j => by
    simpa [entrywiseCubic] using abs_cube_sub_cube_le (hX i j) (hY i j)

/-- Bound of the entrywise cubic nonlinearity: `‖G X‖ ≤ R² ‖X‖` if all entries of `X` are
bounded by `R`. -/
theorem norm_entrywiseCubic_le {X : Matrix m n ℝ} {R : ℝ} (hX : ∀ i j, |X i j| ≤ R) :
    ‖entrywiseCubic X‖ ≤ R ^ 2 * ‖X‖ :=
  norm_le_of_abs_apply_le (by positivity) fun i j => by
    simp only [entrywiseCubic, abs_pow]
    have := hX i j
    have h0 := abs_nonneg (X i j)
    rw [show |X i j| ^ 3 = |X i j| ^ 2 * |X i j| by ring]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 this 2) h0

/-- **arXiv 2010.05249, Property 1(b)** (OP-OT-10 (a)), real-matrix version: if the exact
solution satisfies the entrywise bound `|A(t)ᵢⱼ| ≤ δ` on `[a, b]` (Assumption 1(a) of the paper),
then the entrywise cubic nonlinearity is Lipschitz on the Frobenius tube of radius `ρ` around `A`
with constant `3 (δ + ρ)²`.  (Points of the tube have entries bounded by `δ + ρ`, since
`|Xᵢⱼ - A(t)ᵢⱼ| ≤ ‖X - A(t)‖_F`.) -/
theorem isLipschitzOnTube_entrywiseCubic {A : ℝ → Matrix m n ℝ} {a b δ ρ : ℝ}
    (hA : ∀ t ∈ Icc a b, ∀ i j, |A t i j| ≤ δ) :
    IsLipschitzOnTube (fun _ X => entrywiseCubic X) A a b ρ (3 * (δ + ρ) ^ 2) := by
  intro t ht X Y hX hY
  have hent : ∀ Z : Matrix m n ℝ, ‖Z - A t‖ ≤ ρ → ∀ i j, |Z i j| ≤ δ + ρ := fun Z hZ i j => by
    have h1 := LeanDLRA.Frobenius.abs_apply_le_norm (Z - A t) i j
    have h2 := hA t ht i j
    simp only [Matrix.sub_apply] at h1
    have := abs_sub_abs_le_abs_sub (Z i j) (A t i j)
    linarith
  exact norm_entrywiseCubic_sub_le (hent X hX) (hent Y hY)

/-- **arXiv 2010.05249, Property 1(b)**, bound: if moreover `‖A(t)‖_F ≤ R₀`, the cubic
nonlinearity is bounded on the tube by `H = (δ + ρ)² (R₀ + ρ)`.  (The paper states that `H`
depends only on `δ` and `ρ`; in the Frobenius norm it also depends on the size `‖A‖_F` of the
solution, which grows with the number of grid points unless the norm is grid-scaled.) -/
theorem isBoundedOnTube_entrywiseCubic {A : ℝ → Matrix m n ℝ} {a b δ ρ R₀ : ℝ}
    (hA : ∀ t ∈ Icc a b, ∀ i j, |A t i j| ≤ δ) (hR₀ : ∀ t ∈ Icc a b, ‖A t‖ ≤ R₀) :
    IsBoundedOnTube (fun _ X => entrywiseCubic X) A a b ρ ((δ + ρ) ^ 2 * (R₀ + ρ)) := by
  intro t ht X hX
  have hent : ∀ i j, |X i j| ≤ δ + ρ := fun i j => by
    have h1 := LeanDLRA.Frobenius.abs_apply_le_norm (X - A t) i j
    have h2 := hA t ht i j
    simp only [Matrix.sub_apply] at h1
    have := abs_sub_abs_le_abs_sub (X i j) (A t i j)
    linarith
  have hXn : ‖X‖ ≤ R₀ + ρ := by
    have := norm_le_insert' X (A t)
    linarith [hR₀ t ht, norm_sub_norm_le X (A t)]
  exact (norm_entrywiseCubic_le hent).trans (by gcongr)

/-- **Robust BUG error bound for the cubic nonlinearity** (OP-OT-10 (b), BUG version;
arXiv 2010.05249, Property 1(b) combined with arXiv 2010.02022, Theorem 4).  Let `A` solve
`Ȧ = G(A)` with the entrywise cubic `G` on real `m × n` matrices, with entries bounded by `δA`
and `‖A(t)‖_F ≤ R₀`.  With `L = 3 (δA + ρ)²` and `B = (δA + ρ)² (R₀ + ρ)` (the local constants
of Property 1(b) on the Frobenius tube of radius `ρ`), the robust global bound of the BUG
integrator holds as soon as it is smaller than `ρ - 4 B h`; in particular every iterate stays in
the tube where the local constants are valid.  No global Lipschitz constant exists for `G`. -/
theorem bug_global_error_le_entrywiseCubic {A : ℝ → Matrix m n ℝ} {δA ρ R₀ ε t₀ h H δ T : ℝ}
    {N : ℕ} (hAent : ∀ t ∈ Icc t₀ (t₀ + N * h), ∀ i j, |A t i j| ≤ δA)
    (hAnorm : ∀ t ∈ Icc t₀ (t₀ + N * h), ‖A t‖ ≤ R₀) (hρ : 0 ≤ ρ) (hR₀ : 0 ≤ R₀) (hε : 0 ≤ ε)
    (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution (fun _ X => entrywiseCubic X) A t₀ (t₀ + N * h))
    {P Q : ℕ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {Y : ℕ → Matrix m n ℝ}
    {YK YL YS Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ n' < N, IsBUGStep (fun _ X => entrywiseCubic X) ε (P n') (Q n') (P (n' + 1))
      (Q (n' + 1)) (t₀ + n' * h) (t₀ + (n' + 1) * h) (Y n') (YK n') (YL n') (YS n'))
    (hY : ∀ n' < N, Y (n' + 1) = YS n' (t₀ + (n' + 1) * h))
    (hΦ : ∀ n' < N, ODESolution (fun _ X => entrywiseCubic X) (Φ n') (t₀ + n' * h)
      (t₀ + (n' + 1) * h))
    (hΦ₀ : ∀ n' < N, Φ n' (t₀ + n' * h) = Y n') (hδ : ‖Y 0 - A t₀‖ ≤ δ) (hNT : N * h ≤ T)
    (hsmall : bugGlobalBound (3 * (δA + ρ) ^ 2) ((δA + ρ) ^ 2 * (R₀ + ρ)) H T δ ε h
      + 4 * ((δA + ρ) ^ 2 * (R₀ + ρ)) * h < ρ) :
    ∀ n' ≤ N, ‖Y n' - A (t₀ + n' * h)‖ ≤
      bugGlobalBound (3 * (δA + ρ) ^ 2) ((δA + ρ) ^ 2 * (R₀ + ρ)) H T δ ε h :=
  bug_global_error_le_of_tube (isLipschitzOnTube_entrywiseCubic hAent) (by positivity)
    (isBoundedOnTube_entrywiseCubic hAent hAnorm) (by positivity) hε hh hhH hA hstep hY hΦ hΦ₀
    hδ hNT hsmall

end Cubic

/-! ### The Gram-inverse ball -/

section Gram

open scoped LeanDLRA.Frobenius Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Neumann-type perturbation of the inverse** (Frobenius norm).  If `C₀` is invertible with
`‖C₀⁻¹‖ ≤ γ` and `γ ‖Δ‖ ≤ θ < 1`, then `C₀ + Δ` is invertible. -/
theorem isUnit_det_add_of_norm_le {C₀ Δ : Matrix ι ι ℝ} (h₀ : IsUnit C₀.det) {γ θ : ℝ}
    (hγ : ‖C₀⁻¹‖ ≤ γ) (hΔ : γ * ‖Δ‖ ≤ θ) (hθ : θ < 1) : IsUnit (C₀ + Δ).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  set u := v - w with hu_def
  have hu : (C₀ + Δ) *ᵥ u = 0 := by
    simp only [hu_def, Matrix.mulVec_sub, sub_eq_zero]; exact hvw
  have hX : ‖C₀⁻¹ * Δ‖ ≤ θ :=
    (LeanDLRA.Frobenius.norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right hγ (norm_nonneg _)).trans hΔ)
  have hfix : u = -((C₀⁻¹ * Δ) *ᵥ u) := by
    have h1 : C₀⁻¹ *ᵥ ((C₀ + Δ) *ᵥ u) = u + (C₀⁻¹ * Δ) *ᵥ u := by
      rw [Matrix.mulVec_mulVec, mul_add, Matrix.nonsing_inv_mul _ h₀, Matrix.add_mulVec,
        Matrix.one_mulVec]
    rw [hu, Matrix.mulVec_zero] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  set c : Matrix ι Unit ℝ := Matrix.replicateCol Unit u with hc_def
  have hc : c = -((C₀⁻¹ * Δ) * c) := by
    rw [hc_def, ← Matrix.replicateCol_mulVec]
    conv_lhs => rw [hfix]
    ext i j
    simp
  have hnorm : ‖c‖ ≤ θ * ‖c‖ := by
    calc ‖c‖ = ‖(C₀⁻¹ * Δ) * c‖ := by conv_lhs => rw [hc, norm_neg]
      _ ≤ ‖C₀⁻¹ * Δ‖ * ‖c‖ := LeanDLRA.Frobenius.norm_mul_le _ _
      _ ≤ θ * ‖c‖ := mul_le_mul_of_nonneg_right hX (norm_nonneg _)
  have hc0 : c = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg c])
  have hu0 : u = 0 := funext fun i => by
    have := congrFun (congrFun hc0 i) ()
    simpa [hc_def] using this
  exact sub_eq_zero.1 hu0

/-- **Neumann-type perturbation bound for the inverse** (Frobenius norm): under the hypotheses
of `isUnit_det_add_of_norm_le`, `‖(C₀ + Δ)⁻¹‖ ≤ γ / (1 - θ)`.  (Proof: the identity
`C⁻¹ = C₀⁻¹ - C⁻¹ Δ C₀⁻¹` and submultiplicativity; no Neumann series and no `‖1‖ = 1` needed.) -/
theorem norm_inv_add_le {C₀ Δ : Matrix ι ι ℝ} (h₀ : IsUnit C₀.det) {γ θ : ℝ}
    (hγ : ‖C₀⁻¹‖ ≤ γ) (hΔ : γ * ‖Δ‖ ≤ θ) (hθ : θ < 1) : ‖(C₀ + Δ)⁻¹‖ ≤ γ / (1 - θ) := by
  have h1 := isUnit_det_add_of_norm_le h₀ hγ hΔ hθ
  set C := C₀ + Δ with hC
  have hid : C⁻¹ = C₀⁻¹ - C⁻¹ * Δ * C₀⁻¹ := by
    have hΔ' : Δ = C - C₀ := by rw [hC]; abel
    rw [hΔ', mul_sub, sub_mul, Matrix.nonsing_inv_mul _ h1, one_mul, mul_assoc,
      Matrix.mul_nonsing_inv _ h₀, mul_one]
    abel
  have hb : ‖C⁻¹‖ ≤ γ + ‖C⁻¹‖ * θ := by
    calc ‖C⁻¹‖ = ‖C₀⁻¹ - C⁻¹ * Δ * C₀⁻¹‖ := by rw [← hid]
      _ ≤ ‖C₀⁻¹‖ + ‖C⁻¹ * Δ * C₀⁻¹‖ := norm_sub_le _ _
      _ ≤ γ + ‖C⁻¹‖ * ‖Δ‖ * γ := by
          gcongr
          calc _ ≤ ‖C⁻¹ * Δ‖ * ‖C₀⁻¹‖ := LeanDLRA.Frobenius.norm_mul_le _ _
            _ ≤ ‖C⁻¹‖ * ‖Δ‖ * ‖C₀⁻¹‖ := by
                gcongr; exact LeanDLRA.Frobenius.norm_mul_le _ _
            _ ≤ _ := by gcongr
      _ ≤ γ + ‖C⁻¹‖ * θ := by
          have := mul_le_mul_of_nonneg_left hΔ (norm_nonneg C⁻¹)
          nlinarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [DecidableEq ι] in
/-- Frobenius norm of a cross-Gram matrix: `‖(⟪aʲ, bˡ⟫)‖_F ≤ ‖a‖ ‖b‖` (Cauchy–Schwarz). -/
lemma norm_crossGram_le (a b : PiLp 2 fun _ : ι => H) : ‖crossGram a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hsq : ‖crossGram a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [LeanDLRA.Frobenius.norm_sq_eq_sum, mul_pow, PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
    have h := abs_real_inner_le_norm (a j) (b l)
    rw [← mul_pow, crossGram, Matrix.of_apply, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

omit [DecidableEq ι] in
/-- `‖C_Z - C_{Z₀}‖_F ≤ ‖Z - Z₀‖ (‖Z‖ + ‖Z₀‖)`. -/
lemma norm_gramMatrix_sub_le (Z Z₀ : PiLp 2 fun _ : ι => H) :
    ‖gramMatrix Z - gramMatrix Z₀‖ ≤ ‖Z - Z₀‖ * (‖Z‖ + ‖Z₀‖) := by
  have hdec : gramMatrix Z - gramMatrix Z₀ = crossGram (Z - Z₀) Z + crossGram Z₀ (Z - Z₀) := by
    ext j l
    simp only [gramMatrix, crossGram, Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply,
      PiLp.sub_apply, inner_sub_left, inner_sub_right]
    ring
  rw [hdec]
  calc _ ≤ ‖crossGram (Z - Z₀) Z‖ + ‖crossGram Z₀ (Z - Z₀)‖ := norm_add_le _ _
    _ ≤ ‖Z - Z₀‖ * ‖Z‖ + ‖Z₀‖ * ‖Z - Z₀‖ :=
        add_le_add (norm_crossGram_le _ _) (norm_crossGram_le _ _)
    _ = _ := by ring

/-- **The Gram-inverse ball** (Kazashi–Nobile–Zoccolan, arXiv 2308.11581, Proposition A.1 =
arXiv 2609.20307, Proposition 2.2).  Let `Z₀ ∈ [H]^k` with `‖Z₀‖ ≤ ρ`, invertible Gram matrix
`C_{Z₀}` and `‖C_{Z₀}⁻¹‖_F ≤ γ` (`γ > 0`).  Put `η = -ρ + √(ρ² + 1/(2γ))`.  Then every `Z` with
`‖Z - Z₀‖ < η` has linearly independent components (invertible Gram matrix) and
`‖C_Z⁻¹‖_F ≤ 2γ`.  This is the tube on which the dynamically orthogonal (DO) factor field,
which contains `C_Z⁻¹`, is Lipschitz. -/
theorem gramMatrix_inv_ball {Z₀ Z : PiLp 2 fun _ : ι => H} {ρ γ : ℝ} (hγ0 : 0 < γ)
    (hρ : ‖Z₀‖ ≤ ρ) (h₀ : IsUnit (gramMatrix Z₀).det) (hγ : ‖(gramMatrix Z₀)⁻¹‖ ≤ γ)
    (hZ : ‖Z - Z₀‖ < -ρ + √(ρ ^ 2 + 1 / (2 * γ))) :
    IsUnit (gramMatrix Z).det ∧ ‖(gramMatrix Z)⁻¹‖ ≤ 2 * γ := by
  set r := ‖Z - Z₀‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  set s := √(ρ ^ 2 + 1 / (2 * γ)) with hs
  have hs2 : s ^ 2 = ρ ^ 2 + 1 / (2 * γ) := Real.sq_sqrt (by positivity)
  have hZn : ‖Z‖ ≤ ρ + r := by
    have := norm_le_insert' Z Z₀
    linarith [norm_sub_norm_le Z Z₀]
  have hΔ : ‖gramMatrix Z - gramMatrix Z₀‖ ≤ r * (2 * ρ + r) :=
    (norm_gramMatrix_sub_le Z Z₀).trans (mul_le_mul_of_nonneg_left (by linarith) hr0)
  have hlt : r * (2 * ρ + r) < 1 / (2 * γ) := by
    have h1 : r + ρ < s := by linarith
    have h2 : (r + ρ) ^ 2 < s ^ 2 := by nlinarith
    nlinarith
  have hθ : γ * ‖gramMatrix Z - gramMatrix Z₀‖ ≤ 1 / 2 := by
    have : γ * (r * (2 * ρ + r)) ≤ γ * (1 / (2 * γ)) :=
      mul_le_mul_of_nonneg_left hlt.le hγ0.le
    have e : γ * (1 / (2 * γ)) = 1 / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hΔ hγ0.le]
  have hC : gramMatrix Z = gramMatrix Z₀ + (gramMatrix Z - gramMatrix Z₀) := by abel
  refine ⟨hC ▸ isUnit_det_add_of_norm_le h₀ hγ hθ (by norm_num), ?_⟩
  rw [hC]
  refine (norm_inv_add_le h₀ hγ hθ (by norm_num)).trans_eq ?_
  ring

/-- **Weyl-type lemma without SVD** (OP-EX-04 (b), the rank part; Frobenius-inverse form).
Let `A = U S Vᵀ` with orthonormal `U`, `V` (`UᵀU = 1`, `VᵀV = 1`) and invertible core `S` with
`‖S⁻¹‖_F ≤ γ`.  If `γ ‖Y - A‖_F ≤ θ < 1`, then the coefficient matrix `Uᵀ Y V` is invertible
(so `rank Y ≥ k`) and `‖(Uᵀ Y V)⁻¹‖_F ≤ γ / (1 - θ)`, i.e. the smallest singular value of the
`k × k` core of `Y` stays above `(1 - θ)/γ`: a perturbation of size `< σ_k(A)` cannot leave the
rank-`k` manifold.  This is the certificate behind the continuation principle of OP-EX-04 (b). -/
theorem isUnit_det_coeff_of_near {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq k] {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {S : Matrix k k ℝ} (hS : IsUnit S.det) {γ θ : ℝ} (hγ : ‖S⁻¹‖ ≤ γ) (hγ0 : 0 ≤ γ)
    {Y : Matrix m n ℝ} (hY : γ * ‖Y - U * S * Vᵀ‖ ≤ θ) (hθ : θ < 1) :
    IsUnit (Uᵀ * Y * V).det ∧ ‖(Uᵀ * Y * V)⁻¹‖ ≤ γ / (1 - θ) := by
  set Δ := Uᵀ * (Y - U * S * Vᵀ) * V with hΔ
  have hcore : Uᵀ * (U * S * Vᵀ) * V = S := by
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hdec : Uᵀ * Y * V = S + Δ := by
    rw [hΔ, Matrix.mul_sub, Matrix.sub_mul, hcore]
    abel
  have hΔn : γ * ‖Δ‖ ≤ θ := by
    have h1 : ‖Δ‖ ≤ ‖Y - U * S * Vᵀ‖ :=
      (norm_mul_le_of_orthonormal hV _).trans (norm_transpose_mul_le hU _)
    nlinarith [mul_le_mul_of_nonneg_left h1 hγ0]
  rw [hdec]
  exact ⟨isUnit_det_add_of_norm_le hS hγ hΔn hθ, norm_inv_add_le hS hγ hΔn hθ⟩

end Gram

/-! ### Satisfiability of the hypotheses -/

section Examples

/-- The zero trajectory solves `y' = f(t, y)` whenever `f t 0 = 0`. -/
lemma odeSolution_zero_of_eq_zero {f : ℝ → ℝ → ℝ} (hf : ∀ t, f t 0 = 0) (a b : ℝ) :
    ODESolution f (fun _ => 0) a b :=
  ⟨continuousOn_const, fun t _ => by rw [hf]; exact hasDerivWithinAt_const _ _ _⟩

/-- The tube hypotheses of `bug_global_error_le_of_tube`, including the smallness condition, are
jointly satisfiable for a field that is **not globally Lipschitz**: `F(t, x) = x²` on `ℝ` is
`2`-Lipschitz and bounded by `1` on the tube of radius `1` around the exact solution `A = 0`, and
with ten BUG steps of size `h = 1/100` (all projectors the identity) the theorem applies. -/
example : ∀ n ≤ 10, ‖(0 : ℝ) - 0‖ ≤ bugGlobalBound 2 1 (1 / 100) (1 / 10) 0 0 (1 / 100) := by
  have hsol : ∀ a b : ℝ, ODESolution (fun (_ : ℝ) (x : ℝ) => x ^ 2) (fun _ => (0 : ℝ)) a b :=
    odeSolution_zero_of_eq_zero (f := fun _ x => x ^ 2) fun _ => by norm_num
  have key := bug_global_error_le_of_tube (E := ℝ) (F := fun _ x => x ^ 2) (A := fun _ => 0)
    (ρ := 1) (B := 1) (ε := 0) (L := 2) (H := 1 / 100) (t₀ := 0) (h := 1 / 100) (N := 10)
    (fun t _ x y hx hy => by
      simp only [sub_zero, Real.norm_eq_abs] at hx hy ⊢
      rw [show x ^ 2 - y ^ 2 = (x + y) * (x - y) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_right ((abs_add_le x y).trans (by linarith)) (abs_nonneg _))
    (by norm_num)
    (fun t _ x hx => by
      simp only [sub_zero, Real.norm_eq_abs] at hx ⊢
      rw [abs_pow]; nlinarith [abs_nonneg x])
    zero_le_one le_rfl (by norm_num) le_rfl (hsol _ _)
    (P := fun _ => 1) (Q := fun _ => 1) (Y := fun _ => 0) (YK := fun _ _ => 0)
    (YL := fun _ _ => 0) (YS := fun _ _ => 0) (Φ := fun _ _ => 0)
    (fun n _ =>
      { projP₀ := IsOrthProj.one
        projQ₀ := IsOrthProj.one
        projP₁ := IsOrthProj.one
        projQ₁ := IsOrthProj.one
        comm₁ := fun _ => rfl
        kSol := ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const _ _ _⟩
        kStart := rfl
        kCap := by simp
        kNormal := fun _ _ => by simp
        lSol := ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const _ _ _⟩
        lStart := rfl
        lCap := by simp
        lNormal := fun _ _ => by simp
        sSol := ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const _ _ _⟩
        sStart := by simp })
    (fun _ _ => rfl) (fun _ _ => hsol _ _) (fun _ _ => rfl)
    (δ := 0) (T := 1 / 10) (by simp) (by norm_num) (by
      have e1 : Real.exp (2 * (1 / 10)) ≤ 3 :=
        (Real.exp_le_exp.2 (by norm_num)).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
      have e2 : Real.exp (2 * (1 / 100)) ≤ 3 :=
        (Real.exp_le_exp.2 (by norm_num)).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
      have p1 := Real.exp_pos (2 * (1 / 10))
      have p2 := Real.exp_pos (2 * (1 / 100))
      unfold bugGlobalBound bugC₁ bugC₂
      nlinarith [mul_le_mul e1 e2 p2.le (by norm_num)])
  intro n hn
  simpa using key n hn

/-- `exists_ODESolution_of_linearGrowth` applies to unbounded fields: `F(t, x) = -x + sin t`
on `ℝ` (Lipschitz constant `1`, `|F(t, 0)| ≤ 1`, unbounded in `x`). -/
example : ∃ y : ℝ → ℝ, ODESolution (fun t x => -x + Real.sin t) y 0 10 ∧ y 0 = 5 :=
  exists_ODESolution_of_linearGrowth (L := 1) (K := 1)
    (fun t x y => by
      simp only [Real.norm_eq_abs]
      rw [show -x + Real.sin t - (-y + Real.sin t) = -(x - y) by ring, abs_neg, one_mul])
    zero_le_one (fun t _ => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one t)
    (fun x => by fun_prop) (by norm_num) 5

end Examples

end LeanDLRA
