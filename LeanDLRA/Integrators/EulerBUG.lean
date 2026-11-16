import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Stability.Energy
import LeanDLRA.Matrix.Projectors

/-!
# Explicit-Euler BUG, XL/sXL and GAP integrators

Most practical DLRA codes replace the exact K-, L- and S-substep flows of the basis-update &
Galerkin (BUG) integrator by **one explicit Euler step each**, but quote robust error bounds that
were proved for exactly solved substeps.  This file closes that gap and adds the corresponding
theory for the XL/sXL integrators (Einkemmer–Hu–Zhang, arXiv 2502.08951) and the GAP
integrator (Ceruti–Crouseilles–Einkemmer, arXiv 2505.19929).  Everything is abstract: `E` is a
real inner product space, left/right bases are orthogonal projectors.

## Main results

### Discrete capture lemma (OP-OT-01)

* `ODESolution.norm_sub_euler_le_half`, `euler_defect_le`: the local error of the full explicit
  Euler step is `≤ (L B + Lₜ) h² / 2` (`Lₜ` is a time-Lipschitz constant of `F` at the starting
  point; `Lₜ = 0` for autonomous problems).
* `euler_capture`: if the new basis `P₁` captures the Euler K-step `YK₁ = Y₀ + h Q₀ F(t₀, Y₀)`,
  then `‖(1 - P₁) A(t₁)‖ ≤ h (ε + (L B + Lₜ) h / 2)` with `ε` the normal component at `Y₀`.
* `euler_capture_of_normal_at_K`: the same with the normal-component assumption at `YK₁` (the
  factored form): `‖(1 - P₁) A(t₁)‖ ≤ h (ε + (3 L B + Lₜ) h / 2)`; for `Lₜ = 0`
  this is exactly the claimed `h (ε + (3/2) L B h)` of OP-OT-01.
* `euler_bug_capture`: `‖A(t₁) - P₁ Q₁ A(t₁)‖ ≤ 2 h (ε + (3 L B + Lₜ) h / 2)`.

### Explicit-Euler BUG (Hauck–Schnake, arXiv 2209.00550, Thm 4.1 / Lemma 4.1; arXiv 2502.07040)

* `projected_euler_local_error`, `galerkin_euler_local_error`: local error of the projected
  Euler step `R (Y₀ + h F(t₀, Y₀))` (2209.00550, (4.18), Algorithm 4.3; the forward-Euler
  augmented BUG of 2502.07040, Sec. 2.1) and of the Galerkin Euler step
  `R (R Y₀ + h F(t₀, R Y₀))` (2209.00550, (4.16)) in terms of the capture defect of `R`.
* `eulerBug_local_error`, `eulerBug_global_error`: Lemma 4.1 and Theorem 4.1 of 2209.00550 with
  explicit constants: `‖Yₙ - A(tₙ)‖ ≤ e^{L T} (δ + T (2 ε + (7 L B + 3 Lₜ) h / 2))`.
  The global bound is obtained by **Lady Windermere's fan with exact-flow propagation**; the
  published proof instead invokes stability of the full forward Euler map, which does not apply
  because the bases (hence the numerical map) depend on the state.
* `galerkinEulerBug_local_error`, `galerkinEulerBug_global_error`: the same for the Galerkin
  Euler S-step, which starts from the projected old coefficients `P₁ Q₁ Y₀` (the
  `S^{n,*} = M Sⁿ Nᵀ` step of OP-OT-01); the projection only adds `h L (B h + ϑ)` per step.
* `augmentedBug_euler_local_error`, `augmentedBug_euler_global_error`,
  `parallelBUG_euler_local_error`: for the augmented (rank-adaptive) and the parallel BUG with
  Euler substeps the local error is `h ε + (L B + Lₜ) h² / 2 + ϑ_tr` with `ε` the doubly normal
  component at `Y₀` (constant `1` in front of `h ε`).
* `kslEuler_sub_euler`, `kslEuler_local_error`, `kslEuler_global_error`: the projector-splitting
  integrator with explicit Euler substeps (`Energy.kslEulerStep`) has local error
  `h (ε + (9 L B + Lₜ) h / 2)` (exact substeps: `h (11 L B h + ε)`, KLW 2016 Thm 2.1).

### Lipschitz-free comparison with the full Euler scheme (OP-ST-01; Uschmajew–Zeiser 2609.02721)

* `sub_proj_proj_eq`, `norm_sub_proj_proj_le`: under the capture hypotheses of the augmented
  bases (`P₁ ⊇ P₀`, `Q₁ ⊇ Q₀`, `P₁` contains `Q₀ f`, `Q₁` contains `P₀ f`),
  `f - P₁ Q₁ f = (1 - P₁) X + P₁ (1 - Q₁) X` with `X = (1 - P₀)(1 - Q₀) f`, so
  `‖f - P₁ Q₁ f‖ ≤ ‖X‖` (the doubly normal component; no `√2`).
* `augmentedBug_euler_sub_euler` (matrix form: `matrix_augmentedBug_euler_sub_euler`): one
  augmented BUG Euler step deviates from the full Euler step by at most `h ‖X‖`;
  `parallelBUG_euler_sub_euler` (exactly `h ‖X‖`) and
  `xl_euler_sub_euler`/`sxl_euler_eq` for the parallel BUG and the XL/sXL integrators.
* `perturbed_iteration_le`: discrete Grönwall comparison of a perturbed iteration with a
  `(1 + C h)`-Lipschitz one-step map.
* `augmentedBug_euler_global_vs_euler`, `parallelBUG_euler_global_vs_euler`,
  `xl_euler_global_vs_euler`: `‖Yₙ - uₙ‖ ≤ e^{C tₙ} (‖Y₀ - u₀‖ + tₙ ε + n θ)` against the full
  explicit Euler iterates `uₙ`, **without any Lipschitz constant of `F`**.
* `sat_step_sub_euler`, `sat_global_error`, `sat_global_error_paper`: Theorem 4.3 of
  arXiv 2609.02721 (rank-adaptive SAT scheme vs. full forward Euler), and
  `sat_tolerance_scaling`: the tolerance-scaling corollary (`≤ 2 C τ`).

### XL, sXL and GAP (OP-HO-07; arXiv 2502.08951, Sec. 2; arXiv 2505.19929)

* `xl_local_error`, `xl_global_error`: robust local/global error of the XL integrator
  (K-step, then Galerkin L-step in the new left basis, truncation):
  `‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1)(B h + ϑ) + ϑ + ϑ_tr`, `ϑ = h (4 L B h + ε)`.
* `gap_local_error`, `gap_global_error`: the GAP integrator (Algorithm 2.3 of 2505.19929),
  the mirror image of XL (L-step, then Galerkin K-step in the new right basis).
* `sxl_local_error`, `sxl_global_error`: the explicit-Euler XL integrator of 2502.08951
  (sXL) has local error `≤ h ε + (L B + Lₜ) h² / 2 + ϑ_tr` with `ε` the doubly normal component
  at `Y₀`; for separable fields (the setting of 2502.08951, (2.7)) `ε = 0`.
* `normal_dist_lipschitz`, `normal_dist_le_end`: Lemma 3.2 of 2505.19929 (with the sharper
  constant `B` instead of `2 B`).

## Open problems addressed

* **OP-OT-01** (explicit part resolved): discrete capture lemma (both forms of the normal
  bound), two-sided capture, explicit-Euler BUG (projected and Galerkin S-step), augmented,
  parallel and KSL integrators with Euler substeps: local `O(h (h + ε))` and global bounds via
  Lady Windermere's fan.  Not covered: IMEX / one-sided-Lipschitz (stiff, `ε`-uniform) variants,
  and the convergence-to-equilibrium part of the `S^{n,*}` heuristic.
* **OP-ST-01** (resolved): Lipschitz-free comparison of the explicit-Euler augmented and parallel
  BUG with the full explicit Euler scheme.
* **OP-HO-07** (resolved): robust error bounds for XL and sXL (and GAP).
-/

open Set ContinuousLinearMap Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The local error of the explicit Euler step -/

section EulerDefect

/-- **Local error of the explicit Euler method, sharp constant.**  If `φ' = F(t, φ)` on `[a, b]`
and `‖F(t, φ t) - F(a, φ a)‖ ≤ c (t - a)`, then
`‖φ b - (φ a + (b - a) F(a, φ a))‖ ≤ c (b - a)² / 2`. -/
theorem ODESolution.norm_sub_euler_le_half {F : ℝ → E → E} {φ : ℝ → E} {a b c : ℝ}
    (hab : a ≤ b) (hφ : ODESolution F φ a b)
    (hK : ∀ t ∈ Ico a b, ‖F t (φ t) - F a (φ a)‖ ≤ c * (t - a)) :
    ‖φ b - (φ a + (b - a) • F a (φ a))‖ ≤ c * (b - a) ^ 2 / 2 := by
  set v := F a (φ a)
  set g : ℝ → E := fun t => φ t - (φ a + (t - a) • v) with hg
  have hgc : ContinuousOn g (Icc a b) :=
    hφ.cont.sub (continuousOn_const.add
      ((continuous_id.sub continuous_const).smul continuous_const).continuousOn)
  have hgd : ∀ t ∈ Ico a b, HasDerivWithinAt g (F t (φ t) - v) (Ici t) t := fun t ht => by
    have h1 : HasDerivWithinAt (fun s : ℝ => φ a + (s - a) • v) ((1 : ℝ) • v) (Ici t) t :=
      (((hasDerivWithinAt_id t _).sub_const a).smul_const v).const_add _
    rw [one_smul] at h1
    exact (hφ.deriv t ht).sub h1
  have hga : ‖g a‖ ≤ c * (a - a) ^ 2 / 2 := by simp [hg]
  have hB : ∀ x, HasDerivAt (fun t => c * (t - a) ^ 2 / 2) (c * (x - a)) x := fun x => by
    have h1 : HasDerivAt (fun t => (t - a) ^ 2) (2 * (x - a)) x := by
      simpa using ((hasDerivAt_id x).sub_const a).fun_pow 2
    convert (h1.const_mul c).div_const 2 using 1; ring
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary hgc hgd hga hB hK ⟨hab, le_rfl⟩

/-- **Euler defect of the exact flow.**  Let `F` be `L`-Lipschitz and bounded by `B`, `A` a
solution of `A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, and let `F` be `Lₜ`-Lipschitz in time at
the starting point: `‖F(t, A t₀) - F(t₀, A t₀)‖ ≤ Lₜ (t - t₀)` (automatic with `Lₜ = 0` for
autonomous problems).  Then `‖A t₁ - (A t₀ + h F(t₀, A t₀))‖ ≤ (L B + Lₜ) h² / 2`. -/
theorem euler_defect_le {F : ℝ → E → E} {L B Lt : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {A : ℝ → E}
    (hA : ODESolution F A t₀ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t (A t₀) - F t₀ (A t₀)‖ ≤ Lt * (t - t₀)) :
    ‖A t₁ - (A t₀ + h • F t₀ (A t₀))‖ ≤ (L * B + Lt) * h ^ 2 / 2 := by
  have hle : t₀ ≤ t₁ := by linarith
  have h1 := hA.norm_sub_euler_le_half (c := L * B + Lt) hle fun t ht => by
    have hs := hA.norm_sub_le_of_bounded hB t ⟨ht.1, ht.2.le⟩
    calc ‖F t (A t) - F t₀ (A t₀)‖
        ≤ ‖F t (A t) - F t (A t₀)‖ + ‖F t (A t₀) - F t₀ (A t₀)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * (B * (t - t₀)) + Lt * (t - t₀) :=
          add_le_add ((hF t _ _).trans (mul_le_mul_of_nonneg_left hs hL)) (hFt t ht)
      _ = (L * B + Lt) * (t - t₀) := by ring
  rwa [show t₁ - t₀ = h by linarith] at h1

end EulerDefect

/-! ### The discrete capture lemma (OP-OT-01) -/

section Capture

variable {F : ℝ → E → E} {L B Lt ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {Y₀ : E}

/-- **Discrete (explicit Euler) capture lemma, normal component at `Y₀`.**  Let `F` be
`L`-Lipschitz and bounded by `B`, `A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, `A t₀ = Y₀`, and
`‖F(t, Y₀) - F(t₀, Y₀)‖ ≤ Lₜ (t - t₀)`.  If the new basis `P₁` (an orthogonal projector) captures
the explicit Euler K-step `YK₁ = Y₀ + h Q₀ F(t₀, Y₀)` (any linear `Q₀`, in practice the old right
projector), and `‖(1 - P₁)(1 - Q₀) F(t₀, Y₀)‖ ≤ ε`, then
`‖(1 - P₁) A(t₁)‖ ≤ h (ε + (L B + Lₜ) h / 2)`.

*Proof.* `(1 - P₁) A₁ = (1 - P₁)(A₁ - Y₀ - h F₀) + h (1 - P₁)(1 - Q₀) F₀` because `P₁` fixes
`YK₁`; the first term is the Euler defect `euler_defect_le`. -/
theorem euler_capture (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hKcap : P₁ (Y₀ + h • Q₀ (F t₀ Y₀)) = Y₀ + h • Q₀ (F t₀ Y₀))
    (hε : ‖(1 - P₁) ((1 - Q₀) (F t₀ Y₀))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (ε + (L * B + Lt) * h / 2) := by
  have hdef := euler_defect_le hF hL hB ht₁ hh hA (by rw [hA₀]; exact hFt)
  rw [hA₀] at hdef
  have hz : (1 - P₁) (Y₀ + h • Q₀ (F t₀ Y₀)) = 0 := by simp [hKcap]
  have hsplit : (1 - P₁) (Y₀ + h • F t₀ Y₀) =
      (1 - P₁) (Y₀ + h • Q₀ (F t₀ Y₀)) + h • (1 - P₁) ((1 - Q₀) (F t₀ Y₀)) := by
    simp only [map_add, map_smul, sub_apply, one_apply_eq_self, map_sub, smul_sub]; abel
  rw [hz, zero_add] at hsplit
  have key : (1 - P₁) (A t₁) =
      (1 - P₁) (A t₁ - (Y₀ + h • F t₀ Y₀)) + h • (1 - P₁) ((1 - Q₀) (F t₀ Y₀)) := by
    rw [map_sub, hsplit]; abel
  rw [key]
  calc _ ≤ ‖(1 - P₁) (A t₁ - (Y₀ + h • F t₀ Y₀))‖ + ‖h • (1 - P₁) ((1 - Q₀) (F t₀ Y₀))‖ :=
        norm_add_le _ _
    _ ≤ (L * B + Lt) * h ^ 2 / 2 + h * ε := by
        rw [norm_smul, Real.norm_of_nonneg hh]
        exact add_le_add ((hP₁.compl.norm_le _).trans hdef) (mul_le_mul_of_nonneg_left hε hh)
    _ = h * (ε + (L * B + Lt) * h / 2) := by ring

/-- Moving the normal-component bound from the Euler K-step point `YK₁ = Y₀ + h Q₀ F(t₀, Y₀)` to
`Y₀`: `‖(1 - P₁)(1 - Q₀) F(t₀, Y₀)‖ ≤ ε + L B h` if `‖(1 - P₁)(1 - Q₀) F(t₀, YK₁)‖ ≤ ε`. -/
theorem normal_le_of_normal_at_K (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hh : 0 ≤ h) (hε : ‖(1 - P₁) ((1 - Q₀) (F t₀ (Y₀ + h • Q₀ (F t₀ Y₀))))‖ ≤ ε) :
    ‖(1 - P₁) ((1 - Q₀) (F t₀ Y₀))‖ ≤ ε + L * B * h := by
  set YK := Y₀ + h • Q₀ (F t₀ Y₀)
  have hYK : ‖Y₀ - YK‖ ≤ h * B := by
    simp only [YK, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left ((hQ₀.norm_le _).trans (hB _ _)) hh
  have hsplit : (1 - P₁) ((1 - Q₀) (F t₀ Y₀)) =
      (1 - P₁) ((1 - Q₀) (F t₀ YK)) + (1 - P₁) ((1 - Q₀) (F t₀ Y₀ - F t₀ YK)) := by
    rw [map_sub, map_sub]; abel
  rw [hsplit]
  calc _ ≤ ‖(1 - P₁) ((1 - Q₀) (F t₀ YK))‖ + ‖(1 - P₁) ((1 - Q₀) (F t₀ Y₀ - F t₀ YK))‖ :=
        norm_add_le _ _
    _ ≤ ε + L * (h * B) := by
        refine add_le_add hε ?_
        exact (hP₁.compl.norm_le _).trans ((hQ₀.compl.norm_le _).trans
          ((hF _ _ _).trans (mul_le_mul_of_nonneg_left hYK hL)))
    _ = ε + L * B * h := by ring

/-- **Discrete capture lemma, normal component at the K-step point** (OP-OT-01 as stated).  As
`euler_capture`, but with the normal-component assumption at `YK₁ = Y₀ + h Q₀ F(t₀, Y₀)` (which
for matrices is `U₁ (U₁ᵀ K₁) V₀ᵀ`, a point of the rank-`r` manifold, so the factored assumption
`‖(I - U₁U₁ᵀ) F(U₁ S V₀ᵀ) (I - V₀V₀ᵀ)‖ ≤ ε` applies) and `Q₀` an orthogonal projector:
`‖(1 - P₁) A(t₁)‖ ≤ h (ε + (3 L B + Lₜ) h / 2)`, i.e. `h (ε + (3/2) L B h)` when `Lₜ = 0`. -/
theorem euler_capture_of_normal_at_K (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hKcap : P₁ (Y₀ + h • Q₀ (F t₀ Y₀)) = Y₀ + h • Q₀ (F t₀ Y₀))
    (hε : ‖(1 - P₁) ((1 - Q₀) (F t₀ (Y₀ + h • Q₀ (F t₀ Y₀))))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (ε + (3 * L * B + Lt) * h / 2) := by
  calc _ ≤ h * (ε + L * B * h + (L * B + Lt) * h / 2) :=
        euler_capture hF hL hB hP₁ ht₁ hh hA hA₀ hFt hKcap
          (normal_le_of_normal_at_K hF hL hB hP₁ hQ₀ hh hε)
    _ = h * (ε + (3 * L * B + Lt) * h / 2) := by ring

/-- **Two-sided discrete capture** (OP-OT-01): if the new left basis `P₁` captures the Euler
K-step `Y₀ + h Q₀ F(t₀, Y₀)` and the new right basis `Q₁` captures the Euler L-step
`Y₀ + h P₀ F(t₀, Y₀)`, with the normal-component bounds at these points, then
`‖A(t₁) - P₁ Q₁ A(t₁)‖ ≤ 2 h (ε + (3 L B + Lₜ) h / 2)`. -/
theorem euler_bug_capture (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀)
    (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hKcap : P₁ (Y₀ + h • Q₀ (F t₀ Y₀)) = Y₀ + h • Q₀ (F t₀ Y₀))
    (hLcap : Q₁ (Y₀ + h • P₀ (F t₀ Y₀)) = Y₀ + h • P₀ (F t₀ Y₀))
    (hεK : ‖(1 - P₁) ((1 - Q₀) (F t₀ (Y₀ + h • Q₀ (F t₀ Y₀))))‖ ≤ ε)
    (hεL : ‖(1 - Q₁) ((1 - P₀) (F t₀ (Y₀ + h • P₀ (F t₀ Y₀))))‖ ≤ ε) :
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ 2 * h * (ε + (3 * L * B + Lt) * h / 2) := by
  have h1 := euler_capture_of_normal_at_K hF hL hB hP₁ hQ₀ ht₁ hh hA hA₀ hFt hKcap hεK
  have h2 := euler_capture_of_normal_at_K hF hL hB hQ₁ hP₀ ht₁ hh hA hA₀ hFt hLcap hεL
  have h3 := norm_sub_apply_apply_le (Q := Q₁) hP₁ (A t₁)
  linarith

end Capture

/-! ### Explicit-Euler BUG: local and global error (arXiv 2209.00550, Thm 4.1) -/

section EulerBUG

variable {F : ℝ → E → E} {L B Lt ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {Y₀ : E}

/-- **Local error of a projected Euler step** (arXiv 2209.00550, proof of Lemma 4.1).  For any
orthogonal projector `R` with capture defect `‖A(t₁) - R A(t₁)‖ ≤ θ`,
`‖R (Y₀ + h F(t₀, Y₀)) - A(t₁)‖ ≤ (L B + Lₜ) h² / 2 + θ`.  With `R = P₁ Q₁` this is the projected
unconventional integrator (2209.00550, (4.18), Algorithm 4.3), and, when `R` fixes `Y₀`, the
forward-Euler augmented BUG step (arXiv 2502.07040, Sec. 2.1: the Galerkin projection of the
full Euler step). -/
theorem projected_euler_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {R : E →L[ℝ] E} (hR : IsOrthProj R) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {θ : ℝ}
    (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖R (Y₀ + h • F t₀ Y₀) - A t₁‖ ≤ (L * B + Lt) * h ^ 2 / 2 + θ := by
  have hdef := euler_defect_le hF hL hB ht₁ hh hA (by rw [hA₀]; exact hFt)
  rw [hA₀] at hdef
  have hsplit : R (Y₀ + h • F t₀ Y₀) - A t₁ =
      R ((Y₀ + h • F t₀ Y₀) - A t₁) - (A t₁ - R (A t₁)) := by rw [map_sub]; abel
  rw [hsplit]
  calc _ ≤ ‖R ((Y₀ + h • F t₀ Y₀) - A t₁)‖ + ‖A t₁ - R (A t₁)‖ := norm_sub_le _ _
    _ ≤ (L * B + Lt) * h ^ 2 / 2 + θ := by
        refine add_le_add ((hR.norm_le _).trans ?_) hθ
        rwa [norm_sub_rev]

/-- **Local error of a Galerkin Euler step** (arXiv 2209.00550, (4.16); the explicit-Euler BUG
step `Energy.galerkinEulerStep`).  The S-step starts from the *projected* old value `R Y₀` (the
`S^{n,*}` of OP-OT-01): for any orthogonal projector `R` with `‖A(t₁) - R A(t₁)‖ ≤ θ`,
`‖R (R Y₀ + h F(t₀, R Y₀)) - A(t₁)‖ ≤ (L B + Lₜ) h² / 2 + θ + h L (B h + θ)`.
The projection of the old coefficients enters only through the term `h L (B h + θ)`. -/
theorem galerkin_euler_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {R : E →L[ℝ] E} (hR : IsOrthProj R) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {θ : ℝ}
    (hθ : ‖A t₁ - R (A t₁)‖ ≤ θ) :
    ‖R (R Y₀ + h • F t₀ (R Y₀)) - A t₁‖ ≤
      (L * B + Lt) * h ^ 2 / 2 + θ + h * L * (B * h + θ) := by
  have h1 := projected_euler_local_error hF hL hB hR ht₁ hh hA hA₀ hFt hθ
  have hY : ‖Y₀ - R Y₀‖ ≤ B * h + θ := by
    have hs := hA.norm_sub_start_le hB ht₁ t₁ ⟨by linarith, le_rfl⟩
    rw [hA₀] at hs
    have hdec : Y₀ - R Y₀ = ((Y₀ - A t₁) - R (Y₀ - A t₁)) + (A t₁ - R (A t₁)) := by
      rw [map_sub]; abel
    rw [hdec]
    calc _ ≤ ‖(Y₀ - A t₁) - R (Y₀ - A t₁)‖ + ‖A t₁ - R (A t₁)‖ := norm_add_le _ _
      _ ≤ ‖Y₀ - A t₁‖ + θ := add_le_add (hR.norm_sub_le _) hθ
      _ ≤ B * h + θ := by rw [norm_sub_rev]; linarith
  have hsplit : R (R Y₀ + h • F t₀ (R Y₀)) - A t₁ =
      (R (Y₀ + h • F t₀ Y₀) - A t₁) + h • R (F t₀ (R Y₀) - F t₀ Y₀) := by
    simp only [map_add, map_smul, map_sub, hR.idem, smul_sub]; abel
  rw [hsplit]
  calc _ ≤ ‖R (Y₀ + h • F t₀ Y₀) - A t₁‖ + ‖h • R (F t₀ (R Y₀) - F t₀ Y₀)‖ := norm_add_le _ _
    _ ≤ ((L * B + Lt) * h ^ 2 / 2 + θ) + h * (L * (B * h + θ)) := by
        refine add_le_add h1 ?_
        rw [norm_smul, Real.norm_of_nonneg hh]
        refine mul_le_mul_of_nonneg_left ?_ hh
        refine (hR.norm_le _).trans ((hF _ _ _).trans ?_)
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_left hY hL
    _ = _ := by ring

/-- **Robust local error of the explicit-Euler BUG step** (arXiv 2209.00550, Lemma 4.1, with
explicit constants; Algorithm 4.3, *projected unconventional integrator*).  The new bases
`P₁`, `Q₁` (commuting orthogonal projectors) capture the Euler K- and L-steps, and the normal
component is bounded at these points.  Then the step `Y₁ = P₁ Q₁ (Y₀ + h F(t₀, Y₀))` satisfies
`‖Y₁ - A(t₁)‖ ≤ h (2 ε + (7 L B + 3 Lₜ) h / 2) = O(h (h + ε))`, independently of singular
values. -/
theorem eulerBug_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀)
    (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁) (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x))
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hKcap : P₁ (Y₀ + h • Q₀ (F t₀ Y₀)) = Y₀ + h • Q₀ (F t₀ Y₀))
    (hLcap : Q₁ (Y₀ + h • P₀ (F t₀ Y₀)) = Y₀ + h • P₀ (F t₀ Y₀))
    (hεK : ‖(1 - P₁) ((1 - Q₀) (F t₀ (Y₀ + h • Q₀ (F t₀ Y₀))))‖ ≤ ε)
    (hεL : ‖(1 - Q₁) ((1 - P₀) (F t₀ (Y₀ + h • P₀ (F t₀ Y₀))))‖ ≤ ε) :
    ‖P₁ (Q₁ (Y₀ + h • F t₀ Y₀)) - A t₁‖ ≤ h * (2 * ε + (7 * L * B + 3 * Lt) * h / 2) := by
  have hcap := euler_bug_capture hF hL hB hP₀ hQ₀ hP₁ hQ₁ ht₁ hh hA hA₀ hFt hKcap hLcap hεK hεL
  have h1 := projected_euler_local_error hF hL hB (hP₁.mul hQ₁ hc₁) ht₁ hh hA hA₀ hFt hcap
  calc _ ≤ _ := h1
    _ = _ := by ring

/-- **Local error of the explicit-Euler BUG step with Galerkin S-step** (arXiv 2209.00550,
(4.16); arXiv 2107.07282, eq. (38)): `Y₁ = P₁ Q₁ (Ȳ + h F(t₀, Ȳ))` with `Ȳ = P₁ Q₁ Y₀`.  Under the
hypotheses of `eulerBug_local_error`, with `ϑ = 2 h (ε + (3 L B + Lₜ) h / 2)`,
`‖Y₁ - A(t₁)‖ ≤ (L B + Lₜ) h² / 2 + ϑ + h L (B h + ϑ)`. -/
theorem galerkinEulerBug_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀)
    (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hKcap : P₁ (Y₀ + h • Q₀ (F t₀ Y₀)) = Y₀ + h • Q₀ (F t₀ Y₀))
    (hLcap : Q₁ (Y₀ + h • P₀ (F t₀ Y₀)) = Y₀ + h • P₀ (F t₀ Y₀))
    (hεK : ‖(1 - P₁) ((1 - Q₀) (F t₀ (Y₀ + h • Q₀ (F t₀ Y₀))))‖ ≤ ε)
    (hεL : ‖(1 - Q₁) ((1 - P₀) (F t₀ (Y₀ + h • P₀ (F t₀ Y₀))))‖ ≤ ε) :
    ‖P₁ (Q₁ (P₁ (Q₁ Y₀) + h • F t₀ (P₁ (Q₁ Y₀)))) - A t₁‖ ≤
      (L * B + Lt) * h ^ 2 / 2 + 2 * h * (ε + (3 * L * B + Lt) * h / 2)
        + h * L * (B * h + 2 * h * (ε + (3 * L * B + Lt) * h / 2)) := by
  have hcap := euler_bug_capture hF hL hB hP₀ hQ₀ hP₁ hQ₁ ht₁ hh hA hA₀ hFt hKcap hLcap hεK hεL
  exact galerkin_euler_local_error hF hL hB (hP₁.mul hQ₁ hc₁) ht₁ hh hA hA₀ hFt hcap

/-- **Robust global error of the explicit-Euler BUG integrator** (arXiv 2209.00550,
Theorem 4.1, with explicit constants `c₀ = e^{L T}`, `c₁ = 2 T e^{L T}`,
`c₂ = T e^{L T} (7 L B + 3 Lₜ) / 2`).  On the grid `tₙ = t₀ + n h`, the step `n` uses old bases
`P n`, `Q n` and new bases `P (n+1)`, `Q (n+1)` capturing the Euler K- and L-steps from `Y n`,
and `Y (n+1) = P (n+1) Q (n+1) (Y n + h F(tₙ, Y n))`.  With `Φ n` the exact flow from `(tₙ, Y n)`
(Lady Windermere's fan), for `n ≤ N`, `n h ≤ T`:
`‖Y n - A(tₙ)‖ ≤ e^{L T} (‖Y 0 - A t₀‖ + T (2 ε + (7 L B + 3 Lₜ) h / 2))`.

The error is propagated by the **exact flow** (`lady_windermere_of_le`), not by the numerical
map: the published proof appeals to the stability of the full forward Euler map, but the BUG map
`Y ↦ P₁(Y) Q₁(Y) (Y + h F(Y))` has state-dependent bases, so non-expansiveness of a fixed
projector does not make it Lipschitz-stable. -/
theorem eulerBug_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hLt : 0 ≤ Lt) (hε : 0 ≤ ε) (hh : 0 ≤ h) {N : ℕ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {Φ : ℕ → ℝ → E} (hP : ∀ n, IsOrthProj (P n)) (hQ : ∀ n, IsOrthProj (Q n))
    (hc : ∀ n x, P n (Q n x) = Q n (P n x))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hFt : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (Y n) - F (t₀ + n * h) (Y n)‖ ≤ Lt * (t - (t₀ + n * h)))
    (hKcap : ∀ n < N, P (n + 1) (Y n + h • Q n (F (t₀ + n * h) (Y n))) =
      Y n + h • Q n (F (t₀ + n * h) (Y n)))
    (hLcap : ∀ n < N, Q (n + 1) (Y n + h • P n (F (t₀ + n * h) (Y n))) =
      Y n + h • P n (F (t₀ + n * h) (Y n)))
    (hεK : ∀ n < N, ‖(1 - P (n + 1)) ((1 - Q n)
      (F (t₀ + n * h) (Y n + h • Q n (F (t₀ + n * h) (Y n)))))‖ ≤ ε)
    (hεL : ∀ n < N, ‖(1 - Q (n + 1)) ((1 - P n)
      (F (t₀ + n * h) (Y n + h • P n (F (t₀ + n * h) (Y n)))))‖ ≤ ε)
    (hY : ∀ n < N, Y (n + 1) = P (n + 1) (Q (n + 1) (Y n + h • F (t₀ + n * h) (Y n))))
    {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (2 * ε + (7 * L * B + 3 * Lt) * h / 2)) := by
  have hB0 := hB.nonneg
  refine lady_windermere_of_le hF hL hh hA hΦ hΦ₀ (by positivity) fun n hn => ?_
  rw [hY n hn]
  exact eulerBug_local_error hF hL hB (hP n) (hQ n) (hP (n + 1)) (hQ (n + 1)) (hc (n + 1))
    (by ring) hh (hΦ n hn) (hΦ₀ n hn) (hFt n hn) (hKcap n hn) (hLcap n hn) (hεK n hn) (hεL n hn)

/-- **Robust global error of the explicit-Euler BUG integrator with Galerkin S-step**
(arXiv 2209.00550, (4.16); arXiv 2107.07282, eq. (38)).  As `eulerBug_global_error`, but with
`Y (n+1) = P₁ Q₁ (Ȳ + h F(tₙ, Ȳ))`, `Ȳ = P₁ Q₁ Y n`, `P₁ = P (n+1)`, `Q₁ = Q (n+1)`: with
`ϑ = 2 h (ε + (3 L B + Lₜ) h / 2)` and `ℓ = (L B + Lₜ) h² / 2 + ϑ + h L (B h + ϑ) = O(h (h + ε))`,
`‖Y n - A(tₙ)‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n ℓ)`. -/
theorem galerkinEulerBug_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hh : 0 ≤ h) {N : ℕ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {Φ : ℕ → ℝ → E} (hP : ∀ n, IsOrthProj (P n)) (hQ : ∀ n, IsOrthProj (Q n))
    (hc : ∀ n x, P n (Q n x) = Q n (P n x))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hFt : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (Y n) - F (t₀ + n * h) (Y n)‖ ≤ Lt * (t - (t₀ + n * h)))
    (hKcap : ∀ n < N, P (n + 1) (Y n + h • Q n (F (t₀ + n * h) (Y n))) =
      Y n + h • Q n (F (t₀ + n * h) (Y n)))
    (hLcap : ∀ n < N, Q (n + 1) (Y n + h • P n (F (t₀ + n * h) (Y n))) =
      Y n + h • P n (F (t₀ + n * h) (Y n)))
    (hεK : ∀ n < N, ‖(1 - P (n + 1)) ((1 - Q n)
      (F (t₀ + n * h) (Y n + h • Q n (F (t₀ + n * h) (Y n)))))‖ ≤ ε)
    (hεL : ∀ n < N, ‖(1 - Q (n + 1)) ((1 - P n)
      (F (t₀ + n * h) (Y n + h • P n (F (t₀ + n * h) (Y n)))))‖ ≤ ε)
    (hY : ∀ n < N, Y (n + 1) = P (n + 1) (Q (n + 1) (P (n + 1) (Q (n + 1) (Y n))
      + h • F (t₀ + n * h) (P (n + 1) (Q (n + 1) (Y n)))))) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ +
      n * ((L * B + Lt) * h ^ 2 / 2 + 2 * h * (ε + (3 * L * B + Lt) * h / 2)
        + h * L * (B * h + 2 * h * (ε + (3 * L * B + Lt) * h / 2)))) :=
  lady_windermere hF hL hh hA hΦ hΦ₀ fun n hn => by
    rw [hY n hn]
    exact galerkinEulerBug_local_error hF hL hB (hP n) (hQ n) (hP (n + 1)) (hQ (n + 1))
      (hc (n + 1)) (by ring) hh (hΦ n hn) (hΦ₀ n hn) (hFt n hn) (hKcap n hn) (hLcap n hn)
      (hεK n hn) (hεL n hn)

end EulerBUG

/-! ### Lipschitz-free comparison with the full explicit Euler scheme (OP-ST-01) -/

section Comparison

omit [InnerProductSpace ℝ E] in
/-- Triangle inequality through an intermediate point. -/
theorem norm_sub_le_of_le_of_le {a b c : E} {x y : ℝ} (h₁ : ‖a - b‖ ≤ x) (h₂ : ‖b - c‖ ≤ y) :
    ‖a - c‖ ≤ x + y :=
  (norm_sub_le_norm_sub_add_norm_sub a b c).trans (add_le_add h₁ h₂)

/-- **Projector identity behind OP-ST-01.**  Let `P₀ ≤ P₁` (`P₁ P₀ = P₀`), `Q₀ ≤ Q₁`, `P₀` commute
with `Q₁`, and let the augmented bases contain the K- and L-step directions: `P₁ (Q₀ f) = Q₀ f`,
`Q₁ (P₀ f) = P₀ f` (matrices: `Uf ⊇ [U₀, F V₀]`, `V̂ ⊇ [V₀, Fᵀ U₀]`).  Then with the doubly normal
component `X = (1 - P₀)(1 - Q₀) f`,
`f - P₁ Q₁ f = (1 - P₁) X + P₁ ((1 - Q₁) X)`. -/
theorem sub_proj_proj_eq {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP : ∀ x, P₁ (P₀ x) = P₀ x)
    (hQ : ∀ x, Q₁ (Q₀ x) = Q₀ x) (hc : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) {f : E}
    (hKf : P₁ (Q₀ f) = Q₀ f) (hLf : Q₁ (P₀ f) = P₀ f) :
    f - P₁ (Q₁ f) = (1 - P₁) ((1 - P₀) ((1 - Q₀) f)) + P₁ ((1 - Q₁) ((1 - P₀) ((1 - Q₀) f))) := by
  have hX : P₁ (Q₁ (P₀ (Q₀ f))) = P₀ (Q₀ f) := by rw [← hc, hQ, hP]
  simp only [sub_apply, one_apply_eq_self, map_sub, hP, hQ, hKf, hLf, hX]
  abel

/-- **The augmented Galerkin defect is bounded by the doubly normal component** (OP-ST-01).
Under the hypotheses of `sub_proj_proj_eq`, with orthogonal projectors and commuting `P₁`, `Q₁`:
`‖f - P₁ Q₁ f‖ ≤ ‖(1 - P₀)(1 - Q₀) f‖`.  (The two pieces are orthogonal and their squared norms
add up to at most `‖X‖²`, so no factor `√2` appears.) -/
theorem norm_sub_proj_proj_le {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₁ : IsOrthProj Q₁) (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (hP : ∀ x, P₁ (P₀ x) = P₀ x)
    (hQ : ∀ x, Q₁ (Q₀ x) = Q₀ x) (hc : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) {f : E}
    (hKf : P₁ (Q₀ f) = Q₀ f) (hLf : Q₁ (P₀ f) = P₀ f) :
    ‖f - P₁ (Q₁ f)‖ ≤ ‖(1 - P₀) ((1 - Q₀) f)‖ := by
  rw [sub_proj_proj_eq hP hQ hc hKf hLf]
  set X := (1 - P₀) ((1 - Q₀) f)
  have horth : ⟪(1 - P₁) X, P₁ ((1 - Q₁) X)⟫ = 0 := by
    rw [real_inner_comm]; simpa using hP₁.inner_sub_self ((1 - Q₁) X) X
  have hb : ‖P₁ ((1 - Q₁) X)‖ ≤ ‖P₁ X‖ := by
    have : P₁ ((1 - Q₁) X) = (1 - Q₁) (P₁ X) := by simp [hc₁]
    rw [this]; exact hQ₁.compl.norm_le _
  have hpy := hP₁.norm_sq_add X
  have hsq : ‖(1 - P₁) X + P₁ ((1 - Q₁) X)‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [norm_add_sq_real, horth]
    have : (1 - P₁) X = X - P₁ X := by simp
    rw [this]
    nlinarith [norm_nonneg (P₁ ((1 - Q₁) X)), norm_nonneg (P₁ X)]
  exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |>.2

/-- **One explicit-Euler augmented BUG step vs. the full explicit Euler step** (OP-ST-01).
Let `Y₀` lie in the old bases (`P₀ Y₀ = Y₀`, `Q₀ Y₀ = Y₀`), `f = F(t₀, Y₀)`, and let the augmented
bases `P₁ ⊇ [P₀, Q₀ f]`, `Q₁ ⊇ [Q₀, P₀ f]` be as in `norm_sub_proj_proj_le`.  Then the untruncated
step `Ŷ₁ = P₁ Q₁ (Y₀ + h f)` (`= Y₀ + h P₁ f Q₁`) satisfies
`‖Ŷ₁ - (Y₀ + h f)‖ ≤ h ‖(1 - P₀)(1 - Q₀) f‖`.  No Lipschitz constant of `F` enters. -/
theorem augmentedBug_euler_sub_euler {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₁ : IsOrthProj Q₁) (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (hP : ∀ x, P₁ (P₀ x) = P₀ x)
    (hQ : ∀ x, Q₁ (Q₀ x) = Q₀ x) (hc : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) {Y₀ f : E}
    (hPY : P₀ Y₀ = Y₀) (hQY : Q₀ Y₀ = Y₀) (hKf : P₁ (Q₀ f) = Q₀ f) (hLf : Q₁ (P₀ f) = P₀ f)
    {h : ℝ} (hh : 0 ≤ h) :
    ‖P₁ (Q₁ (Y₀ + h • f)) - (Y₀ + h • f)‖ ≤ h * ‖(1 - P₀) ((1 - Q₀) f)‖ := by
  have hY : P₁ (Q₁ Y₀) = Y₀ := by
    have h1 : Q₁ Y₀ = Y₀ := by rw [← hQY]; exact hQ Y₀
    rw [h1, ← hPY, hP]
  have heq : P₁ (Q₁ (Y₀ + h • f)) - (Y₀ + h • f) = -(h • (f - P₁ (Q₁ f))) := by
    simp only [map_add, map_smul, hY, smul_sub]; abel
  rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left (norm_sub_proj_proj_le hP₁ hQ₁ hc₁ hP hQ hc hKf hLf) hh

/-- **Parallel BUG with Euler substeps vs. the full Euler step** (OP-ST-01, parallel variant):
for commuting `P₀`, `Q₀` fixing `Y₀`, the parallel BUG step with explicit Euler substeps differs
from the full Euler step by exactly `h` times the doubly normal component:
`‖Ŷ₁ - (Y₀ + h f)‖ = |h| ‖(1 - P₀)(1 - Q₀) f‖`. -/
theorem parallelBUG_euler_sub_euler {P₀ Q₀ : E →L[ℝ] E} (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x))
    {Y₀ : E} (hPY : P₀ Y₀ = Y₀) (hQY : Q₀ Y₀ = Y₀) (h : ℝ) (f : E) :
    ‖parallelBUG P₀ Q₀ (Y₀ + h • Q₀ f) (Y₀ + h • P₀ f) (Y₀ + h • P₀ (Q₀ f)) - (Y₀ + h • f)‖ =
      |h| * ‖(1 - P₀) ((1 - Q₀) f)‖ := by
  rw [parallelBUG_euler hc hPY hQY]
  have heq : tangent P₀ Q₀ (Y₀ + h • f) - (Y₀ + h • f) = -(h • ((1 - P₀) ((1 - Q₀) f))) := by
    simp only [tangent_apply, sub_apply, one_apply_eq_self, map_add, map_smul, map_sub, hPY, hQY,
      hc, smul_sub, smul_add]
    abel
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs]

/-- **Explicit-Euler XL step vs. the full Euler step.**  If the new left basis `Pa` contains the
old one (`Pa P₀ = P₀`) and the Euler K-step direction (`Pa (Q₀ f) = Q₀ f`), and `P₀ Y₀ = Y₀`, then
the explicit-Euler XL step (augmentation, then one explicit Euler L-step in the basis `Pa`)
`Ŷ₁ = Pa (Y₀ + h f)` satisfies `‖Ŷ₁ - (Y₀ + h f)‖ ≤ h ‖(1 - P₀)(1 - Q₀) f‖`. -/
theorem xl_euler_sub_euler {P₀ Q₀ Pa : E →L[ℝ] E} (hPa : IsOrthProj Pa)
    (hP : ∀ x, Pa (P₀ x) = P₀ x) {Y₀ f : E} (hPY : P₀ Y₀ = Y₀) (hKf : Pa (Q₀ f) = Q₀ f) {h : ℝ}
    (hh : 0 ≤ h) :
    ‖Pa (Y₀ + h • f) - (Y₀ + h • f)‖ ≤ h * ‖(1 - P₀) ((1 - Q₀) f)‖ := by
  have hY : Pa Y₀ = Y₀ := by rw [← hPY, hP]
  have heq : Pa (Y₀ + h • f) - (Y₀ + h • f) = -(h • (1 - Pa) ((1 - P₀) ((1 - Q₀) f))) := by
    simp only [map_add, map_smul, hY, sub_apply, one_apply_eq_self, map_sub, hP, hKf, smul_sub]
    abel
  rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left (hPa.compl.norm_le _) hh

/-- **The sXL step is the full Euler step** (arXiv 2502.08951, Sec. 2, separable fields
`F(K Vᵀ) = 𝒦(K) 𝒱(V)ᵀ`): the augmented basis `X̂ = orth[Xⁿ, 𝒦(Xⁿ Sⁿ)]` contains the range of
`f = F(Yⁿ)`, i.e. `Pa f = f`, and `Pa Y₀ = Y₀`; then the untruncated sXL step `Pa (Y₀ + h f)`
*equals* the full explicit Euler step `Y₀ + h f`. -/
theorem sxl_euler_eq {Pa : E →L[ℝ] E} {Y₀ f : E} (hY : Pa Y₀ = Y₀) (hf : Pa f = f) (h : ℝ) :
    Pa (Y₀ + h • f) = Y₀ + h • f := by
  rw [map_add, map_smul, hY, hf]

omit [InnerProductSpace ℝ E] in
/-- **Comparison of a perturbed iteration with a stable one-step method** (discrete Grönwall).
Let the one-step maps `Φ n` be `(1 + C h)`-Lipschitz (`C, h ≥ 0`), `u (n+1) = Φ n (u n)`, and
`‖Y (n+1) - Φ n (Y n)‖ ≤ η`.  Then `‖Y n - u n‖ ≤ e^{C n h} (‖Y 0 - u 0‖ + n η)` for `n ≤ N`. -/
theorem perturbed_iteration_le {Φ : ℕ → E → E} {C h η : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h)
    (hη : 0 ≤ η) {N : ℕ} (hΦ : ∀ n < N, ∀ x y, ‖Φ n x - Φ n y‖ ≤ (1 + C * h) * ‖x - y‖)
    {u Y : ℕ → E} (hu : ∀ n < N, u (n + 1) = Φ n (u n))
    (hY : ∀ n < N, ‖Y (n + 1) - Φ n (Y n)‖ ≤ η) :
    ∀ n ≤ N, ‖Y n - u n‖ ≤ Real.exp (C * (n * h)) * (‖Y 0 - u 0‖ + n * η) := by
  refine discrete_gronwall_exp_le (e := fun n => ‖Y n - u n‖) hC hh hη fun n hn => ?_
  have hexp : 1 + C * h ≤ Real.exp (C * h) := by linarith [Real.add_one_le_exp (C * h)]
  have hsplit : Y (n + 1) - u (n + 1) = (Y (n + 1) - Φ n (Y n)) + (Φ n (Y n) - Φ n (u n)) := by
    rw [hu n hn]; abel
  change ‖Y (n + 1) - u (n + 1)‖ ≤ Real.exp (C * h) * ‖Y n - u n‖ + η
  rw [hsplit]
  calc _ ≤ ‖Y (n + 1) - Φ n (Y n)‖ + ‖Φ n (Y n) - Φ n (u n)‖ := norm_add_le _ _
    _ ≤ η + (1 + C * h) * ‖Y n - u n‖ := add_le_add (hY n hn) (hΦ n hn _ _)
    _ ≤ η + Real.exp (C * h) * ‖Y n - u n‖ := by gcongr
    _ = _ := by ring

/-- **OP-ST-01: Lipschitz-free global comparison of the explicit-Euler augmented BUG integrator
with the full explicit Euler scheme.**  Let the full Euler map `Y ↦ Y + h F(tₙ, Y)` be
`(1 + C h)`-Lipschitz (e.g. under the CFL condition of the full scheme; `C = 0` for a
non-expansive scheme) and `uₙ₊₁ = uₙ + h F(tₙ, uₙ)`.  At step `n` the iterate `Y n` lies in the
old bases `P n`, `Q n`; the augmented bases `Pa n ⊇ [P n, Q n fₙ]`, `Qa n ⊇ [Q n, P n fₙ]`
(`fₙ = F(tₙ, Y n)`) are commuting orthogonal projectors; the doubly normal component satisfies
`‖(1 - P n)(1 - Q n) fₙ‖ ≤ ε`; and the truncation obeys
`‖Y (n+1) - Pa n Qa n (Y n + h fₙ)‖ ≤ θ`.  Then for `n ≤ N`, with `tₙ - t₀ = n h`,
`‖Y n - u n‖ ≤ e^{C n h} (‖Y 0 - u 0‖ + n h ε + n θ)`.
No Lipschitz constant of `F` (which is `~ 1/Δx` for kinetic equations) enters. -/
theorem augmentedBug_euler_global_vs_euler {F : ℝ → E → E} {C h t₀ ε θ : ℝ} (hC : 0 ≤ C)
    (hh : 0 ≤ h) (hε : 0 ≤ ε) (hθ : 0 ≤ θ) {N : ℕ}
    (hΦ : ∀ n < N, ∀ x y, ‖(x + h • F (t₀ + n * h) x) - (y + h • F (t₀ + n * h) y)‖ ≤
      (1 + C * h) * ‖x - y‖)
    {u Y : ℕ → E} (hu : ∀ n < N, u (n + 1) = u n + h • F (t₀ + n * h) (u n))
    {P Q Pa Qa : ℕ → E →L[ℝ] E} (hPa : ∀ n, IsOrthProj (Pa n)) (hQa : ∀ n, IsOrthProj (Qa n))
    (hc₁ : ∀ n x, Pa n (Qa n x) = Qa n (Pa n x)) (hP : ∀ n x, Pa n (P n x) = P n x)
    (hQ : ∀ n x, Qa n (Q n x) = Q n x) (hc : ∀ n x, P n (Qa n x) = Qa n (P n x))
    (hPY : ∀ n < N, P n (Y n) = Y n) (hQY : ∀ n < N, Q n (Y n) = Y n)
    (hKf : ∀ n < N, Pa n (Q n (F (t₀ + n * h) (Y n))) = Q n (F (t₀ + n * h) (Y n)))
    (hLf : ∀ n < N, Qa n (P n (F (t₀ + n * h) (Y n))) = P n (F (t₀ + n * h) (Y n)))
    (hX : ∀ n < N, ‖(1 - P n) ((1 - Q n) (F (t₀ + n * h) (Y n)))‖ ≤ ε)
    (htr : ∀ n < N, ‖Y (n + 1) - Pa n (Qa n (Y n + h • F (t₀ + n * h) (Y n)))‖ ≤ θ) :
    ∀ n ≤ N, ‖Y n - u n‖ ≤ Real.exp (C * (n * h)) * (‖Y 0 - u 0‖ + n * h * ε + n * θ) := by
  intro n hn
  have := perturbed_iteration_le (Φ := fun n x => x + h • F (t₀ + n * h) x) hC hh
    (add_nonneg (mul_nonneg hh hε) hθ) hΦ hu (Y := Y) (fun k hk => by
      have h1 := augmentedBug_euler_sub_euler (hPa k) (hQa k) (hc₁ k) (hP k) (hQ k) (hc k)
        (hPY k hk) (hQY k hk) (hKf k hk) (hLf k hk) hh
      have h2 := norm_sub_le_of_le_of_le (htr k hk)
        (h1.trans (mul_le_mul_of_nonneg_left (hX k hk) hh))
      linarith) n hn
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **OP-ST-01, parallel BUG version.**  The parallel BUG integrator with explicit Euler substeps
(commuting `P n`, `Q n` fixing `Y n`) and truncation tolerance `θ` satisfies, against the full
explicit Euler iterates of a `(1 + C h)`-Lipschitz Euler map,
`‖Y n - u n‖ ≤ e^{C n h} (‖Y 0 - u 0‖ + n h ε + n θ)` with `ε` bounding the doubly normal
components `‖(1 - P n)(1 - Q n) F(tₙ, Y n)‖`. -/
theorem parallelBUG_euler_global_vs_euler {F : ℝ → E → E} {C h t₀ ε θ : ℝ} (hC : 0 ≤ C)
    (hh : 0 ≤ h) (hε : 0 ≤ ε) (hθ : 0 ≤ θ) {N : ℕ}
    (hΦ : ∀ n < N, ∀ x y, ‖(x + h • F (t₀ + n * h) x) - (y + h • F (t₀ + n * h) y)‖ ≤
      (1 + C * h) * ‖x - y‖)
    {u Y : ℕ → E} (hu : ∀ n < N, u (n + 1) = u n + h • F (t₀ + n * h) (u n))
    {P Q : ℕ → E →L[ℝ] E} (hc : ∀ n x, P n (Q n x) = Q n (P n x))
    (hPY : ∀ n < N, P n (Y n) = Y n) (hQY : ∀ n < N, Q n (Y n) = Y n)
    (hX : ∀ n < N, ‖(1 - P n) ((1 - Q n) (F (t₀ + n * h) (Y n)))‖ ≤ ε)
    (htr : ∀ n < N, ‖Y (n + 1) - parallelBUG (P n) (Q n)
      (Y n + h • Q n (F (t₀ + n * h) (Y n))) (Y n + h • P n (F (t₀ + n * h) (Y n)))
      (Y n + h • P n (Q n (F (t₀ + n * h) (Y n))))‖ ≤ θ) :
    ∀ n ≤ N, ‖Y n - u n‖ ≤ Real.exp (C * (n * h)) * (‖Y 0 - u 0‖ + n * h * ε + n * θ) := by
  intro n hn
  have := perturbed_iteration_le (Φ := fun n x => x + h • F (t₀ + n * h) x) hC hh
    (add_nonneg (mul_nonneg hh hε) hθ) hΦ hu (Y := Y) (fun k hk => by
      have h1 := parallelBUG_euler_sub_euler (hc k) (hPY k hk) (hQY k hk) h
        (F (t₀ + k * h) (Y k))
      rw [abs_of_nonneg hh] at h1
      have h2 := norm_sub_le_of_le_of_le (htr k hk)
        (h1.le.trans (mul_le_mul_of_nonneg_left (hX k hk) hh))
      linarith) n hn
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Explicit-Euler XL/sXL vs. the full explicit Euler scheme** (Lipschitz-free).  With the
augmented left bases `Pa n ⊇ [P n, Q n fₙ]` (explicit Euler K-step; for sXL with separable fields
even `Pa n fₙ = fₙ`), `P n (Y n) = Y n`, doubly normal components `≤ ε` and truncation `≤ θ`,
`‖Y n - u n‖ ≤ e^{C n h} (‖Y 0 - u 0‖ + n h ε + n θ)`. -/
theorem xl_euler_global_vs_euler {F : ℝ → E → E} {C h t₀ ε θ : ℝ} (hC : 0 ≤ C)
    (hh : 0 ≤ h) (hε : 0 ≤ ε) (hθ : 0 ≤ θ) {N : ℕ}
    (hΦ : ∀ n < N, ∀ x y, ‖(x + h • F (t₀ + n * h) x) - (y + h • F (t₀ + n * h) y)‖ ≤
      (1 + C * h) * ‖x - y‖)
    {u Y : ℕ → E} (hu : ∀ n < N, u (n + 1) = u n + h • F (t₀ + n * h) (u n))
    {P Q Pa : ℕ → E →L[ℝ] E} (hPa : ∀ n, IsOrthProj (Pa n)) (hP : ∀ n x, Pa n (P n x) = P n x)
    (hPY : ∀ n < N, P n (Y n) = Y n)
    (hKf : ∀ n < N, Pa n (Q n (F (t₀ + n * h) (Y n))) = Q n (F (t₀ + n * h) (Y n)))
    (hX : ∀ n < N, ‖(1 - P n) ((1 - Q n) (F (t₀ + n * h) (Y n)))‖ ≤ ε)
    (htr : ∀ n < N, ‖Y (n + 1) - Pa n (Y n + h • F (t₀ + n * h) (Y n))‖ ≤ θ) :
    ∀ n ≤ N, ‖Y n - u n‖ ≤ Real.exp (C * (n * h)) * (‖Y 0 - u 0‖ + n * h * ε + n * θ) := by
  intro n hn
  have := perturbed_iteration_le (Φ := fun n x => x + h • F (t₀ + n * h) x) hC hh
    (add_nonneg (mul_nonneg hh hε) hθ) hΦ hu (Y := Y) (fun k hk => by
      have h1 := xl_euler_sub_euler (hPa k) (hP k) (hPY k hk) (hKf k hk) hh
      have h2 := norm_sub_le_of_le_of_le (htr k hk)
        (h1.trans (mul_le_mul_of_nonneg_left (hX k hk) hh))
      linarith) n hn
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **One step of the rank-adaptive SAT scheme vs. full forward Euler** (arXiv 2609.02721,
proof of Theorem 4.3, eq. (4.1)).  If `P`, `Q` are commuting orthogonal projectors (`X̃ X̃ᵀ ·` and
`· Ṽ Ṽᵀ`), `P Q U = U`, and some `G` in the Galerkin space (the `ε₁`-truncated SVD of the
right-hand side) is `ε₁`-close to `f = F(tₙ, U)`, then
`‖P Q (U + τ f) - (U + τ f)‖ ≤ τ ε₁`. -/
theorem sat_step_sub_euler {P Q : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (hc : ∀ x, P (Q x) = Q (P x)) {U f G : E} (hU : P (Q U) = U) (hG : P (Q G) = G)
    {ε₁ τ : ℝ} (hfG : ‖f - G‖ ≤ ε₁) (hτ : 0 ≤ τ) :
    ‖P (Q (U + τ • f)) - (U + τ • f)‖ ≤ τ * ε₁ := by
  have hR := hP.mul hQ hc
  have h1 : ‖f - P (Q f)‖ ≤ ‖f - G‖ := hR.norm_sub_le_of_mem_range f G hG
  have heq : P (Q (U + τ • f)) - (U + τ • f) = -(τ • (f - P (Q f))) := by
    simp only [map_add, map_smul, hU, smul_sub]; abel
  rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg hτ]
  exact mul_le_mul_of_nonneg_left (h1.trans hfG) hτ

/-- **Theorem 4.3 of arXiv 2609.02721, generalized** (rank-adaptive SAT scheme vs. the fully
discrete forward Euler scheme).  The full Euler map `Y ↦ Y + τ F(tₙ, Y)` is `(1 + C τ)`-Lipschitz;
`Ufₙ` are its iterates; the SAT iterates `Uₙ` satisfy, at each step, the hypotheses of
`sat_step_sub_euler` with tolerance `ε₁` and the final truncation `‖Uₙ₊₁ - Ũₙ₊₁‖ ≤ ε₂`.  Then
`‖Uₙ - Ufₙ‖ ≤ e^{C n τ} (‖U₀ - Uf₀‖ + n τ ε₁ + n ε₂)`. -/
theorem sat_global_error {F : ℝ → E → E} {C τ t₀ ε₁ ε₂ : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) {N : ℕ}
    (hΦ : ∀ n < N, ∀ x y, ‖(x + τ • F (t₀ + n * τ) x) - (y + τ • F (t₀ + n * τ) y)‖ ≤
      (1 + C * τ) * ‖x - y‖)
    {Uf U G : ℕ → E} (hUf : ∀ n < N, Uf (n + 1) = Uf n + τ • F (t₀ + n * τ) (Uf n))
    {P Q : ℕ → E →L[ℝ] E} (hP : ∀ n, IsOrthProj (P n)) (hQ : ∀ n, IsOrthProj (Q n))
    (hc : ∀ n x, P n (Q n x) = Q n (P n x)) (hU : ∀ n < N, P n (Q n (U n)) = U n)
    (hG : ∀ n < N, P n (Q n (G n)) = G n)
    (hfG : ∀ n < N, ‖F (t₀ + n * τ) (U n) - G n‖ ≤ ε₁)
    (htr : ∀ n < N, ‖U (n + 1) - P n (Q n (U n + τ • F (t₀ + n * τ) (U n)))‖ ≤ ε₂) :
    ∀ n ≤ N, ‖U n - Uf n‖ ≤ Real.exp (C * (n * τ)) * (‖U 0 - Uf 0‖ + n * τ * ε₁ + n * ε₂) := by
  intro n hn
  have := perturbed_iteration_le (Φ := fun n x => x + τ • F (t₀ + n * τ) x) hC hτ
    (add_nonneg (mul_nonneg hτ hε₁) hε₂) hΦ hUf (Y := U) (fun k hk => by
      have h1 := sat_step_sub_euler (hP k) (hQ k) (hc k) (hU k hk) (hG k hk) (hfG k hk) hτ
      have h2 := norm_sub_le_of_le_of_le (htr k hk) h1
      linarith) n hn
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Theorem 4.3 of arXiv 2609.02721, verbatim form** (non-expansive full scheme, `C = 0`):
`‖Uₙ - Ufₙ‖ ≤ δ + tₙ ε₁ + (tₙ / τ) ε₂ ≤ δ + T ε₁ + (T / τ) ε₂` for `tₙ = n τ ≤ T`. -/
theorem sat_global_error_paper {F : ℝ → E → E} {τ t₀ ε₁ ε₂ δ T : ℝ} (hτ : 0 < τ)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) {N : ℕ}
    (hΦ : ∀ n < N, ∀ x y, ‖(x + τ • F (t₀ + n * τ) x) - (y + τ • F (t₀ + n * τ) y)‖ ≤ ‖x - y‖)
    {Uf U G : ℕ → E} (hUf : ∀ n < N, Uf (n + 1) = Uf n + τ • F (t₀ + n * τ) (Uf n))
    {P Q : ℕ → E →L[ℝ] E} (hP : ∀ n, IsOrthProj (P n)) (hQ : ∀ n, IsOrthProj (Q n))
    (hc : ∀ n x, P n (Q n x) = Q n (P n x)) (hU : ∀ n < N, P n (Q n (U n)) = U n)
    (hG : ∀ n < N, P n (Q n (G n)) = G n)
    (hfG : ∀ n < N, ‖F (t₀ + n * τ) (U n) - G n‖ ≤ ε₁)
    (htr : ∀ n < N, ‖U (n + 1) - P n (Q n (U n + τ • F (t₀ + n * τ) (U n)))‖ ≤ ε₂)
    (hδ : ‖U 0 - Uf 0‖ ≤ δ) :
    ∀ n ≤ N, ‖U n - Uf n‖ ≤ δ + n * τ * ε₁ + n * τ / τ * ε₂ ∧
      ((n : ℝ) * τ ≤ T → ‖U n - Uf n‖ ≤ δ + T * ε₁ + T / τ * ε₂) := by
  intro n hn
  have h := sat_global_error (C := 0) le_rfl hτ.le hε₁ hε₂ (fun k hk x y => by
    simpa using hΦ k hk x y) hUf hP hQ hc hU hG hfG htr n hn
  rw [zero_mul, Real.exp_zero, one_mul] at h
  have hnτ : (n : ℝ) * τ / τ = n := by field_simp
  refine ⟨by rw [hnτ]; linarith, fun hT => ?_⟩
  have h1 : (n : ℝ) * τ * ε₁ ≤ T * ε₁ := mul_le_mul_of_nonneg_right hT hε₁
  have h2 : (n : ℝ) * ε₂ ≤ T / τ * ε₂ := by
    refine mul_le_mul_of_nonneg_right ?_ hε₂
    rw [le_div_iff₀ hτ]; exact hT
  linarith

omit [InnerProductSpace ℝ E] in
/-- **Tolerance-scaling corollary of Theorem 4.3** (arXiv 2609.02721, after Theorem 4.3).  If
the full forward Euler scheme converges with `‖A(tₙ) - Ufₙ‖ ≤ C τ`, the low-rank iterates obey the
bound of Theorem 4.3, `‖Uₙ - Ufₙ‖ ≤ δ + tₙ ε₁ + n ε₂`, and the tolerances are chosen as
`δ ≤ C τ / 3`, `ε₁ = C τ / (3 T)`, `ε₂ = C τ² / (3 T)`, then `‖A(tₙ) - Uₙ‖ ≤ 2 C τ` for
`tₙ = n τ ≤ T`. -/
theorem sat_tolerance_scaling {A : ℝ → E} {Uf U : ℕ → E} {C τ T δ ε₁ ε₂ t₀ : ℝ} (hC : 0 ≤ C)
    (hτ : 0 < τ) (hT : 0 < T) (hδ : δ ≤ C * τ / 3) (hε₁ : ε₁ = C * τ / (3 * T))
    (hε₂ : ε₂ = C * τ ^ 2 / (3 * T)) {n : ℕ} (hnT : (n : ℝ) * τ ≤ T)
    (hfull : ‖A (t₀ + n * τ) - Uf n‖ ≤ C * τ)
    (hlr : ‖U n - Uf n‖ ≤ δ + n * τ * ε₁ + n * ε₂) :
    ‖A (t₀ + n * τ) - U n‖ ≤ 2 * (C * τ) := by
  have hCτ : 0 ≤ C * τ := mul_nonneg hC hτ.le
  have h1 : (n : ℝ) * τ * ε₁ ≤ C * τ / 3 := by
    rw [hε₁]
    calc (n : ℝ) * τ * (C * τ / (3 * T)) ≤ T * (C * τ / (3 * T)) := by gcongr
      _ = C * τ / 3 := by field_simp
  have h2 : (n : ℝ) * ε₂ ≤ C * τ / 3 := by
    rw [hε₂]
    calc (n : ℝ) * (C * τ ^ 2 / (3 * T)) = (n * τ) * (C * τ / (3 * T)) := by ring
      _ ≤ T * (C * τ / (3 * T)) := by gcongr
      _ = C * τ / 3 := by field_simp
  calc ‖A (t₀ + n * τ) - U n‖ ≤ ‖A (t₀ + n * τ) - Uf n‖ + ‖U n - Uf n‖ := by
        rw [← norm_neg (U n - Uf n), neg_sub]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * τ + (C * τ / 3 + C * τ / 3 + C * τ / 3) := by linarith
    _ = 2 * (C * τ) := by ring

end Comparison

/-! ### OP-ST-01 in matrix form -/

section MatrixForm

open scoped Matrix LeanDLRA.Frobenius

variable {m n k k' k₂ k₂' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k']
  [Fintype k₂] [Fintype k₂'] [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq k']
  [DecidableEq k₂] [DecidableEq k₂']

/-- **OP-ST-01, matrix form** (one step).  Let `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀`, let
`F = F(t₀, Y₀) ∈ ℝ^{m×n}`, and let `Û`, `V̂` be orthonormal augmented bases with
`range Û ⊇ range [U₀, F V₀]` and `range V̂ ⊇ range [V₀, Fᵀ U₀]` (e.g. `Û = orth[U₀, K₁]`,
`K₁ = U₀ S₀ + h F V₀`, as in the augmented BUG with explicit Euler substeps).  Then the untruncated
step `Ŷ₁ = Û Ûᵀ (Y₀ + h F) V̂ V̂ᵀ` deviates from the full explicit Euler step by at most `h` times
the doubly normal component: `‖Ŷ₁ - (Y₀ + h F)‖_F ≤ h ‖(I - U₀U₀ᵀ) F (I - V₀V₀ᵀ)‖_F`. -/
theorem matrix_augmentedBug_euler_sub_euler {U₀ : Matrix m k ℝ} {V₀ : Matrix n k' ℝ}
    {Ua : Matrix m k₂ ℝ} {Va : Matrix n k₂' ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hUa : Uaᵀ * Ua = 1) (hVa : Vaᵀ * Va = 1) (hUU : Ua * Uaᵀ * U₀ = U₀)
    (hVV : Va * Vaᵀ * V₀ = V₀) (S₀ : Matrix k k' ℝ) (F : Matrix m n ℝ)
    (hK : Ua * Uaᵀ * (F * V₀) = F * V₀) (hL : Va * Vaᵀ * (Fᵀ * U₀) = Fᵀ * U₀) {h : ℝ}
    (hh : 0 ≤ h) :
    ‖Ua * Uaᵀ * (U₀ * S₀ * V₀ᵀ + h • F) * Va * Vaᵀ - (U₀ * S₀ * V₀ᵀ + h • F)‖ ≤
      h * ‖(1 - U₀ * U₀ᵀ) * F * (1 - V₀ * V₀ᵀ)‖ := by
  have hPY : leftProj U₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    rw [Matrix.mul_assoc]; exact leftProj_mul_left hU₀ _
  have hQY : rightProj V₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := rightProj_mul_transpose hV₀ _
  have hKf : leftProj Ua (rightProj V₀ F) = rightProj V₀ F := by
    simp only [leftProj_apply, rightProj_apply]
    rw [show Ua * Uaᵀ * (F * V₀ * V₀ᵀ) = Ua * Uaᵀ * (F * V₀) * V₀ᵀ by
      simp only [Matrix.mul_assoc], hK]
  have hL' : U₀ᵀ * F * Va * Vaᵀ = U₀ᵀ * F := by
    have := congrArg Matrix.transpose hL
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc (U₀ᵀ * F)]; exact this
  have hLf : rightProj Va (leftProj U₀ F) = leftProj U₀ F := by
    simp only [leftProj_apply, rightProj_apply]
    rw [show U₀ * U₀ᵀ * F * Va * Vaᵀ = U₀ * (U₀ᵀ * F * Va * Vaᵀ) by simp only [Matrix.mul_assoc],
      hL', Matrix.mul_assoc]
  have key := augmentedBug_euler_sub_euler (P₀ := leftProj U₀) (Q₀ := rightProj V₀)
    (P₁ := leftProj Ua) (Q₁ := rightProj Va) (isOrthProj_leftProj hUa)
    (isOrthProj_rightProj hVa) (leftProj_rightProj_comm Ua Va) (leftProj_leftProj_of_mul hUU)
    (rightProj_rightProj_of_mul hVV) (leftProj_rightProj_comm U₀ Va) hPY hQY hKf hLf hh
  rw [one_sub_leftProj_one_sub_rightProj_apply] at key
  have e : ∀ X : Matrix m n ℝ, leftProj Ua (rightProj Va X) = Ua * Uaᵀ * X * Va * Vaᵀ := by
    intro X; simp [Matrix.mul_assoc]
  rwa [e] at key

end MatrixForm

/-! ### Robust bounds against the exact solution through the full Euler step -/

section ViaEuler

variable {F : ℝ → E → E} {L B Lt ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {Y₀ : E}

/-- **From the full Euler step to the exact flow.**  If a computed step `Y₁` is `η`-close to the
full explicit Euler step `Y₀ + h F(t₀, Y₀)`, then `‖Y₁ - A(t₁)‖ ≤ η + (L B + Lₜ) h² / 2`. -/
theorem norm_sub_exact_le_of_sub_euler (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = Y₀) (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {Y₁ : E}
    {η : ℝ} (hη : ‖Y₁ - (Y₀ + h • F t₀ Y₀)‖ ≤ η) :
    ‖Y₁ - A t₁‖ ≤ η + (L * B + Lt) * h ^ 2 / 2 := by
  have hdef := euler_defect_le hF hL hB ht₁ hh hA (by rw [hA₀]; exact hFt)
  rw [hA₀, norm_sub_rev] at hdef
  exact norm_sub_le_of_le_of_le hη hdef

/-- **Robust local error of the explicit-Euler augmented (rank-adaptive) BUG step**
(arXiv 2502.07040, Sec. 2.1, Algorithm 1; arXiv 2104.05247 with Euler substeps).  With the
augmented bases `P₁ ⊇ [P₀, Q₀ f]`, `Q₁ ⊇ [Q₀, P₀ f]`, `f = F(t₀, Y₀)`, doubly normal component
`‖(1 - P₀)(1 - Q₀) f‖ ≤ ε` and truncation `‖Y₁ - P₁ Q₁ (Y₀ + h f)‖ ≤ ϑ_tr`:
`‖Y₁ - A(t₁)‖ ≤ h ε + (L B + Lₜ) h² / 2 + ϑ_tr`.  The constant in front of `h ε` is `1` (compare
`2` in `eulerBug_local_error` and `2 + O(h)` for exact substeps). -/
theorem augmentedBug_euler_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₁ : IsOrthProj Q₁) (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (hP : ∀ x, P₁ (P₀ x) = P₀ x)
    (hQ : ∀ x, Q₁ (Q₀ x) = Q₀ x) (hc : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) (hPY : P₀ Y₀ = Y₀)
    (hQY : Q₀ Y₀ = Y₀) (hKf : P₁ (Q₀ (F t₀ Y₀)) = Q₀ (F t₀ Y₀))
    (hLf : Q₁ (P₀ (F t₀ Y₀)) = P₀ (F t₀ Y₀)) (hX : ‖(1 - P₀) ((1 - Q₀) (F t₀ Y₀))‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {Y₁ : E} {θtr : ℝ}
    (htr : ‖Y₁ - P₁ (Q₁ (Y₀ + h • F t₀ Y₀))‖ ≤ θtr) :
    ‖Y₁ - A t₁‖ ≤ h * ε + (L * B + Lt) * h ^ 2 / 2 + θtr := by
  have h1 := augmentedBug_euler_sub_euler hP₁ hQ₁ hc₁ hP hQ hc hPY hQY hKf hLf hh
  have h2 := norm_sub_le_of_le_of_le htr (h1.trans (mul_le_mul_of_nonneg_left hX hh))
  have := norm_sub_exact_le_of_sub_euler hF hL hB ht₁ hh hA hA₀ hFt h2
  linarith

/-- **Robust global error of the explicit-Euler augmented BUG integrator**: with the hypotheses
of `augmentedBug_euler_local_error` at every step and `Φ n` the exact flow from `(tₙ, Y n)`,
`‖Y n - A(tₙ)‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n (h ε + (L B + Lₜ) h² / 2 + ϑ_tr))`. -/
theorem augmentedBug_euler_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hh : 0 ≤ h) {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E} {Φ : ℕ → ℝ → E} (hPa : ∀ n, IsOrthProj (Pa n))
    (hQa : ∀ n, IsOrthProj (Qa n)) (hc₁ : ∀ n x, Pa n (Qa n x) = Qa n (Pa n x))
    (hP : ∀ n x, Pa n (P n x) = P n x) (hQ : ∀ n x, Qa n (Q n x) = Q n x)
    (hc : ∀ n x, P n (Qa n x) = Qa n (P n x))
    (hPY : ∀ n < N, P n (Y n) = Y n) (hQY : ∀ n < N, Q n (Y n) = Y n)
    (hKf : ∀ n < N, Pa n (Q n (F (t₀ + n * h) (Y n))) = Q n (F (t₀ + n * h) (Y n)))
    (hLf : ∀ n < N, Qa n (P n (F (t₀ + n * h) (Y n))) = P n (F (t₀ + n * h) (Y n)))
    (hX : ∀ n < N, ‖(1 - P n) ((1 - Q n) (F (t₀ + n * h) (Y n)))‖ ≤ ε)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hFt : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (Y n) - F (t₀ + n * h) (Y n)‖ ≤ Lt * (t - (t₀ + n * h))) {θtr : ℝ}
    (htr : ∀ n < N, ‖Y (n + 1) - Pa n (Qa n (Y n + h • F (t₀ + n * h) (Y n)))‖ ≤ θtr) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * (h * ε + (L * B + Lt) * h ^ 2 / 2 + θtr)) :=
  lady_windermere hF hL hh hA hΦ hΦ₀ fun n hn =>
    augmentedBug_euler_local_error hF hL hB (hPa n) (hQa n) (hc₁ n) (hP n) (hQ n) (hc n)
      (hPY n hn) (hQY n hn) (hKf n hn) (hLf n hn) (hX n hn) (by ring) hh (hΦ n hn) (hΦ₀ n hn)
      (hFt n hn) (htr n hn)

/-- **Robust local error of the parallel BUG step with explicit Euler substeps**: for commuting
`P₀`, `Q₀` fixing `Y₀`, `‖(1 - P₀)(1 - Q₀) F(t₀, Y₀)‖ ≤ ε` and truncation `≤ ϑ_tr`,
`‖Y₁ - A(t₁)‖ ≤ h ε + (L B + Lₜ) h² / 2 + ϑ_tr` (compare `h ((7 L B + Lₜ) h + ε)` for exactly
solved substeps, `parallelBUG_local_error_of_timeLipschitz`). -/
theorem parallelBUG_euler_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {P₀ Q₀ : E →L[ℝ] E} (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x))
    (hPY : P₀ Y₀ = Y₀) (hQY : Q₀ Y₀ = Y₀) (hX : ‖(1 - P₀) ((1 - Q₀) (F t₀ Y₀))‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {Y₁ : E} {θtr : ℝ}
    (htr : ‖Y₁ - parallelBUG P₀ Q₀ (Y₀ + h • Q₀ (F t₀ Y₀)) (Y₀ + h • P₀ (F t₀ Y₀))
      (Y₀ + h • P₀ (Q₀ (F t₀ Y₀)))‖ ≤ θtr) :
    ‖Y₁ - A t₁‖ ≤ h * ε + (L * B + Lt) * h ^ 2 / 2 + θtr := by
  have h1 := parallelBUG_euler_sub_euler hc hPY hQY h (F t₀ Y₀)
  rw [abs_of_nonneg hh] at h1
  have h2 := norm_sub_le_of_le_of_le htr (h1.le.trans (mul_le_mul_of_nonneg_left hX hh))
  have := norm_sub_exact_le_of_sub_euler hF hL hB ht₁ hh hA hA₀ hFt h2
  linarith

/-- **Explicit-Euler projector-splitting (KSL) step vs. the full Euler step** (OP-OT-01, KSL
part).  For a frozen field `G` (`L`-Lipschitz, bounded by `B`) and a new basis `P₁` capturing the
Euler K-step `Y₀ + h Q₀ G(Y₀)`, the step `kslEulerStep P₁ Q₀ G h Y₀` (K-, backward S- and
L-substep, one explicit Euler step each) satisfies
`‖Y₁ - (Y₀ + h G Y₀)‖ ≤ h (‖(1 - P₁)(1 - Q₀) G Y₀‖ + 3 L B h)`. -/
theorem kslEuler_sub_euler {G : E → E} (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hGB : ∀ x, ‖G x‖ ≤ B) (hL : 0 ≤ L) {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁)
    (hQ₀ : IsOrthProj Q₀) (hh : 0 ≤ h) (hKcap : P₁ (Y₀ + h • Q₀ (G Y₀)) = Y₀ + h • Q₀ (G Y₀)) :
    ‖kslEulerStep P₁ Q₀ G h Y₀ - (Y₀ + h • G Y₀)‖ ≤
      h * (‖(1 - P₁) ((1 - Q₀) (G Y₀))‖ + 3 * L * B * h) := by
  set z := Y₀ + h • Q₀ (G Y₀) with hz
  set w := z - h • P₁ (Q₀ (G z)) with hw
  have hstep : kslEulerStep P₁ Q₀ G h Y₀ = w + h • P₁ (G w) := by
    change kslL P₁ G h (kslS P₁ Q₀ G h z) = _
    simp only [kslS, kslL, hKcap, hw]
  have alg : ∀ gz gw : E, (z - h • P₁ (Q₀ gz)) + h • P₁ gw - (Y₀ + h • G Y₀) =
      h • (P₁ (Q₀ (G Y₀ - gz)) + P₁ (gw - G Y₀) - (1 - P₁) ((1 - Q₀) (G Y₀))) := by
    intro gz gw
    simp only [hz, map_sub, sub_apply, one_apply_eq_self, smul_sub, smul_add]
    abel
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hGB Y₀)
  have hzY : ‖Y₀ - z‖ ≤ h * B := by
    rw [hz, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left ((hQ₀.norm_le _).trans (hGB _)) hh
  have hwY : ‖w - Y₀‖ ≤ 2 * (h * B) := by
    have : w - Y₀ = h • Q₀ (G Y₀) - h • P₁ (Q₀ (G z)) := by rw [hw, hz]; abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hh]
    have h1 : ‖Q₀ (G Y₀)‖ ≤ B := (hQ₀.norm_le _).trans (hGB _)
    have h2 : ‖P₁ (Q₀ (G z))‖ ≤ B := (hP₁.norm_le _).trans ((hQ₀.norm_le _).trans (hGB _))
    nlinarith
  rw [hstep, alg, norm_smul, Real.norm_of_nonneg hh]
  refine mul_le_mul_of_nonneg_left ?_ hh
  have e1 : ‖P₁ (Q₀ (G Y₀ - G z))‖ ≤ L * (h * B) :=
    (hP₁.norm_le _).trans ((hQ₀.norm_le _).trans ((hG _ _).trans
      (mul_le_mul_of_nonneg_left hzY hL)))
  have e2 : ‖P₁ (G w - G Y₀)‖ ≤ L * (2 * (h * B)) :=
    (hP₁.norm_le _).trans ((hG _ _).trans (mul_le_mul_of_nonneg_left hwY hL))
  calc _ ≤ ‖P₁ (Q₀ (G Y₀ - G z)) + P₁ (G w - G Y₀)‖ + ‖(1 - P₁) ((1 - Q₀) (G Y₀))‖ :=
        norm_sub_le _ _
    _ ≤ L * (h * B) + L * (2 * (h * B)) + ‖(1 - P₁) ((1 - Q₀) (G Y₀))‖ := by
        gcongr; exact norm_add_le_of_le e1 e2
    _ = _ := by ring

/-- **Robust local error of the explicit-Euler KSL step** (OP-OT-01, KSL part; compare
Kieri–Lubich–Walach 2016, Thm 2.1, `h (11 L B h + ε)` for exactly solved substeps).  With the
normal-component assumption at the K-step point (factored form) and the new basis capturing the
Euler K-step: `‖Y₁ - A(t₁)‖ ≤ h (ε + (9 L B + Lₜ) h / 2)` for
`Y₁ = kslEulerStep P₁ Q₀ (F t₀) h Y₀`. -/
theorem kslEuler_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hKcap : P₁ (Y₀ + h • Q₀ (F t₀ Y₀)) = Y₀ + h • Q₀ (F t₀ Y₀))
    (hε : ‖(1 - P₁) ((1 - Q₀) (F t₀ (Y₀ + h • Q₀ (F t₀ Y₀))))‖ ≤ ε) :
    ‖kslEulerStep P₁ Q₀ (F t₀) h Y₀ - A t₁‖ ≤ h * (ε + (9 * L * B + Lt) * h / 2) := by
  have h1 := kslEuler_sub_euler (G := F t₀) (hF t₀) (hB t₀) hL hP₁ hQ₀ hh hKcap
  have hn := normal_le_of_normal_at_K hF hL hB hP₁ hQ₀ hh hε
  have h2 : ‖kslEulerStep P₁ Q₀ (F t₀) h Y₀ - (Y₀ + h • F t₀ Y₀)‖ ≤
      h * (ε + L * B * h + 3 * L * B * h) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) hh)
  have := norm_sub_exact_le_of_sub_euler hF hL hB ht₁ hh hA hA₀ hFt h2
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Robust global error of the explicit-Euler KSL integrator** (OP-OT-01, KSL part): on the
grid `tₙ = t₀ + n h` with step `n` from bases `Q n` (old right) and `P (n+1)` (new left,
capturing the Euler K-step), for `n ≤ N`, `n h ≤ T`:
`‖Y n - A(tₙ)‖ ≤ e^{L T} (‖Y 0 - A t₀‖ + T (ε + (9 L B + Lₜ) h / 2))`. -/
theorem kslEuler_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hLt : 0 ≤ Lt) (hε : 0 ≤ ε) (hh : 0 ≤ h) {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E} {Φ : ℕ → ℝ → E} (hP : ∀ n, IsOrthProj (P n))
    (hQ : ∀ n, IsOrthProj (Q n))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hFt : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (Y n) - F (t₀ + n * h) (Y n)‖ ≤ Lt * (t - (t₀ + n * h)))
    (hKcap : ∀ n < N, P (n + 1) (Y n + h • Q n (F (t₀ + n * h) (Y n))) =
      Y n + h • Q n (F (t₀ + n * h) (Y n)))
    (hεK : ∀ n < N, ‖(1 - P (n + 1)) ((1 - Q n)
      (F (t₀ + n * h) (Y n + h • Q n (F (t₀ + n * h) (Y n)))))‖ ≤ ε)
    (hY : ∀ n < N, Y (n + 1) = kslEulerStep (P (n + 1)) (Q n) (F (t₀ + n * h)) h (Y n))
    {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (ε + (9 * L * B + Lt) * h / 2)) := by
  have hB0 := hB.nonneg
  refine lady_windermere_of_le hF hL hh hA hΦ hΦ₀ (by positivity) fun n hn => ?_
  rw [hY n hn]
  exact kslEuler_local_error hF hL hB (hP (n + 1)) (hQ n) (by ring) hh (hΦ n hn) (hΦ₀ n hn)
    (hFt n hn) (hKcap n hn) (hεK n hn)

end ViaEuler

/-! ### XL, sXL and GAP integrators (OP-HO-07) -/

section XL

variable {F : ℝ → E → E} {L B Lt ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {Y₀ : E}

/-- **Robust local error of the XL integrator** (OP-HO-07; arXiv 2502.08951, Sec. 2).  K-step
`YK' = Q₀ F(t, YK)`, `YK t₀ = A t₀`; the new left basis `Pa` (an orthogonal projector) captures
`YK t₁` with normal-component bound `‖(1 - Pa)(1 - Q₀) F(t, YK t₁)‖ ≤ ε`; Galerkin L-step
`YL' = Pa F(t, YL)` from `YL t₀ = Pa (A t₀)` (`= A t₀` for the augmented basis `X̂ = [Xⁿ, K]` of
2502.08951); truncation `‖Y₁ - YL t₁‖ ≤ ϑ_tr`.  Then with `ϑ = h (4 L B h + ε)`,
`‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1)(B h + ϑ) + ϑ + ϑ_tr`. -/
theorem xl_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {Pa Q₀ : E →L[ℝ] E} (hPa : IsOrthProj Pa) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) {YK YL : ℝ → E}
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀)
    (hKcap : Pa (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - Pa) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hYL : ODESolution (fun t x => Pa (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = Pa (A t₀))
    {Y₁ : E} {θtr : ℝ} (htr : ‖Y₁ - YL t₁‖ ≤ θtr) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + h * (4 * L * B * h + ε))
      + h * (4 * L * B * h + ε) + θtr := by
  have hcap := kstep_capture hF hL hB hPa hQ₀ ht₁ hh hA hK hK₀ hKcap hε
  have hcap' : ‖A t₁ - Pa (A t₁)‖ ≤ h * (4 * L * B * h + ε) := by simpa using hcap
  have hg := galerkin_step_error hPa hF hL hB ht₁ hh hA hYL hL₀ hcap'
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YL t₁‖ + ‖YL t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Robust global error of the XL integrator** (OP-HO-07).  On the grid `tₙ = t₀ + n h`, step
`n` performs the XL step of `xl_local_error` from `Y n` (old right projector `Q n`, new left
projector `Pa n`), followed by a truncation with tolerance `ϑ_tr`.  With `Φ n` the exact flow from
`(tₙ, Y n)`: `‖Y n - A(tₙ)‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n ℓ)` with the local bound
`ℓ = (e^{L h} - 1)(B h + ϑ) + ϑ + ϑ_tr`, `ϑ = h (4 L B h + ε)`.  Since
`ℓ ≤ h (c₁ ε + c₂ h) + ϑ_tr` (`xl_bound_le`), this is `O(δ + ε + h + n ϑ_tr)`,
independent of singular values. -/
theorem xl_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hh : 0 ≤ h) {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h)) {Pa Q : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL Φ : ℕ → ℝ → E} (hPa : ∀ n, IsOrthProj (Pa n))
    (hQ : ∀ n, IsOrthProj (Q n))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hK : ∀ n < N, ODESolution (fun t x => Q n (F t x)) (YK n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hK₀ : ∀ n < N, YK n (t₀ + n * h) = Y n)
    (hKcap : ∀ n < N, Pa n (YK n (t₀ + (n + 1) * h)) = YK n (t₀ + (n + 1) * h))
    (hε : ∀ n < N, ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - Pa n) ((1 - Q n) (F t (YK n (t₀ + (n + 1) * h))))‖ ≤ ε)
    (hYL : ∀ n < N,
      ODESolution (fun t x => Pa n (F t x)) (YL n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hL₀ : ∀ n < N, YL n (t₀ + n * h) = Pa n (Y n)) {θtr : ℝ}
    (htr : ∀ n < N, ‖Y (n + 1) - YL n (t₀ + (n + 1) * h)‖ ≤ θtr) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ +
      n * ((Real.exp (L * h) - 1) * (B * h + h * (4 * L * B * h + ε))
        + h * (4 * L * B * h + ε) + θtr)) :=
  lady_windermere hF hL hh hA hΦ hΦ₀ fun n hn =>
    xl_local_error hF hL hB (hPa n) (hQ n) (by ring) hh (hΦ n hn) (hK n hn)
      ((hK₀ n hn).trans (hΦ₀ n hn).symm) (hKcap n hn) (hε n hn) (hYL n hn)
      (by rw [hL₀ n hn, hΦ₀ n hn]) (htr n hn)

/-- The XL local bound in `O`-form: `(e^{L h} - 1)(B h + ϑ) + ϑ ≤ h (c₁ ε + c₂ h)` with the BUG
constants `bugC₁`, `bugC₂` (for `0 ≤ h ≤ H`, `ε ≥ 0`). -/
theorem xl_bound_le {H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hh : 0 ≤ h) (hhH : h ≤ H) :
    (Real.exp (L * h) - 1) * (B * h + h * (4 * L * B * h + ε)) + h * (4 * L * B * h + ε) ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) := by
  have hϑ : 0 ≤ h * (4 * L * B * h + ε) := by positivity
  have he : 0 ≤ Real.exp (L * h) - 1 := by
    linarith [Real.one_le_exp (mul_nonneg hL hh)]
  have := bug_bound_le hL hB hε hh hhH
  nlinarith

/-- **Robust local error of the GAP integrator** (arXiv 2505.19929, Algorithm 2.3 and
Theorem 3.3, with explicit constants).  L-step `YL' = P₀ F(t, YL)`, `YL t₀ = A t₀`; the new right
basis `Q₁` captures `YL t₁` with `‖(1 - Q₁)(1 - P₀) F(t, YL t₁)‖ ≤ ε`; Galerkin K-step
`YK' = Q₁ F(t, YK)` from `YK t₀ = Q₁ (A t₀)`.  Then with `ϑ = h (4 L B h + ε)`,
`‖YK t₁ - A(t₁)‖ ≤ (e^{L h} - 1)(B h + ϑ) + ϑ`.  (GAP is XL with left and right exchanged, so this
is `xl_local_error` with `ϑ_tr = 0`.) -/
theorem gap_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {P₀ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀) (hQ₁ : IsOrthProj Q₁) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) {YK YL : ℝ → E}
    (hYL : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = A t₀)
    (hLcap : Q₁ (YL t₁) = YL t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hYK : ODESolution (fun t x => Q₁ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Q₁ (A t₀)) :
    ‖YK t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + h * (4 * L * B * h + ε))
      + h * (4 * L * B * h + ε) := by
  simpa using xl_local_error hF hL hB hQ₁ hP₀ ht₁ hh hA hYL hL₀ hLcap hε hYK hK₀
    (Y₁ := YK t₁) (θtr := 0) (by simp)

/-- **Global error of the GAP integrator** (arXiv 2505.19929, Corollary 3.4, with explicit
constants): `‖Y n - A(tₙ)‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n ((e^{L h} - 1)(B h + ϑ) + ϑ))`, i.e.
`O(δ + ε + h)` on bounded time intervals (cf. `xl_bound_le`). -/
theorem gap_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hh : 0 ≤ h) {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL Φ : ℕ → ℝ → E} (hP : ∀ n, IsOrthProj (P n))
    (hQ : ∀ n, IsOrthProj (Q n))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hYL : ∀ n < N,
      ODESolution (fun t x => P n (F t x)) (YL n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hL₀ : ∀ n < N, YL n (t₀ + n * h) = Y n)
    (hLcap : ∀ n < N, Q (n + 1) (YL n (t₀ + (n + 1) * h)) = YL n (t₀ + (n + 1) * h))
    (hε : ∀ n < N, ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - Q (n + 1)) ((1 - P n) (F t (YL n (t₀ + (n + 1) * h))))‖ ≤ ε)
    (hYK : ∀ n < N,
      ODESolution (fun t x => Q (n + 1) (F t x)) (YK n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hK₀ : ∀ n < N, YK n (t₀ + n * h) = Q (n + 1) (Y n))
    (hY : ∀ n < N, Y (n + 1) = YK n (t₀ + (n + 1) * h)) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ +
      n * ((Real.exp (L * h) - 1) * (B * h + h * (4 * L * B * h + ε))
        + h * (4 * L * B * h + ε))) :=
  lady_windermere hF hL hh hA hΦ hΦ₀ fun n hn => by
    rw [hY n hn]
    exact gap_local_error hF hL hB (hP n) (hQ (n + 1)) (by ring) hh (hΦ n hn) (hYL n hn)
      ((hL₀ n hn).trans (hΦ₀ n hn).symm) (hLcap n hn) (hε n hn) (hYK n hn)
      (by rw [hK₀ n hn, hΦ₀ n hn])

/-- **Robust local error of the sXL integrator** (OP-HO-07; arXiv 2502.08951, Sec. 2,
(2.9)–(2.11)): augmentation `Pa ⊇ [P₀, Q₀ F(t₀, Y₀)]` (for separable fields `Pa ⊇ range F(Y₀)`),
explicit Euler L-step `Ŷ₁ = Pa (Y₀ + h F(t₀, Y₀))`, truncation `‖Y₁ - Ŷ₁‖ ≤ ϑ_tr`.  With the
doubly normal component `‖(1 - P₀)(1 - Q₀) F(t₀, Y₀)‖ ≤ ε` (`ε = 0` for separable fields):
`‖Y₁ - A(t₁)‖ ≤ h ε + (L B + Lₜ) h² / 2 + ϑ_tr`. -/
theorem sxl_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {P₀ Q₀ Pa : E →L[ℝ] E} (hPa : IsOrthProj Pa) (hP : ∀ x, Pa (P₀ x) = P₀ x)
    (hPY : P₀ Y₀ = Y₀) (hKf : Pa (Q₀ (F t₀ Y₀)) = Q₀ (F t₀ Y₀))
    (hX : ‖(1 - P₀) ((1 - Q₀) (F t₀ Y₀))‖ ≤ ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) {Y₁ : E} {θtr : ℝ}
    (htr : ‖Y₁ - Pa (Y₀ + h • F t₀ Y₀)‖ ≤ θtr) :
    ‖Y₁ - A t₁‖ ≤ h * ε + (L * B + Lt) * h ^ 2 / 2 + θtr := by
  have h1 := xl_euler_sub_euler hPa hP hPY hKf hh
  have hdef := euler_defect_le hF hL hB ht₁ hh hA (by rw [hA₀]; exact hFt)
  rw [hA₀] at hdef
  have hdec : Y₁ - A t₁ = (Y₁ - Pa (Y₀ + h • F t₀ Y₀))
      + (Pa (Y₀ + h • F t₀ Y₀) - (Y₀ + h • F t₀ Y₀)) - (A t₁ - (Y₀ + h • F t₀ Y₀)) := by abel
  rw [hdec]
  calc _ ≤ ‖(Y₁ - Pa (Y₀ + h • F t₀ Y₀)) + (Pa (Y₀ + h • F t₀ Y₀) - (Y₀ + h • F t₀ Y₀))‖
        + ‖A t₁ - (Y₀ + h • F t₀ Y₀)‖ := norm_sub_le _ _
    _ ≤ θtr + h * ‖(1 - P₀) ((1 - Q₀) (F t₀ Y₀))‖ + (L * B + Lt) * h ^ 2 / 2 := by
        gcongr; exact norm_add_le_of_le htr h1
    _ ≤ θtr + h * ε + (L * B + Lt) * h ^ 2 / 2 := by gcongr
    _ = _ := by ring

/-- **Robust global error of the sXL integrator** (OP-HO-07): with the hypotheses of
`sxl_local_error` at every step and `Φ n` the exact flow from `(tₙ, Y n)`,
`‖Y n - A(tₙ)‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n (h ε + (L B + Lₜ) h² / 2 + ϑ_tr))`, i.e.
`O(δ + ε + h + n ϑ_tr)`. -/
theorem sxl_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hh : 0 ≤ h) {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {Φ : ℕ → ℝ → E} (hPa : ∀ n, IsOrthProj (Pa n))
    (hP : ∀ n x, Pa n (P n x) = P n x) (hPY : ∀ n < N, P n (Y n) = Y n)
    (hKf : ∀ n < N, Pa n (Q n (F (t₀ + n * h) (Y n))) = Q n (F (t₀ + n * h) (Y n)))
    (hX : ∀ n < N, ‖(1 - P n) ((1 - Q n) (F (t₀ + n * h) (Y n)))‖ ≤ ε)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    (hFt : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (Y n) - F (t₀ + n * h) (Y n)‖ ≤ Lt * (t - (t₀ + n * h))) {θtr : ℝ}
    (htr : ∀ n < N, ‖Y (n + 1) - Pa n (Y n + h • F (t₀ + n * h) (Y n))‖ ≤ θtr) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * (h * ε + (L * B + Lt) * h ^ 2 / 2 + θtr)) :=
  lady_windermere hF hL hh hA hΦ hΦ₀ fun n hn =>
    sxl_local_error hF hL hB (hPa n) (hP n) (hPY n hn) (hKf n hn) (hX n hn) (by ring) hh
      (hΦ n hn) (hΦ₀ n hn) (hFt n hn) (htr n hn)

/-- Speed bound between two arbitrary times: a trajectory of a field bounded by `B` satisfies
`‖A t - A s‖ ≤ B |t - s|` on `[t₀, t₁]`. -/
theorem ODESolution.norm_sub_le_abs {A : ℝ → E} (hB : IsBoundedField F B)
    (hA : ODESolution F A t₀ t₁) {s t : ℝ} (hs : s ∈ Icc t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    ‖A t - A s‖ ≤ B * |t - s| := by
  rcases le_total s t with hst | hts
  · have := (hA.mono hs.1 ht.2).norm_sub_le_of_bounded hB t ⟨hst, le_rfl⟩
    rwa [abs_of_nonneg (sub_nonneg.2 hst)]
  · have := (hA.mono ht.1 hs.2).norm_sub_le_of_bounded hB s ⟨hts, le_rfl⟩
    rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 hts), neg_sub]; exact this

/-- **Lemma 3.2 of arXiv 2505.19929, Lipschitz part**: for an orthogonal projector `P` onto a
fixed subspace, `s ↦ ‖A s - P A s‖` is `B`-Lipschitz along the exact flow. -/
theorem normal_dist_lipschitz {P : E →L[ℝ] E} (hP : IsOrthProj P) (hB : IsBoundedField F B)
    (hA : ODESolution F A t₀ t₁) {s t : ℝ} (hs : s ∈ Icc t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    |‖A t - P (A t)‖ - ‖A s - P (A s)‖| ≤ B * |t - s| := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have : A t - P (A t) - (A s - P (A s)) = (A t - A s) - P (A t - A s) := by
    rw [map_sub]; abel
  rw [this]
  exact (hP.norm_sub_le _).trans (hA.norm_sub_le_abs hB hs ht)

/-- **Lemma 3.2 of arXiv 2505.19929, bound (3.1)**, with the sharper constant `B` (the paper
states `2 B`): `‖A s - P A s‖ ≤ ‖A t₁ - P A t₁‖ + B (t₁ - s)` for `s ∈ [t₀, t₁]`. -/
theorem normal_dist_le_end {P : E →L[ℝ] E} (hP : IsOrthProj P) (hB : IsBoundedField F B)
    (hA : ODESolution F A t₀ t₁) {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    ‖A s - P (A s)‖ ≤ ‖A t₁ - P (A t₁)‖ + B * (t₁ - s) := by
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨hs.1.trans hs.2, le_rfl⟩
  have h := normal_dist_lipschitz hP hB hA ht₁ hs
  rw [abs_sub_comm s t₁, abs_of_nonneg (sub_nonneg.2 hs.2)] at h
  linarith [le_abs_self (‖A s - P (A s)‖ - ‖A t₁ - P (A t₁)‖)]

/-- Bound (3.1) of arXiv 2505.19929 exactly as published (constant `2 B`). -/
theorem normal_dist_le_end_paper {P : E →L[ℝ] E} (hP : IsOrthProj P) (hB : IsBoundedField F B)
    (hA : ODESolution F A t₀ t₁) {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    ‖A s - P (A s)‖ ≤ ‖A t₁ - P (A t₁)‖ + 2 * B * |t₁ - s| := by
  have h := normal_dist_le_end hP hB hA hs
  rw [abs_of_nonneg (sub_nonneg.2 hs.2)]
  nlinarith [hB.nonneg, sub_nonneg.2 hs.2]

end XL

/-! ### Examples: the hypotheses are jointly satisfiable, and the bounds are sharp -/

namespace EulerBUGExamples

open EnergyExamples

lemma lineProj0_e0 : lineProj 0 (e 0) = e 0 := lineProj_self 0

lemma lineProj0_e1 : lineProj 0 (e 1) = 0 := by rw [lineProj_apply, inner_e01, zero_smul]

/-- `A(t) = e₀ + t e₁` solves `A' = e₁`. -/
lemma odeSolution_line (a b : ℝ) :
    ODESolution (fun _ _ => e 1) (fun t : ℝ => e 0 + t • e 1) a b where
  cont := (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  deriv t _ := by
    simpa using ((hasDerivWithinAt_id t (Ici t)).smul_const (e 1)).const_add (e 0)

lemma lip_const : IsLipschitzField (fun (_ : ℝ) (_ : E2) => e 1) 0 := fun _ _ _ => by simp

lemma bdd_const : IsBoundedField (fun (_ : ℝ) (_ : E2) => e 1) 1 := fun _ _ => by simp [norm_e]

/-- `euler_capture` on `ℝ²` with the rank-one projectors `P₁ = Q₀ = e₀e₀ᵀ` (`≠ 1`), the constant
field `F ≡ e₁` (`L = 0`, `B = 1`, `Lₜ = 0`, normal component `ε = 1`), `Y₀ = e₀`, `h = 1`.  The
bound `h (ε + (L B + Lₜ) h / 2) = 1` is attained (next example), so the `h ε` term is sharp. -/
example : ‖(1 - lineProj 0) (e 0 + (1 : ℝ) • e 1)‖ ≤ 1 * (1 + (0 * 1 + 0) * 1 / 2) :=
  euler_capture (F := fun _ _ => e 1) (A := fun t : ℝ => e 0 + t • e 1) (t₀ := 0) (t₁ := 1)
    (h := 1) (Y₀ := e 0) (Q₀ := lineProj 0) lip_const le_rfl bdd_const (isOrthProj_lineProj 0)
    (by norm_num) zero_le_one (odeSolution_line 0 1) (by simp) (fun _ _ => by simp)
    (by simp [lineProj0_e0, lineProj0_e1]) (by simp [lineProj0_e1, norm_e])

example : ‖(1 - lineProj 0) (e 0 + (1 : ℝ) • e 1)‖ = 1 := by
  simp [lineProj0_e0, lineProj0_e1, norm_e]

/-- `eulerBug_local_error` on `ℝ²` with all four bases rank-one (`e₀e₀ᵀ`) and `F ≡ e₁`: all
hypotheses hold with `ε = 1`, `L = Lₜ = 0`, `B = 1`. -/
example : ‖lineProj 0 (lineProj 0 (e 0 + (1 : ℝ) • e 1)) - (e 0 + (1 : ℝ) • e 1)‖ ≤
    1 * (2 * 1 + (7 * 0 * 1 + 3 * 0) * 1 / 2) :=
  eulerBug_local_error (F := fun _ _ => e 1) (A := fun t : ℝ => e 0 + t • e 1) (t₀ := 0)
    (t₁ := 1) (h := 1) (Y₀ := e 0) lip_const le_rfl bdd_const (isOrthProj_lineProj 0)
    (isOrthProj_lineProj 0) (isOrthProj_lineProj 0) (isOrthProj_lineProj 0) (fun _ => rfl)
    (by norm_num) zero_le_one (odeSolution_line 0 1) (by simp) (fun _ _ => by simp)
    (by simp [lineProj0_e0, lineProj0_e1]) (by simp [lineProj0_e0, lineProj0_e1])
    (by simp [lineProj0_e1, norm_e]) (by simp [lineProj0_e1, norm_e])

/-- `augmentedBug_euler_sub_euler` (OP-ST-01) on `ℝ²` with `P₀ = Q₀ = P₁ = e₀e₀ᵀ`, `Q₁ = 1`,
`Y₀ = e₀`, `f = e₁`, `h = 1`: the augmented step is `e₀`, the full Euler step `e₀ + e₁`, and the
bound `h ‖(1 - P₀)(1 - Q₀) f‖ = 1` is attained. -/
example : ‖lineProj 0 ((1 : E2 →L[ℝ] E2) (e 0 + (1 : ℝ) • e 1)) - (e 0 + (1 : ℝ) • e 1)‖ ≤
    1 * ‖(1 - lineProj 0) ((1 - lineProj 0) (e 1))‖ :=
  augmentedBug_euler_sub_euler (P₀ := lineProj 0) (Q₀ := lineProj 0) (P₁ := lineProj 0)
    (Q₁ := 1) (f := e 1) (isOrthProj_lineProj 0) IsOrthProj.one (fun _ => rfl)
    (isOrthProj_lineProj 0).idem (fun _ => rfl) (fun _ => rfl) lineProj0_e0 lineProj0_e0
    (by simp [lineProj0_e1]) rfl zero_le_one

example : ‖lineProj 0 ((1 : E2 →L[ℝ] E2) (e 0 + (1 : ℝ) • e 1)) - (e 0 + (1 : ℝ) • e 1)‖ = 1 ∧
    ‖(1 - lineProj 0) ((1 - lineProj 0) (e 1))‖ = 1 := by
  constructor <;> simp [lineProj0_e0, lineProj0_e1, norm_e]

end EulerBUGExamples

end LeanDLRA
