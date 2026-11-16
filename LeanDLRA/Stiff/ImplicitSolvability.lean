import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Stability.Energy
import LeanDLRA.Matrix.Frobenius

/-!
# Unique solvability of projected implicit stages

Implicit (backward Euler, θ-method, BDF, DIRK) dynamical low-rank integrators replace the
explicit increments of the K-, L- and S-steps by **implicit Galerkin stages**

    x₁ = Π (x₀ + h F(t, x₁)),

where `Π` is an orthogonal projector (`X ↦ X V Vᵀ`, `X ↦ U Uᵀ X`, `X ↦ U Uᵀ X V Vᵀ`, or a Tucker /
tree-tensor-network projector).  LeanDLRA already proves *uniqueness* and *stability* of such
stages for one-sided Lipschitz fields (`Foundations/OneSided.lean`:
`proj_implicit_step_stability`, `galerkin_implicitEuler_stability`, `implicitEuler_unique`).
This file supplies the missing **existence** half and its consequences.

## Main results

Linear stages (OP-EX-03 (i), OP-SB-08):
* `existsUnique_linear_implicitGalerkin`: `T` linear, `⟪T x, x⟫ ≤ α ‖x‖²` on `range Π`, `h ≥ 0`,
  `h α < 1` ⇒ `x = Π (x₀ + h T x)` has a unique solution, `(1 - h α) ‖x‖ ≤ ‖Π x₀‖`.
* `bijective_one_sub_smul_compress`, `norm_le_norm_one_sub_smul_compress`: dissipative `A` ⇒
  `I - h Π A Π` bijective for every `h ≥ 0` with `‖(I - h Π A Π)⁻¹‖ ≤ 1`, in any inner product
  (in particular a weighted one `⟪·,·⟫_W` with `W`-orthogonal `Π`);
  `implicitGalerkin_linear_contract`: geometric contraction for strongly monotone fields.
* `not_exists_euclideanProj_weighted`: a `W`-dissipative `2 × 2` operator whose
  *Euclidean*-orthogonal Galerkin compression makes the implicit step unsolvable at `h = 8/3`.

Nonlinear stages (OP-ST-03, OP-EX-03 (i)):
* `exists_implicitGalerkin_of_lipschitz`: `F(t, ·)` Lipschitz (any constant `L`) and one-sided
  Lipschitz (`ℓ`) ⇒ a solution exists for **every** `h ≥ 0` with `h ℓ < 1` (Banach fixed point
  for `x ↦ x - ω (G x - Π x₀)`, `G x = x - h Π F(Π x)` strongly monotone and Lipschitz);
  `existsUnique_implicitGalerkin` adds uniqueness.
* `exists_implicitGalerkin_of_lipschitzOnBounded`,
  `existsUnique_implicitGalerkin_of_locallyLipschitz`: the same for fields that are only
  Lipschitz on bounded sets (finite dimension: locally Lipschitz, e.g. `C¹`), via an a priori
  bound and the radial retraction `zeroBallRetract`;
  `allenCahn_implicit_wellPosed` is a non-globally-Lipschitz instance.
* `not_exists_implicitEuler_discontinuous`: without continuity the stage can fail to exist.
* `implicitBUG_wellPosed`: implicit K-, L- and S-steps of the BUG integrator are uniquely
  solvable, and the S-step satisfies `(1 - h ℓ) ‖Y₁‖ ≤ ‖Y₀‖`.

Matrix equations and solvers:
* `compressedSylvester_existsUnique` (`a + b > 0`) and
  `compressedSylvester_existsUnique_of_numericalRange` (numerical ranges in the left half-plane):
  unique solvability of `A K + K (Vᵀ B V) = C` (OP-EX-03 (ii));
  `compressedSylvester_counterexample`: spectral disjointness `σ(A) ∩ σ(-B) = ∅` alone is not
  enough.
* `bugPreconditioner_exact`: the BUG preconditioner ([MengAppeloCheng2025, Alg. 4.1]) returns
  `X⋆` exactly when `Q₀ X⋆ = X⋆` and `𝒜` is coercive; `existsUnique_galerkin_linear`,
  `bijective_of_coercive` (finite-dimensional Lax–Milgram).
* `sylvester_iff_shifted_columns`, `shifted_existsUnique`: correctness and well-posedness of the
  sparse-by-small Sylvester solver ([SahaYangYin2026, Alg. 4.1]).
* `densitySolve_invertible`, `densitySolve_coercive`, `densitySolve_perturbation`,
  `grid_l2_le_sqrt_mul`: [LiEtAl2026b], Lemmas 4–5 and Proposition 6 (abstract cores).
* `thetaMethod_resolvent`, `thetaMethod_step_le`: [AdakEtAl2026, Lemma 5.3 (i)]–(ii).

Variational steps (OP-ST-17, [SuttiVandereycken2024], [BachmayrEtAl2021]):
* `cone_minimizer_fderiv_self`, `rothe_cone_optimality`, `rothe_energy_step`,
  `rothe_energy_sum`: [BachmayrEtAl2021, Lemma 4.4] (optimality on cones, energy estimate (4.1)).
* `mm_energy_le`, `mm_energy_sum`: unconditional energy stability of minimising-movement steps
  over any admissible set containing the previous iterate; `mm_exists_minimizer`: existence on
  closed sets; `mm_unique_of_semiconvex`: uniqueness on convex sets when `h κ < 1`;
  `mm_nonunique_rankOne`: on the rank-`≤ 1` variety, two minimisers for every `h > 0` even for a
  strongly convex energy.

Counterexamples and root selection:
* `implicitGalerkin_linear_counterexample`, `exp_lt_inv_one_sub`: the `e^{α Δt}` bound of
  [AppeloCheng2025, Thm. 3.2] fails for every `α ≠ 0` (OP-SB-11); the factor `(1 - α Δt)⁻¹`
  is attained; `norm_implicitGalerkin_iter_le_exp`: `‖xₙ‖ ≤ e^{2 α tₙ} ‖x₀‖` for
  `0 ≤ α Δt ≤ 1/2`.
* `cubic_stage_roots`, `cubic_stage_unique_of_mem_ball`: [HuYu2026, §5.4] — the three
  zero-residual roots of `z - τ z³ = 0`, and selection by the energy ball `|z| ≤ Q`, `τ Q² < 1`.

## What remains open

* Existence of implicit stages for fields that are merely *continuous* and one-sided Lipschitz
  (finite-dimensional Browder–Minty; Mathlib has no Brouwer fixed point theorem).
* OP-EX-03 (iii) (Hurwitz property of compressions `Uᵀ A U` for complex eigenvalues) is not
  formalised here.
* Closedness of `{X | rank X ≤ r}` is a hypothesis of `mm_exists_minimizer` (`IsClosed S`).

## References

* Appelö–Cheng, [AppeloCheng2025], Theorems 3.1–3.2; Hu–Yu, [HuYu2026, Thm. 5.1], §5.4;
  Meng–Appelö–Cheng, [MengAppeloCheng2025, Alg. 4.1]; Saha–Yang–Yin, [SahaYangYin2026],
  Algorithm 4.1, Theorem 3.6; [LiEtAl2026b], Lemmas 4–5, Proposition 6; [AdakEtAl2026],
  Lemma 5.3; Bachmayr–Eisenmann–Kieri–Uschmajew, [BachmayrEtAl2021, Lemma 4.4];
  Sutti–Vandereycken, [SuttiVandereycken2024] (implicit steps as Riemannian optimisation).
* Open problems addressed: OP-EX-03, OP-SB-08, OP-ST-03, OP-ST-17, OP-SB-11.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Linear implicit Galerkin stages -/

section Linear

variable {P T : E →L[ℝ] E}

/-- **Coercivity of the projected implicit operator** on `range P`:
`(1 - h α) ‖x‖² ≤ ⟪x - h P (T x), x⟫` when `P x = x`, `h ≥ 0` and `⟪T x, x⟫ ≤ α ‖x‖²`. -/
lemma inner_sub_smul_proj_ge (hP : IsOrthProj P) {α h : ℝ} (hh : 0 ≤ h) {x : E} (hx : P x = x)
    (hT : ⟪T x, x⟫ ≤ α * ‖x‖ ^ 2) :
    (1 - h * α) * ‖x‖ ^ 2 ≤ ⟪x - h • P (T x), x⟫ := by
  rw [inner_sub_left, real_inner_smul_left, hP.inner_apply_left_of_mem _ hx,
    real_inner_self_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_left hT hh]

/-- The linear map `x ↦ x - h P (T x)`. -/
noncomputable def implicitOp (P T : E →L[ℝ] E) (h : ℝ) : E →ₗ[ℝ] E :=
  LinearMap.id - h • (P.comp T).toLinearMap

@[simp] lemma implicitOp_apply (P T : E →L[ℝ] E) (h : ℝ) (x : E) :
    implicitOp P T h x = x - h • P (T x) := rfl

/-- The operator `x ↦ x - h P (T x)` is injective when `T` satisfies the one-sided bound
`⟪T x, x⟫ ≤ α ‖x‖²` on `range P`, `h ≥ 0` and `h α < 1`. -/
lemma implicitOp_injective (hP : IsOrthProj P) {α h : ℝ} (hh : 0 ≤ h) (hhα : h * α < 1)
    (hT : ∀ x, P x = x → ⟪T x, x⟫ ≤ α * ‖x‖ ^ 2) : Function.Injective (implicitOp P T h) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [implicitOp_apply, sub_eq_zero] at hx
  have hPx : P x = x := by rw [hx, map_smul, hP.idem]
  have h1 := inner_sub_smul_proj_ge hP hh hPx (hT x hPx)
  rw [← hx, sub_self, inner_zero_left] at h1
  have h2 : ‖x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x‖]
  have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.1 this

/-- **Unique solvability of the linear implicit Galerkin stage** (OP-EX-03 (i), linear case;
OP-SB-08).  Let `E` be finite-dimensional, `P` an orthogonal projector and `T` linear with
`⟪T x, x⟫ ≤ α ‖x‖²` for `x ∈ range P`.  If `h ≥ 0` and `h α < 1`, then for every `x₀` the stage
`x₁ = P (x₀ + h T x₁)` has exactly one solution, and it satisfies
`(1 - h α) ‖x₁‖ ≤ ‖P x₀‖`.  (Injectivity by coercivity, surjectivity by finite dimension.) -/
theorem existsUnique_linear_implicitGalerkin [FiniteDimensional ℝ E] (hP : IsOrthProj P)
    {α h : ℝ} (hh : 0 ≤ h) (hhα : h * α < 1) (hT : ∀ x, P x = x → ⟪T x, x⟫ ≤ α * ‖x‖ ^ 2)
    (x₀ : E) :
    (∃! x₁, x₁ = P (x₀ + h • T x₁)) ∧
      ∀ x₁, x₁ = P (x₀ + h • T x₁) → (1 - h * α) * ‖x₁‖ ≤ ‖P x₀‖ := by
  have hinj := implicitOp_injective hP hh hhα hT
  have hsurj := LinearMap.surjective_of_injective hinj
  have key : ∀ x₁, x₁ = P (x₀ + h • T x₁) ↔ implicitOp P T h x₁ = P x₀ := by
    intro x₁
    rw [implicitOp_apply, map_add, map_smul, sub_eq_iff_eq_add]
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsurj (P x₀)
    refine ⟨x, (key x).2 hx, fun y hy => hinj ?_⟩
    rw [(key y).1 hy, hx]
  · intro x₁ hx₁
    have hPx : P x₁ = x₁ := by rw [hx₁, hP.idem]
    have hx' : x₁ = P (P x₀ + h • T x₁) := by rw [map_add, hP.idem, ← map_add, ← hx₁]
    exact galerkin_implicitEuler_norm_le (F := fun _ => T) (t := 0) hP hh (hT x₁ hPx) hx'

/-- **Dissipative compressions are invertible for every step size** (OP-SB-08).  If `A` is
dissipative, `⟪A y, y⟫ ≤ 0` for all `y` (in the inner product of `E`, e.g. a weighted inner
product `⟪·,·⟫_W` for which `P` is orthogonal), then `‖x‖ ≤ ‖(I - h P A P) x‖` for all `x` and
`h ≥ 0`; i.e. `‖(I - h P A P)⁻¹‖ ≤ 1`. -/
theorem norm_le_norm_one_sub_smul_compress (hP : IsOrthProj P) {A : E →L[ℝ] E}
    (hA : ∀ y, ⟪A y, y⟫ ≤ 0) {h : ℝ} (hh : 0 ≤ h) (x : E) :
    ‖x‖ ≤ ‖x - h • P (A (P x))‖ := by
  have h1 : ⟪x - h • P (A (P x)), x⟫ = ‖x‖ ^ 2 - h * ⟪A (P x), P x⟫ := by
    rw [inner_sub_left, real_inner_smul_left, hP.symm, real_inner_self_eq_norm_sq]
  have h2 : ‖x‖ ^ 2 ≤ ‖x - h • P (A (P x))‖ * ‖x‖ := by
    have := real_inner_le_norm (x - h • P (A (P x))) x
    nlinarith [mul_nonneg hh (neg_nonneg.2 (hA (P x)))]
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

/-- **`I - h P A P` is bijective** on a finite-dimensional space for dissipative `A` and every
`h ≥ 0` (OP-SB-08: unique solvability of the projected implicit substep
`(I - Δt Π A Π) x = b`, for every `b`, with no step-size restriction). -/
theorem bijective_one_sub_smul_compress [FiniteDimensional ℝ E] (hP : IsOrthProj P)
    {A : E →L[ℝ] E} (hA : ∀ y, ⟪A y, y⟫ ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    Function.Bijective (fun x => x - h • P (A (P x))) := by
  let G : E →ₗ[ℝ] E := LinearMap.id - h • (P.comp (A.comp P)).toLinearMap
  have hG : ∀ x, G x = x - h • P (A (P x)) := fun x => rfl
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := norm_le_norm_one_sub_smul_compress hP hA hh x
    rw [← hG, hx, norm_zero] at this
    exact norm_le_zero_iff.1 this
  have hsurj := LinearMap.surjective_of_injective hinj
  exact ⟨fun x y hxy => hinj (by rw [hG, hG]; exact hxy),
    fun b => (hsurj b).imp fun x hx => (hG x).symm.trans hx⟩

/-- **Strongly monotone affine fields contract geometrically** (OP-SB-08): if
`⟪T x, x⟫ ≤ -μ ‖x‖²` on `range P` with `μ > 0`, two implicit Galerkin stages with data `x₀, y₀`
satisfy `‖x₁ - y₁‖ ≤ (1 + h μ)⁻¹ ‖x₀ - y₀‖`. -/
theorem implicitGalerkin_linear_contract (hP : IsOrthProj P) {μ h : ℝ} (hμ : 0 < μ)
    (hh : 0 ≤ h) (hT : ∀ x, P x = x → ⟪T x, x⟫ ≤ -μ * ‖x‖ ^ 2) {x₀ y₀ x₁ y₁ : E}
    (hx : x₁ = P (x₀ + h • T x₁)) (hy : y₁ = P (y₀ + h • T y₁)) :
    ‖x₁ - y₁‖ ≤ (1 + h * μ)⁻¹ * ‖x₀ - y₀‖ := by
  have hPx : P x₁ = x₁ := by rw [hx, hP.idem]
  have hPy : P y₁ = y₁ := by rw [hy, hP.idem]
  have hPd : P (x₁ - y₁) = x₁ - y₁ := by rw [map_sub, hPx, hPy]
  have hfg : ⟪T x₁ - T y₁, x₁ - y₁⟫ ≤ -μ * ‖x₁ - y₁‖ ^ 2 := by
    rw [← map_sub]; exact hT _ hPd
  have h1 := proj_implicit_step_stability hP hh hx hy hfg
  have hpos : 0 < 1 + h * μ := by nlinarith
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  nlinarith

end Linear

/-! ### Nonlinear implicit Galerkin stages: existence by Banach's fixed point theorem -/

section Nonlinear

/-- Scalar inequality behind the contraction factor: `1 - q ≤ (1 - q/2)²`. -/
private lemma one_sub_le_sq_one_sub_half (q : ℝ) : 1 - q ≤ (1 - q / 2) ^ 2 := by
  nlinarith [sq_nonneg q]

/-- **Existence of the implicit Galerkin stage for Lipschitz, one-sided Lipschitz maps**
(OP-ST-03 and OP-EX-03 (i), nonlinear case).  Let `E` be complete, `P` an orthogonal projector,
`f : E → E` Lipschitz with constant `L` and one-sided Lipschitz with constant `ℓ`.  Then for
every `h ≥ 0` with `h ℓ < 1` and every `x₀` there is `x₁` with `x₁ = P (x₀ + h f(x₁))`.

The step size is restricted only through the (small, possibly negative) one-sided constant `ℓ`,
not through the (possibly huge, stiff) Lipschitz constant `L`. -/
theorem exists_implicitGalerkin_of_lipschitz [CompleteSpace E] {f : E → E} {ℓ L h : ℝ}
    (hosl : ∀ x y, ⟪f x - f y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2)
    (hlip : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) {P : E →L[ℝ] E} (hP : IsOrthProj P)
    (hh : 0 ≤ h) (hhℓ : h * ℓ < 1) (x₀ : E) : ∃ x₁, x₁ = P (x₀ + h • f x₁) := by
  -- constants
  set L' := max L 0 with hL'
  set m := 1 - h * max ℓ 0 with hm
  set M := 1 + h * L' with hM
  have hm0 : 0 < m := by
    rcases le_total ℓ 0 with hl | hl
    · rw [hm, max_eq_right hl]; norm_num
    · rw [hm, max_eq_left hl]; linarith
  have hm1 : m ≤ 1 := by rw [hm]; nlinarith [le_max_right ℓ 0]
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [le_max_right L 0]
  have hM0 : 0 < M := by linarith
  set ω := m / M ^ 2 with hω
  have hωM : ω * M ^ 2 = m := by rw [hω]; field_simp
  have hω0 : 0 < ω := by positivity
  set q := ω * m with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by
    have : q * M ^ 2 = m ^ 2 := by rw [hq, mul_right_comm, hωM, sq]
    nlinarith [sq_nonneg (M - m), mul_le_mul hM1 hM1 zero_le_one (by linarith)]
  -- the strongly monotone map
  let G : E → E := fun x => x - h • P (f (P x))
  have hosl' : IsOneSidedLipschitzField (fun _ => f) ℓ := fun _ => hosl
  have hmono : ∀ x y, m * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫ := by
    intro x y
    have hc := hosl'.compress hP 0 x y
    have e : G x - G y = (x - y) - h • (P (f (P x)) - P (f (P y))) := by
      simp only [G, smul_sub]; abel
    rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hm]
    nlinarith [mul_le_mul_of_nonneg_left hc hh]
  have hlipG : ∀ x y, ‖G x - G y‖ ≤ M * ‖x - y‖ := by
    intro x y
    have e : G x - G y = (x - y) - h • P (f (P x) - f (P y)) := by
      simp only [G, map_sub, smul_sub]; abel
    have h1 : ‖P (f (P x) - f (P y))‖ ≤ L' * ‖x - y‖ := by
      calc ‖P (f (P x) - f (P y))‖ ≤ ‖f (P x) - f (P y)‖ := hP.norm_le _
        _ ≤ L * ‖P x - P y‖ := hlip _ _
        _ ≤ L' * ‖P x - P y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ L' * ‖x - y‖ := by
          rw [← map_sub]
          exact mul_le_mul_of_nonneg_left (hP.norm_le _) (le_max_right _ _)
    rw [e, hM]
    calc ‖(x - y) - h • P (f (P x) - f (P y))‖
        ≤ ‖x - y‖ + ‖h • P (f (P x) - f (P y))‖ := norm_sub_le _ _
      _ = ‖x - y‖ + h * ‖P (f (P x) - f (P y))‖ := by
          rw [norm_smul, Real.norm_of_nonneg hh]
      _ ≤ ‖x - y‖ + h * (L' * ‖x - y‖) := by gcongr
      _ = (1 + h * L') * ‖x - y‖ := by ring
  -- the contraction
  let Φ : E → E := fun x => x - ω • (G x - P x₀)
  set K := 1 - q / 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have hK1 : K < 1 := by rw [hK]; linarith
  have hcontr : ∀ x y, ‖Φ x - Φ y‖ ≤ K * ‖x - y‖ := by
    intro x y
    have e : Φ x - Φ y = (x - y) - ω • (G x - G y) := by
      simp only [Φ, smul_sub]; abel
    have hsq : ‖Φ x - Φ y‖ ^ 2 ≤ (K * ‖x - y‖) ^ 2 := by
      rw [e, norm_sub_sq_real, norm_smul, Real.norm_of_nonneg hω0.le, inner_smul_right,
        real_inner_comm]
      have h1 := hmono x y
      have h2 := hlipG x y
      have h3 : ‖G x - G y‖ ^ 2 ≤ M ^ 2 * ‖x - y‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 := one_sub_le_sq_one_sub_half q
      rw [← hK] at h4
      have hD := sq_nonneg ‖x - y‖
      calc ‖x - y‖ ^ 2 - 2 * (ω * ⟪G x - G y, x - y⟫) + (ω * ‖G x - G y‖) ^ 2
          ≤ ‖x - y‖ ^ 2 - 2 * (ω * (m * ‖x - y‖ ^ 2)) + ω ^ 2 * (M ^ 2 * ‖x - y‖ ^ 2) := by
            rw [mul_pow]
            have := mul_le_mul_of_nonneg_left h1 hω0.le
            have := mul_le_mul_of_nonneg_left h3 (sq_nonneg ω)
            linarith
        _ = (1 - q) * ‖x - y‖ ^ 2 := by
            have : ω ^ 2 * (M ^ 2 * ‖x - y‖ ^ 2) = ω * m * ‖x - y‖ ^ 2 := by
              rw [← hωM]; ring
            rw [this, hq]; ring
        _ ≤ K ^ 2 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_right h4 hD
        _ = (K * ‖x - y‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hΦ : ContractingWith ⟨K, hK0⟩ Φ := by
    refine ⟨by exact_mod_cast hK1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    exact hcontr x y
  set x := ContractingWith.fixedPoint Φ hΦ
  have hfix : Φ x = x := ContractingWith.fixedPoint_isFixedPt hΦ
  have hGx : G x = P x₀ := by
    have h1 : ω • (G x - P x₀) = 0 := by
      have : x - ω • (G x - P x₀) = x := hfix
      rwa [sub_eq_self] at this
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left hω0.ne')
  have hxe : x = P x₀ + h • P (f (P x)) := by
    rw [← hGx]; simp only [G, sub_add_cancel]
  have hPx : P x = x := by
    have : P x = P x₀ + h • P (f (P x)) := by
      conv_lhs => rw [hxe]
      rw [map_add, map_smul, hP.idem, hP.idem]
    rw [this, ← hxe]
  refine ⟨x, ?_⟩
  calc x = P x₀ + h • P (f (P x)) := hxe
    _ = P (x₀ + h • f x) := by rw [hPx, map_add, map_smul]

/-- **Well-posedness of the implicit Galerkin stage** (OP-ST-03): for a field `F` that is
Lipschitz (constant `L`, arbitrary) and one-sided Lipschitz (constant `ℓ`), every `h ≥ 0` with
`h ℓ < 1` and every orthogonal projector `P`, the stage `x₁ = P (x₀ + h F(t, x₁))` has exactly one
solution, and two such stages satisfy `(1 - h ℓ) ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖`. -/
theorem existsUnique_implicitGalerkin [CompleteSpace E] {F : ℝ → E → E} {ℓ L h : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hL : IsLipschitzField F L) {P : E →L[ℝ] E}
    (hP : IsOrthProj P) (hh : 0 ≤ h) (hhℓ : h * ℓ < 1) (t : ℝ) (x₀ : E) :
    ∃! x₁, x₁ = P (x₀ + h • F t x₁) := by
  obtain ⟨x, hx⟩ := exists_implicitGalerkin_of_lipschitz (hF t) (hL t) hP hh hhℓ x₀
  refine ⟨x, hx, fun y hy => ?_⟩
  have h1 := galerkin_implicitEuler_stability hF hP hh hy hx
  rw [sub_self, norm_zero] at h1
  have h2 : ‖y - x‖ ≤ 0 := by nlinarith [norm_nonneg (y - x)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

/-- The step size is not limited by the Lipschitz constant: for the stiff field `x ↦ -100 x`
(`L = 100`, `ℓ = -100`) the implicit Galerkin stage is uniquely solvable for `h = 1`, although
`h L = 100 ≫ 1`. -/
example {P : E →L[ℝ] E} (hP : IsOrthProj P) [CompleteSpace E] (x₀ : E) :
    ∃! x, x = P (x₀ + (1 : ℝ) • ((-100 : ℝ) • x)) :=
  existsUnique_implicitGalerkin (F := fun _ x => (-100 : ℝ) • x) (ℓ := -100) (L := 100)
    (isOneSidedLipschitzField_smul_id _)
    (fun _ x y => by rw [← smul_sub, norm_smul]; norm_num) hP zero_le_one (by norm_num) 0 x₀

/-- **Without continuity, the implicit stage can fail to exist** (on the literal statement of
OP-ST-03).  The scalar field `f(x) = -1` for `x ≥ 0`, `f(x) = 1` for `x < 0` is nonincreasing,
i.e. one-sided Lipschitz with `ℓ = 0`, but the backward Euler stage `x = 0 + h f(x)` has no
solution for any `h > 0`.  Some regularity of `F` (here: Lipschitz) is therefore needed. -/
theorem not_exists_implicitEuler_discontinuous :
    let f : ℝ → ℝ := fun x => if 0 ≤ x then -1 else 1
    IsOneSidedLipschitzField (fun _ => f) 0 ∧ ∀ h : ℝ, 0 < h → ¬ ∃ x, x = 0 + h • f x := by
  intro f
  refine ⟨fun _ x y => ?_, fun h hh => ?_⟩
  · simp only [Real.inner_apply, zero_mul, f]
    split_ifs <;> nlinarith
  · rintro ⟨x, hx⟩
    simp only [zero_add, smul_eq_mul, f] at hx
    split_ifs at hx with h0 <;> nlinarith

end Nonlinear

/-! ### Counterexample to the `e^{α Δt}` growth bound (OP-SB-11) -/

section GrowthBound

/-- `e^x < (1 - x)⁻¹` for every `x < 1`, `x ≠ 0` (from `1 - x < e^{-x}`). -/
theorem exp_lt_inv_one_sub {x : ℝ} (hx : x < 1) (hx0 : x ≠ 0) : Real.exp x < (1 - x)⁻¹ := by
  have h1 : -x + 1 < Real.exp (-x) := Real.add_one_lt_exp (neg_ne_zero.2 hx0)
  rw [← one_div, lt_div_iff₀ (by linarith)]
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos x]

/-- **Counterexample to [AppeloCheng2025, Thm. 3.2]** (OP-SB-11).  For the semi-bounded field
`F(X) = α X` (`⟪F X, X⟫ = α ‖X‖²`), any orthogonal projector `P`, `x₀ ≠ 0` in `range P`, `Δt > 0`,
`α Δt < 1` and `α ≠ 0`, the implicit Galerkin step `x₁ = P (x₀ + Δt F(x₁))` is
`x₁ = (1 - α Δt)⁻¹ x₀` (its unique solution), so `‖x₁‖ = (1 - α Δt)⁻¹ ‖x₀‖`, which is
**strictly larger** than the claimed bound `e^{α Δt} ‖x₀‖`.  The factor `(1 - α Δt)⁻¹` of
`galerkin_implicitEuler_norm_le` is attained, hence sharp. -/
theorem implicitGalerkin_linear_counterexample {P : E →L[ℝ] E} (hP : IsOrthProj P) {α dt : ℝ}
    (hdt : 0 < dt) (hα : α ≠ 0) (hαdt : α * dt < 1) {x₀ : E} (hx₀ : P x₀ = x₀) (hne : x₀ ≠ 0) :
    let x₁ := (1 - α * dt)⁻¹ • x₀
    x₁ = P (x₀ + dt • (α • x₁)) ∧
      (∀ y, y = P (x₀ + dt • (α • y)) → y = x₁) ∧
      ‖x₁‖ = (1 - α * dt)⁻¹ * ‖x₀‖ ∧ Real.exp (α * dt) * ‖x₀‖ < ‖x₁‖ := by
  intro x₁
  have hpos : 0 < 1 - α * dt := by linarith
  have heq : x₁ = P (x₀ + dt • (α • x₁)) := by
    have hc : (1 - α * dt)⁻¹ = 1 + dt * (α * (1 - α * dt)⁻¹) := by
      field_simp [hpos.ne']
      ring
    simp only [x₁, map_add, map_smul, hx₀, smul_smul]
    conv_lhs => rw [hc, add_smul, one_smul]
  have hnorm : ‖x₁‖ = (1 - α * dt)⁻¹ * ‖x₀‖ := by
    simp only [x₁, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
  refine ⟨heq, fun y hy => ?_, hnorm, ?_⟩
  · have hF : IsOneSidedLipschitzField (fun _ (z : E) => α • z) α :=
      isOneSidedLipschitzField_smul_id α
    have h1 := galerkin_implicitEuler_stability (t := 0) hF hP hdt.le hy heq
    rw [sub_self, norm_zero] at h1
    have h2 : ‖y - x₁‖ ≤ 0 := by nlinarith [norm_nonneg (y - x₁)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  · rw [hnorm]
    have h0 : 0 < ‖x₀‖ := norm_pos_iff.2 hne
    have := exp_lt_inv_one_sub hαdt (mul_ne_zero hα hdt.ne')
    nlinarith

/-- `(1 - x)⁻¹ ≤ e^{2x}` for `0 ≤ x ≤ 1/2` (convexity of `exp` and `e ≥ 2`). -/
theorem inv_one_sub_le_exp_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (by linarith : (0 : ℝ) ≤ 1 - 2 * x) (by linarith : (0 : ℝ) ≤ 2 * x)
    (by ring : (1 - 2 * x) + 2 * x = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have h1 : Real.exp (-(2 * x)) ≤ 1 - x := by
    have : 2 * x * -1 = -(2 * x) := by ring
    rw [this] at hc
    nlinarith
  have h3 : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith [Real.exp_pos (2 * x)]

/-- **Corrected multi-step bound** (OP-SB-11).  If `⟪F(t, y), y⟫ ≤ α ‖y‖²` for all `y` and
`0 ≤ α Δt ≤ 1/2`, the implicit Galerkin iterates `xₙ₊₁ = Pₙ (xₙ + Δt F(t, xₙ₊₁))` (arbitrary
orthogonal projectors `Pₙ`, e.g. changing bases) satisfy `‖xₙ‖ ≤ e^{2 α n Δt} ‖x₀‖`. -/
theorem norm_implicitGalerkin_iter_le_exp {F : ℝ → E → E} {α dt t : ℝ}
    (hF : ∀ y, ⟪F t y, y⟫ ≤ α * ‖y‖ ^ 2) (hdt : 0 ≤ dt) (h0 : 0 ≤ α * dt)
    (h1 : α * dt ≤ 1 / 2) {P : ℕ → E →L[ℝ] E} (hP : ∀ n, IsOrthProj (P n)) {x : ℕ → E}
    (hx : ∀ n, x (n + 1) = P n (x n + dt • F t (x (n + 1)))) (n : ℕ) :
    ‖x n‖ ≤ Real.exp (2 * α * dt * n) * ‖x 0‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := galerkin_implicitEuler_norm_le (hP n) hdt (hF _) (hx n)
    have hpos : 0 < 1 - dt * α := by nlinarith
    have hb : ‖x (n + 1)‖ ≤ (1 - α * dt)⁻¹ * ‖x n‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
      nlinarith
    have he := inv_one_sub_le_exp_two_mul h0 h1
    have hexp : Real.exp (2 * α * dt * ↑(n + 1)) = Real.exp (2 * (α * dt)) *
        Real.exp (2 * α * dt * n) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [hexp]
    calc ‖x (n + 1)‖ ≤ (1 - α * dt)⁻¹ * ‖x n‖ := hb
      _ ≤ Real.exp (2 * (α * dt)) * (Real.exp (2 * α * dt * n) * ‖x 0‖) := by
          gcongr
      _ = _ := by ring

end GrowthBound

/-! ### Residual control cannot select the root (Hu–Yu, [HuYu2026, §5.4]) -/

section Cubic

/-- **Three zero-residual roots** ([HuYu2026, eq. (5.9)]).  For `y' = y³` with `yₙ = 0`
and step `τ > 0`, the backward Euler stage `z - τ z³ = 0` has the three distinct roots
`0`, `τ^{-1/2}`, `-τ^{-1/2}`; the two nonzero ones have error `τ^{-1/2}`, which blows up as
`τ → 0`.  So a residual test alone cannot select the correct root. -/
theorem cubic_stage_roots {τ : ℝ} (hτ : 0 < τ) :
    let z := (Real.sqrt τ)⁻¹
    (0 : ℝ) - τ * 0 ^ 3 = 0 ∧ z - τ * z ^ 3 = 0 ∧ (-z) - τ * (-z) ^ 3 = 0 ∧
      0 < z ∧ z ^ 2 = τ⁻¹ := by
  intro z
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hz2 : z ^ 2 = τ⁻¹ := by
    simp only [z, inv_pow, Real.sq_sqrt hτ.le]
  have hroot : z - τ * z ^ 3 = 0 := by
    have : τ * z ^ 3 = τ * z ^ 2 * z := by ring
    rw [this, hz2, mul_inv_cancel₀ hτ.ne', one_mul, sub_self]
  refine ⟨by ring, hroot, by linear_combination -hroot, inv_pos.2 hs, hz2⟩

/-- **The energy ball selects the root** ([HuYu2026, §5.4]): if `τ ≥ 0` and `τ Q² < 1`,
the only root of `z - τ z³ = 0` with `|z| ≤ Q` is `z = 0`. -/
theorem cubic_stage_unique_of_mem_ball {τ Q z : ℝ} (hτ : 0 ≤ τ) (hQ : τ * Q ^ 2 < 1)
    (hz : |z| ≤ Q) (h : z - τ * z ^ 3 = 0) : z = 0 := by
  have hz2 : z ^ 2 ≤ Q ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  have hfac : z * (1 - τ * z ^ 2) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hfac with h0 | h1
  · exact h0
  · nlinarith [mul_le_mul_of_nonneg_left hz2 hτ]

end Cubic

/-! ### Weighted dissipativity with a Euclidean projector (OP-SB-08) -/

section WeightedMismatch

open Matrix

/-- **The weighted/Euclidean mismatch of OP-SB-08 is real.**  With the weight `W = diag(1, 4)`
(positive definite) and `A = W⁻¹ S`, `S = [[0, 1], [-1, 0]]`, the operator `A` is `W`-dissipative
(in fact `W`-skew: `yᵀ W A y = 0`), but the Euclidean-orthogonal rank-one projector `Π` onto
`span (1, 1)` compresses it to the *positive* scalar `3/8`.  Consequently the projected implicit
step `x = Π (x₀ + h A x)` with `x₀ = (1, 1)` has **no solution** at `h = 8/3`.  By contrast, for a
`W`-orthogonal `Π` the step is uniquely solvable for every `h ≥ 0`
(`bijective_one_sub_smul_compress` in the inner product `⟪·,·⟫_W`). -/
theorem not_exists_euclideanProj_weighted :
    let W : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 4]
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1 / 4, 0]
    let Pe : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]
    (∀ y : Fin 2 → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (W *ᵥ y)) ∧
      (∀ y : Fin 2 → ℝ, y ⬝ᵥ (W *ᵥ (A *ᵥ y)) = 0) ∧ Pe * Pe = Pe ∧ Peᵀ = Pe ∧
      ![1, 1] ⬝ᵥ (A *ᵥ ![1, 1]) / (![1, 1] ⬝ᵥ ![(1 : ℝ), 1]) = 3 / 8 ∧
      ¬ ∃ x : Fin 2 → ℝ, x = Pe *ᵥ (![1, 1] + (8 / 3 : ℝ) • (A *ᵥ x)) := by
  intro W A Pe
  refine ⟨fun y hy => ?_, fun y => ?_, ?_, ?_, ?_, ?_⟩
  · have hy' : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      apply hy
      ext i
      fin_cases i <;> simp [hc.1, hc.2]
    simp only [W, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    rcases hy' with h | h
    · have := mul_self_pos.2 h
      nlinarith [sq_nonneg (y 1)]
    · have := mul_self_pos.2 h
      nlinarith [sq_nonneg (y 0)]
  · simp only [W, A, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    ring
  · simp only [Pe]
    rw [mul_fin_two]
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Pe]
  · simp only [A, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    norm_num
  · rintro ⟨x, hx⟩
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    simp only [Pe, A, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at h0 h1
    linarith

end WeightedMismatch

/-! ### Locally Lipschitz fields: existence via a priori bound and radial retraction -/

section LocallyLipschitz

/-- The radial retraction onto the closed ball of radius `R` (the metric projection onto the
ball). -/
noncomputable def zeroBallRetract (R : ℝ) (x : E) : E := if ‖x‖ ≤ R then x else (R / ‖x‖) • x

lemma norm_zeroBallRetract_le {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖zeroBallRetract R x‖ ≤ R := by
  unfold zeroBallRetract
  split_ifs with h
  · exact h
  · replace h := not_le.1 h
    have hx : 0 < ‖x‖ := hR.trans_lt h
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR hx.le), div_mul_cancel₀ _ hx.ne']

lemma zeroBallRetract_of_norm_le {R : ℝ} {x : E} (h : ‖x‖ ≤ R) : zeroBallRetract R x = x := by
  simp [zeroBallRetract, h]

/-- Variational characterisation of the radial retraction:
`⟪x - r x, z - r x⟫ ≤ 0` for every `z` in the ball. -/
lemma inner_sub_zeroBallRetract_le {R : ℝ} (hR : 0 ≤ R) (x : E) {z : E} (hz : ‖z‖ ≤ R) :
    ⟪x - zeroBallRetract R x, z - zeroBallRetract R x⟫ ≤ 0 := by
  unfold zeroBallRetract
  split_ifs with h
  · simp
  · replace h := not_le.1 h
    have hx : 0 < ‖x‖ := hR.trans_lt h
    have hc1 : R / ‖x‖ ≤ 1 := div_le_one_of_le₀ h.le hx.le
    have hcx : R / ‖x‖ * ‖x‖ = R := div_mul_cancel₀ _ hx.ne'
    have e : x - (R / ‖x‖) • x = (1 - R / ‖x‖) • x := by rw [sub_smul, one_smul]
    rw [e, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have h1 : ⟪x, z⟫ ≤ ‖x‖ * R :=
      (real_inner_le_norm x z).trans (mul_le_mul_of_nonneg_left hz hx.le)
    have h2 : 0 ≤ 1 - R / ‖x‖ := by linarith
    have h3 : R / ‖x‖ * ‖x‖ ^ 2 = ‖x‖ * R := by rw [sq, ← mul_assoc, hcx]; ring
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- The radial retraction is firmly nonexpansive: `‖r x - r y‖² ≤ ⟪x - y, r x - r y⟫`. -/
lemma zeroBallRetract_firm {R : ℝ} (hR : 0 ≤ R) (x y : E) :
    ‖zeroBallRetract R x - zeroBallRetract R y‖ ^ 2 ≤
      ⟪x - y, zeroBallRetract R x - zeroBallRetract R y⟫ := by
  have h1 := inner_sub_zeroBallRetract_le hR x (norm_zeroBallRetract_le hR y)
  have h2 := inner_sub_zeroBallRetract_le hR y (norm_zeroBallRetract_le hR x)
  set a := zeroBallRetract R x
  set b := zeroBallRetract R y
  have e1 : x - y = (x - a) - (y - b) + (a - b) := by abel
  have e2 : b - a = -(a - b) := by abel
  rw [e2, inner_neg_right] at h1
  rw [e1, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

/-- The radial retraction is nonexpansive. -/
lemma norm_zeroBallRetract_sub_le {R : ℝ} (hR : 0 ≤ R) (x y : E) :
    ‖zeroBallRetract R x - zeroBallRetract R y‖ ≤ ‖x - y‖ := by
  have h1 := zeroBallRetract_firm hR x y
  have h2 := real_inner_le_norm (x - y) (zeroBallRetract R x - zeroBallRetract R y)
  rcases (norm_nonneg (zeroBallRetract R x - zeroBallRetract R y)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

/-- **Existence of the implicit Galerkin stage for fields that are Lipschitz on bounded sets**
(OP-ST-03, OP-EX-03 (i)).  Let `E` be complete, `P` an orthogonal projector and `f` one-sided
Lipschitz with constant `ℓ` and Lipschitz on every ball (e.g. polynomial reaction terms such as
the Allen–Cahn nonlinearity `u - u³`).  Then `x = P (x₀ + h f(x))` has a solution for every
`h ≥ 0` with `h ℓ < 1`.

*Proof.*  An a priori bound `‖x‖ < R` (with `R` depending only on `‖x₀‖`, `h ‖f 0‖`, `h ℓ`)
holds for every solution of the modified equation with
`g(x) = f(r x) - κ (x - r x)`, `r` the radial retraction onto the ball of radius `R`.  For large
`κ` the field `g` is globally Lipschitz and one-sided Lipschitz with constant
`max ℓ 0 + δ`, `h (max ℓ 0 + δ) < 1` (firm nonexpansiveness of `r` and Young's inequality), so
`exists_implicitGalerkin_of_lipschitz` applies; the a priori bound shows `r x = x`. -/
theorem exists_implicitGalerkin_of_lipschitzOnBounded [CompleteSpace E] {f : E → E} {ℓ h : ℝ}
    (hosl : ∀ x y, ⟪f x - f y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2)
    (hloc : ∀ R, ∃ L, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) (hh : 0 ≤ h) (hhℓ : h * ℓ < 1) (x₀ : E) :
    ∃ x₁, x₁ = P (x₀ + h • f x₁) := by
  set c := 1 - h * max ℓ 0 with hc
  have hc0 : 0 < c := by
    rcases le_total ℓ 0 with hl | hl
    · rw [hc, max_eq_right hl]; norm_num
    · rw [hc, max_eq_left hl]; linarith
  set δ := c / (2 * (h + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hhδ : h * δ ≤ c / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set S := ‖x₀‖ + h * ‖f 0‖ with hS
  have hS0 : 0 ≤ S := by positivity
  set R := 2 * S / c + 1 with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨L₀, hL₀⟩ := hloc R
  set L := max L₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hL : ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖ := fun x y hx hy =>
    (hL₀ x y hx hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set κ := L ^ 2 / (4 * δ) + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκδ : L ^ 2 ≤ 4 * κ * δ := by
    have : 4 * κ * δ = L ^ 2 + 4 * δ := by rw [hκ]; field_simp
    rw [this]; linarith
  let r : E → E := zeroBallRetract R
  have hr : ∀ x, ‖r x‖ ≤ R := norm_zeroBallRetract_le hR0.le
  let g : E → E := fun x => f (r x) - κ • (x - r x)
  have hgosl : ∀ x y, ⟪g x - g y, x - y⟫ ≤ (max ℓ 0 + δ) * ‖x - y‖ ^ 2 := by
    intro x y
    set a := r x - r y with ha_def
    set b := (x - r x) - (y - r y) with hb_def
    have hxy : x - y = a + b := by rw [ha_def, hb_def]; abel
    have hfirm : ‖a‖ ^ 2 ≤ ⟪x - y, a⟫ := zeroBallRetract_firm hR0.le x y
    have hba : 0 ≤ ⟪b, a⟫ := by
      have : ⟪x - y, a⟫ = ‖a‖ ^ 2 + ⟪b, a⟫ := by
        rw [hxy, inner_add_left, real_inner_self_eq_norm_sq]
      linarith
    have ha : ‖a‖ ≤ ‖x - y‖ := norm_zeroBallRetract_sub_le hR0.le x y
    have ha2 : ‖a‖ ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have hf1 : ⟪f (r x) - f (r y), a⟫ ≤ ℓ * ‖a‖ ^ 2 := hosl _ _
    have hf2 : ⟪f (r x) - f (r y), b⟫ ≤ L * ‖a‖ * ‖b‖ :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hL _ _ (hr x) (hr y)) (norm_nonneg _))
    have e : g x - g y = (f (r x) - f (r y)) - κ • b := by
      simp only [g, hb_def, smul_sub]; abel
    have hk : 0 ≤ κ * (δ * ‖a‖ ^ 2 + κ * ‖b‖ ^ 2 - L * ‖a‖ * ‖b‖) := by
      nlinarith [sq_nonneg (κ * ‖b‖ - L * ‖a‖ / 2),
        mul_le_mul_of_nonneg_right hκδ (sq_nonneg ‖a‖)]
    have hyoung := (mul_nonneg_iff_of_pos_left hκ0).1 hk
    have hℓ : ℓ * ‖a‖ ^ 2 ≤ max ℓ 0 * ‖a‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hmx : (max ℓ 0 + δ) * ‖a‖ ^ 2 ≤ (max ℓ 0 + δ) * ‖x - y‖ ^ 2 :=
      mul_le_mul_of_nonneg_left ha2 (by positivity)
    rw [e, inner_sub_left, real_inner_smul_left, hxy, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, ← hxy]
    nlinarith [mul_nonneg hκ0.le hba]
  have hglip : ∀ x y, ‖g x - g y‖ ≤ (L + 2 * κ) * ‖x - y‖ := by
    intro x y
    have ha : ‖r x - r y‖ ≤ ‖x - y‖ := norm_zeroBallRetract_sub_le hR0.le x y
    have hb : ‖(x - r x) - (y - r y)‖ ≤ 2 * ‖x - y‖ := by
      have : (x - r x) - (y - r y) = (x - y) - (r x - r y) := by abel
      rw [this]
      linarith [norm_sub_le (x - y) (r x - r y)]
    have e : g x - g y = (f (r x) - f (r y)) - κ • ((x - r x) - (y - r y)) := by
      simp only [g, smul_sub]; abel
    rw [e]
    calc ‖(f (r x) - f (r y)) - κ • ((x - r x) - (y - r y))‖
        ≤ ‖f (r x) - f (r y)‖ + ‖κ • ((x - r x) - (y - r y))‖ := norm_sub_le _ _
      _ = ‖f (r x) - f (r y)‖ + κ * ‖(x - r x) - (y - r y)‖ := by
          rw [norm_smul, Real.norm_of_nonneg hκ0.le]
      _ ≤ L * ‖x - y‖ + κ * (2 * ‖x - y‖) := by
          gcongr
          exact (hL _ _ (hr x) (hr y)).trans (mul_le_mul_of_nonneg_left ha hL0)
      _ = (L + 2 * κ) * ‖x - y‖ := by ring
  have hhℓ' : h * (max ℓ 0 + δ) < 1 := by nlinarith
  obtain ⟨x, hx⟩ := exists_implicitGalerkin_of_lipschitz hgosl hglip hP hh hhℓ' x₀
  -- a priori bound
  have hr0 : r 0 = 0 := zeroBallRetract_of_norm_le (by simpa using hR0.le)
  have hg0 : g 0 = f 0 := by simp [g, hr0]
  have h0 : (0 : E) = P (-(h • f 0) + h • g 0) := by rw [hg0]; simp
  have hstab := proj_implicit_step_stability hP hh hx h0 (by simpa using hgosl x 0)
  rw [sub_zero, sub_neg_eq_add] at hstab
  have hS' : ‖x₀ + h • f 0‖ ≤ S := by
    rw [hS]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh]
  have hxS : c / 2 * ‖x‖ ≤ S := by nlinarith [norm_nonneg x]
  have hxR : ‖x‖ ≤ R := by
    have : ‖x‖ ≤ 2 * S / c := by
      rw [le_div_iff₀ hc0]; linarith
    linarith
  have hrx : r x = x := zeroBallRetract_of_norm_le hxR
  have hgx : g x = f x := by simp [g, hrx]
  exact ⟨x, by rw [← hgx]; exact hx⟩

/-- **Existence for locally Lipschitz (e.g. `C¹`) one-sided Lipschitz fields in finite
dimension** (OP-ST-03): the implicit Galerkin stage `x = P (x₀ + h f(x))` is uniquely solvable
for every `h ≥ 0` with `h ℓ < 1`. -/
theorem existsUnique_implicitGalerkin_of_locallyLipschitz [FiniteDimensional ℝ E] {f : E → E}
    {ℓ h : ℝ} (hosl : ∀ x y, ⟪f x - f y, x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2) (hf : LocallyLipschitz f)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) (hh : 0 ≤ h) (hhℓ : h * ℓ < 1) (x₀ : E) :
    ∃! x₁, x₁ = P (x₀ + h • f x₁) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hloc : ∀ R, ∃ L, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖ := by
    intro R
    have hLL : LocallyLipschitzOn (Metric.closedBall (0 : E) R) f := hf.locallyLipschitzOn
    obtain ⟨K, hK⟩ := hLL.exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 R)
    refine ⟨K, fun x y hx hy => ?_⟩
    have := hK.dist_le_mul x (by simpa using hx) y (by simpa using hy)
    simpa [dist_eq_norm] using this
  obtain ⟨x, hx⟩ := exists_implicitGalerkin_of_lipschitzOnBounded hosl hloc hP hh hhℓ x₀
  refine ⟨x, hx, fun y hy => ?_⟩
  have h1 := proj_implicit_step_stability hP hh hy hx (hosl y x)
  rw [sub_self, norm_zero] at h1
  have h2 : ‖y - x‖ ≤ 0 := by nlinarith [norm_nonneg (y - x)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

/-- A non-degenerate instance: the Allen–Cahn reaction `f(u) = u - u³` on `ℝ` is **not** globally
Lipschitz, but it is `C¹` and one-sided Lipschitz with `ℓ = 1`; hence its backward Euler stage
`u = u₀ + h (u - u³)` is uniquely solvable for every `0 ≤ h < 1`, which
`exists_implicitGalerkin_of_lipschitz` alone could not give. -/
theorem allenCahn_implicit_wellPosed :
    (¬ ∃ L : ℝ, ∀ x y : ℝ, ‖(x - x ^ 3) - (y - y ^ 3)‖ ≤ L * ‖x - y‖) ∧
      ∀ h : ℝ, 0 ≤ h → h < 1 → ∀ u₀ : ℝ,
        ∃! u, u = (1 : ℝ →L[ℝ] ℝ) (u₀ + h • (u - u ^ 3)) := by
  refine ⟨?_, fun h hh h1 u₀ => ?_⟩
  · rintro ⟨L, hL⟩
    set x := |L| + 2 with hx
    have h0 := hL x 0
    have hx2 : 2 ≤ x := by rw [hx]; linarith [abs_nonneg L]
    have hLx : L ≤ x - 2 := by rw [hx]; linarith [le_abs_self L]
    have e : (x - x ^ 3) - (0 - 0 ^ 3) = -(x * (x ^ 2 - 1)) := by ring
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_neg, abs_of_nonneg (by nlinarith),
      abs_of_nonneg (by linarith)] at h0
    nlinarith
  · have hosl : ∀ x y : ℝ, ⟪(x - x ^ 3) - (y - y ^ 3), x - y⟫ ≤ 1 * ‖x - y‖ ^ 2 := by
      intro x y
      rw [Real.inner_apply, Real.norm_eq_abs, sq_abs]
      nlinarith [mul_nonneg (sq_nonneg (x - y)) (add_nonneg (sq_nonneg (x + y))
        (add_nonneg (sq_nonneg x) (sq_nonneg y)))]
    have hf : LocallyLipschitz (fun u : ℝ => u - u ^ 3) :=
      (show ContDiff ℝ 1 (fun u : ℝ => u - u ^ 3) by fun_prop).locallyLipschitz
    exact existsUnique_implicitGalerkin_of_locallyLipschitz hosl hf IsOrthProj.one hh
      (by linarith) u₀

end LocallyLipschitz

/-! ### Coercive linear systems and projected (Galerkin) linear systems -/

section Coercive

omit [InnerProductSpace ℝ E] in
/-- `c ‖x‖² ≤ 0` with `c > 0` forces `x = 0`. -/
lemma eq_zero_of_mul_norm_sq_nonpos {c : ℝ} (hc : 0 < c) {x : E} (h : c * ‖x‖ ^ 2 ≤ 0) :
    x = 0 := by
  have h3 : ‖x‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    linarith [mul_pos hc hcon]
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h3 (sq_nonneg _)))

/-- **Finite-dimensional Lax–Milgram**: a linear endomorphism with
`c ‖x‖² ≤ ⟪G x, x⟫`, `c > 0`, is bijective and `c ‖x‖ ≤ ‖G x‖`, i.e. `‖G⁻¹‖ ≤ c⁻¹`. -/
theorem bijective_of_coercive [FiniteDimensional ℝ E] (G : E →ₗ[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫) : Function.Bijective G ∧ ∀ x, c * ‖x‖ ≤ ‖G x‖ := by
  have hb : ∀ x, c * ‖x‖ ≤ ‖G x‖ := by
    intro x
    have h1 := hG x
    have h2 := real_inner_le_norm (G x) x
    rcases (norm_nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · nlinarith
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := hb x
    rw [hx, norm_zero] at h
    have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    exact norm_le_zero_iff.1 this
  exact ⟨⟨hinj, LinearMap.surjective_of_injective hinj⟩, hb⟩

variable {P : E →L[ℝ] E}

/-- **Uniqueness for projected linear systems**: if `𝒜` is coercive on `range P`, `𝒜 X = b` and
`P X = X`, then every solution `Y ∈ range P` of the Galerkin system `P (𝒜 Y) = P b` equals `X`. -/
theorem galerkin_linear_eq_of_mem (hP : IsOrthProj P) {𝒜 : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (h𝒜 : ∀ y, P y = y → c * ‖y‖ ^ 2 ≤ ⟪𝒜 y, y⟫) {X b Y : E} (hX : 𝒜 X = b) (hPX : P X = X)
    (hY : P Y = Y) (hYs : P (𝒜 Y) = P b) : Y = X := by
  have hd : P (Y - X) = Y - X := by rw [map_sub, hY, hPX]
  have h0 : P (𝒜 (Y - X)) = 0 := by rw [map_sub, map_sub, hYs, hX, sub_self]
  have h1 : ⟪𝒜 (Y - X), Y - X⟫ = 0 := by
    rw [← hP.inner_apply_left_of_mem _ hd, h0, inner_zero_left]
  have h2 := h𝒜 _ hd
  rw [h1] at h2
  exact sub_eq_zero.1 (eq_zero_of_mul_norm_sq_nonpos hc h2)

/-- **Existence and uniqueness for projected linear systems**: if `𝒜` is coercive on `range P`,
then for every `b` the Galerkin system `P Y = Y`, `P (𝒜 Y) = P b` has exactly one solution. -/
theorem existsUnique_galerkin_linear [FiniteDimensional ℝ E] (hP : IsOrthProj P)
    {𝒜 : E →L[ℝ] E} {c : ℝ} (hc : 0 < c) (h𝒜 : ∀ y, P y = y → c * ‖y‖ ^ 2 ≤ ⟪𝒜 y, y⟫)
    (b : E) : ∃! Y, P Y = Y ∧ P (𝒜 Y) = P b := by
  let G : E →ₗ[ℝ] E := (P.comp (𝒜.comp P)).toLinearMap + (LinearMap.id - P.toLinearMap)
  have hG : ∀ Y, G Y = P (𝒜 (P Y)) + (Y - P Y) := fun Y => rfl
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    rw [hG] at hY
    have h1 : P (P (𝒜 (P Y)) + (Y - P Y)) = P (𝒜 (P Y)) := by
      rw [map_add, map_sub, hP.idem, hP.idem, sub_self, add_zero]
    rw [hY, map_zero] at h1
    rw [← h1, zero_add, sub_eq_zero] at hY
    have hPY : P Y = Y := hY.symm
    rw [hPY] at h1
    have h2 := h𝒜 Y hPY
    rw [← hP.inner_apply_left_of_mem _ hPY, ← h1, inner_zero_left] at h2
    exact eq_zero_of_mul_norm_sq_nonpos hc h2
  obtain ⟨Y, hY⟩ := LinearMap.surjective_of_injective hinj (P b)
  rw [hG] at hY
  have h1 : P (𝒜 (P Y)) = P b := by
    have := congrArg P hY
    rwa [map_add, map_sub, hP.idem, hP.idem, sub_self, add_zero, hP.idem] at this
  have hPY : P Y = Y := by
    rw [h1, add_eq_left, sub_eq_zero] at hY
    exact hY.symm
  refine ⟨Y, ⟨hPY, by rw [← h1, hPY]⟩, fun Z hZ => ?_⟩
  exact galerkin_linear_eq_of_mem (X := Y) (b := 𝒜 Y) hP hc h𝒜 rfl hPY hZ.1
    (by rw [hZ.2, ← h1, hPY])

end Coercive

/-! ### The BUG preconditioner is exact ([MengAppeloCheng2025, Alg. 4.1]) -/

section BUGPreconditioner

/-- **Exactness of the BUG preconditioner** (Meng–Appelö–Cheng, [MengAppeloCheng2025],
Algorithm 4.1; abstract form).  Let `𝒜` be coercive (`c ‖y‖² ≤ ⟪𝒜 y, y⟫`, e.g.
`𝒜 X = X - Δt θ Σⱼ Aⱼ X Bⱼᵀ` with `Δt θ μ < 1` for a one-sided bound `μ` of `Σⱼ Aⱼ X Bⱼᵀ`), and
let `X⋆` solve `𝒜 X⋆ = b`.  The preconditioner solves, in sequence,

* the K-system `Q₀ YK = YK`, `Q₀ (𝒜 YK) = Q₀ b` (`Q₀ = V Vᵀ`: `𝒜(K₁ Vᵀ) V = b V`),
* the L-system `P₁ YL = YL`, `P₁ (𝒜 YL) = P₁ b` with a new basis `P₁ = U Uᵀ` capturing `YK`,
* the Galerkin system for `P₁ Q₁` with a new basis `Q₁` capturing `YL`.

If `Q₀ X⋆ = X⋆` (the row space of `X⋆` lies in the input co-range `V`, e.g. `X⋆ = U Uᵀ X⋆ V Vᵀ`),
then all three projected solutions equal `X⋆`, so the preconditioner returns `X⋆` **exactly**.
Each projected system is uniquely solvable by `existsUnique_galerkin_linear`. -/
theorem bugPreconditioner_exact {𝒜 : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (h𝒜 : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪𝒜 y, y⟫) {P₁ Q₀ Q₁ : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀)
    (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁) (hcomm : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x))
    {Xs b YK YL YS : E} (hX : 𝒜 Xs = b) (hQX : Q₀ Xs = Xs)
    (hK : Q₀ YK = YK) (hKs : Q₀ (𝒜 YK) = Q₀ b) (hP₁K : P₁ YK = YK)
    (hL : P₁ YL = YL) (hLs : P₁ (𝒜 YL) = P₁ b) (hQ₁L : Q₁ YL = YL)
    (hS : P₁ (Q₁ YS) = YS) (hSs : P₁ (Q₁ (𝒜 YS)) = P₁ (Q₁ b)) :
    YK = Xs ∧ YL = Xs ∧ YS = Xs := by
  have hYK := galerkin_linear_eq_of_mem hQ₀ hc (fun y _ => h𝒜 y) hX hQX hK hKs
  have hPX : P₁ Xs = Xs := by rw [← hYK, hP₁K]
  have hYL := galerkin_linear_eq_of_mem hP₁ hc (fun y _ => h𝒜 y) hX hPX hL hLs
  have hQ₁X : Q₁ Xs = Xs := by rw [← hYL, hQ₁L]
  have hPQ := hP₁.mul hQ₁ hcomm
  have hYS := galerkin_linear_eq_of_mem hPQ hc (fun y _ => h𝒜 y) hX
    (by change P₁ (Q₁ Xs) = Xs; rw [hQ₁X, hPX]) hS hSs
  exact ⟨hYK, hYL, hYS⟩

end BUGPreconditioner

/-! ### Compressed Sylvester equations (OP-EX-03 (ii)) and the sparse-by-small solver -/

section Sylvester

open Matrix
open scoped LeanDLRA.Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [Fintype k] in
/-- The Frobenius pairing `⟪A X, X⟫` is the sum over the columns `xⱼ` of `xⱼᵀ A xⱼ`. -/
theorem frob_inner_mul_self_eq_sum [Fintype k] (A : Matrix m m ℝ) (X : Matrix m k ℝ) :
    ⟪A * X, X⟫ = ∑ j, (fun i => X i j) ⬝ᵥ (A *ᵥ fun i => X i j) := by
  rw [Frobenius.inner_def, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [dotProduct, mulVec, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A vector numerical-range bound `xᵀ A x ≤ a xᵀ x` gives the Frobenius bound
`⟪A X, X⟫ ≤ a ‖X‖²`. -/
theorem frob_inner_mul_self_le (A : Matrix m m ℝ) {a : ℝ}
    (hA : ∀ x : m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ a * (x ⬝ᵥ x)) (X : Matrix m k ℝ) :
    ⟪A * X, X⟫ ≤ a * ‖X‖ ^ 2 := by
  have h2 : ‖X‖ ^ 2 = ∑ j, (fun i => X i j) ⬝ᵥ (fun i => X i j) := by
    rw [Frobenius.norm_sq_eq_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dotProduct, sq]
  rw [frob_inner_mul_self_eq_sum, h2, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hA _

/-- Right multiplication: a vector bound `yᵀ B y ≤ b yᵀ y` gives `⟪Y B, Y⟫ ≤ b ‖Y‖²`. -/
theorem frob_inner_mul_right_self_le (B : Matrix n n ℝ) {b : ℝ}
    (hB : ∀ y : n → ℝ, y ⬝ᵥ (B *ᵥ y) ≤ b * (y ⬝ᵥ y)) (Y : Matrix k n ℝ) :
    ⟪Y * B, Y⟫ ≤ b * ‖Y‖ ^ 2 := by
  rw [← Frobenius.inner_transpose, Matrix.transpose_mul, ← Frobenius.norm_transpose Y]
  refine frob_inner_mul_self_le Bᵀ (fun y => ?_) Yᵀ
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  exact hB y

/-- The Sylvester operator `K ↦ A K + K M`. -/
noncomputable def sylvesterOp (A : Matrix m m ℝ) (M : Matrix k k ℝ) :
    Matrix m k ℝ →ₗ[ℝ] Matrix m k ℝ where
  toFun K := A * K + K * M
  map_add' K L := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' r K := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

@[simp] lemma sylvesterOp_apply (A : Matrix m m ℝ) (M : Matrix k k ℝ) (K : Matrix m k ℝ) :
    sylvesterOp A M K = A * K + K * M := rfl

/-- Compression does not increase the right one-sided bound: if `⟪Y B, Y⟫ ≤ -b ‖Y‖²` for all
`Y`, and `Vᵀ V = 1`, then `⟪K (Vᵀ B V), K⟫ ≤ -b ‖K‖²`. -/
theorem frob_inner_compress_le [DecidableEq k] {B : Matrix n n ℝ} {V : Matrix n k ℝ}
    (hV : Vᵀ * V = 1) {b : ℝ} (hB : ∀ Y : Matrix m n ℝ, ⟪Y * B, Y⟫ ≤ -b * ‖Y‖ ^ 2)
    (K : Matrix m k ℝ) : ⟪K * (Vᵀ * B * V), K⟫ ≤ -b * ‖K‖ ^ 2 := by
  have e : K * (Vᵀ * B * V) = K * Vᵀ * B * V := by simp only [Matrix.mul_assoc]
  rw [e, Frobenius.inner_mul_right, ← Frobenius.norm_mul_transpose_of_orthonormal hV K]
  exact hB _

/-- **Unique solvability of compressed Sylvester equations** (OP-EX-03 (ii), quantitative
form).  If `⟪A X, X⟫ ≤ -a ‖X‖²` and `⟪Y B, Y⟫ ≤ -b ‖Y‖²` (Frobenius) with `a + b > 0` and
`Vᵀ V = 1`, then `A K + K (Vᵀ B V) = C` has exactly one solution for every `C`, and
`(a + b) ‖K‖ ≤ ‖C‖`.  Only the *sum* of the two dissipativity constants must be positive. -/
theorem compressedSylvester_existsUnique [DecidableEq k] {A : Matrix m m ℝ}
    {B : Matrix n n ℝ} {V : Matrix n k ℝ} (hV : Vᵀ * V = 1) {a b : ℝ} (hab : 0 < a + b)
    (hA : ∀ X : Matrix m k ℝ, ⟪A * X, X⟫ ≤ -a * ‖X‖ ^ 2)
    (hB : ∀ Y : Matrix m n ℝ, ⟪Y * B, Y⟫ ≤ -b * ‖Y‖ ^ 2) (C : Matrix m k ℝ) :
    (∃! K : Matrix m k ℝ, A * K + K * (Vᵀ * B * V) = C) ∧
      ∀ K : Matrix m k ℝ, A * K + K * (Vᵀ * B * V) = C → (a + b) * ‖K‖ ≤ ‖C‖ := by
  have hcoer : ∀ K : Matrix m k ℝ, (a + b) * ‖K‖ ^ 2 ≤ ⟪(-sylvesterOp A (Vᵀ * B * V)) K, K⟫ := by
    intro K
    rw [LinearMap.neg_apply, sylvesterOp_apply, inner_neg_left, inner_add_left]
    have h1 := hA K
    have h2 := frob_inner_compress_le hV hB K
    linarith
  obtain ⟨hbij, hbd⟩ := bijective_of_coercive _ hab hcoer
  refine ⟨?_, fun K hK => ?_⟩
  · obtain ⟨K, hK⟩ := hbij.2 (-C)
    refine ⟨K, ?_, fun L hL => hbij.1 ?_⟩
    · rw [LinearMap.neg_apply, neg_inj] at hK
      exact hK
    · rw [hK, LinearMap.neg_apply, sylvesterOp_apply, hL]
  · have := hbd K
    rwa [LinearMap.neg_apply, sylvesterOp_apply, hK, norm_neg] at this

/-- **Numerical ranges in the left half-plane suffice** (OP-EX-03 (ii), qualitative form): if
`xᵀ A x < 0` for all `x ≠ 0` and `yᵀ B y ≤ 0` for all `y`, then every compressed Sylvester
equation `A K + K (Vᵀ B V) = C` (`Vᵀ V = 1`) is uniquely solvable.  No spectral theory is
needed. -/
theorem compressedSylvester_existsUnique_of_numericalRange [DecidableEq k]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ} {V : Matrix n k ℝ} (hV : Vᵀ * V = 1)
    (hA : ∀ x : m → ℝ, x ≠ 0 → x ⬝ᵥ (A *ᵥ x) < 0) (hB : ∀ y : n → ℝ, y ⬝ᵥ (B *ᵥ y) ≤ 0)
    (C : Matrix m k ℝ) : ∃! K : Matrix m k ℝ, A * K + K * (Vᵀ * B * V) = C := by
  have hA' : ∀ x : m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ 0 := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hA x hx).le
  have hB' : ∀ Y : Matrix m n ℝ, ⟪Y * B, Y⟫ ≤ -0 * ‖Y‖ ^ 2 := fun Y => by
    have := frob_inner_mul_right_self_le B (b := 0) (fun y => by simpa using hB y) Y
    simpa using this
  have hinj : Function.Injective (sylvesterOp A (Vᵀ * B * V)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro K hK
    by_contra hne
    obtain ⟨i, j, hij⟩ : ∃ i j, K i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Matrix.ext h)
    have hcol : (fun i => K i j) ≠ 0 := fun h => hij (congrFun h i)
    have hlt : ⟪A * K, K⟫ < 0 := by
      rw [frob_inner_mul_self_eq_sum]
      calc ∑ j, (fun i => K i j) ⬝ᵥ (A *ᵥ fun i => K i j) < ∑ _j : k, (0 : ℝ) :=
            Finset.sum_lt_sum (fun j _ => hA' _) ⟨j, Finset.mem_univ _, hA _ hcol⟩
        _ = 0 := by simp
    have h2 := frob_inner_compress_le hV hB' K
    have h3 : ⟪A * K + K * (Vᵀ * B * V), K⟫ = 0 := by
      rw [← sylvesterOp_apply, hK, inner_zero_left]
    rw [inner_add_left] at h3
    nlinarith [sq_nonneg ‖K‖]
  have hsurj := LinearMap.surjective_of_injective hinj
  obtain ⟨K, hK⟩ := hsurj C
  exact ⟨K, hK, fun L hL => hinj (by rw [hK]; exact hL)⟩

/-- **Spectral disjointness is not enough** (OP-EX-03 (ii)).  `A = (1)`, `B = diag(-11/3, 1/2)`
and `v = (3/5, 4/5)`: the full Sylvester operator `X ↦ A X + X B` is injective (`σ(A) = {1}` and
`σ(-B) = {11/3, -1/2}` are disjoint), but `vᵀ B v = -1`, so the compressed operator
`k ↦ A k + k (vᵀ B v)` vanishes identically and the compressed equation is not uniquely
solvable. -/
theorem compressedSylvester_counterexample :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![1]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![-11 / 3, 0; 0, 1 / 2]
    let V : Matrix (Fin 2) (Fin 1) ℝ := !![3 / 5; 4 / 5]
    Vᵀ * V = 1 ∧ (∀ X : Matrix (Fin 1) (Fin 2) ℝ, A * X + X * B = 0 → X = 0) ∧
      (∀ K : Matrix (Fin 1) (Fin 1) ℝ, A * K + K * (Vᵀ * B * V) = 0) ∧
      (!![1] : Matrix (Fin 1) (Fin 1) ℝ) ≠ 0 := by
  intro A B V
  refine ⟨?_, fun X hX => ?_, fun K => ?_, ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp [V, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  · have h0 := congrFun (congrFun hX 0) 0
    have h1 := congrFun (congrFun hX 0) 1
    simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at h0 h1
    ext i j
    fin_cases i; fin_cases j
    · simp; linarith
    · simp; linarith
  · ext i j
    fin_cases i; fin_cases j
    simp [A, B, V, Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
    norm_num
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this

/-- One shifted column system: `((A + s I) v)ᵢ = (A v)ᵢ + s vᵢ`. -/
lemma shifted_mulVec_apply [DecidableEq m] (A : Matrix m m ℝ) (s : ℝ) (v : m → ℝ) (i : m) :
    ((A + s • (1 : Matrix m m ℝ)) *ᵥ v) i = (A *ᵥ v) i + s * v i := by
  simp [add_mulVec, smul_mulVec, one_mulVec]

/-- **Correctness of the sparse-by-small Sylvester solver** (Saha–Yang–Yin, [SahaYangYin2026],
Algorithm 4.1).  If `B Q = Q Λ` with `Λ = diag(λ)` and `Q` orthogonal (`Q Qᵀ = 1`), then
`A X + X B = C` holds iff every column `yⱼ` of `Y = X Q` solves the shifted system
`(A + λⱼ I) yⱼ = c̃ⱼ`, `c̃ⱼ` the `j`-th column of `C Q`. -/
theorem sylvester_iff_shifted_columns [DecidableEq m] [DecidableEq k] {A : Matrix m m ℝ}
    {B Q : Matrix k k ℝ} {d : k → ℝ} (hQ : Q * Qᵀ = 1) (hBQ : B * Q = Q * diagonal d)
    (X C : Matrix m k ℝ) :
    A * X + X * B = C ↔
      ∀ j, (A + d j • (1 : Matrix m m ℝ)) *ᵥ (fun i => (X * Q) i j) = fun i => (C * Q) i j := by
  have step1 : A * X + X * B = C ↔ A * (X * Q) + X * Q * diagonal d = C * Q := by
    constructor
    · intro h
      rw [← h]
      simp only [Matrix.add_mul, Matrix.mul_assoc, hBQ]
    · intro h
      have h' : (A * (X * Q) + X * Q * diagonal d) * Qᵀ = C * Q * Qᵀ := by rw [h]
      have e : Q * (diagonal d * Qᵀ) = B := by
        rw [← Matrix.mul_assoc, ← hBQ, Matrix.mul_assoc, hQ, Matrix.mul_one]
      simp only [Matrix.add_mul, Matrix.mul_assoc, hQ, Matrix.mul_one, e] at h'
      exact h'
  rw [step1]
  constructor
  · intro h j
    funext i
    have := congrFun (congrFun h i) j
    rw [shifted_mulVec_apply, ← this, Matrix.add_apply, mul_diagonal]
    simp only [mulVec, dotProduct, Matrix.mul_apply]
    ring
  · intro h
    ext i j
    have := congrFun (h j) i
    rw [shifted_mulVec_apply] at this
    rw [← this, Matrix.add_apply, mul_diagonal]
    simp only [mulVec, dotProduct, Matrix.mul_apply]
    ring

/-- **Well-posedness of the shifted systems** of Algorithm 4.1 ([SahaYangYin2026], with
Theorem 3.6 there): if `xᵀ A x ≥ 0` for all `x` (no symmetry of `A` needed) and `s > 0`, then
`(A + s I) y = c` has exactly one solution for every `c`. -/
theorem shifted_existsUnique [DecidableEq m] {A : Matrix m m ℝ}
    (hA : ∀ x : m → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) {s : ℝ} (hs : 0 < s) (c : m → ℝ) :
    ∃! y, (A + s • (1 : Matrix m m ℝ)) *ᵥ y = c := by
  have hinj : Function.Injective (A + s • (1 : Matrix m m ℝ)).mulVec := by
    intro x y hxy
    have hz : (A + s • (1 : Matrix m m ℝ)) *ᵥ (x - y) = 0 := by
      rw [mulVec_sub, hxy, sub_self]
    have h1 : (x - y) ⬝ᵥ ((A + s • (1 : Matrix m m ℝ)) *ᵥ (x - y)) =
        (x - y) ⬝ᵥ (A *ᵥ (x - y)) + s * ((x - y) ⬝ᵥ (x - y)) := by
      rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [hz, dotProduct_zero] at h1
    have h2 := hA (x - y)
    have h3 : (x - y) ⬝ᵥ (x - y) = 0 := by
      have := dotProduct_self_star_nonneg (x - y)
      simp only [star_trivial] at this
      nlinarith
    exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h3)
  have hunit := mulVec_injective_iff_isUnit.1 hinj
  obtain ⟨y, hy⟩ := mulVec_surjective_iff_isUnit.2 hunit c
  exact ⟨y, hy, fun z hz => hinj (by rw [hz, hy])⟩

end Sylvester

/-! ### Implicit macroscopic density solve ([LiEtAl2026b], Lemmas 4–5, Proposition 6) -/

section DensitySolve

/-- **Lemma 5 of [LiEtAl2026b]** (abstract form).  If `⟪A u, u⟫ ≥ ‖u‖²` for all `u` (e.g.
`A = I - Δt L_β + Δt diag(σᵃ)` with `-L_β`, `diag(σᵃ)` positive semidefinite), then `A` is
invertible and `‖A⁻¹‖ ≤ 1`, i.e. `‖u‖ ≤ ‖A u‖`. -/
theorem densitySolve_invertible [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E)
    (hA : ∀ u, ‖u‖ ^ 2 ≤ ⟪A u, u⟫) : Function.Bijective A ∧ ∀ u, ‖u‖ ≤ ‖A u‖ := by
  obtain ⟨h1, h2⟩ := bijective_of_coercive A one_pos (fun u => by simpa using hA u)
  exact ⟨h1, fun u => by simpa using h2 u⟩

/-- The structural hypothesis of Lemma 5: `A = I + Δt (N + S)` with `⟪N u, u⟫ ≥ 0` and
`⟪S u, u⟫ ≥ 0` (`N = -L_β`, `S = diag(σᵃ)`) and `Δt ≥ 0` satisfies `⟪A u, u⟫ ≥ ‖u‖²`. -/
theorem densitySolve_coercive {N S : E →L[ℝ] E} (hN : ∀ u, 0 ≤ ⟪N u, u⟫)
    (hS : ∀ u, 0 ≤ ⟪S u, u⟫) {Δt : ℝ} (hΔt : 0 ≤ Δt) (u : E) :
    ‖u‖ ^ 2 ≤ ⟪u + Δt • (N u + S u), u⟫ := by
  rw [inner_add_left, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg hΔt (add_nonneg (hN u) (hS u))]

/-- **Proposition 6 of [LiEtAl2026b]** (eq. (13), abstract form).  If `⟪A u, u⟫ ≥ ‖u‖²` and
the two provisional densities differ by `A (ρ - ρ') = c • D η` (`c = -Δt/ε`,
`D = diag(α₁)` with `‖D η‖ ≤ d ‖η‖`, `η` the flux sampling error), then
`‖ρ - ρ'‖ ≤ |c| d ‖η‖`. -/
theorem densitySolve_perturbation {A D : E →L[ℝ] E} (hA : ∀ u, ‖u‖ ^ 2 ≤ ⟪A u, u⟫) {d c : ℝ}
    {η e : E} (hD : ‖D η‖ ≤ d * ‖η‖) (he : A e = c • D η) : ‖e‖ ≤ |c| * d * ‖η‖ := by
  have h1 : ‖e‖ ≤ ‖A e‖ := by
    have h := hA e
    have h2 := real_inner_le_norm (A e) e
    rcases (norm_nonneg e).eq_or_lt with h0 | hpos
    · rw [← h0]; exact norm_nonneg _
    · nlinarith
  rw [he, norm_smul, Real.norm_eq_abs] at h1
  calc ‖e‖ ≤ |c| * ‖D η‖ := h1
    _ ≤ |c| * (d * ‖η‖) := mul_le_mul_of_nonneg_left hD (abs_nonneg c)
    _ = |c| * d * ‖η‖ := by ring

/-- **Lemma 4 of [LiEtAl2026b]** (abstract core: sup-norm to grid-`ℓ²` bound).  On a grid of
`N` cells of width `Δx ≥ 0` (`N Δx = x_R - x_L`), if `|J̃ᵢ| ≤ a` and `|Jᵢ| ≤ b` for all `i`, then
`‖J̃ - J‖_{Δx} = (Σᵢ Δx (J̃ᵢ - Jᵢ)²)^{1/2} ≤ √(N Δx) (a + b)`.  With `a = 2 C_g C_we / Δx`,
`b = 2 C_g / Δx` this is the paper's bound `2 √(x_R - x_L) C_g (1 + C_we) / Δx`. -/
theorem grid_l2_le_sqrt_mul {N : ℕ} {Δx a b : ℝ} (hΔx : 0 ≤ Δx) {J J' : Fin N → ℝ}
    (hJ' : ∀ i, |J' i| ≤ a) (hJ : ∀ i, |J i| ≤ b) :
    Real.sqrt (∑ i, Δx * (J' i - J i) ^ 2) ≤ Real.sqrt (N * Δx) * (a + b) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  have hab : 0 ≤ a + b := by
    let i0 : Fin N := ⟨0, hN⟩
    linarith [abs_nonneg (J' i0), hJ' i0, abs_nonneg (J i0), hJ i0]
  have hsum : ∑ i, Δx * (J' i - J i) ^ 2 ≤ N * Δx * (a + b) ^ 2 := by
    have : ∀ i ∈ Finset.univ, Δx * (J' i - J i) ^ 2 ≤ Δx * (a + b) ^ 2 := by
      intro i _
      have h1 : |J' i - J i| ≤ a + b := (abs_sub _ _).trans (add_le_add (hJ' i) (hJ i))
      have h2 : (J' i - J i) ^ 2 ≤ (a + b) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_left h2 hΔx
    calc ∑ i, Δx * (J' i - J i) ^ 2 ≤ ∑ _i : Fin N, Δx * (a + b) ^ 2 := Finset.sum_le_sum this
      _ = N * Δx * (a + b) ^ 2 := by simp [Finset.card_univ]; ring
  calc Real.sqrt (∑ i, Δx * (J' i - J i) ^ 2) ≤ Real.sqrt (N * Δx * (a + b) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (N * Δx) * (a + b) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hab]

end DensitySolve

/-! ### θ-method in an energy norm ([AdakEtAl2026, Lemma 5.3]) -/

section ThetaMethod

/-- **Lemma 5.3 (i) of [AdakEtAl2026]** (abstract form).  In the energy inner product
`⟪x, y⟫_E = xᵀ W V⁻¹ y`, write `Vi = V⁻¹` and assume the energy inequality
`xᵀ W A x = ⟪x, V A x⟫_E ≥ -γ ‖x‖²_E`.  For `θ, Δt ≥ 0` with `θ γ Δt < 1` the θ-method step
matrix `K = V⁻¹ + θ Δt A` is invertible and `(1 - θ γ Δt) ‖K⁻¹ y‖_E ≤ ‖V y‖_E`. -/
theorem thetaMethod_resolvent [FiniteDimensional ℝ E] {Vi V A : E →ₗ[ℝ] E}
    (hVVi : ∀ z, V (Vi z) = z) {γ θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt)
    (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫) (hs : θ * γ * Δt < 1) :
    Function.Bijective (Vi + (θ * Δt) • A) ∧
      ∀ y z, (Vi + (θ * Δt) • A) z = y → (1 - θ * γ * Δt) * ‖z‖ ≤ ‖V y‖ := by
  have hVK : ∀ z, V ((Vi + (θ * Δt) • A) z) = z + (θ * Δt) • V (A z) := by
    intro z
    rw [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hVVi]
  have hco : ∀ z, (1 - θ * γ * Δt) * ‖z‖ ^ 2 ≤ ⟪V ((Vi + (θ * Δt) • A) z), z⟫ := by
    intro z
    rw [hVK, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm]
    have := mul_le_mul_of_nonneg_left (hγ z) (mul_nonneg hθ hΔt)
    nlinarith
  have hc : 0 < 1 - θ * γ * Δt := by linarith
  have hinj : Function.Injective (Vi + (θ * Δt) • A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h := hco z
    rw [hz, map_zero, inner_zero_left] at h
    exact eq_zero_of_mul_norm_sq_nonpos hc h
  refine ⟨⟨hinj, LinearMap.surjective_of_injective hinj⟩, fun y z hz => ?_⟩
  have h1 := hco z
  rw [hz] at h1
  have h2 := real_inner_le_norm (V y) z
  rcases (norm_nonneg z).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · nlinarith

/-- **Lemma 5.3 (ii) of [AdakEtAl2026]**: for `1/2 ≤ θ ≤ 1`, `γ, Δt ≥ 0` and `θ γ Δt < 1`,
one exact θ-step `K z = B x` (`K = V⁻¹ + θ Δt A`, `B = V⁻¹ - (1 - θ) Δt A`) satisfies
`(1 - θ γ Δt) ‖z‖_E ≤ (1 + (1 - θ) γ Δt) ‖x‖_E`, i.e. `‖K⁻¹ B‖_E ≤ ϑ`. -/
theorem thetaMethod_step_le {Vi V A : E →ₗ[ℝ] E} (hVVi : ∀ z, V (Vi z) = z) {γ θ Δt : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hγ0 : 0 ≤ γ) (hΔt : 0 ≤ Δt)
    (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫) (hs : θ * γ * Δt < 1) {x z : E}
    (hz : Vi z + (θ * Δt) • A z = Vi x - ((1 - θ) * Δt) • A x) :
    (1 - θ * γ * Δt) * ‖z‖ ≤ (1 + (1 - θ) * γ * Δt) * ‖x‖ := by
  set zb := θ • z + (1 - θ) • x with hzb
  have hV := congrArg V hz
  rw [map_add, map_sub, map_smul, map_smul, hVVi, hVVi] at hV
  have hVA : V (A zb) = θ • V (A z) + (1 - θ) • V (A x) := by
    rw [hzb, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  have hw : z - x = -(Δt • V (A zb)) := by
    rw [hVA, smul_add, smul_smul, smul_smul]
    have hz' : z = x - ((1 - θ) * Δt) • V (A x) - (θ * Δt) • V (A z) := by
      rw [← hV]; abel
    conv_lhs => rw [hz']
    rw [mul_comm Δt θ, mul_comm Δt (1 - θ)]
    abel
  set a := ‖z‖ with ha
  set b := ‖x‖ with hb
  have hzbn : ‖zb‖ ≤ θ * a + (1 - θ) * b := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by linarith)]
  have hW : 0 ≤ θ * a + (1 - θ) * b := by
    have := norm_nonneg z; have := norm_nonneg x
    nlinarith
  have hsq : ‖zb‖ ^ 2 ≤ (θ * a + (1 - θ) * b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzbn 2
  have hinner : ⟪zb, z - x⟫ ≤ γ * Δt * ‖zb‖ ^ 2 := by
    rw [hw, inner_neg_right, real_inner_smul_right]
    have := mul_le_mul_of_nonneg_left (hγ zb) hΔt
    nlinarith
  have hexp : ⟪zb, z - x⟫ = θ * a ^ 2 - (1 - θ) * b ^ 2 + (1 - 2 * θ) * ⟪z, x⟫ := by
    rw [hzb, inner_add_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm x z]
    ring
  have hcs : ⟪z, x⟫ ≤ a * b := real_inner_le_norm z x
  have hkey : (a - b) * (θ * a + (1 - θ) * b) ≤ γ * Δt * (θ * a + (1 - θ) * b) ^ 2 := by
    have h1 : (1 - 2 * θ) * (a * b) ≤ (1 - 2 * θ) * ⟪z, x⟫ :=
      mul_le_mul_of_nonpos_left hcs (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hγ0 hΔt)
    nlinarith
  have ha0 : 0 ≤ a := norm_nonneg z
  have hb0 : 0 ≤ b := norm_nonneg x
  rcases hW.eq_or_lt with h0 | hpos
  · have hθa : θ * a = 0 := by nlinarith
    have : a = 0 := by
      rcases mul_eq_zero.1 hθa with h | h
      · linarith
      · exact h
    rw [this]
    nlinarith [mul_nonneg hγ0 hΔt]
  · have : a - b ≤ γ * Δt * (θ * a + (1 - θ) * b) := by
      have h3 : (a - b) * (θ * a + (1 - θ) * b) ≤
          (γ * Δt * (θ * a + (1 - θ) * b)) * (θ * a + (1 - θ) * b) := by nlinarith
      exact le_of_mul_le_mul_right h3 hpos
    nlinarith

end ThetaMethod

/-! ### Rothe steps on cones: optimality and energy estimates ([BachmayrEtAl2021, Lemma 4.4]) -/

section Rothe

/-- **Optimality along rays for minimisers on cones** ([BachmayrEtAl2021], proof of Lemma 4.4:
"since `M` is a cone ... the optimality condition holds with `v = u_{i+1}`").  If `M` is a cone
(`s • u ∈ M` for `u ∈ M`, `s > 0`, e.g. the low-rank variety `M_{≤ r}`), `u ∈ M` minimises `J`
on `M` and `J` is differentiable at `u`, then `J'(u) u = 0`. -/
theorem cone_minimizer_fderiv_self {M : Set E} (hM : ∀ u ∈ M, ∀ s : ℝ, 0 < s → s • u ∈ M)
    {J : E → ℝ} {J' : E →L[ℝ] ℝ} {u : E} (hu : u ∈ M) (hmin : ∀ v ∈ M, J u ≤ J v)
    (hJ : HasFDerivAt J J' u) : J' u = 0 := by
  have hd : HasDerivAt (fun s : ℝ => s • u) u 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const u
  have hJ1 : HasFDerivAt J J' ((fun s : ℝ => s • u) 1) := by simpa using hJ
  have hφ : HasDerivAt (fun s : ℝ => J (s • u)) (J' u) 1 := hJ1.comp_hasDerivAt (1 : ℝ) hd
  have hloc : IsLocalMin (fun s : ℝ => J (s • u)) 1 := by
    filter_upwards [Ioi_mem_nhds one_pos] with s hs
    simpa using hmin _ (hM u hu s hs)
  exact hloc.hasDerivAt_eq_zero hφ

/-- **Optimality condition of a Rothe step on a cone**: if `u₁ ∈ M` minimises
`½ ‖v - u₀‖² + h Ψ(v)` over a cone `M` and `Ψ` has derivative `Ψ'` at `u₁`, then
`⟪u₁ - u₀, u₁⟫ + h Ψ'(u₁) = 0` ([BachmayrEtAl2021, eq. (3.1)] with `v = u_{i+1}`). -/
theorem rothe_cone_optimality {M : Set E} (hM : ∀ u ∈ M, ∀ s : ℝ, 0 < s → s • u ∈ M)
    {Ψ : E → ℝ} {Ψ' : E →L[ℝ] ℝ} {u₀ u₁ : E} {h : ℝ} (hu₁ : u₁ ∈ M)
    (hmin : ∀ v ∈ M, ‖u₁ - u₀‖ ^ 2 / 2 + h * Ψ u₁ ≤ ‖v - u₀‖ ^ 2 / 2 + h * Ψ v)
    (hΨ : HasFDerivAt Ψ Ψ' u₁) : ⟪u₁ - u₀, u₁⟫ + h * Ψ' u₁ = 0 := by
  have hq : HasFDerivAt (fun v : E => ‖v - u₀‖ ^ 2 / 2)
      ((innerSL ℝ (u₁ - u₀)).comp (ContinuousLinearMap.id ℝ E)) u₁ := by
    have h1 := hasFDerivAt_half_norm_sq (u₁ - u₀)
    have h2 := (hasFDerivAt_id (𝕜 := ℝ) u₁).sub_const u₀
    have h3 := h1.comp u₁ h2
    exact h3
  have hJ := hq.add (hΨ.const_mul h)
  have := cone_minimizer_fderiv_self hM (J := fun v => ‖v - u₀‖ ^ 2 / 2 + h * Ψ v) hu₁ hmin hJ
  simp at this
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

/-- Polarisation: `2 ⟪u₁ - u₀, u₁⟫ = ‖u₁‖² - ‖u₀‖² + ‖u₁ - u₀‖²`. -/
theorem two_inner_sub_self (u₀ u₁ : E) :
    2 * ⟪u₁ - u₀, u₁⟫ = ‖u₁‖ ^ 2 - ‖u₀‖ ^ 2 + ‖u₁ - u₀‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
  ring

/-- **One-step energy estimate of the Rothe scheme** ([BachmayrEtAl2021, Lemma 4.4], first
display).  If `⟪u₁ - u₀, u₁⟫ + h a₁ = h g₁` with coercivity `a₁ ≥ μ v₁²` (`v₁ = ‖u₁‖_V`,
`a₁ = a(u₁, u₁)`), forcing `g₁ ≤ φ v₁` (`g₁ = ⟨f, u₁⟩`, `φ = ‖f‖_{V*}`), `μ > 0` and `h ≥ 0`,
then `‖u₁‖² - ‖u₀‖² + ‖u₁ - u₀‖² + h μ v₁² ≤ h φ² / μ`. -/
theorem rothe_energy_step {u₀ u₁ : E} {h μ a₁ g₁ v₁ φ : ℝ} (hh : 0 ≤ h) (hμ : 0 < μ)
    (hopt : ⟪u₁ - u₀, u₁⟫ + h * a₁ = h * g₁) (ha : μ * v₁ ^ 2 ≤ a₁) (hg : g₁ ≤ φ * v₁) :
    ‖u₁‖ ^ 2 - ‖u₀‖ ^ 2 + ‖u₁ - u₀‖ ^ 2 + h * μ * v₁ ^ 2 ≤ h * φ ^ 2 / μ := by
  have hpol := two_inner_sub_self u₀ u₁
  have hyoung : 2 * φ * v₁ ≤ φ ^ 2 / μ + μ * v₁ ^ 2 := by
    have : 0 ≤ (φ - μ * v₁) ^ 2 / μ := by positivity
    have e : (φ - μ * v₁) ^ 2 / μ = φ ^ 2 / μ - 2 * φ * v₁ + μ * v₁ ^ 2 := by
      field_simp; ring
    linarith
  have h1 := mul_le_mul_of_nonneg_left ha hh
  have h2 := mul_le_mul_of_nonneg_left hg hh
  have h3 := mul_le_mul_of_nonneg_left hyoung hh
  rw [mul_div_assoc]
  nlinarith

omit [InnerProductSpace ℝ E] in
/-- **Telescoped energy estimate** ([BachmayrEtAl2021, Lemma 4.4], eq. (4.1)): if every Rothe step
satisfies the one-step estimate of `rothe_energy_step`, then
`‖u_N‖² + Σ_{i<N} ‖u_{i+1} - u_i‖² + h μ Σ_{i<N} v_{i+1}² ≤ ‖u₀‖² + (h/μ) Σ_{i<N} φ_{i+1}²`. -/
theorem rothe_energy_sum {u : ℕ → E} {v φ : ℕ → ℝ} {h μ : ℝ}
    (hstep : ∀ i, ‖u (i + 1)‖ ^ 2 - ‖u i‖ ^ 2 + ‖u (i + 1) - u i‖ ^ 2 + h * μ * v (i + 1) ^ 2 ≤
      h * φ (i + 1) ^ 2 / μ) (N : ℕ) :
    ‖u N‖ ^ 2 + ∑ i ∈ Finset.range N, ‖u (i + 1) - u i‖ ^ 2 +
        h * μ * ∑ i ∈ Finset.range N, v (i + 1) ^ 2 ≤
      ‖u 0‖ ^ 2 + h / μ * ∑ i ∈ Finset.range N, φ (i + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have := hstep N
    have e : h * φ (N + 1) ^ 2 / μ = h / μ * φ (N + 1) ^ 2 := by ring
    rw [e] at this
    nlinarith

end Rothe

/-! ### Minimising-movement (variational implicit) low-rank steps (OP-ST-17) -/

section MinimizingMovement

/-- The minimising-movement objective `ℰ(X) + ‖X - X₀‖² / (2 h)`. -/
noncomputable def mmObjective (ℰ : E → ℝ) (h : ℝ) (X₀ X : E) : ℝ :=
  ℰ X + ‖X - X₀‖ ^ 2 / (2 * h)

omit [InnerProductSpace ℝ E] in
/-- **Unconditional energy stability of minimising-movement steps** (OP-ST-17 (a), arXiv
2305.11532).  Any `X₁` whose objective does not exceed the objective of the admissible competitor
`X₀` (in particular any minimiser over a set `S ∋ X₀`, such as `M_{≤ r}`) satisfies
`ℰ(X₁) + ‖X₁ - X₀‖² / (2 h) ≤ ℰ(X₀)` — for **every** `h`, no step-size restriction. -/
theorem mm_energy_le {ℰ : E → ℝ} {h : ℝ} {X₀ X₁ : E}
    (h1 : mmObjective ℰ h X₀ X₁ ≤ mmObjective ℰ h X₀ X₀) :
    ℰ X₁ + ‖X₁ - X₀‖ ^ 2 / (2 * h) ≤ ℰ X₀ := by
  simpa [mmObjective] using h1

omit [InnerProductSpace ℝ E] in
/-- **Telescoped energy decay** for minimising-movement iterates (OP-ST-17 (a)): if every step
does not increase the objective relative to staying put, then for `h > 0`
`ℰ(X_n) + Σ_{k<n} ‖X_{k+1} - X_k‖² / (2h) ≤ ℰ(X_0)`; in particular `ℰ` is nonincreasing. -/
theorem mm_energy_sum {ℰ : E → ℝ} {h : ℝ} {X : ℕ → E}
    (hstep : ∀ k, mmObjective ℰ h (X k) (X (k + 1)) ≤ mmObjective ℰ h (X k) (X k)) (n : ℕ) :
    ℰ (X n) + ∑ k ∈ Finset.range n, ‖X (k + 1) - X k‖ ^ 2 / (2 * h) ≤ ℰ (X 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := mm_energy_le (hstep n)
    linarith

omit [InnerProductSpace ℝ E] in
/-- **Existence of a minimising-movement step** (OP-ST-17 (b)).  In a proper space (e.g. any
finite-dimensional space, such as matrices with the Frobenius norm), for a closed admissible set
`S ∋ X₀` (e.g. `M_{≤ r}`; its closedness is taken as a hypothesis here), a continuous energy
bounded below and `h > 0`, the objective attains its minimum on `S`. -/
theorem mm_exists_minimizer [ProperSpace E] {S : Set E} (hS : IsClosed S) {X₀ : E}
    (hX₀ : X₀ ∈ S) {ℰ : E → ℝ} (hℰ : Continuous ℰ) {m : ℝ} (hm : ∀ X, m ≤ ℰ X) {h : ℝ}
    (hh : 0 < h) : ∃ X₁ ∈ S, ∀ X ∈ S, mmObjective ℰ h X₀ X₁ ≤ mmObjective ℰ h X₀ X := by
  set J := mmObjective ℰ h X₀ with hJdef
  have hJc : Continuous J := by
    change Continuous (fun X => ℰ X + ‖X - X₀‖ ^ 2 / (2 * h))
    fun_prop
  set K := S ∩ {X | J X ≤ J X₀} with hK
  have hKc : IsClosed K := hS.inter (isClosed_le hJc continuous_const)
  set R := Real.sqrt (2 * h * (J X₀ - m)) with hR
  have hKb : K ⊆ Metric.closedBall X₀ R := by
    intro X hX
    rw [Metric.mem_closedBall, dist_eq_norm, hR]
    have h1 : J X ≤ J X₀ := hX.2
    have h2 : ‖X - X₀‖ ^ 2 ≤ 2 * h * (J X₀ - m) := by
      have h3 : J X = ℰ X + ‖X - X₀‖ ^ 2 / (2 * h) := rfl
      have h4 := hm X
      have h5 : ‖X - X₀‖ ^ 2 / (2 * h) ≤ J X₀ - m := by linarith
      rwa [div_le_iff₀ (by positivity), mul_comm] at h5
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hKcpt : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKc (Metric.isBounded_closedBall.subset hKb)
  obtain ⟨X₁, hX₁, hmin⟩ := hKcpt.exists_isMinOn ⟨X₀, hX₀, show J X₀ ≤ J X₀ from le_rfl⟩
    hJc.continuousOn
  refine ⟨X₁, hX₁.1, fun X hX => ?_⟩
  by_cases hXK : J X ≤ J X₀
  · exact hmin ⟨hX, hXK⟩
  · exact (hX₁.2).trans (le_of_lt (not_le.1 hXK))

/-- **Uniqueness on convex admissible sets under a step-size condition** (OP-ST-17 (c), positive
part).  If `S` is convex and `ℰ` is `κ`-semiconvex on `S`
(`ℰ((X+Y)/2) ≤ (ℰ X + ℰ Y)/2 + κ ‖X - Y‖² / 8`, e.g. `κ = 1/ε²` for Allen–Cahn), then for
`h > 0` with `h κ < 1` the minimising-movement step has at most one minimiser on `S`. -/
theorem mm_unique_of_semiconvex {S : Set E} (hS : Convex ℝ S) {ℰ : E → ℝ} {κ : ℝ}
    (hℰ : ∀ X ∈ S, ∀ Y ∈ S, ℰ ((1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y) ≤
      (ℰ X + ℰ Y) / 2 + κ * ‖X - Y‖ ^ 2 / 8)
    {h : ℝ} (hh : 0 < h) (hκ : h * κ < 1) {X₀ X Y : E} (hX : X ∈ S) (hY : Y ∈ S)
    (hXmin : ∀ Z ∈ S, mmObjective ℰ h X₀ X ≤ mmObjective ℰ h X₀ Z)
    (hYmin : ∀ Z ∈ S, mmObjective ℰ h X₀ Y ≤ mmObjective ℰ h X₀ Z) : X = Y := by
  set Z := (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y with hZ
  have hZS : Z ∈ S := hS hX hY (by norm_num) (by norm_num) (by norm_num)
  have hpar : ‖Z - X₀‖ ^ 2 = (‖X - X₀‖ ^ 2 + ‖Y - X₀‖ ^ 2) / 2 - ‖X - Y‖ ^ 2 / 4 := by
    have e1 : Z - X₀ = (1 / 2 : ℝ) • ((X - X₀) + (Y - X₀)) := by
      rw [hZ, smul_add]
      module
    have e2 : X - Y = (X - X₀) - (Y - X₀) := by abel
    have hp := parallelogram_law_with_norm ℝ (X - X₀) (Y - X₀)
    rw [e1, norm_smul, mul_pow, e2]
    rw [Real.norm_of_nonneg (by norm_num)]
    linarith
  have h1 := hXmin Z hZS
  have h2 := hYmin X hX
  have h3 := hXmin Y hY
  have h4 := hℰ X hX Y hY
  rw [← hZ] at h4
  simp only [mmObjective] at h1 h2 h3
  rw [hpar] at h1
  set t := 1 / (2 * h) with ht
  have htpos : 0 < t := by positivity
  have hdiv : ∀ x : ℝ, x / (2 * h) = x * t := fun x => by rw [ht, mul_one_div]
  rw [hdiv, hdiv] at h1
  rw [hdiv, hdiv] at h3
  rw [hdiv, hdiv] at h2
  have hth : t * (2 * h) = 1 := by rw [ht]; field_simp
  have hd : (1 - h * κ) * ‖X - Y‖ ^ 2 ≤ 0 := by
    have h5 : ‖X - Y‖ ^ 2 / 4 * t ≤ κ * ‖X - Y‖ ^ 2 / 8 := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 8 * h)
    have h7 : 8 * h * (‖X - Y‖ ^ 2 / 4 * t) = ‖X - Y‖ ^ 2 := by
      calc 8 * h * (‖X - Y‖ ^ 2 / 4 * t) = ‖X - Y‖ ^ 2 * (t * (2 * h)) := by ring
        _ = ‖X - Y‖ ^ 2 := by rw [hth, mul_one]
    nlinarith
  exact sub_eq_zero.1 (eq_zero_of_mul_norm_sq_nonpos (by linarith) hd)

end MinimizingMovement

section MinimizingMovementMatrix

open Matrix
open scoped LeanDLRA.Frobenius

/-- **Non-uniqueness on the rank-one variety for every step size** (OP-ST-17 (c), negative
part).  On `2 × 2` matrices with the Frobenius norm take the `1`-strongly convex energy
`ℰ(X) = ‖X‖²/2 - tr X`, `X₀ = 0` (rank `0`) and the admissible set `S = {det X = 0}`, which is
the rank-`≤ 1` variety `M_{≤1}`.  For **every** `h > 0` the minimising-movement step has the two
distinct minimisers `c E₁₁` and `c E₂₂`, `c = h/(h+1)`.  So on `M_{≤ r}` neither strong convexity
of `ℰ` nor a step-size condition yields uniqueness; `mm_unique_of_semiconvex` needs a convex
admissible set. -/
theorem mm_nonunique_rankOne {h : ℝ} (hh : 0 < h) :
    let ℰ : Matrix (Fin 2) (Fin 2) ℝ → ℝ := fun X => ‖X‖ ^ 2 / 2 - X.trace
    let S := {X : Matrix (Fin 2) (Fin 2) ℝ | X.det = 0}
    let X₁ : Matrix (Fin 2) (Fin 2) ℝ := !![h / (h + 1), 0; 0, 0]
    let X₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, h / (h + 1)]
    X₁ ∈ S ∧ X₂ ∈ S ∧ X₁ ≠ X₂ ∧ (∀ X ∈ S, mmObjective ℰ h 0 X₁ ≤ mmObjective ℰ h 0 X) ∧
      ∀ X ∈ S, mmObjective ℰ h 0 X₂ ≤ mmObjective ℰ h 0 X := by
  intro ℰ S X₁ X₂
  set c := h / (h + 1) with hc
  have hc0 : 0 < c := by positivity
  set u := 1 / h with hu
  have hu0 : 0 < u := by positivity
  have hcu : c * (1 + u) = 1 := by rw [hc, hu]; field_simp
  have hdiv : ∀ x : ℝ, x / (2 * h) = x * u / 2 := fun x => by rw [hu]; field_simp
  -- the objective in coordinates
  have hobj : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, mmObjective ℰ h 0 X =
      (1 + u) / 2 * (X 0 0 ^ 2 + X 0 1 ^ 2 + X 1 0 ^ 2 + X 1 1 ^ 2) - (X 0 0 + X 1 1) := by
    intro X
    simp only [mmObjective, ℰ, sub_zero, hdiv, Frobenius.norm_sq_eq_sum, Fin.sum_univ_two,
      trace_fin_two]
    ring
  have hlow : ∀ X ∈ S, -c / 2 ≤ mmObjective ℰ h 0 X := by
    intro X hX
    have hdet : X 0 0 * X 1 1 - X 0 1 * X 1 0 = 0 := by
      have : X.det = 0 := hX
      rwa [det_fin_two] at this
    rw [hobj]
    have hN : (X 0 0 + X 1 1) ^ 2 ≤ X 0 0 ^ 2 + X 0 1 ^ 2 + X 1 0 ^ 2 + X 1 1 ^ 2 := by
      nlinarith [sq_nonneg (X 0 1 - X 1 0)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + u) / 2)
      (sq_nonneg (X 0 0 + X 1 1 - c)), mul_le_mul_of_nonneg_left hN
      (by positivity : (0 : ℝ) ≤ (1 + u) / 2)]
  have hv1 : mmObjective ℰ h 0 X₁ = -c / 2 := by
    rw [hobj]
    simp only [X₁, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    nlinarith [hcu]
  have hv2 : mmObjective ℰ h 0 X₂ = -c / 2 := by
    rw [hobj]
    simp only [X₂, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    nlinarith [hcu]
  refine ⟨?_, ?_, ?_, fun X hX => hv1 ▸ hlow X hX, fun X hX => hv2 ▸ hlow X hX⟩
  · change X₁.det = 0
    simp [X₁, det_fin_two]
  · change X₂.det = 0
    simp [X₂, det_fin_two]
  · intro h12
    have h00 := congrFun (congrFun h12 0) 0
    simp only [X₁, X₂, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one] at h00
    linarith [hc, (by positivity : (0 : ℝ) < h / (h + 1))]

end MinimizingMovementMatrix

/-! ### Implicit BUG steps are well posed and norm-stable (OP-ST-03) -/

section ImplicitBUG

/-- **Well-posedness and stability of an implicit (backward Euler) BUG step** (OP-ST-03).  Let
`F(t, ·)` be Lipschitz and one-sided Lipschitz with `ℓ`, `h ≥ 0`, `h ℓ < 1`, and let `P₀, Q₀`
be orthogonal projectors with `P₀ Y₀ = Q₀ Y₀ = Y₀`.  Then the implicit K-step
`YK = Q₀ (Y₀ + h F(YK))` and L-step `YL = P₀ (Y₀ + h F(YL))` have unique solutions, and for any
commuting orthogonal projectors `P₁, Q₁` (bases built from `YK`, `YL`) the implicit Galerkin
S-step `YS = P₁ Q₁ (P₁ Q₁ Y₀ + h F(YS))` has a unique solution with
`(1 - h ℓ) ‖YS‖ ≤ ‖Y₀‖` as soon as `⟪F(t, y), y⟫ ≤ ℓ ‖y‖²` (e.g. `F(t, 0) = 0`).  Hence
for dissipative fields (`ℓ ≤ 0`) the implicit BUG integrator is norm-nonincreasing for every
step size.  The same statement covers Tucker and tree-tensor-network bases, which only change
the projectors. -/
theorem implicitBUG_wellPosed [CompleteSpace E] {F : ℝ → E → E} {ℓ L h : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hL : IsLipschitzField F L) (hh : 0 ≤ h)
    (hhℓ : h * ℓ < 1) (t : ℝ) {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀)
    (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (hF0 : ∀ y, ⟪F t y, y⟫ ≤ ℓ * ‖y‖ ^ 2) (Y₀ : E) :
    (∃! YK, YK = Q₀ (Y₀ + h • F t YK)) ∧ (∃! YL, YL = P₀ (Y₀ + h • F t YL)) ∧
      (∃! YS, YS = (P₁ * Q₁) ((P₁ * Q₁) Y₀ + h • F t YS)) ∧
      ∀ YS, YS = (P₁ * Q₁) ((P₁ * Q₁) Y₀ + h • F t YS) → (1 - h * ℓ) * ‖YS‖ ≤ ‖Y₀‖ := by
  have hPQ := hP₁.mul hQ₁ hc
  refine ⟨existsUnique_implicitGalerkin hF hL hQ₀ hh hhℓ t Y₀,
    existsUnique_implicitGalerkin hF hL hP₀ hh hhℓ t Y₀,
    existsUnique_implicitGalerkin hF hL hPQ hh hhℓ t _, fun YS hYS => ?_⟩
  exact (galerkin_implicitEuler_norm_le hPQ hh (hF0 YS) hYS).trans (hPQ.norm_le Y₀)

end ImplicitBUG

end LeanDLRA
