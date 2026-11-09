import LeanDLRA.Stability.Energy
import LeanDLRA.LinearAlgebra.Projection.Defs

/-!
# Conservation properties of dynamical low-rank integrators

Kinetic equations conserve mass, momentum and (sometimes) energy, i.e. the velocity moments
`ϕ = ⟨f, U⟩_v` of the distribution function with respect to a few functions
`U = (1, v, v²)` satisfy *local conservation laws* `∂ₜ ϕ = ⟨F(f), U⟩_v` (with a flux in
divergence form), and integrating in space gives *global* invariants.  Standard dynamical
low-rank integrators destroy these laws twice: the Galerkin step projects the flux onto the
spatial basis, and the SVD truncation does not preserve moments.  The conservative integrators of
Einkemmer–Ostermann–Scalone (arXiv 2206.09374) and Einkemmer–Kusch–Schotthöfer
(arXiv 2311.06399) cure both defects by

* keeping the conserved velocity functions `U` in the velocity basis (as already done, for a
  fixed-rank scheme with modified Galerkin equations, by Einkemmer–Joseph 2021), here through
  augmentation and the *conservative truncation* of arXiv 2206.09374 (a similar approach is
  Guo–Qiu, arXiv 2201.10397) that only truncates the part orthogonal to `U`, and
* making sure that the spatial basis contains the flux moments (automatic for the augmented BUG
  integrator with explicit Euler substeps, enforced by one extra augmentation for general
  Runge–Kutta S-steps).

Following the abstract framework of the library, everything is formulated on a real inner product
space `E` with orthogonal projectors.  The velocity moments are encoded by an orthogonal projector
`C` (for matrices: the right projector `Y ↦ Y U Uᵀ` onto the conserved velocity directions), so
that `C Y = ϕ Uᵀ` carries exactly the moments `ϕ = Y U`; `C` commutes with every left (spatial)
projector, and `Q C = C` expresses that a right projector `Q` (a velocity basis) contains `U`.
Global invariants are linear functionals `⟪c, ·⟫` (e.g. `c = 1ₓ ⊗ U₁` for the total mass).

## Main results

Linear invariants of Galerkin steps (exact and explicit Euler substeps).
* `inner_apply_sub_inner`, `abs_inner_apply_sub_le`: a projection changes `⟪c, ·⟫` by
  `-⟪(1 - P) c, (1 - P) z⟫`; in particular not at all if `P c = c`.
* `galerkinEulerStep_inner`, `bug_euler_inner_eq`, `galerkinEulerIter_inner_eq`,
  `galerkinRK_inner`, `galerkinRK_inner_eq`: explicit Euler / Runge–Kutta Galerkin steps,
  the explicit Euler BUG step and its iterates conserve `⟪c, ·⟫` if `⟪c, F⟫ = 0` and the Galerkin
  space contains `c` (no assumption on the bases otherwise).  For the explicit Euler K- and
  L-steps see `inner_projEuler_eq`, `inner_projEuler_eq_of_mem` in `Foundations/Galerkin.lean`.
* `bug_inner_eq`: the same for the exact BUG step (exact S-step started at `P₁ Q₁ Y₀`).
* `kslEulerStep_inner_eq`, `backward_inner_const`, `ksl_inner_eq`: the projector-splitting
  integrator (explicit Euler or exact substeps, including the backward S-step) conserves
  `⟪c, ·⟫` if `Q₀ c = c` and `P₁ c = c`.  No commutation of the left and right projectors is
  assumed anywhere.
* `inner_eq_of_forall_step`: per-step conservation gives conservation over many steps.

Conservative truncation (arXiv 2206.09374, Algorithm 1, steps 5–12).
* `consTrunc C T Ŷ = C Ŷ + T ((1 - C) Ŷ)`: the truncation `T` only acts on the part of `Ŷ`
  orthogonal to the conserved directions.
* `consTrunc_moments`, `consTrunc_inner`: if `T` maps into `range (1 - C)`, all moments and all
  invariants `⟪c, ·⟫` with `C c = c` are conserved exactly.
* `sub_consTrunc`, `norm_sub_consTrunc`, `norm_sub_consTrunc_le`: the truncation error is
  exactly `‖(1 - C) Ŷ - T ((1 - C) Ŷ)‖` (the discarded singular values of the remainder).
* `norm_consTrunc_sq`, `norm_consTrunc_le`: Pythagoras; a norm-nonincreasing `T` gives a
  norm-nonincreasing conservative truncation (so `L²`-stability is not affected).
* `consTrunc_optimal`: optimality among all moment-preserving approximations whose remainder
  lies in a prescribed set (e.g. of rank `≤ r - m`).
* `IsOrthProj.add_of_comp_eq_zero`, `consTrunc_mem_range`: the new velocity basis `[U, W]`
  (projector `C + R`) again contains the conserved directions, and contains `Y₁`;
  `consTrunc_proj_eq`: truncation by a projector `R ⊥ C` is the projection onto `[U, W]`.

Local conservation laws (arXiv 2206.09374, Theorems 1–2 and the moment part of Theorem 3, abstract
analogue of Lemmas 1–2; arXiv 2311.06399, §§5–7).  The S-step is modelled as
`P̂ Q̂ (Y₀ + h F(Y₀))`; this is the BUG S-step (whose field is evaluated at `P̂ Q̂ Y₀`) whenever the
augmented bases contain the old ones, `P̂ Q̂ Y₀ = Y₀`.
* `moment_galerkin`, `galerkin_moment_hasDerivWithinAt`: the Galerkin moment identity
  `⟨P_V̂ P_X̂ F, U⟩_v = P_X̂ ⟨F, U⟩_v` and the continuous law `∂ₜ ϕ_S = P_X̂ ⟨F(Y_S), U⟩_v`
  (arXiv 2311.06399, eq. (5)).
* `consBug_euler_flux_mem` (abstract analogue of Lemmas 1–2 of arXiv 2206.09374, following the
  argument of §6.1 of arXiv 2311.06399): the augmented spatial basis contains the combined flux
  moments `⟨F(Y₀), U⟩_v` of the explicit Euler K-step, without a `∇ₓX` augmentation.
* `consBug_euler_moment`, `consBug_euler_local_law`: the explicit Euler augmented BUG step with
  conservative truncation reproduces *exactly* the moment equations of the full explicit Euler
  scheme, `C Y₁ = C (Y₀ + h F(Y₀))` — the discrete continuity and momentum equations
  (Theorems 1–2); `consBug_euler_inner`, `consBug_euler_inner_eq`: global invariants;
  `consBug_euler_moment_functional`: reduction lemma — every quantity depending only on the
  moments takes the same value as for the full explicit Euler step (so the energy identity (26)
  of Theorem 3 transfers once known for the full scheme; (26) itself is not formalised here);
  `consBug_euler_norm_le`: the step is moreover `L²`-stable under the full scheme's CFL condition.
* `consBug_rk_moment`, `consBug_rk_local_law`, `consBug_rk_local_law_iff`, `consBug_rk_inner_eq`:
  for an explicit
  Runge–Kutta S-step the discrete law `ϕ¹ = ϕ⁰ + h P_X̄ ∑ bᵢ ⟨F⁽ⁱ⁾, U⟩_v` (eq. (8)), which is the
  exact law (7) iff the spatial basis contains the RK flux moment;
  `norm_sub_apply_le_of_le`: the extra augmentation `X̄ = [X̂, ∑ bᵢ ⟨F⁽ⁱ⁾, U⟩_v]` can only
  decrease the projection (robust) errors.
* `kStep_moment_hasDerivWithinAt`, `consParallelBug_moment`, `consParallelBug_inner_eq`:
  the K-step satisfies the exact local law `∂ₜ ϕ = ⟨F(t, Y_K), U⟩_v` (eq. (11)) and the
  conservative parallel BUG integrator (§7) inherits it.

Metric projections, motivated by the positivity-preserving corrections (3.3), (4.4) of
arXiv 2606.31662 (standard convex-projection facts, not results of that paper).
* `norm_sub_sq_add_le_of_metricProj`, `norm_sub_le_of_metricProj`, `exists_metricProj`: the
  metric projection onto a closed convex set `K` exists and is at least as close to every
  *element of `K`* as the uncorrected state (Kolmogorov criterion / obtuse-angle inequality).
  In arXiv 2606.31662 `K` is the admissible set within the current low-rank bases, so this
  covers comparison states representable in these bases, not the analytical solution `F_a` of
  the paper's error split (3.2) in general.

## Conventions

In the code the augmented bases `P̂, Q̂` are called `Pa, Qa` and the enlarged spatial basis `P̄`
of the Runge–Kutta construction is called `Pe`.  The truncation `T : E → E` is an arbitrary map
(in practice an SVD truncation of the remainder); only the properties used are assumed.  As in
`Stability/Energy.lean`, discrete steps use frozen fields `F : E → E` and Runge–Kutta stages
`G i = F(Y⁽ⁱ⁾)` are arbitrary vectors.  Rank bounds (`rank Y₁ ≤ m + (r - m)`) are matrix
statements and are not part of the abstract layer.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Rank-one projectors (for examples) -/

section RankOne

/- `rankOneProj` and `rankOneProj_apply` are defined in
`LeanDLRA/LinearAlgebra/Projection/Defs.lean`. -/

/-- For a unit vector `e`, `x ↦ ⟪e, x⟫ e` is an orthogonal projector. -/
lemma isOrthProj_rankOneProj {e : E} (he : ‖e‖ = 1) : IsOrthProj (rankOneProj e) where
  idem x := by
    simp only [rankOneProj_apply, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    simp
  symm x y := by
    simp only [rankOneProj_apply, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm e x]
    ring

end RankOne

/-! ### Linear invariants of Galerkin steps -/

section LinearInvariants

variable {P : E →L[ℝ] E}

/-- **Conservation defect of a projection**: `⟪c, P z⟫ - ⟪c, z⟫ = -⟪(1 - P) c, (1 - P) z⟫`.
In particular a projection conserves `⟪c, ·⟫` if `P c = c`. -/
theorem inner_apply_sub_inner (hP : IsOrthProj P) (c z : E) :
    ⟪c, P z⟫ - ⟪c, z⟫ = -⟪c - P c, z - P z⟫ := by
  have h1 : ⟪c, P z⟫ = ⟪P c, z⟫ := (hP.symm c z).symm
  have h2 : ⟪P c, P z⟫ = ⟪P c, z⟫ := hP.inner_comp c z
  rw [inner_sub_left, inner_sub_right, inner_sub_right, h2, h1]
  ring

/-- **Robust bound on the conservation defect of a projection**:
`|⟪c, P z⟫ - ⟪c, z⟫| ≤ ‖(1 - P) c‖ ‖(1 - P) z‖`, the product of the distances of the conserved
direction and of the projected state to the Galerkin space. -/
theorem abs_inner_apply_sub_le (hP : IsOrthProj P) (c z : E) :
    |⟪c, P z⟫ - ⟪c, z⟫| ≤ ‖c - P c‖ * ‖z - P z‖ := by
  rw [inner_apply_sub_inner hP, abs_neg]
  exact abs_real_inner_le_norm _ _

/-- **Explicit Euler Galerkin steps and linear invariants.**  If the Galerkin space contains the
conserved direction, `P c = c`, then the step `x ↦ P (P x + h F(P x))` changes `⟪c, ·⟫` exactly as
the full explicit Euler step from `P x` does: `⟪c, x₁⟫ = ⟪c, x⟫ + h ⟪c, F(P x)⟫`. -/
theorem galerkinEulerStep_inner (hP : IsOrthProj P) {c : E} (hc : P c = c) (F : E → E) (h : ℝ)
    (x : E) : ⟪c, galerkinEulerStep P F h x⟫ = ⟪c, x⟫ + h * ⟪c, F (P x)⟫ := by
  rw [galerkinEulerStep, hP.inner_apply_right_of_mem _ hc, eulerStep, inner_add_right,
    real_inner_smul_right, hP.inner_apply_right_of_mem _ hc]

/-- **Conservation of linear invariants by explicit Euler Galerkin steps**: if `P c = c` and
`⟪c, F(P x)⟫ = 0`, then `⟪c, P (P x + h F(P x))⟫ = ⟪c, x⟫`. -/
theorem galerkinEulerStep_inner_eq (hP : IsOrthProj P) {c : E} (hc : P c = c) {F : E → E}
    {h : ℝ} {x : E} (hF : ⟪c, F (P x)⟫ = 0) : ⟪c, galerkinEulerStep P F h x⟫ = ⟪c, x⟫ := by
  rw [galerkinEulerStep_inner hP hc, hF, mul_zero, add_zero]

/-- **Explicit Euler K- and L-steps and linear invariants**: the projected Euler step
`x ↦ x + h P F(t, x)` (the K-step for `P = Q₀`, the L-step for `P = P₀`) satisfies
`⟪c, x₁⟫ = ⟪c, x⟫ + h ⟪c, F(t, x)⟫` if `P c = c`.  (A specialisation of `inner_projEuler_eq`
from `Foundations/Galerkin.lean`, kept for its explicit-argument form.) -/
theorem projEuler_inner (hP : IsOrthProj P) {c : E} (hc : P c = c) (F : ℝ → E → E) (h t : ℝ)
    (x : E) : ⟪c, projEuler P F h t x⟫ = ⟪c, x⟫ + h * ⟪c, F t x⟫ :=
  inner_projEuler_eq (hP.inner_apply_right_of_mem _ hc)

/-- **Conservation of linear invariants by the explicit Euler BUG step**: if the new bases
contain the conserved direction (`P₁ c = c`, `Q₁ c = c`) and `⟪c, F y⟫ = 0` for all `y`, the BUG
step `u₁ = P₁ Q₁ (ū + h F(ū))`, `ū = P₁ Q₁ u₀`, satisfies `⟪c, u₁⟫ = ⟪c, u₀⟫`.  No commutation of
the projectors is needed. -/
theorem bug_euler_inner_eq {P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    {c : E} (hc₁ : P₁ c = c) (hc₂ : Q₁ c = c) {F : E → E} (hF : ∀ y, ⟪c, F y⟫ = 0) (h : ℝ)
    (u₀ : E) : ⟪c, P₁ (Q₁ (eulerStep F h (P₁ (Q₁ u₀))))⟫ = ⟪c, u₀⟫ := by
  rw [hP₁.inner_apply_right_of_mem _ hc₁, hQ₁.inner_apply_right_of_mem _ hc₂, eulerStep,
    inner_add_right, real_inner_smul_right, hF, mul_zero, add_zero,
    hP₁.inner_apply_right_of_mem _ hc₁, hQ₁.inner_apply_right_of_mem _ hc₂]

/-- **Conservation of linear invariants over many explicit Euler BUG steps** with step-dependent
bases `P n` (all containing `c`) and fields `F n` (all with `⟪c, F n y⟫ = 0`). -/
theorem galerkinEulerIter_inner_eq {P : ℕ → E →L[ℝ] E} (hP : ∀ n, IsOrthProj (P n)) {c : E}
    (hc : ∀ n, P n c = c) {F : ℕ → E → E} (hF : ∀ n y, ⟪c, F n y⟫ = 0) (h : ℝ) (u₀ : E)
    (n : ℕ) : ⟪c, galerkinEulerIter P F h u₀ n⟫ = ⟪c, u₀⟫ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [galerkinEulerIter, galerkinEulerStep_inner_eq (hP n) (hc n) (hF n _), ih]

/-- **Runge–Kutta Galerkin steps and linear invariants**: for an explicit Runge–Kutta S-step
`v = P (u + h ∑ᵢ bᵢ Gᵢ)` (with arbitrary stage values `Gᵢ = F(Y⁽ⁱ⁾)`) and `P c = c`,
`⟪c, v⟫ = ⟪c, u⟫ + h ∑ᵢ bᵢ ⟪c, Gᵢ⟫`. -/
theorem galerkinRK_inner (hP : IsOrthProj P) {c : E} (hc : P c = c) {s : ℕ} (b : Fin s → ℝ)
    (G : Fin s → E) (h : ℝ) (u : E) :
    ⟪c, P (u + h • ∑ i, b i • G i)⟫ = ⟪c, u⟫ + h * ∑ i, b i * ⟪c, G i⟫ := by
  rw [hP.inner_apply_right_of_mem _ hc, inner_add_right, real_inner_smul_right, inner_sum]
  simp only [real_inner_smul_right]

/-- **Runge–Kutta Galerkin steps conserve linear invariants** (all Runge–Kutta methods preserve
linear invariants, arXiv 2311.06399, §7): if `P c = c` and `⟪c, Gᵢ⟫ = 0` for all stages. -/
theorem galerkinRK_inner_eq (hP : IsOrthProj P) {c : E} (hc : P c = c) {s : ℕ} (b : Fin s → ℝ)
    {G : Fin s → E} (hG : ∀ i, ⟪c, G i⟫ = 0) (h : ℝ) (u : E) :
    ⟪c, P (u + h • ∑ i, b i • G i)⟫ = ⟪c, u⟫ := by
  rw [galerkinRK_inner hP hc]
  simp [hG]

/-- **Conservation of linear invariants by the exact BUG step.**  If the S-step
`YS' = P₁ Q₁ F(t, YS)` starts at `YS(t₀) = P₁ Q₁ Y₀`, the new bases contain the conserved
direction (`P₁ c = c`, `Q₁ c = c`) and `⟪c, F(t, x)⟫ = 0`, then `⟪c, YS(t)⟫ = ⟪c, Y₀⟫`.  (The K- and
L-steps conserve `⟪c, ·⟫` whenever `Q₀ c = c`, resp. `P₀ c = c`, by
`ODESolution.galerkin_inner_const'`; for the BUG step only the S-step matters.)  No commutation of
`P₁` and `Q₁` is needed: `⟪c, P₁ Q₁ z⟫ = ⟪c, z⟫` follows from `P₁ c = c` and `Q₁ c = c`
(`ODESolution.galerkin_inner_const_of_inner_apply`). -/
theorem bug_inner_eq {P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    {F : ℝ → E → E} {YS : ℝ → E} {t₀ t₁ : ℝ}
    (hYS : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁) {Y₀ : E}
    (h0 : YS t₀ = P₁ (Q₁ Y₀)) {c : E} (hc₁ : P₁ c = c) (hc₂ : Q₁ c = c)
    (hF : ∀ t x, ⟪c, F t x⟫ = 0) : ∀ t ∈ Icc t₀ t₁, ⟪c, YS t⟫ = ⟪c, Y₀⟫ := by
  have hYS' : ODESolution (fun t x => P₁ ((fun t x => Q₁ (F t x)) t x)) YS t₀ t₁ := hYS
  intro t ht
  rw [hYS'.galerkin_inner_const_of_inner_apply
      (fun _ _ => hP₁.inner_apply_right_of_mem _ hc₁)
      (fun _ _ => by simp only [hQ₁.inner_apply_right_of_mem _ hc₂, hF]) t ht,
    h0, hP₁.inner_apply_right_of_mem _ hc₁, hQ₁.inner_apply_right_of_mem _ hc₂]

/-- **Conservation of linear invariants by the explicit Euler projector-splitting step**
(`kslEulerStep` of `Stability/Energy.lean`): if `P₁ c = c`, `Q₀ c = c` and `⟪c, F y⟫ = 0` for all
`y`, then the K-, S- and L-substeps all conserve `⟪c, ·⟫`, hence so does the KSL step. -/
theorem kslEulerStep_inner_eq {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    {c : E} (hc₁ : P₁ c = c) (hc₀ : Q₀ c = c) {F : E → E} (hF : ∀ y, ⟪c, F y⟫ = 0) (h : ℝ)
    (x : E) : ⟪c, kslEulerStep P₁ Q₀ F h x⟫ = ⟪c, x⟫ := by
  simp only [kslEulerStep, kslL, kslS, kslK, inner_add_right, inner_sub_right,
    real_inner_smul_right, hP₁.inner_apply_right_of_mem _ hc₁,
    hQ₀.inner_apply_right_of_mem _ hc₀, hF, mul_zero, add_zero, sub_zero]

/-- A backward Galerkin step `y' = -P F(t, y)` (the KSL S-step for `P = P₁ Q₀`) conserves
`⟪c, ·⟫` if `P c = c` and `⟪c, F(t, x)⟫ = 0`. -/
theorem backward_inner_const {P : E →L[ℝ] E} (hP : IsOrthProj P) {F : ℝ → E → E} {y : ℝ → E}
    {a b : ℝ} (hy : ODESolution (fun t x => -P (F t x)) y a b) {c : E} (hc : P c = c)
    (hF : ∀ t x, ⟪c, F t x⟫ = 0) : ∀ t ∈ Icc a b, ⟪c, y t⟫ = ⟪c, y a⟫ := by
  have hy' : ODESolution (fun t x => P (-F t x)) y a b :=
    ⟨hy.cont, fun t ht => (hy.deriv t ht).congr_deriv (map_neg P _).symm⟩
  exact hy'.galerkin_inner_const' hP hc fun t x => by rw [inner_neg_right, hF, neg_zero]

/-- **Conservation of linear invariants by the exact projector-splitting (KSL) step.**  K-step
`YK' = Q₀ F(t, YK)` from `Y₀`, backward S-step `YS' = -P₁ Q₀ F(t, YS)` from `P₁ YK(t₁)`, L-step
`YL' = P₁ F(t, YL)` from `YS(t₁)`.  If the old right basis and the new left basis contain the
conserved direction (`Q₀ c = c`, `P₁ c = c`) and `⟪c, F(t, x)⟫ = 0`, then
`⟪c, YL(t₁)⟫ = ⟪c, Y₀⟫`.  No commutation of `P₁` and `Q₀` is needed. -/
theorem ksl_inner_eq {P₁ Q₀ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    {F : ℝ → E → E} {YK YS YL : ℝ → E} {t₀ t₁ : ℝ}
    (ht : t₀ ≤ t₁) (hYK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁)
    (hYS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁)
    (hYL : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) {Y₀ : E} (hK0 : YK t₀ = Y₀)
    (hS0 : YS t₀ = P₁ (YK t₁)) (hL0 : YL t₀ = YS t₁) {c : E} (hc₁ : P₁ c = c)
    (hc₀ : Q₀ c = c) (hF : ∀ t x, ⟪c, F t x⟫ = 0) : ⟪c, YL t₁⟫ = ⟪c, Y₀⟫ := by
  have hYS' : ODESolution (fun t x => P₁ ((fun t x => -Q₀ (F t x)) t x)) YS t₀ t₁ :=
    ⟨hYS.cont, fun t ht => (hYS.deriv t ht).congr_deriv (map_neg P₁ _).symm⟩
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  rw [hYL.galerkin_inner_const' hP₁ hc₁ hF t₁ ht₁, hL0,
    hYS'.galerkin_inner_const_of_inner_apply (fun _ _ => hP₁.inner_apply_right_of_mem _ hc₁)
      (fun _ _ => by
        simp only [inner_neg_right, hQ₀.inner_apply_right_of_mem _ hc₀, hF, neg_zero]) t₁ ht₁,
    hS0, hP₁.inner_apply_right_of_mem _ hc₁, hYK.galerkin_inner_const' hQ₀ hc₀ hF t₁ ht₁, hK0]

end LinearInvariants

/-! ### Conservative truncation -/

section ConservativeTruncation

variable {C : E →L[ℝ] E}

/-- The **conservative truncation** of Einkemmer–Ostermann–Scalone (arXiv 2206.09374,
Algorithm 1, steps 5–12; a similar approach is Guo–Qiu, arXiv 2201.10397): the part `C Ŷ` of
`Ŷ` in the conserved directions (`K̃_cons Uᵀ`) is kept exactly, and only the remainder
`(1 - C) Ŷ` (`K̃_rem W̃ᵀ`) is truncated by `T` (an SVD truncation to rank `r - m`). -/
def consTrunc (C : E →L[ℝ] E) (T : E → E) (Y : E) : E := C Y + T (Y - C Y)

/-- **The conservative truncation preserves all moments**: if `T` maps the remainder into
`range (1 - C)` (`C (T z) = 0`: its velocity factor `W` is orthogonal to `U`), then
`C Y₁ = C Ŷ`. -/
theorem consTrunc_moments (hC : IsOrthProj C) {T : E → E} {Y : E}
    (hT : C (T (Y - C Y)) = 0) : C (consTrunc C T Y) = C Y := by
  rw [consTrunc, map_add, hC.idem, hT, add_zero]

/-- **The conservative truncation conserves linear invariants** `⟪c, ·⟫` with `C c = c`. -/
theorem consTrunc_inner (hC : IsOrthProj C) {T : E → E} {Y : E} (hT : C (T (Y - C Y)) = 0)
    {c : E} (hc : C c = c) : ⟪c, consTrunc C T Y⟫ = ⟪c, Y⟫ := by
  rw [← hC.inner_apply_right_of_mem _ hc, consTrunc_moments hC hT,
    hC.inner_apply_right_of_mem _ hc]

/-- The error of the conservative truncation is the truncation error of the remainder:
`Ŷ - Y₁ = (1 - C) Ŷ - T ((1 - C) Ŷ)`. -/
theorem sub_consTrunc (C : E →L[ℝ] E) (T : E → E) (Y : E) :
    Y - consTrunc C T Y = (Y - C Y) - T (Y - C Y) := by
  rw [consTrunc]; abel

/-- **Truncation error of the conservative truncation**:
`‖Ŷ - Y₁‖ = ‖(1 - C) Ŷ - T ((1 - C) Ŷ)‖` (the discarded singular values of the remainder
`K̃_rem`). -/
theorem norm_sub_consTrunc (C : E →L[ℝ] E) (T : E → E) (Y : E) :
    ‖Y - consTrunc C T Y‖ = ‖(Y - C Y) - T (Y - C Y)‖ := by
  rw [sub_consTrunc]

/-- A conservative truncation with remainder tolerance `ϑ` is a truncation with tolerance `ϑ`,
so the error analysis of the rank-adaptive BUG integrator applies verbatim. -/
theorem norm_sub_consTrunc_le {T : E → E} {Y : E} {ϑ : ℝ}
    (hT : ‖(Y - C Y) - T (Y - C Y)‖ ≤ ϑ) : ‖consTrunc C T Y - Y‖ ≤ ϑ := by
  rwa [norm_sub_rev, norm_sub_consTrunc]

/-- **Pythagoras for the conservative truncation**: `‖Y₁‖² = ‖C Ŷ‖² + ‖T ((1 - C) Ŷ)‖²`. -/
theorem norm_consTrunc_sq (hC : IsOrthProj C) {T : E → E} {Y : E}
    (hT : C (T (Y - C Y)) = 0) : ‖consTrunc C T Y‖ ^ 2 = ‖C Y‖ ^ 2 + ‖T (Y - C Y)‖ ^ 2 := by
  have h0 : ⟪C Y, T (Y - C Y)⟫ = 0 := by rw [hC.symm, hT, inner_zero_right]
  rw [consTrunc, norm_add_sq_real, h0]
  ring

/-- **The conservative truncation is norm-nonincreasing** as soon as the truncation of the
remainder is (e.g. an SVD truncation): `‖Y₁‖ ≤ ‖Ŷ‖`.  Hence it does not affect `L²`-stability. -/
theorem norm_consTrunc_le (hC : IsOrthProj C) {T : E → E} {Y : E} (hT : C (T (Y - C Y)) = 0)
    (hTn : ‖T (Y - C Y)‖ ≤ ‖Y - C Y‖) : ‖consTrunc C T Y‖ ≤ ‖Y‖ := by
  have h1 := norm_consTrunc_sq hC hT
  have h2 := hC.norm_sq_add Y
  have h3 : ‖T (Y - C Y)‖ ^ 2 ≤ ‖Y - C Y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hTn 2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- **Optimality of the conservative truncation.**  If `T z` is a best approximation of the
remainder `z = (1 - C) Ŷ` in a set `S` (e.g. matrices of rank `≤ r - m`), then `Y₁` is a best
approximation of `Ŷ` among all `Z` with the same moments, `C Z = C Ŷ`, whose remainder
`(1 - C) Z` lies in `S`. -/
theorem consTrunc_optimal {T : E → E} {Y : E} {S : Set E}
    (hT : ∀ w ∈ S, ‖(Y - C Y) - T (Y - C Y)‖ ≤ ‖(Y - C Y) - w‖) {Z : E} (hZ : C Z = C Y)
    (hZS : Z - C Z ∈ S) : ‖Y - consTrunc C T Y‖ ≤ ‖Y - Z‖ := by
  have h : Y - Z = (Y - C Y) - (Z - C Z) := by rw [hZ]; abel
  rw [norm_sub_consTrunc, h]
  exact hT _ hZS

/-- If `C R = 0` for orthogonal projectors, then also `R C = 0`. -/
lemma IsOrthProj.comp_eq_zero_of_comp_eq_zero (hC : IsOrthProj C) {R : E →L[ℝ] E}
    (hR : IsOrthProj R) (h : ∀ x, C (R x) = 0) (x : E) : R (C x) = 0 := by
  refine ext_inner_right ℝ fun y => ?_
  rw [hR.symm, hC.symm, h, inner_zero_right, inner_zero_left]

/-- The sum of two orthogonal projectors with orthogonal ranges (`C R = 0`) is an orthogonal
projector: the velocity basis `[U, W]` after a conservative truncation. -/
lemma IsOrthProj.add_of_comp_eq_zero (hC : IsOrthProj C) {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (h : ∀ x, C (R x) = 0) : IsOrthProj (C + R) where
  idem x := by
    simp only [add_apply, map_add, hC.idem, hR.idem, h,
      hC.comp_eq_zero_of_comp_eq_zero hR h]
    abel
  symm x y := by
    simp only [add_apply, inner_add_left, inner_add_right, hC.symm, hR.symm]

/-- **The new velocity basis contains the conserved directions** (arXiv 2311.06399, §5: "if
`P_V̂ U = U` then `P_{V¹} U = U`").  If the truncated remainder lies in the range of a projector
`R` orthogonal to the conserved directions (`C R = 0`, the span of the new non-conserved
velocity functions `W`), then the new basis projector `C + R` contains the conserved directions
and the truncated solution `Y₁`; this is the hypothesis `Q₀ C = C` of the next step. -/
theorem consTrunc_mem_range (hC : IsOrthProj C) {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hCR : ∀ x, C (R x) = 0) {T : E → E} {Y : E} (hT : R (T (Y - C Y)) = T (Y - C Y)) :
    (C + R) (consTrunc C T Y) = consTrunc C T Y ∧ (∀ x, (C + R) (C x) = C x) ∧
      C (T (Y - C Y)) = 0 := by
  have hRC := hC.comp_eq_zero_of_comp_eq_zero hR hCR
  have hCT : C (T (Y - C Y)) = 0 := by rw [← hT, hCR]
  refine ⟨?_, fun x => ?_, hCT⟩
  · simp only [consTrunc, add_apply, map_add, hC.idem, hRC, hCT, hT]
    abel
  · simp only [add_apply, hC.idem, hRC, add_zero]

/-- A conservative truncation by an orthogonal projection `R` of the remainder (with `C R = 0`)
is the orthogonal projection `C + R` of `Ŷ`. -/
theorem consTrunc_proj_eq (hC : IsOrthProj C) {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hCR : ∀ x, C (R x) = 0) (Y : E) : consTrunc C R Y = (C + R) Y := by
  rw [consTrunc, map_sub, hC.comp_eq_zero_of_comp_eq_zero hR hCR, sub_zero]
  rfl

end ConservativeTruncation

/-! ### Local conservation laws of conservative BUG integrators -/

section LocalConservation

variable {C : E →L[ℝ] E}

/-- **Galerkin moment identity** (arXiv 2311.06399, eq. (5)): if the right projector `Q` contains
the conserved directions (`Q C = C`) and the left projector `P` commutes with `C`, then
`C (P Q z) = P (C z)`, i.e. `⟨P_V̂ P_X̂ F, U⟩_v = P_X̂ ⟨F, U⟩_v`. -/
theorem moment_galerkin (hC : IsOrthProj C) {P Q : E →L[ℝ] E} (hQ : IsOrthProj Q)
    (hQC : ∀ x, Q (C x) = C x) (hPC : ∀ x, P (C x) = C (P x)) (z : E) :
    C (P (Q z)) = P (C z) := by
  rw [← hPC, hC.comp_eq_of_comp_eq hQ hQC]

/-- **Continuous moment law of the S-step** (arXiv 2311.06399, eq. (5)): along the Galerkin
S-step `YS' = P̂ Q̂ F(t, YS)` the moments satisfy `d/dt C YS = P̂ C F(t, YS)`, i.e.
`∂ₜ ϕ_S = P_X̂ ⟨F(Y_S), U⟩_v`: the exact law up to the spatial projection. -/
theorem galerkin_moment_hasDerivWithinAt (hC : IsOrthProj C) {P Q : E →L[ℝ] E}
    (hQ : IsOrthProj Q) (hQC : ∀ x, Q (C x) = C x) (hPC : ∀ x, P (C x) = C (P x))
    {F : ℝ → E → E} {YS : ℝ → E} {a b t : ℝ}
    (hYS : ODESolution (fun t x => P (Q (F t x))) YS a b) (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun s => C (YS s)) (P (C (F t (YS t)))) (Ici t) t := by
  have h := C.hasFDerivAt.comp_hasDerivWithinAt t (hYS.deriv t ht)
  rw [← moment_galerkin hC hQ hQC hPC]
  exact h

/-- **Exact local conservation law along the K-step** (arXiv 2311.06399, eq. (11)): if the old
velocity basis contains the conserved directions (`Q₀ C = C`), the K-step `YK' = Q₀ F(t, YK)`
satisfies `d/dt C YK = C F(t, YK)`, i.e. `∂ₜ ϕ = ⟨F(t, Y_K), U⟩_v`. -/
theorem kStep_moment_hasDerivWithinAt (hC : IsOrthProj C) {Q₀ : E →L[ℝ] E}
    (hQ₀ : IsOrthProj Q₀) (hQ₀C : ∀ x, Q₀ (C x) = C x) {F : ℝ → E → E} {YK : ℝ → E}
    {a b t : ℝ} (hYK : ODESolution (fun t x => Q₀ (F t x)) YK a b) (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun s => C (YK s)) (C (F t (YK t))) (Ici t) t := by
  have h := C.hasFDerivAt.comp_hasDerivWithinAt t (hYK.deriv t ht)
  rw [← hC.comp_eq_of_comp_eq hQ₀ hQ₀C]
  exact h

/-- **The augmented spatial basis contains the flux moments of the explicit Euler K-step**
(abstract analogue of Lemmas 1–2 of arXiv 2206.09374, by the argument of §6.1 of
arXiv 2311.06399).  If the old
velocity basis contains the conserved directions (`Q₀ C = C`), the augmented left basis `P̂`
(commuting with `C`) contains the old solution `Y₀` and the explicit Euler K-step result
`YK₁ = Y₀ + h Q₀ F(Y₀)` (`span[X⁰, K¹] ⊆ span X̂`), and `h ≠ 0`, then `P̂` fixes the flux moments:
`P̂ C F(Y₀) = C F(Y₀)`, i.e. the *combined* flux moments `⟨F(Y₀), U_k⟩_v` (for Vlasov–Poisson
`-∇ₓ·j`, `-∇ₓ·σ ± E ρ`, …) lie in `span X̂`.  This is what the discrete local laws need, and it
holds without a `∇ₓX` augmentation (arXiv 2311.06399, §4.1).  It does not show that the separate
terms (`∇ₓ·j`, `E ρ`, `E·j`) lie in `span X̂`, which is the content of EOS Lemmas 1–2 and uses the
`∇ₓX` augmentation there. -/
theorem consBug_euler_flux_mem (hC : IsOrthProj C) {Q₀ Pa : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀)
    (hQ₀C : ∀ x, Q₀ (C x) = C x) (hPC : ∀ x, Pa (C x) = C (Pa x)) {F : E → E} {h : ℝ}
    (hh : h ≠ 0) {Y₀ : E} (hY₀ : Pa Y₀ = Y₀)
    (hK : Pa (Y₀ + h • Q₀ (F Y₀)) = Y₀ + h • Q₀ (F Y₀)) : Pa (C (F Y₀)) = C (F Y₀) := by
  have hinc : Pa (Q₀ (F Y₀)) = Q₀ (F Y₀) := by
    rw [map_add, map_smul, hY₀] at hK
    exact smul_right_injective E hh (add_left_cancel hK)
  rw [← hC.comp_eq_of_comp_eq hQ₀ hQ₀C (F Y₀), hPC, hinc]

/-- **Discrete moment law of the explicit Euler augmented BUG step** (abstract form of the proofs
of Theorems 1–3 of arXiv 2206.09374 and §6.1 of arXiv 2311.06399).  Assume

* the old velocity basis `Q₀` and the augmented velocity basis `Q̂` contain the conserved
  directions (`Q₀ C = C`, `Q̂ C = C`; `U ⊆ span V⁰ ⊆ span Ṽ`),
* the augmented spatial basis `P̂` commutes with `C` and contains `Y₀` and the explicit Euler
  K-step result `Y₀ + h Q₀ F(Y₀)`.

Then the explicit Euler Galerkin S-step `Ŷ = P̂ Q̂ (Y₀ + h F(Y₀))` has exactly the moments of the
full explicit Euler step: `C Ŷ = C (Y₀ + h F(Y₀))`.  No condition on `h` is needed.  The field is
evaluated at `Y₀`; the BUG S-step evaluates it at `P̂ Q̂ Y₀`, and the two coincide when the
augmented bases contain the old ones (`P̂ Q̂ Y₀ = Y₀`, e.g. `Q̂ Y₀ = Y₀` together with `hY₀`). -/
theorem consBug_euler_moment (hC : IsOrthProj C) {Q₀ Pa Qa : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀)
    (hQa : IsOrthProj Qa) (hQ₀C : ∀ x, Q₀ (C x) = C x) (hQaC : ∀ x, Qa (C x) = C x)
    (hPC : ∀ x, Pa (C x) = C (Pa x)) {F : E → E} {h : ℝ} {Y₀ : E} (hY₀ : Pa Y₀ = Y₀)
    (hK : Pa (Y₀ + h • Q₀ (F Y₀)) = Y₀ + h • Q₀ (F Y₀)) :
    C (Pa (Qa (eulerStep F h Y₀))) = C (eulerStep F h Y₀) := by
  have hinc : h • Pa (Q₀ (F Y₀)) = h • Q₀ (F Y₀) := by
    rw [map_add, map_smul, hY₀] at hK
    exact add_left_cancel hK
  have hCQ₀ := hC.comp_eq_of_comp_eq hQ₀ hQ₀C
  rw [moment_galerkin hC hQa hQaC hPC, eulerStep, map_add, map_add, map_smul, map_smul, hPC Y₀,
    hY₀, ← hCQ₀ (F Y₀), hPC, ← map_smul, hinc, map_smul]

/-- **The conservative augmented BUG integrator satisfies the discrete local conservation laws**
(Einkemmer–Ostermann–Scalone, arXiv 2206.09374, Theorems 1–2, abstract form; arXiv 2311.06399,
§6.1).  With the hypotheses of `consBug_euler_moment` and a conservative truncation
`Y₁ = C Ŷ + T((1 - C) Ŷ)` whose truncated part has no conserved components, the new
approximation has exactly the moments of the full explicit Euler step,
`C Y₁ = C Y₀ + h C F(Y₀)`: for `U = (1, v)` this is the discrete continuity equation
`ρ¹ = ρ⁰ - h ∇ₓ·j⁰` and the discrete momentum equation.  (As in `consBug_euler_moment`, the S-step
field is evaluated at `Y₀`, which is the BUG S-step when `P̂ Q̂ Y₀ = Y₀`.) -/
theorem consBug_euler_local_law (hC : IsOrthProj C) {Q₀ Pa Qa : E →L[ℝ] E}
    (hQ₀ : IsOrthProj Q₀) (hQa : IsOrthProj Qa) (hQ₀C : ∀ x, Q₀ (C x) = C x)
    (hQaC : ∀ x, Qa (C x) = C x) (hPC : ∀ x, Pa (C x) = C (Pa x)) {F : E → E} {h : ℝ} {Y₀ : E}
    (hY₀ : Pa Y₀ = Y₀) (hK : Pa (Y₀ + h • Q₀ (F Y₀)) = Y₀ + h • Q₀ (F Y₀)) {T : E → E}
    (hT : C (T (Pa (Qa (eulerStep F h Y₀)) - C (Pa (Qa (eulerStep F h Y₀))))) = 0) :
    C (consTrunc C T (Pa (Qa (eulerStep F h Y₀)))) = C Y₀ + h • C (F Y₀) := by
  rw [consTrunc_moments hC hT, consBug_euler_moment hC hQ₀ hQa hQ₀C hQaC hPC hY₀ hK, eulerStep,
    map_add, map_smul]

/-- **Global invariants of the conservative augmented BUG step**: for every `c` in the conserved
directions (`C c = c`, e.g. `c = 1ₓ ⊗ U₁` for the total mass),
`⟪c, Y₁⟫ = ⟪c, Y₀⟫ + h ⟪c, F(Y₀)⟫`. -/
theorem consBug_euler_inner (hC : IsOrthProj C) {Q₀ Pa Qa : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀)
    (hQa : IsOrthProj Qa) (hQ₀C : ∀ x, Q₀ (C x) = C x) (hQaC : ∀ x, Qa (C x) = C x)
    (hPC : ∀ x, Pa (C x) = C (Pa x)) {F : E → E} {h : ℝ} {Y₀ : E} (hY₀ : Pa Y₀ = Y₀)
    (hK : Pa (Y₀ + h • Q₀ (F Y₀)) = Y₀ + h • Q₀ (F Y₀)) {T : E → E}
    (hT : C (T (Pa (Qa (eulerStep F h Y₀)) - C (Pa (Qa (eulerStep F h Y₀))))) = 0) {c : E}
    (hc : C c = c) :
    ⟪c, consTrunc C T (Pa (Qa (eulerStep F h Y₀)))⟫ = ⟪c, Y₀⟫ + h * ⟪c, F Y₀⟫ := by
  rw [← hC.inner_apply_right_of_mem _ hc,
    consBug_euler_local_law hC hQ₀ hQa hQ₀C hQaC hPC hY₀ hK hT, ← map_smul, ← map_add,
    hC.inner_apply_right_of_mem _ hc, inner_add_right, real_inner_smul_right]

/-- **Conservation of total mass/momentum by the conservative augmented BUG step**
(arXiv 2206.09374, Theorems 1–2, integrated in space): if moreover `⟪c, F(Y₀)⟫ = 0` (the flux is
a divergence, `∫ ∇ₓ·j dx = 0`), then `⟪c, Y₁⟫ = ⟪c, Y₀⟫`. -/
theorem consBug_euler_inner_eq (hC : IsOrthProj C) {Q₀ Pa Qa : E →L[ℝ] E}
    (hQ₀ : IsOrthProj Q₀) (hQa : IsOrthProj Qa) (hQ₀C : ∀ x, Q₀ (C x) = C x)
    (hQaC : ∀ x, Qa (C x) = C x) (hPC : ∀ x, Pa (C x) = C (Pa x)) {F : E → E} {h : ℝ} {Y₀ : E}
    (hY₀ : Pa Y₀ = Y₀) (hK : Pa (Y₀ + h • Q₀ (F Y₀)) = Y₀ + h • Q₀ (F Y₀)) {T : E → E}
    (hT : C (T (Pa (Qa (eulerStep F h Y₀)) - C (Pa (Qa (eulerStep F h Y₀))))) = 0) {c : E}
    (hc : C c = c) (hF : ⟪c, F Y₀⟫ = 0) :
    ⟪c, consTrunc C T (Pa (Qa (eulerStep F h Y₀)))⟫ = ⟪c, Y₀⟫ := by
  rw [consBug_euler_inner hC hQ₀ hQa hQ₀C hQaC hPC hY₀ hK hT hc, hF, mul_zero, add_zero]

/-- **Moment-dependent quantities agree with the full scheme** (a reduction lemma towards
arXiv 2206.09374, Theorem 3).  Every quantity `Φ` depending only on the moments (for
`U = (1, v, v² - 1)`: the density, the current, the kinetic energy and, through the Poisson
equation, the electric energy) takes the same value on the low-rank solution `Y₁` as on the full
explicit Euler step `Y₀ + h F(Y₀)`.  Consequently any identity between moment-determined
quantities of the full explicit Euler scheme, such as the discrete energy identity (26) of
arXiv 2206.09374, transfers to the low-rank step.  The identity (26) itself (and its `O(h²)`
defect) is not formalised here. -/
theorem consBug_euler_moment_functional {α : Type*} (Φ : E → α) (hC : IsOrthProj C)
    {Q₀ Pa Qa : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀) (hQa : IsOrthProj Qa)
    (hQ₀C : ∀ x, Q₀ (C x) = C x) (hQaC : ∀ x, Qa (C x) = C x) (hPC : ∀ x, Pa (C x) = C (Pa x))
    {F : E → E} {h : ℝ} {Y₀ : E} (hY₀ : Pa Y₀ = Y₀)
    (hK : Pa (Y₀ + h • Q₀ (F Y₀)) = Y₀ + h • Q₀ (F Y₀)) {T : E → E}
    (hT : C (T (Pa (Qa (eulerStep F h Y₀)) - C (Pa (Qa (eulerStep F h Y₀))))) = 0) :
    Φ (C (consTrunc C T (Pa (Qa (eulerStep F h Y₀))))) = Φ (C (eulerStep F h Y₀)) := by
  rw [consTrunc_moments hC hT, consBug_euler_moment hC hQ₀ hQa hQ₀C hQaC hPC hY₀ hK]

/-- **The conservative augmented BUG step is `L²`-stable under the CFL condition of the full
scheme**: if the full explicit Euler step is norm-nonincreasing at `Y₀` and the truncation of the
remainder is norm-nonincreasing, then `‖Y₁‖ ≤ ‖Y₀‖` (combining arXiv 2206.09374 with
arXiv 2107.07282, Theorem 4). -/
theorem consBug_euler_norm_le (hC : IsOrthProj C) {Pa Qa : E →L[ℝ] E} (hPa : IsOrthProj Pa)
    (hQa : IsOrthProj Qa) {F : E → E} {h : ℝ} {Y₀ : E} (hF : ‖eulerStep F h Y₀‖ ≤ ‖Y₀‖)
    {T : E → E}
    (hT : C (T (Pa (Qa (eulerStep F h Y₀)) - C (Pa (Qa (eulerStep F h Y₀))))) = 0)
    (hTn : ‖T (Pa (Qa (eulerStep F h Y₀)) - C (Pa (Qa (eulerStep F h Y₀))))‖ ≤
      ‖Pa (Qa (eulerStep F h Y₀)) - C (Pa (Qa (eulerStep F h Y₀)))‖) :
    ‖consTrunc C T (Pa (Qa (eulerStep F h Y₀)))‖ ≤ ‖Y₀‖ :=
  (norm_consTrunc_le hC hT hTn).trans
    ((hPa.norm_le _).trans ((hQa.norm_le _).trans hF))

/-- **Discrete moment law of a Runge–Kutta S-step** (arXiv 2311.06399, eq. (8)).  Let the
velocity basis `Q̂` contain the conserved directions, let the spatial basis `P̄` commute with `C`
and contain `Y₀` (augmented bases contain the old ones; with `Q̂ Y₀ = Y₀` the S-step then starts at
`P̄ Q̂ Y₀ = Y₀`).  For the explicit Runge–Kutta S-step
`Ŷ = P̄ Q̂ (Y₀ + h ∑ᵢ bᵢ Gᵢ)` with stage values `Gᵢ = F(Y⁽ⁱ⁾)`:
`C Ŷ = C Y₀ + h P̄ (∑ᵢ bᵢ C Gᵢ)`, i.e. `ϕ¹ = ϕ⁰ + h P_X̄ ∑ᵢ bᵢ ⟨F⁽ⁱ⁾, U⟩_v`. -/
theorem consBug_rk_moment (hC : IsOrthProj C) {Pe Qa : E →L[ℝ] E} (hQa : IsOrthProj Qa)
    (hQaC : ∀ x, Qa (C x) = C x) (hPC : ∀ x, Pe (C x) = C (Pe x)) {Y₀ : E} (hY₀ : Pe Y₀ = Y₀)
    {s : ℕ} (b : Fin s → ℝ) (G : Fin s → E) (h : ℝ) :
    C (Pe (Qa (Y₀ + h • ∑ i, b i • G i))) = C Y₀ + h • Pe (∑ i, b i • C (G i)) := by
  rw [moment_galerkin hC hQa hQaC hPC, map_add, map_add, hPC Y₀, hY₀, map_smul, map_smul,
    map_sum]
  simp only [map_smul]

/-- **Local conservation of the Runge–Kutta BUG integrator with flux augmentation**
(arXiv 2311.06399, §5, eq. (7)): if the spatial basis contains the Runge–Kutta flux moment
`∑ᵢ bᵢ ⟨F⁽ⁱ⁾, U⟩_v` (as it does for `X̄ = ortho[X̂, ∑ᵢ bᵢ ⟨F⁽ⁱ⁾, U⟩_v]`), the moments satisfy the
discrete local conservation law `C Ŷ = C Y₀ + h ∑ᵢ bᵢ C Gᵢ` of the Runge–Kutta method. -/
theorem consBug_rk_local_law (hC : IsOrthProj C) {Pe Qa : E →L[ℝ] E} (hQa : IsOrthProj Qa)
    (hQaC : ∀ x, Qa (C x) = C x) (hPC : ∀ x, Pe (C x) = C (Pe x)) {Y₀ : E} (hY₀ : Pe Y₀ = Y₀)
    {s : ℕ} (b : Fin s → ℝ) (G : Fin s → E) (h : ℝ)
    (hflux : Pe (∑ i, b i • C (G i)) = ∑ i, b i • C (G i)) :
    C (Pe (Qa (Y₀ + h • ∑ i, b i • G i))) = C Y₀ + h • ∑ i, b i • C (G i) := by
  rw [consBug_rk_moment hC hQa hQaC hPC hY₀, hflux]

/-- **The flux condition is also necessary** (cf. arXiv 2311.06399, §6, where
`P_X̂ ∑ᵢ bᵢ ⟨F⁽ⁱ⁾, U⟩_v = ∑ᵢ bᵢ ⟨F⁽ⁱ⁾, U⟩_v` is identified as the key ingredient): for `h ≠ 0`, the
Runge–Kutta S-step satisfies the discrete local conservation law iff the spatial basis contains
the flux moment. -/
theorem consBug_rk_local_law_iff (hC : IsOrthProj C) {Pe Qa : E →L[ℝ] E} (hQa : IsOrthProj Qa)
    (hQaC : ∀ x, Qa (C x) = C x) (hPC : ∀ x, Pe (C x) = C (Pe x)) {Y₀ : E} (hY₀ : Pe Y₀ = Y₀)
    {s : ℕ} (b : Fin s → ℝ) (G : Fin s → E) {h : ℝ} (hh : h ≠ 0) :
    C (Pe (Qa (Y₀ + h • ∑ i, b i • G i))) = C Y₀ + h • ∑ i, b i • C (G i) ↔
      Pe (∑ i, b i • C (G i)) = ∑ i, b i • C (G i) := by
  rw [consBug_rk_moment hC hQa hQaC hPC hY₀]
  constructor
  · intro H
    exact smul_right_injective E hh (add_left_cancel H)
  · intro H
    rw [H]

/-- **Global conservation for the Runge–Kutta BUG integrator with flux augmentation and
conservative truncation**: for `C c = c` and `⟪c, Gᵢ⟫ = 0` (`⟨F⁽ⁱ⁾, U⟩_{x,v} = 0`),
`⟪c, Y₁⟫ = ⟪c, Y₀⟫`. -/
theorem consBug_rk_inner_eq (hC : IsOrthProj C) {Pe Qa : E →L[ℝ] E} (hQa : IsOrthProj Qa)
    (hQaC : ∀ x, Qa (C x) = C x) (hPC : ∀ x, Pe (C x) = C (Pe x)) {Y₀ : E} (hY₀ : Pe Y₀ = Y₀)
    {s : ℕ} (b : Fin s → ℝ) {G : Fin s → E} (h : ℝ)
    (hflux : Pe (∑ i, b i • C (G i)) = ∑ i, b i • C (G i)) {T : E → E}
    (hT : C (T (Pe (Qa (Y₀ + h • ∑ i, b i • G i)) - C (Pe (Qa (Y₀ + h • ∑ i, b i • G i))))) = 0)
    {c : E} (hc : C c = c) (hG : ∀ i, ⟪c, G i⟫ = 0) :
    ⟪c, consTrunc C T (Pe (Qa (Y₀ + h • ∑ i, b i • G i)))⟫ = ⟪c, Y₀⟫ := by
  rw [consTrunc_inner hC hT hc, ← hC.inner_apply_right_of_mem _ hc,
    consBug_rk_local_law hC hQa hQaC hPC hY₀ b G h hflux, inner_add_right,
    hC.inner_apply_right_of_mem _ hc, real_inner_smul_right, inner_sum]
  simp only [real_inner_smul_right, hC.inner_apply_right_of_mem _ hc, hG, mul_zero,
    Finset.sum_const_zero, add_zero]

/-- **Extra augmentation does not hurt the error analysis**: if the enlarged spatial basis
contains the old one (`P̄ P̂ = P̂`, as for `X̄ = [X̂, X̄⋆]`), its projection error is not larger:
`‖x - P̄ x‖ ≤ ‖x - P̂ x‖` (and likewise for the normal components entering the robust error
bounds, by applying it to `(1 - Q) x`). -/
theorem norm_sub_apply_le_of_le {Pa Pe : E →L[ℝ] E} (hPe : IsOrthProj Pe)
    (hle : ∀ x, Pe (Pa x) = Pa x) (x : E) : ‖x - Pe x‖ ≤ ‖x - Pa x‖ :=
  hPe.norm_sub_le_of_mem_range x (Pa x) (hle x)

/-- **Moments of the conservative parallel BUG integrator** (arXiv 2311.06399, §7).  The S-block
is replaced by the K-step result: `Ŷ₁ = P̂ YK(t₁) + Z`, where the augmented spatial basis
contains `YK(t₁)` (`X̂¹ = [X̂⁰, X̃²]` captures `K(t₁)`) and the remaining block `Z` has velocity
factor `Ṽ₂ ⊥ U` (`C Z = 0`).  Then `C Ŷ₁ = C YK(t₁)`: the moments follow the K-step, whose
moments satisfy the exact local law `kStep_moment_hasDerivWithinAt`. -/
theorem consParallelBug_moment {Pa : E →L[ℝ] E} {YK₁ Z : E} (hYK : Pa YK₁ = YK₁)
    (hZ : C Z = 0) : C (Pa YK₁ + Z) = C YK₁ := by
  rw [map_add, hYK, hZ, add_zero]

/-- **Global conservation by the conservative parallel BUG integrator** (arXiv 2311.06399, §7):
if `YK` solves the K-step `YK' = Q₀ F(t, YK)` on `[t₀, t₁]` (in the algorithm `YK(t₀) = Y₀`), `Q₀`
contains the conserved directions, `C c = c` and `⟪c, F(t, x)⟫ = 0`, then `Ŷ₁ = P̂ YK(t₁) + Z`
(with `P̂ YK(t₁) = YK(t₁)`, `C Z = 0`) satisfies `⟪c, Ŷ₁⟫ = ⟪c, YK(t₀)⟫`. -/
theorem consParallelBug_inner_eq (hC : IsOrthProj C) {Q₀ Pa : E →L[ℝ] E} (hQ₀ : IsOrthProj Q₀)
    (hQ₀C : ∀ x, Q₀ (C x) = C x) {F : ℝ → E → E} {YK : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hYK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) {Z : E} (hYK₁ : Pa (YK t₁) = YK t₁)
    (hZ : C Z = 0) {c : E} (hc : C c = c) (hF : ∀ t x, ⟪c, F t x⟫ = 0) :
    ⟪c, Pa (YK t₁) + Z⟫ = ⟪c, YK t₀⟫ := by
  have hQc : Q₀ c = c := by rw [← hc, hQ₀C]
  rw [← hC.inner_apply_right_of_mem _ hc, consParallelBug_moment hYK₁ hZ,
    hC.inner_apply_right_of_mem _ hc]
  exact hYK.galerkin_inner_const' hQ₀ hQc hF t₁ ⟨ht, le_rfl⟩

/-- Conservation over many steps: if every step conserves `⟪c, ·⟫`, so does the whole scheme. -/
theorem inner_eq_of_forall_step {Y : ℕ → E} {c : E} (h : ∀ n, ⟪c, Y (n + 1)⟫ = ⟪c, Y n⟫)
    (n : ℕ) : ⟪c, Y n⟫ = ⟪c, Y 0⟫ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [h n, ih]

end LocalConservation

/-! ### Positivity-preserving corrections by metric projection -/

section Positivity

/-- **Metric projections onto convex sets do not increase distances to points of the set**
(the standard Kolmogorov criterion / obtuse-angle inequality for projections onto convex sets;
motivated by the positivity- and moment-preserving corrections (3.3), (4.4) of
Kormann–Nazarov–Wen, arXiv 2606.31662).  If `u` satisfies the variational inequality
`⟪x - u, w - u⟫ ≤ 0` for all `w ∈ K` (for convex `K` and `u ∈ K` this characterises the metric
projection of `x` onto `K`, cf. `norm_eq_iInf_iff_real_inner_le_zero`), then for every `a ∈ K`:
`‖u - a‖² + ‖x - u‖² ≤ ‖x - a‖²`.

Scope.  The comparison state must lie in `K` (for `a ∉ K` the conclusion fails: `x = -1`,
`K = [0, ∞)`, `u = 0`, `a = -1`).  In arXiv 2606.31662, `K` is the set of admissible states
*within the current bases* (`{(K̃ + δK) Vᵀ ⪰ 0}` for (3.3), resp. `{X (S̃ + δS) Vᵀ ⪰ 0}` with fixed
mass and momentum for (4.4)), so the analytical solution `F_a` of the error split (3.2) is covered
only if these bases can represent it; this theorem does not replace (3.2) in general.  Moreover
the paper minimises `‖δK‖_F` (resp. `‖δS‖_F`); this is the Frobenius metric projection of the
full state only when `Vᵀ V = I` (and `Xᵀ X = I`), which is the identification assumed here. -/
theorem norm_sub_sq_add_le_of_metricProj {K : Set E} {x u : E}
    (hvi : ∀ w ∈ K, ⟪x - u, w - u⟫ ≤ 0) {a : E} (ha : a ∈ K) :
    ‖u - a‖ ^ 2 + ‖x - u‖ ^ 2 ≤ ‖x - a‖ ^ 2 := by
  have h1 : x - a = (x - u) + (u - a) := by abel
  have h2 : ⟪x - u, u - a⟫ = -⟪x - u, a - u⟫ := by
    rw [← inner_neg_right, neg_sub]
  have h3 := hvi a ha
  rw [h1, norm_add_sq_real, h2]
  nlinarith

/-- Consequences of `norm_sub_sq_add_le_of_metricProj`: the corrected state `u` is at least as
close to every `a ∈ K` as the uncorrected state `x`, and the correction `‖x - u‖` is minimal
among all moves into `K`.  The hypothesis `a ∈ K` is essential (see the docstring there). -/
theorem norm_sub_le_of_metricProj {K : Set E} {x u : E} (hvi : ∀ w ∈ K, ⟪x - u, w - u⟫ ≤ 0)
    {a : E} (ha : a ∈ K) : ‖u - a‖ ≤ ‖x - a‖ ∧ ‖x - u‖ ≤ ‖x - a‖ := by
  have h := norm_sub_sq_add_le_of_metricProj hvi ha
  constructor
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖x - u‖])
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖u - a‖])

/-- **Existence of the metric projection** onto a nonempty, complete and convex set `K` (e.g. the
non-negative states with prescribed mass and momentum within fixed low-rank bases, the feasible set
of the corrections (3.3), (4.4) of arXiv 2606.31662, when it is nonempty). -/
theorem exists_metricProj {K : Set E} (hne : K.Nonempty) (hcomp : IsComplete K)
    (hconv : Convex ℝ K) (x : E) : ∃ u ∈ K, ∀ w ∈ K, ⟪x - u, w - u⟫ ≤ 0 := by
  obtain ⟨u, hu, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcomp hconv x
  exact ⟨u, hu, (norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hmin⟩

end Positivity

/-! ### Consistency examples -/

section Examples

/-- An orthonormal pair exists (in `ℝ²`), so the examples below are not vacuous. -/
theorem exists_orthonormal_pair :
    ∃ e₁ e₂ : EuclideanSpace ℝ (Fin 2), ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ ⟪e₁, e₂⟫ = 0 := by
  refine ⟨EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, by simp, by simp, ?_⟩
  simp [EuclideanSpace.inner_single_left]

variable {e₁ e₂ : E}

/-- A non-trivial conservative truncation: for orthonormal `e₁` (conserved direction) and `e₂`,
truncating the remainder of `Ŷ = e₁ + e₂` completely (`T = 0`) keeps the moment `C Ŷ = e₁` and
the invariant `⟪e₁, ·⟫ = 1`, with truncation error `1`. -/
example (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    rankOneProj e₁ (consTrunc (rankOneProj e₁) (fun _ => 0) (e₁ + e₂)) =
        rankOneProj e₁ (e₁ + e₂) ∧
      ⟪e₁, consTrunc (rankOneProj e₁) (fun _ => 0) (e₁ + e₂)⟫ = 1 ∧
      ‖(e₁ + e₂) - consTrunc (rankOneProj e₁) (fun _ => 0) (e₁ + e₂)‖ = 1 := by
  have hC := isOrthProj_rankOneProj h₁
  have hT : rankOneProj e₁ ((fun _ => (0 : E)) ((e₁ + e₂) - rankOneProj e₁ (e₁ + e₂))) = 0 :=
    map_zero _
  have hee : ⟪e₁, e₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have hCY : rankOneProj e₁ (e₁ + e₂) = e₁ := by
    rw [rankOneProj_apply, inner_add_right, hee, h₁₂, add_zero, one_smul]
  have hCe : rankOneProj e₁ e₁ = e₁ := by rw [rankOneProj_apply, hee, one_smul]
  refine ⟨consTrunc_moments hC hT, ?_, ?_⟩
  · rw [consTrunc_inner (T := fun _ => 0) (Y := e₁ + e₂) hC hT hCe, inner_add_right, hee, h₁₂,
      add_zero]
  · rw [norm_sub_consTrunc, hCY, add_sub_cancel_left, sub_zero, h₂]

/-- Composition of rank-one projectors: `⟪e, ⟪f, x⟫ f⟫ e = (⟪e, f⟫ ⟪f, x⟫) e`. -/
lemma rankOneProj_rankOneProj (e f x : E) :
    rankOneProj e (rankOneProj f x) = (⟪e, f⟫ * ⟪f, x⟫) • e := by
  simp only [rankOneProj_apply, real_inner_smul_right, mul_comm]

/-- The projector onto the span of two orthonormal vectors. -/
lemma isOrthProj_rankOneProj_add {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    IsOrthProj (rankOneProj e + rankOneProj f) :=
  (isOrthProj_rankOneProj he).add_of_comp_eq_zero (isOrthProj_rankOneProj hf) fun x => by
    rw [rankOneProj_rankOneProj, hef, zero_mul, zero_smul]

variable {v : Fin 2 × Fin 2 → E}

/-- An orthonormal family indexed by `Fin 2 × Fin 2` exists, so the tensor-product examples below
are not vacuous. -/
theorem exists_orthonormal_grid :
    ∃ w : Fin 2 × Fin 2 → EuclideanSpace ℝ (Fin 2 × Fin 2), Orthonormal ℝ w :=
  ⟨_, (EuclideanSpace.basisFun (Fin 2 × Fin 2) ℝ).orthonormal⟩

/-- Values of rank-one projectors on an orthonormal family. -/
lemma rankOneProj_orthonormal (hv : Orthonormal ℝ v) (k l : Fin 2 × Fin 2) :
    rankOneProj (v k) (v l) = if k = l then v k else 0 := by
  rw [rankOneProj_apply, orthonormal_iff_ite.1 hv]
  split_ifs <;> simp

/-- **The conservative augmented BUG step in a tensor-product configuration.**  Take
`E ≅ ℝ² ⊗ ℝ²` with orthonormal basis `v (i, j) = eᵢ ⊗ eⱼ` (`i` spatial, `j` velocity), the
conserved velocity direction `U = e₀`, so that `C` is the *right* projector `Y ↦ Y U Uᵀ`, the
augmented *left* projector `P̂` onto `X̂ = span{e₀}` (which commutes with `C`), the augmented
velocity basis `Q̂ = 1` (rank `2`), the rank-one initial value `Y₀ = e₀ ⊗ U` (`X⁰ = e₀`,
`V⁰ = U`, so `Q₀ = C`) and the field `F(Y) = ⟪e₀ ⊗ U, Y⟫ (e₀ ⊗ e₁ - e₀ ⊗ U)`.  Then all hypotheses
of `consBug_euler_local_law` hold, `P̂ Q̂ Y₀ = Y₀` (so the S-step is the BUG S-step), the remainder
`(1 - C) Ŷ = h e₀ ⊗ e₁` is nonzero, its rank-`(r - m) = 0` truncation `T = 0` removes it with error
`|h|`, and the result `Y₁ = (1 - h) Y₀` has exactly the moments `C Y₀ + h C F(Y₀)` of the full
explicit Euler step. -/
example (hv : Orthonormal ℝ v) {h : ℝ} (hh : h ≠ 0) :
    let C := rankOneProj (v (0, 0)) + rankOneProj (v (1, 0))
    let Pa := rankOneProj (v (0, 0)) + rankOneProj (v (0, 1))
    let Qa : E →L[ℝ] E := 1
    let F : E → E := fun x => ⟪v (0, 0), x⟫ • (v (0, 1) - v (0, 0))
    let Y₀ := v (0, 0)
    let Yh := Pa (Qa (eulerStep F h Y₀))
    IsOrthProj C ∧ IsOrthProj Pa ∧ IsOrthProj Qa ∧ (∀ x, Qa (C x) = C x) ∧
      (∀ x, Pa (C x) = C (Pa x)) ∧ Pa (Qa Y₀) = Y₀ ∧ C Y₀ = Y₀ ∧
      Pa (Y₀ + h • C (F Y₀)) = Y₀ + h • C (F Y₀) ∧
      Yh - C Yh = h • v (0, 1) ∧ h • v (0, 1) ≠ 0 ∧
      C (consTrunc C (fun _ => 0) Yh) = C Y₀ + h • C (F Y₀) ∧
      consTrunc C (fun _ => 0) Yh = (1 - h) • Y₀ ∧
      ‖Yh - consTrunc C (fun _ => 0) Yh‖ = |h| := by
  intro C Pa Qa F Y₀ Yh
  have hvv := orthonormal_iff_ite.1 hv
  have hn : ∀ k, ‖v k‖ = 1 := hv.1
  have hp := rankOneProj_orthonormal hv
  have hC : IsOrthProj C :=
    isOrthProj_rankOneProj_add (hn _) (hn _) (by rw [hvv]; simp)
  have hPa : IsOrthProj Pa :=
    isOrthProj_rankOneProj_add (hn _) (hn _) (by rw [hvv]; simp)
  have hY : eulerStep F h Y₀ = (1 - h) • v (0, 0) + h • v (0, 1) := by
    simp only [eulerStep, F, Y₀, hvv, ite_true, one_smul]
    module
  have hYh : Yh = (1 - h) • v (0, 0) + h • v (0, 1) := by
    simp only [Yh, Qa, one_apply_eq_self, hY, Pa, add_apply, map_add, map_smul, hp]
    simp
  have hCY : C Yh = (1 - h) • v (0, 0) := by
    simp only [hYh, C, add_apply, map_add, map_smul, hp]
    simp
  have hCY₀ : C Y₀ = Y₀ := by
    simp only [Y₀, C, add_apply, hp]
    simp
  have hFY₀ : C (F Y₀) = -v (0, 0) := by
    simp only [F, Y₀, hvv, ite_true, one_smul, C, add_apply, map_sub, hp]
    simp
  have hPaY₀ : Pa Y₀ = Y₀ := by
    simp only [Y₀, Pa, add_apply, hp]
    simp
  have hPC : ∀ x, Pa (C x) = C (Pa x) := fun x => by
    simp only [C, Pa, add_apply, map_add, rankOneProj_rankOneProj, hvv]
    simp
  have hK : Pa (Y₀ + h • C (F Y₀)) = Y₀ + h • C (F Y₀) := by
    rw [hFY₀, map_add, hPaY₀, map_smul, map_neg, hPaY₀]
  have hrem : Yh - C Yh = h • v (0, 1) := by rw [hCY, hYh]; abel
  have hT : C ((fun _ => (0 : E)) (Yh - C Yh)) = 0 := map_zero _
  have hY1 : consTrunc C (fun _ => 0) Yh = (1 - h) • Y₀ := by
    rw [consTrunc, hCY, add_zero]
  refine ⟨hC, hPa, IsOrthProj.one, fun _ => rfl, hPC, hPaY₀, hCY₀, hK, hrem,
    smul_ne_zero hh (hv.ne_zero _), ?_, hY1, ?_⟩
  · rw [consBug_euler_local_law hC hC IsOrthProj.one hC.idem (fun _ => rfl) hPC hPaY₀ hK hT,
      hCY₀]
  · rw [norm_sub_consTrunc, hrem]
    simp [norm_smul, hn]

/-- **Without the flux augmentation the local conservation law fails** (the reason for the extra
augmentation of arXiv 2311.06399, §5), in the tensor-product configuration of the previous example:
right projector `C` onto `U = e₀`, velocity basis `Q̂ = 1`, left projector `P̄` onto `span{e₀}`,
`Y₀ = e₀ ⊗ U` (so `P̄ Q̂ Y₀ = Y₀` is a valid S-step start) and a single explicit Euler stage with
flux `G = e₁ ⊗ U` (mass flowing into the spatial cell `e₁`).  The S-step violates the discrete
local law for every `h ≠ 0`, because `P̄` does not contain the flux moment `C G = e₁ ⊗ U`
(`consBug_rk_local_law_iff`). -/
example (hv : Orthonormal ℝ v) {h : ℝ} (hh : h ≠ 0) :
    let C := rankOneProj (v (0, 0)) + rankOneProj (v (1, 0))
    let Pe := rankOneProj (v (0, 0)) + rankOneProj (v (0, 1))
    let Qa : E →L[ℝ] E := 1
    Pe (Qa (v (0, 0))) = v (0, 0) ∧
      C (Pe (Qa (v (0, 0) + h • ∑ i : Fin 1, (1 : ℝ) • ![v (1, 0)] i))) ≠
        C (v (0, 0)) + h • ∑ i : Fin 1, (1 : ℝ) • C (![v (1, 0)] i) := by
  intro C Pe Qa
  have hvv := orthonormal_iff_ite.1 hv
  have hn : ∀ k, ‖v k‖ = 1 := hv.1
  have hp := rankOneProj_orthonormal hv
  have hC : IsOrthProj C :=
    isOrthProj_rankOneProj_add (hn _) (hn _) (by rw [hvv]; simp)
  have hPC : ∀ x, Pe (C x) = C (Pe x) := fun x => by
    simp only [C, Pe, add_apply, map_add, rankOneProj_rankOneProj, hvv]
    simp
  have hY₀ : Pe (v (0, 0)) = v (0, 0) := by
    simp only [Pe, add_apply, hp]
    simp
  refine ⟨hY₀, ?_⟩
  rw [Ne, consBug_rk_local_law_iff hC IsOrthProj.one (fun _ => rfl) hPC hY₀ _ _ hh]
  intro H
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, one_smul, C, Pe, add_apply, hp] at H
  simp only [ite_true, map_add, hp] at H
  simp at H
  exact hv.ne_zero _ H.symm

/-- The hypothesis `a ∈ K` of `norm_sub_le_of_metricProj` cannot be dropped: for `x = -1`,
`K = [0, ∞)` and its metric projection `u = 0`, the point `a = -1 ∉ K` is closer to `x` than
to `u`. -/
example : -1 ∉ Ici (0 : ℝ) ∧ ¬ ‖(0 : ℝ) - (-1)‖ ≤ ‖(-1 : ℝ) - (-1)‖ := by
  norm_num

/-- The variational inequality of `norm_sub_le_of_metricProj` is satisfiable: the metric
projection of `x = -1` onto the non-negative reals `K = [0, ∞)` is `u = 0`. -/
example : ∀ w ∈ Ici (0 : ℝ), ⟪(-1 : ℝ) - 0, w - 0⟫ ≤ 0 := by
  intro w hw
  simp only [sub_zero, RCLike.inner_apply, conj_trivial]
  nlinarith [mem_Ici.1 hw]

end Examples

end LeanDLRA
