import LeanDLRA.Foundations.ODE
import LeanDLRA.Analysis.Defs

/-!
# Galerkin ODEs `y' = P F(t, y)`

Every substep of a robust dynamical low-rank integrator that is *not* a basis update is a
**Galerkin ODE** on a fixed linear space: the S-step of the basis-update & Galerkin (BUG)
integrator (Ceruti–Lubich, arXiv 2010.02022), the S-step of the augmented / rank-adaptive BUG
integrator (Ceruti–Kusch–Lubich, arXiv 2104.05247, eq. (5)), the conservative schemes with
augmented bases (Einkemmer–Ostermann–Scalone, arXiv 2206.09374, there discretized by explicit
Euler, see `inner_proj_euler_eq`) and the coefficient flow of dynamical low-rank training.  In
all of them the full-space trajectory `Ŷ(t) = Û S(t) V̂ᵀ` solves

    Ŷ' = P F(t, Ŷ),     P Z = Û Ûᵀ Z V̂ V̂ᵀ,

with `P` an orthogonal projector (a product of commuting left and right projectors).  We work
with an arbitrary orthogonal projector `P` on a real inner product space `E`.

## Main results

* `normal_const_of_deriv_mem_range`, `range_invariant_of_deriv_mem_range`,
  `ODESolution.galerkin_mem_range`: if `y' ∈ range P` then `(1 - P) y` is constant; in
  particular a Galerkin trajectory starting in `range P` stays there.
* `ODESolution.galerkin_inner_eq_zero` (**Galerkin condition**), `ODESolution.galerkin_defect_le`
  (**Dirac–Frenkel / minimal defect**), `IsOrthProj.eq_apply_of_galerkin` (the Galerkin condition
  determines the velocity uniquely).
* `ODESolution.galerkin_norm_eq` / `ODESolution.galerkin_norm_le`: **norm conservation** if
  `⟪F(t, x), x⟫ = 0` and **norm dissipation** if `⟪F(t, x), x⟫ ≤ 0`
  (arXiv 2104.05247, Thm 4, the identity `d/dt ‖Ŝ‖² / 2 = ⟪Ŷ, F(Ŷ)⟫ = 0`).
* `ODESolution.hasDerivWithinAt_energy_gradFlow`, `ODESolution.energy_le_sub_gradFlow`,
  `ODESolution.energy_le_gradFlow`: **energy decay** for projected gradient flows
  `y' = -P ∇ℰ(y)`, with the dissipation identity `d/dt ℰ(y) = -‖P ∇ℰ(y)‖²`
  (arXiv 2104.05247, Thm 5, without the truncation term).
* `ODESolution.galerkin_energy_eq`, `ODESolution.galerkin_energy_eq_of_skew`: **energy
  conservation**; for `F = J ∇ℰ` with `J` skew and commuting with `P` (the Schrödinger case
  `J = -i`, arXiv 2104.05247, Thms 6–7, without the truncation term).
* `ODESolution.galerkin_inner_const`: the standard Galerkin **conservation of linear invariants**
  `⟪c, y⟫` when `⟪c, F⟫ = 0` and the conserved direction lies in the trial space, `P c = c`.
  `ODESolution.hasDerivWithinAt_inner_galerkin` and
  `ODESolution.galerkin_inner_const_of_inner_apply` give the variant in which only the moment is
  reproduced, `⟪c, P F⟫ = ⟪c, F⟫`, which is how conservative DLRA (Einkemmer–Joseph 2021;
  Einkemmer–Ostermann–Scalone, arXiv 2206.09374) enforces conservation.
* `inner_proj_euler_eq`, `inner_projEuler_eq`, `inner_projEuler_eq_of_mem`,
  `inner_projEulerIter_eq_of_mem`: the **discrete balance law** `⟪c, x₁⟫ = ⟪c, x₀⟫ + h ⟪c, F⟫`
  of an explicit-Euler Galerkin step `x₁ = P (x₀ + h F(t, x₀))` when the projection is exact on
  the moments of `x₀` and of `F(t, x₀)`.  This is the abstract form of the local continuity
  equation of arXiv 2206.09374, Thm 1 (see the docstrings for what is and is not covered).
* `ODESolution.truncated_galerkin_norm_sub_le`, `ODESolution.truncated_energy_le_gradFlow`,
  `ODESolution.truncated_energy_sub_le_of_skew`,
  `ODESolution.truncated_quadratic_energy_sub_le_of_skew`: the same properties for a Galerkin
  step followed by a truncation `‖Y₁ - Ŷ₁‖ ≤ ϑ`, up to `O(ϑ)` (arXiv 2104.05247, Thms 4–7,
  abstract form, comparing with `Ŷ₀ = y a`).  The identification `Ŷ₀ = Y₀` (Lemma 1 of that
  paper) is not proved in this file; it is `IsRankAdaptiveBUGStep.start_eq` in
  `Integrators/RankAdaptiveBUG.lean`, which derives the paper-form theorems from these.  The last
  one recovers the published constant of Thm 6.
* `galerkin_euler_norm_le`, `projEuler_norm_le`, `projEulerIter_norm_le`: **stability of
  explicit-Euler Galerkin steps**: if the full explicit Euler step is norm-nonincreasing then so
  is the Galerkin step.  This is the abstract mechanism of Kusch–Einkemmer–Ceruti,
  arXiv 2107.07282, Thm 4 (unconventional/BUG integrator), and of Thm 3 substep by substep.  It
  does not cover Thm 2 (projector splitting), whose S-step is amplifying.  `L²`-stability of the
  full explicit step (the CFL condition and Fourier analysis) is an assumption, not a result of
  this file.

## Conventions

Solutions are `ODESolution (fun t x => P (F t x)) y a b` (continuity on `[a, b]`, right
derivatives on `[a, b)`).  Hypotheses on the vector field are only required *along the
trajectory* in the main theorems; corollaries state the familiar global versions.  The SVD
truncation itself is not modelled; it enters only through the abstract bound `‖Y₁ - Ŷ₁‖ ≤ ϑ`.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Algebraic Galerkin facts -/

namespace IsOrthProj

variable {P : E →L[ℝ] E}

/-- For `w ∈ range P`, `⟪P v, w⟫ = ⟪v, w⟫`. -/
lemma inner_apply_left_of_mem (hP : IsOrthProj P) (v : E) {w : E} (hw : P w = w) :
    ⟪P v, w⟫ = ⟪v, w⟫ := by
  rw [hP.symm, hw]

/-- For `w ∈ range P`, `⟪w, P v⟫ = ⟪w, v⟫`. -/
lemma inner_apply_right_of_mem (hP : IsOrthProj P) (v : E) {w : E} (hw : P w = w) :
    ⟪w, P v⟫ = ⟪w, v⟫ := by
  rw [← hP.symm, hw]

/-- **Galerkin orthogonality**: the defect `P v - v` is orthogonal to `range P`. -/
lemma inner_apply_sub_self_of_mem (hP : IsOrthProj P) (v : E) {w : E} (hw : P w = w) :
    ⟪P v - v, w⟫ = 0 := by
  rw [inner_sub_left, hP.inner_apply_left_of_mem v hw, sub_self]

/-- **Uniqueness of the Galerkin solution**: if `v ∈ range P` satisfies the Galerkin condition
`⟪v - f, w⟫ = 0` for all `w ∈ range P`, then `v = P f`. -/
lemma eq_apply_of_galerkin (hP : IsOrthProj P) {v f : E} (hv : P v = v)
    (h : ∀ w, P w = w → ⟪v - f, w⟫ = 0) : v = P f := by
  have hw : P (v - P f) = v - P f := by rw [map_sub, hv, hP.idem]
  have h1 := h _ hw
  have h2 := hP.inner_apply_sub_self_of_mem f hw
  have e : v - P f = (v - f) - (P f - f) := by abel
  have h3 : ⟪v - P f, v - P f⟫ = 0 := by
    calc ⟪v - P f, v - P f⟫ = ⟪(v - f) - (P f - f), v - P f⟫ := by rw [← e]
      _ = 0 := by rw [inner_sub_left, h1, h2, sub_zero]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

/-- **Minimal defect** (Dirac–Frenkel): `P f` is the element of `range P` closest to `f`. -/
lemma norm_apply_sub_le (hP : IsOrthProj P) (f : E) {w : E} (hw : P w = w) :
    ‖P f - f‖ ≤ ‖w - f‖ := by
  rw [norm_sub_rev, norm_sub_rev w]
  exact hP.norm_sub_le_of_mem_range f w hw

end IsOrthProj

/-! ### Range invariance -/

section RangeInvariance

variable {P : E →L[ℝ] E} {y G : ℝ → E} {a b : ℝ}

/-- If `y' = P (G t)` (for an arbitrary `G`) on `[a, b]`, the normal component `y - P y` is
constant on `[a, b]`. -/
theorem normal_const_of_deriv_mem_range (hP : IsOrthProj P) (hyc : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (P (G t)) (Ici t) t) :
    ∀ t ∈ Icc a b, y t - P (y t) = y a - P (y a) := by
  refine constant_of_has_deriv_right_zero (f := fun t => y t - P (y t))
    (hyc.sub (P.continuous.comp_continuousOn hyc)) fun t ht => ?_
  have h := (hy t ht).sub (P.hasFDerivAt.comp_hasDerivWithinAt t (hy t ht))
  simp only [hP.idem, sub_self] at h
  exact h

/-- **Range invariance.** If `y' = P (G t)` on `[a, b]` and `y a ∈ range P`, then
`y t ∈ range P` for all `t ∈ [a, b]`. -/
theorem range_invariant_of_deriv_mem_range (hP : IsOrthProj P) (hyc : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (P (G t)) (Ici t) t) (h0 : P (y a) = y a) :
    ∀ t ∈ Icc a b, P (y t) = y t := by
  intro t ht
  have h := normal_const_of_deriv_mem_range hP hyc hy t ht
  rw [h0, sub_self, sub_eq_zero] at h
  exact h.symm

end RangeInvariance

namespace ODESolution

variable {P : E →L[ℝ] E} {F : ℝ → E → E} {y : ℝ → E} {a b : ℝ}

/-- A solution of the Galerkin ODE `y' = P F(t, y)` starting in `range P` stays in `range P`. -/
theorem galerkin_mem_range (hP : IsOrthProj P) (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) : ∀ t ∈ Icc a b, P (y t) = y t :=
  range_invariant_of_deriv_mem_range (G := fun t => F t (y t)) hP hy.cont hy.deriv h0

/-! ### Galerkin condition and Dirac–Frenkel principle -/

/-- Any right derivative of a Galerkin solution equals `P F(t, y t)`. -/
theorem galerkin_deriv_eq (hy : ODESolution (fun t x => P (F t x)) y a b) {t : ℝ}
    (ht : t ∈ Ico a b) {v : E} (hv : HasDerivWithinAt y v (Ici t) t) :
    v = P (F t (y t)) :=
  (uniqueDiffWithinAt_Ici t).eq_deriv _ hv (hy.deriv t ht)

/-- **Galerkin condition.** The velocity `v = y'(t)` of a solution of `y' = P F(t, y)` satisfies
`⟪v - F(t, y), w⟫ = 0` for every `w ∈ range P`. -/
theorem galerkin_inner_eq_zero (hP : IsOrthProj P)
    (hy : ODESolution (fun t x => P (F t x)) y a b) {t : ℝ} (ht : t ∈ Ico a b) {v : E}
    (hv : HasDerivWithinAt y v (Ici t) t) {w : E} (hw : P w = w) :
    ⟪v - F t (y t), w⟫ = 0 := by
  rw [hy.galerkin_deriv_eq ht hv]
  exact hP.inner_apply_sub_self_of_mem _ hw

/-- **Dirac–Frenkel principle / minimal defect.** The velocity of a solution of
`y' = P F(t, y)` is the element of `range P` closest to `F(t, y)`:
`‖y'(t) - F(t, y)‖ ≤ ‖w - F(t, y)‖` for all `w ∈ range P`. -/
theorem galerkin_defect_le (hP : IsOrthProj P)
    (hy : ODESolution (fun t x => P (F t x)) y a b) {t : ℝ} (ht : t ∈ Ico a b) {v : E}
    (hv : HasDerivWithinAt y v (Ici t) t) {w : E} (hw : P w = w) :
    ‖v - F t (y t)‖ ≤ ‖w - F t (y t)‖ := by
  rw [hy.galerkin_deriv_eq ht hv]
  exact hP.norm_apply_sub_le _ hw

/-! ### Norm conservation and dissipation -/

/-- Along a Galerkin solution in `range P`, `d/dt ‖y‖² = 2 ⟪F(t, y), y⟫`. -/
theorem hasDerivWithinAt_norm_sq_galerkin (hP : IsOrthProj P)
    (hy : ODESolution (fun t x => P (F t x)) y a b) (h0 : P (y a) = y a) {t : ℝ}
    (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun s => ‖y s‖ ^ 2) (2 * ⟪F t (y t), y t⟫) (Ici t) t := by
  have hr : P (y t) = y t := hy.galerkin_mem_range hP h0 t (Ico_subset_Icc_self ht)
  refine (hy.deriv t ht).norm_sq.congr_deriv ?_
  show 2 * ⟪y t, P (F t (y t))⟫ = _
  rw [hP.inner_apply_right_of_mem _ hr, real_inner_comm]

/-- **Norm conservation** of the Galerkin ODE (Ceruti–Kusch–Lubich, arXiv 2104.05247, Thm 4,
for the Galerkin step without truncation): if `⟪F(t, y t), y t⟫ = 0` along the solution and
`y a ∈ range P`, then `‖y t‖ = ‖y a‖`. -/
theorem galerkin_norm_eq (hP : IsOrthProj P) (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) (hF : ∀ t ∈ Ico a b, ⟪F t (y t), y t⟫ = 0) :
    ∀ t ∈ Icc a b, ‖y t‖ = ‖y a‖ := by
  have hc : ContinuousOn (fun s => ‖y s‖ ^ 2) (Icc a b) := hy.cont.norm.pow 2
  have hconst := constant_of_has_deriv_right_zero hc fun t ht => by
    simpa [hF t ht] using hy.hasDerivWithinAt_norm_sq_galerkin hP h0 ht
  intro t ht
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hconst t ht)

/-- **Norm dissipation** of the Galerkin ODE: if `⟪F(t, y t), y t⟫ ≤ 0` along the solution and
`y a ∈ range P`, then `‖y t‖ ≤ ‖y a‖`. -/
theorem galerkin_norm_le (hP : IsOrthProj P) (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) (hF : ∀ t ∈ Ico a b, ⟪F t (y t), y t⟫ ≤ 0) :
    ∀ t ∈ Icc a b, ‖y t‖ ≤ ‖y a‖ := by
  have hc : ContinuousOn (fun s => ‖y s‖ ^ 2) (Icc a b) := hy.cont.norm.pow 2
  have hle := image_le_of_deriv_right_le_deriv_boundary hc
    (fun t ht => hy.hasDerivWithinAt_norm_sq_galerkin hP h0 ht)
    (B := fun _ => ‖y a‖ ^ 2) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun t _ => hasDerivWithinAt_const _ _ _) fun t ht => by nlinarith [hF t ht]
  intro t ht
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hle ht)

/-- Norm conservation, global form: `⟪F(t, x), x⟫ = 0` for all `t` and all `x ∈ range P`. -/
theorem galerkin_norm_eq' (hP : IsOrthProj P) (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) (hF : ∀ t x, P x = x → ⟪F t x, x⟫ = 0) :
    ∀ t ∈ Icc a b, ‖y t‖ = ‖y a‖ :=
  hy.galerkin_norm_eq hP h0 fun t ht =>
    hF t _ (hy.galerkin_mem_range hP h0 t (Ico_subset_Icc_self ht))

/-- Norm dissipation, global form: `⟪F(t, x), x⟫ ≤ 0` for all `t` and all `x ∈ range P`. -/
theorem galerkin_norm_le' (hP : IsOrthProj P) (hy : ODESolution (fun t x => P (F t x)) y a b)
    (h0 : P (y a) = y a) (hF : ∀ t x, P x = x → ⟪F t x, x⟫ ≤ 0) :
    ∀ t ∈ Icc a b, ‖y t‖ ≤ ‖y a‖ :=
  hy.galerkin_norm_le hP h0 fun t ht =>
    hF t _ (hy.galerkin_mem_range hP h0 t (Ico_subset_Icc_self ht))

/-! ### Conservation of linear invariants -/

/-- **Exact balance law along a Galerkin solution.** If at time `t` the projection reproduces the
moment `⟪c, ·⟫` of the vector field, `⟪c, P F(t, y t)⟫ = ⟪c, F(t, y t)⟫`, then
`d/dt ⟪c, y⟫ = ⟪c, F(t, y)⟫` at `t`: the Galerkin solution satisfies the balance law of the full
model in the direction `c`.  Neither `P c = c` nor an orthogonality property of `P` is needed;
`P c = c` is one sufficient condition (`IsOrthProj.inner_apply_right_of_mem`).  For an orthogonal
`P` the hypothesis is equivalent to `F(t, y t) ⊥ (c - P c)`.  In conservative DLRA it holds
because the relevant moment of the field (for mass, the flux divergence `∫ F dv = -∇ₓ · j`) lies
in the range of the spatial projector and `1` lies in the velocity basis; this is how local
conservation is enforced there (cf. arXiv 2206.09374, eqs. (10)–(12)). -/
theorem hasDerivWithinAt_inner_galerkin (hy : ODESolution (fun t x => P (F t x)) y a b) {c : E}
    {t : ℝ} (ht : t ∈ Ico a b) (hPF : ⟪c, P (F t (y t))⟫ = ⟪c, F t (y t)⟫) :
    HasDerivWithinAt (fun s => ⟪c, y s⟫) ⟪c, F t (y t)⟫ (Ici t) t := by
  have h := (innerSL ℝ c).hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)
  refine h.congr_deriv ?_
  simp only [innerSL_apply_apply]
  exact hPF

/-- **Conservation of a linear invariant whose moment is reproduced by the projection.** If
`⟪c, P F(t, y t)⟫ = ⟪c, F(t, y t)⟫` (the projection is exact on the relevant moment of the
field) and `⟪c, F(t, y t)⟫ = 0` along a solution of `y' = P F(t, y)`, then `⟪c, y t⟫ = ⟪c, y a⟫`.
This is the continuous-time form of the mechanism of conservative DLRA (Einkemmer–Joseph 2021;
Einkemmer–Ostermann–Scalone, arXiv 2206.09374), where the conserved direction `c` need not lie in
the Galerkin space.  No assumption on `y a` is needed. -/
theorem galerkin_inner_const_of_inner_apply (hy : ODESolution (fun t x => P (F t x)) y a b)
    {c : E} (hPF : ∀ t ∈ Ico a b, ⟪c, P (F t (y t))⟫ = ⟪c, F t (y t)⟫)
    (hF : ∀ t ∈ Ico a b, ⟪c, F t (y t)⟫ = 0) :
    ∀ t ∈ Icc a b, ⟪c, y t⟫ = ⟪c, y a⟫ :=
  constant_of_has_deriv_right_zero (f := fun t => ⟪c, y t⟫)
    ((innerSL ℝ c).continuous.comp_continuousOn hy.cont) fun t ht =>
      (hy.hasDerivWithinAt_inner_galerkin ht (hPF t ht)).congr_deriv (hF t ht)

/-- **Conservation of linear invariants** (the standard Galerkin argument): if
`⟪c, F(t, y t)⟫ = 0` along a solution of `y' = P F(t, y)` and the conserved direction lies in the
Galerkin trial space, `P c = c`, then `⟪c, y t⟫ = ⟪c, y a⟫`.  No assumption on `y a` is needed.

Cf. conservative DLRA (Einkemmer–Joseph 2021; Einkemmer–Ostermann–Scalone, arXiv 2206.09374),
where conservation is instead enforced by making the projection exact on `f^n` and on the flux
rather than by `P c = c`; that mechanism is `galerkin_inner_const_of_inner_apply` and, for the
explicit-Euler step of the paper, `inner_proj_euler_eq`.  With `P c = c` one also has
`⟪c, P Y₀⟫ = ⟪c, Y₀⟫`, so a Galerkin step started from the projected value `P Y₀` conserves
`⟪c, Y₀⟫` (`galerkin_inner_eq_of_eq_proj`). -/
theorem galerkin_inner_const (hP : IsOrthProj P) (hy : ODESolution (fun t x => P (F t x)) y a b)
    {c : E} (hc : P c = c) (hF : ∀ t ∈ Ico a b, ⟪c, F t (y t)⟫ = 0) :
    ∀ t ∈ Icc a b, ⟪c, y t⟫ = ⟪c, y a⟫ :=
  hy.galerkin_inner_const_of_inner_apply (fun _ _ => hP.inner_apply_right_of_mem _ hc) hF

/-- A Galerkin step started from the projection `y a = P Y₀` of an arbitrary `Y₀` conserves
`⟪c, Y₀⟫` when `P c = c` and `⟪c, F(t, y t)⟫ = 0`: the projection of the starting value does not
change the invariant. -/
theorem galerkin_inner_eq_of_eq_proj (hP : IsOrthProj P)
    (hy : ODESolution (fun t x => P (F t x)) y a b) {c Y₀ : E} (hc : P c = c)
    (hF : ∀ t ∈ Ico a b, ⟪c, F t (y t)⟫ = 0) (h0 : y a = P Y₀) :
    ∀ t ∈ Icc a b, ⟪c, y t⟫ = ⟪c, Y₀⟫ := fun t ht => by
  rw [hy.galerkin_inner_const hP hc hF t ht, h0, hP.inner_apply_right_of_mem _ hc]

/-- Conservation of linear invariants, global form: `⟪c, F(t, x)⟫ = 0` for all `t, x`. -/
theorem galerkin_inner_const' (hP : IsOrthProj P)
    (hy : ODESolution (fun t x => P (F t x)) y a b) {c : E} (hc : P c = c)
    (hF : ∀ t x, ⟪c, F t x⟫ = 0) : ∀ t ∈ Icc a b, ⟪c, y t⟫ = ⟪c, y a⟫ :=
  hy.galerkin_inner_const hP hc fun t _ => hF t _

end ODESolution

/-! ### Energy decay and energy conservation -/

section Energy

variable {P : E →L[ℝ] E} {ℰ : E → ℝ} {g : E → E} {y : ℝ → E} {a b : ℝ}

/-- Chain rule for an energy with gradient field `g`: `d/dt ℰ(y) = ⟪g(y), y'⟫`. -/
theorem hasDerivWithinAt_energy_comp (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    {s : Set ℝ} {t : ℝ} {v : E} (hv : HasDerivWithinAt y v s t) :
    HasDerivWithinAt (ℰ ∘ y) ⟪g (y t), v⟫ s t := by
  simpa [innerSL_apply_apply] using (hℰ (y t)).comp_hasDerivWithinAt t hv

/-- An energy with a gradient (in the sense of `HasGradientAt`) has the Fréchet derivative
`⟪g x, ·⟫`.  (Requires completeness, as Mathlib's `HasGradientAt` does.) -/
theorem hasFDerivAt_of_hasGradientAt [CompleteSpace E] (hℰ : ∀ x, HasGradientAt ℰ (g x) x)
    (x : E) : HasFDerivAt ℰ (innerSL ℝ (g x)) x := by
  have h := (hℰ x).hasFDerivAt
  convert h using 1
  ext v
  rfl

/-- An energy with a gradient field is continuous. -/
theorem continuous_of_hasFDerivAt_innerSL (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) :
    Continuous ℰ :=
  continuous_iff_continuousAt.2 fun x => (hℰ x).continuousAt

namespace ODESolution

/-- **Dissipation identity** for projected gradient flows `y' = -P ∇ℰ(y)`:
`d/dt ℰ(y(t)) = -‖P ∇ℰ(y(t))‖²` (Ceruti–Kusch–Lubich, arXiv 2104.05247, proof of Thm 5).
No assumption on `y a` is needed. -/
theorem hasDerivWithinAt_energy_gradFlow (hP : IsOrthProj P)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hy : ODESolution (fun _ x => -P (g x)) y a b)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (ℰ ∘ y) (-‖P (g (y t))‖ ^ 2) (Ici t) t := by
  refine (hasDerivWithinAt_energy_comp hℰ (hy.deriv t ht)).congr_deriv ?_
  rw [inner_neg_right, real_inner_comm, hP.inner_self_apply]

/-- **Energy decay with rate** for projected gradient flows (Ceruti–Kusch–Lubich,
arXiv 2104.05247, Thm 5 for the Galerkin step, i.e. without the truncation term `β ϑ`):
if `α² ≤ ‖P ∇ℰ(y)‖²` along the solution, then `ℰ(y t) ≤ ℰ(y a) - α² (t - a)`. -/
theorem energy_le_sub_gradFlow (hP : IsOrthProj P)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hy : ODESolution (fun _ x => -P (g x)) y a b)
    {α : ℝ} (hα : ∀ t ∈ Ico a b, α ^ 2 ≤ ‖P (g (y t))‖ ^ 2) :
    ∀ t ∈ Icc a b, ℰ (y t) ≤ ℰ (y a) - α ^ 2 * (t - a) := by
  have hc : ContinuousOn (ℰ ∘ y) (Icc a b) :=
    (continuous_of_hasFDerivAt_innerSL hℰ).comp_continuousOn hy.cont
  have hB : ∀ t, HasDerivWithinAt (fun s => ℰ (y a) - α ^ 2 * (s - a)) (-(α ^ 2)) (Ici t) t :=
    fun t => by
      simpa using (((hasDerivWithinAt_id t (Ici t)).sub_const a).const_mul (α ^ 2)).const_sub
        (ℰ (y a))
  have h := image_le_of_deriv_right_le_deriv_boundary hc
    (fun t ht => hy.hasDerivWithinAt_energy_gradFlow hP hℰ ht)
    (B := fun s => ℰ (y a) - α ^ 2 * (s - a)) (by simp)
    (Continuous.continuousOn (by fun_prop)) (fun t _ => hB t)
    fun t ht => by simpa using hα t ht
  exact fun t ht => h ht

/-- **Energy decay** for projected gradient flows `y' = -P ∇ℰ(y)`: `ℰ(y t) ≤ ℰ(y a)`. -/
theorem energy_le_gradFlow (hP : IsOrthProj P) (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    (hy : ODESolution (fun _ x => -P (g x)) y a b) : ∀ t ∈ Icc a b, ℰ (y t) ≤ ℰ (y a) := by
  intro t ht
  have h := hy.energy_le_sub_gradFlow hP hℰ (α := 0)
    (fun t _ => by nlinarith [sq_nonneg ‖P (g (y t))‖]) t ht
  simpa using h

/-- Energy decay for projected gradient flows, stated with Mathlib's `HasGradientAt`. -/
theorem energy_le_gradFlow_of_hasGradientAt [CompleteSpace E] (hP : IsOrthProj P)
    (hℰ : ∀ x, HasGradientAt ℰ (g x) x) (hy : ODESolution (fun _ x => -P (g x)) y a b) :
    ∀ t ∈ Icc a b, ℰ (y t) ≤ ℰ (y a) :=
  hy.energy_le_gradFlow hP (hasFDerivAt_of_hasGradientAt hℰ)

/-- Dissipation identity, stated with Mathlib's `HasGradientAt`. -/
theorem hasDerivWithinAt_energy_gradFlow_of_hasGradientAt [CompleteSpace E] (hP : IsOrthProj P)
    (hℰ : ∀ x, HasGradientAt ℰ (g x) x) (hy : ODESolution (fun _ x => -P (g x)) y a b)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (ℰ ∘ y) (-‖P (g (y t))‖ ^ 2) (Ici t) t :=
  hy.hasDerivWithinAt_energy_gradFlow hP (hasFDerivAt_of_hasGradientAt hℰ) ht

variable {F : ℝ → E → E}

/-- **Energy conservation** for the Galerkin ODE `y' = P F(t, y)`: if
`⟪∇ℰ(y), P F(t, y)⟫ = 0` along the solution, then `ℰ(y t) = ℰ(y a)`. -/
theorem galerkin_energy_eq (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    (hy : ODESolution (fun t x => P (F t x)) y a b)
    (hF : ∀ t ∈ Ico a b, ⟪g (y t), P (F t (y t))⟫ = 0) :
    ∀ t ∈ Icc a b, ℰ (y t) = ℰ (y a) :=
  constant_of_has_deriv_right_zero
    ((continuous_of_hasFDerivAt_innerSL hℰ).comp_continuousOn hy.cont) fun t ht =>
      (hasDerivWithinAt_energy_comp hℰ (hy.deriv t ht)).congr_deriv (hF t ht)

/-- Energy conservation, range form: if `⟪∇ℰ(x), P F(t, x)⟫ = 0` for all `x ∈ range P` and
`y a ∈ range P`, then `ℰ(y t) = ℰ(y a)`. -/
theorem galerkin_energy_eq' (hP : IsOrthProj P) (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    (hy : ODESolution (fun t x => P (F t x)) y a b) (h0 : P (y a) = y a)
    (hF : ∀ t x, P x = x → ⟪g x, P (F t x)⟫ = 0) :
    ∀ t ∈ Icc a b, ℰ (y t) = ℰ (y a) :=
  hy.galerkin_energy_eq hℰ fun t ht =>
    hF t _ (hy.galerkin_mem_range hP h0 t (Ico_subset_Icc_self ht))

/-- **Energy conservation for Hamiltonian-type fields** (Ceruti–Kusch–Lubich,
arXiv 2104.05247, Thms 6–7 for the Galerkin step, i.e. without truncation): if
`F(t, x) = J ∇ℰ(x)` with `J` skew (`⟪J z, z⟫ = 0`, e.g. multiplication by `-i` on a complex
space viewed as a real one) and `J` commuting with `P` (e.g. `P` complex linear), then the
Galerkin solution conserves `ℰ`.  No assumption on `y a` is needed. -/
theorem galerkin_energy_eq_of_skew (hP : IsOrthProj P)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E}
    (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJP : ∀ z, J (P z) = P (J z)) (hFJ : ∀ t x, F t x = J (g x))
    (hy : ODESolution (fun t x => P (F t x)) y a b) :
    ∀ t ∈ Icc a b, ℰ (y t) = ℰ (y a) := by
  refine hy.galerkin_energy_eq hℰ fun t _ => ?_
  rw [hFJ, ← hP.symm, ← hP.inner_comp, ← hJP, real_inner_comm, hJ]

end ODESolution

end Energy

/-! ### Galerkin steps followed by a truncation

The rank-adaptive BUG integrator (Ceruti–Kusch–Lubich, arXiv 2104.05247) follows the Galerkin
step `Ŷ₀ = y a ↦ Ŷ₁ = y b` by a truncation `Y₁` with `‖Y₁ - Ŷ₁‖ ≤ ϑ`.  The conservation
properties of the Galerkin step then hold up to `O(ϑ)`; this is the structure of the proofs of
Thms 4–7 of that paper, and we state them for an abstract Galerkin step.  Two inputs of the paper
are hypotheses here: the identification `Ŷ₀ = Y₀` (Lemma 1 of arXiv 2104.05247 for augmented
bases), which the statements below leave to the user by comparing with `y a`; and the truncation
bound `‖Y₁ - Ŷ₁‖ ≤ ϑ` itself.  Lemma 1 is proved downstream as `IsRankAdaptiveBUGStep.start_eq`
(`Integrators/RankAdaptiveBUG.lean`), where the paper-form statements comparing with `Y₀` are
`IsRankAdaptiveBUGStep.abs_norm_sub_le` (Thm 4), `IsRankAdaptiveBUGStep.energy_le` (Thm 5),
`IsRankAdaptiveBUGStep.schrodinger_energy_sub_le` (Thm 6) and
`IsRankAdaptiveBUGStep.hamiltonian_energy_sub_le` (Thm 7).  For Thm 6 the generic mean-value
constant of `truncated_energy_sub_le_of_skew` is weaker than the published one; the exact
constant is recovered by `truncated_quadratic_energy_sub_le_of_skew`. -/

section Truncation

variable {P : E →L[ℝ] E} {ℰ : E → ℝ} {g : E → E} {F : ℝ → E → E} {y : ℝ → E} {a b : ℝ}

/-- Mean value bound for an energy: `|ℰ x - ℰ z| ≤ β ‖x - z‖` if `‖∇ℰ‖ ≤ β` on `[z, x]`. -/
theorem abs_energy_sub_le (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {x z : E} {β : ℝ}
    (hβ : ∀ w ∈ segment ℝ z x, ‖g w‖ ≤ β) : |ℰ x - ℰ z| ≤ β * ‖x - z‖ := by
  have h := (convex_segment z x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := ℰ) (f' := fun w => innerSL ℝ (g w)) (fun w _ => (hℰ w).hasFDerivWithinAt)
    (fun w hw => by rw [innerSL_apply_norm]; exact hβ w hw) (left_mem_segment ℝ z x)
    (right_mem_segment ℝ z x)
  simpa [Real.norm_eq_abs] using h

/-- **Midpoint identity for quadratic energies**: for self-adjoint `A`,
`⟪x, A x⟫ - ⟪z, A z⟫ = ⟪A x + A z, x - z⟫`. -/
lemma inner_apply_self_sub_inner_apply_self {A : E →L[ℝ] E} (hA : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (x z : E) : ⟪x, A x⟫ - ⟪z, A z⟫ = ⟪A x + A z, x - z⟫ := by
  rw [inner_add_left, inner_sub_right, inner_sub_right, hA x z, real_inner_comm (A x) x,
    real_inner_comm (A z) x, real_inner_comm (A z) z]
  ring

/-- The quadratic energy `x ↦ ⟪x, A x⟫ / 2` of a self-adjoint `A` has gradient `A x`. -/
theorem hasFDerivAt_half_inner_apply_self {A : E →L[ℝ] E} (hA : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (x : E) : HasFDerivAt (fun x : E => ⟪x, A x⟫ / 2) (innerSL ℝ (A x)) x := by
  have h : HasFDerivAt (fun x : E => ⟪x, A x⟫) (innerSL ℝ ((2 : ℝ) • A x)) x := by
    refine ((hasFDerivAt_id x).inner ℝ A.hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, id_eq, ContinuousLinearMap.coe_id', innerSL_apply_apply,
      real_inner_smul_left]
    rw [← hA x v, real_inner_comm v]
    ring
  convert HasFDerivAt.mul_const h (1 / 2 : ℝ) using 1
  · ext z
    ring
  · ext v
    simp only [innerSL_apply_apply, smul_apply, real_inner_smul_left,
      smul_eq_mul]
    ring

namespace ODESolution

/-- **Norm conservation up to truncation** (Ceruti–Kusch–Lubich, arXiv 2104.05247, Thm 4, in
the two-sided form): if the Galerkin step conserves the norm (`⟪F(t, y), y⟫ = 0` along the
solution, `y a ∈ range P`) and `‖Y₁ - y b‖ ≤ ϑ`, then `|‖Y₁‖ - ‖y a‖| ≤ ϑ`.  The paper's
statement compares with `Y₀`: it is recovered with `y a = Y₀`, which for the augmented BUG step
(together with `P (y a) = y a`) is Lemma 1 of arXiv 2104.05247, not proved in this file
(`IsRankAdaptiveBUGStep.start_eq`; the paper form is `IsRankAdaptiveBUGStep.abs_norm_sub_le` in
`Integrators/RankAdaptiveBUG.lean`). -/
theorem truncated_galerkin_norm_sub_le (hP : IsOrthProj P)
    (hy : ODESolution (fun t x => P (F t x)) y a b) (h0 : P (y a) = y a)
    (hF : ∀ t ∈ Ico a b, ⟪F t (y t), y t⟫ = 0) (hab : a ≤ b) {Y₁ : E} {ϑ : ℝ}
    (htr : ‖Y₁ - y b‖ ≤ ϑ) : |‖Y₁‖ - ‖y a‖| ≤ ϑ := by
  rw [← hy.galerkin_norm_eq hP h0 hF b (right_mem_Icc.2 hab)]
  exact (abs_norm_sub_norm_le _ _).trans htr

/-- **Energy decay up to truncation** for projected gradient flows (Ceruti–Kusch–Lubich,
arXiv 2104.05247, Thm 5): if `α² ≤ ‖P ∇ℰ(y)‖²` along the Galerkin solution of
`y' = -P ∇ℰ(y)`, the truncation satisfies `‖Y₁ - y b‖ ≤ ϑ` and `‖∇ℰ‖ ≤ β` on the segment
`[y b, Y₁]`, then `ℰ(Y₁) ≤ ℰ(y a) - α² (b - a) + β ϑ`.  The paper's statement compares with
`Y₀`: it is recovered with `y a = Y₀`, which for the augmented BUG step is Lemma 1 of
arXiv 2104.05247, not proved in this file (`IsRankAdaptiveBUGStep.start_eq`; the paper form is
`IsRankAdaptiveBUGStep.energy_le` in `Integrators/RankAdaptiveBUG.lean`). -/
theorem truncated_energy_le_gradFlow (hP : IsOrthProj P)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hy : ODESolution (fun _ x => -P (g x)) y a b)
    (hab : a ≤ b) {α : ℝ} (hα : ∀ t ∈ Ico a b, α ^ 2 ≤ ‖P (g (y t))‖ ^ 2) {Y₁ : E} {ϑ β : ℝ}
    (htr : ‖Y₁ - y b‖ ≤ ϑ) (hβ : ∀ w ∈ segment ℝ (y b) Y₁, ‖g w‖ ≤ β) :
    ℰ Y₁ ≤ ℰ (y a) - α ^ 2 * (b - a) + β * ϑ := by
  have h1 := hy.energy_le_sub_gradFlow hP hℰ hα b (right_mem_Icc.2 hab)
  have h2 := abs_energy_sub_le hℰ hβ
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ _ (left_mem_segment ℝ _ _))
  have h3 : β * ‖Y₁ - y b‖ ≤ β * ϑ := mul_le_mul_of_nonneg_left htr hβ0
  have h4 := (abs_le.1 h2).2
  linarith

/-- **Energy conservation up to truncation** for Hamiltonian-type fields `F = J ∇ℰ`
(Ceruti–Kusch–Lubich, arXiv 2104.05247, Thms 6–7): with `J` skew and commuting with `P`,
`‖Y₁ - y b‖ ≤ ϑ` and `‖∇ℰ‖ ≤ β` on `[y b, Y₁]`, one has `|ℰ(Y₁) - ℰ(y a)| ≤ β ϑ`.  The paper's
statement compares with `Y₀`: it is recovered with `y a = Y₀`, which for the augmented BUG step
is Lemma 1 of arXiv 2104.05247, not proved in this file (`IsRankAdaptiveBUGStep.start_eq`; the
paper form of Thm 7 is `IsRankAdaptiveBUGStep.hamiltonian_energy_sub_le` in
`Integrators/RankAdaptiveBUG.lean`).

For Thm 7 the constant matches the paper (`β` is the maximum of `‖∇ℰ‖` over the segment).  For
Thm 6 (Schrödinger, `E(Y) = ⟪Y, H Y⟫`, `Y' = -i H Y`) one takes `ℰ = E / 2`, `∇ℰ = H`, `J = -i`;
the resulting constant `2 sup_{[Ŷ₁, Y₁]} ‖H w‖ = 2 max (‖H Y₁‖, ‖H Ŷ₁‖)` for `E` is at least the
paper's `γ = ‖H Y₁ + H Ŷ₁‖` (equal to leading order as `ϑ → 0`).  The exact constant `γ` is
`truncated_quadratic_energy_sub_le_of_skew`. -/
theorem truncated_energy_sub_le_of_skew (hP : IsOrthProj P)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E}
    (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJP : ∀ z, J (P z) = P (J z)) (hFJ : ∀ t x, F t x = J (g x))
    (hy : ODESolution (fun t x => P (F t x)) y a b) (hab : a ≤ b) {Y₁ : E} {ϑ β : ℝ}
    (htr : ‖Y₁ - y b‖ ≤ ϑ) (hβ : ∀ w ∈ segment ℝ (y b) Y₁, ‖g w‖ ≤ β) :
    |ℰ Y₁ - ℰ (y a)| ≤ β * ϑ := by
  rw [← hy.galerkin_energy_eq_of_skew hP hℰ hJ hJP hFJ b (right_mem_Icc.2 hab)]
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ _ (left_mem_segment ℝ _ _))
  exact (abs_energy_sub_le hℰ hβ).trans (mul_le_mul_of_nonneg_left htr hβ0)

/-- **Quadratic energy conservation up to truncation, with the published constant**
(Ceruti–Kusch–Lubich, arXiv 2104.05247, Thm 6): let `A` be self-adjoint, `E(x) = ⟪x, A x⟫`,
and let the Galerkin step solve `y' = P (J (A y))` with `J` skew and commuting with `P` (the
Schrödinger equation `i Y' = H[Y]` on `ℂ^{m×n}` viewed as a real space, with `A = H`, `J = -i`,
`P` the complex-linear projector `Z ↦ Û Û* Z V̂ V̂*`).  If `‖Y₁ - y b‖ ≤ ϑ`, then
`|E(Y₁) - E(y a)| ≤ γ ϑ` with `γ = ‖A Y₁ + A (y b)‖`, the paper's `‖H[Y₁] + H[Ŷ₁]‖`.  The proof
is the paper's: `E` is conserved by the Galerkin step and
`E(Y₁) - E(Ŷ₁) = ⟪A Y₁ + A Ŷ₁, Y₁ - Ŷ₁⟫`.  The bound is stated two-sided.  The paper's
comparison with `Y₀` is recovered with `y a = Y₀`, Lemma 1 of arXiv 2104.05247, not proved in
this file (`IsRankAdaptiveBUGStep.start_eq`; the paper form is
`IsRankAdaptiveBUGStep.schrodinger_energy_sub_le` in `Integrators/RankAdaptiveBUG.lean`). -/
theorem truncated_quadratic_energy_sub_le_of_skew (hP : IsOrthProj P) {A J : E →L[ℝ] E}
    (hA : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫) (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJP : ∀ z, J (P z) = P (J z))
    (hFJ : ∀ t x, F t x = J (A x)) (hy : ODESolution (fun t x => P (F t x)) y a b)
    (hab : a ≤ b) {Y₁ : E} {ϑ : ℝ} (htr : ‖Y₁ - y b‖ ≤ ϑ) :
    |⟪Y₁, A Y₁⟫ - ⟪y a, A (y a)⟫| ≤ ‖A Y₁ + A (y b)‖ * ϑ := by
  have hcons : ⟪y b, A (y b)⟫ / 2 = ⟪y a, A (y a)⟫ / 2 :=
    hy.galerkin_energy_eq_of_skew (ℰ := fun x : E => ⟪x, A x⟫ / 2) hP
      (hasFDerivAt_half_inner_apply_self hA) hJ hJP hFJ b (right_mem_Icc.2 hab)
  have hab' : ⟪y a, A (y a)⟫ = ⟪y b, A (y b)⟫ := by linarith
  rw [hab', inner_apply_self_sub_inner_apply_self hA]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left htr (norm_nonneg _))

end ODESolution

end Truncation

/-! ### Stability of explicit-Euler Galerkin steps -/

section Euler

variable {P : E →L[ℝ] E}

/-- **Galerkin explicit Euler step is stable**: if the full explicit Euler step
`x ↦ x + h F(t, x)` does not increase the norm on `range P`, then the Galerkin step
`x ↦ P (P x + h F(t, P x))` does not increase the norm.

This is the form `uⁿ⁺¹ = P_{n+1} G(P_{n+1} uⁿ)` of the unconventional (BUG) integrator applied to
an explicit full step `G` in Kusch–Einkemmer–Ceruti, arXiv 2107.07282, Thm 4, and it applies to
Thm 3 of that paper substep by substep (each of the K-, S- and L-substeps is a projection of a
nonexpansive full step; for the S-step with the sign-reversed full step).  It does **not** cover
Thm 2 (projector splitting with the original S-step), whose S-step amplifies and whose stability
comes only from the product of the three substep factors under a stricter CFL condition.  The
`L²`-stability of the full explicit step (CFL condition and Fourier analysis, the substantive part
of Thm 4) is the hypothesis `hF`, not a result of this file. -/
theorem galerkin_euler_norm_le (hP : IsOrthProj P) {F : ℝ → E → E} {t h : ℝ}
    (hF : ∀ x, P x = x → ‖x + h • F t x‖ ≤ ‖x‖) (x : E) :
    ‖P (P x + h • F t (P x))‖ ≤ ‖x‖ :=
  (hP.norm_le _).trans ((hF _ (hP.idem x)).trans (hP.norm_le x))

/-- On `range P`, the projected Euler step is the projection of the full Euler step. -/
lemma projEuler_eq {F : ℝ → E → E} {h t : ℝ} {x : E} (hx : P x = x) :
    projEuler P F h t x = P (x + h • F t x) := by
  rw [projEuler, map_add, map_smul, hx]

/-- The projected forward Euler step maps `range P` into itself. -/
lemma projEuler_mem_range (hP : IsOrthProj P) {F : ℝ → E → E} {h t : ℝ} {x : E}
    (hx : P x = x) : P (projEuler P F h t x) = projEuler P F h t x := by
  rw [projEuler_eq hx, hP.idem]

/-- **Stability of the projected forward Euler step** on `range P`: under the hypothesis that
the full forward Euler step is norm-nonincreasing on `range P`, so is the projected step.  See
`galerkin_euler_norm_le` for the relation to arXiv 2107.07282: Thm 4 (and Thm 3 substep by
substep), not Thm 2; the full-step `L²`-stability (CFL condition) is the hypothesis `hF`. -/
theorem projEuler_norm_le (hP : IsOrthProj P) {F : ℝ → E → E} {t h : ℝ}
    (hF : ∀ x, P x = x → ‖x + h • F t x‖ ≤ ‖x‖) {x : E} (hx : P x = x) :
    ‖projEuler P F h t x‖ ≤ ‖x‖ := by
  rw [projEuler_eq hx]
  exact (hP.norm_le _).trans (hF x hx)

/-- **Discrete norm stability**: if every full forward Euler step is norm-nonincreasing on
`range P` and `x₀ ∈ range P`, all iterates of the projected forward Euler method stay in
`range P` and satisfy `‖xₙ‖ ≤ ‖x₀‖`.  (The projector is fixed here; for the BUG integrator of
arXiv 2107.07282, Thm 4, with step-dependent projectors, iterate `galerkin_euler_norm_le`.) -/
theorem projEulerIter_norm_le (hP : IsOrthProj P) {F : ℝ → E → E} {h t₀ : ℝ}
    (hF : ∀ t x, P x = x → ‖x + h • F t x‖ ≤ ‖x‖) {x₀ : E} (hx₀ : P x₀ = x₀) (n : ℕ) :
    P (projEulerIter P F h t₀ x₀ n) = projEulerIter P F h t₀ x₀ n ∧
      ‖projEulerIter P F h t₀ x₀ n‖ ≤ ‖x₀‖ := by
  induction n with
  | zero => exact ⟨hx₀, le_rfl⟩
  | succ n ih =>
    refine ⟨projEuler_mem_range hP ih.1, ?_⟩
    exact (projEuler_norm_le hP (hF _) ih.1).trans ih.2

/-! ### Discrete balance laws of explicit-Euler Galerkin steps -/

/-- **Discrete balance law of a Galerkin explicit Euler step** (abstract form of the local
continuity equation of Einkemmer–Ostermann–Scalone, arXiv 2206.09374, Thm 1): for the step
`x₁ = P (x₀ + h F(t, x₀))`, if the projection is exact on the moments `⟪c, ·⟫` of the old state
and of the field, `⟪c, P x₀⟫ = ⟪c, x₀⟫` and `⟪c, P F(t, x₀)⟫ = ⟪c, F(t, x₀)⟫`, then
`⟪c, x₁⟫ = ⟪c, x₀⟫ + h ⟪c, F(t, x₀)⟫`, i.e. `(⟪c, x₁⟫ - ⟪c, x₀⟫) / h = ⟪c, F(t, x₀)⟫`.

In the paper `P = P_x ⊗ P_v` is the projection onto the augmented bases, the first hypothesis
holds because `P fⁿ = fⁿ` (augmentation by `Xⁿ`, `Vⁿ`, eqs. (10)–(11)), the second because `1`
lies in the velocity basis and the flux divergence lies in the spatial basis (augmentation by
`∇Xⁿ`, eq. (12)), and `c` ranges over the local test functionals `δ_x ⊗ 1_v`, for which
`⟪c, F(t, fⁿ)⟫ = -∇ₓ · jⁿ(x)`; the conclusion is then eq. (13).  The verification of the two
exactness hypotheses for the concrete Vlasov discretization, and the conservative truncation that
completes Algorithm 1 of the paper (see `Stability/Conservation.lean`), are not part of this
file. -/
theorem inner_proj_euler_eq {P : E →L[ℝ] E} {F : ℝ → E → E} {t h : ℝ} {x₀ c : E}
    (hx : ⟪c, P x₀⟫ = ⟪c, x₀⟫) (hPF : ⟪c, P (F t x₀)⟫ = ⟪c, F t x₀⟫) :
    ⟪c, P (x₀ + h • F t x₀)⟫ = ⟪c, x₀⟫ + h * ⟪c, F t x₀⟫ := by
  rw [map_add, map_smul, inner_add_right, real_inner_smul_right, hx, hPF]

/-- Discrete balance law for the projected forward Euler step `x + h P F(t, x)`: if
`⟪c, P F(t, x)⟫ = ⟪c, F(t, x)⟫`, then `⟪c, projEuler P F h t x⟫ = ⟪c, x⟫ + h ⟪c, F(t, x)⟫`. -/
theorem inner_projEuler_eq {F : ℝ → E → E} {h t : ℝ} {x c : E}
    (hPF : ⟪c, P (F t x)⟫ = ⟪c, F t x⟫) :
    ⟪c, projEuler P F h t x⟫ = ⟪c, x⟫ + h * ⟪c, F t x⟫ := by
  rw [projEuler, inner_add_right, real_inner_smul_right, hPF]

/-- **Discrete conservation of linear invariants** by the projected forward Euler step: if
`P c = c` and `⟪c, F(t, x)⟫ = 0`, then `⟪c, projEuler P F h t x⟫ = ⟪c, x⟫` (for any `x`). -/
theorem inner_projEuler_eq_of_mem (hP : IsOrthProj P) {F : ℝ → E → E} {h t : ℝ} {x c : E}
    (hc : P c = c) (hF : ⟪c, F t x⟫ = 0) : ⟪c, projEuler P F h t x⟫ = ⟪c, x⟫ := by
  rw [inner_projEuler_eq (hP.inner_apply_right_of_mem _ hc), hF, mul_zero, add_zero]

/-- Discrete conservation of linear invariants along the projected forward Euler method: if
`P c = c` and `⟪c, F(t, x)⟫ = 0` for all `t, x`, then `⟪c, xₙ⟫ = ⟪c, x₀⟫` for all `n`. -/
theorem inner_projEulerIter_eq_of_mem (hP : IsOrthProj P) {F : ℝ → E → E} {h t₀ : ℝ} {x₀ c : E}
    (hc : P c = c) (hF : ∀ t x, ⟪c, F t x⟫ = 0) (n : ℕ) :
    ⟪c, projEulerIter P F h t₀ x₀ n⟫ = ⟪c, x₀⟫ := by
  induction n with
  | zero => rfl
  | succ n ih => exact (inner_projEuler_eq_of_mem hP hc (hF _ _)).trans ih

end Euler

/-! ### Examples: the hypotheses are jointly satisfiable -/

section Examples

variable {P : E →L[ℝ] E}

/-- `ℰ = ‖·‖² / 2` has gradient `id`. -/
theorem hasFDerivAt_half_norm_sq (x : E) :
    HasFDerivAt (fun x : E => ‖x‖ ^ 2 / 2) (innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (1 / 2 : ℝ)
  convert h using 1
  · ext z; ring
  · ext v; simp

/-- A non-trivial projected gradient flow: for `ℰ = ‖·‖² / 2` (so `∇ℰ = id`) and
`x₀ ∈ range P`, `y t = e^{a-t} x₀` solves `y' = -P ∇ℰ(y)`. -/
theorem odeSolution_exp_smul {x₀ : E} (hx₀ : P x₀ = x₀) (a b : ℝ) :
    ODESolution (fun _ x => -P (id x)) (fun t => Real.exp (a - t) • x₀) a b := by
  have hd : ∀ t, HasDerivAt (fun t => Real.exp (a - t) • x₀)
      (-P (id (Real.exp (a - t) • x₀))) t := fun t => by
    have h1 : HasDerivAt (fun t => a - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub a
    convert h1.exp.smul_const x₀ using 1
    simp only [id, map_smul, hx₀, mul_neg_one, neg_smul]
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt,
    fun t _ => (hd t).hasDerivWithinAt⟩

/-- The hypotheses of `ODESolution.energy_le_gradFlow` are jointly satisfiable for every
orthogonal projector `P` and starting value `x₀ ∈ range P` (and the theorem applies). -/
example (hP : IsOrthProj P) {x₀ : E} (hx₀ : P x₀ = x₀) (a b : ℝ) :
    ∀ t ∈ Icc a b, ‖Real.exp (a - t) • x₀‖ ^ 2 / 2 ≤ ‖x₀‖ ^ 2 / 2 := by
  intro t ht
  have h := (odeSolution_exp_smul hx₀ a b).energy_le_gradFlow
    (ℰ := fun x : E => ‖x‖ ^ 2 / 2) hP hasFDerivAt_half_norm_sq t ht
  simpa using h

/-- A concrete **non-constant** instance of `ODESolution.energy_le_gradFlow`: `E = ℝ`, `P = 1`,
`x₀ = 1`, `a < b`.  The trajectory `y t = e^{a-t}` satisfies `y b ≠ y a`, and the energy
`y² / 2` decreases along it. -/
example {a b : ℝ} (hab : a < b) :
    Real.exp (a - b) • (1 : ℝ) ≠ Real.exp (a - a) • (1 : ℝ) ∧
      ∀ t ∈ Icc a b, ‖Real.exp (a - t) • (1 : ℝ)‖ ^ 2 / 2 ≤ ‖(1 : ℝ)‖ ^ 2 / 2 := by
  refine ⟨?_, fun t ht => ?_⟩
  · rw [sub_self, Real.exp_zero, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    exact (Real.exp_lt_one_iff.2 (by linarith)).ne
  · have hy := odeSolution_exp_smul (P := (1 : ℝ →L[ℝ] ℝ)) (x₀ := 1) (by simp) a b
    have h := hy.energy_le_gradFlow (ℰ := fun x : ℝ => ‖x‖ ^ 2 / 2) IsOrthProj.one
      hasFDerivAt_half_norm_sq t ht
    simpa using h

/-- The stability hypothesis of `galerkin_euler_norm_le` is satisfiable non-trivially: the
damping field `F(t, x) = -x` with `h = 1 / 2` (full step `x ↦ x / 2`), for any orthogonal `P`. -/
example (hP : IsOrthProj P) (x : E) :
    ‖P (P x + (1 / 2 : ℝ) • -(P x))‖ ≤ ‖x‖ := by
  refine galerkin_euler_norm_le (F := fun (_ : ℝ) (z : E) => -z) (t := 0) (h := 1 / 2) hP
    (fun z _ => ?_) x
  have hz : z + (1 / 2 : ℝ) • -z = (1 / 2 : ℝ) • z := by
    rw [smul_neg]; module
  rw [hz, norm_smul]
  have := norm_nonneg z
  norm_num
  linarith

/-- The real inner product of `ℂⁿ` viewed as a real space is the real part of the complex one. -/
lemma real_inner_euclideanSpace_complex {n : ℕ} (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪x, y⟫ = RCLike.re (inner ℂ x y) := by
  simp [PiLp.inner_apply, Complex.inner, mul_comm]

/-- The skew hypotheses of `ODESolution.galerkin_energy_eq_of_skew`,
`ODESolution.truncated_energy_sub_le_of_skew` and
`ODESolution.truncated_quadratic_energy_sub_le_of_skew` are jointly satisfiable
non-degenerately: on `ℂⁿ` viewed as a real inner product space, `P` the orthogonal projector
onto an arbitrary complex subspace `K`, `J = -i` (the Schrödinger case), and `A` the orthogonal
projector onto another complex subspace `K'` (self-adjoint, in general not commuting with `P`).
(Over `ℝ²` the hypotheses `hJ`, `hJP` would force `P ∈ {0, 1}` or `J = 0`, so a complex structure
is needed.) -/
example {n : ℕ} (K K' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    let P : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
      K.starProjection.restrictScalars ℝ
    let J : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
      ((-Complex.I) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))).restrictScalars ℝ
    let A : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
      K'.starProjection.restrictScalars ℝ
    IsOrthProj P ∧ (∀ z, ⟪J z, z⟫ = 0) ∧ (∀ z, J (P z) = P (J z)) ∧
      ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫ := by
  intro P J A
  refine ⟨⟨fun x => ?_, fun x y => ?_⟩, fun z => ?_, fun z => ?_, fun u v => ?_⟩
  · simp only [P, ContinuousLinearMap.coe_restrictScalars']
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem K x)
  · simp only [P, ContinuousLinearMap.coe_restrictScalars', real_inner_euclideanSpace_complex]
    rw [Submodule.inner_starProjection_left_eq_right]
  · simp [J, real_inner_euclideanSpace_complex, ← Complex.ofReal_pow]
  · simp [P, J]
  · simp only [A, ContinuousLinearMap.coe_restrictScalars', real_inner_euclideanSpace_complex]
    rw [Submodule.inner_starProjection_left_eq_right]

/-- The hypotheses of the discrete conservation law `inner_projEulerIter_eq_of_mem` are
satisfiable with a non-trivial dynamics: for orthogonal `P` and `c ∈ range P`, the field
`F(t, x) = x - ⟪c, x⟫ • c` (with `‖c‖ = 1`) has `⟪c, F⟫ = 0` and moves every `x ∉ span {c}`. -/
example (hP : IsOrthProj P) {c : E} (hc : P c = c) (hc1 : ‖c‖ = 1) {h t₀ : ℝ} {x₀ : E}
    (n : ℕ) :
    ⟪c, projEulerIter P (fun _ x => x - ⟪c, x⟫ • c) h t₀ x₀ n⟫ = ⟪c, x₀⟫ := by
  refine inner_projEulerIter_eq_of_mem hP hc (fun _ x => ?_) n
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hc1]
  ring

/-- A **non-constant** solution to which the norm- and energy-conservation results apply
(`ODESolution.galerkin_norm_eq'` and `ODESolution.galerkin_energy_eq_of_skew`): on `ℂ` viewed as a
real inner product space, `P = 1`, `F(t, z) = -i z` (the Schrödinger case with `H = 1`, i.e.
`J = -i`, `ℰ = ‖·‖² / 2`, `∇ℰ = id`) and `y t = e^{-i t} z₀`.  For `z₀ ≠ 0` the trajectory is not
constant: `y π = -z₀ ≠ z₀ = y 0`. -/
example (z₀ : ℂ) (hz₀ : z₀ ≠ 0) :
    Complex.exp (-Complex.I * Real.pi) * z₀ ≠ Complex.exp (-Complex.I * (0 : ℝ)) * z₀ ∧
      (∀ t ∈ Icc (0 : ℝ) Real.pi,
        ‖Complex.exp (-Complex.I * t) * z₀‖ = ‖Complex.exp (-Complex.I * (0 : ℝ)) * z₀‖) ∧
      ∀ t ∈ Icc (0 : ℝ) Real.pi, ‖Complex.exp (-Complex.I * t) * z₀‖ ^ 2 / 2 =
        ‖Complex.exp (-Complex.I * (0 : ℝ)) * z₀‖ ^ 2 / 2 := by
  have hskew : ∀ z : ℂ, ⟪-Complex.I * z, z⟫ = 0 := fun z => by
    rw [Complex.inner]
    simp only [neg_mul, map_neg, map_mul, Complex.conj_I, neg_neg, Complex.mul_re, Complex.I_re,
      Complex.conj_re, zero_mul, Complex.I_im, Complex.conj_im, mul_neg, one_mul, sub_neg_eq_add,
      zero_add, Complex.mul_im, neg_zero]
    ring
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * t) * z₀)
      ((1 : ℂ →L[ℝ] ℂ) (-Complex.I * (Complex.exp (-Complex.I * t) * z₀))) t := fun t => by
    have h1 : HasDerivAt (fun w : ℂ => Complex.exp (-Complex.I * w))
        (Complex.exp (-Complex.I * t) * (-Complex.I * 1)) t :=
      ((hasDerivAt_id (t : ℂ)).const_mul (-Complex.I)).cexp
    convert h1.comp_ofReal.mul_const z₀ using 1
    rw [one_apply_eq_self]
    ring
  have hy : ODESolution (fun _ z => (1 : ℂ →L[ℝ] ℂ) (-Complex.I * z))
      (fun t : ℝ => Complex.exp (-Complex.I * t) * z₀) 0 Real.pi :=
    ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩
  let J : ℂ →L[ℝ] ℂ := (-Complex.I) • ContinuousLinearMap.id ℝ ℂ
  have hJ : ∀ z, J z = -Complex.I * z := fun z => by
    simp only [J, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  refine ⟨?_, hy.galerkin_norm_eq' IsOrthProj.one rfl fun t x _ => hskew x, ?_⟩
  · have hpi : Complex.exp (-Complex.I * Real.pi) = -1 := by
      rw [show -Complex.I * Real.pi = -(Real.pi * Complex.I) by ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      norm_num
    rw [hpi, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    intro h
    exact hz₀ (by linear_combination -h / 2)
  · exact hy.galerkin_energy_eq_of_skew (ℰ := fun x : ℂ => ‖x‖ ^ 2 / 2) (g := fun x => x)
      (J := J) IsOrthProj.one hasFDerivAt_half_norm_sq (fun z => by rw [hJ]; exact hskew z)
      (fun _ => rfl) (fun _ x => (hJ x).symm)

/-- The moment-exactness variant `ODESolution.galerkin_inner_const_of_inner_apply` applies where
the standard argument does not (`P c ≠ c`): on `ℂ` as a real inner product space, `P` the
orthogonal projector onto the imaginary axis, `c = 1` (so `P c = 0`), `F(t, z) = i` and the
non-constant solution `y t = z₀ + t i` of `y' = P F`; the invariant is `⟪1, y⟫ = Re y`. -/
example (z₀ : ℂ) (a b : ℝ) :
    let P : ℂ →L[ℝ] ℂ := Complex.imCLM.smulRight Complex.I
    IsOrthProj P ∧ P 1 ≠ 1 ∧
      ∀ t ∈ Icc a b, ⟪(1 : ℂ), z₀ + t * Complex.I⟫ = ⟪(1 : ℂ), z₀ + a * Complex.I⟫ := by
  intro P
  have hPz : ∀ z : ℂ, P z = z.im * Complex.I := fun z => by
    simp [P, Complex.real_smul]
  have hPI : P Complex.I = Complex.I := by rw [hPz]; simp
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z₀ + t * Complex.I)
      (P ((fun (_ : ℝ) (_ : ℂ) => Complex.I) t (z₀ + t * Complex.I))) t := fun t => by
    rw [hPI]
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add z₀
  have hy : ODESolution (fun t x => P ((fun (_ : ℝ) (_ : ℂ) => Complex.I) t x))
      (fun t : ℝ => z₀ + t * Complex.I) a b :=
    ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩
  have h1I : ⟪(1 : ℂ), Complex.I⟫ = 0 := by simp [Complex.inner]
  refine ⟨⟨fun z => ?_, fun z w => ?_⟩, ?_, ?_⟩
  · rw [hPz, hPz]; simp
  · rw [hPz, hPz, Complex.inner, Complex.inner]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.neg_re, Complex.neg_im]
    ring
  · rw [hPz]; simp
  · exact hy.galerkin_inner_const_of_inner_apply (fun _ _ => by rw [hPI]) (fun _ _ => h1I)

end Examples

end LeanDLRA
