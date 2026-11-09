import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Analysis.Defs
import LeanDLRA.LinearAlgebra.Projection.Defs

/-!
# Time-continuous dynamical low-rank approximation

Dynamical low-rank approximation (DLRA) replaces the full evolution equation
`Ȧ = F(t, A)` by the projected equation

    Ẏ = P(Y) F(t, Y),

where `P(Y)` is the orthogonal projector onto the tangent space `T_Y M` of the low-rank manifold
`M` at `Y` (Koch–Lubich, SIAM J. Matrix Anal. Appl. 29 (2007), eq. (1.2) and Lemma 4.1).  All
results below only use the projector *along the trajectory*, so we write the DLRA equation as an
ODE with a **time-dependent family of orthogonal projectors** `P : ℝ → (E →L[ℝ] E)`,

    Ẏ(t) = P(t) F(t, Y(t)),       P(t) = P(Y(t)),

on an arbitrary real inner product space `E` (matrices with the Frobenius inner product, Tucker
and tree tensors, or function spaces).  A solution with a state-dependent projector field
`PY : E → (E →L[ℝ] E)` is converted into this form by `ODESolution.dlra_of_stateProj`.

## Main results

* **Dirac–Frenkel principle** (Koch–Lubich 2007, eq. (1.2); Lubich's variational principle):
  `IsOrthProj.diracFrenkel_tfae` — for an orthogonal projector `Q` the three statements
  `v = Q f`, (`v ∈ range Q` and `⟪v - f, w⟫ = 0` for `w ∈ range Q`), and
  (`v ∈ range Q` and `‖v - f‖ ≤ ‖w - f‖` for `w ∈ range Q`) are equivalent.  Along a DLRA
  trajectory: `ODESolution.dlra_inner_eq_zero` (Galerkin condition),
  `ODESolution.dlra_defect_le` (`Ẏ` is the best approximation of `F(t, Y)` in the tangent
  space), `ODESolution.dlra_defect_eq` (the defect is the normal component), and the converse
  `odeSolution_dlra_of_galerkin` / `odeSolution_dlra_of_minDefect`.
* **Robust error bound, Lipschitz case** (`ODESolution.dlra_norm_sub_le_gronwallBound`): if `F`
  is `L`-Lipschitz, `‖(1 - P(t)) F(t, Y t)‖ ≤ ε` along `Y` and `‖Y a - A a‖ ≤ δ`, then
  `‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a) = e^{L(t-a)} δ + ε (e^{L(t-a)} - 1)/L`
  (Kieri–Lubich–Walach, SIAM J. Numer. Anal. 54 (2016), the continuous DLRA estimate;
  Carrel–Gander–Vandereycken, arXiv 2203.08455, Theorem 2.3), with explicit forms
  `dlra_norm_sub_le_exp_add` and `dlra_norm_sub_le_exp_mul`.
* **One-sided Lipschitz (stiff / parabolic) version**
  (`ODESolution.dlra_norm_sub_le_gronwallBound_of_oneSided`): the same with the one-sided
  Lipschitz constant `ℓ ∈ ℝ` (possibly negative) in place of `L` (Carrel–Vandereycken,
  arXiv 2312.00172, Theorem 7), also with the one-sided condition only along the two
  trajectories, and the stiff splitting `F = 𝓛 + G` with tangent stiff part
  (`dlra_norm_sub_le_of_stiff_split`, Theorem 7 with `ℓ_F ≤ ℓ_𝓛 + L_G` and `ε` bounding only
  the normal component of `G`).  For `ℓ < 0` the bound is **uniform in time**:
  `‖Y t - A t‖ ≤ e^{ℓ(t-a)} δ + ε/(-ℓ)`, and `dlra_eventually_norm_sub_le` gives
  `‖Y t - A t‖ ≤ ε/(-ℓ) + η` for all large `t` (long-time behaviour, the deterministic analogue
  of the rank-defect bound of arXiv 2606.15843, Theorem 4.5).
* **Norm conservation / dissipation** (`ODESolution.dlra_norm_eq`, `ODESolution.dlra_norm_le`)
  when `⟪F(t, Y), Y⟫ = 0` resp. `≤ 0` and `P(t) Y = Y` (the cone property `Y ∈ T_Y M` of
  low-rank manifolds), the identity `d/dt ‖Y‖² = 2 ⟪F(t, Y), Y⟫`, exponential bounds
  `‖Y t‖ ≤ e^{μ(t-a)} ‖Y a‖` and the **uniform-in-time Lyapunov bound**
  `‖Y t‖² ≤ e^{2μ(t-a)} ‖Y a‖² + β/(-μ)` under `⟪F(t, Y), Y⟫ ≤ μ ‖Y‖² + β`, `μ < 0`
  (deterministic analogue of arXiv 2606.15843, Theorem 4.4, whose key step is exactly
  `⟪Y, P_Y f⟫ = ⟪Y, f⟫`).  Further: energy decay for projected gradient flows and conservation
  of linear invariants `⟪c, Y⟫` with `P(t) c = c`.
* **Quasi-optimality** (`ODESolution.dlra_norm_sub_le_of_comparison`,
  `ODESolution.dlra_quasiOptimal`): comparison of `Y` with an arbitrary differentiable curve `X`
  (e.g. the best approximation of `A` on `M`) under curvature-free hypotheses on the tangential
  defect `‖P(t) (F(t, X) - Ẋ)‖` and on the normal component `‖(1 - P(t)) Ẋ‖`; and the abstract
  form of Koch–Lubich 2007, Theorem 5.1: if the projectors are Lipschitz along the two curves
  (`‖(P(t) - P_X(t)) z‖ ≤ γ ‖Y - X‖ ‖z‖`, the curvature bound of Koch–Lubich Lemma 4.2),
  `Ẋ ∈ range P_X(t)` and `‖Ẋ - P_X(t) Ȧ‖ ≤ c ‖A - X‖` (best-approximation property), then
  `‖Y t - A t‖ ≤ d + gronwallBound ‖Y a - X a‖ (L + γ(μ + μ')) ((L + c) d) (t - a)`, where
  `d` bounds the best-approximation error `‖A - X‖` on the interval.
* **Stability with respect to the data** (`ODESolution.dlra_norm_sub_sq_le_of_curvature`,
  abstract form of Bachmayr–Eisenmann–Uschmajew, arXiv 2308.16720, Theorem 2.5, parabolic
  problems on low-rank tensor manifolds): two DLRA trajectories `u' = P(t) F₁(t, u)`,
  `v' = Q(t) F₂(t, v)` satisfy
  `‖u t - v t‖² ≤ gronwallBound ‖u a - v a‖² (2(ℓ + κ(α + β)) + ε) (η²/ε) (t - a)` under the
  curvature estimate `‖(1 - P(t)) (u - v)‖ ≤ κ ‖u - v‖²` (Assumption A2 there), bounded normal
  components `α, β` and the one-sided bound `⟪F₁(u) - F₂(v), u - v⟫ ≤ ℓ ‖u - v‖² + η ‖u - v‖`;
  with exact data the exponential bound `dlra_norm_sub_le_exp_of_curvature` and uniqueness
  `dlra_eqOn_of_curvature`.

## Deviations from the papers

* The projector is a time-dependent family `P(t)` (frozen along the trajectory) rather than a
  map `Y ↦ P(Y)` on a manifold; all assumptions are required only along the trajectories, which
  is the generality used in the proofs of Koch–Lubich and Carrel–Vandereycken.
* In the stability theorem of arXiv 2308.16720 the time-dependent integrand of
  `Λ(t) = 2κ ∫ (‖u'‖ + ‖v'‖ + …)` is replaced by constant bounds `α, β` of the normal components,
  and the operator is bounded (the paper allows unbounded coercive `𝒜(t) : V → V*`).
* Koch–Lubich Theorem 5.1 bounds `‖Y - X‖` by `2βe^{βt} ∫₀ᵗ ‖A - X‖`; we use the supremum `d`
  of `‖A - X‖` on the interval (so `∫₀ᵗ ‖A - X‖ ≤ t d`), and keep general Lipschitz `F`
  (Koch–Lubich treat `F(t, Y) = Ȧ(t)`, i.e. `L = 0`).  The geometric facts (curvature bound,
  derivative of the best approximation) are hypotheses.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Dirac–Frenkel principle: pointwise form -/

namespace IsOrthProj

variable {Q : E →L[ℝ] E}

/-- Pythagoras for the best approximation in `range Q`: for `w ∈ range Q`,
`‖w - f‖² = ‖w - Q f‖² + ‖Q f - f‖²`. -/
lemma norm_sub_sq_eq_of_mem (hQ : IsOrthProj Q) (f : E) {w : E} (hw : Q w = w) :
    ‖w - f‖ ^ 2 = ‖w - Q f‖ ^ 2 + ‖Q f - f‖ ^ 2 := by
  have h1 : w - f = (w - Q f) + (Q f - f) := by abel
  have hm : Q (w - Q f) = w - Q f := by rw [map_sub, hw, hQ.idem]
  have h2 : ⟪Q f - f, w - Q f⟫ = 0 := hQ.inner_apply_sub_self_of_mem f hm
  rw [h1, norm_add_sq_real, real_inner_comm (Q f - f) (w - Q f), h2]
  ring

/-- **Uniqueness of the best approximation**: if `v ∈ range Q` is at least as close to `f` as
every element of `range Q`, then `v = Q f`. -/
lemma eq_apply_of_forall_norm_sub_le (hQ : IsOrthProj Q) {v f : E} (hv : Q v = v)
    (h : ∀ w, Q w = w → ‖v - f‖ ≤ ‖w - f‖) : v = Q f := by
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (h (Q f) (hQ.idem f)) 2
  have h2 := hQ.norm_sub_sq_eq_of_mem f hv
  have h3 : ‖v - Q f‖ ^ 2 ≤ 0 := by linarith
  have h4 : ‖v - Q f‖ = 0 := by nlinarith [norm_nonneg (v - Q f)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h4)

/-- **Dirac–Frenkel principle (pointwise form).**  For an orthogonal projector `Q` (the tangent
projector `P(Y)`) and a vector `f` (the vector field `F(t, Y)`), the following are equivalent:
1. `v = Q f` (the DLRA velocity);
2. `v ∈ range Q` and the Galerkin condition `⟪v - f, w⟫ = 0` holds for all `w ∈ range Q`
   (the Dirac–Frenkel time-dependent variational principle);
3. `v ∈ range Q` and `‖v - f‖ ≤ ‖w - f‖` for all `w ∈ range Q` (minimal defect).

(Koch–Lubich 2007, eq. (1.2) and the remark following it.) -/
theorem diracFrenkel_tfae (hQ : IsOrthProj Q) (v f : E) :
    List.TFAE [v = Q f, Q v = v ∧ ∀ w, Q w = w → ⟪v - f, w⟫ = 0,
      Q v = v ∧ ∀ w, Q w = w → ‖v - f‖ ≤ ‖w - f‖] := by
  tfae_have 1 → 2 := by
    rintro rfl
    exact ⟨hQ.idem f, fun w hw => hQ.inner_apply_sub_self_of_mem f hw⟩
  tfae_have 2 → 1 := fun ⟨hv, h⟩ => hQ.eq_apply_of_galerkin hv h
  tfae_have 1 → 3 := by
    rintro rfl
    exact ⟨hQ.idem f, fun w hw => hQ.norm_apply_sub_le f hw⟩
  tfae_have 3 → 1 := fun ⟨hv, h⟩ => hQ.eq_apply_of_forall_norm_sub_le hv h
  tfae_finish

end IsOrthProj

/-! ### DLRA trajectories -/

section Trajectory

variable {P : ℝ → E →L[ℝ] E} {F : ℝ → E → E} {Y : ℝ → E} {a b : ℝ}

/-- A solution of the DLRA equation `Ẏ = PY(Y) F(t, Y)` with a state-dependent projector field
`PY : E → (E →L[ℝ] E)` (`PY x` = tangent projector at `x`) solves the DLRA equation with the
time-dependent projector family `P(t) = PY(Y t)` frozen along the trajectory.  All theorems of
this file therefore apply to the manifold formulation. -/
lemma ODESolution.dlra_of_stateProj {PY : E → E →L[ℝ] E}
    (hY : ODESolution (fun t x => PY x (F t x)) Y a b) :
    ODESolution (fun t x => PY (Y t) (F t x)) Y a b :=
  ⟨hY.cont, hY.deriv⟩

namespace ODESolution

/-- Any right derivative of a DLRA trajectory equals `P(t) F(t, Y t)`. -/
theorem dlra_deriv_eq (hY : ODESolution (fun t x => P t (F t x)) Y a b) {t : ℝ}
    (ht : t ∈ Ico a b) {v : E} (hv : HasDerivWithinAt Y v (Ici t) t) :
    v = P t (F t (Y t)) :=
  (uniqueDiffWithinAt_Ici t).eq_deriv _ hv (hY.deriv t ht)

/-- The DLRA velocity lies in the range of `P(t)` (the tangent space). -/
theorem dlra_deriv_mem (hY : ODESolution (fun t x => P t (F t x)) Y a b) {t : ℝ}
    (ht : t ∈ Ico a b) (hPt : IsOrthProj (P t)) {v : E} (hv : HasDerivWithinAt Y v (Ici t) t) :
    P t v = v := by
  rw [hY.dlra_deriv_eq ht hv, hPt.idem]

/-- **Galerkin condition / Dirac–Frenkel principle** along a DLRA trajectory: the velocity
`v = Ẏ(t)` satisfies `⟪v - F(t, Y), w⟫ = 0` for every `w` in the tangent space `range P(t)`. -/
theorem dlra_inner_eq_zero (hY : ODESolution (fun t x => P t (F t x)) Y a b) {t : ℝ}
    (ht : t ∈ Ico a b) (hPt : IsOrthProj (P t)) {v : E} (hv : HasDerivWithinAt Y v (Ici t) t)
    {w : E} (hw : P t w = w) : ⟪v - F t (Y t), w⟫ = 0 := by
  rw [hY.dlra_deriv_eq ht hv]
  exact hPt.inner_apply_sub_self_of_mem _ hw

/-- **Minimal defect.**  The DLRA velocity is the best approximation of `F(t, Y)` in the tangent
space: `‖Ẏ - F(t, Y)‖ ≤ ‖w - F(t, Y)‖` for every `w ∈ range P(t)`. -/
theorem dlra_defect_le (hY : ODESolution (fun t x => P t (F t x)) Y a b) {t : ℝ}
    (ht : t ∈ Ico a b) (hPt : IsOrthProj (P t)) {v : E} (hv : HasDerivWithinAt Y v (Ici t) t)
    {w : E} (hw : P t w = w) : ‖v - F t (Y t)‖ ≤ ‖w - F t (Y t)‖ := by
  rw [hY.dlra_deriv_eq ht hv]
  exact hPt.norm_apply_sub_le _ hw

/-- The defect of the DLRA velocity is the normal component of the vector field:
`‖Ẏ - F(t, Y)‖ = ‖(1 - P(t)) F(t, Y)‖` (the quantity bounded by `ε` in the error analysis). -/
theorem dlra_defect_eq (hY : ODESolution (fun t x => P t (F t x)) Y a b) {t : ℝ}
    (ht : t ∈ Ico a b) {v : E} (hv : HasDerivWithinAt Y v (Ici t) t) :
    ‖v - F t (Y t)‖ = ‖(1 - P t) (F t (Y t))‖ := by
  rw [hY.dlra_deriv_eq ht hv, sub_apply, one_apply_eq_self,
    norm_sub_rev]

end ODESolution

/-- **Dirac–Frenkel principle ⇒ DLRA equation.**  If `Y` is continuous on `[a, b]` and has right
derivatives `v t` in the tangent space `range P(t)` which satisfy the Galerkin condition
`⟪v t - F(t, Y t), w⟫ = 0` for all `w ∈ range P(t)`, then `Y` solves `Ẏ = P(t) F(t, Y)`. -/
theorem odeSolution_dlra_of_galerkin (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) {v : ℝ → E}
    (hc : ContinuousOn Y (Icc a b)) (hv : ∀ t ∈ Ico a b, HasDerivWithinAt Y (v t) (Ici t) t)
    (hvP : ∀ t ∈ Ico a b, P t (v t) = v t)
    (hg : ∀ t ∈ Ico a b, ∀ w, P t w = w → ⟪v t - F t (Y t), w⟫ = 0) :
    ODESolution (fun t x => P t (F t x)) Y a b where
  cont := hc
  deriv t ht := by
    have h := (hP t ht).eq_apply_of_galerkin (hvP t ht) (hg t ht)
    change HasDerivWithinAt Y (P t (F t (Y t))) (Ici t) t
    rw [← h]
    exact hv t ht

/-- **Minimal-defect principle ⇒ DLRA equation.**  If the right derivatives `v t` of `Y` lie in
`range P(t)` and minimise `‖w - F(t, Y t)‖` over `w ∈ range P(t)`, then `Y` solves
`Ẏ = P(t) F(t, Y)`. -/
theorem odeSolution_dlra_of_minDefect (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) {v : ℝ → E}
    (hc : ContinuousOn Y (Icc a b)) (hv : ∀ t ∈ Ico a b, HasDerivWithinAt Y (v t) (Ici t) t)
    (hvP : ∀ t ∈ Ico a b, P t (v t) = v t)
    (hm : ∀ t ∈ Ico a b, ∀ w, P t w = w → ‖v t - F t (Y t)‖ ≤ ‖w - F t (Y t)‖) :
    ODESolution (fun t x => P t (F t x)) Y a b where
  cont := hc
  deriv t ht := by
    have h := (hP t ht).eq_apply_of_forall_norm_sub_le (hvP t ht) (hm t ht)
    change HasDerivWithinAt Y (P t (F t (Y t))) (Ici t) t
    rw [← h]
    exact hv t ht

end Trajectory

/-! ### Robust error bounds -/

section ErrorBounds

variable {P : ℝ → E →L[ℝ] E} {F : ℝ → E → E} {Y A : ℝ → E} {a b ε δ : ℝ}

/-- The defect of the DLRA field with respect to the full field is the normal component. -/
private lemma dlra_field_defect (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) :
    ∀ t ∈ Ico a b, ‖(fun t x => P t (F t x)) t (Y t) - F t (Y t)‖ ≤ ε := fun t ht => by
  have h := hε t ht
  rwa [sub_apply, one_apply_eq_self, norm_sub_rev] at h

namespace ODESolution

/-- **Robust DLRA error bound, Lipschitz case** (Kieri–Lubich–Walach 2016; Carrel–Gander–
Vandereycken, arXiv 2203.08455, Theorem 2.3).  Let `A' = F(t, A)` with `F` `L`-Lipschitz and let
`Y` solve the DLRA equation `Y' = P(t) F(t, Y)`.  If the normal component of the field is small
along the DLRA trajectory, `‖(1 - P(t)) F(t, Y t)‖ ≤ ε`, and `‖Y a - A a‖ ≤ δ`, then
`‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a) = e^{L(t-a)} δ + ε (e^{L(t-a)} - 1) / L`.
No property of the projectors is needed. -/
theorem dlra_norm_sub_le_gronwallBound {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound hF hL (ηy := ε) (ηz := 0) hY.cont hY.deriv
    (dlra_field_defect hε) hA.cont hA.deriv (fun _ _ => by simp) hδ t ht
  rwa [add_zero] at h

/-- Explicit form of the Lipschitz error bound for `L > 0`:
`‖Y t - A t‖ ≤ e^{L(t-a)} δ + ε (e^{L(t-a)} - 1) / L`. -/
theorem dlra_norm_sub_le_exp_add {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 < L)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b,
      ‖Y t - A t‖ ≤ Real.exp (L * (t - a)) * δ + ε * (Real.exp (L * (t - a)) - 1) / L := by
  intro t ht
  have h := dlra_norm_sub_le_gronwallBound hF hL.le hA hY hε hδ t ht
  rw [gronwallBound_of_K_ne_0 hL.ne'] at h
  calc ‖Y t - A t‖ ≤ δ * Real.exp (L * (t - a)) + ε / L * (Real.exp (L * (t - a)) - 1) := h
    _ = _ := by ring

/-- Error bound in the non-stiff form `‖Y t - A t‖ ≤ e^{L(t-a)} (δ + ε (t - a))`. -/
theorem dlra_norm_sub_le_exp_mul {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hε0 : 0 ≤ ε) (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ Real.exp (L * (t - a)) * (δ + ε * (t - a)) := fun t ht =>
  (dlra_norm_sub_le_gronwallBound hF hL hA hY hε hδ t ht).trans
    (gronwallBound_le_exp_mul hL hε0)

/-- **Manifold form of the Lipschitz error bound.**  With a state-dependent projector field `PY`
and the normal-component assumption `‖(1 - PY x) F(t, x)‖ ≤ ε` for all `x` in a set `M` (the
low-rank manifold, or a neighbourhood of the solution in it) that contains the DLRA trajectory:
`‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a)`. -/
theorem dlra_norm_sub_le_gronwallBound_of_mem {L : ℝ} {PY : E → E →L[ℝ] E} {M : Set E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hA : ODESolution F A a b)
    (hY : ODESolution (fun t x => PY x (F t x)) Y a b) (hYM : ∀ t ∈ Ico a b, Y t ∈ M)
    (hεM : ∀ t, ∀ x ∈ M, ‖(1 - PY x) (F t x)‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ L ε (t - a) :=
  dlra_norm_sub_le_gronwallBound hF hL hA hY.dlra_of_stateProj
    (fun t ht => hεM t _ (hYM t ht)) hδ

/-- **Robust DLRA error bound, one-sided Lipschitz case** (Carrel–Vandereycken,
arXiv 2312.00172, Theorem 7).  If `F` is one-sided Lipschitz with constant `ℓ ∈ ℝ` (possibly
negative: stiff, parabolic, dissipative problems), `‖(1 - P(t)) F(t, Y t)‖ ≤ ε` along the DLRA
trajectory and `‖Y a - A a‖ ≤ δ`, then
`‖Y t - A t‖ ≤ gronwallBound δ ℓ ε (t - a) = e^{ℓ(t-a)} δ + (t - a) φ₁(ℓ (t - a)) ε`. -/
theorem dlra_norm_sub_le_gronwallBound_of_oneSided {ℓ : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ ℓ ε (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSided hF (ηy := ε) (ηz := 0) hY.cont hY.deriv
    (dlra_field_defect hε) hA.cont hA.deriv (fun _ _ => by simp) hδ t ht
  rwa [add_zero] at h

/-- **Localised one-sided version**: the one-sided Lipschitz inequality is only required along
the pair of trajectories, `⟪F(t, Y) - F(t, A), Y - A⟫ ≤ ℓ ‖Y - A‖²` (cf. the energy-localised
region of Hu–Yu, arXiv 2610.41606, §3). -/
theorem dlra_norm_sub_le_gronwallBound_of_inner_le {ℓ : ℝ}
    (hF : ∀ t ∈ Ico a b, ⟪F t (Y t) - F t (A t), Y t - A t⟫ ≤ ℓ * ‖Y t - A t‖ ^ 2)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ ℓ ε (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_inner_le hF (ηy := ε) (ηz := 0) hY.cont hY.deriv
    (dlra_field_defect hε) hA.cont hA.deriv (fun _ _ => by simp) hδ t ht
  rwa [add_zero] at h

/-- Explicit one-sided bound valid for every real `ℓ`:
`‖Y t - A t‖ ≤ e^{ℓ(t-a)} δ + ε (t - a) max 1 e^{ℓ(t-a)}`. -/
theorem dlra_norm_sub_le_exp_add_max {ℓ : ℝ} (hF : IsOneSidedLipschitzField F ℓ) (hε0 : 0 ≤ ε)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤
      Real.exp (ℓ * (t - a)) * δ + ε * (t - a) * max 1 (Real.exp (ℓ * (t - a))) := fun t ht =>
  (dlra_norm_sub_le_gronwallBound_of_oneSided hF hA hY hε hδ t ht).trans
    (gronwallBound_le_exp_mul_add_max hε0 (sub_nonneg.2 ht.1))

/-- **Dissipative case** `ℓ ≤ 0`: `‖Y t - A t‖ ≤ e^{ℓ(t-a)} δ + ε (t - a)`; the modelling error
accumulates at most linearly in time. -/
theorem dlra_norm_sub_le_of_oneSided_nonpos {ℓ : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    (hℓ : ℓ ≤ 0) (hε0 : 0 ≤ ε) (hA : ODESolution F A a b)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ Real.exp (ℓ * (t - a)) * δ + ε * (t - a) := fun t ht => by
  have h := (dlra_norm_sub_le_gronwallBound_of_oneSided hF hA hY hε hδ t ht).trans
    (gronwallBound_le_of_nonpos hℓ hε0)
  linarith [mul_comm δ (Real.exp (ℓ * (t - a)))]

/-- **Uniform-in-time error bound** for strictly dissipative problems `ℓ < 0`:
`‖Y t - A t‖ ≤ e^{ℓ(t-a)} δ + ε / (-ℓ)` for all `t ∈ [a, b]`, independently of `b`
(long-time behaviour of DLRA; deterministic analogue of arXiv 2606.15843, Theorem 4.5, where
the rank defect `d - r` plays the role of `ε`). -/
theorem dlra_norm_sub_le_of_oneSided_neg {ℓ : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    (hℓ : ℓ < 0) (hε0 : 0 ≤ ε) (hA : ODESolution F A a b)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (F t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ Real.exp (ℓ * (t - a)) * δ + ε / (-ℓ) := fun t ht => by
  have h := (dlra_norm_sub_le_gronwallBound_of_oneSided hF hA hY hε hδ t ht).trans
    (gronwallBound_le_of_neg hℓ hε0)
  linarith [mul_comm δ (Real.exp (ℓ * (t - a)))]

/-- **Stiff splitting** (Carrel–Vandereycken, arXiv 2312.00172, Theorem 7 with
`ℓ_F ≤ ℓ_𝓛 + L_G`).  Let `F(t, x) = 𝓛(t) x + G(t, x)` with linear stiff part of logarithmic norm
`μ` (`⟪𝓛(t) x, x⟫ ≤ μ ‖x‖²`) and `L_G`-Lipschitz non-stiff part `G`.  If the stiff part maps the
DLRA trajectory into the tangent space (`P(t) 𝓛(t) Y = 𝓛(t) Y`, true e.g. for Lyapunov/Sylvester
operators on low-rank matrices) then only the normal component of `G` enters:
`‖(1 - P(t)) G(t, Y)‖ ≤ ε` gives `‖Y t - A t‖ ≤ gronwallBound δ (μ + L_G) ε (t - a)`, with no
dependence on `‖𝓛‖`. -/
theorem dlra_norm_sub_le_of_stiff_split {𝓛 : ℝ → E →L[ℝ] E} {G : ℝ → E → E} {μ LG : ℝ}
    (h𝓛 : ∀ t x, ⟪𝓛 t x, x⟫ ≤ μ * ‖x‖ ^ 2) (hG : IsLipschitzField G LG)
    (hA : ODESolution (fun t x => 𝓛 t x + G t x) A a b)
    (hY : ODESolution (fun t x => P t (𝓛 t x + G t x)) Y a b)
    (htan : ∀ t ∈ Ico a b, P t (𝓛 t (Y t)) = 𝓛 t (Y t))
    (hε : ∀ t ∈ Ico a b, ‖(1 - P t) (G t (Y t))‖ ≤ ε) (hδ : ‖Y a - A a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound δ (μ + LG) ε (t - a) := by
  have hF : IsOneSidedLipschitzField (fun t x => 𝓛 t x + G t x) (μ + LG) :=
    ((isOneSidedLipschitzField_linear_iff 𝓛 μ).2 h𝓛).add_lipschitz hG
  refine dlra_norm_sub_le_gronwallBound_of_oneSided hF hA hY (fun t ht => ?_) hδ
  have h1 : (1 - P t) (𝓛 t (Y t) + G t (Y t)) = (1 - P t) (G t (Y t)) := by
    simp only [sub_apply, one_apply_eq_self, map_add,
      htan t ht]
    abel
  rw [h1]
  exact hε t ht

end ODESolution

/-- **Long-time behaviour** for strictly dissipative problems (`ℓ < 0`): if the DLRA trajectory
and the exact solution exist on `[a, ∞)` and the normal component is bounded by `ε`, then for every
`η > 0` eventually `‖Y t - A t‖ ≤ ε / (-ℓ) + η`: the DLRA error is asymptotically bounded by the
modelling error divided by the dissipation rate, independently of the initial error. -/
theorem dlra_eventually_norm_sub_le {ℓ : ℝ} (hF : IsOneSidedLipschitzField F ℓ) (hℓ : ℓ < 0)
    (hε0 : 0 ≤ ε) (hA : ∀ b, ODESolution F A a b)
    (hY : ∀ b, ODESolution (fun t x => P t (F t x)) Y a b)
    (hε : ∀ t, a ≤ t → ‖(1 - P t) (F t (Y t))‖ ≤ ε) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, ‖Y t - A t‖ ≤ ε / (-ℓ) + η := by
  have hlim : Tendsto (fun t => Real.exp (ℓ * (t - a)) * ‖Y a - A a‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => ℓ * (t - a)) atTop atBot :=
      (tendsto_id.atTop_add (tendsto_const_nhds (x := -a))).const_mul_atTop_of_neg hℓ
        |>.congr fun t => by simp [sub_eq_add_neg]
    simpa using (Real.tendsto_exp_atBot.comp h1).mul_const ‖Y a - A a‖
  filter_upwards [hlim.eventually (eventually_le_nhds hη), eventually_ge_atTop a] with t ht hat
  have h := ODESolution.dlra_norm_sub_le_of_oneSided_neg hF hℓ hε0 (hA t) (hY t)
    (fun s hs => hε s hs.1) le_rfl t ⟨hat, le_rfl⟩
  linarith

end ErrorBounds

/-! ### Norm, energy and invariants along the DLRA flow -/

section Norm

variable {P : ℝ → E →L[ℝ] E} {F : ℝ → E → E} {Y : ℝ → E} {a b : ℝ}

namespace ODESolution

/-- **Norm identity.**  If `Y(t) ∈ range P(t)` (on the low-rank manifold: `Y ∈ T_Y M`), then
`d/dt ‖Y‖² = 2 ⟪F(t, Y), Y⟫`: the projection does not change the energy balance. -/
theorem dlra_hasDerivWithinAt_norm_sq (hY : ODESolution (fun t x => P t (F t x)) Y a b) {t : ℝ}
    (ht : t ∈ Ico a b) (hPt : IsOrthProj (P t)) (hYt : P t (Y t) = Y t) :
    HasDerivWithinAt (fun s => ‖Y s‖ ^ 2) (2 * ⟪F t (Y t), Y t⟫) (Ici t) t := by
  refine (hY.deriv t ht).norm_sq.congr_deriv ?_
  show 2 * ⟪Y t, P t (F t (Y t))⟫ = _
  rw [hPt.inner_apply_right_of_mem _ hYt, real_inner_comm]

/-- **Norm conservation** of the DLRA flow: if `⟪F(t, Y), Y⟫ = 0` and `P(t) Y = Y` along the
trajectory, then `‖Y t‖ = ‖Y a‖` (Koch–Lubich 2007, §1; e.g. Schrödinger-type equations). -/
theorem dlra_norm_eq (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hYP : ∀ t ∈ Ico a b, P t (Y t) = Y t)
    (hF : ∀ t ∈ Ico a b, ⟪F t (Y t), Y t⟫ = 0) : ∀ t ∈ Icc a b, ‖Y t‖ = ‖Y a‖ := by
  have hc : ContinuousOn (fun s => ‖Y s‖ ^ 2) (Icc a b) := hY.cont.norm.pow 2
  have hconst := constant_of_has_deriv_right_zero hc fun t ht => by
    simpa [hF t ht] using hY.dlra_hasDerivWithinAt_norm_sq ht (hP t ht) (hYP t ht)
  intro t ht
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hconst t ht)

/-- **Lyapunov bound** for the DLRA flow: if `⟪F(t, Y), Y⟫ ≤ μ ‖Y‖² + β` and `P(t) Y = Y` along
the trajectory, then `‖Y t‖² ≤ gronwallBound ‖Y a‖² (2μ) (2β) (t - a)`.  The key step is
`⟪Y, P(t) F⟫ = ⟪Y, F⟫` (arXiv 2606.15843, proof of Theorem 4.4). -/
theorem dlra_norm_sq_le_gronwallBound (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hYP : ∀ t ∈ Ico a b, P t (Y t) = Y t) {μ β : ℝ}
    (hF : ∀ t ∈ Ico a b, ⟪F t (Y t), Y t⟫ ≤ μ * ‖Y t‖ ^ 2 + β) :
    ∀ t ∈ Icc a b, ‖Y t‖ ^ 2 ≤ gronwallBound (‖Y a‖ ^ 2) (2 * μ) (2 * β) (t - a) :=
  le_gronwallBound_of_liminf_deriv_right_le (f := fun s => ‖Y s‖ ^ 2)
    (f' := fun t => 2 * ⟪F t (Y t), Y t⟫) (hY.cont.norm.pow 2)
    (fun t ht _ hr =>
      (hY.dlra_hasDerivWithinAt_norm_sq ht (hP t ht) (hYP t ht)).liminf_right_slope_le hr)
    le_rfl (fun t ht => by nlinarith [hF t ht])

/-- **Exponential norm bound**: if `⟪F(t, Y), Y⟫ ≤ μ ‖Y‖²` and `P(t) Y = Y` along the trajectory,
then `‖Y t‖ ≤ e^{μ(t-a)} ‖Y a‖`. -/
theorem dlra_norm_le_exp (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hYP : ∀ t ∈ Ico a b, P t (Y t) = Y t) {μ : ℝ}
    (hF : ∀ t ∈ Ico a b, ⟪F t (Y t), Y t⟫ ≤ μ * ‖Y t‖ ^ 2) :
    ∀ t ∈ Icc a b, ‖Y t‖ ≤ Real.exp (μ * (t - a)) * ‖Y a‖ := by
  intro t ht
  have h := hY.dlra_norm_sq_le_gronwallBound hP hYP (μ := μ) (β := 0)
    (fun s hs => by simpa using hF s hs) t ht
  rw [mul_zero, gronwallBound_ε0] at h
  have he : Real.exp (2 * μ * (t - a)) = Real.exp (μ * (t - a)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [he, ← mul_pow, mul_comm] at h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- **Norm dissipation** of the DLRA flow: if `⟪F(t, Y), Y⟫ ≤ 0` and `P(t) Y = Y` along the
trajectory, then `‖Y t‖ ≤ ‖Y a‖`. -/
theorem dlra_norm_le (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hYP : ∀ t ∈ Ico a b, P t (Y t) = Y t)
    (hF : ∀ t ∈ Ico a b, ⟪F t (Y t), Y t⟫ ≤ 0) : ∀ t ∈ Icc a b, ‖Y t‖ ≤ ‖Y a‖ := by
  intro t ht
  have h := hY.dlra_norm_le_exp hP hYP (μ := 0) (fun s hs => by simpa using hF s hs) t ht
  simpa using h

/-- **Uniform-in-time Lyapunov bound** (deterministic analogue of arXiv 2606.15843,
Theorem 4.4): if `⟪F(t, Y), Y⟫ ≤ μ ‖Y‖² + β` with `μ < 0 ≤ β` and `P(t) Y = Y` along the
trajectory, then `‖Y t‖² ≤ e^{2μ(t-a)} ‖Y a‖² + β / (-μ)` for all `t ∈ [a, b]`. -/
theorem dlra_norm_sq_le_of_neg (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hYP : ∀ t ∈ Ico a b, P t (Y t) = Y t) {μ β : ℝ}
    (hμ : μ < 0) (hβ : 0 ≤ β) (hF : ∀ t ∈ Ico a b, ⟪F t (Y t), Y t⟫ ≤ μ * ‖Y t‖ ^ 2 + β) :
    ∀ t ∈ Icc a b, ‖Y t‖ ^ 2 ≤ Real.exp (2 * μ * (t - a)) * ‖Y a‖ ^ 2 + β / (-μ) := by
  intro t ht
  have h := (hY.dlra_norm_sq_le_gronwallBound hP hYP hF t ht).trans
    (gronwallBound_le_of_neg (by linarith : 2 * μ < 0) (by linarith : 0 ≤ 2 * β))
  have he : 2 * β / -(2 * μ) = β / -μ := by
    rw [neg_mul_eq_mul_neg, mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  rw [he] at h
  linarith [mul_comm (‖Y a‖ ^ 2) (Real.exp (2 * μ * (t - a)))]

/-- **Conservation of linear invariants** by the DLRA flow: if `c` lies in the tangent space
along the trajectory (`P(t) c = c`, e.g. bases augmented by the conserved directions as in
Einkemmer–Joseph and arXiv 2206.09374) and `⟪c, F(t, Y)⟫ = 0`, then `⟪c, Y t⟫` is constant. -/
theorem dlra_inner_const (hY : ODESolution (fun t x => P t (F t x)) Y a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) {c : E} (hc : ∀ t ∈ Ico a b, P t c = c)
    (hF : ∀ t ∈ Ico a b, ⟪c, F t (Y t)⟫ = 0) : ∀ t ∈ Icc a b, ⟪c, Y t⟫ = ⟪c, Y a⟫ := by
  refine constant_of_has_deriv_right_zero (f := fun t => ⟪c, Y t⟫)
    ((innerSL ℝ c).continuous.comp_continuousOn hY.cont) fun t ht => ?_
  have h := (innerSL ℝ c).hasFDerivAt.comp_hasDerivWithinAt t (hY.deriv t ht)
  refine h.congr_deriv ?_
  simp only [innerSL_apply_apply]
  rw [(hP t ht).inner_apply_right_of_mem _ (hc t ht), hF t ht]

variable {ℰ : E → ℝ} {g : E → E}

/-- **Energy dissipation identity** for DLRA of a gradient flow `Ȧ = -∇ℰ(A)`:
along `Ẏ = P(t) (-∇ℰ(Y))` one has `d/dt ℰ(Y) = -‖P(t) ∇ℰ(Y)‖²`. -/
theorem dlra_hasDerivWithinAt_energy (hY : ODESolution (fun t x => P t (-g x)) Y a b)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {t : ℝ} (ht : t ∈ Ico a b)
    (hPt : IsOrthProj (P t)) :
    HasDerivWithinAt (ℰ ∘ Y) (-‖P t (g (Y t))‖ ^ 2) (Ici t) t := by
  refine (hasDerivWithinAt_energy_comp hℰ (hY.deriv t ht)).congr_deriv ?_
  rw [map_neg, inner_neg_right, real_inner_comm, hPt.inner_self_apply]

/-- **Energy decay** for DLRA of gradient flows: `ℰ(Y t) ≤ ℰ(Y a) - α² (t - a)` whenever
`α² ≤ ‖P(t) ∇ℰ(Y)‖²` along the trajectory; in particular `ℰ(Y t) ≤ ℰ(Y a)` (`α = 0`). -/
theorem dlra_energy_le (hY : ODESolution (fun t x => P t (-g x)) Y a b)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    {α : ℝ} (hα : ∀ t ∈ Ico a b, α ^ 2 ≤ ‖P t (g (Y t))‖ ^ 2) :
    ∀ t ∈ Icc a b, ℰ (Y t) ≤ ℰ (Y a) - α ^ 2 * (t - a) := by
  have hc : ContinuousOn (ℰ ∘ Y) (Icc a b) :=
    (continuous_of_hasFDerivAt_innerSL hℰ).comp_continuousOn hY.cont
  have hB : ∀ t, HasDerivWithinAt (fun s => ℰ (Y a) - α ^ 2 * (s - a)) (-(α ^ 2)) (Ici t) t :=
    fun t => by
      simpa using (((hasDerivWithinAt_id t (Ici t)).sub_const a).const_mul (α ^ 2)).const_sub
        (ℰ (Y a))
  have h := image_le_of_deriv_right_le_deriv_boundary hc
    (fun t ht => hY.dlra_hasDerivWithinAt_energy hℰ ht (hP t ht))
    (B := fun s => ℰ (Y a) - α ^ 2 * (s - a)) (by simp)
    (Continuous.continuousOn (by fun_prop)) (fun t _ => hB t)
    fun t ht => by simpa using hα t ht
  exact fun t ht => h ht

end ODESolution

end Norm

/-! ### Quasi-optimality -/

section QuasiOptimal

/-! #### Grönwall's inequality with a time-dependent source term -/

/-- `gronwallIntegralBound` solves `u' = K u + η`. -/
lemma hasDerivAt_gronwallIntegralBound (δ K : ℝ) {η : ℝ → ℝ} (hη : Continuous η) (a x : ℝ) :
    HasDerivAt (gronwallIntegralBound δ K η a) (K * gronwallIntegralBound δ K η a x + η x) x := by
  have hc : Continuous fun s => Real.exp (-(K * (s - a))) * η s := by fun_prop
  have h1 : HasDerivAt (fun x => Real.exp (K * (x - a))) (Real.exp (K * (x - a)) * K) x := by
    have := ((hasDerivAt_id x).sub_const a).const_mul K
    simpa using this.exp
  have h2 := (hc.integral_hasStrictDerivAt a x).hasDerivAt
  have h3 := h1.mul (h2.const_add δ)
  have he : Real.exp (K * (x - a)) * Real.exp (-(K * (x - a))) = 1 := by
    rw [← Real.exp_add]; simp
  unfold gronwallIntegralBound
  convert h3 using 1
  linear_combination (-η x) * he

/-- **Grönwall's inequality with a time-dependent source.**  If `f` has right derivatives `f'` on
`[a, b)` with `‖f'(x)‖ ≤ K ‖f(x)‖ + η(x)` for a continuous `η`, and `‖f a‖ ≤ δ`, then
`‖f x‖ ≤ e^{K(x-a)} (δ + ∫ₐˣ e^{-K(s-a)} η(s) ds)` on `[a, b]` (any real `K`). -/
theorem norm_le_gronwallIntegralBound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {δ K a b : ℝ} {η : ℝ → ℝ}
    (hη : Continuous η) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : ‖f a‖ ≤ δ) (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + η x) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallIntegralBound δ K η a x := by
  have H : ∀ x ∈ Icc a b, ∀ ε > 0,
      ‖f x‖ ≤ gronwallIntegralBound δ K η a x + ε * gronwallBound 0 K 1 (x - a) := by
    intro x hx ε hε
    refine image_le_of_liminf_slope_right_lt_deriv_boundary (f := fun t => ‖f t‖)
      (f' := fun t => K * ‖f t‖ + η t) (continuous_norm.comp_continuousOn hf) ?_
      (B := fun t => gronwallIntegralBound δ K η a t + ε * gronwallBound 0 K 1 (t - a))
      (B' := fun t => K * (gronwallIntegralBound δ K η a t + ε * gronwallBound 0 K 1 (t - a)) +
        η t + ε) ?_ ?_ ?_ hx
    · intro t ht r hr
      exact (hf' t ht).liminf_right_slope_norm_le ((bound t ht).trans_lt hr)
    · simp [gronwallIntegralBound, gronwallBound_x0, ha]
    · intro t
      have h1 := hasDerivAt_gronwallIntegralBound δ K hη a t
      have h2 := (hasDerivAt_gronwallBound_shift 0 K 1 t a).const_mul ε
      convert h1.add h2 using 1
      ring
    · intro t _ heq
      rw [heq]
      linarith
  intro x hx
  have hlim : Tendsto (fun ε => gronwallIntegralBound δ K η a x + ε * gronwallBound 0 K 1 (x - a))
      (𝓝[>] 0) (𝓝 (gronwallIntegralBound δ K η a x)) := by
    have : Tendsto
        (fun ε : ℝ => gronwallIntegralBound δ K η a x + ε * gronwallBound 0 K 1 (x - a))
        (𝓝 0) (𝓝 (gronwallIntegralBound δ K η a x + 0 * gronwallBound 0 K 1 (x - a))) :=
      tendsto_const_nhds.add (tendsto_id.mul_const _)
    simpa using this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => H x hx ε hε)

/-- For `K ≥ 0` and a nonnegative source: `gronwallIntegralBound δ K η a x ≤
e^{K(x-a)} (δ + ∫ₐˣ η)`. -/
lemma gronwallIntegralBound_le {δ K a x : ℝ} {η : ℝ → ℝ} (hη : Continuous η) (hK : 0 ≤ K)
    (hax : a ≤ x) (hη0 : ∀ s ∈ Icc a x, 0 ≤ η s) :
    gronwallIntegralBound δ K η a x ≤ Real.exp (K * (x - a)) * (δ + ∫ s in a..x, η s) := by
  unfold gronwallIntegralBound
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.exp_pos _).le
  have hc : Continuous fun s => Real.exp (-(K * (s - a))) * η s := by fun_prop
  refine intervalIntegral.integral_mono_on hax (hc.intervalIntegrable _ _)
    (hη.intervalIntegrable _ _) fun s hs => ?_
  have he : Real.exp (-(K * (s - a))) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hK (sub_nonneg.2 hs.1)))
  exact mul_le_of_le_one_left (hη0 s hs) he

/-! #### Comparison with an arbitrary curve -/

/-- Pointwise splitting of the velocity difference `P F(Y) - X'` used in the comparison
theorems. -/
private lemma dlra_comparison_deriv_bound {Q : E →L[ℝ] E} (hQ : IsOrthProj Q) {fy fx x' y x : E}
    {L κ₁ κ₂ e₁ e₂ : ℝ} (hL : ‖fy - fx‖ ≤ L * ‖y - x‖)
    (h₁ : ‖Q (fx - x')‖ ≤ κ₁ * ‖y - x‖ + e₁) (h₂ : ‖(1 - Q) x'‖ ≤ κ₂ * ‖y - x‖ + e₂) :
    ‖Q fy - x'‖ ≤ (L + κ₁ + κ₂) * ‖y - x‖ + (e₁ + e₂) := by
  have hsplit : Q fy - x' = Q (fy - fx) + Q (fx - x') - (1 - Q) x' := by
    simp only [map_sub, sub_apply, one_apply_eq_self]
    abel
  rw [hsplit]
  calc ‖Q (fy - fx) + Q (fx - x') - (1 - Q) x'‖
      ≤ ‖Q (fy - fx)‖ + ‖Q (fx - x')‖ + ‖(1 - Q) x'‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ L * ‖y - x‖ + (κ₁ * ‖y - x‖ + e₁) + (κ₂ * ‖y - x‖ + e₂) :=
        add_le_add (add_le_add ((hQ.norm_le _).trans hL) h₁) h₂
    _ = (L + κ₁ + κ₂) * ‖y - x‖ + (e₁ + e₂) := by ring

/-- Tangential defect of the best approximation (pointwise, Koch–Lubich-type hypotheses). -/
private lemma kl_tangential_bound {Q QX : E →L[ℝ] E} (hQ : IsOrthProj Q) (hQX : IsOrthProj QX)
    {fx fa x' : E} {r e L γ μ c : ℝ} (hγr : 0 ≤ γ * r) (hfx : ‖fx - fa‖ ≤ L * e)
    (hcurv : ∀ z, ‖(Q - QX) z‖ ≤ γ * r * ‖z‖) (hbest : ‖x' - QX fa‖ ≤ c * e)
    (hμ : ‖fa‖ ≤ μ) : ‖Q (fx - x')‖ ≤ γ * μ * r + (L + c) * e := by
  have hidem : QX ((1 - QX) fa) = 0 := by simp [hQX.idem]
  have hmid : (Q - QX) ((1 - QX) fa) = Q (fa - QX fa) := by
    rw [sub_apply, hidem, sub_zero, sub_apply, one_apply_eq_self]
  have hsplit : Q (fx - x') = Q (fx - fa) + (Q - QX) ((1 - QX) fa) + Q (QX fa - x') := by
    rw [hmid]
    simp only [map_sub]
    abel
  have hA2 : ‖(Q - QX) ((1 - QX) fa)‖ ≤ γ * μ * r :=
    calc ‖(Q - QX) ((1 - QX) fa)‖ ≤ γ * r * ‖(1 - QX) fa‖ := hcurv _
      _ ≤ γ * r * μ :=
          mul_le_mul_of_nonneg_left ((hQX.compl.norm_le fa).trans hμ) hγr
      _ = γ * μ * r := by ring
  have hA3 : ‖Q (QX fa - x')‖ ≤ c * e := by
    refine (hQ.norm_le _).trans ?_
    rw [norm_sub_rev]
    exact hbest
  rw [hsplit]
  calc ‖Q (fx - fa) + (Q - QX) ((1 - QX) fa) + Q (QX fa - x')‖
      ≤ ‖Q (fx - fa)‖ + ‖(Q - QX) ((1 - QX) fa)‖ + ‖Q (QX fa - x')‖ := norm_add₃_le
    _ ≤ L * e + γ * μ * r + c * e :=
        add_le_add (add_le_add ((hQ.norm_le _).trans hfx) hA2) hA3
    _ = γ * μ * r + (L + c) * e := by ring

/-- Normal component of the velocity of the best approximation (pointwise). -/
private lemma kl_normal_bound {Q QX : E →L[ℝ] E} {x' : E} {r γ μ' : ℝ} (hx' : QX x' = x')
    (hγr : 0 ≤ γ * r) (hcurv : ∀ z, ‖(Q - QX) z‖ ≤ γ * r * ‖z‖) (hμ' : ‖x'‖ ≤ μ') :
    ‖(1 - Q) x'‖ ≤ γ * μ' * r + 0 := by
  have he : (1 - Q) x' = -((Q - QX) x') := by
    simp only [sub_apply, one_apply_eq_self, hx']
    abel
  rw [he, norm_neg, add_zero]
  calc ‖(Q - QX) x'‖ ≤ γ * r * ‖x'‖ := hcurv _
    _ ≤ γ * r * μ' := mul_le_mul_of_nonneg_left hμ' hγr
    _ = γ * μ' * r := by ring

variable {P : ℝ → E →L[ℝ] E} {F : ℝ → E → E} {Y : ℝ → E} {a b : ℝ}

namespace ODESolution

/-- **Comparison with an arbitrary curve.**  Let `Y` solve the DLRA equation `Ẏ = P(t) F(t, Y)`
with `F` `L`-Lipschitz, and let `X` be any curve with right derivative `X'` on `[a, b)` (e.g. the
best approximation of the exact solution on the low-rank manifold).  Assume the curvature-free
hypotheses

* `‖P(t) (F(t, X) - X')‖ ≤ κ₁ ‖Y - X‖ + η₁` (tangential defect of `X` in the DLRA equation),
* `‖(1 - P(t)) X'‖ ≤ κ₂ ‖Y - X‖ + η₂` (normal component of `X'` w.r.t. the projector along `Y`;
  it vanishes when `X = Y` and is a curvature term in general).

Then `‖Y t - X t‖ ≤ gronwallBound ‖Y a - X a‖ (L + κ₁ + κ₂) (η₁ + η₂) (t - a)`. -/
theorem dlra_norm_sub_le_of_comparison {L κ₁ κ₂ η₁ η₂ δ : ℝ} (hF : IsLipschitzField F L)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    {X X' : ℝ → E} (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (h₁ : ∀ t ∈ Ico a b, ‖P t (F t (X t) - X' t)‖ ≤ κ₁ * ‖Y t - X t‖ + η₁)
    (h₂ : ∀ t ∈ Ico a b, ‖(1 - P t) (X' t)‖ ≤ κ₂ * ‖Y t - X t‖ + η₂)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤ gronwallBound δ (L + κ₁ + κ₂) (η₁ + η₂) (t - a) :=
  norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => Y t - X t)
    (f' := fun t => P t (F t (Y t)) - X' t) (hY.cont.sub hXc)
    (fun t ht => (hY.deriv t ht).sub (hX t ht)) hδ fun t ht =>
      dlra_comparison_deriv_bound (hP t ht) (hF t _ _) (h₁ t ht) (h₂ t ht)

/-- **Comparison with an arbitrary curve, integral form.**  As
`ODESolution.dlra_norm_sub_le_of_comparison`, with time-dependent continuous sources `η₁, η₂`:
`‖Y t - X t‖ ≤ e^{K(t-a)} (‖Y a - X a‖ + ∫ₐᵗ e^{-K(s-a)} (η₁ + η₂)(s) ds)`,
`K = L + κ₁ + κ₂`. -/
theorem dlra_norm_sub_le_of_comparison_integral {L κ₁ κ₂ δ : ℝ} {η₁ η₂ : ℝ → ℝ}
    (hη₁ : Continuous η₁) (hη₂ : Continuous η₂) (hF : IsLipschitzField F L)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    {X X' : ℝ → E} (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (h₁ : ∀ t ∈ Ico a b, ‖P t (F t (X t) - X' t)‖ ≤ κ₁ * ‖Y t - X t‖ + η₁ t)
    (h₂ : ∀ t ∈ Ico a b, ‖(1 - P t) (X' t)‖ ≤ κ₂ * ‖Y t - X t‖ + η₂ t)
    (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - X t‖ ≤
      gronwallIntegralBound δ (L + κ₁ + κ₂) (fun s => η₁ s + η₂ s) a t :=
  norm_le_gronwallIntegralBound (f := fun t => Y t - X t)
    (f' := fun t => P t (F t (Y t)) - X' t) (hη₁.add hη₂) (hY.cont.sub hXc)
    (fun t ht => (hY.deriv t ht).sub (hX t ht)) hδ fun t ht =>
      dlra_comparison_deriv_bound (hP t ht) (hF t _ _) (h₁ t ht) (h₂ t ht)

/-- **Quasi-optimality of DLRA** (abstract form of Koch–Lubich, SIAM J. Matrix Anal. Appl. 29
(2007), Theorem 5.1).  Let `F` be `L`-Lipschitz, `Y` the DLRA solution with projectors
`P(t) = P(Y(t))`, `A` the exact solution (so that `F(t, A t) = Ȧ(t)`), and `X` a differentiable
curve (the best approximation of `A` on the low-rank manifold) with tangent projectors `P_X(t)`.
Assume

* `X' ∈ range P_X(t)` (`X` moves on the manifold);
* the curvature bound `‖(P(t) - P_X(t)) z‖ ≤ γ ‖Y - X‖ ‖z‖` (Koch–Lubich Lemma 4.2,
  `γ ~ 1/ρ` with `ρ` a lower bound of the smallest nonzero singular value);
* the best-approximation property `‖X' - P_X(t) Ȧ‖ ≤ c ‖A - X‖` (the derivative of the best
  approximation differs from the projected derivative by a curvature term);
* `‖Ȧ‖ ≤ μ`, `‖X'‖ ≤ μ'` and `‖A - X‖ ≤ d` on `[a, b]`.

Then `‖Y t - A t‖ ≤ d + gronwallBound ‖Y a - X a‖ (L + γ (μ + μ')) ((L + c) d) (t - a)`: on
bounded time intervals the DLRA error is bounded by a constant times the best-approximation
error `d` (plus the propagated initial deviation).

The proof never uses that `A` solves the full equation: `F(t, A t)` only enters through the
hypotheses `hbest` and `hμ`.  So `A` may be any curve. -/
theorem dlra_quasiOptimal {A X X' : ℝ → E} {PX : ℝ → E →L[ℝ] E} {L γ μ μ' c d δ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hPX : ∀ t ∈ Ico a b, IsOrthProj (PX t)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXtan : ∀ t ∈ Ico a b, PX t (X' t) = X' t) (hγ : 0 ≤ γ)
    (hcurv : ∀ t ∈ Ico a b, ∀ z, ‖(P t - PX t) z‖ ≤ γ * ‖Y t - X t‖ * ‖z‖)
    (hc : 0 ≤ c) (hbest : ∀ t ∈ Ico a b, ‖X' t - PX t (F t (A t))‖ ≤ c * ‖A t - X t‖)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hμ' : ∀ t ∈ Ico a b, ‖X' t‖ ≤ μ')
    (hd : ∀ t ∈ Icc a b, ‖A t - X t‖ ≤ d) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b,
      ‖Y t - A t‖ ≤ d + gronwallBound δ (L + γ * (μ + μ')) ((L + c) * d) (t - a) := by
  have hγe : ∀ t, 0 ≤ γ * ‖Y t - X t‖ := fun t => mul_nonneg hγ (norm_nonneg _)
  have h₁ : ∀ t ∈ Ico a b, ‖P t (F t (X t) - X' t)‖ ≤ γ * μ * ‖Y t - X t‖ + (L + c) * d :=
    fun t ht => (kl_tangential_bound (hP t ht) (hPX t ht) (hγe t)
      ((hF t _ _).trans_eq (by rw [norm_sub_rev])) (hcurv t ht) (hbest t ht) (hμ t ht)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hd t (Ico_subset_Icc_self ht))
        (add_nonneg hL hc)))
  have h₂ : ∀ t ∈ Ico a b, ‖(1 - P t) (X' t)‖ ≤ γ * μ' * ‖Y t - X t‖ + 0 := fun t ht =>
    kl_normal_bound (hXtan t ht) (hγe t) (hcurv t ht) (hμ' t ht)
  intro t ht
  have hYX := dlra_norm_sub_le_of_comparison hF hY hP hXc hX h₁ h₂ hδ t ht
  have hK : L + γ * μ + γ * μ' = L + γ * (μ + μ') := by ring
  rw [hK, add_zero] at hYX
  calc ‖Y t - A t‖ = ‖(Y t - X t) + (X t - A t)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖Y t - X t‖ + ‖X t - A t‖ := norm_add_le _ _
    _ ≤ gronwallBound δ (L + γ * (μ + μ')) ((L + c) * d) (t - a) + d := by
        rw [norm_sub_rev (X t)]
        exact add_le_add hYX (hd t ht)
    _ = _ := by ring

/-- Explicit form of quasi-optimality when the DLRA starts at the best approximation
(`Y a = X a`): `‖Y t - A t‖ ≤ (1 + (L + c) (t - a) e^{K (t-a)}) d` with
`K = L + γ (μ + μ')`, i.e. the DLRA error is at most a time-dependent constant times the
best-approximation error `d`. -/
theorem dlra_quasiOptimal_explicit {A X X' : ℝ → E} {PX : ℝ → E →L[ℝ] E} {L γ μ μ' c d : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hPX : ∀ t ∈ Ico a b, IsOrthProj (PX t)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXtan : ∀ t ∈ Ico a b, PX t (X' t) = X' t) (hγ : 0 ≤ γ)
    (hcurv : ∀ t ∈ Ico a b, ∀ z, ‖(P t - PX t) z‖ ≤ γ * ‖Y t - X t‖ * ‖z‖)
    (hc : 0 ≤ c) (hbest : ∀ t ∈ Ico a b, ‖X' t - PX t (F t (A t))‖ ≤ c * ‖A t - X t‖)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hμ' : ∀ t ∈ Ico a b, ‖X' t‖ ≤ μ')
    (hd : ∀ t ∈ Icc a b, ‖A t - X t‖ ≤ d) (h0 : Y a = X a) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤
      (1 + (L + c) * (t - a) * Real.exp ((L + γ * (μ + μ')) * (t - a))) * d := by
  intro t ht
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd a (left_mem_Icc.2 (ht.1.trans ht.2)))
  rcases eq_or_lt_of_le ht.1 with hat | hat
  · subst hat
    rw [sub_self, mul_zero, zero_mul, add_zero, one_mul, h0, norm_sub_rev]
    exact hd _ ht
  have hab : a < b := hat.trans_le ht.2
  have hμ0 : 0 ≤ μ + μ' := add_nonneg ((norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩))
    ((norm_nonneg _).trans (hμ' a ⟨le_rfl, hab⟩))
  have h := dlra_quasiOptimal hF hL hY hP hPX hXc hX hXtan hγ hcurv hc hbest hμ hμ' hd
    (δ := 0) (by rw [h0, sub_self, norm_zero]) t ht
  have hK : 0 ≤ L + γ * (μ + μ') := add_nonneg hL (mul_nonneg hγ hμ0)
  have hg := gronwallBound_le_exp_mul (δ := 0) (x := t - a) hK
    (mul_nonneg (add_nonneg hL hc) hd0)
  calc ‖Y t - A t‖ ≤ d + gronwallBound 0 (L + γ * (μ + μ')) ((L + c) * d) (t - a) := h
    _ ≤ d + Real.exp ((L + γ * (μ + μ')) * (t - a)) * (0 + (L + c) * d * (t - a)) := by
        gcongr
    _ = _ := by ring

/-- **Quasi-optimality, integral form** (Koch–Lubich, SIAM J. Matrix Anal. Appl. 29 (2007),
Theorem 5.1: `‖Y(t) - X(t)‖ ≤ 2β e^{βt} ∫₀ᵗ ‖A(s) - X(s)‖ ds`).  Under the hypotheses of
`ODESolution.dlra_quasiOptimal`, with the best-approximation error majorised by a continuous
function, `‖A t - X t‖ ≤ η t` on `[a, b]` (e.g. `η = ‖A - X‖` when `A, X` are continuous):

    ‖Y t - A t‖ ≤ η t + e^{K(t-a)} (‖Y a - X a‖ + (L + c) ∫ₐᵗ η(s) ds),   K = L + γ (μ + μ').

With `Y a = X a` and `F(t, Y) = Ȧ(t)` (`L = 0`) this is Koch–Lubich's estimate with the constant
`c` in place of `2β`. -/
theorem dlra_quasiOptimal_integral {A X X' : ℝ → E} {PX : ℝ → E →L[ℝ] E} {η : ℝ → ℝ}
    {L γ μ μ' c δ : ℝ} (hη : Continuous η)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hY : ODESolution (fun t x => P t (F t x)) Y a b) (hP : ∀ t ∈ Ico a b, IsOrthProj (P t))
    (hPX : ∀ t ∈ Ico a b, IsOrthProj (PX t)) (hXc : ContinuousOn X (Icc a b))
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (X' t) (Ici t) t)
    (hXtan : ∀ t ∈ Ico a b, PX t (X' t) = X' t) (hγ : 0 ≤ γ)
    (hcurv : ∀ t ∈ Ico a b, ∀ z, ‖(P t - PX t) z‖ ≤ γ * ‖Y t - X t‖ * ‖z‖)
    (hc : 0 ≤ c) (hbest : ∀ t ∈ Ico a b, ‖X' t - PX t (F t (A t))‖ ≤ c * ‖A t - X t‖)
    (hμ : ∀ t ∈ Ico a b, ‖F t (A t)‖ ≤ μ) (hμ' : ∀ t ∈ Ico a b, ‖X' t‖ ≤ μ')
    (hd : ∀ t ∈ Icc a b, ‖A t - X t‖ ≤ η t) (hδ : ‖Y a - X a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤
      η t + Real.exp ((L + γ * (μ + μ')) * (t - a)) * (δ + (L + c) * ∫ s in a..t, η s) := by
  have hγe : ∀ t, 0 ≤ γ * ‖Y t - X t‖ := fun t => mul_nonneg hγ (norm_nonneg _)
  have h₁ : ∀ t ∈ Ico a b,
      ‖P t (F t (X t) - X' t)‖ ≤ γ * μ * ‖Y t - X t‖ + (L + c) * η t :=
    fun t ht => (kl_tangential_bound (hP t ht) (hPX t ht) (hγe t)
      ((hF t _ _).trans_eq (by rw [norm_sub_rev])) (hcurv t ht) (hbest t ht) (hμ t ht)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hd t (Ico_subset_Icc_self ht))
        (add_nonneg hL hc)))
  have h₂ : ∀ t ∈ Ico a b, ‖(1 - P t) (X' t)‖ ≤ γ * μ' * ‖Y t - X t‖ + 0 := fun t ht =>
    kl_normal_bound (hXtan t ht) (hγe t) (hcurv t ht) (hμ' t ht)
  intro t ht
  have hYX := dlra_norm_sub_le_of_comparison_integral (η₁ := fun s => (L + c) * η s)
    (η₂ := fun _ => 0) (continuous_const.mul hη) continuous_const hF hY hP hXc hX h₁ h₂ hδ t ht
  have hK : L + γ * μ + γ * μ' = L + γ * (μ + μ') := by ring
  rw [hK] at hYX
  have hYX' : ‖Y t - X t‖ ≤
      Real.exp ((L + γ * (μ + μ')) * (t - a)) * (δ + (L + c) * ∫ s in a..t, η s) := by
    rcases eq_or_lt_of_le ht.1 with hat | hat
    · subst hat
      simpa [gronwallIntegralBound] using hYX
    have hab : a < b := hat.trans_le ht.2
    have hμ0 : 0 ≤ μ + μ' := add_nonneg ((norm_nonneg _).trans (hμ a ⟨le_rfl, hab⟩))
      ((norm_nonneg _).trans (hμ' a ⟨le_rfl, hab⟩))
    refine hYX.trans ((gronwallIntegralBound_le ((continuous_const.mul hη).add continuous_const)
      (add_nonneg hL (mul_nonneg hγ hμ0)) ht.1 fun s hs => ?_).trans_eq ?_)
    · exact add_nonneg (mul_nonneg (add_nonneg hL hc)
        ((norm_nonneg _).trans (hd s ⟨hs.1, hs.2.trans ht.2⟩))) le_rfl
    · simp only [Pi.add_apply, Pi.mul_apply, add_zero, intervalIntegral.integral_const_mul]
  calc ‖Y t - A t‖ = ‖(Y t - X t) + (X t - A t)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖Y t - X t‖ + ‖X t - A t‖ := norm_add_le _ _
    _ ≤ _ + η t := by
        rw [norm_sub_rev (X t)]
        exact add_le_add hYX' (hd t ht)
    _ = _ := by ring

end ODESolution

end QuasiOptimal

/-! ### Stability with respect to the data (curvature estimate) -/

section Stability

/-- The normal part of a vector field only sees the normal part of the error:
`|⟪(1 - Q) f, e⟫| ≤ α r` when `‖(1 - Q) f‖ ≤ α` and `‖(1 - Q) e‖ ≤ r`. -/
private lemma abs_inner_normal_le {Q : E →L[ℝ] E} (hQ : IsOrthProj Q) {f e : E} {α r : ℝ}
    (hf : ‖(1 - Q) f‖ ≤ α) (he : ‖(1 - Q) e‖ ≤ r) : |⟪(1 - Q) f, e⟫| ≤ α * r := by
  rw [← hQ.compl.inner_comp f e]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul hf he (norm_nonneg _) ((norm_nonneg _).trans hf))

/-- Pointwise energy estimate for the difference of two DLRA velocities
`P F₁(u) - Q F₂(v)` (proof of Bachmayr–Eisenmann–Uschmajew, arXiv 2308.16720, Theorem 2.5). -/
private lemma inner_dlra_sub_le {P Q : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    {f₁ f₂ e : E} {ℓ η κ α β : ℝ} (hF : ⟪f₁ - f₂, e⟫ ≤ ℓ * ‖e‖ ^ 2 + η * ‖e‖)
    (hcP : ‖(1 - P) e‖ ≤ κ * ‖e‖ ^ 2) (hcQ : ‖(1 - Q) e‖ ≤ κ * ‖e‖ ^ 2)
    (hα : ‖(1 - P) f₁‖ ≤ α) (hβ : ‖(1 - Q) f₂‖ ≤ β) :
    ⟪e, P f₁ - Q f₂⟫ ≤ (ℓ + κ * (α + β)) * ‖e‖ ^ 2 + η * ‖e‖ := by
  have hsplit : P f₁ - Q f₂ = (f₁ - f₂) - (1 - P) f₁ + (1 - Q) f₂ := by
    simp only [sub_apply, one_apply_eq_self]
    abel
  have h1 := abs_inner_normal_le hP hα hcP
  have h2 := abs_inner_normal_le hQ hβ hcQ
  rw [hsplit, real_inner_comm, inner_add_left, inner_sub_left]
  have h1' := neg_abs_le ⟪(1 - P) f₁, e⟫
  have h2' := le_abs_self ⟪(1 - Q) f₂, e⟫
  nlinarith

/-- Young's inequality in the form `2 η x ≤ ε x² + η² / ε` (`ε > 0`). -/
private lemma two_mul_le_young {η x ε : ℝ} (hε : 0 < ε) :
    2 * η * x ≤ ε * x ^ 2 + η ^ 2 / ε := by
  have h : ε * x ^ 2 + η ^ 2 / ε - 2 * η * x = (ε * x - η) ^ 2 / ε := by
    field_simp
    ring
  have h0 : 0 ≤ (ε * x - η) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  linarith

namespace ODESolution

variable {P Q : ℝ → E →L[ℝ] E} {F₁ F₂ : ℝ → E → E} {u v : ℝ → E} {a b : ℝ}

/-- The squared distance of two DLRA trajectories `u' = P(t) F₁(t, u)`, `v' = Q(t) F₂(t, v)` has
right derivative `2 ⟪u - v, P F₁(u) - Q F₂(v)⟫`. -/
private lemma hasDerivWithinAt_norm_sub_sq
    (hu : ODESolution (fun t x => P t (F₁ t x)) u a b)
    (hv : ODESolution (fun t x => Q t (F₂ t x)) v a b) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun s => ‖u s - v s‖ ^ 2)
      (2 * ⟪u t - v t, P t (F₁ t (u t)) - Q t (F₂ t (v t))⟫) (Ici t) t :=
  ((hu.deriv t ht).sub (hv.deriv t ht)).norm_sq

/-- **Stability of DLRA with respect to the data** (abstract form of Bachmayr–Eisenmann–
Uschmajew, arXiv 2308.16720, Theorem 2.5, for parabolic problems on low-rank tensor manifolds).
Let `u' = P(t) F₁(t, u)` and `v' = Q(t) F₂(t, v)` be two DLRA trajectories with orthogonal
projector families `P(t) = P(u(t))`, `Q(t) = P(v(t))` (tangent projectors at `u`, `v`).  Assume
along the trajectories

* the one-sided bound `⟪F₁(t, u) - F₂(t, v), u - v⟫ ≤ ℓ ‖u - v‖² + η ‖u - v‖` (for
  `F₁ = f - 𝒜 u`, `F₂ = g - 𝒜 v` with coercive `𝒜`: `ℓ ≤ 0` and `η = ‖f - g‖`);
* the curvature estimate `‖(1 - P(t)) (u - v)‖ ≤ κ ‖u - v‖²`, `‖(1 - Q(t)) (u - v)‖ ≤ κ ‖u - v‖²`
  (Assumption A2 of arXiv 2308.16720, valid on low-rank manifolds away from lower rank);
* the normal components `‖(1 - P(t)) F₁(t, u)‖ ≤ α`, `‖(1 - Q(t)) F₂(t, v)‖ ≤ β`.

Then for every `ε > 0`, with `K = ℓ + κ (α + β)`,

    ‖u t - v t‖² ≤ gronwallBound ‖u a - v a‖² (2K + ε) (η² / ε) (t - a).

The paper's constant `Λ(t) = 2κ ∫₀ᵗ (‖u'‖ + ‖v'‖ + …)` is replaced here by the constant
`2κ (α + β) (t - a)` (the integrand in the paper bounds the normal components `α, β`); the
one-sided constant `ℓ` is kept general (the paper drops `⟪𝒜 (u - v), u - v⟫` by coercivity,
i.e. `ℓ = 0`). -/
theorem dlra_norm_sub_sq_le_of_curvature {ℓ η κ α β ε : ℝ}
    (hu : ODESolution (fun t x => P t (F₁ t x)) u a b)
    (hv : ODESolution (fun t x => Q t (F₂ t x)) v a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hQ : ∀ t ∈ Ico a b, IsOrthProj (Q t))
    (hF : ∀ t ∈ Ico a b,
      ⟪F₁ t (u t) - F₂ t (v t), u t - v t⟫ ≤ ℓ * ‖u t - v t‖ ^ 2 + η * ‖u t - v t‖)
    (hcP : ∀ t ∈ Ico a b, ‖(1 - P t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hcQ : ∀ t ∈ Ico a b, ‖(1 - Q t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hα : ∀ t ∈ Ico a b, ‖(1 - P t) (F₁ t (u t))‖ ≤ α)
    (hβ : ∀ t ∈ Ico a b, ‖(1 - Q t) (F₂ t (v t))‖ ≤ β) (hε : 0 < ε) :
    ∀ t ∈ Icc a b, ‖u t - v t‖ ^ 2 ≤
      gronwallBound (‖u a - v a‖ ^ 2) (2 * (ℓ + κ * (α + β)) + ε) (η ^ 2 / ε) (t - a) :=
  le_gronwallBound_of_liminf_deriv_right_le (f := fun s => ‖u s - v s‖ ^ 2)
    (f' := fun t => 2 * ⟪u t - v t, P t (F₁ t (u t)) - Q t (F₂ t (v t))⟫)
    ((hu.cont.sub hv.cont).norm.pow 2)
    (fun t ht _ hr => (hasDerivWithinAt_norm_sub_sq hu hv ht).liminf_right_slope_le hr) le_rfl
    fun t ht => by
      have h := inner_dlra_sub_le (hP t ht) (hQ t ht) (hF t ht) (hcP t ht) (hcQ t ht) (hα t ht)
        (hβ t ht)
      have hy := two_mul_le_young (η := η) (x := ‖u t - v t‖) hε
      nlinarith

/-- Explicit form of `ODESolution.dlra_norm_sub_sq_le_of_curvature` in the shape of
arXiv 2308.16720, Theorem 2.5: if `2K + ε ≥ 0` then
`‖u t - v t‖² ≤ (‖u a - v a‖² + (t - a) η² / ε) e^{(2K + ε)(t - a)}`. -/
theorem dlra_norm_sub_sq_le_exp_of_curvature {ℓ η κ α β ε : ℝ}
    (hu : ODESolution (fun t x => P t (F₁ t x)) u a b)
    (hv : ODESolution (fun t x => Q t (F₂ t x)) v a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hQ : ∀ t ∈ Ico a b, IsOrthProj (Q t))
    (hF : ∀ t ∈ Ico a b,
      ⟪F₁ t (u t) - F₂ t (v t), u t - v t⟫ ≤ ℓ * ‖u t - v t‖ ^ 2 + η * ‖u t - v t‖)
    (hcP : ∀ t ∈ Ico a b, ‖(1 - P t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hcQ : ∀ t ∈ Ico a b, ‖(1 - Q t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hα : ∀ t ∈ Ico a b, ‖(1 - P t) (F₁ t (u t))‖ ≤ α)
    (hβ : ∀ t ∈ Ico a b, ‖(1 - Q t) (F₂ t (v t))‖ ≤ β) (hε : 0 < ε)
    (hK : 0 ≤ 2 * (ℓ + κ * (α + β)) + ε) :
    ∀ t ∈ Icc a b, ‖u t - v t‖ ^ 2 ≤
      (‖u a - v a‖ ^ 2 + (t - a) * (η ^ 2 / ε)) *
        Real.exp ((2 * (ℓ + κ * (α + β)) + ε) * (t - a)) := fun t ht => by
  have h := (dlra_norm_sub_sq_le_of_curvature hu hv hP hQ hF hcP hcQ hα hβ hε t ht).trans
    (gronwallBound_le_exp_mul hK (div_nonneg (sq_nonneg η) hε.le))
  linarith [mul_comm (Real.exp ((2 * (ℓ + κ * (α + β)) + ε) * (t - a)))
    (‖u a - v a‖ ^ 2 + (t - a) * (η ^ 2 / ε)), mul_comm (η ^ 2 / ε) (t - a)]

/-- **Stability with exact data** (`η = 0`): under the hypotheses of
`ODESolution.dlra_norm_sub_sq_le_of_curvature` with
`⟪F₁(t, u) - F₂(t, v), u - v⟫ ≤ ℓ ‖u - v‖²`,
`‖u t - v t‖ ≤ e^{(ℓ + κ (α + β))(t - a)} ‖u a - v a‖`. -/
theorem dlra_norm_sub_le_exp_of_curvature {ℓ κ α β : ℝ}
    (hu : ODESolution (fun t x => P t (F₁ t x)) u a b)
    (hv : ODESolution (fun t x => Q t (F₂ t x)) v a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hQ : ∀ t ∈ Ico a b, IsOrthProj (Q t))
    (hF : ∀ t ∈ Ico a b, ⟪F₁ t (u t) - F₂ t (v t), u t - v t⟫ ≤ ℓ * ‖u t - v t‖ ^ 2)
    (hcP : ∀ t ∈ Ico a b, ‖(1 - P t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hcQ : ∀ t ∈ Ico a b, ‖(1 - Q t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hα : ∀ t ∈ Ico a b, ‖(1 - P t) (F₁ t (u t))‖ ≤ α)
    (hβ : ∀ t ∈ Ico a b, ‖(1 - Q t) (F₂ t (v t))‖ ≤ β) :
    ∀ t ∈ Icc a b, ‖u t - v t‖ ≤ Real.exp ((ℓ + κ * (α + β)) * (t - a)) * ‖u a - v a‖ := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => ‖u s - v s‖ ^ 2)
    (f' := fun t => 2 * ⟪u t - v t, P t (F₁ t (u t)) - Q t (F₂ t (v t))⟫)
    (K := 2 * (ℓ + κ * (α + β))) (ε := 0)
    ((hu.cont.sub hv.cont).norm.pow 2)
    (fun t ht _ hr => (hasDerivWithinAt_norm_sub_sq hu hv ht).liminf_right_slope_le hr) le_rfl
    (fun t ht => by
      have h := inner_dlra_sub_le (η := 0) (hP t ht) (hQ t ht) (by simpa using hF t ht)
        (hcP t ht) (hcQ t ht) (hα t ht) (hβ t ht)
      simp only [zero_mul, add_zero] at h ⊢
      linarith) t ht
  rw [gronwallBound_ε0] at h
  have he : Real.exp (2 * (ℓ + κ * (α + β)) * (t - a)) =
      Real.exp ((ℓ + κ * (α + β)) * (t - a)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [he, ← mul_pow, mul_comm] at h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h

/-- **Uniqueness of DLRA trajectories through the curvature estimate**: two DLRA trajectories
of the same problem starting at the same point coincide, provided the curvature estimate and
bounded normal components hold along them (arXiv 2308.16720, uniqueness part of Theorem 2.2,
i.e. Theorem 2.5 with equal data). -/
theorem dlra_eqOn_of_curvature {ℓ κ α β : ℝ}
    (hu : ODESolution (fun t x => P t (F₁ t x)) u a b)
    (hv : ODESolution (fun t x => Q t (F₂ t x)) v a b)
    (hP : ∀ t ∈ Ico a b, IsOrthProj (P t)) (hQ : ∀ t ∈ Ico a b, IsOrthProj (Q t))
    (hF : ∀ t ∈ Ico a b, ⟪F₁ t (u t) - F₂ t (v t), u t - v t⟫ ≤ ℓ * ‖u t - v t‖ ^ 2)
    (hcP : ∀ t ∈ Ico a b, ‖(1 - P t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hcQ : ∀ t ∈ Ico a b, ‖(1 - Q t) (u t - v t)‖ ≤ κ * ‖u t - v t‖ ^ 2)
    (hα : ∀ t ∈ Ico a b, ‖(1 - P t) (F₁ t (u t))‖ ≤ α)
    (hβ : ∀ t ∈ Ico a b, ‖(1 - Q t) (F₂ t (v t))‖ ≤ β) (h0 : u a = v a) :
    EqOn u v (Icc a b) := fun t ht => by
  have h := dlra_norm_sub_le_exp_of_curvature hu hv hP hQ hF hcP hcQ hα hβ t ht
  rw [h0, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

end ODESolution

end Stability

/-! ### Consistency examples -/

section Examples

/-- Changing the vector field away from the trajectory does not affect `ODESolution`. -/
private lemma ODESolution.congr_field_dlra {f g : ℝ → E → E} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution f y a b) (h : ∀ t ∈ Ico a b, f t (y t) = g t (y t)) :
    ODESolution g y a b where
  cont := hy.cont
  deriv t ht := by
    rw [← h t ht]
    exact hy.deriv t ht

/-- Affine curves solve constant-field ODEs. -/
private lemma odeSolution_affine (x₀ w : E) (a b : ℝ) :
    ODESolution (fun _ _ => w) (fun t => x₀ + (t - a) • w) a b where
  cont := Continuous.continuousOn (by fun_prop)
  deriv t _ := by
    have h := (((hasDerivAt_id t).sub_const a).smul_const w).const_add x₀
    simpa using h.hasDerivWithinAt

/-- Relaxation curves `p + e^{-(t-a)} w` solve `y' = p - y`. -/
private lemma odeSolution_relax (p w : E) (a b : ℝ) :
    ODESolution (fun _ x => p - x) (fun t => p + Real.exp (-(t - a)) • w) a b where
  cont := Continuous.continuousOn (by fun_prop)
  deriv t _ := by
    have h1 : HasDerivAt (fun s => -(s - a)) (-1) t := ((hasDerivAt_id t).sub_const a).neg
    have h2 := (h1.exp.smul_const w).const_add p
    convert h2.hasDerivWithinAt using 1
    simp

variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

/-- The relaxation curve `Y t = P v + e^{-(t-a)} (x₀ - P v)`, `P = proj_K`, `x₀ ∈ K`, stays in
`K`. -/
private lemma relax_mem {v x₀ : E} (hx₀ : x₀ ∈ K) (a t : ℝ) :
    K.starProjection (K.starProjection v + Real.exp (-(t - a)) • (x₀ - K.starProjection v)) =
      K.starProjection v + Real.exp (-(t - a)) • (x₀ - K.starProjection v) := by
  have hP := isOrthProj_starProjection K
  rw [map_add, map_smul, map_sub, hP.idem, Submodule.starProjection_eq_self_iff.2 hx₀]

/-- The relaxation curve solves the DLRA equation `Y' = P (v - Y)` of `A' = v - A`. -/
private lemma relax_dlra {v x₀ : E} (hx₀ : x₀ ∈ K) (a b : ℝ) :
    ODESolution (fun t x => (fun _ => K.starProjection) t ((fun _ x => v - x) t x))
      (fun t => K.starProjection v + Real.exp (-(t - a)) • (x₀ - K.starProjection v)) a b :=
  (odeSolution_relax _ _ a b).congr_field_dlra fun t _ => by
    simp only [map_sub, relax_mem K hx₀ a t]

/-- **Consistency of the Lipschitz error bound** (non-trivial: `ε > 0` whenever `v ∉ K`).  For a
complete subspace `K` playing the role of the tangent space, the constant field `F(t, x) = v`,
the exact solution `A t = x₀ + (t - a) v` and the DLRA solution `Y t = x₀ + (t - a) P v`,
`P = proj_K`, satisfy all hypotheses of `ODESolution.dlra_norm_sub_le_gronwallBound` with `L = 0`,
`δ = 0` and `ε = ‖(1 - P) v‖`; the bound `‖Y t - A t‖ ≤ ε (t - a)` is attained. -/
example (v x₀ : E) (a b : ℝ) :
    ∀ t ∈ Icc a b, ‖(x₀ + (t - a) • K.starProjection v) - (x₀ + (t - a) • v)‖ ≤
      gronwallBound 0 0 ‖(1 - K.starProjection) v‖ (t - a) :=
  ODESolution.dlra_norm_sub_le_gronwallBound (P := fun _ => K.starProjection)
    (F := fun _ _ => v) (L := 0) (fun _ _ _ => by simp) le_rfl (odeSolution_affine x₀ v a b)
    (odeSolution_affine x₀ _ a b) (fun _ _ => le_rfl) (by simp)

/-- **Consistency of the uniform-in-time one-sided bound.**  For the dissipative field
`F(t, x) = v - x` (one-sided Lipschitz with `ℓ = -1`) with exact solution
`A t = v + e^{-(t-a)} (x₀ - v)` and DLRA solution `Y t = P v + e^{-(t-a)} (x₀ - P v)`
(`x₀ ∈ K`), `ODESolution.dlra_norm_sub_le_of_oneSided_neg` gives
`‖Y t - A t‖ ≤ ‖(1 - P) v‖` for all `t`; the bound is approached as `t → ∞`. -/
example (v x₀ : E) (hx₀ : x₀ ∈ K) (a b : ℝ) :
    ∀ t ∈ Icc a b,
      ‖(K.starProjection v + Real.exp (-(t - a)) • (x₀ - K.starProjection v)) -
        (v + Real.exp (-(t - a)) • (x₀ - v))‖ ≤ ‖(1 - K.starProjection) v‖ := by
  intro t ht
  have hF : IsOneSidedLipschitzField (fun _ (x : E) => v - x) (-1) := fun _ x y => by
    have h : v - x - (v - y) = -(x - y) := by abel
    rw [h, inner_neg_left, real_inner_self_eq_norm_sq]
    linarith
  have h := ODESolution.dlra_norm_sub_le_of_oneSided_neg (P := fun _ => K.starProjection)
    (δ := 0) (ε := ‖(1 - K.starProjection) v‖) hF (by norm_num) (norm_nonneg _)
    (odeSolution_relax v (x₀ - v) a b) (relax_dlra K hx₀ a b) (fun s _ => by
      have h1 : (1 - K.starProjection) (v - (K.starProjection v +
          Real.exp (-(s - a)) • (x₀ - K.starProjection v))) = (1 - K.starProjection) v := by
        simp only [sub_apply, one_apply_eq_self, map_sub, relax_mem K hx₀ a s]
        abel
      simp only [h1, le_refl]) (by simp) t ht
  simpa using h

/-- **Consistency of the uniform-in-time Lyapunov bound.**  Along the DLRA solution
`Y t = P v + e^{-(t-a)} (x₀ - P v)` of `F(t, x) = v - x` one has
`⟪F(t, Y), Y⟫ ≤ -‖Y‖²/2 + ‖v‖²/2`, so `ODESolution.dlra_norm_sq_le_of_neg` (`μ = -1/2`,
`β = ‖v‖²/2`) gives `‖Y t‖² ≤ e^{-(t-a)} ‖x₀‖² + ‖v‖²`. -/
example (v x₀ : E) (hx₀ : x₀ ∈ K) (a b : ℝ) :
    ∀ t ∈ Icc a b,
      ‖K.starProjection v + Real.exp (-(t - a)) • (x₀ - K.starProjection v)‖ ^ 2 ≤
        Real.exp (2 * (-1 / 2) * (t - a)) * ‖x₀‖ ^ 2 + ‖v‖ ^ 2 / 2 / (-(-1 / 2)) := by
  have h := (relax_dlra K (v := v) hx₀ a b).dlra_norm_sq_le_of_neg
    (fun _ _ => isOrthProj_starProjection K) (fun t _ => relax_mem K hx₀ a t)
    (μ := -1 / 2) (β := ‖v‖ ^ 2 / 2) (by norm_num) (by positivity) (fun t _ => by
      set y := K.starProjection v + Real.exp (-(t - a)) • (x₀ - K.starProjection v)
      show ⟪v - y, y⟫ ≤ -1 / 2 * ‖y‖ ^ 2 + ‖v‖ ^ 2 / 2
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
      nlinarith [real_inner_le_norm v y, sq_nonneg (‖v‖ - ‖y‖)])
  simpa using h

/-- **Consistency of quasi-optimality.**  For the constant field `F(t, x) = v`, the exact solution
`A t = x₀ + (t - a) v`, the curve `X t = x₀ + (t - a) P v` (for `x₀ ∈ K` this is the best
approximation `P (A t)` of `A t` in `K`) and the DLRA solution `Y = X`, all hypotheses of
`ODESolution.dlra_quasiOptimal` hold with `L = γ = c = 0`, `μ = ‖v‖`, `μ' = ‖P v‖` and the
best-approximation error `d = (b - a) ‖(1 - P) v‖`. -/
example (v x₀ : E) (a b : ℝ) :
    ∀ t ∈ Icc a b, ‖(x₀ + (t - a) • K.starProjection v) - (x₀ + (t - a) • v)‖ ≤
      (b - a) * ‖(1 - K.starProjection) v‖ +
        gronwallBound 0 (0 + 0 * (‖v‖ + ‖K.starProjection v‖))
          ((0 + 0) * ((b - a) * ‖(1 - K.starProjection) v‖)) (t - a) := by
  have hP := isOrthProj_starProjection K
  refine ODESolution.dlra_quasiOptimal (P := fun _ => K.starProjection) (F := fun _ _ => v)
    (A := fun t => x₀ + (t - a) • v) (PX := fun _ => K.starProjection) (L := 0) (γ := 0) (c := 0)
    (fun _ _ _ => by simp) le_rfl (odeSolution_affine x₀ _ a b) (fun _ _ => hP)
    (fun _ _ => hP) (odeSolution_affine x₀ _ a b).cont (odeSolution_affine x₀ _ a b).deriv
    (fun _ _ => hP.idem _) le_rfl (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun t ht => ?_) (by simp)
  have h1 : x₀ + (t - a) • v - (x₀ + (t - a) • K.starProjection v) =
      (t - a) • (1 - K.starProjection) v := by
    simp only [sub_apply, one_apply_eq_self, smul_sub]
    abel
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht.1)]
  exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) (norm_nonneg _)

/-- **Consistency of the stability theorem.**  Two DLRA trajectories
`u t = P w + e^{-(t-a)} (x₀ - P w)`, `v t = P w + e^{-(t-a)} (x₁ - P w)` of `F(t, x) = w - x`
(`x₀, x₁ ∈ K`, `P = proj_K`) satisfy the hypotheses of
`ODESolution.dlra_norm_sub_le_exp_of_curvature` with `ℓ = -1`, `κ = 0` and the (generally
nonzero) normal components `α = β = ‖(1 - P) w‖`; the bound `‖u t - v t‖ ≤ e^{-(t-a)} ‖x₀ - x₁‖`
holds with equality. -/
example (w x₀ x₁ : E) (hx₀ : x₀ ∈ K) (hx₁ : x₁ ∈ K) (a b : ℝ) :
    ∀ t ∈ Icc a b,
      ‖(K.starProjection w + Real.exp (-(t - a)) • (x₀ - K.starProjection w)) -
        (K.starProjection w + Real.exp (-(t - a)) • (x₁ - K.starProjection w))‖ ≤
      Real.exp (-(t - a)) * ‖x₀ - x₁‖ := by
  have hP := isOrthProj_starProjection K
  have hnormal : ∀ {y : E}, y ∈ K → ∀ t : ℝ,
      ‖(1 - K.starProjection) (w - (K.starProjection w +
        Real.exp (-(t - a)) • (y - K.starProjection w)))‖ ≤ ‖(1 - K.starProjection) w‖ :=
    fun hy t => by
      simp only [sub_apply, one_apply_eq_self, map_sub, relax_mem K hy a t, sub_self, sub_zero,
        le_refl]
  intro t ht
  have h := ODESolution.dlra_norm_sub_le_exp_of_curvature (ℓ := -1) (κ := 0)
    (relax_dlra K (v := w) hx₀ a b) (relax_dlra K (v := w) hx₁ a b) (fun _ _ => hP)
    (fun _ _ => hP) (fun s _ => ?_) (fun s _ => ?_) (fun s _ => ?_) (fun s _ => hnormal hx₀ s)
    (fun s _ => hnormal hx₁ s) t ht
  · simpa using h
  · have he : w - (K.starProjection w + Real.exp (-(s - a)) • (x₀ - K.starProjection w)) -
        (w - (K.starProjection w + Real.exp (-(s - a)) • (x₁ - K.starProjection w))) =
        -((K.starProjection w + Real.exp (-(s - a)) • (x₀ - K.starProjection w)) -
          (K.starProjection w + Real.exp (-(s - a)) • (x₁ - K.starProjection w))) := by abel
    rw [he, inner_neg_left, real_inner_self_eq_norm_sq]
    linarith
  · rw [zero_mul, sub_apply, one_apply_eq_self, map_sub, relax_mem K hx₀ a s,
      relax_mem K hx₁ a s, sub_self, norm_zero]
  · rw [zero_mul, sub_apply, one_apply_eq_self, map_sub, relax_mem K hx₀ a s,
      relax_mem K hx₁ a s, sub_self, norm_zero]

end Examples

end LeanDLRA
