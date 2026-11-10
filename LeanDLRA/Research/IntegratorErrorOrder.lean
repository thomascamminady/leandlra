import LeanDLRA.Integrators.Exactness
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature

/-!
# An error partial order of KSL, BUG, augmented BUG and parallel BUG

For a state-independent right-hand side `F(t, Y) = Ȧ(t)` (the class behind every exactness
theorem of dynamical low-rank approximation) all robust integrators are explicit: their outputs
are *words in projectors* applied to `A₁ = A(t₁)`.  This file compares their one-step errors
exactly, by best approximation in nested ranges and Pythagoras.

## Setting

`E` is a real inner product space, `Y₀ = A₀ = A(t₀)` with `P₀ A₀ = A₀ = Q₀ A₀`, `Δ = A₁ - A₀`.
All projectors are orthogonal (`IsOrthProj`), and the left projectors commute with the right ones
(`P₀ Q₀ = Q₀ P₀`, `P₁ Q₁ = Q₁ P₁`, `Pa Qa = Qa Pa`).  The outputs are

* KSL (Lubich–Oseledets, arXiv:1301.1058): `P₁ A₁`, where `P₁` fixes the K-step value `Q₀ A₁`
  (`Exactness.ksl_eq_abstract`);
* LSK (L-step first): `Q₁ A₁`, where `Q₁` fixes the L-step value `P₀ A₁` (`lsk_eq`);
* BUG (Ceruti–Lubich, arXiv:2010.02022): `P₁ Q₁ A₁` (`Exactness.bug_eq_abstract`);
* augmented BUG before truncation (Ceruti–Kusch–Lubich, arXiv:2104.05247): `Pa Qa A₁`, where
  `Pa P₀ = P₀`, `Pa` fixes `Q₀ A₁`, `Qa Q₀ = Q₀`, `Qa` fixes `P₀ A₁` (`augBug_eq`);
* parallel BUG before truncation (Ceruti–Kusch–Lubich, arXiv:2304.05660): `A₁ - N`,
  `N = (1 - P₀)(1 - Q₀) Δ` (`Exactness.parBug_eq_abstract`).

These are bundled in `StepData` with the hypotheses `StepData.Admissible`; the range inclusion
`Pa P₁ = P₁`, `Qa Q₁ = Q₁` is `StepData.Nested`.

## Main results

Write `e_X = A₁ - Y₁^X`.

* **(i)** `‖e_BUG‖² = ‖e_KSL‖² + ‖P₁ (1 - Q₁) A₁‖²` (`norm_sq_sub_bug`,
  `StepData.Admissible.norm_sq_bug`, ODE form `ksl_bug_ode`), and symmetrically
  `‖e_BUG‖² = ‖e_LSK‖² + ‖(1 - P₁) Q₁ A₁‖²` (`norm_sq_sub_bug_lsk`).
* **(ii)** `Y₁^aug = Y₁^par + Pa Qa N` and `‖e_par‖² = ‖e_aug‖² + ‖Pa Qa N‖²`
  (`aug_eq_par_add`, `norm_sq_sub_par`, ODE form `aug_par_ode`).  For matrices,
  `Pa Qa N = Ũ₁Ũ₁ᵀ N Ṽ₁Ṽ₁ᵀ` is exactly the "doubly new" coefficient block that the parallel
  integrator sets to zero in its augmented coefficient matrix (arXiv:2304.05660, eq. (3.4)).
* **(iii)** If `Pa P₁ = P₁` and `Qa Q₁ = Q₁`, then
  `‖e_BUG‖² = ‖e_aug‖² + ‖(Pa Qa - P₁ Q₁) A₁‖²` (`norm_sq_sub_bug_aug`, ODE form `aug_bug_ode`).
* **(iv)** Word identities `BUG = Q₁ · KSL = P₁ · LSK` (`bug_eq_right_ksl`,
  `StepData.bug_eq_left_lsk`), so BUG is the common refinement of KSL and LSK, and
  `KSL = LSK ⇔ KSL = BUG = LSK ⇔ P₁ (1 - Q₁) A₁ = 0 = (1 - P₁) Q₁ A₁`
  (`ksl_eq_lsk_iff`, `ksl_eq_bug_eq_lsk_iff`).
* **(v)** These are the only comparisons (`only_comparisons`): explicit rank-one examples with
  rational projectors (`Examples.ex₁`, `ex₂` on `ℝ^{2×2}`, `ex₃` on `ℝ^{2×3}`, all admissible and
  nested, with the natural QR bases of the K- and L-step values) show that (i)–(iii) can be
  strict and that KSL/par, BUG/par and KSL/aug are incomparable.  The Hasse diagram of the error
  order is `KSL ≤ BUG`, `aug ≤ BUG`, `aug ≤ par` (and `LSK ≤ BUG`).

## Remarks on the hypotheses

The identities need less than the full setting: (i) uses only that `P₁` is an orthogonal
projector (no capture property, nothing about `Q₁`); (ii) uses only `Pa`, `Qa` and the old
projectors; none of (i)–(iii) uses the capture of the K-step and L-step values by `P₁`, `Q₁`, which
only serves to make the outputs those of the actual integrators.  The LSK step needs
`P₀ Q₁ = Q₁ P₀` to write its S-step field as `-P₀ Q₁ F`.

## Motivation and relation to the literature

Practitioners report from numerical tests that projector splitting seems more accurate than BUG
for reversible problems (Einkemmer–Mangott–Prugger, arXiv:2309.08252, §3, citing earlier
experiments) and that the parallel BUG is less accurate than the rank-adaptive BUG
(Ceruti–Kusch–Lubich–Sulz, arXiv:2412.00858, §1); the robust error bounds of all of these
integrators have the same form and cannot explain such rankings (open problem OP-OT-52 of the
catalog, comparing hidden constants of robust integrators; OP-PA-02 concerns variants of the
zero block).  To our knowledge no paper states `KSL ≤ BUG`, `aug ≤ par`, the exact Pythagorean
defects or the word identity `BUG = Q₁ · KSL = P₁ · LSK`.  Inside the library,
`Integrators/Exactness.lean` gives the individual outputs and exactness criteria and
`Integrators/TuckerBUG.lean` an `O(h (h + ε))` bound between parallel and rank-adaptive steps;
here the gap is identified exactly.  The result is for one step with state-independent fields
and untruncated rank-adaptive steps; it says nothing about stiff or nonlinear problems.

## Follow-up questions

* For a general Lipschitz field, is the ordering perturbed only at higher order, e.g.
  `‖e_KSL‖ ≤ ‖e_BUG‖ + O(h² L ‖F‖)`?
* Does `aug ≤ par` survive the truncation step to tolerance `ϑ` (with an additive `ϑ`)?
* Tucker and tree tensor network versions: with `d` mode projectors the outputs are again
  words; which orderings hold for the TTN BUG and parallel TTN BUG of arXiv:2412.00858?
* Where do the midpoint and second-order BUG variants sit in this order?
* The per-step order does not obviously propagate over several steps (different
  starting values); is there a multi-step comparison?
-/

open scoped RealInnerProductSpace

namespace LeanDLRA

namespace ErrorOrder

/-! ## Projector-level identities -/

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pythagoras for best approximation in the range of an orthogonal projector: if `R y = y`,
then `‖x - y‖² = ‖x - R x‖² + ‖R x - y‖²`. -/
theorem norm_sub_sq_eq_of_mem_range {R : E →L[ℝ] E} (hR : IsOrthProj R) (x y : E)
    (hy : R y = y) : ‖x - y‖ ^ 2 = ‖x - R x‖ ^ 2 + ‖R x - y‖ ^ 2 := by
  have h1 : R x - y = R (x - y) := by rw [map_sub, hy]
  have horth : ⟪x - R x, R x - y⟫ = 0 := by
    rw [h1, real_inner_comm, hR.inner_sub_self]
  have h := norm_add_sq_real (x - R x) (R x - y)
  rw [horth, sub_add_sub_cancel] at h
  linarith

/-- **(i) KSL versus BUG.**  For an orthogonal projector `P₁` and an arbitrary map `Q₁`,
`‖A₁ - P₁ Q₁ A₁‖² = ‖A₁ - P₁ A₁‖² + ‖P₁ (1 - Q₁) A₁‖²`. -/
theorem norm_sq_sub_bug {P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (A₁ : E) :
    ‖A₁ - P₁ (Q₁ A₁)‖ ^ 2 = ‖A₁ - P₁ A₁‖ ^ 2 + ‖P₁ ((1 - Q₁) A₁)‖ ^ 2 := by
  rw [norm_sub_sq_eq_of_mem_range hP₁ A₁ _ (hP₁.idem _)]
  congr 3
  simp [map_sub]

/-- **LSK versus BUG** (the mirror image of `norm_sq_sub_bug`).  For an orthogonal projector
`Q₁` commuting with `P₁`,
`‖A₁ - P₁ Q₁ A₁‖² = ‖A₁ - Q₁ A₁‖² + ‖(1 - P₁) Q₁ A₁‖²`. -/
theorem norm_sq_sub_bug_lsk {P₁ Q₁ : E →L[ℝ] E} (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (A₁ : E) :
    ‖A₁ - P₁ (Q₁ A₁)‖ ^ 2 = ‖A₁ - Q₁ A₁‖ ^ 2 + ‖(1 - P₁) (Q₁ A₁)‖ ^ 2 := by
  have hy : Q₁ (P₁ (Q₁ A₁)) = P₁ (Q₁ A₁) := by rw [← hc, hQ₁.idem]
  rw [norm_sub_sq_eq_of_mem_range hQ₁ A₁ _ hy]
  rfl

/-- The output `A₁ - (1 - P₀)(1 - Q₀)(A₁ - A₀)` of the untruncated parallel BUG step, written as
the word `P₀ A₁ + Q₀ A₁ - P₀ Q₀ A₁` when `P₀`, `Q₀` fix `A₀`. -/
theorem par_eq_word {P₀ Q₀ : E →L[ℝ] E} {A₀ : E} (hP₀ : P₀ A₀ = A₀) (hQ₀ : Q₀ A₀ = A₀)
    (A₁ : E) :
    A₁ - (1 - P₀) ((1 - Q₀) (A₁ - A₀)) = P₀ A₁ + Q₀ A₁ - P₀ (Q₀ A₁) := by
  simp only [sub_apply, one_apply_eq_self, map_sub, hP₀, hQ₀]
  abel

/-- The parallel output lies in the range of the augmented Galerkin projector `Pa Qa`. -/
theorem aug_par_fixed {P₀ Q₀ Pa Qa : E →L[ℝ] E} {A₀ A₁ : E} (hP₀ : P₀ A₀ = A₀)
    (hQ₀ : Q₀ A₀ = A₀) (hc₀ : P₀ (Q₀ A₁) = Q₀ (P₀ A₁)) (hPP : ∀ x, Pa (P₀ x) = P₀ x)
    (hQQ : ∀ x, Qa (Q₀ x) = Q₀ x) (hK : Pa (Q₀ A₁) = Q₀ A₁) (hL : Qa (P₀ A₁) = P₀ A₁) :
    Pa (Qa (A₁ - (1 - P₀) ((1 - Q₀) (A₁ - A₀)))) = A₁ - (1 - P₀) ((1 - Q₀) (A₁ - A₀)) := by
  rw [par_eq_word hP₀ hQ₀]
  have h3 : Qa (P₀ (Q₀ A₁)) = P₀ (Q₀ A₁) := by rw [hc₀, hQQ]
  simp only [map_sub, map_add, hL, hQQ, h3, hPP, hK]

/-- **(ii) augmented versus parallel BUG, the exact gap.**  The augmented output `Pa Qa A₁` is
the parallel output plus `Pa Qa N`, where `N = (1 - P₀)(1 - Q₀)(A₁ - A₀)` is the doubly-normal
defect of the parallel step. -/
theorem aug_eq_par_add {P₀ Q₀ Pa Qa : E →L[ℝ] E} {A₀ A₁ : E} (hP₀ : P₀ A₀ = A₀)
    (hQ₀ : Q₀ A₀ = A₀) (hc₀ : P₀ (Q₀ A₁) = Q₀ (P₀ A₁)) (hPP : ∀ x, Pa (P₀ x) = P₀ x)
    (hQQ : ∀ x, Qa (Q₀ x) = Q₀ x) (hK : Pa (Q₀ A₁) = Q₀ A₁) (hL : Qa (P₀ A₁) = P₀ A₁) :
    Pa (Qa A₁) = (A₁ - (1 - P₀) ((1 - Q₀) (A₁ - A₀))) +
      Pa (Qa ((1 - P₀) ((1 - Q₀) (A₁ - A₀)))) := by
  have hfix := aug_par_fixed hP₀ hQ₀ hc₀ hPP hQQ hK hL
  set N := (1 - P₀) ((1 - Q₀) (A₁ - A₀))
  conv_lhs => rw [← sub_add_cancel A₁ N]
  rw [map_add, map_add, hfix]

/-- **(ii) augmented versus parallel BUG, Pythagorean form.**
`‖A₁ - Y_par‖² = ‖A₁ - Pa Qa A₁‖² + ‖Pa Qa N‖²` with `Y_par = A₁ - N`. -/
theorem norm_sq_sub_par {P₀ Q₀ Pa Qa : E →L[ℝ] E} {A₀ A₁ : E} (hPa : IsOrthProj Pa)
    (hQa : IsOrthProj Qa) (hca : ∀ x, Pa (Qa x) = Qa (Pa x)) (hP₀ : P₀ A₀ = A₀)
    (hQ₀ : Q₀ A₀ = A₀) (hc₀ : P₀ (Q₀ A₁) = Q₀ (P₀ A₁)) (hPP : ∀ x, Pa (P₀ x) = P₀ x)
    (hQQ : ∀ x, Qa (Q₀ x) = Q₀ x) (hK : Pa (Q₀ A₁) = Q₀ A₁) (hL : Qa (P₀ A₁) = P₀ A₁) :
    ‖A₁ - (A₁ - (1 - P₀) ((1 - Q₀) (A₁ - A₀)))‖ ^ 2 =
      ‖A₁ - Pa (Qa A₁)‖ ^ 2 + ‖Pa (Qa ((1 - P₀) ((1 - Q₀) (A₁ - A₀))))‖ ^ 2 := by
  have hfix := aug_par_fixed hP₀ hQ₀ hc₀ hPP hQQ hK hL
  have heq := aug_eq_par_add hP₀ hQ₀ hc₀ hPP hQQ hK hL
  have h2 : (Pa * Qa) A₁ - (A₁ - (1 - P₀) ((1 - Q₀) (A₁ - A₀))) =
      Pa (Qa ((1 - P₀) ((1 - Q₀) (A₁ - A₀)))) := by
    change Pa (Qa A₁) - _ = _
    rw [heq, add_sub_cancel_left]
  rw [norm_sub_sq_eq_of_mem_range (hPa.mul hQa hca) A₁ _ hfix, h2]
  rfl

/-- **(iii) augmented versus BUG.**  If the augmented ranges contain the BUG ranges
(`Pa P₁ = P₁`, `Qa Q₁ = Q₁`), then
`‖A₁ - P₁ Q₁ A₁‖² = ‖A₁ - Pa Qa A₁‖² + ‖(Pa Qa - P₁ Q₁) A₁‖²`. -/
theorem norm_sq_sub_bug_aug {P₁ Q₁ Pa Qa : E →L[ℝ] E} (hPa : IsOrthProj Pa)
    (hQa : IsOrthProj Qa) (hca : ∀ x, Pa (Qa x) = Qa (Pa x))
    (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (hnP : ∀ x, Pa (P₁ x) = P₁ x)
    (hnQ : ∀ x, Qa (Q₁ x) = Q₁ x) (A₁ : E) :
    ‖A₁ - P₁ (Q₁ A₁)‖ ^ 2 = ‖A₁ - Pa (Qa A₁)‖ ^ 2 + ‖(Pa * Qa - P₁ * Q₁) A₁‖ ^ 2 := by
  have hy : (Pa * Qa) (P₁ (Q₁ A₁)) = P₁ (Q₁ A₁) := by
    change Pa (Qa (P₁ (Q₁ A₁))) = _
    rw [hc₁, hnQ, ← hc₁, hnP]
  rw [norm_sub_sq_eq_of_mem_range (hPa.mul hQa hca) A₁ _ hy]
  rfl

/-- **(iv) Word identity `BUG = Q₁ · KSL`** for commuting `P₁`, `Q₁`. -/
theorem bug_eq_right_ksl {P₁ Q₁ : E →L[ℝ] E} (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (A₁ : E) :
    Q₁ (P₁ A₁) = P₁ (Q₁ A₁) :=
  (hc₁ A₁).symm

/-- **(iv) `KSL = LSK ⇔ KSL = BUG = LSK`** (for an idempotent `P₁` and an idempotent `Q₁`). -/
theorem ksl_eq_lsk_iff {P₁ Q₁ : E →L[ℝ] E} (hP₁ : ∀ x, P₁ (P₁ x) = P₁ x) (A₁ : E) :
    P₁ A₁ = Q₁ A₁ ↔ P₁ A₁ = P₁ (Q₁ A₁) ∧ P₁ (Q₁ A₁) = Q₁ A₁ := by
  constructor
  · intro h
    have hb : P₁ (Q₁ A₁) = P₁ A₁ := by rw [← h, hP₁]
    exact ⟨hb.symm, hb.trans h⟩
  · rintro ⟨h1, h2⟩
    exact h1.trans h2

/-- **(iv) Coincidence criterion.** `KSL = BUG = LSK` iff `P₁ (1 - Q₁) A₁ = 0` and
`(1 - P₁) Q₁ A₁ = 0`. -/
theorem ksl_eq_bug_eq_lsk_iff {P₁ Q₁ : E →L[ℝ] E} (A₁ : E) :
    (P₁ A₁ = P₁ (Q₁ A₁) ∧ P₁ (Q₁ A₁) = Q₁ A₁) ↔
      P₁ ((1 - Q₁) A₁) = 0 ∧ (1 - P₁) (Q₁ A₁) = 0 := by
  simp only [sub_apply, one_apply_eq_self, map_sub,
    sub_eq_zero]
  exact and_congr Iff.rfl eq_comm

end Core

/-! ## The four integrators for a state-independent field -/

section ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ}

/-- **Explicit output of the augmented BUG step** (Ceruti–Kusch–Lubich, arXiv:2104.05247,
before truncation).  The S-step `y' = Pa Qa F(t, y)`, `y(t₀) = A(t₀)`, with `F(t,Y) = Ȧ(t)`
returns `Pa Qa A(t₁)` when the augmented ranges contain the old ones and `P₀`, `Q₀` fix
`A(t₀)`.  No capture of `A(t₁)` is assumed. -/
theorem augBug_eq (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {P₀ Q₀ Pa Qa : E →L[ℝ] E}
    {y : ℝ → E} (hy : ODESolution (fun t Y => Pa (Qa (F t Y))) y t₀ t₁) (h0 : y t₀ = A t₀)
    (hP₀ : P₀ (A t₀) = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀) (hPP : ∀ x, Pa (P₀ x) = P₀ x)
    (hQQ : ∀ x, Qa (Q₀ x) = Q₀ x) : y t₁ = Pa (Qa (A t₁)) := by
  have hfix : Pa (Qa (A t₀)) = A t₀ := by
    calc Pa (Qa (A t₀)) = Pa (Qa (Q₀ (A t₀))) := by rw [hQ₀]
      _ = Pa (P₀ (A t₀)) := by rw [hQQ, hQ₀, hP₀]
      _ = A t₀ := by rw [hPP, hP₀]
  exact Exactness.bug_eq_abstract ht hA hy (h0.trans hfix.symm)

/-- **Explicit output of the LSK step** (projector splitting with the L-step first).
L-step `YL' = P₀ F`, `YL(t₀) = A(t₀)`; the new right projector `Q₁`; backward S-step
`YS' = -P₀ Q₁ F`, `YS(t₀) = Q₁ YL(t₁)`; K-step `YK' = Q₁ F`, `YK(t₀) = YS(t₁)`.  For
`F(t,Y) = Ȧ(t)`, `P₀ A(t₀) = A(t₀)` and `P₀ Q₁ = Q₁ P₀` the result is `Q₁ A(t₁)`.  This is
`Exactness.ksl_eq_abstract` with the roles of the left and right projectors exchanged. -/
theorem lsk_eq (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {P₀ Q₁ : E →L[ℝ] E}
    (hc : ∀ x, P₀ (Q₁ x) = Q₁ (P₀ x)) {YL YS YK : ℝ → E}
    (hYL : ODESolution (fun t Y => P₀ (F t Y)) YL t₀ t₁)
    (hYS : ODESolution (fun t Y => -P₀ (Q₁ (F t Y))) YS t₀ t₁)
    (hYK : ODESolution (fun t Y => Q₁ (F t Y)) YK t₀ t₁)
    (hL0 : YL t₀ = A t₀) (hS0 : YS t₀ = Q₁ (YL t₁)) (hK0 : YK t₀ = YS t₁)
    (hP₀ : P₀ (A t₀) = A t₀) : YK t₁ = Q₁ (A t₁) := by
  have hf : (fun t Y => -P₀ (Q₁ (F t Y))) = (fun t Y => -Q₁ (P₀ (F t Y))) := by
    funext t Y; rw [hc]
  rw [hf] at hYS
  exact Exactness.ksl_eq_abstract ht hA hYL hYS hYK hL0 hS0 hK0 hP₀

/-- **(i) at the ODE level: KSL is never less accurate than BUG**, with the exact defect.
The KSL trajectories are those of `Exactness.ksl_eq_abstract`; the BUG S-step uses the same
`P₁` and any right projector `Q₁`. -/
theorem ksl_bug_ode (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₀ Q₁ : E →L[ℝ] E}
    (hP₁ : IsOrthProj P₁) {YK YS YL yB : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYS : ODESolution (fun t Y => -P₁ (Q₀ (F t Y))) YS t₀ t₁)
    (hYL : ODESolution (fun t Y => P₁ (F t Y)) YL t₀ t₁)
    (hK0 : YK t₀ = A t₀) (hS0 : YS t₀ = P₁ (YK t₁)) (hL0 : YL t₀ = YS t₁)
    (hQ₀ : Q₀ (A t₀) = A t₀)
    (hyB : ODESolution (fun t Y => P₁ (Q₁ (F t Y))) yB t₀ t₁)
    (hB0 : yB t₀ = P₁ (Q₁ (A t₀))) :
    ‖A t₁ - yB t₁‖ ^ 2 = ‖A t₁ - YL t₁‖ ^ 2 + ‖P₁ ((1 - Q₁) (A t₁))‖ ^ 2 := by
  rw [Exactness.ksl_eq_abstract ht hA hYK hYS hYL hK0 hS0 hL0 hQ₀,
    Exactness.bug_eq_abstract ht hA hyB hB0]
  exact norm_sq_sub_bug hP₁ (A t₁)

/-- **(ii) at the ODE level: the augmented BUG step is never less accurate than the
(untruncated) parallel BUG step**, with the exact defect `‖Pa Qa N‖²`,
`N = (1 - P₀)(1 - Q₀)(A(t₁) - A(t₀))`.  The parallel trajectories are those of
`Exactness.parBug_eq_abstract`. -/
theorem aug_par_ode (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {P₀ Q₀ Pa Qa : E →L[ℝ] E}
    (hPa : IsOrthProj Pa) (hQa : IsOrthProj Qa) (hca : ∀ x, Pa (Qa x) = Qa (Pa x))
    (hc₀ : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) {YK YL YS y : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYL : ODESolution (fun t Y => P₀ (F t Y)) YL t₀ t₁)
    (hYS : ODESolution (fun t Y => P₀ (Q₀ (F t Y))) YS t₀ t₁)
    (hK0 : YK t₀ = A t₀) (hL0 : YL t₀ = A t₀) (hS0 : YS t₀ = A t₀)
    (hP₀ : P₀ (A t₀) = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀)
    (hPP : ∀ x, Pa (P₀ x) = P₀ x) (hQQ : ∀ x, Qa (Q₀ x) = Q₀ x)
    (hK : Pa (Q₀ (A t₁)) = Q₀ (A t₁)) (hL : Qa (P₀ (A t₁)) = P₀ (A t₁))
    (hy : ODESolution (fun t Y => Pa (Qa (F t Y))) y t₀ t₁) (h0 : y t₀ = A t₀) :
    ‖A t₁ - (YS t₁ + (1 - P₀) (YK t₁) + (1 - Q₀) (YL t₁))‖ ^ 2 =
      ‖A t₁ - y t₁‖ ^ 2 + ‖Pa (Qa ((1 - P₀) ((1 - Q₀) (A t₁ - A t₀))))‖ ^ 2 := by
  rw [Exactness.parBug_eq_abstract ht hA hc₀ hYK hYL hYS hK0 hL0 hS0 hP₀ hQ₀,
    augBug_eq ht hA hy h0 hP₀ hQ₀ hPP hQQ]
  exact norm_sq_sub_par hPa hQa hca hP₀ hQ₀ (hc₀ _) hPP hQQ hK hL

/-- **(iii) at the ODE level: the augmented BUG step is never less accurate than the BUG step**
when the augmented ranges contain the BUG ranges, with the exact defect
`‖(Pa Qa - P₁ Q₁) A(t₁)‖²`. -/
theorem aug_bug_ode (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {P₀ Q₀ P₁ Q₁ Pa Qa : E →L[ℝ] E} (hPa : IsOrthProj Pa) (hQa : IsOrthProj Qa)
    (hca : ∀ x, Pa (Qa x) = Qa (Pa x)) (hc₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x))
    (hnP : ∀ x, Pa (P₁ x) = P₁ x) (hnQ : ∀ x, Qa (Q₁ x) = Q₁ x)
    (hP₀ : P₀ (A t₀) = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀)
    (hPP : ∀ x, Pa (P₀ x) = P₀ x) (hQQ : ∀ x, Qa (Q₀ x) = Q₀ x) {y yB : ℝ → E}
    (hy : ODESolution (fun t Y => Pa (Qa (F t Y))) y t₀ t₁) (h0 : y t₀ = A t₀)
    (hyB : ODESolution (fun t Y => P₁ (Q₁ (F t Y))) yB t₀ t₁)
    (hB0 : yB t₀ = P₁ (Q₁ (A t₀))) :
    ‖A t₁ - yB t₁‖ ^ 2 = ‖A t₁ - y t₁‖ ^ 2 + ‖(Pa * Qa - P₁ * Q₁) (A t₁)‖ ^ 2 := by
  rw [augBug_eq ht hA hy h0 hP₀ hQ₀ hPP hQQ, Exactness.bug_eq_abstract ht hA hyB hB0]
  exact norm_sq_sub_bug_aug hPa hQa hca hc₁ hnP hnQ (A t₁)

end ODE

/-! ## Bundled form: the partial order -/

/-- The data of one step of the four integrators for a state-independent field: the old and new
values `A₀ = A(t₀)`, `A₁ = A(t₁)`, the old projectors `P₀`, `Q₀`, the new BUG/KSL projectors
`P₁` (from the K-step) and `Q₁` (from the L-step), and the augmented projectors `Pa`, `Qa`. -/
structure StepData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The old value `A(t₀) = Y₀`. -/
  A₀ : E
  /-- The new value `A(t₁)`. -/
  A₁ : E
  /-- The old left projector (`U₀U₀ᵀ ·`). -/
  P₀ : E →L[ℝ] E
  /-- The old right projector (`· V₀V₀ᵀ`). -/
  Q₀ : E →L[ℝ] E
  /-- The new left projector (`U₁U₁ᵀ ·`, from the K-step). -/
  P₁ : E →L[ℝ] E
  /-- The new right projector (`· V₁V₁ᵀ`, from the L-step). -/
  Q₁ : E →L[ℝ] E
  /-- The augmented left projector (`ÛÛᵀ ·`, `Û` spanning `[K₁, U₀]`). -/
  Pa : E →L[ℝ] E
  /-- The augmented right projector (`· V̂V̂ᵀ`, `V̂` spanning `[L₁, V₀]`). -/
  Qa : E →L[ℝ] E

namespace StepData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : StepData E)

/-- Output of the KSL (projector-splitting) step: `P₁ A₁` (`Exactness.ksl_eq_abstract`). -/
def ksl : E := d.P₁ d.A₁

/-- Output of the LSK step (L-step first): `Q₁ A₁` (`lsk_eq`). -/
def lsk : E := d.Q₁ d.A₁

/-- Output of the BUG step: `P₁ Q₁ A₁` (`Exactness.bug_eq_abstract`). -/
def bug : E := d.P₁ (d.Q₁ d.A₁)

/-- Output of the augmented (rank-adaptive, untruncated) BUG step: `Pa Qa A₁` (`augBug_eq`). -/
def aug : E := d.Pa (d.Qa d.A₁)

/-- The doubly-normal defect `N = (1 - P₀)(1 - Q₀)(A₁ - A₀)` of the parallel BUG step. -/
def defect : E := (1 - d.P₀) ((1 - d.Q₀) (d.A₁ - d.A₀))

/-- Output of the (untruncated) parallel BUG step: `A₁ - N` (`Exactness.parBug_eq_abstract`). -/
def par : E := d.A₁ - d.defect

/-- The hypotheses of the setting: all projectors orthogonal, the three left/right pairs
commute, `P₀`, `Q₀` fix `A₀`, `P₁` captures the K-step value `Q₀ A₁`, `Q₁` captures the L-step
value `P₀ A₁`, and the augmented projectors contain the old ranges and capture both values. -/
structure Admissible : Prop where
  orth_P₀ : IsOrthProj d.P₀
  orth_Q₀ : IsOrthProj d.Q₀
  orth_P₁ : IsOrthProj d.P₁
  orth_Q₁ : IsOrthProj d.Q₁
  orth_Pa : IsOrthProj d.Pa
  orth_Qa : IsOrthProj d.Qa
  comm₀ : ∀ x, d.P₀ (d.Q₀ x) = d.Q₀ (d.P₀ x)
  comm₁ : ∀ x, d.P₁ (d.Q₁ x) = d.Q₁ (d.P₁ x)
  comma : ∀ x, d.Pa (d.Qa x) = d.Qa (d.Pa x)
  fix_P₀ : d.P₀ d.A₀ = d.A₀
  fix_Q₀ : d.Q₀ d.A₀ = d.A₀
  capK : d.P₁ (d.Q₀ d.A₁) = d.Q₀ d.A₁
  capL : d.Q₁ (d.P₀ d.A₁) = d.P₀ d.A₁
  aug_P₀ : ∀ x, d.Pa (d.P₀ x) = d.P₀ x
  aug_Q₀ : ∀ x, d.Qa (d.Q₀ x) = d.Q₀ x
  augK : d.Pa (d.Q₀ d.A₁) = d.Q₀ d.A₁
  augL : d.Qa (d.P₀ d.A₁) = d.P₀ d.A₁

/-- The augmented ranges contain the BUG ranges: `Pa P₁ = P₁`, `Qa Q₁ = Q₁`. -/
structure Nested : Prop where
  left : ∀ x, d.Pa (d.P₁ x) = d.P₁ x
  right : ∀ x, d.Qa (d.Q₁ x) = d.Q₁ x

variable {d}

/-- **(i)** `‖e_BUG‖² = ‖e_KSL‖² + ‖P₁ (1 - Q₁) A₁‖²`. -/
theorem Admissible.norm_sq_bug (h : d.Admissible) :
    ‖d.A₁ - d.bug‖ ^ 2 = ‖d.A₁ - d.ksl‖ ^ 2 + ‖d.P₁ ((1 - d.Q₁) d.A₁)‖ ^ 2 :=
  norm_sq_sub_bug h.orth_P₁ d.A₁

/-- **(i), mirrored** `‖e_BUG‖² = ‖e_LSK‖² + ‖(1 - P₁) Q₁ A₁‖²`. -/
theorem Admissible.norm_sq_bug_lsk (h : d.Admissible) :
    ‖d.A₁ - d.bug‖ ^ 2 = ‖d.A₁ - d.lsk‖ ^ 2 + ‖(1 - d.P₁) (d.Q₁ d.A₁)‖ ^ 2 :=
  norm_sq_sub_bug_lsk h.orth_Q₁ h.comm₁ d.A₁

/-- **(ii)** The augmented output is the parallel output plus the doubly-new block `Pa Qa N`. -/
theorem Admissible.aug_eq_par_add (h : d.Admissible) : d.aug = d.par + d.Pa (d.Qa d.defect) :=
  ErrorOrder.aug_eq_par_add h.fix_P₀ h.fix_Q₀ (h.comm₀ _) h.aug_P₀ h.aug_Q₀ h.augK h.augL

/-- **(ii)** `‖e_par‖² = ‖e_aug‖² + ‖Pa Qa N‖²`. -/
theorem Admissible.norm_sq_par (h : d.Admissible) :
    ‖d.A₁ - d.par‖ ^ 2 = ‖d.A₁ - d.aug‖ ^ 2 + ‖d.Pa (d.Qa d.defect)‖ ^ 2 :=
  norm_sq_sub_par h.orth_Pa h.orth_Qa h.comma h.fix_P₀ h.fix_Q₀ (h.comm₀ _) h.aug_P₀ h.aug_Q₀
    h.augK h.augL

/-- **(iii)** `‖e_BUG‖² = ‖e_aug‖² + ‖(Pa Qa - P₁ Q₁) A₁‖²` for nested ranges. -/
theorem Admissible.norm_sq_bug_aug (h : d.Admissible) (hn : d.Nested) :
    ‖d.A₁ - d.bug‖ ^ 2 = ‖d.A₁ - d.aug‖ ^ 2 + ‖(d.Pa * d.Qa - d.P₁ * d.Q₁) d.A₁‖ ^ 2 :=
  norm_sq_sub_bug_aug h.orth_Pa h.orth_Qa h.comma h.comm₁ hn.left hn.right d.A₁

/-- From `b² = a² + c²` and `b ≥ 0` get `a ≤ b`. -/
lemma le_of_sq_eq_add {a b c : ℝ} (hb : 0 ≤ b) (h : b ^ 2 = a ^ 2 + c ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg c]

/-- `KSL ≤ BUG`. -/
theorem Admissible.ksl_le_bug (h : d.Admissible) : ‖d.A₁ - d.ksl‖ ≤ ‖d.A₁ - d.bug‖ :=
  le_of_sq_eq_add (norm_nonneg _) h.norm_sq_bug

/-- `LSK ≤ BUG`. -/
theorem Admissible.lsk_le_bug (h : d.Admissible) : ‖d.A₁ - d.lsk‖ ≤ ‖d.A₁ - d.bug‖ :=
  le_of_sq_eq_add (norm_nonneg _) h.norm_sq_bug_lsk

/-- `aug ≤ par`. -/
theorem Admissible.aug_le_par (h : d.Admissible) : ‖d.A₁ - d.aug‖ ≤ ‖d.A₁ - d.par‖ :=
  le_of_sq_eq_add (norm_nonneg _) h.norm_sq_par

/-- `aug ≤ BUG` for nested ranges. -/
theorem Admissible.aug_le_bug (h : d.Admissible) (hn : d.Nested) :
    ‖d.A₁ - d.aug‖ ≤ ‖d.A₁ - d.bug‖ :=
  le_of_sq_eq_add (norm_nonneg _) (h.norm_sq_bug_aug hn)

/-- **(iv)** `BUG = Q₁ · KSL`. -/
theorem Admissible.bug_eq_right_ksl (h : d.Admissible) : d.bug = d.Q₁ d.ksl :=
  (ErrorOrder.bug_eq_right_ksl h.comm₁ d.A₁).symm

/-- **(iv)** `BUG = P₁ · LSK`. -/
theorem bug_eq_left_lsk : d.bug = d.P₁ d.lsk :=
  rfl

/-- **(iv)** `KSL = LSK ⇔ KSL = BUG = LSK`. -/
theorem Admissible.ksl_eq_lsk_iff (h : d.Admissible) :
    d.ksl = d.lsk ↔ d.ksl = d.bug ∧ d.bug = d.lsk :=
  ErrorOrder.ksl_eq_lsk_iff h.orth_P₁.idem d.A₁

/-- **(iv)** `KSL = BUG = LSK ⇔ P₁ (1 - Q₁) A₁ = 0 = (1 - P₁) Q₁ A₁`. -/
theorem ksl_eq_bug_eq_lsk_iff :
    d.ksl = d.bug ∧ d.bug = d.lsk ↔
      d.P₁ ((1 - d.Q₁) d.A₁) = 0 ∧ (1 - d.P₁) (d.Q₁ d.A₁) = 0 :=
  ErrorOrder.ksl_eq_bug_eq_lsk_iff d.A₁

end StepData

/-! ## Matrix realizations: strictness and incomparability -/

section Matrices

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Left multiplication by a symmetric idempotent matrix is an orthogonal projector on
`ℝ^{m × n}` with the Frobenius inner product (an instance of the core
`Curvature.IsOrthProjMat.isOrthProj_leftMulCLM`). -/
theorem isOrthProj_leftMulCLM {M : Matrix m m ℝ} (hM : M * M = M) (hMt : Mᵀ = M) :
    IsOrthProj (Frobenius.leftMulCLM M : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  (⟨hMt, hM⟩ : Curvature.IsOrthProjMat M).isOrthProj_leftMulCLM

/-- Right multiplication by a symmetric idempotent matrix is an orthogonal projector on
`ℝ^{m × n}` with the Frobenius inner product (an instance of the core
`Curvature.IsOrthProjMat.isOrthProj_rightMulCLM`). -/
theorem isOrthProj_rightMulCLM {M : Matrix n n ℝ} (hM : M * M = M) (hMt : Mᵀ = M) :
    IsOrthProj (Frobenius.rightMulCLM M : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  (⟨hMt, hM⟩ : Curvature.IsOrthProjMat M).isOrthProj_rightMulCLM

/-- Step data on `ℝ^{m × n}` given by matrices: `P₀ = M₀ ·`, `Q₀ = · N₀`, `P₁ = M₁ ·`,
`Q₁ = · N₁`, `Pa = Ma ·`, `Qa = · Na`. -/
noncomputable def StepData.ofMatrices (A₀ A₁ : Matrix m n ℝ) (M₀ M₁ Ma : Matrix m m ℝ)
    (N₀ N₁ Na : Matrix n n ℝ) : StepData (Matrix m n ℝ) where
  A₀ := A₀
  A₁ := A₁
  P₀ := Frobenius.leftMulCLM M₀
  Q₀ := Frobenius.rightMulCLM N₀
  P₁ := Frobenius.leftMulCLM M₁
  Q₁ := Frobenius.rightMulCLM N₁
  Pa := Frobenius.leftMulCLM Ma
  Qa := Frobenius.rightMulCLM Na

/-- Admissibility of matrix step data from matrix identities. -/
theorem StepData.admissible_ofMatrices {A₀ A₁ : Matrix m n ℝ} {M₀ M₁ Ma : Matrix m m ℝ}
    {N₀ N₁ Na : Matrix n n ℝ}
    (hM₀ : M₀ * M₀ = M₀) (hM₀t : M₀ᵀ = M₀) (hM₁ : M₁ * M₁ = M₁) (hM₁t : M₁ᵀ = M₁)
    (hMa : Ma * Ma = Ma) (hMat : Maᵀ = Ma)
    (hN₀ : N₀ * N₀ = N₀) (hN₀t : N₀ᵀ = N₀) (hN₁ : N₁ * N₁ = N₁) (hN₁t : N₁ᵀ = N₁)
    (hNa : Na * Na = Na) (hNat : Naᵀ = Na)
    (hfP : M₀ * A₀ = A₀) (hfQ : A₀ * N₀ = A₀)
    (hK : M₁ * (A₁ * N₀) = A₁ * N₀) (hL : M₀ * A₁ * N₁ = M₀ * A₁)
    (haP : Ma * M₀ = M₀) (haQ : N₀ * Na = N₀)
    (haK : Ma * (A₁ * N₀) = A₁ * N₀) (haL : M₀ * A₁ * Na = M₀ * A₁) :
    (StepData.ofMatrices A₀ A₁ M₀ M₁ Ma N₀ N₁ Na).Admissible where
  orth_P₀ := isOrthProj_leftMulCLM hM₀ hM₀t
  orth_Q₀ := isOrthProj_rightMulCLM hN₀ hN₀t
  orth_P₁ := isOrthProj_leftMulCLM hM₁ hM₁t
  orth_Q₁ := isOrthProj_rightMulCLM hN₁ hN₁t
  orth_Pa := isOrthProj_leftMulCLM hMa hMat
  orth_Qa := isOrthProj_rightMulCLM hNa hNat
  comm₀ X := (Matrix.mul_assoc M₀ X N₀).symm
  comm₁ X := (Matrix.mul_assoc M₁ X N₁).symm
  comma X := (Matrix.mul_assoc Ma X Na).symm
  fix_P₀ := hfP
  fix_Q₀ := hfQ
  capK := hK
  capL := hL
  aug_P₀ X := show Ma * (M₀ * X) = M₀ * X by rw [← Matrix.mul_assoc, haP]
  aug_Q₀ X := show X * N₀ * Na = X * N₀ by rw [Matrix.mul_assoc, haQ]
  augK := haK
  augL := haL

/-- Nestedness of matrix step data from matrix identities. -/
theorem StepData.nested_ofMatrices {A₀ A₁ : Matrix m n ℝ} {M₀ M₁ Ma : Matrix m m ℝ}
    {N₀ N₁ Na : Matrix n n ℝ} (hP : Ma * M₁ = M₁) (hQ : N₁ * Na = N₁) :
    (StepData.ofMatrices A₀ A₁ M₀ M₁ Ma N₀ N₁ Na).Nested where
  left X := show Ma * (M₁ * X) = M₁ * X by rw [← Matrix.mul_assoc, hP]
  right X := show X * N₁ * Na = X * N₁ by rw [Matrix.mul_assoc, hQ]

/-- From `a² < b²` and `0 ≤ b` get `a < b`. -/
lemma lt_of_sq_lt_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  nlinarith

/-- Entrywise verification of a small matrix identity. -/
local macro "mat_eq" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_fin_two, Matrix.one_fin_three]))

namespace Examples

/-- `e₁ e₁ᵀ` on `ℝ²`, the old projector `U₀U₀ᵀ` (and `V₀V₀ᵀ` in the square examples). -/
noncomputable def E₁₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- `u uᵀ` with `u = (1, 1)/√2`: the new projector `U₁U₁ᵀ` (and `V₁V₁ᵀ`). -/
noncomputable def J₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- **Example 1** (`2 × 2`): `Y₀ = e₁e₁ᵀ`, `A₁ = (e₁ + e₂)(e₁ + e₂)ᵀ`.  KSL, BUG and augmented
BUG are exact; the parallel BUG has error `1`. -/
noncomputable def ex₁ : StepData (Matrix (Fin 2) (Fin 2) ℝ) :=
  StepData.ofMatrices !![1, 0; 0, 0] !![1, 1; 1, 1] E₁₁ J₂ 1 E₁₁ J₂ 1

/-- **Example 2** (`2 × 2`): `Y₀ = e₁e₁ᵀ`, `A₁ = e₁e₁ᵀ + e₂e₁ᵀ + e₁e₂ᵀ`.  Parallel and augmented
BUG are exact; `‖e_KSL‖² = 1/2`, `‖e_BUG‖² = 3/4`. -/
noncomputable def ex₂ : StepData (Matrix (Fin 2) (Fin 2) ℝ) :=
  StepData.ofMatrices !![1, 0; 0, 0] !![1, 1; 1, 0] E₁₁ J₂ 1 E₁₁ J₂ 1

/-- The right projector `· e₁e₁ᵀ` on `ℝ^{2 × 3}`. -/
noncomputable def F₁₁ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- The new right projector `V₁V₁ᵀ = v vᵀ / 101`, `v = (10, 1, 0)`, of example 3. -/
noncomputable def G₁ : Matrix (Fin 3) (Fin 3) ℝ :=
  !![100 / 101, 10 / 101, 0; 10 / 101, 1 / 101, 0; 0, 0, 0]

/-- The augmented right projector onto `span(e₁, e₂) ⊂ ℝ³` of example 3. -/
noncomputable def F₁₂ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- **Example 3** (`2 × 3`): `Y₀ = e₁e₁ᵀ`, `A₁ = [[1, 1/10, 0], [1, 0, 1]]`.
`‖e_KSL‖² = 101/200 < 1 = ‖e_aug‖²`. -/
noncomputable def ex₃ : StepData (Matrix (Fin 2) (Fin 3) ℝ) :=
  StepData.ofMatrices !![1, 0, 0; 0, 0, 0] !![1, 1 / 10, 0; 1, 0, 1] E₁₁ J₂ 1 F₁₁ G₁ F₁₂

theorem ex₁_admissible : ex₁.Admissible := by
  unfold ex₁ E₁₁ J₂
  exact StepData.admissible_ofMatrices (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq)

theorem ex₁_nested : ex₁.Nested := by
  unfold ex₁ J₂
  exact StepData.nested_ofMatrices (by mat_eq) (by mat_eq)

theorem ex₂_admissible : ex₂.Admissible := by
  unfold ex₂ E₁₁ J₂
  exact StepData.admissible_ofMatrices (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq)

theorem ex₂_nested : ex₂.Nested := by
  unfold ex₂ J₂
  exact StepData.nested_ofMatrices (by mat_eq) (by mat_eq)

theorem ex₃_admissible : ex₃.Admissible := by
  unfold ex₃ E₁₁ J₂ F₁₁ G₁ F₁₂
  exact StepData.admissible_ofMatrices (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq) (by mat_eq)
    (by mat_eq) (by mat_eq)

theorem ex₃_nested : ex₃.Nested := by
  unfold ex₃ G₁ F₁₂
  exact StepData.nested_ofMatrices (by mat_eq) (by mat_eq)

theorem ex₁_ksl : ‖ex₁.A₁ - ex₁.ksl‖ ^ 2 = 0 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₁, E₁₁, J₂, StepData.ofMatrices, StepData.ksl, Fin.sum_univ_succ, Matrix.mul_apply]

theorem ex₁_bug : ‖ex₁.A₁ - ex₁.bug‖ ^ 2 = 0 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₁, E₁₁, J₂, StepData.ofMatrices, StepData.bug, Fin.sum_univ_succ, Matrix.mul_apply]

theorem ex₁_aug : ‖ex₁.A₁ - ex₁.aug‖ ^ 2 = 0 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₁, StepData.ofMatrices, StepData.aug, Fin.sum_univ_succ]

theorem ex₁_par : ‖ex₁.A₁ - ex₁.par‖ ^ 2 = 1 := by
  rw [StepData.par, sub_sub_cancel, Frobenius.norm_sq_eq_sum]
  norm_num [ex₁, E₁₁, StepData.ofMatrices, StepData.defect, Fin.sum_univ_succ, Matrix.mul_apply]

theorem ex₂_ksl : ‖ex₂.A₁ - ex₂.ksl‖ ^ 2 = 1 / 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₂, E₁₁, J₂, StepData.ofMatrices, StepData.ksl, Fin.sum_univ_succ, Matrix.mul_apply]

theorem ex₂_bug : ‖ex₂.A₁ - ex₂.bug‖ ^ 2 = 3 / 4 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₂, E₁₁, J₂, StepData.ofMatrices, StepData.bug, Fin.sum_univ_succ, Matrix.mul_apply]

theorem ex₂_aug : ‖ex₂.A₁ - ex₂.aug‖ ^ 2 = 0 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₂, StepData.ofMatrices, StepData.aug, Fin.sum_univ_succ]

theorem ex₂_par : ‖ex₂.A₁ - ex₂.par‖ ^ 2 = 0 := by
  rw [StepData.par, sub_sub_cancel, Frobenius.norm_sq_eq_sum]
  norm_num [ex₂, E₁₁, StepData.ofMatrices, StepData.defect, Fin.sum_univ_succ, Matrix.mul_apply]

theorem ex₃_ksl : ‖ex₃.A₁ - ex₃.ksl‖ ^ 2 = 101 / 200 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₃, E₁₁, J₂, StepData.ofMatrices, StepData.ksl, Fin.sum_univ_succ, Matrix.mul_apply]

theorem ex₃_aug : ‖ex₃.A₁ - ex₃.aug‖ ^ 2 = 1 := by
  rw [Frobenius.norm_sq_eq_sum]
  norm_num [ex₃, F₁₂, StepData.ofMatrices, StepData.aug, Fin.sum_univ_succ, Matrix.mul_apply]

end Examples

open Examples in
/-- **(v) These are the only comparisons.**  On admissible, nested step data:

* example 2 shows `KSL < BUG`, `aug < BUG` strictly and `par < KSL`, `par < BUG`,
  `aug < KSL`;
* example 1 shows `aug < par` strictly and `KSL < par`, `BUG < par`;
* example 3 shows `KSL < aug`.

Together with `Admissible.ksl_le_bug`, `Admissible.aug_le_bug` and `Admissible.aug_le_par`, the
error order is exactly the partial order with Hasse diagram `KSL ≤ BUG`, `aug ≤ BUG`,
`aug ≤ par`; the pairs KSL/par, BUG/par and KSL/aug are incomparable. -/
theorem only_comparisons :
    (∃ d : StepData (Matrix (Fin 2) (Fin 2) ℝ), d.Admissible ∧ d.Nested ∧
      ‖d.A₁ - d.ksl‖ < ‖d.A₁ - d.bug‖ ∧ ‖d.A₁ - d.aug‖ < ‖d.A₁ - d.bug‖ ∧
      ‖d.A₁ - d.par‖ < ‖d.A₁ - d.ksl‖ ∧ ‖d.A₁ - d.par‖ < ‖d.A₁ - d.bug‖ ∧
      ‖d.A₁ - d.aug‖ < ‖d.A₁ - d.ksl‖) ∧
    (∃ d : StepData (Matrix (Fin 2) (Fin 2) ℝ), d.Admissible ∧ d.Nested ∧
      ‖d.A₁ - d.aug‖ < ‖d.A₁ - d.par‖ ∧ ‖d.A₁ - d.ksl‖ < ‖d.A₁ - d.par‖ ∧
      ‖d.A₁ - d.bug‖ < ‖d.A₁ - d.par‖) ∧
    (∃ d : StepData (Matrix (Fin 2) (Fin 3) ℝ), d.Admissible ∧ d.Nested ∧
      ‖d.A₁ - d.ksl‖ < ‖d.A₁ - d.aug‖) := by
  refine ⟨⟨ex₂, ex₂_admissible, ex₂_nested, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨ex₁, ex₁_admissible, ex₁_nested, ?_, ?_, ?_⟩, ⟨ex₃, ex₃_admissible, ex₃_nested, ?_⟩⟩ <;>
  refine lt_of_sq_lt_sq' (norm_nonneg _) ?_ <;>
  simp only [ex₁_ksl, ex₁_bug, ex₁_aug, ex₁_par, ex₂_ksl, ex₂_bug, ex₂_aug, ex₂_par, ex₃_ksl,
    ex₃_aug] <;>
  norm_num

end Matrices

end ErrorOrder

end LeanDLRA
