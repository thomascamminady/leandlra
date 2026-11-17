import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Curated.HighOrdera

/-!
# Lemma 4.2 of arXiv 2403.02834: the Variant 2 bases capture the exact solution to third order

J. Kusch, *Second-order robust parallel integrators for dynamical low-rank approximation*,
arXiv 2403.02834, §3.3 (Variant 2) and Lemma 4.2.  One step of Variant 2 from `Y₀ = U₀ S₀ V₀ᵀ`
pre-augments the bases, `Û₀ = orth([U₀, F(t₀, Y₀) V₀])`, `V̂₀ = orth([V₀, F(t₀, Y₀)ᵀ U₀])`, solves
the K- and L-steps in these bases and sets `Û₁ = orth([Û₀, K(t₁)])`,
`V̂₁ = orth([V̂₀, L(t₁)])` (`Variant2Bases`).  This module proves Lemma 4.2: these bases capture the
exact solution `Ã` from `Y₀` to third order,
`‖Ã(t₁) - Û₁Û₁ᵀ Ã(t₁) V̂₁V̂₁ᵀ‖ ≤ C₁ h³ + C₂ ε₂ᵣ h + C₃ εᵣ h²`, with the explicit constants
`C₁ = M₃/6 + L M₂/2`, `C₂ = 2`, `C₃ = 2 L` and no dependence on singular values.  The proof
follows the paper (midpoint rule for `Ã` and for the K-subflow, tangent/normal splitting at the
predictor `Ŷ⋆` of (4.2a), `(I - Û₁Û₁ᵀ) Û₀ = 0`).  It is first done for commuting orthogonal
projectors on a real inner product space (`left_capture`, `capture_abstract`) and then for matrices
with the Frobenius norm (`Variant2Bases.capture`).  `lemma_4_2` takes Assumption 2.1(3) in the
paper's form (on all of `M_r` and `M_{2r}`, `NormalPartSmall`), whereas `Variant2Bases.capture`
uses it only at `Y₀` and `Ŷ⋆`.  `Variant2Bases.capture_of_contDiff` derives every regularity
hypothesis from a jointly `C²` field with bounded derivatives (`IsC3Bounded.of_contDiff`), so that
its constants depend only on `F`.

Differences from the paper.  (a) The paper says its constants depend on "a bound of third
derivatives of the exact solution", but its proof also applies the midpoint rule to the K- and
L-subflows and expands the exact solution to second order at the half step.  `Variant2Bases.capture`
therefore assumes bounds `M₂`, `M₃` on the second and third derivatives of `Ã`, of `K V̂₀ᵀ` and of
`Û₀ Lᵀ` (`IsC3Bounded`); `capture_of_contDiff` replaces them by bounds on `F`.  (b) The paper quotes
`‖Ŷ⋆ - Ã(t_{1/2})‖ ≲ h² + h εᵣ` from the error analysis of the augmented BUG integrator; here it is
proved directly from the pre-augmentation, as `M₂ h²/8 + h εᵣ/2`
(`IsPreAugmentation.predictor_error`, `IsPreAugmentation.norm_sub_le`).  (c) Applying the normal
bound at `Ŷ⋆` presupposes `Ŷ⋆ ∈ M_{2r}`, which the paper does not check; in `lemma_4_2` this is the
hypothesis that `Û₀ᵀ (Y₀ + (h/2) F(t₀, Y₀)) V̂₀` is invertible.  (d) `orth` enters only through
orthonormal columns and range inclusions, with arbitrary numbers of columns.  (e) The step size is
positive.  The other results of the paper (Lemma 4.4, Theorems 4.1, 4.5, 5.1) are not part of this
module.
-/

open Set Filter Topology
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2403_02834

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Regularity of trajectories -/

/-- `IsC3Bounded y a b M₂ M₃`: the curve `y` is `C³` on `[a, b]`, with second and third derivatives
(within the interval) bounded by `M₂` and `M₃`. -/
structure IsC3Bounded (y : ℝ → E) (a b M₂ M₃ : ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 3 y (Icc a b)
  second : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 2 y (Icc a b) t‖ ≤ M₂
  third : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 y (Icc a b) t‖ ≤ M₃

/-- On `[t₀, t₀ + h)` the first iterated derivative of a `C³` solution is the vector field. -/
private theorem iterated_one_eq {f : ℝ → E → E} {y : ℝ → E} {t₀ h : ℝ} (hh : 0 < h)
    (hy : ODESolution f y t₀ (t₀ + h)) (h3 : ContDiffOn ℝ 3 y (Icc t₀ (t₀ + h))) :
    ∀ t ∈ Ico t₀ (t₀ + h), iteratedDerivWithin 1 y (Icc t₀ (t₀ + h)) t = f t (y t) := by
  obtain ⟨-, hw, -⟩ := MidpointBUG.contDiffOn_three_data hh h3
  intro t ht
  have h1 := hw 0 (by norm_num) t (Ico_subset_Icc_self ht)
  rw [iteratedDerivWithin_zero] at h1
  have hsub : Icc t (t₀ + h) ⊆ Icc t₀ (t₀ + h) := Icc_subset_Icc_left ht.1
  exact (uniqueDiffOn_Icc ht.2 t ⟨le_rfl, ht.2.le⟩).eq_deriv _ (h1.mono hsub)
    ((hy.deriv t ht).mono Icc_subset_Ici_self)

/-- **Midpoint rule** for a `C³` solution, with the sharp constant `1/24`. -/
theorem IsC3Bounded.midpoint_defect {f : ℝ → E → E} {y : ℝ → E} {t₀ h M₂ M₃ : ℝ} (hh : 0 < h)
    (hy : ODESolution f y t₀ (t₀ + h)) (hreg : IsC3Bounded y t₀ (t₀ + h) M₂ M₃) :
    ‖y (t₀ + h) - y t₀ - h • f (t₀ + h / 2) (y (t₀ + h / 2))‖ ≤ M₃ * h ^ 3 / 24 := by
  obtain ⟨hc, -, hd⟩ := MidpointBUG.contDiffOn_three_data hh hreg.contDiffOn
  have hm : t₀ + h / 2 ∈ Ico t₀ (t₀ + h) := ⟨by linarith, by linarith⟩
  have := MidpointBUG.midpoint_defect_le_sharp (A := y) hh hy.cont (hc 1 (by norm_num))
    (hc 2 (by norm_num))
    (fun x hx => by simpa [iteratedDerivWithin_zero] using hd 0 (by norm_num) x hx)
    (hd 1 (by norm_num)) (hd 2 (by norm_num)) (fun x hx => hreg.third x (Ioo_subset_Icc_self hx))
  rwa [iterated_one_eq hh hy hreg.contDiffOn _ hm] at this

/-- **Explicit Euler half step** for a `C³` solution:
`‖y(t₀ + h/2) - y₀ - (h/2) y'(t₀)‖ ≤ M₂ h²/8`. -/
theorem IsC3Bounded.half_step_defect {f : ℝ → E → E} {y : ℝ → E} {t₀ h M₂ M₃ : ℝ} (hh : 0 < h)
    (hy : ODESolution f y t₀ (t₀ + h)) (hreg : IsC3Bounded y t₀ (t₀ + h) M₂ M₃) :
    ‖y (t₀ + h / 2) - y t₀ - (h / 2) • f t₀ (y t₀)‖ ≤ M₂ * h ^ 2 / 8 := by
  obtain ⟨hc, hw, -⟩ := MidpointBUG.contDiffOn_three_data hh hreg.contDiffOn
  have h1 := iterated_one_eq hh hy hreg.contDiffOn
  have hT := MidpointBUG.norm_taylor_one_le (g := y)
    (g₁ := iteratedDerivWithin 1 y (Icc t₀ (t₀ + h)))
    (g₂ := iteratedDerivWithin 2 y (Icc t₀ (t₀ + h))) (a := t₀) (b := t₀ + h) (M := M₂) hy.cont
    (fun s hs => by rw [h1 s hs]; exact hy.deriv s hs) (hc 1 (by norm_num))
    (fun s hs => (hw 1 (by norm_num) s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (fun s hs => hreg.second s (Ico_subset_Icc_self hs)) (t₀ + h / 2) ⟨by linarith, by linarith⟩
  rw [h1 t₀ ⟨le_rfl, by linarith⟩, show t₀ + h / 2 - t₀ = h / 2 by ring] at hT
  calc _ ≤ _ := hT
    _ = _ := by ring

/-! ### Pre-augmented bases -/

/-- Abstract form of the pre-augmentation in step 1 of Variant 2 (arXiv 2403.02834, §3.3):
`P₀ = U₀U₀ᵀ·`, `Q₀ = ·V₀V₀ᵀ`, `P = Û₀Û₀ᵀ·`, `Q = ·V̂₀V̂₀ᵀ`, where `Û₀` contains `U₀` and `F₀ V₀`,
and `V̂₀` contains `V₀` and `F₀ᵀ U₀`. -/
structure IsPreAugmentation (P₀ Q₀ P Q : E →L[ℝ] E) (F₀ : E) : Prop where
  projP₀ : IsOrthProj P₀
  projQ₀ : IsOrthProj Q₀
  projP : IsOrthProj P
  projQ : IsOrthProj Q
  comm₀ : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)
  comm : ∀ x, P (Q x) = Q (P x)
  absorbP : ∀ x, P (P₀ x) = P₀ x
  absorbQ : ∀ x, Q (Q₀ x) = Q₀ x
  capP : P (Q₀ F₀) = Q₀ F₀
  capQ : Q (P₀ F₀) = P₀ F₀

namespace IsPreAugmentation

variable {P₀ Q₀ P Q : E →L[ℝ] E} {F₀ : E}

/-- The hypotheses are symmetric under exchanging left and right. -/
theorem symm (h : IsPreAugmentation P₀ Q₀ P Q F₀) : IsPreAugmentation Q₀ P₀ Q P F₀ where
  projP₀ := h.projQ₀
  projQ₀ := h.projP₀
  projP := h.projQ
  projQ := h.projP
  comm₀ x := (h.comm₀ x).symm
  comm x := (h.comm x).symm
  absorbP := h.absorbQ
  absorbQ := h.absorbP
  capP := h.capQ
  capQ := h.capP

/-- **The augmented Galerkin defect of `F₀` is a normal component** (arXiv 2403.02834, §3.3 and
proof of Lemma 4.4): `‖F₀ - Û₀Û₀ᵀ F₀ V̂₀V̂₀ᵀ‖ ≤ ‖(I - U₀U₀ᵀ) F₀ (I - V₀V₀ᵀ)‖`.  The paper's proof of
Lemma 4.4 has the factor `2`; here the factor is `1`, by writing the defect as the image of the
normal part under the orthogonal projector `1 - P Q`. -/
theorem norm_sub_le (h : IsPreAugmentation P₀ Q₀ P Q F₀) :
    ‖F₀ - P (Q F₀)‖ ≤ ‖(1 - P₀) ((1 - Q₀) F₀)‖ := by
  set N := (1 - P₀) ((1 - Q₀) F₀) with hNdef
  have hN : N = F₀ - Q₀ F₀ - P₀ F₀ + P₀ (Q₀ F₀) := by
    simp only [hNdef, sub_apply, one_apply_eq_self, map_sub]
    abel
  have h1 : P (Q (Q₀ F₀)) = Q₀ F₀ := by rw [h.absorbQ, h.capP]
  have h2 : P (Q (P₀ F₀)) = P₀ F₀ := by rw [h.capQ, h.absorbP]
  have h3 : P (Q (P₀ (Q₀ F₀))) = P₀ (Q₀ F₀) := by
    rw [h.comm₀, h.absorbQ, ← h.comm₀, h.absorbP]
  have key : F₀ - P (Q F₀) = N - P (Q N) := by
    rw [hN]
    simp only [map_add, map_sub, h1, h2, h3]
    abel
  rw [key]
  exact (h.projP.mul h.projQ h.comm).norm_sub_le N

/-- `‖(I - Û₀Û₀ᵀ) F₀ V̂₀V̂₀ᵀ‖ ≤ ‖(I - U₀U₀ᵀ) F₀ (I - V₀V₀ᵀ)‖`, the bound used at the end of
the proof of Lemma 4.2 of arXiv 2403.02834. -/
theorem norm_right_sub_le (h : IsPreAugmentation P₀ Q₀ P Q F₀) :
    ‖Q F₀ - P (Q F₀)‖ ≤ ‖(1 - P₀) ((1 - Q₀) F₀)‖ := by
  set y := F₀ - P (Q F₀) with hy
  have e : Q F₀ - P (Q F₀) = (1 - P) (Q y) := by
    have hQ : Q (P (Q F₀)) = P (Q F₀) := by rw [← h.comm, h.projQ.idem]
    simp only [hy, sub_apply, one_apply_eq_self, map_sub, hQ,
      h.projP.idem, sub_self, sub_zero]
  rw [e]
  exact (h.projP.compl.norm_le _).trans ((h.projQ.norm_le _).trans h.norm_sub_le)

/-- **Error of the half-step predictor** `Ŷ⋆ = P Q (Y₀ + (h/2) F₀)` (eq. (4.2a) of
arXiv 2403.02834): if a point `y` is `d`-close to `Y₀ + (h/2) v`, where `v` agrees with `P Q F₀`
up to `n` (in the application, the normal component), then `‖y - Ŷ⋆‖ ≤ d + (h/2) n`. -/
theorem predictor_error {Y₀ y v : E} {h d n : ℝ} (hh : 0 ≤ h)
    (hPQ : P (Q Y₀) = Y₀) (hv : ‖v - P (Q F₀)‖ ≤ n) (hd : ‖y - Y₀ - (h / 2) • v‖ ≤ d) :
    ‖y - P (Q (Y₀ + (h / 2) • F₀))‖ ≤ d + h / 2 * n := by
  have e : y - P (Q (Y₀ + (h / 2) • F₀))
      = (y - Y₀ - (h / 2) • v) + (h / 2) • (v - P (Q F₀)) := by
    simp only [map_add, map_smul, hPQ]
    module
  rw [e]
  have hh2 : 0 ≤ h / 2 := by linarith
  calc _ ≤ ‖y - Y₀ - (h / 2) • v‖ + ‖(h / 2) • (v - P (Q F₀))‖ := norm_add_le _ _
    _ ≤ d + h / 2 * n := by
        rw [norm_smul, Real.norm_of_nonneg hh2]
        exact add_le_add hd (mul_le_mul_of_nonneg_left hv hh2)

end IsPreAugmentation

/-! ### One-sided capture -/

/-- Core of the proof of Lemma 4.2 of arXiv 2403.02834 in terms of quadrature defects. -/
theorem left_capture_of_defects {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {P Q P₁ : E →L[ℝ] E} (hQ : IsOrthProj Q)
    (hP₁ : IsOrthProj P₁) (hP₁P : ∀ x, P₁ (P x) = P x) {Y₀ Ystar : E} (hY₀ : P Y₀ = Y₀)
    {A YK : ℝ → E} (hA₀ : A t₀ = Y₀) (hK₀ : YK t₀ = Y₀)
    (hcap : P₁ (YK (t₀ + h)) = YK (t₀ + h)) {q qK d dK ε₂ : ℝ}
    (hq : ‖A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ q)
    (hqK : ‖YK (t₀ + h) - YK t₀ - h • Q (F (t₀ + h / 2) (YK (t₀ + h / 2)))‖ ≤ qK)
    (hd : ‖A (t₀ + h / 2) - Ystar‖ ≤ d) (hdK : ‖YK (t₀ + h / 2) - Ystar‖ ≤ dK)
    (hn : ‖(1 - P) ((1 - Q) (F (t₀ + h / 2) Ystar))‖ ≤ ε₂) :
    ‖A (t₀ + h) - P₁ (A (t₀ + h))‖ ≤ q + qK + h * (L * d + L * dK + ε₂) := by
  have hfix : P₁ Y₀ = Y₀ := by
    have := hP₁P Y₀
    rwa [hY₀] at this
  have hm := MidpointBUG.midpoint_capture (A := A) (t₁ := t₀ + h) hP₁ hF hL hh
    (by rw [hA₀, hfix]) hq hd (ε' := ‖F (t₀ + h / 2) Ystar - P₁ (F (t₀ + h / 2) Ystar)‖) le_rfl
  set Fs := F (t₀ + h / 2) Ystar with hFs
  set Fk := F (t₀ + h / 2) (YK (t₀ + h / 2)) with hFk
  -- the K-step end value lies in the range of `P₁`, so the midpoint rule for it captures `Q Fk`
  have hG : h * ‖Q Fk - P₁ (Q Fk)‖ ≤ qK := by
    have e : h • (Q Fk - P₁ (Q Fk))
        = -((1 - P₁) (YK (t₀ + h) - YK t₀ - h • Q Fk)) := by
      simp only [sub_apply, one_apply_eq_self, map_sub, map_smul,
        hcap, hK₀, hfix]
      module
    calc h * ‖Q Fk - P₁ (Q Fk)‖ = ‖h • (Q Fk - P₁ (Q Fk))‖ := by
          rw [norm_smul, Real.norm_of_nonneg hh]
      _ = ‖(1 - P₁) (YK (t₀ + h) - YK t₀ - h • Q Fk)‖ := by rw [e, norm_neg]
      _ ≤ ‖YK (t₀ + h) - YK t₀ - h • Q Fk‖ := hP₁.compl.norm_le _
      _ ≤ qK := hqK
  -- tangent/normal splitting at the predictor, using `(1 - P₁) P = 0`
  have hdec : Fs - P₁ Fs = (1 - P₁) ((1 - P) ((1 - Q) Fs)) + (1 - P₁) (Q Fs) := by
    simp only [sub_apply, one_apply_eq_self, map_sub, hP₁P]
    abel
  have hsplit : ‖Fs - P₁ Fs‖ ≤ ε₂ + ‖Q Fs - P₁ (Q Fs)‖ := by
    rw [hdec]
    calc _ ≤ ‖(1 - P₁) ((1 - P) ((1 - Q) Fs))‖ + ‖(1 - P₁) (Q Fs)‖ := norm_add_le _ _
      _ ≤ ‖(1 - P) ((1 - Q) Fs)‖ + ‖Q Fs - P₁ (Q Fs)‖ :=
          add_le_add (hP₁.compl.norm_le _) (by simp)
      _ ≤ _ := by gcongr
  -- comparison of the two nodes
  have hcomp : ‖Q Fs - P₁ (Q Fs)‖ ≤ ‖Q Fk - P₁ (Q Fk)‖ + L * dK := by
    have e : Q Fs - P₁ (Q Fs) = (Q Fk - P₁ (Q Fk)) + (1 - P₁) (Q (Fs - Fk)) := by
      simp only [sub_apply, one_apply_eq_self, map_sub]
      abel
    rw [e]
    have hw : ‖Fs - Fk‖ ≤ L * dK := by
      refine (hF _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [norm_sub_rev]
      exact hdK
    calc _ ≤ ‖Q Fk - P₁ (Q Fk)‖ + ‖(1 - P₁) (Q (Fs - Fk))‖ := norm_add_le _ _
      _ ≤ _ := by
          gcongr
          exact (hP₁.compl.norm_le _).trans ((hQ.norm_le _).trans hw)
  have hfinal : h * ‖Fs - P₁ Fs‖ ≤ h * ε₂ + qK + h * (L * dK) := by
    have : h * ‖Fs - P₁ Fs‖ ≤ h * (ε₂ + ‖Q Fk - P₁ (Q Fk)‖ + L * dK) :=
      mul_le_mul_of_nonneg_left (by linarith) hh
    nlinarith
  calc _ ≤ q + h * (L * d + ‖Fs - P₁ Fs‖) := hm
    _ ≤ _ := by nlinarith

/-- **Left half of Lemma 4.2 of arXiv 2403.02834** (abstract form):
`‖(I - Û₁Û₁ᵀ) Ã(t₁)‖ ≤ (M₃/12 + L M₂/4) h³ + ε₂ᵣ h + L εᵣ h²`.  This is the estimate proved in the
paper; the bound `‖Ŷ⋆ - Ã(t_{1/2})‖ ≲ h² + h εᵣ`, which the paper quotes from the first-order error
analysis of the augmented BUG integrator, is proved here directly (`predictor_error`). -/
theorem left_capture {F : ℝ → E → E} {L εr ε2r M₂ M₃ t₀ h : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hh : 0 < h) {P₀ Q₀ P Q P₁ : E →L[ℝ] E} {Y₀ : E}
    (haug : IsPreAugmentation P₀ Q₀ P Q (F t₀ Y₀)) (hP₁ : IsOrthProj P₁)
    (hP₁P : ∀ x, P₁ (P x) = P x) (hY₀ : P (Q Y₀) = Y₀) {A YK : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = Y₀)
    (hAreg : IsC3Bounded A t₀ (t₀ + h) M₂ M₃)
    (hK : ODESolution (fun t x => Q (F t x)) YK t₀ (t₀ + h)) (hK₀ : YK t₀ = Y₀)
    (hKreg : IsC3Bounded YK t₀ (t₀ + h) M₂ M₃) (hcap : P₁ (YK (t₀ + h)) = YK (t₀ + h))
    (hεr : ‖(1 - P₀) ((1 - Q₀) (F t₀ Y₀))‖ ≤ εr)
    (hε2r : ‖(1 - P) ((1 - Q) (F (t₀ + h / 2) (P (Q (Y₀ + (h / 2) • F t₀ Y₀)))))‖ ≤ ε2r) :
    ‖A (t₀ + h) - P₁ (A (t₀ + h))‖
      ≤ (M₃ / 12 + L * M₂ / 4) * h ^ 3 + ε2r * h + L * εr * h ^ 2 := by
  have hh0 : 0 ≤ h := hh.le
  have hPY : P Y₀ = Y₀ := by
    conv_lhs => rw [← hY₀]
    rw [haug.projP.idem, hY₀]
  have hq := hAreg.midpoint_defect hh hA
  have hqK := hKreg.midpoint_defect hh hK
  have hd0 := hAreg.half_step_defect hh hA
  have hdK0 := hKreg.half_step_defect hh hK
  simp only [hA₀] at hd0
  simp only [hK₀] at hdK0
  have hN1 := haug.norm_sub_le.trans hεr
  have hN2 := haug.norm_right_sub_le.trans hεr
  have hd := IsPreAugmentation.predictor_error hh0 hY₀ hN1 hd0
  have hdK := IsPreAugmentation.predictor_error hh0 hY₀ hN2 hdK0
  have key := left_capture_of_defects hF hL hh0 haug.projQ hP₁ hP₁P hPY hA₀ hK₀ hcap hq hqK hd hdK
    hε2r
  calc _ ≤ _ := key
    _ = _ := by ring

/-- **Lemma 4.2 of arXiv 2403.02834, abstract form.**  With the notation of `IsPreAugmentation`,
let `P₁`, `Q₁` be orthogonal projectors whose ranges contain those of `P`, `Q` and the end values of
the K- and L-steps `YK' = Q F(t, YK)`, `YL' = P F(t, YL)` started at `Y₀`.  Then the exact solution
from `Y₀` satisfies `‖Ã(t₁) - P₁ Q₁ Ã(t₁)‖ ≤ (M₃/6 + L M₂/2) h³ + 2 ε₂ᵣ h + 2 L εᵣ h²`. -/
theorem capture_abstract {F : ℝ → E → E} {L εr ε2r M₂ M₃ t₀ t₁ h : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 < h)
    {P₀ Q₀ P Q P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} (haug : IsPreAugmentation P₀ Q₀ P Q (F t₀ Y₀))
    (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁) (hP₁P : ∀ x, P₁ (P x) = P x)
    (hQ₁Q : ∀ x, Q₁ (Q x) = Q x) (hY₀ : P (Q Y₀) = Y₀) {A YK YL : ℝ → E}
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) (hAreg : IsC3Bounded A t₀ t₁ M₂ M₃)
    (hK : ODESolution (fun t x => Q (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKreg : IsC3Bounded YK t₀ t₁ M₂ M₃) (hKcap : P₁ (YK t₁) = YK t₁)
    (hLs : ODESolution (fun t x => P (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hLreg : IsC3Bounded YL t₀ t₁ M₂ M₃) (hLcap : Q₁ (YL t₁) = YL t₁)
    (hεr : ‖(1 - P₀) ((1 - Q₀) (F t₀ Y₀))‖ ≤ εr)
    (hε2r : ‖(1 - P) ((1 - Q) (F (t₀ + h / 2) (P (Q (Y₀ + (h / 2) • F t₀ Y₀)))))‖ ≤ ε2r) :
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ (M₃ / 6 + L * M₂ / 2) * h ^ 3 + 2 * ε2r * h + 2 * L * εr * h ^ 2 := by
  subst ht₁
  have hl := left_capture hF hL hh haug hP₁ hP₁P hY₀ hA hA₀ hAreg hK hK₀ hKreg hKcap hεr hε2r
  have hεr' : ‖(1 - Q₀) ((1 - P₀) (F t₀ Y₀))‖ ≤ εr := by
    have e : (1 - Q₀) ((1 - P₀) (F t₀ Y₀)) = (1 - P₀) ((1 - Q₀) (F t₀ Y₀)) := by
      simp only [sub_apply, one_apply_eq_self, map_sub, haug.comm₀]
      abel
    rwa [e]
  have hε2r' : ‖(1 - Q) ((1 - P) (F (t₀ + h / 2) (Q (P (Y₀ + (h / 2) • F t₀ Y₀)))))‖ ≤ ε2r := by
    have e : ∀ x, (1 - Q) ((1 - P) x) = (1 - P) ((1 - Q) x) := fun x => by
      simp only [sub_apply, one_apply_eq_self, map_sub, haug.comm]
      abel
    rwa [e, ← haug.comm]
  have hY₀' : Q (P Y₀) = Y₀ := by rw [← haug.comm, hY₀]
  have hr := left_capture hF hL hh haug.symm hQ₁ hQ₁Q hY₀' hA hA₀ hAreg hLs hL₀ hLreg hLcap
    hεr' hε2r'
  have hsplit := norm_sub_apply_apply_le (Q := Q₁) hP₁ (A (t₀ + h))
  simp only [sub_apply, one_apply_eq_self] at hsplit
  calc _ ≤ _ := hsplit
    _ ≤ _ := add_le_add hl hr
    _ = _ := by ring

/-! ### Regularity of the (sub)flows of a `C²` field -/

/-- **The third-derivative hypotheses follow from smoothness of `F`.**  If `F` is jointly `C²` with
`‖F‖ ≤ B`, `‖DF‖ ≤ M₁`, `‖D²F‖ ≤ M₂`, then every solution of `y' = R F(t, y)` with `‖R‖ ≤ 1` (the
exact flow `R = 1`, a K-step `R = Q`, an L-step `R = P`) is `C³` with `‖y''‖ ≤ M₁ (1 + B)` and
`‖y'''‖ ≤ M₂ (1 + B)² + M₁² (1 + B)`.  In particular the bounds do not depend on `R`, that is, on
the bases.  The third derivative is `ODESolution.norm_iteratedDerivWithin_three_le` of the
library. -/
theorem IsC3Bounded.of_contDiff {F : ℝ → E → E} {R : E →L[ℝ] E} (hR : ‖R‖ ≤ 1) {B M₁ M₂ : ℝ}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) (hB : IsBoundedField F B)
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂) {y : ℝ → E} {a b : ℝ}
    (hab : a < b) (hy : ODESolution (fun t x => R (F t x)) y a b) :
    IsC3Bounded y a b (M₁ * (1 + B)) (M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) := by
  obtain ⟨h3, hbd⟩ := ODESolution.norm_iteratedDerivWithin_three_le hR hF hB hM₁ hM₂ hy
  refine ⟨h3, ?_, hbd⟩
  obtain ⟨h, rfl⟩ : ∃ h, b = a + h := ⟨b - a, by ring⟩
  have hh : 0 < h := by linarith
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg (fderiv ℝ (Function.uncurry F) 0)).trans (hM₁ 0)
  obtain ⟨hc, -, hd⟩ := MidpointBUG.contDiffOn_three_data hh h3
  set D : ℝ → E → (ℝ × E) →L[ℝ] E := fun t x => fderiv ℝ (Function.uncurry F) (t, x) with hDdef
  have hD : ∀ t x, HasFDerivAt (fun p : ℝ × E => F p.1 p.2) (D t x) (t, x) := fun t x =>
    (hF.differentiable (by norm_num) (t, x)).hasFDerivAt
  have hDt : ∀ t x, ‖D t x (1, 0)‖ ≤ M₁ := fun t x => by
    have h1 := (D t x).le_opNorm ((1 : ℝ), (0 : E))
    have h2 : ‖((1 : ℝ), (0 : E))‖ = 1 := by simp [Prod.norm_def]
    rw [h2, mul_one] at h1
    exact h1.trans (hM₁ _)
  have hDx : ∀ t x v, ‖D t x (0, v)‖ ≤ M₁ * ‖v‖ := fun t x v => by
    have h1 := (D t x).le_opNorm ((0 : ℝ), v)
    have h2 : ‖((0 : ℝ), v)‖ = ‖v‖ := by simp [Prod.norm_def]
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hM₁ _) (norm_nonneg _))
  have hR' : ∀ x, ‖R x‖ ≤ ‖x‖ := fun x =>
    (R.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hR (norm_nonneg _)).trans_eq (one_mul _))
  obtain ⟨-, hsd⟩ := MidpointBUG.projected_trajectory_second_deriv hD hDt hDx hM₁0 hB hR' hy
  have h1 := iterated_one_eq hh hy h3
  -- the bound in the interior, by uniqueness of the right derivative
  have hin : ∀ x ∈ Ioo a (a + h),
      ‖iteratedDerivWithin 2 y (Icc a (a + h)) x‖ ≤ M₁ * (1 + B) := by
    intro x hx
    obtain ⟨hs1, hs2⟩ := hsd x ⟨hx.1.le, hx.2⟩
    have hd1 : HasDerivWithinAt (fun t => R (F t (y t)))
        (iteratedDerivWithin 2 y (Icc a (a + h)) x) (Ico x (a + h)) x :=
      ((hd 1 (by norm_num) x hx).hasDerivWithinAt).congr
        (fun t ht => (h1 t ⟨hx.1.le.trans ht.1, ht.2⟩).symm)
        (h1 x ⟨hx.1.le, hx.2⟩).symm
    have heq := (uniqueDiffOn_Ico x (a + h) x ⟨le_rfl, hx.2⟩).eq_deriv _ hd1
      (hs1.mono Ico_subset_Ici_self)
    rw [heq]
    calc _ ≤ M₁ + M₁ * B := hs2
      _ = _ := by ring
  -- extension to the endpoints by continuity
  intro t ht
  have hcl' : closure (Ioo a (a + h)) = Icc a (a + h) := closure_Ioo (by linarith)
  have hcl : t ∈ closure (Ioo a (a + h)) := by rwa [hcl']
  exact le_on_closure hin (by rw [hcl']; exact (hc 2 (by norm_num)).norm) continuousOn_const hcl

/-! ### Matrices: the Variant 2 integrator -/

section Matrix

open scoped LeanDLRA.Frobenius
open LeanDLRA.MatrixKSL (kField lField odeSolution_kField odeSolution_lField)

variable {m n r k l k₁ l₁ : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype k] [Fintype l]
  [Fintype k₁] [Fintype l₁] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq k]
  [DecidableEq l] [DecidableEq k₁] [DecidableEq l₁]

/-- **The bases of Variant 2** (arXiv 2403.02834, §3.3, steps 1 and 2).  From `Y₀ = U₀ S₀ V₀ᵀ`:

* step 1: `Û₀ = orth([U₀, F(t₀, Y₀) V₀])`, `V̂₀ = orth([V₀, F(t₀, Y₀)ᵀ U₀])`;
* K-step: `K' = F(t, K V̂₀ᵀ) V̂₀`, `K(t₀) = U₀ S₀ V₀ᵀ V̂₀`, and `Û₁ = orth([Û₀, K(t₁)])`;
* L-step: `L' = F(t, Û₀ Lᵀ)ᵀ Û₀`, `L(t₀) = V₀ S₀ᵀ U₀ᵀ Û₀`, and `V̂₁ = orth([V̂₀, L(t₁)])`.

Only the facts on `orth` that matter are recorded: orthonormal columns and the inclusion of the
listed ranges.  The numbers of columns are arbitrary (the paper has `2r`, `2r`, `4r`, `4r`). -/
structure Variant2Bases (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (Uh₀ : Matrix m k ℝ) (Vh₀ : Matrix n l ℝ)
    (Uh₁ : Matrix m k₁ ℝ) (Vh₁ : Matrix n l₁ ℝ) (K : ℝ → Matrix m l ℝ) (Lf : ℝ → Matrix n k ℝ) :
    Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  orthUh₀ : Uh₀ᵀ * Uh₀ = 1
  orthVh₀ : Vh₀ᵀ * Vh₀ = 1
  /-- `range U₀ ⊆ range Û₀`. -/
  spanU₀ : Uh₀ * Uh₀ᵀ * U₀ = U₀
  /-- `range (F(t₀, Y₀) V₀) ⊆ range Û₀`. -/
  spanFV : Uh₀ * Uh₀ᵀ * (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀) = F t₀ (U₀ * S₀ * V₀ᵀ) * V₀
  /-- `range V₀ ⊆ range V̂₀`. -/
  spanV₀ : Vh₀ * Vh₀ᵀ * V₀ = V₀
  /-- `range (F(t₀, Y₀)ᵀ U₀) ⊆ range V̂₀`. -/
  spanFU : Vh₀ * Vh₀ᵀ * ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀) = (F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀
  kSol : ODESolution (kField Vh₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀ * V₀ᵀ * Vh₀
  lSol : ODESolution (lField Uh₀ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ * U₀ᵀ * Uh₀
  orthUh₁ : Uh₁ᵀ * Uh₁ = 1
  orthVh₁ : Vh₁ᵀ * Vh₁ = 1
  /-- `range Û₀ ⊆ range Û₁`. -/
  spanUh₀ : Uh₁ * Uh₁ᵀ * Uh₀ = Uh₀
  /-- `range K(t₁) ⊆ range Û₁`. -/
  spanK : Uh₁ * Uh₁ᵀ * K t₁ = K t₁
  /-- `range V̂₀ ⊆ range V̂₁`. -/
  spanVh₀ : Vh₁ * Vh₁ᵀ * Vh₀ = Vh₀
  /-- `range L(t₁) ⊆ range V̂₁`. -/
  spanL : Vh₁ * Vh₁ᵀ * Lf t₁ = Lf t₁

/-- The half-step predictor `Ŷ⋆ = Û₀Û₀ᵀ (Y₀ + (h/2) F(t₀, Y₀)) V̂₀V̂₀ᵀ`, eq. (4.2a) of
arXiv 2403.02834. -/
noncomputable def predictor (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ h : ℝ) (Y₀ : Matrix m n ℝ)
    (Uh₀ : Matrix m k ℝ) (Vh₀ : Matrix n l ℝ) : Matrix m n ℝ :=
  Uh₀ * Uh₀ᵀ * (Y₀ + (h / 2) • F t₀ Y₀) * Vh₀ * Vh₀ᵀ

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l] in
/-- `Ŷ⋆` in the abstract notation. -/
theorem predictor_eq (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ h : ℝ) (Y₀ : Matrix m n ℝ)
    (Uh₀ : Matrix m k ℝ) (Vh₀ : Matrix n l ℝ) :
    predictor F t₀ h Y₀ Uh₀ Vh₀
      = leftProj Uh₀ (rightProj Vh₀ (Y₀ + (h / 2) • F t₀ Y₀)) := by
  simp only [predictor, leftProj_apply, rightProj_apply, Matrix.mul_assoc]

namespace Variant2Bases

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m r ℝ}
  {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {Uh₀ : Matrix m k ℝ} {Vh₀ : Matrix n l ℝ}
  {Uh₁ : Matrix m k₁ ℝ} {Vh₁ : Matrix n l₁ ℝ} {K : ℝ → Matrix m l ℝ} {Lf : ℝ → Matrix n k ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- The matrix bases give the abstract projectors of `IsPreAugmentation`. -/
theorem isPreAugmentation (hs : Variant2Bases F t₀ t₁ U₀ S₀ V₀ Uh₀ Vh₀ Uh₁ Vh₁ K Lf) :
    IsPreAugmentation (leftProj U₀) (rightProj V₀) (leftProj Uh₀) (rightProj Vh₀)
      (F t₀ (U₀ * S₀ * V₀ᵀ)) where
  projP₀ := isOrthProj_leftProj hs.orthU₀
  projQ₀ := isOrthProj_rightProj hs.orthV₀
  projP := isOrthProj_leftProj hs.orthUh₀
  projQ := isOrthProj_rightProj hs.orthVh₀
  comm₀ := leftProj_rightProj_comm U₀ V₀
  comm := leftProj_rightProj_comm Uh₀ Vh₀
  absorbP := leftProj_leftProj_of_mul hs.spanU₀
  absorbQ := rightProj_rightProj_of_mul hs.spanV₀
  capP := by
    have h := hs.spanFV
    simp only [leftProj_apply, rightProj_apply]
    calc _ = Uh₀ * Uh₀ᵀ * (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀) * V₀ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h]
  capQ := by
    have h := congrArg Matrix.transpose hs.spanFU
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h
    simp only [leftProj_apply, rightProj_apply]
    calc _ = U₀ * ((U₀ᵀ * F t₀ (U₀ * S₀ * V₀ᵀ)) * (Vh₀ * Vh₀ᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [h]
          simp only [Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
/-- `Û₀Û₀ᵀ Y₀ V̂₀V̂₀ᵀ = Y₀`. -/
theorem proj_start (hs : Variant2Bases F t₀ t₁ U₀ S₀ V₀ Uh₀ Vh₀ Uh₁ Vh₁ K Lf) :
    leftProj Uh₀ (rightProj Vh₀ (U₀ * S₀ * V₀ᵀ)) = U₀ * S₀ * V₀ᵀ := by
  have h := hs.isPreAugmentation
  have h1 : rightProj V₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ :=
    rightProj_mul_transpose hs.orthV₀ (U₀ * S₀)
  have h2 : leftProj U₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    rw [Matrix.mul_assoc]
    exact leftProj_mul_left hs.orthU₀ _
  calc _ = leftProj Uh₀ (rightProj Vh₀ (rightProj V₀ (U₀ * S₀ * V₀ᵀ))) := by rw [h1]
    _ = leftProj Uh₀ (rightProj V₀ (U₀ * S₀ * V₀ᵀ)) := by rw [h.absorbQ]
    _ = leftProj Uh₀ (leftProj U₀ (U₀ * S₀ * V₀ᵀ)) := by rw [h1, h2]
    _ = _ := by rw [h.absorbP, h2]

omit [DecidableEq m] [DecidableEq n] in
/-- The K-subflow `YK = K V̂₀ᵀ` starts at `Y₀`. -/
theorem yk_start (hs : Variant2Bases F t₀ t₁ U₀ S₀ V₀ Uh₀ Vh₀ Uh₁ Vh₁ K Lf) :
    K t₀ * Vh₀ᵀ = U₀ * S₀ * V₀ᵀ := by
  rw [hs.kStart, ← rightProj_apply]
  have h1 : rightProj V₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ :=
    rightProj_mul_transpose hs.orthV₀ (U₀ * S₀)
  conv_rhs => rw [← h1]
  conv_lhs => rw [← h1]
  exact hs.isPreAugmentation.absorbQ _

omit [DecidableEq m] [DecidableEq n] in
/-- The L-subflow `YL = Û₀ Lᵀ` starts at `Y₀`. -/
theorem yl_start (hs : Variant2Bases F t₀ t₁ U₀ S₀ V₀ Uh₀ Vh₀ Uh₁ Vh₁ K Lf) :
    Uh₀ * (Lf t₀)ᵀ = U₀ * S₀ * V₀ᵀ := by
  rw [hs.lStart]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = Uh₀ * Uh₀ᵀ * U₀ * (S₀ * V₀ᵀ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hs.spanU₀, Matrix.mul_assoc]

variable {L εr ε2r M₂ M₃ h : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Lemma 4.2 of arXiv 2403.02834 (Variant 2 basis captures the exact solution).**  Let `F` be
`L`-Lipschitz, `Y₀ = U₀ S₀ V₀ᵀ`, let `Û₀, V̂₀, K, L, Û₁, V̂₁` be as in Variant 2 (`Variant2Bases`),
`t₁ = t₀ + h`, `h > 0`, and let `Ã` be the exact solution with `Ã(t₀) = Y₀`.  If `Ã` and the
K- and L-subflows `K V̂₀ᵀ`, `Û₀ Lᵀ` are `C³` on `[t₀, t₁]` with second and third derivatives bounded
by `M₂`, `M₃`, and

* `‖(I - U₀U₀ᵀ) F(t₀, Y₀) (I - V₀V₀ᵀ)‖ ≤ εᵣ`,
* `‖(I - Û₀Û₀ᵀ) F(t₀ + h/2, Ŷ⋆) (I - V̂₀V̂₀ᵀ)‖ ≤ ε₂ᵣ`, with `Ŷ⋆` the predictor (4.2a),

then, in the Frobenius norm,

    ‖Ã(t₁) - Û₁Û₁ᵀ Ã(t₁) V̂₁V̂₁ᵀ‖ ≤ C₁ h³ + C₂ ε₂ᵣ h + C₃ εᵣ h²

with `C₁ = M₃/6 + L M₂/2`, `C₂ = 2`, `C₃ = 2 L`, which do not depend on singular values.

Differences from the paper: (1) the constants are explicit; (2) Assumption 2.1(3) is used only at
the two points above, which is weaker than the paper's assumption on all of `M_r` and `M_{2r}`, see
`lemma_4_2`; (3) the paper names only "a bound of third derivatives of the exact solution", while
its proof also applies the midpoint rule to `K` and `L`, so their regularity is a hypothesis here;
(4) the second derivatives are bounded as well, which the proof needs for the half step (this
does not follow from a third-derivative bound on a short interval).  Points (3), (4) disappear in
`capture_of_contDiff`.  The boundedness of `F` is not needed. -/
theorem capture (hs : Variant2Bases F t₀ t₁ U₀ S₀ V₀ Uh₀ Vh₀ Uh₁ Vh₁ K Lf)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 < h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hAreg : IsC3Bounded A t₀ t₁ M₂ M₃)
    (hKreg : IsC3Bounded (fun t => K t * Vh₀ᵀ) t₀ t₁ M₂ M₃)
    (hLreg : IsC3Bounded (fun t => Uh₀ * (Lf t)ᵀ) t₀ t₁ M₂ M₃)
    (hεr : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ εr)
    (hε2r : ‖(1 - Uh₀ * Uh₀ᵀ) * F (t₀ + h / 2) (predictor F t₀ h (U₀ * S₀ * V₀ᵀ) Uh₀ Vh₀) *
      (1 - Vh₀ * Vh₀ᵀ)‖ ≤ ε2r) :
    ‖A t₁ - Uh₁ * Uh₁ᵀ * A t₁ * Vh₁ * Vh₁ᵀ‖
      ≤ (M₃ / 6 + L * M₂ / 2) * h ^ 3 + 2 * ε2r * h + 2 * L * εr * h ^ 2 := by
  have hPK : leftProj Uh₁ (K t₁ * Vh₀ᵀ) = K t₁ * Vh₀ᵀ := by
    rw [leftProj_apply, ← Matrix.mul_assoc, hs.spanK]
  have hQL : rightProj Vh₁ (Uh₀ * (Lf t₁)ᵀ) = Uh₀ * (Lf t₁)ᵀ := by
    have h1 := congrArg Matrix.transpose hs.spanL
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    rw [rightProj_apply]
    calc _ = Uh₀ * ((Lf t₁)ᵀ * (Vh₁ * Vh₁ᵀ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]
  have key := capture_abstract (εr := εr) (ε2r := ε2r) (M₂ := M₂) (M₃ := M₃) hF hL ht₁ hh
    hs.isPreAugmentation (isOrthProj_leftProj hs.orthUh₁) (isOrthProj_rightProj hs.orthVh₁)
    (leftProj_leftProj_of_mul hs.spanUh₀) (rightProj_rightProj_of_mul hs.spanVh₀) hs.proj_start
    hA hA₀ hAreg (odeSolution_kField hs.kSol) hs.yk_start hKreg hPK
    (odeSolution_lField hs.lSol) hs.yl_start hLreg hQL
    (by rw [one_sub_leftProj_one_sub_rightProj_apply]; exact hεr)
    (by rw [one_sub_leftProj_one_sub_rightProj_apply, ← predictor_eq]; exact hε2r)
  calc _ = ‖A t₁ - leftProj Uh₁ (rightProj Vh₁ (A t₁))‖ := by
        simp only [leftProj_apply, rightProj_apply, Matrix.mul_assoc]
    _ ≤ _ := key

/-- **Lemma 4.2 of arXiv 2403.02834 with constants depending only on `F`.**  If `F` is jointly `C²`
with `‖F‖ ≤ B`, `‖DF‖ ≤ M₁`, `‖D²F‖ ≤ M₂`, then the regularity hypotheses of `capture` hold
automatically, with `D₂ = M₁ (1 + B)` and `D₃ = M₂ (1 + B)² + M₁² (1 + B)`, for the exact flow and
for the K- and L-subflows, whatever the bases.  Hence

    ‖Ã(t₁) - Û₁Û₁ᵀ Ã(t₁) V̂₁V̂₁ᵀ‖ ≤ (D₃/6 + L D₂/2) h³ + 2 ε₂ᵣ h + 2 L εᵣ h².

This replaces the paper's "a bound of third derivatives of the exact solution" by bounds on `F`,
which control the K- and L-subflows too. -/
theorem capture_of_contDiff {B M₁ : ℝ}
    (hs : Variant2Bases F t₀ t₁ U₀ S₀ V₀ Uh₀ Vh₀ Uh₁ Vh₁ K Lf)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hF2 : ContDiff ℝ 2 (Function.uncurry F))
    (hM₁ : ∀ p, ‖fderiv ℝ (Function.uncurry F) p‖ ≤ M₁)
    (hM₂ : ∀ p, ‖iteratedFDeriv ℝ 2 (Function.uncurry F) p‖ ≤ M₂)
    (ht₁ : t₁ = t₀ + h) (hh : 0 < h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hεr : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ εr)
    (hε2r : ‖(1 - Uh₀ * Uh₀ᵀ) * F (t₀ + h / 2) (predictor F t₀ h (U₀ * S₀ * V₀ᵀ) Uh₀ Vh₀) *
      (1 - Vh₀ * Vh₀ᵀ)‖ ≤ ε2r) :
    ‖A t₁ - Uh₁ * Uh₁ᵀ * A t₁ * Vh₁ * Vh₁ᵀ‖
      ≤ ((M₂ * (1 + B) ^ 2 + M₁ ^ 2 * (1 + B)) / 6 + L * (M₁ * (1 + B)) / 2) * h ^ 3
        + 2 * ε2r * h + 2 * L * εr * h ^ 2 := by
  have hlt : t₀ < t₁ := by linarith
  have hA1 : ODESolution (fun t x => (1 : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (F t x)) A t₀ t₁ := by
    simpa only [one_apply_eq_self] using hA
  exact hs.capture hF hL ht₁ hh hA hA₀
    (IsC3Bounded.of_contDiff ContinuousLinearMap.norm_id_le hF2 hB hM₁ hM₂ hlt hA1)
    (IsC3Bounded.of_contDiff (isOrthProj_rightProj hs.orthVh₀).opNorm_le hF2 hB hM₁ hM₂ hlt
      (odeSolution_kField hs.kSol))
    (IsC3Bounded.of_contDiff (isOrthProj_leftProj hs.orthUh₀).opNorm_le hF2 hB hM₁ hM₂ hlt
      (odeSolution_lField hs.lSol))
    hεr hε2r

end Variant2Bases

/-- **Assumption 2.1(3) of arXiv 2403.02834**: at every matrix `Y = U S Vᵀ` with `S` invertible
and with `|ι|` orthonormal columns in `U` and `V`, that is at every point of the manifold `M_{|ι|}`
of matrices of rank `|ι|`, the normal part of `F` is `ε`-small:
`‖R(t, Y)‖ = ‖(I - P(Y)) F(t, Y)‖ = ‖(I - UUᵀ) F(t, Y) (I - VVᵀ)‖ ≤ ε`. -/
def NormalPartSmall (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ε : ℝ) : Prop :=
  ∀ (t : ℝ) (U : Matrix m ι ℝ) (V : Matrix n ι ℝ) (S : Matrix ι ι ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 →
    IsUnit S → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε

/-- **Lemma 4.2 of arXiv 2403.02834, under Assumptions 2.1 as stated in the paper.**  `F` is
`L`-Lipschitz, Assumption 2.1(3) holds at rank `r` with `εᵣ` and at the rank of the
pre-augmented bases (`2r` in the paper) with `ε₂ᵣ`, `S₀` is invertible, so that `Y₀ ∈ M_r`, and the
predictor (4.2a) lies in `M_{2r}`, that is, `Ŝ⋆ = Û₀ᵀ (Y₀ + (h/2) F(t₀, Y₀)) V̂₀` is invertible.
The paper uses the last fact without comment; `Variant2Bases.capture` does not need it.  Then

    ‖Ã(t₁) - Û₁Û₁ᵀ Ã(t₁) V̂₁V̂₁ᵀ‖ ≤ C₁ h³ + C₂ ε₂ᵣ h + C₃ εᵣ h²

with `C₁ = M₃/6 + L M₂/2`, `C₂ = 2`, `C₃ = 2 L`.  Regularity as in `Variant2Bases.capture`. -/
theorem lemma_4_2 {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ L εr ε2r M₂ M₃ h : ℝ}
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {Uh₀ : Matrix m k ℝ}
    {Vh₀ : Matrix n k ℝ} {Uh₁ : Matrix m k₁ ℝ} {Vh₁ : Matrix n l₁ ℝ} {K : ℝ → Matrix m k ℝ}
    {Lf : ℝ → Matrix n k ℝ} {A : ℝ → Matrix m n ℝ}
    (hs : Variant2Bases F t₀ t₁ U₀ S₀ V₀ Uh₀ Vh₀ Uh₁ Vh₁ K Lf)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hεr : NormalPartSmall F r εr)
    (hε2r : NormalPartSmall F k ε2r) (hS₀ : IsUnit S₀)
    (hSstar : IsUnit (Uh₀ᵀ * (U₀ * S₀ * V₀ᵀ + (h / 2) • F t₀ (U₀ * S₀ * V₀ᵀ)) * Vh₀))
    (ht₁ : t₁ = t₀ + h) (hh : 0 < h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hAreg : IsC3Bounded A t₀ t₁ M₂ M₃)
    (hKreg : IsC3Bounded (fun t => K t * Vh₀ᵀ) t₀ t₁ M₂ M₃)
    (hLreg : IsC3Bounded (fun t => Uh₀ * (Lf t)ᵀ) t₀ t₁ M₂ M₃) :
    ‖A t₁ - Uh₁ * Uh₁ᵀ * A t₁ * Vh₁ * Vh₁ᵀ‖
      ≤ (M₃ / 6 + L * M₂ / 2) * h ^ 3 + 2 * ε2r * h + 2 * L * εr * h ^ 2 := by
  refine hs.capture hF hL ht₁ hh hA hA₀ hAreg hKreg hLreg
    (hεr t₀ U₀ V₀ S₀ hs.orthU₀ hs.orthV₀ hS₀) ?_
  have e : predictor F t₀ h (U₀ * S₀ * V₀ᵀ) Uh₀ Vh₀
      = Uh₀ * (Uh₀ᵀ * (U₀ * S₀ * V₀ᵀ + (h / 2) • F t₀ (U₀ * S₀ * V₀ᵀ)) * Vh₀) * Vh₀ᵀ := by
    simp only [predictor, Matrix.mul_assoc]
  rw [e]
  exact hε2r _ Uh₀ Vh₀ _ hs.orthUh₀ hs.orthVh₀ hSstar

end Matrix


/-! ### Satisfiability -/

section Example

open scoped LeanDLRA.Frobenius
open LeanDLRA.MatrixKSL (kField lField odeSolution_affine)

/-- `U₀ = V₀ = e₁ ∈ ℝ^{2×1}` for the example. -/
private def exU : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The constant field `F ≡ C`, `C = [[0, 1], [1, 1]]`, for the example. -/
private def exC : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

/-- `Y₀ = e₁ e₁ᵀ`. -/
private def exY : Matrix (Fin 2) (Fin 2) ℝ := exU * exUᵀ

/-- The exact solution `Ã(t) = Y₀ + t C` of `Ã' = C`. -/
private def exA (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := exY + (t - 0) • exC

private theorem exU_orth : exUᵀ * exU = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [exU, Matrix.mul_apply, Fin.sum_univ_two]

/-- The hypotheses of `Variant2Bases` hold for the constant field `F ≡ C` on `2 × 2` matrices, with
`r = 1`, `Y₀ = e₁e₁ᵀ`, `S₀ = 1`, pre-augmented and new bases the identity (`2r = 2` columns), and
the affine K- and L-trajectories. -/
private theorem ex_bases :
    Variant2Bases (fun _ _ => exC) 0 1 exU (1 : Matrix (Fin 1) (Fin 1) ℝ) exU
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (fun t => exY + (t - 0) • exC) (fun t => exY + (t - 0) • exCᵀ) where
  orthU₀ := exU_orth
  orthV₀ := exU_orth
  orthUh₀ := by simp
  orthVh₀ := by simp
  spanU₀ := by simp
  spanFV := by simp
  spanV₀ := by simp
  spanFU := by simp
  kSol := by
    have e : kField (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
        exC) = fun _ _ => exC := by
      funext t K; simp [kField]
    rw [e]
    exact odeSolution_affine _ _ 0 1
  kStart := by simp [exY]
  lSol := by
    have e : lField (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
        exC) = fun _ _ => exCᵀ := by
      funext t K; simp [lField]
    rw [e]
    exact odeSolution_affine _ _ 0 1
  lStart := by simp [exY]
  orthUh₁ := by simp
  orthVh₁ := by simp
  spanUh₀ := by simp
  spanK := by simp
  spanVh₀ := by simp
  spanL := by simp

/-- **The hypotheses of `Variant2Bases.capture_of_contDiff` are jointly satisfiable** with a
nonzero field and a nonzero normal component at `Y₀`
(`εᵣ = ‖(I - e₁e₁ᵀ) C (I - e₁e₁ᵀ)‖ = ‖e₂e₂ᵀ‖ = 1`): the constant field `F ≡ C`
(`L = M₁ = M₂ = 0`, `B = ‖C‖`), `h = 1`. -/
example :
    ‖exA 1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * exA 1 *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖
      ≤ ((0 * (1 + ‖exC‖) ^ 2 + 0 ^ 2 * (1 + ‖exC‖)) / 6 + 0 * (0 * (1 + ‖exC‖)) / 2) * 1 ^ 3
        + 2 * ‖(1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) * exC *
            (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖ * 1
        + 2 * 0 * ‖(1 - exU * exUᵀ) * exC * (1 - exU * exUᵀ)‖ * 1 ^ 2 := by
  have hu : Function.uncurry (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => exC)
      = fun _ => exC := rfl
  exact ex_bases.capture_of_contDiff (L := 0) (B := ‖exC‖) (M₁ := 0) (M₂ := 0) (h := 1)
    (A := exA) (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (by rw [hu]; exact contDiff_const)
    (fun p => by rw [hu]; simp)
    (fun p => by rw [hu, iteratedFDeriv_const_of_ne (by norm_num)]; simp)
    (by norm_num) one_pos (odeSolution_affine exY exC 0 1) (by simp [exA, exY]) le_rfl le_rfl

end Example

end LeanDLRA.Literature.P2403_02834
