import LeanDLRA.Tensor.Tucker.Tangent
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.CommutingProjectorTelescoping

/-!
# Open problems OP-PA-01, OP-TN-04, OP-TN-10, OP-TN-13, OP-TN-21
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA

namespace TTNFrame

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end TTNFrame

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Inexact

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end Inexact

section TTN

variable {G : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end TTN

section TTNGlobal

variable {F : ℝ → E → E} {L B ε : ℝ}

end TTNGlobal

section Exact

variable {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ}

end Exact

section AugTTN

variable {G : ℝ → E → E} {L B ε ϑ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end AugTTN

section AugTTNGlobal

variable {F : ℝ → E → E} {L B ε ϑ : ℝ}

end AugTTNGlobal

section ParTTN

variable {G : ℝ → E → E} {L B Lt ε ϑ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

end ParTTN

section ParTTNGlobal

variable {F : ℝ → E → E} {L B Lt ε ϑ : ℝ}

end ParTTNGlobal

section DIndependent

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

private theorem clm_commute_of_apply {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hc : ∀ i j x, P i (P j x) = P j (P i x)) (i j : Fin d) : Commute (P i) (P j) :=
  ContinuousLinearMap.ext (hc i j)

private theorem modeProd_apply_proj {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hc : ∀ i j x, P i (P j x) = P j (P i x)) (j : Fin d) (y : E) :
    modeProd P (P j y) = P j (modeProd P y) :=
  (Commute.clm_apply (commute_modeProd (a := P j) fun i => clm_commute_of_apply hc j i) y).symm

private theorem modeProd_apply_compl {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hidem : ∀ i x, P i (P i x) = P i x) (hc : ∀ i j x, P i (P j x) = P j (P i x)) (j : Fin d)
    (y : E) : modeProd P ((1 - P j) y) = 0 := by
  rw [show (1 - P j) y = y - P j y by simp, map_sub, modeProd_apply_proj hc,
    apply_modeProd_eq_self hidem hc, sub_self]

/-- **Capture with a `d`-independent `ε`-constant** (source: research idea; sharpens
the `d ϑ` / `√d ϑ` capture constants of OP-TN-21 and OP-TN-04). For the rank-adaptive Tucker BUG
integrator (new bases `P₁ i ⊇ P₀ i` capturing the exact `K`-steps) and the normal bound
`‖(1 - T) F(t, Y₀)‖ ≤ ε` for the Tucker tangent projector `T = modeTangentProj P₀ Q₀`,
`‖A(t₁) - (∏ P₁ i) A(t₁)‖ ≤ h (ε + L B h) + √d L B h²`.  The linear (`d ϑ`,
`tucker_capture`) and Pythagorean (`√d ϑ`, `tucker_capture'`) telescoping bounds both carry
`d` resp. `√d` in front of `h ε`; here the normal part is treated once and only the
`O(h²)` basis-update defects, which lie in the mutually orthogonal blocks
`(1 - P₀ i) Q₀ i`, accumulate. -/
theorem aug_tucker_capture_dindep {d : ℕ} {P₀ Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E}
    {YK : Fin d → ℝ → E} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hP₁ : ∀ i, IsOrthProj (P₁ i))
    (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hc₀₁ : ∀ i j x, P₀ i (P₁ j x) = P₁ j (P₀ i x))
    (hc₁₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hcQ₁ : ∀ i x, Q₀ i (P₁ i x) = P₁ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x)
    (hnest : ∀ i x, P₁ i (P₀ i x) = P₀ i x) (hY₀ : ∀ i, P₀ i Y₀ = Y₀)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = Y₀)
    (hKcap : ∀ i, P₁ i (YK i t₁) = YK i t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖F t Y₀ - modeTangentProj P₀ Q₀ (F t Y₀)‖ ≤ ε) :
    ‖A t₁ - modeProd P₁ (A t₁)‖ ≤ h * (ε + L * B * h) + √(d : ℝ) * (L * B * h ^ 2) := by
  have _unused : _ ∧ _ := And.intro hc₀₁ hcQ₁
  have hle : t₀ ≤ t₁ := by linarith
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
  have hidem₁ : ∀ i x, P₁ i (P₁ i x) = P₁ i x := fun i => (hP₁ i).idem
  have hPi1 : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hP₁ hc₁₁
  have hT := modeTangentProj_isOrthProj hP₀ hQ₀ hc₀₀ hcQ₀ hQsub
  have hY₁ : ∀ i, P₁ i Y₀ = Y₀ := fun i => by
    have := hnest i Y₀
    rwa [hY₀ i] at this
  have hPiY : modeProd P₁ Y₀ = Y₀ := modeProd_apply_eq_self hY₁
  set w : E := A t₁ - Y₀ with hw
  have hgoal : A t₁ - modeProd P₁ (A t₁) = (1 - modeProd P₁) w := by
    simp only [map_sub, sub_apply, one_apply_eq_self, hw, hPiY]; abel
  -- the blocks
  set u : Fin d → E := fun i => (1 - P₀ i) (Q₀ i w) with hu
  have hPu : ∀ i j, j ≠ i → P₁ j (u i) = u i := by
    intro i j hji
    have h0 : P₀ j (u i) = u i := by
      simp only [hu, sub_apply, one_apply_eq_self, map_sub]
      rw [hc₀₀ j i, hQsub i j hji]
    rw [← h0, hnest j, h0]
  set e : Fin d → E := fun i => (1 - P₁ i) (u i) with he
  have hPe : ∀ i j, j ≠ i → P₁ j (e i) = e i := by
    intro i j hji
    simp only [he, sub_apply, one_apply_eq_self, map_sub]
    rw [hc₁₁ j i, hPu i j hji]
  have hPiu : ∀ i, (1 - modeProd P₁) (u i) = e i := by
    intro i
    have hfix : modeProd P₁ (P₁ i (u i)) = P₁ i (u i) := by
      refine modeProd_apply_eq_self fun j => ?_
      by_cases hji : j = i
      · subst hji; exact hidem₁ j _
      · rw [hc₁₁ j i, hPu i j hji]
    have hdec : u i = P₁ i (u i) + e i := by simp [he]
    have h0 : modeProd P₁ (e i) = 0 := modeProd_apply_compl hidem₁ hc₁₁ i _
    rw [sub_apply, one_apply_eq_self, show modeProd P₁ (u i) = P₁ i (u i) by
      conv_lhs => rw [hdec]
      rw [map_add, hfix, h0, add_zero]]
    simp [he]
  have hPi0w : (1 - modeProd P₁) (modeProd P₀ w) = 0 := by
    have : modeProd P₁ (modeProd P₀ w) = modeProd P₀ w := by
      refine modeProd_apply_eq_self fun i => ?_
      rw [← apply_modeProd_eq_self (P := P₀) (fun i => (hP₀ i).idem) hc₀₀ i w, hnest i]
    simp [this]
  have hdecw : w = (1 - modeTangentProj P₀ Q₀) w + modeProd P₀ w + ∑ i, u i := by
    have hTw : modeTangentProj P₀ Q₀ w = modeProd P₀ w + ∑ i, u i := by
      simp [modeTangentProj, hu]
    rw [sub_apply, one_apply_eq_self, hTw]; abel
  have hsplit : (1 - modeProd P₁) w = (1 - modeProd P₁) ((1 - modeTangentProj P₀ Q₀) w)
      + ∑ i, e i := by
    conv_lhs => rw [hdecw]
    rw [map_add, map_add, hPi0w, add_zero, map_sum]
    simp only [hPiu]
  -- the normal part
  have hnormal : ‖(1 - modeTangentProj P₀ Q₀) w‖ ≤ h * (ε + L * B * h) := by
    have hgc : ContinuousOn (fun t => (1 - modeTangentProj P₀ Q₀) (A t)) (Icc t₀ t₁) :=
      (1 - modeTangentProj P₀ Q₀).continuous.comp_continuousOn hA.cont
    have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => (1 - modeTangentProj P₀ Q₀) (A t))
        ((1 - modeTangentProj P₀ Q₀) (F t (A t))) (Ici t) t := fun t ht =>
      (1 - modeTangentProj P₀ Q₀).hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
    have hbd : ∀ t ∈ Ico t₀ t₁, ‖(1 - modeTangentProj P₀ Q₀) (F t (A t))‖
        ≤ ε + L * B * h := by
      intro t ht
      have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
      have hdec : (1 - modeTangentProj P₀ Q₀) (F t (A t))
          = (1 - modeTangentProj P₀ Q₀) (F t (A t) - F t Y₀)
            + (F t Y₀ - modeTangentProj P₀ Q₀ (F t Y₀)) := by
        simp only [map_sub, sub_apply, one_apply_eq_self]; abel
      have hAt : ‖A t - Y₀‖ ≤ B * h := by
        have := hA.norm_sub_le_of_bounded hB t htI
        rw [hA₀] at this
        have h2 : t - t₀ ≤ h := by linarith [htI.2]
        nlinarith
      rw [hdec]
      calc _ ≤ ‖(1 - modeTangentProj P₀ Q₀) (F t (A t) - F t Y₀)‖
            + ‖F t Y₀ - modeTangentProj P₀ Q₀ (F t Y₀)‖ := norm_add_le _ _
        _ ≤ ‖F t (A t) - F t Y₀‖ + ε :=
            add_le_add (hT.compl.norm_le _) (hε t htI)
        _ ≤ L * ‖A t - Y₀‖ + ε := add_le_add (hF t _ _) le_rfl
        _ ≤ L * (B * h) + ε := by gcongr
        _ = ε + L * B * h := by ring
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbd t₁ ⟨hle, le_rfl⟩
    rw [hA₀, hlen] at hmvt
    rw [mul_comm h]
    simpa [hw, hA₀, map_sub] using hmvt
  -- the basis-update defects
  have hedef : ∀ i, ‖e i‖ ≤ L * B * h ^ 2 := by
    intro i
    have hBK : IsBoundedField (fun t x => Q₀ i (F t x)) B :=
      hB.comp_contraction (Q₀ i) (hQ₀ i).norm_le
    set f : ℝ → E := fun t => Q₀ i (A t) - YK i t - (Q₀ i Y₀ - Y₀) with hf
    have hfc : ContinuousOn f (Icc t₀ t₁) :=
      ((Q₀ i).continuous.comp_continuousOn hA.cont).sub (hK i).cont |>.sub continuousOn_const
    have hfd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt f (Q₀ i (F t (A t)) - Q₀ i (F t (YK i t)))
        (Ici t) t := fun t ht =>
      (((Q₀ i).hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)).sub
        ((hK i).deriv t ht)).sub_const _
    have hBd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => L * B * (t - t₀) ^ 2)
        (2 * L * B * (x - t₀)) x := by
      intro x
      have := ((hasDerivAt_pow 2 (x - t₀)).comp x ((hasDerivAt_id x).sub_const t₀)).const_mul
        (L * B)
      refine this.congr_deriv ?_
      simp; ring
    have hbd : ∀ t ∈ Ico t₀ t₁, ‖Q₀ i (F t (A t)) - Q₀ i (F t (YK i t))‖
        ≤ 2 * L * B * (t - t₀) := by
      intro t ht
      have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
      have h1 : ‖A t - Y₀‖ ≤ B * (t - t₀) := by
        have := hA.norm_sub_le_of_bounded hB t htI
        rwa [hA₀] at this
      have h2 : ‖YK i t - Y₀‖ ≤ B * (t - t₀) := by
        have := (hK i).norm_sub_le_of_bounded hBK t htI
        rwa [hK₀ i] at this
      calc _ = ‖Q₀ i (F t (A t) - F t (YK i t))‖ := by rw [map_sub]
        _ ≤ ‖F t (A t) - F t (YK i t)‖ := (hQ₀ i).norm_le _
        _ ≤ L * ‖A t - YK i t‖ := hF t _ _
        _ ≤ L * (B * (t - t₀) + B * (t - t₀)) := by
            gcongr
            calc ‖A t - YK i t‖ = ‖(A t - Y₀) - (YK i t - Y₀)‖ := by congr 1; abel
              _ ≤ ‖A t - Y₀‖ + ‖YK i t - Y₀‖ := norm_sub_le _ _
              _ ≤ _ := add_le_add h1 h2
        _ = 2 * L * B * (t - t₀) := by ring
    have hf0 : ‖f t₀‖ ≤ L * B * (t₀ - t₀) ^ 2 := by
      simp [hf, hA₀, hK₀ i]
    have hfin := image_norm_le_of_norm_deriv_right_le_deriv_boundary hfc hfd hf0 hBd hbd
      (x := t₁) ⟨hle, le_rfl⟩
    rw [hlen] at hfin
    have hcap : (1 - P₁ i) (f t₁) = e i := by
      have h1 : (1 - P₁ i) (YK i t₁) = 0 := by simp [hKcap i]
      have h2 : (1 - P₁ i) Y₀ = 0 := by simp [hY₁ i]
      have h3 : e i = (1 - P₁ i) (Q₀ i w) := by
        simp only [he, hu, sub_apply, one_apply_eq_self, map_sub]
        rw [hnest i]; abel
      have h4 : f t₁ = Q₀ i w - (YK i t₁ - Y₀) := by
        simp only [hf, hw, map_sub]; abel
      rw [h4, map_sub (1 - P₁ i) (Q₀ i w), map_sub (1 - P₁ i) (YK i t₁), h1, h2]; simp [h3]
    calc ‖e i‖ = ‖(1 - P₁ i) (f t₁)‖ := by rw [hcap]
      _ ≤ ‖f t₁‖ := (hP₁ i).compl.norm_le _
      _ ≤ L * B * h ^ 2 := hfin
  have horth : ∀ i j, i ≠ j → ⟪e i, e j⟫ = 0 := by
    intro i j hij
    have h1 : P₁ j (e j) = 0 := by
      simp only [he, sub_apply, one_apply_eq_self, map_sub, hidem₁]; abel
    rw [← hPe i j (Ne.symm hij), (hP₁ j).symm, h1, inner_zero_right]
  have hsq : ‖∑ i, e i‖ ^ 2 = ∑ i, ‖e i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i, real_inner_self_eq_norm_sq]
    · intro j _ hji; exact horth i j (Ne.symm hji)
    · simp
  have hsum : ‖∑ i, e i‖ ≤ √(d : ℝ) * (L * B * h ^ 2) := by
    have hc0 : 0 ≤ L * B * h ^ 2 := by positivity
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [hsq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    calc ∑ i, ‖e i‖ ^ 2 ≤ ∑ _i : Fin d, (L * B * h ^ 2) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            gcongr
            exact hedef i
      _ = d * (L * B * h ^ 2) ^ 2 := by simp
  rw [hgoal, hsplit]
  calc _ ≤ ‖(1 - modeProd P₁) ((1 - modeTangentProj P₀ Q₀) w)‖ + ‖∑ i, e i‖ := norm_add_le _ _
    _ ≤ ‖(1 - modeTangentProj P₀ Q₀) w‖ + ‖∑ i, e i‖ :=
        add_le_add (hPi1.compl.norm_le _) le_rfl
    _ ≤ _ := add_le_add hnormal hsum

/-- **Local error of the rank-adaptive Tucker BUG integrator with a `d`-independent `ε`-constant**
(source: research idea; sharpens OP-TN-21, cf. OP-TN-10 (ii)). Under the hypotheses of
`aug_tucker_capture_dindep`, the Galerkin core step `YS' = (∏ P₁ i) F(t, YS)` from `Y₀` satisfies
`‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1)(B h + θ) + θ` with `θ = h (ε + L B h) + √d L B h²`, i.e.
`h (c₁ ε + c₂ h)` with `c₁ = 1 + O(h)` independent of `d` and `c₂ = O(√d)`. -/
theorem aug_tucker_local_error_dindep {d : ℕ} {P₀ Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E}
    {YK : Fin d → ℝ → E} {YS : ℝ → E} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hP₁ : ∀ i, IsOrthProj (P₁ i))
    (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hc₀₁ : ∀ i j x, P₀ i (P₁ j x) = P₁ j (P₀ i x))
    (hc₁₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hcQ₁ : ∀ i x, Q₀ i (P₁ i x) = P₁ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x)
    (hnest : ∀ i x, P₁ i (P₀ i x) = P₀ i x) (hY₀ : ∀ i, P₀ i Y₀ = Y₀)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = Y₀)
    (hKcap : ∀ i, P₁ i (YK i t₁) = YK i t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖F t Y₀ - modeTangentProj P₀ Q₀ (F t Y₀)‖ ≤ ε)
    (hS : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁) (hS₀ : YS t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) *
        (B * h + (h * (ε + L * B * h) + √(d : ℝ) * (L * B * h ^ 2))) +
      (h * (ε + L * B * h) + √(d : ℝ) * (L * B * h ^ 2)) := by
  have hPi1 : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hP₁ hc₁₁
  have hY₁ : ∀ i, P₁ i Y₀ = Y₀ := fun i => by
    have := hnest i Y₀
    rwa [hY₀ i] at this
  exact galerkin_step_error hPi1 hF hL hB ht₁ hh hA hS
    (by rw [hS₀, hA₀, modeProd_apply_eq_self hY₁])
    (aug_tucker_capture_dindep hF hL hB ht₁ hh hP₀ hQ₀ hP₁ hc₀₀ hc₀₁ hc₁₁ hcQ₀ hcQ₁ hQsub hnest
      hY₀ hA hA₀ hK hK₀ hKcap hε)

end DIndependent

end LeanDLRA
