import LeanDLRA.Stability.Conservation
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Matrix.Curvature

/-!
# Norm and energy balance of the BUG, projector-splitting and parallel BUG steps

For a field with `⟪F(t, x), x⟫ = 0` the exact flow conserves the norm. This file states what the
three basic integrators do with the norm in one step, on the core step structures `IsBUGStep`,
`IsKSLStep` and `IsParallelBUGStep`: the fixed-rank BUG step loses exactly the projection defect
of its starting value, the projector-splitting (KSL) step conserves norm and energy exactly, and
the untruncated parallel BUG step can only gain norm.

## Main results

* `IsBUGStep.norm_sq_add_defect_sq_and_defect_le`: for a norm-conserving field bounded by `B`,
  the result `Y₁ = YS t₁` satisfies `‖Y₁‖² + ‖Y₀ - P₁ Q₁ Y₀‖² = ‖Y₀‖²`, and
  `‖Y₀ - P₁ Q₁ Y₀‖ ≤ 2 B (t₁ - t₀)`.
* `IsBUGStep.norm_sq_add_defect`: the same statement with the additional hypothesis `0 ≤ B`.
* `IsKSLStep.norm_eq`: if the projectors commute, `Q₀ Y₀ = Y₀` and the field conserves the norm,
  the result `Y₁ = YL t₁` of one KSL step satisfies `‖Y₁‖ = ‖Y₀‖`, the backward S-step
  included.
* `IsKSLStep.energy_eq_of_skew`: for `F(t, x) = J ∇ℰ(x)` with `J` skew and commuting with both
  projectors, and commuting projectors, one KSL step gives `ℰ(Y₁) = ℰ(Y₀)`.
* `IsParallelBUGStep.norm_sq_eq`: for a norm-conserving field the untruncated parallel BUG output
  `Ŷ₁` satisfies `‖Ŷ₁‖² = ‖Y₀‖² + ‖(1 - P₀) YK(t₁)‖² + ‖(1 - Q₀) YL(t₁)‖²`.
* `IsParallelBUGStep.norm_sq_sub_le`: if the field is also bounded by `B` and the step has
  length `h`, `0 ≤ ‖Ŷ₁‖² - ‖Y₀‖² ≤ 2 (B h)²`.
* `parallelBUG_norm_drift`: with orthogonal truncations of tolerance `ϑ` and step sizes at most
  `h`, `-n ϑ² ≤ ‖Yₙ‖² - ‖Y₀‖² ≤ 2 n (B h)²`.

## References

* C. Lubich, I. V. Oseledets, *A projector-splitting integrator for dynamical low-rank
  approximation*, arXiv 1301.1058.
* G. Ceruti, J. Kusch, C. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, arXiv 2104.05247 (Theorems 6 and 7: norm and energy for the BUG integrator).
* arXiv 2306.17526, Sec. 6 (observed norm defect of the fixed-rank BUG integrator).
* G. Ceruti, J. Kusch, C. Lubich, *A parallel rank-adaptive integrator for dynamical low-rank
  approximation*, arXiv 2403.02834 (Remark 5.2).
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Norm defect of the fixed-rank BUG integrator, without a sign condition on the bound**
(the statement of `IsBUGStep.norm_sq_add_defect`, whose docstring names the sources, without the
hypothesis `0 ≤ B`). For a field with `⟪F(t, x), x⟫ = 0` that is bounded by `B`, one BUG step
loses exactly the projection defect of the starting value,
`‖Y₁‖² + ‖Y₀ - P₁ Q₁ Y₀‖² = ‖Y₀‖²`, and this defect is at most `2 B h`, `h = t₁ - t₀`. That `B`
is nonnegative is a consequence of the bound on the field (`IsBoundedField.nonneg`). -/
theorem IsBUGStep.norm_sq_add_defect_sq_and_defect_le {F : ℝ → E → E} {ε B : ℝ}
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (h01 : t₀ ≤ t₁)
    (hB : IsBoundedField F B) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ‖YS t₁‖ ^ 2 + ‖Y₀ - P₁ (Q₁ Y₀)‖ ^ 2 = ‖Y₀‖ ^ 2 ∧
      ‖Y₀ - P₁ (Q₁ Y₀)‖ ≤ 2 * B * (t₁ - t₀) := by
  have hPQ : IsOrthProj (P₁ * Q₁) := hs.projP₁.mul hs.projQ₁ hs.comm₁
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  have h0 : (P₁ * Q₁) (YS t₀) = YS t₀ := by
    rw [hs.sStart]; exact hPQ.idem _
  have hn := hs.sSol.galerkin_norm_eq (P := P₁ * Q₁) hPQ h0 (fun t _ => hF t _) t₁ ht₁
  rw [hs.sStart] at hn
  have hpy := hPQ.norm_sq_add Y₀
  have hmul : (P₁ * Q₁) Y₀ = P₁ (Q₁ Y₀) := rfl
  rw [hmul] at hpy
  refine ⟨by rw [hn]; exact hpy, ?_⟩
  have hh : t₁ = t₀ + (t₁ - t₀) := by ring
  have hK := hs.kSol.norm_sub_start_le_of_proj (F := F) hB hs.projQ₀ hh t₁ ht₁
  have hL := hs.lSol.norm_sub_start_le_of_proj (F := F) hB hs.projP₀ hh t₁ ht₁
  rw [hs.kStart] at hK
  rw [hs.lStart] at hL
  have e1 : (1 - P₁) Y₀ = (1 - P₁) (Y₀ - YK t₁) := by
    simp only [map_sub, sub_apply, one_apply_eq_self, hs.kCap]
    abel
  have e2 : (1 - Q₁) Y₀ = (1 - Q₁) (Y₀ - YL t₁) := by
    simp only [map_sub, sub_apply, one_apply_eq_self, hs.lCap]
    abel
  have hsplit : Y₀ - P₁ (Q₁ Y₀) = (1 - P₁) Y₀ + P₁ ((1 - Q₁) Y₀) := by
    simp only [map_sub, sub_apply, one_apply_eq_self]
    abel
  have b1 : ‖(1 - P₁) Y₀‖ ≤ B * (t₁ - t₀) := by
    rw [e1]
    refine (hs.projP₁.compl.norm_le _).trans ?_
    rw [norm_sub_rev]; exact hK
  have b2 : ‖P₁ ((1 - Q₁) Y₀)‖ ≤ B * (t₁ - t₀) := by
    refine (hs.projP₁.norm_le _).trans ?_
    rw [e2]
    refine (hs.projQ₁.compl.norm_le _).trans ?_
    rw [norm_sub_rev]; exact hL
  rw [hsplit]
  calc _ ≤ ‖(1 - P₁) Y₀‖ + ‖P₁ ((1 - Q₁) Y₀)‖ := norm_add_le _ _
    _ ≤ B * (t₁ - t₀) + B * (t₁ - t₀) := add_le_add b1 b2
    _ = 2 * B * (t₁ - t₀) := by ring

/-- **Norm defect of the fixed-rank BUG integrator** (source: OP-SB-03; arXiv 2306.17526,
Sec. 6, observed mass/energy defect of BUG).  The bound on the defect is a research idea.  For a
norm-conserving field, one BUG step loses exactly the projection defect of the starting value,
`‖Y₁‖² + ‖Y₀ - P₁ Q₁ Y₀‖² = ‖Y₀‖²`, and this defect is at most `2 B h`.
This is the recorded form of the statement, with the redundant hypothesis `0 ≤ B`;
`IsBUGStep.norm_sq_add_defect_sq_and_defect_le` is the same statement without it. -/
theorem IsBUGStep.norm_sq_add_defect {F : ℝ → E → E} {ε B : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (h01 : t₀ ≤ t₁)
    (hB : IsBoundedField F B) (hB₀ : 0 ≤ B) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ‖YS t₁‖ ^ 2 + ‖Y₀ - P₁ (Q₁ Y₀)‖ ^ 2 = ‖Y₀‖ ^ 2 ∧
      ‖Y₀ - P₁ (Q₁ Y₀)‖ ≤ 2 * B * (t₁ - t₀) := by
  have _ := hB₀
  exact IsBUGStep.norm_sq_add_defect_sq_and_defect_le hs h01 hB hF

/-- **Exact norm conservation of the projector-splitting integrator** (source: OP-SB-03, OP-SB-65;
Lubich–Oseledets, arXiv 1301.1058).  If `⟪F(t, Y), Y⟫ = 0`, the left and right
projectors commute and `Y₀` lies in the old right basis, then one KSL step (K-step, backward
S-step, L-step) conserves the norm exactly, `‖Y₁‖ = ‖Y₀‖`, for every step size and without
truncation. -/
theorem IsKSLStep.norm_eq {F : ℝ → E → E} {ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hY₀ : Q₀ Y₀ = Y₀) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ‖YL t₁‖ = ‖Y₀‖ := by
  have ht := h01
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hPQ : IsOrthProj (P₁ * Q₀) := hs.projP₁.mul hs.projQ₀ hc
  have hK := ODESolution.galerkin_norm_eq' (F := F) hs.projQ₀ hs.kSol (by rw [hs.kStart, hY₀])
    (fun t x _ => hF t x) t₁ ht₁
  rw [hs.kStart] at hK
  have hKQ : Q₀ (YK t₁) = YK t₁ := by
    have := hs.kSol.map_eq_of_idem hs.projQ₀.idem (by rw [hs.kStart, hY₀]) t₁ ht₁
    exact this
  have h0S : (P₁ * Q₀) (YS t₀) = YS t₀ := by
    rw [hs.sStart]; change P₁ (Q₀ (YK t₁)) = YK t₁; rw [hKQ, hs.kCap]
  -- the S-step
  have hS : ‖YS t₁‖ = ‖YS t₀‖ := by
    have hc0 : ContinuousOn (fun s => ‖YS s‖ ^ 2) (Icc t₀ t₁) := hs.sSol.cont.norm.pow 2
    have hconst := constant_of_has_deriv_right_zero hc0 fun t ht' => by
      obtain ⟨h1, h2⟩ := ksl_sStep_hasDerivWithinAt_norm_sq hs.projP₁ hs.projQ₀ hc hs.sSol h0S ht'
      rw [h2, hF] at h1
      simpa using h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hconst t₁ ht₁)
  have hSr : (P₁ * Q₀) (YS t₁) = YS t₁ := by
    have hy' : ODESolution (fun t x => -(P₁ * Q₀) (F t x)) YS t₀ t₁ := hs.sSol
    exact backward_mem_range hPQ hy' h0S t₁ ht₁
  have hSP : P₁ (YS t₁) = YS t₁ := by
    rw [← hSr]; change P₁ (P₁ (Q₀ (YS t₁))) = P₁ (Q₀ (YS t₁)); rw [hs.projP₁.idem]
  have hL := ODESolution.galerkin_norm_eq' (F := F) hs.projP₁ hs.lSol (by rw [hs.lStart, hSP])
    (fun t x _ => hF t x) t₁ ht₁
  rw [hL, hs.lStart, hS, hs.sStart, hK]

/-- **Exact energy conservation of the projector-splitting integrator for Hamiltonian fields**
(source: arXiv 2104.05247, Thms 6–7 transferred from BUG to KSL; OP-SB-65). Let
`F(t, x) = J ∇ℰ(x)` with `J` skew and commuting with both projectors, and let the projectors
commute. Then one KSL step conserves `ℰ` exactly, including the backward S-step. -/
theorem IsKSLStep.energy_eq_of_skew {F : ℝ → E → E} {ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) {ℰ : E → ℝ} {g : E → E}
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJP : ∀ z, J (P₁ z) = P₁ (J z)) (hJQ : ∀ z, J (Q₀ z) = Q₀ (J z))
    (hFJ : ∀ t x, F t x = J (g x)) :
    ℰ (YL t₁) = ℰ Y₀ := by
  have ht := h01
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hPQ : IsOrthProj (P₁ * Q₀) := hs.projP₁.mul hs.projQ₀ hc
  have hK : ℰ (YK t₁) = ℰ (YK t₀) :=
    ODESolution.galerkin_energy_eq_of_skew (F := F) hs.projQ₀ hℰ hJ hJQ hFJ hs.kSol t₁ ht₁
  -- S-step: it solves `y' = (P₁ Q₀) ((-J) ∇ℰ)`
  have hJP' : ∀ z, (-J) ((P₁ * Q₀) z) = (P₁ * Q₀) ((-J) z) := fun z => by
    change -J (P₁ (Q₀ z)) = P₁ (Q₀ (-J z))
    simp only [map_neg, hJP, hJQ]
  have hJ' : ∀ z, ⟪(-J) z, z⟫ = 0 := fun z => by simp [hJ z]
  have hy' : ODESolution (fun t x => (P₁ * Q₀) ((fun t x => (-J) (g x)) t x)) YS t₀ t₁ := by
    refine ⟨hs.sSol.cont, fun t ht' => ?_⟩
    have := hs.sSol.deriv t ht'
    convert this using 1
    simp [hFJ]
  have hS : ℰ (YS t₁) = ℰ (YS t₀) :=
    ODESolution.galerkin_energy_eq_of_skew (F := fun t x => (-J) (g x)) hPQ hℰ hJ' hJP'
      (fun _ _ => rfl) hy' t₁ ht₁
  have hL : ℰ (YL t₁) = ℰ (YL t₀) :=
    ODESolution.galerkin_energy_eq_of_skew (F := F) hs.projP₁ hℰ hJ hJP hFJ hs.lSol t₁ ht₁
  rw [hL, hs.lStart, hS, hs.sStart, hK, hs.kStart]

/-- Pythagoras for the untruncated parallel BUG update of a norm-conserving field. -/
private theorem parallelBUG_norm_sq_aux {F : ℝ → E → E}
    {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS) (ht : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 =
      ‖Y₀‖ ^ 2 + ‖(1 - P₀) (YK t₁)‖ ^ 2 + ‖(1 - Q₀) (YL t₁)‖ ^ 2 := by
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hPQ : IsOrthProj (P₀ * Q₀) := hs.orthP.mul hs.orthQ hs.comm
  have hK := hs.solK.map_eq_of_idem hs.orthQ.idem (by rw [hs.initK, hs.fixQ]) t₁ ht₁
  have hL := hs.solL.map_eq_of_idem hs.orthP.idem (by rw [hs.initL, hs.fixP]) t₁ ht₁
  have h0S : (P₀ * Q₀) (YS t₀) = YS t₀ := by
    rw [hs.initS]; change P₀ (Q₀ Y₀) = Y₀; rw [hs.fixQ, hs.fixP]
  have hS := ODESolution.map_eq_of_idem (R := P₀ * Q₀) hPQ.idem hs.solS h0S t₁ ht₁
  change P₀ (Q₀ (YS t₁)) = YS t₁ at hS
  have hSQ : Q₀ (YS t₁) = YS t₁ := by rw [← hS, ← hs.comm, hs.orthQ.idem]
  have hSP : P₀ (YS t₁) = YS t₁ := by rw [← hS, hs.orthP.idem]
  have hnS : ‖YS t₁‖ = ‖Y₀‖ := by
    have h := ODESolution.galerkin_norm_eq' (F := F) hPQ hs.solS h0S (fun t x _ => hF t x) t₁ ht₁
    rwa [hs.initS] at h
  have hnS2 : ‖YS t₁‖ ^ 2 = ‖Y₀‖ ^ 2 := by rw [hnS]
  have h1 : ⟪YS t₁, (1 - P₀) (YK t₁)⟫ = 0 := by
    have := hs.orthP.inner_sub_self (YS t₁) (YK t₁)
    rw [hSP] at this; simpa using this
  have h2 : ⟪YS t₁, (1 - Q₀) (YL t₁)⟫ = 0 := by
    have := hs.orthQ.inner_sub_self (YS t₁) (YL t₁)
    rw [hSQ] at this; simpa using this
  have hw : P₀ ((1 - Q₀) (YL t₁)) = (1 - Q₀) (YL t₁) := by
    simp only [sub_apply, one_apply_eq_self, map_sub, hs.comm, hL]
  have h3 : ⟪(1 - P₀) (YK t₁), (1 - Q₀) (YL t₁)⟫ = 0 := by
    have := hs.orthP.inner_sub_self ((1 - Q₀) (YL t₁)) (YK t₁)
    rw [hw] at this
    rw [real_inner_comm]; simpa using this
  have hnorm : ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 =
      ‖YS t₁‖ ^ 2 + ‖(1 - P₀) (YK t₁)‖ ^ 2 + ‖(1 - Q₀) (YL t₁)‖ ^ 2 := by
    unfold parallelBUG
    rw [add_assoc] at *
    have e1 := norm_add_sq_real (YS t₁) ((1 - P₀) (YK t₁) + (1 - Q₀) (YL t₁))
    have e2 := norm_add_sq_real ((1 - P₀) (YK t₁)) ((1 - Q₀) (YL t₁))
    rw [inner_add_right, h1, h2, h3] at *
    nlinarith [e1, e2]
  rw [hnorm, hnS2]

/-- Speed bounds for the two normal pieces of the parallel BUG update. -/
private theorem parallelBUG_normal_le {F : ℝ → E → E} {B : ℝ} (hB : IsBoundedField F B)
    {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS) (ht : t₀ ≤ t₁) :
    ‖(1 - P₀) (YK t₁)‖ ≤ B * (t₁ - t₀) ∧ ‖(1 - Q₀) (YL t₁)‖ ≤ B * (t₁ - t₀) := by
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have ha : ‖(1 - P₀) (YK t₁)‖ ≤ B * (t₁ - t₀) := by
    have hd : ∀ x ∈ Ico t₀ t₁, HasDerivWithinAt (fun s => (1 - P₀) (YK s))
        ((1 - P₀) (Q₀ (F x (YK x)))) (Ici x) x := fun x hx =>
      ((1 - P₀).hasFDerivAt.comp_hasDerivWithinAt x (hs.solK.deriv x hx))
    have := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := fun s => (1 - P₀) (YK s)) (f' := fun x => (1 - P₀) (Q₀ (F x (YK x))))
      ((1 - P₀).continuous.comp_continuousOn hs.solK.cont) hd
      (C := B) (fun x _ => (hs.orthP.compl.norm_le _).trans
        ((hs.orthQ.norm_le _).trans (hB _ _))) t₁ ht₁
    simpa [hs.initK, hs.fixP] using this
  have hb : ‖(1 - Q₀) (YL t₁)‖ ≤ B * (t₁ - t₀) := by
    have hd : ∀ x ∈ Ico t₀ t₁, HasDerivWithinAt (fun s => (1 - Q₀) (YL s))
        ((1 - Q₀) (P₀ (F x (YL x)))) (Ici x) x := fun x hx =>
      ((1 - Q₀).hasFDerivAt.comp_hasDerivWithinAt x (hs.solL.deriv x hx))
    have := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := fun s => (1 - Q₀) (YL s)) (f' := fun x => (1 - Q₀) (P₀ (F x (YL x))))
      ((1 - Q₀).continuous.comp_continuousOn hs.solL.cont) hd
      (C := B) (fun x _ => (hs.orthQ.compl.norm_le _).trans
        ((hs.orthP.norm_le _).trans (hB _ _))) t₁ ht₁
    simpa [hs.initL, hs.fixQ] using this
  exact ⟨ha, hb⟩

/-- **Exact norm gain of the parallel BUG integrator** (source: OP-CO-07, OP-SB-05;
arXiv 2403.02834, Remark 5.2). For a norm-conserving field, the untruncated parallel BUG
output satisfies `‖Ŷ₁‖² = ‖Y₀‖² + ‖(1 - P₀) YK(t₁)‖² + ‖(1 - Q₀) YL(t₁)‖²`, so it never
decreases the norm. -/
theorem IsParallelBUGStep.norm_sq_eq {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 =
      ‖Y₀‖ ^ 2 + ‖(1 - P₀) (YK t₁)‖ ^ 2 + ‖(1 - Q₀) (YL t₁)‖ ^ 2 := by
  exact parallelBUG_norm_sq_aux hs h01 hF

/-- **Quantitative norm drift of one parallel BUG step** (source: OP-CO-07; arXiv 2403.02834,
Remark 5.2). For a norm-conserving field bounded by `B`, the untruncated parallel BUG output
satisfies `0 ≤ ‖Ŷ₁‖² - ‖Y₀‖² ≤ 2 (B h)²`. -/
theorem IsParallelBUGStep.norm_sq_sub_le {F : ℝ → E → E} {B : ℝ} {P₀ Q₀ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS)
    (h01 : t₀ ≤ t₁) (hB : IsBoundedField F B) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    0 ≤ ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 - ‖Y₀‖ ^ 2 ∧
      ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 - ‖Y₀‖ ^ 2 ≤ 2 * (B * (t₁ - t₀)) ^ 2 := by
  have hB0 : 0 ≤ B := hB.nonneg
  have hh : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hid := parallelBUG_norm_sq_aux hs h01 hF
  obtain ⟨ha, hb⟩ := parallelBUG_normal_le hB hs h01
  have h1 : ‖(1 - P₀) (YK t₁)‖ ^ 2 ≤ (B * (t₁ - t₀)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have h2 : ‖(1 - Q₀) (YL t₁)‖ ^ 2 ≤ (B * (t₁ - t₀)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  constructor
  · rw [hid]; nlinarith [sq_nonneg ‖(1 - P₀) (YK t₁)‖, sq_nonneg ‖(1 - Q₀) (YL t₁)‖]
  · rw [hid]; nlinarith

/-- **Norm drift of the truncated parallel BUG integrator over many steps** (source: OP-CO-07;
arXiv 2403.02834, Remark 5.2). With orthogonal (SVD-type) truncations `Yₙ₊₁ = Tₙ Ŷₙ₊₁` of
tolerance `ϑ` and step sizes at most `h`, a norm-conserving field bounded by `B` gives
`-n ϑ² ≤ ‖Yₙ‖² - ‖Y₀‖² ≤ 2 n (B h)²`: truncation can only decrease the norm, the parallel update
can only increase it. -/
theorem parallelBUG_norm_drift {F : ℝ → E → E} {B ϑ h : ℝ} {τ : ℕ → ℝ} {N : ℕ}
    {P Q T : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParallelBUGStep F (P n) (Q n) (τ n) (τ (n + 1)) (Y n) (YK n) (YL n)
      (YS n))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1) ∧ τ (n + 1) - τ n ≤ h)
    (hT : ∀ n < N, IsOrthProj (T n))
    (hY : ∀ n < N, Y (n + 1) =
      T n (parallelBUG (P n) (Q n) (YK n (τ (n + 1))) (YL n (τ (n + 1))) (YS n (τ (n + 1)))))
    (htr : ∀ n < N, ‖Y (n + 1) -
      parallelBUG (P n) (Q n) (YK n (τ (n + 1))) (YL n (τ (n + 1))) (YS n (τ (n + 1)))‖ ≤ ϑ)
    (hB : IsBoundedField F B) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ∀ n ≤ N, -(n * ϑ ^ 2) ≤ ‖Y n‖ ^ 2 - ‖Y 0‖ ^ 2 ∧
      ‖Y n‖ ^ 2 - ‖Y 0‖ ^ 2 ≤ n * (2 * (B * h) ^ 2) := by
  intro n hn
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : k < N := hn
    obtain ⟨ihl, ihr⟩ := ih (Nat.le_of_lt hk)
    obtain ⟨hτ1, hτ2⟩ := hτ k hk
    have hB0 : 0 ≤ B := hB.nonneg
    have hid := parallelBUG_norm_sq_aux (hstep k hk) hτ1 hF
    obtain ⟨ha, hb⟩ := parallelBUG_normal_le hB (hstep k hk) hτ1
    set Yh := parallelBUG (P k) (Q k) (YK k (τ (k + 1))) (YL k (τ (k + 1))) (YS k (τ (k + 1)))
      with hYh
    have hpy := (hT k hk).norm_sq_add Yh
    have hd := htr k hk
    rw [hY k hk] at hd ⊢
    have hd' : ‖Yh - T k Yh‖ ≤ ϑ := by rw [norm_sub_rev]; exact hd
    have hd2 : ‖Yh - T k Yh‖ ^ 2 ≤ ϑ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd' 2
    have hBh : B * (τ (k + 1) - τ k) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith) hB0
    have hBh2 : (B * (τ (k + 1) - τ k)) ^ 2 ≤ (B * h) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hB0 (by linarith)) hBh 2
    have ha2 : ‖(1 - P k) (YK k (τ (k + 1)))‖ ^ 2 ≤ (B * (τ (k + 1) - τ k)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ha 2
    have hb2 : ‖(1 - Q k) (YL k (τ (k + 1)))‖ ^ 2 ≤ (B * (τ (k + 1) - τ k)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hnn : 0 ≤ ‖Yh - T k Yh‖ ^ 2 := sq_nonneg _
    have hnn2 : 0 ≤ ‖T k Yh‖ ^ 2 := sq_nonneg _
    have hna : 0 ≤ ‖(1 - P k) (YK k (τ (k + 1)))‖ ^ 2 := sq_nonneg _
    have hnb : 0 ≤ ‖(1 - Q k) (YL k (τ (k + 1)))‖ ^ 2 := sq_nonneg _
    push_cast
    constructor
    · nlinarith
    · nlinarith

end Abstract

section Matrix

open Matrix
open scoped LeanDLRA.Frobenius

variable {m n k r : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype r] [DecidableEq m]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

end Matrix

end LeanDLRA
