import LeanDLRA.OpenProblems.TensorNetworks.Part1Defs
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.CommutingProjectorTelescoping
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Open problems OP-TN-01, OP-TN-02

The projector-splitting theorems of OP-TN-01 (`tucker_ksl_local_error_inexact`,
`ttn_ksl_local_error`, `ttn_ksl_global_error`) are in
`LeanDLRA/Tensor/TTN/Abstract/ProjectorSplitting.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.OpenProblems.TensorNetworks

open LeanDLRA

section NestedKSL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end NestedKSL

section TTN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end TTN

section Defect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- OP-TN-02 (source: arXiv 2606.28169 §2.4; arXiv 2608.16994 §III.C–D), local error.  A BUG
step whose new bases miss part of the `K`- and `L`-step values (frozen classical–quantum bonds,
failed centre augmentation, rank-revealing thresholds): `‖(1 - P₁) YK(t₁)‖ ≤ ηK`,
`‖(1 - Q₁) YL(t₁)‖ ≤ ηL` instead of exact capture, and the Galerkin step starts at `P₁ Q₁ Y₀`.
Then the robust local error bound holds with the capture defect `θ = 2 h (4 L B h + ε) + ηK + ηL`,
i.e. the lost components enter additively. -/
theorem bug_local_error_of_defect {F : ℝ → E → E} {L B ε t₀ t₁ h ηK ηL : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀)
    (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁) (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) {Y₀ : E}
    {A YK YL YS : ℝ → E} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKdef : ‖(1 - P₁) (YK t₁)‖ ≤ ηK)
    (hKn : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hLs : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hLdef : ‖(1 - Q₁) (YL t₁)‖ ≤ ηL)
    (hLn : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = P₁ (Q₁ Y₀)) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + (2 * (h * (4 * L * B * h + ε)) + ηK + ηL))
      + (2 * (h * (4 * L * B * h + ε)) + ηK + ηL) := by
  have hK1 : ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * B * h + ε) + ηK := by
    refine kstep_capture_approx hF hL hB hP₁ hQ₀ ht₁ hh hA hK (hK₀.trans hA₀.symm)
      (K₁ := P₁ (YK t₁)) (hP₁.idem _) ?_ hKn
    have : ‖(1 - P₁) (YK t₁)‖ ≤ ηK := hKdef
    simpa using this
  have hL1 : ‖(1 - Q₁) (A t₁)‖ ≤ h * (4 * L * B * h + ε) + ηL := by
    refine kstep_capture_approx hF hL hB hQ₁ hP₀ ht₁ hh hA hLs (hL₀.trans hA₀.symm)
      (K₁ := Q₁ (YL t₁)) (hQ₁.idem _) ?_ hLn
    have : ‖(1 - Q₁) (YL t₁)‖ ≤ ηL := hLdef
    simpa using this
  have h3 := norm_sub_apply_apply_le (Q := Q₁) hP₁ (A t₁)
  exact galerkin_step_error (R := P₁ * Q₁) (hP₁.mul hQ₁ hc) hF hL hB ht₁ hh hA hS
    (by rw [hS₀, hA₀]; rfl) (θ := 2 * (h * (4 * L * B * h + ε)) + ηK + ηL)
    (by change ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ _; linarith)

/-- OP-TN-02 (source: arXiv 2608.16994 §III.D), norm drift.  If the field is norm conserving
(`⟪F(t, x), x⟫ = 0`, e.g. real form of a Schrödinger equation) but the augmented Galerkin
projector `P₁ Q₁` does not fix `Y₀`, the untruncated result loses at most the lost component:
`|‖YS(t₁)‖ - ‖Y₀‖| ≤ ‖Y₀ - P₁ Q₁ Y₀‖`. -/
theorem galerkin_norm_drift_le {F : ℝ → E → E} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    {P₁ Q₁ : E →L[ℝ] E} (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (hF : ∀ t x, ⟪F t x, x⟫ = 0) {Y₀ : E} {YS : ℝ → E}
    (hS : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = P₁ (Q₁ Y₀)) :
    |‖YS t₁‖ - ‖Y₀‖| ≤ ‖Y₀ - P₁ (Q₁ Y₀)‖ := by
  have hPQ : IsOrthProj (P₁ * Q₁) := hP₁.mul hQ₁ hc
  have h0 : (P₁ * Q₁) (YS t₀) = YS t₀ := by
    rw [hS₀]; exact hPQ.idem _
  have hn := ODESolution.galerkin_norm_eq' (F := F) hPQ hS h0 (fun t x _ => hF t x) t₁
    ⟨h01, le_rfl⟩
  rw [hn, hS₀]
  have h1 := abs_norm_sub_norm_le Y₀ (P₁ (Q₁ Y₀))
  rwa [abs_sub_comm] at h1

/-- OP-TN-02 (a) (source: arXiv 2606.28169 §2.4), frozen bond: if the bond is not augmented
(`P₁ = P₀`, `P₀ Y₀ = Y₀`), the capture defect of the `K`-step is at most `h` times the size of
the normal component `(1 - P₀) Q₀ F` along the `K`-step trajectory.  The scheme is therefore
first-order consistent only if this normal component is `O(h + ε)`. -/
theorem frozen_bond_defect_le {F : ℝ → E → E} {t₀ t₁ N : ℝ} {P₀ Q₀ : E →L[ℝ] E} {Y₀ : E}
    {YK : ℝ → E} (h01 : t₀ ≤ t₁) (hY₀ : P₀ Y₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hN : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) (Q₀ (F t (YK t)))‖ ≤ N) :
    ‖(1 - P₀) (YK t₁)‖ ≤ (t₁ - t₀) * N := by
  
  have hgc : ContinuousOn (fun t => (1 - P₀) (YK t)) (Icc t₀ t₁) :=
    (1 - P₀).continuous.comp_continuousOn hK.cont
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => (1 - P₀) (YK t))
      ((1 - P₀) (Q₀ (F t (YK t)))) (Ici t) t := fun t ht =>
    (1 - P₀).hasFDerivAt.comp_hasDerivWithinAt t (hK.deriv t ht)
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hN t₁ ⟨h01, le_rfl⟩
  have hg₀ : (1 - P₀) (YK t₀) = 0 := by simp [hK₀, hY₀]
  rwa [hg₀, sub_zero, mul_comm] at hmvt

end Defect

section Factored

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Factored

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Truncation

section Exactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Exactness

section Counterexample

open scoped Matrix LeanDLRA.Frobenius

end Counterexample

section Augmented

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Augmented

section CME

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end CME

end LeanDLRA.OpenProblems.TensorNetworks
