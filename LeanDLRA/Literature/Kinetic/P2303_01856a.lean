import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.Localization
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2303.01856: DLRA for Vlasov–Poisson with boundary

Uschmajew–Zeiser, *Dynamical low-rank approximation of the Vlasov–Poisson equation with piecewise
linear spatial boundary*, BIT 2024.  The paper has no numbered theorems: it derives the projector
splitting from a weak form ("more or less formal") and states two algorithms.  This module proves
that derivation and analyses the algorithms.  On `ℝ^d × ℝ^d`, `formA` and `formL` are the `a`, `ℓ`
of Eq. (5) for arbitrary s-finite measures `μx`, `μv` on `Ω_x`, `Ω_v` and `σ` on `∂Ω_x`.  A
piecewise linear boundary means disjoint pieces with constant normal.  Then `Γ⁻ = ⋃_ν Γ^ν × Ω_v^ν`
(`inflow_eq_iUnion`), the boundary integral is separable (`inflow_integral_tensor`), and `a` is a
finite sum of products of integrals (`formA_tensor`).  Restricting (5) to `T_{V⁰}`, `T_{X¹,V⁰}`,
`T_{X¹}` gives Eqs. (14), (15), (17) with the paper's matrices (`weak_K_restriction`,
`weak_S_restriction`, `weak_L_restriction`); `matAx_transpose`, `matBxx_transpose`,
`matBxx_nonpos` give the Friedrichs structure, the last one beyond the paper.
`isWeakSolution_iff` and `isKSLStep_weakField_iff` are the abstract form, with the sign flip of
the S-step.  Regularity is not assumed away: `isSeparable_of_lipschitz` derives all hypotheses for
bounded Lipschitz functions, i.e. linear FE, by Rademacher's theorem.  On the FE space,
`fe_weak_iff`, `fe_weak_iff_field` turn (5) into `M_x ḟ M_v = R(t, f)`, `integral_tensor_tensor`
identifies `L²(Ω)` with the type `MassSpace`, which has the inner product `M_x ⊗ M_v`, and
`FEData.weak_kRhs_iff`, `weak_sRhs_iff`, `weak_lRhs_iff`, `weak_sRhs_forward_iff` give Eqs.
(20a)–(20c), (21).  `IsAlg1Step` and `IsAlg2Step` are Algorithms 1 and 2.  For `δ = 0`, Algorithm
1 is a KSL step (`IsAlg1Step.isKSLStep`) and Algorithm 2 a rank-adaptive BUG step
(`IsAlg2Step.isRankAdaptiveBUGStep`) in that inner product, with the orthonormality of the output,
the exact initial value of the S-step, the truncation bound `norm_trunc_lt`, and the existence of
the minimal rank (`exists_minRank`).  The error bounds `local_error`, beyond the paper, are for
the real right-hand side: it is affine, so Lipschitz but unbounded, and
`FEData.exists_isBoundedOnTube` supplies a bound on a tube only.  The paper does not say why `δ`
is missing in (20b), (21).  For Algorithm 1 the three fields still add up to the tangent
projection of the stabilised field (`FEData.ksl_fields_sum`), though it is not KSL for that field;
Algorithm 2 is a Galerkin step of the unstabilised field in stabilised bases.
`local_error_stabilised` bounds both against the unstabilised solution, with an extra `O(Dd h)`
per step.  Differences from the paper: the Poisson solve is not formalized, so `M_{x,E_k}` is
assembled from a given frozen field; the CIP matrices are arbitrary; `N` is arbitrary instead of
`2 r₀`; `ϑ > 0` is required, since otherwise line 12 has no solution.  Not formalized: existence of
weak solutions, a global error with the self-consistent field, and mass, momentum and energy
conservation, which the paper leaves open. Non-vacuity: `exists_isAlg1Step`, `exists_isAlg2Step`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace LeanDLRA.Literature.P2303_01856

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Auxiliary for arXiv 2303.01856, Alg. 1.  The KSL analogue of the library's
`IsBUGStep.tubeExt`: a KSL step that starts `‖Y₀ - A s‖ + 4 B h < ρ` close to `A` stays in the
tube and is a KSL step of the extended field `tubeExt F A a b ρ`.  This is what makes the error
analysis applicable to the paper's affine, hence unbounded, right-hand side. -/
theorem ksl_tubeExt {F : ℝ → E → E} {A : ℝ → E} {ε B ρ a b s s₁ h : ℝ} {P₁ Q₀ : E →L[ℝ] E} {Y₀ : E}
    {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ s s₁ Y₀ YK YS YL)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (hh : 0 ≤ h) (ha : a ≤ s) (hb : s₁ ≤ b)
    (ht₁ : s₁ = s + h) (hA : ODESolution F A s s₁) (hsmall : ‖Y₀ - A s‖ + 4 * B * h < ρ) :
    IsKSLStep (tubeExt F A a b ρ) ε P₁ Q₀ s s₁ Y₀ YK YS YL := by
  have hd := norm_nonneg (Y₀ - A s)
  have hρ : 0 ≤ ρ := by nlinarith [mul_nonneg hB hh]
  have hss : s ≤ s₁ := by linarith
  have hFA := hFB.along hρ ha hb
  have hlen : s₁ - s = h := by linarith
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  -- K-substep
  have hKin := tube_trap hA hs.kSol hB hB hFA (hFB.comp_proj ha hb _ hs.projQ₀.norm_le)
    (by rw [hs.kStart, hlen]; nlinarith)
  have hKv := hs.kSol.norm_sub_start_le_of_tube (hFB.comp_proj ha hb _ hs.projQ₀.norm_le) hKin
    s₁ ⟨hss, le_rfl⟩
  rw [hs.kStart, hlen] at hKv
  -- S-substep
  have hSn : ∀ x, ‖-P₁ (Q₀ x)‖ ≤ ‖x‖ := fun x => by
    rw [norm_neg]; exact (hs.projP₁.norm_le _).trans (hs.projQ₀.norm_le _)
  have hS₀ : ‖YS s - A s‖ ≤ ‖Y₀ - A s‖ + B * h := by
    rw [hs.sStart]
    have hdec : YK s₁ - A s = (YK s₁ - Y₀) + (Y₀ - A s) := by abel
    rw [hdec]
    linarith [norm_add_le (YK s₁ - Y₀) (Y₀ - A s)]
  have hSin := tube_trap hA hs.sSol hB hB hFA
    (hFB.comp_proj ha hb (fun x => -P₁ (Q₀ x)) hSn) (by rw [hlen]; nlinarith)
  have hSv := hs.sSol.norm_sub_start_le_of_tube (hFB.comp_proj ha hb (fun x => -P₁ (Q₀ x)) hSn)
    hSin s₁ ⟨hss, le_rfl⟩
  rw [hlen] at hSv
  -- L-substep
  have hL₀ : ‖YL s - A s‖ ≤ ‖Y₀ - A s‖ + 2 * B * h := by
    rw [hs.lStart]
    have hdec : YS s₁ - A s = (YS s₁ - YS s) + (YS s - A s) := by abel
    rw [hdec]
    linarith [norm_add_le (YS s₁ - YS s) (YS s - A s)]
  have hLin := tube_trap hA hs.lSol hB hB hFA (hFB.comp_proj ha hb _ hs.projP₁.norm_le)
    (by rw [hlen]; nlinarith)
  have hsub : ∀ t ∈ Icc s s₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hpt : ∀ t ∈ Icc s s₁, ‖YK s₁ - A t‖ ≤ ρ := by
    intro t ht
    have hAt := hA.norm_sub_le hFA t ht
    have hdec : YK s₁ - A t = (YK s₁ - Y₀) + (Y₀ - A s) - (A t - A s) := by abel
    rw [hdec]
    have h1 : B * (t - s) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB
    calc _ ≤ ‖(YK s₁ - Y₀) + (Y₀ - A s)‖ + ‖A t - A s‖ := norm_sub_le _ _
      _ ≤ ‖YK s₁ - Y₀‖ + ‖Y₀ - A s‖ + ‖A t - A s‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ρ := by nlinarith
  exact
    { projP₁ := hs.projP₁
      projQ₀ := hs.projQ₀
      kSol := (odeSolution_comp_tubeExt_iff (fun x => Q₀ x) ha hb
        fun t ht => (hKin t (Ico_subset_Icc_self ht)).le).2 hs.kSol
      kStart := hs.kStart
      kCap := hs.kCap
      kNormal := fun t ht => by
        rw [tubeExt_eq (hsub t ht) (hpt t ht)]
        exact hs.kNormal t ht
      sSol := (odeSolution_comp_tubeExt_iff (fun x => -P₁ (Q₀ x)) ha hb
        fun t ht => (hSin t (Ico_subset_Icc_self ht)).le).2 hs.sSol
      sStart := hs.sStart
      lSol := (odeSolution_comp_tubeExt_iff (fun x => P₁ x) ha hb
        fun t ht => (hLin t (Ico_subset_Icc_self ht)).le).2 hs.lSol
      lStart := hs.lStart }

/-- Auxiliary for arXiv 2303.01856, Alg. 1.  Local error `h (11 L B h + ε)` of a KSL step (the
library's `IsKSLStep.local_error`) for a globally `L`-Lipschitz field that is bounded by `B`
only on a tube around the exact solution. -/
theorem ksl_local_error_of_tube {F : ℝ → E → E} {A : ℝ → E} {ε L B ρ t₀ t₁ h : ℝ}
    {P₁ Q₀ : E →L[ℝ] E} {Y₀ : E} {YK YS YL : ℝ → E}
    (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ t₁ ρ B) (hB : 0 ≤ B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) (hsmall : 4 * B * h < ρ) :
    ‖YL t₁ - A t₁‖ ≤ h * (11 * L * B * h + ε) := by
  have hρ : 0 ≤ ρ := by nlinarith [mul_nonneg hB hh]
  have hs' := ksl_tubeExt hs hFB hB hh le_rfl le_rfl ht₁ hA (by rw [hA₀]; simpa using hsmall)
  exact hs'.local_error (isLipschitzField_tubeExt (hF.isLipschitzOnTube _ _ _ _) hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) ht₁ hh (hA.tubeExt_self hρ) hA₀

/-- Auxiliary for arXiv 2303.01856, Sec. 3.  K-step capture lemma with a defect: if `Y' = Q F(t,
Y) + v`, `‖v‖ ≤ D`, the new basis captures `Y t₁`, and `A` and `Y` move at most `B h` and `C h`,
then `‖(1 - P) (A t₁)‖ ≤ h (L (B + 3 C) h + ε + D)`.  For `v = 0`, `C = B` this is the library's
bound `h (4 L B h + ε)` of `kstep_capture`, without a global bound on `F`. -/
theorem capture_core {F : ℝ → E → E} {A Y v : ℝ → E} {P Q : E →L[ℝ] E} {L B C D ε t₀ t₁ h : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hAv : ∀ t ∈ Icc t₀ t₁, ‖A t - A t₀‖ ≤ B * h)
    (hYc : ContinuousOn Y (Icc t₀ t₁))
    (hYd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt Y (Q (F t (Y t)) + v t) (Ici t) t)
    (hYv : ∀ t ∈ Icc t₀ t₁, ‖Y t - Y t₀‖ ≤ C * h) (hv : ∀ t ∈ Ico t₀ t₁, ‖v t‖ ≤ D)
    (hY₀ : Y t₀ = A t₀) (hcap : P (Y t₁) = Y t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P) ((1 - Q) (F t (Y t₁)))‖ ≤ ε) :
    ‖(1 - P) (A t₁)‖ ≤ h * (L * (B + 3 * C) * h + ε + D) := by
  have hle : t₀ ≤ t₁ := by linarith
  have ht₁m : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
  set g : ℝ → E := fun t => (1 - P) (A t - Y t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (1 - P).continuous.comp_continuousOn (hA.cont.sub hYc)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g
      ((1 - P) (F t (A t) - (Q (F t (Y t)) + v t))) (Ici t) t := fun t ht =>
    (1 - P).hasFDerivAt.comp_hasDerivWithinAt t ((hA.deriv t ht).sub (hYd t ht))
  have hPn : ∀ z : E, ‖(1 - P) z‖ ≤ ‖z‖ := fun z => by
    simpa using hP.norm_sub_le z
  have hQn : ∀ z : E, ‖Q z‖ ≤ ‖z‖ := hQ.norm_le
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖(1 - P) (F t (A t) - (Q (F t (Y t)) + v t))‖ ≤
      L * (B + 3 * C) * h + ε + D := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have hdec : (1 - P) (F t (A t) - (Q (F t (Y t)) + v t)) =
        (1 - P) (F t (A t) - F t (Y t₁)) + (1 - P) ((1 - Q) (F t (Y t₁))) +
          (1 - P) (Q (F t (Y t₁) - F t (Y t))) - (1 - P) (v t) := by
      simp only [map_sub, map_add, _root_.sub_apply, one_apply_eq_self]
      abel
    have h1 : ‖A t - Y t₁‖ ≤ (B + C) * h := by
      have e : A t - Y t₁ = (A t - A t₀) - (Y t₁ - Y t₀) := by rw [hY₀]; abel
      rw [e]
      have := norm_sub_le (A t - A t₀) (Y t₁ - Y t₀)
      linarith [hAv t htI, hYv t₁ ht₁m]
    have h2 : ‖Y t₁ - Y t‖ ≤ 2 * C * h := by
      have e : Y t₁ - Y t = (Y t₁ - Y t₀) - (Y t - Y t₀) := by abel
      rw [e]
      have := norm_sub_le (Y t₁ - Y t₀) (Y t - Y t₀)
      linarith [hYv t htI, hYv t₁ ht₁m]
    have t1 : ‖(1 - P) (F t (A t) - F t (Y t₁))‖ ≤ L * ((B + C) * h) :=
      (hPn _).trans ((hF t _ _).trans (mul_le_mul_of_nonneg_left h1 hL))
    have t2 := hε t htI
    have t3 : ‖(1 - P) (Q (F t (Y t₁) - F t (Y t)))‖ ≤ L * (2 * C * h) :=
      (hPn _).trans ((hQn _).trans ((hF t _ _).trans (mul_le_mul_of_nonneg_left h2 hL)))
    have t4 : ‖(1 - P) (v t)‖ ≤ D := (hPn _).trans (hv t ht)
    rw [hdec]
    calc _ ≤ ‖(1 - P) (F t (A t) - F t (Y t₁)) + (1 - P) ((1 - Q) (F t (Y t₁))) +
          (1 - P) (Q (F t (Y t₁) - F t (Y t)))‖ + ‖(1 - P) (v t)‖ := norm_sub_le _ _
      _ ≤ ‖(1 - P) (F t (A t) - F t (Y t₁))‖ + ‖(1 - P) ((1 - Q) (F t (Y t₁)))‖ +
          ‖(1 - P) (Q (F t (Y t₁) - F t (Y t)))‖ + ‖(1 - P) (v t)‖ := by
          gcongr; exact norm_add₃_le
      _ ≤ _ := by nlinarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ht₁m
  have hg₀ : g t₀ = 0 := by simp [hg, hY₀]
  have hg₁ : g t₁ = (1 - P) (A t₁) := by
    simp only [hg, map_sub, _root_.sub_apply, one_apply_eq_self, hcap]
    abel
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, sub_zero, hg₁, hlen] at hmvt
  linarith

/-- Abstract form of arXiv 2303.01856, Alg. 1 with stabilisation.  A KSL step in which the K-
and the L-step carry extra terms `a`, `b` (the paper's `-δ C_x K` and `-δ C_v L`), bounded by
`D` on the tube, has local error `h (L (11 B + 7 D) h + ε + 3 D)` against the exact solution of
the field without these terms.  For `D = 0` this is the library's `h (11 L B h + ε)`, under a
bound on the tube only.  The proof is the library's mean value argument with the defects added
in. -/
theorem perturbed_ksl_local_error {F : ℝ → E → E} {a b : E → E} {A YK YS YL : ℝ → E}
    {P₁ Q₀ : E →L[ℝ] E} {L B D ε ρ t₀ t₁ h : ℝ} {Y₀ : E} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A t₀ t₁ ρ B) (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (hD : ∀ t ∈ Icc t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖a x‖ ≤ D ∧ ‖b x‖ ≤ D)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x) + a x) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hLs : ODESolution (fun t x => P₁ (F t x) + b x) YL t₀ t₁) (hL₀ : YL t₀ = YS t₁)
    (hsmall : (4 * B + 2 * D) * h < ρ) :
    ‖YL t₁ - A t₁‖ ≤ h * (L * (11 * B + 7 * D) * h + ε + 3 * D) := by
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hDh : 0 ≤ D * h := mul_nonneg hD0 hh
  have hρ : 0 ≤ ρ := by nlinarith
  have hle : t₀ ≤ t₁ := by linarith
  have hlen : t₁ - t₀ = h := by linarith
  have ht₁m : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
  have hsub : ∀ t ∈ Ico t₀ t₁, t ∈ Icc t₀ t₁ := fun t ht => Ico_subset_Icc_self ht
  have hbd : ∀ t ∈ Icc t₀ t₁, 0 ≤ t - t₀ ∧ t - t₀ ≤ h := fun t ht => ⟨by linarith [ht.1], by
    linarith [ht.2]⟩
  have hFA := hFB.along hρ le_rfl le_rfl
  have hAv : ∀ t ∈ Icc t₀ t₁, ‖A t - A t₀‖ ≤ B * h := fun t ht =>
    (hA.norm_sub_le hFA t ht).trans (mul_le_mul_of_nonneg_left (hbd t ht).2 hB)
  have hBD : 0 ≤ B + D := add_nonneg hB hD0
  -- K-substep
  have hKb : ∀ t ∈ Ico t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖Q₀ (F t x) + a x‖ ≤ B + D := fun t ht x hx =>
    (norm_add_le _ _).trans (add_le_add ((hQ₀.norm_le _).trans (hFB t (hsub t ht) x hx))
      (hD t (hsub t ht) x hx).1)
  have hKin := tube_trap hA hK hB hBD hFA hKb (by rw [hK₀, hA₀, hlen]; simp; nlinarith)
  have hKv : ∀ t ∈ Icc t₀ t₁, ‖YK t - YK t₀‖ ≤ (B + D) * h := fun t ht =>
    (hK.norm_sub_start_le_of_tube hKb hKin t ht).trans
      (mul_le_mul_of_nonneg_left (hbd t ht).2 hBD)
  -- S-substep
  have hSb : ∀ t ∈ Ico t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖-P₁ (Q₀ (F t x))‖ ≤ B := fun t ht x hx => by
    rw [norm_neg]
    exact (hP₁.norm_le _).trans ((hQ₀.norm_le _).trans (hFB t (hsub t ht) x hx))
  have hSd : ‖YS t₀ - A t₀‖ ≤ (B + D) * h := by
    rw [hS₀, hA₀, ← hK₀]; exact hKv t₁ ht₁m
  have hSin := tube_trap hA hS hB hB hFA hSb (by rw [hlen]; nlinarith)
  have hSv : ∀ t ∈ Icc t₀ t₁, ‖YS t - YS t₀‖ ≤ B * h := fun t ht =>
    (hS.norm_sub_start_le_of_tube hSb hSin t ht).trans
      (mul_le_mul_of_nonneg_left (hbd t ht).2 hB)
  -- L-substep
  have hLb : ∀ t ∈ Ico t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖P₁ (F t x) + b x‖ ≤ B + D := fun t ht x hx =>
    (norm_add_le _ _).trans (add_le_add ((hP₁.norm_le _).trans (hFB t (hsub t ht) x hx))
      (hD t (hsub t ht) x hx).2)
  have hLd : ‖YL t₀ - A t₀‖ ≤ (2 * B + D) * h := by
    have e : YL t₀ - A t₀ = (YS t₁ - YS t₀) + (YS t₀ - A t₀) := by rw [hL₀]; abel
    rw [e]
    have := norm_add_le (YS t₁ - YS t₀) (YS t₀ - A t₀)
    nlinarith [hSv t₁ ht₁m]
  have hLin := tube_trap hA hLs hB hBD hFA hLb (by rw [hlen]; nlinarith)
  have hLv : ∀ t ∈ Icc t₀ t₁, ‖YL t - YL t₀‖ ≤ (B + D) * h := fun t ht =>
    (hLs.norm_sub_start_le_of_tube hLb hLin t ht).trans
      (mul_le_mul_of_nonneg_left (hbd t ht).2 hBD)
  -- capture
  have hcapt := capture_core (v := fun t => a (YK t)) (C := B + D) (D := D) hF hL hP₁ hQ₀ ht₁ hh hA
    hAv hK.cont (fun t ht => hK.deriv t ht) hKv
    (fun t ht => (hD t (hsub t ht) _ (hKin t (hsub t ht)).le).1) (hK₀.trans hA₀.symm) hcap hε
  -- the mean value argument
  set g : ℝ → E := fun t => P₁ (YK t) + (YS t - YS t₀) + (YL t - YL t₀) - P₁ (A t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (((P₁.continuous.comp_continuousOn hK.cont).add (hS.cont.sub continuousOn_const)).add
      (hLs.cont.sub continuousOn_const)).sub (P₁.continuous.comp_continuousOn hA.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g
      (P₁ (Q₀ (F t (YK t)) + a (YK t)) + (-P₁ (Q₀ (F t (YS t)))) +
        (P₁ (F t (YL t)) + b (YL t)) - P₁ (F t (A t))) (Ici t) t := fun t ht =>
    (((P₁.hasFDerivAt.comp_hasDerivWithinAt t (hK.deriv t ht)).add
      ((hS.deriv t ht).sub_const _)).add ((hLs.deriv t ht).sub_const _)).sub
      (P₁.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht))
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖P₁ (Q₀ (F t (YK t)) + a (YK t)) + (-P₁ (Q₀ (F t (YS t)))) +
      (P₁ (F t (YL t)) + b (YL t)) - P₁ (F t (A t))‖ ≤ L * (7 * B + 4 * D) * h + 2 * D := by
    intro t ht
    have htI := hsub t ht
    have hdec : P₁ (Q₀ (F t (YK t)) + a (YK t)) + (-P₁ (Q₀ (F t (YS t)))) +
        (P₁ (F t (YL t)) + b (YL t)) - P₁ (F t (A t)) =
        P₁ (Q₀ (F t (YK t) - F t (YS t))) + P₁ (F t (YL t) - F t (A t)) + P₁ (a (YK t)) +
          b (YL t) := by
      simp only [map_add, map_sub]
      abel
    have h1 : ‖YK t - YS t‖ ≤ (3 * B + 2 * D) * h := by
      have e : YK t - YS t = (YK t - YK t₀) - (YK t₁ - YK t₀) - (YS t - YS t₀) := by
        rw [hS₀]; abel
      rw [e]
      have a1 := norm_sub_le ((YK t - YK t₀) - (YK t₁ - YK t₀)) (YS t - YS t₀)
      have a2 := norm_sub_le (YK t - YK t₀) (YK t₁ - YK t₀)
      nlinarith [hKv t htI, hKv t₁ ht₁m, hSv t htI]
    have h2 : ‖YL t - A t‖ ≤ (4 * B + 2 * D) * h := by
      have e : YL t - A t = (YL t - YL t₀) + (YS t₁ - YS t₀) + (YK t₁ - YK t₀) - (A t - A t₀) := by
        rw [hL₀, hS₀, hK₀, hA₀]; abel
      rw [e]
      have a1 := norm_sub_le ((YL t - YL t₀) + (YS t₁ - YS t₀) + (YK t₁ - YK t₀)) (A t - A t₀)
      have a2 := norm_add₃_le (a := YL t - YL t₀) (b := YS t₁ - YS t₀) (c := YK t₁ - YK t₀)
      nlinarith [hLv t htI, hSv t₁ ht₁m, hKv t₁ ht₁m, hAv t htI]
    have t1 : ‖P₁ (Q₀ (F t (YK t) - F t (YS t)))‖ ≤ L * ((3 * B + 2 * D) * h) :=
      (hP₁.norm_le _).trans ((hQ₀.norm_le _).trans ((hF t _ _).trans
        (mul_le_mul_of_nonneg_left h1 hL)))
    have t2 : ‖P₁ (F t (YL t) - F t (A t))‖ ≤ L * ((4 * B + 2 * D) * h) :=
      (hP₁.norm_le _).trans ((hF t _ _).trans (mul_le_mul_of_nonneg_left h2 hL))
    have t3 : ‖P₁ (a (YK t))‖ ≤ D :=
      (hP₁.norm_le _).trans (hD t htI _ (hKin t htI).le).1
    have t4 : ‖b (YL t)‖ ≤ D := (hD t htI _ (hLin t htI).le).2
    rw [hdec]
    calc _ ≤ ‖P₁ (Q₀ (F t (YK t) - F t (YS t))) + P₁ (F t (YL t) - F t (A t)) + P₁ (a (YK t))‖ +
          ‖b (YL t)‖ := norm_add_le _ _
      _ ≤ ‖P₁ (Q₀ (F t (YK t) - F t (YS t)))‖ + ‖P₁ (F t (YL t) - F t (A t))‖ +
          ‖P₁ (a (YK t))‖ + ‖b (YL t)‖ := by gcongr; exact norm_add₃_le
      _ ≤ _ := by nlinarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ht₁m
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀, hA₀]
  have hg₁ : g t₁ = YL t₁ - P₁ (A t₁) := by
    simp only [hg, hcap, hS₀, hL₀]
    abel
  rw [hg₀, sub_zero, hg₁, hlen] at hmvt
  have hdec : YL t₁ - A t₁ = (YL t₁ - P₁ (A t₁)) - (1 - P₁) (A t₁) := by
    simp only [_root_.sub_apply, one_apply_eq_self]
    abel
  rw [hdec]
  have hfin := norm_sub_le (YL t₁ - P₁ (A t₁)) ((1 - P₁) (A t₁))
  have : h * (L * (B + 3 * (B + D)) * h + ε + D) + (L * (7 * B + 4 * D) * h + 2 * D) * h =
      h * (L * (11 * B + 7 * D) * h + ε + 3 * D) := by ring
  linarith

/-- Abstract form of arXiv 2303.01856, Alg. 2 with stabilisation.  An augmented BUG step whose
K- and L-steps carry extra terms bounded by `D` on the tube, followed by the Galerkin S-step of
the field *without* these terms, has the bound of `galerkin_step_error` with `θ = 2 h (L (4 B +
3 D) h + ε + D)`.  Here `YS` starts at `Y₀`, which the augmented bases capture. -/
theorem perturbed_bug_local_error {F : ℝ → E → E} {a b : E → E} {A YK YL YS : ℝ → E}
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {L B D ε ρ t₀ t₁ h : ℝ} {Y₀ : E} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A t₀ t₁ ρ B) (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (hD : ∀ t ∈ Icc t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖a x‖ ≤ D ∧ ‖b x‖ ≤ D)
    (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x) + a x) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hKε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hLs : ODESolution (fun t x => P₀ (F t x) + b x) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hLcap : Q₁ (YL t₁) = YL t₁)
    (hLε : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = Y₀)
    (hfix : P₁ (Q₁ Y₀) = Y₀) (hsmall : (2 * B + D) * h < ρ) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) *
        (B * h + 2 * (h * (L * (4 * B + 3 * D) * h + ε + D))) +
      2 * (h * (L * (4 * B + 3 * D) * h + ε + D)) := by
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hDh : 0 ≤ D * h := mul_nonneg hD0 hh
  have hρ : 0 ≤ ρ := by nlinarith
  have hle : t₀ ≤ t₁ := by linarith
  have hlen : t₁ - t₀ = h := by linarith
  have hsub : ∀ t ∈ Ico t₀ t₁, t ∈ Icc t₀ t₁ := fun t ht => Ico_subset_Icc_self ht
  have hbd : ∀ t ∈ Icc t₀ t₁, 0 ≤ t - t₀ ∧ t - t₀ ≤ h := fun t ht => ⟨by linarith [ht.1], by
    linarith [ht.2]⟩
  have hFA := hFB.along hρ le_rfl le_rfl
  have hAv : ∀ t ∈ Icc t₀ t₁, ‖A t - A t₀‖ ≤ B * h := fun t ht =>
    (hA.norm_sub_le hFA t ht).trans (mul_le_mul_of_nonneg_left (hbd t ht).2 hB)
  have hBD : 0 ≤ B + D := add_nonneg hB hD0
  have hKb : ∀ t ∈ Ico t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖Q₀ (F t x) + a x‖ ≤ B + D := fun t ht x hx =>
    (norm_add_le _ _).trans (add_le_add ((hQ₀.norm_le _).trans (hFB t (hsub t ht) x hx))
      (hD t (hsub t ht) x hx).1)
  have hKin := tube_trap hA hK hB hBD hFA hKb (by rw [hK₀, hA₀, hlen]; simp; nlinarith)
  have hKv : ∀ t ∈ Icc t₀ t₁, ‖YK t - YK t₀‖ ≤ (B + D) * h := fun t ht =>
    (hK.norm_sub_start_le_of_tube hKb hKin t ht).trans
      (mul_le_mul_of_nonneg_left (hbd t ht).2 hBD)
  have hLb : ∀ t ∈ Ico t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖P₀ (F t x) + b x‖ ≤ B + D := fun t ht x hx =>
    (norm_add_le _ _).trans (add_le_add ((hP₀.norm_le _).trans (hFB t (hsub t ht) x hx))
      (hD t (hsub t ht) x hx).2)
  have hLin := tube_trap hA hLs hB hBD hFA hLb (by rw [hL₀, hA₀, hlen]; simp; nlinarith)
  have hLv : ∀ t ∈ Icc t₀ t₁, ‖YL t - YL t₀‖ ≤ (B + D) * h := fun t ht =>
    (hLs.norm_sub_start_le_of_tube hLb hLin t ht).trans
      (mul_le_mul_of_nonneg_left (hbd t ht).2 hBD)
  have hSb : ∀ t ∈ Ico t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ → ‖P₁ (Q₁ (F t x))‖ ≤ B := fun t ht x hx =>
    (hP₁.norm_le _).trans ((hQ₁.norm_le _).trans (hFB t (hsub t ht) x hx))
  have hSin := tube_trap hA hS hB hB hFA hSb (by rw [hS₀, hA₀, hlen]; simp; nlinarith)
  have hcapP := capture_core (v := fun t => a (YK t)) (C := B + D) (D := D) hF hL hP₁ hQ₀ ht₁ hh hA
    hAv hK.cont (fun t ht => hK.deriv t ht) hKv
    (fun t ht => (hD t (hsub t ht) _ (hKin t (hsub t ht)).le).1) (hK₀.trans hA₀.symm) hKcap hKε
  have hcapQ := capture_core (v := fun t => b (YL t)) (C := B + D) (D := D) hF hL hQ₁ hP₀ ht₁ hh hA
    hAv hLs.cont (fun t ht => hLs.deriv t ht) hLv
    (fun t ht => (hD t (hsub t ht) _ (hLin t (hsub t ht)).le).2) (hL₀.trans hA₀.symm) hLcap hLε
  have e1 : L * (B + 3 * (B + D)) = L * (4 * B + 3 * D) := by ring
  rw [e1] at hcapP hcapQ
  have hθ : ‖A t₁ - (P₁ * Q₁) (A t₁)‖ ≤ 2 * (h * (L * (4 * B + 3 * D) * h + ε + D)) := by
    have := norm_sub_apply_apply_le (Q := Q₁) hP₁ (A t₁)
    change ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ _
    linarith
  have hS' : ODESolution (fun t x => (P₁ * Q₁) (tubeExt F A t₀ t₁ ρ t x)) YS t₀ t₁ :=
    (odeSolution_comp_tubeExt_iff (fun x => P₁ (Q₁ x)) le_rfl le_rfl
      fun t ht => (hSin t (hsub t ht)).le).2 hS
  exact galerkin_step_error (hP₁.mul hQ₁ hc) (isLipschitzField_tubeExt
    (hF.isLipschitzOnTube _ _ _ _) hL hρ) hL (isBoundedField_tubeExt hFB hB hρ) ht₁ hh
    (hA.tubeExt_self hρ) hS' (by rw [hS₀, hA₀]; exact hfix.symm) hθ

section Weak

variable [CompleteSpace E]

/-- The Riesz representative `F(t, y) ∈ E` of a weak residual `w ↦ res t y w`, where in the
notation of arXiv 2303.01856, Eq. (5), `res t y w = ℓ(w) - a(t, y, w)`. -/
noncomputable def weakField (res : ℝ → E → E →L[ℝ] ℝ) (t : ℝ) (y : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (res t y)

/-- The defining property of the Riesz representative. -/
lemma inner_weakField (res : ℝ → E → E →L[ℝ] ℝ) (t : ℝ) (y w : E) :
    ⟪weakField res t y, w⟫ = res t y w :=
  InnerProductSpace.toDual_symm_apply

/-- `y` solves the weak problem with residual `res` restricted to the test space `range P`: `y'
∈ range P` and `⟪y', w⟫ = res(t, y, w)` for all `w ∈ range P`, which is `(∂_t y, w) + a(t; y, w)
= ℓ(w)` of arXiv 2303.01856, Eq. (5), on a test space.  Derivatives are right derivatives as in
`ODESolution`. -/
structure IsWeakSolution (res : ℝ → E → E →L[ℝ] ℝ) (P : E →L[ℝ] E) (y : ℝ → E) (a b : ℝ) :
    Prop where
  cont : ContinuousOn y (Icc a b)
  deriv : ∀ t ∈ Ico a b, ∃ y', HasDerivWithinAt y y' (Ici t) t ∧ P y' = y' ∧
    ∀ w, P w = w → ⟪y', w⟫ = res t (y t) w

/-- arXiv 2303.01856, Secs. 2.2–2.4, abstract core: at a fixed time the weak form restricted to
`range P` has the unique solution `y' = P F(t, y)`, where `F` is the Riesz representative. -/
theorem weak_iff_proj {P : E →L[ℝ] E} (hP : IsOrthProj P) (res : ℝ → E → E →L[ℝ] ℝ) (t : ℝ)
    (y y' : E) :
    (P y' = y' ∧ ∀ w, P w = w → ⟪y', w⟫ = res t y w) ↔ y' = P (weakField res t y) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine hP.eq_apply_of_galerkin h1 fun w hw => ?_
    rw [inner_sub_left, h2 w hw, inner_weakField, sub_self]
  · rintro rfl
    refine ⟨hP.idem _, fun w hw => ?_⟩
    rw [hP.inner_apply_left_of_mem _ hw, inner_weakField]

/-- arXiv 2303.01856, Secs. 2.2–2.4, abstract core: the weak problem on `range P` is the
projected ODE `y' = P F(t, y)`. -/
theorem isWeakSolution_iff {P : E →L[ℝ] E} (hP : IsOrthProj P) (res : ℝ → E → E →L[ℝ] ℝ)
    {y : ℝ → E} {a b : ℝ} :
    IsWeakSolution res P y a b ↔ ODESolution (fun t x => P (weakField res t x)) y a b := by
  constructor
  · intro h
    refine ⟨h.cont, fun t ht => ?_⟩
    obtain ⟨y', hd, h1, h2⟩ := h.deriv t ht
    rw [← (weak_iff_proj hP res t (y t) y').1 ⟨h1, h2⟩]
    exact hd
  · intro h
    refine ⟨h.cont, fun t ht => ⟨_, h.deriv t ht, ?_⟩⟩
    exact (weak_iff_proj hP res t (y t) _).2 rfl

/-- Flipping the sign of the residual flips the sign of the Riesz representative. -/
lemma weakField_neg (res : ℝ → E → E →L[ℝ] ℝ) (t : ℝ) (y : E) :
    weakField (fun t y => -res t y) t y = -weakField res t y := by
  simp [weakField]

/-- arXiv 2303.01856, Secs. 2.2–2.4, abstract core.  A KSL step for the Riesz field is exactly:
the weak form on `range Q₀` (`T_{V⁰}`), the weak form with all signs of the right-hand side
flipped on `range (P₁ Q₀)` (`T_{X¹,V⁰}`), and the weak form on `range P₁` (`T_{X¹}`), chained by
the initial values and the capture condition.  The commutativity of `P₁`, `Q₀` holds for the
left and right projectors of the paper (`massLeft_massRight_comm`). -/
theorem isKSLStep_weakField_iff {res : ℝ → E → E →L[ℝ] ℝ} {ε t₀ t₁ : ℝ} {P₁ Q₀ : E →L[ℝ] E}
    {Y₀ : E} {YK YS YL : ℝ → E} (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) :
    IsKSLStep (weakField res) ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL ↔
      (IsWeakSolution res Q₀ YK t₀ t₁ ∧ YK t₀ = Y₀ ∧ P₁ (YK t₁) = YK t₁ ∧
        (∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (weakField res t (YK t₁)))‖ ≤ ε)) ∧
      (IsWeakSolution (fun t y => -res t y) (P₁ * Q₀) YS t₀ t₁ ∧ YS t₀ = YK t₁) ∧
      (IsWeakSolution res P₁ YL t₀ t₁ ∧ YL t₀ = YS t₁) := by
  have hPQ := hP₁.mul hQ₀ hc
  have hS : ∀ t x, (P₁ * Q₀) (weakField (fun t y => -res t y) t x) =
      -P₁ (Q₀ (weakField res t x)) := fun t x => by
    rw [weakField_neg, map_neg]; rfl
  simp only [isWeakSolution_iff hQ₀, isWeakSolution_iff hPQ, isWeakSolution_iff hP₁, hS]
  constructor
  · intro h
    exact ⟨⟨h.kSol, h.kStart, h.kCap, h.kNormal⟩, ⟨h.sSol, h.sStart⟩, h.lSol, h.lStart⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩
    exact ⟨hP₁, hQ₀, h1, h2, h3, h4, h5, h6, h7, h8⟩

end Weak

end Abstract

section Mass

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The `L²(Ω_x × Ω_v)` pairing `tr(Aᵀ M_x B M_v)` of the coefficient matrices of two tensor FE
functions, see `integral_tensor_tensor` (arXiv 2303.01856, Sec. 3). -/
noncomputable def massInner (Mx : Matrix m m ℝ) (Mv : Matrix n n ℝ) (A B : Matrix m n ℝ) : ℝ :=
  Matrix.trace (Aᵀ * Mx * B * Mv)

/-- The pairing written with the Kronecker product `M_x ⊗ M_vᵀ`. -/
lemma massInner_eq_dotProduct (Mx : Matrix m m ℝ) (Mv : Matrix n n ℝ) (A B : Matrix m n ℝ) :
    massInner Mx Mv A B =
      (fun p : m × n => A p.1 p.2) ⬝ᵥ ((Mx ⊗ₖ Mvᵀ) *ᵥ fun p : m × n => B p.1 p.2) := by
  simp only [massInner, Matrix.trace, Matrix.diag, dotProduct, Matrix.mulVec, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- The pairing is positive definite if both mass matrices are. -/
lemma massInner_self_pos {Mx : Matrix m m ℝ} {Mv : Matrix n n ℝ} (hx : Mx.PosDef) (hv : Mv.PosDef)
    {A : Matrix m n ℝ} (hA : A ≠ 0) : 0 < massInner Mx Mv A A := by
  rw [massInner_eq_dotProduct]
  have hvt : Mvᵀ = Mv := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hv.isHermitian.eq
  have h : (Mx ⊗ₖ Mvᵀ).PosDef := by rw [hvt]; exact hx.kronecker hv
  have hne : (fun p : m × n => A p.1 p.2) ≠ 0 := by
    intro h0
    exact hA (Matrix.ext fun i j => congrFun h0 (i, j))
  simpa using h.dotProduct_mulVec_pos hne

/-- A real positive definite matrix is symmetric. -/
lemma transpose_eq_of_posDef {a : Type*} {M : Matrix a a ℝ} (h : M.PosDef) : Mᵀ = M := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h.isHermitian.eq

/-- Coefficient matrices `f` of tensor FE functions.  This type synonym of `Matrix m n ℝ`
carries the inner product `⟪A, B⟫ = tr(Aᵀ M_x B M_v)`, the `M_x ⊗ M_v` inner product of arXiv
2303.01856, Sec. 3, so that the abstract theory of the library applies with mass-matrix
orthonormal bases. -/
def MassSpace (_Mx : Matrix m m ℝ) (_Mv : Matrix n n ℝ) : Type _ := Matrix m n ℝ

namespace MassSpace

variable (Mx : Matrix m m ℝ) (Mv : Matrix n n ℝ)

noncomputable instance : AddCommGroup (MassSpace Mx Mv) :=
  inferInstanceAs (AddCommGroup (Matrix m n ℝ))

noncomputable instance : Module ℝ (MassSpace Mx Mv) :=
  inferInstanceAs (Module ℝ (Matrix m n ℝ))

omit [Fintype m] [Fintype n] in
instance [Finite m] [Finite n] : FiniteDimensional ℝ (MassSpace Mx Mv) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix m n ℝ))

/-- The identification of a matrix with the corresponding element of `MassSpace`. -/
def ofMat : Matrix m n ℝ ≃ₗ[ℝ] MassSpace Mx Mv := LinearEquiv.refl ℝ _

variable {Mx Mv}

noncomputable instance instCore [hx : Fact Mx.PosDef] [hv : Fact Mv.PosDef] :
    InnerProductSpace.Core ℝ (MassSpace Mx Mv) where
  inner A B := massInner Mx Mv (ofMat Mx Mv |>.symm A) (ofMat Mx Mv |>.symm B)
  conj_inner_symm A B := by
    have hxt : Mxᵀ = Mx := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hx.out.isHermitian.eq
    have hvt : Mvᵀ = Mv := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hv.out.isHermitian.eq
    simp only [conj_trivial, massInner]
    rw [← Matrix.trace_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hxt, hvt]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  re_inner_nonneg A := by
    simp only [RCLike.re_to_real]
    by_cases hA : (ofMat Mx Mv).symm A = 0
    · simp [hA, massInner]
    · exact (massInner_self_pos hx.out hv.out hA).le
  add_left A B C := by
    simp [massInner, Matrix.add_mul, Matrix.trace_add]
  smul_left A B c := by
    simp [massInner, Matrix.trace_smul]
  definite A h := by
    by_contra hA
    have hne : (ofMat Mx Mv).symm A ≠ 0 := by simpa using hA
    exact (massInner_self_pos hx.out hv.out hne).ne' h

variable [Fact Mx.PosDef] [Fact Mv.PosDef]

noncomputable instance : NormedAddCommGroup (MassSpace Mx Mv) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := instCore)

noncomputable instance : InnerProductSpace ℝ (MassSpace Mx Mv) :=
  InnerProductSpace.ofCore instCore.toCore

instance : CompleteSpace (MassSpace Mx Mv) := FiniteDimensional.complete ℝ _

/-- The inner product of `MassSpace` is `tr(Aᵀ M_x B M_v)`. -/
lemma inner_ofMat (A B : Matrix m n ℝ) :
    ⟪ofMat Mx Mv A, ofMat Mx Mv B⟫ = Matrix.trace (Aᵀ * Mx * B * Mv) := rfl


variable {r : Type*} [Fintype r]

/-- The left projector `Z ↦ X Xᵀ M_x Z`, the orthogonal projector of `MassSpace` onto `T_X` if
`Xᵀ M_x X = 1` (`isOrthProj_massLeft`, `massLeft_eq_self_iff`). -/
noncomputable def massLeft (X : Matrix m r ℝ) : MassSpace Mx Mv →L[ℝ] MassSpace Mx Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z => ofMat Mx Mv (X * Xᵀ * Mx * (ofMat Mx Mv).symm Z)
      map_add' := fun Z W => by simp [Matrix.mul_add]
      map_smul' := fun c Z => by simp [Matrix.mul_smul] }

/-- The right projector `Z ↦ Z M_v V Vᵀ`, the orthogonal projector of `MassSpace` onto `T_V` if
`Vᵀ M_v V = 1` (`isOrthProj_massRight`, `massRight_eq_self_iff`). -/
noncomputable def massRight (V : Matrix n r ℝ) : MassSpace Mx Mv →L[ℝ] MassSpace Mx Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z => ofMat Mx Mv ((ofMat Mx Mv).symm Z * Mv * V * Vᵀ)
      map_add' := fun Z W => by simp [Matrix.add_mul]
      map_smul' := fun c Z => by simp [Matrix.smul_mul] }

/-- `massLeft` on a matrix. -/
lemma massLeft_ofMat (X : Matrix m r ℝ) (A : Matrix m n ℝ) :
    massLeft X (ofMat Mx Mv A) = ofMat Mx Mv (X * Xᵀ * Mx * A) := rfl

/-- `massRight` on a matrix. -/
lemma massRight_ofMat (V : Matrix n r ℝ) (A : Matrix m n ℝ) :
    massRight V (ofMat Mx Mv A) = ofMat Mx Mv (A * Mv * V * Vᵀ) := rfl

/-- arXiv 2303.01856, Sec. 3: for an `M_x`-orthonormal basis, `massLeft X` is an orthogonal
projector of `MassSpace`. -/
theorem isOrthProj_massLeft {X : Matrix m r ℝ} [DecidableEq r] (hX : Xᵀ * Mx * X = 1) :
    IsOrthProj (massLeft X : MassSpace Mx Mv →L[ℝ] MassSpace Mx Mv) where
  idem Z := by
    obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
    simp only [massLeft_ofMat]
    congr 1
    calc X * Xᵀ * Mx * (X * Xᵀ * Mx * A) = X * (Xᵀ * Mx * X) * Xᵀ * Mx * A := by
          simp only [Matrix.mul_assoc]
      _ = X * Xᵀ * Mx * A := by rw [hX, Matrix.mul_one]
  symm Z W := by
    obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
    obtain ⟨B, rfl⟩ := (ofMat Mx Mv).surjective W
    simp only [massLeft_ofMat, inner_ofMat, Matrix.transpose_mul, Matrix.transpose_transpose,
      transpose_eq_of_posDef (Fact.out : Mx.PosDef), Matrix.mul_assoc]

/-- arXiv 2303.01856, Sec. 3: for an `M_v`-orthonormal basis, `massRight V` is an orthogonal
projector of `MassSpace`. -/
theorem isOrthProj_massRight {V : Matrix n r ℝ} [DecidableEq r] (hV : Vᵀ * Mv * V = 1) :
    IsOrthProj (massRight V : MassSpace Mx Mv →L[ℝ] MassSpace Mx Mv) where
  idem Z := by
    obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
    simp only [massRight_ofMat]
    congr 1
    calc A * Mv * V * Vᵀ * Mv * V * Vᵀ = A * Mv * V * (Vᵀ * Mv * V) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = A * Mv * V * Vᵀ := by rw [hV, Matrix.mul_one]
  symm Z W := by
    obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
    obtain ⟨B, rfl⟩ := (ofMat Mx Mv).surjective W
    simp only [massRight_ofMat, inner_ofMat, Matrix.transpose_mul, Matrix.transpose_transpose,
      transpose_eq_of_posDef (Fact.out : Mv.PosDef)]
    calc Matrix.trace (V * (Vᵀ * (Mv * Aᵀ)) * Mx * B * Mv)
        = Matrix.trace (V * (Vᵀ * Mv * Aᵀ * Mx * B * Mv)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Vᵀ * Mv * Aᵀ * Mx * B * Mv) * V) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Vᵀ * Mv) * (Aᵀ * Mx * B * Mv * V)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Aᵀ * Mx * B * Mv * V) * (Vᵀ * Mv)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Aᵀ * Mx * (B * Mv * V * Vᵀ) * Mv) := by simp only [Matrix.mul_assoc]

/-- `massLeft X` fixes `X B`. -/
lemma massLeft_fix {X : Matrix m r ℝ} [DecidableEq r] (hX : Xᵀ * Mx * X = 1) (B : Matrix r n ℝ) :
    massLeft X (ofMat Mx Mv (X * B)) = ofMat Mx Mv (X * B) := by
  rw [massLeft_ofMat]
  congr 1
  calc X * Xᵀ * Mx * (X * B) = X * (Xᵀ * Mx * X) * B := by simp only [Matrix.mul_assoc]
    _ = X * B := by rw [hX, Matrix.mul_one]

/-- `massRight V` fixes `B Vᵀ`. -/
lemma massRight_fix {V : Matrix n r ℝ} [DecidableEq r] (hV : Vᵀ * Mv * V = 1)
    (B : Matrix m r ℝ) : massRight V (ofMat Mx Mv (B * Vᵀ)) = ofMat Mx Mv (B * Vᵀ) := by
  rw [massRight_ofMat]
  congr 1
  calc B * Vᵀ * Mv * V * Vᵀ = B * (Vᵀ * Mv * V) * Vᵀ := by simp only [Matrix.mul_assoc]
    _ = B * Vᵀ := by rw [hV, Matrix.mul_one]

/-- Left and right projectors commute. -/
lemma massLeft_massRight_comm (X : Matrix m r ℝ) {r' : Type*} [Fintype r'] (V : Matrix n r' ℝ)
    (Z : MassSpace Mx Mv) : massLeft X (massRight V Z) = massRight V (massLeft X Z) := by
  obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
  simp only [massRight_ofMat, massLeft_ofMat]
  congr 1
  simp only [Matrix.mul_assoc]

end MassSpace

end Mass

section FE

open MassSpace
open scoped LeanDLRA.Frobenius

/-- The matrices of the semi-discretisation of arXiv 2303.01856, Sec. 3: mass matrices,
transport, field and boundary matrices, the assembled inflow data `G(t)` and the CIP matrices.
The field matrices are frozen in time: Algs. 1–2 assemble them once per step after the Poisson
solve.  Here all entries are arbitrary, `assemble` gives the actual integrals. -/
structure FEData (ι κ m n : Type*) where
  Mx : Matrix m m ℝ
  Mv : Matrix n n ℝ
  Tx : ι → Matrix m m ℝ
  MxE : ι → Matrix m m ℝ
  Mvk : ι → Matrix n n ℝ
  Tv : ι → Matrix n n ℝ
  MxΓ : κ → Matrix m m ℝ
  MvΩ : κ → Matrix n n ℝ
  G : ℝ → Matrix m n ℝ
  Cx : Matrix m m ℝ
  Cv : Matrix n n ℝ

/-- `⟨M⟩_X = Xᵀ M X`, arXiv 2303.01856, Sec. 3. -/
def ang {a r : Type*} [Fintype a] [Fintype r] (X : Matrix a r ℝ) (M : Matrix a a ℝ) :
    Matrix r r ℝ := Xᵀ * M * X

variable {ι κ m n r r' : Type*} [Fintype ι] [Fintype κ] [Fintype m] [Fintype n] [Fintype r]
  [Fintype r']

namespace FEData

variable (D : FEData ι κ m n)

/-- The linear part of `rhs`. -/
noncomputable def op (f : Matrix m n ℝ) : Matrix m n ℝ :=
  -∑ k, (D.Tx k * f * (D.Mvk k)ᵀ - D.MxE k * f * (D.Tv k)ᵀ) + ∑ ν, D.MxΓ ν * f * (D.MvΩ ν)ᵀ

/-- The right-hand side `R(t, f)` of the full semi-discrete problem `M_x ḟ M_v = R(t, f)`: `R(t,
f) = -∑_k (T_{x,k} f M_{v,k}ᵀ - M_{x,E_k} f T_{v,k}ᵀ) + ∑_ν M_{x,Γ^ν} f M_{v,Ω^ν}ᵀ - G(t)`. The
paper does not display it; `fe_weak_iff` derives it from Eq. (5), and `rhs_mul`,
`transpose_mul_rhs_mul`, `rhs_transpose_mul` recover the paper's Eqs. (20a)–(20c) from it. -/
noncomputable def rhs (t : ℝ) (f : Matrix m n ℝ) : Matrix m n ℝ := D.op f - D.G t

/-- The right-hand side of arXiv 2303.01856, Eq. (20a), for `δ = 0`, with `G_x(t) = G(t) V`. -/
noncomputable def kRhs (V : Matrix n r ℝ) (t : ℝ) (K : Matrix m r ℝ) : Matrix m r ℝ :=
  -∑ k, (D.Tx k * K * (ang V (D.Mvk k))ᵀ - D.MxE k * K * (ang V (D.Tv k))ᵀ)
    + ∑ ν, D.MxΓ ν * K * (ang V (D.MvΩ ν))ᵀ - D.G t * V

/-- The right-hand side of arXiv 2303.01856, Eq. (20b), with `G_S = Xᵀ G(t) V`.  Its negative is
the right-hand side of the forward S-equation (21). -/
noncomputable def sRhs (X : Matrix m r ℝ) (V : Matrix n r' ℝ) (t : ℝ) (S : Matrix r r' ℝ) :
    Matrix r r' ℝ :=
  ∑ k, (ang X (D.Tx k) * S * (ang V (D.Mvk k))ᵀ - ang X (D.MxE k) * S * (ang V (D.Tv k))ᵀ)
    - ∑ ν, ang X (D.MxΓ ν) * S * (ang V (D.MvΩ ν))ᵀ + Xᵀ * D.G t * V

/-- The right-hand side of arXiv 2303.01856, Eq. (20c), for `δ = 0`, with `G_v(t) = G(t)ᵀ X`. -/
noncomputable def lRhs (X : Matrix m r ℝ) (t : ℝ) (L : Matrix n r ℝ) : Matrix n r ℝ :=
  -∑ k, (D.Mvk k * L * (ang X (D.Tx k))ᵀ - D.Tv k * L * (ang X (D.MxE k))ᵀ)
    + ∑ ν, D.MvΩ ν * L * (ang X (D.MxΓ ν))ᵀ - (D.G t)ᵀ * X

/-- arXiv 2303.01856, Eq. (20a): `R(t, K Vᵀ) V` is the right-hand side of the K-equation. -/
lemma rhs_mul (V : Matrix n r ℝ) (t : ℝ) (K : Matrix m r ℝ) :
    D.rhs t (K * Vᵀ) * V = D.kRhs V t K := by
  simp only [rhs, op, kRhs, ang, Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.sum_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- arXiv 2303.01856, Eq. (20b): `Xᵀ R(t, X S Vᵀ) V` is minus the right-hand side of the
S-equation. -/
lemma transpose_mul_rhs_mul (X : Matrix m r ℝ) (V : Matrix n r' ℝ) (t : ℝ) (S : Matrix r r' ℝ) :
    Xᵀ * D.rhs t (X * S * Vᵀ) * V = -D.sRhs X V t S := by
  simp only [rhs, op, sRhs, ang, Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.sum_mul,
    Matrix.mul_sub, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_sum,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- arXiv 2303.01856, Eq. (20c): `R(t, X Lᵀ)ᵀ X` is the right-hand side of the L-equation. -/
lemma rhs_transpose_mul (X : Matrix m r ℝ) (t : ℝ) (L : Matrix n r ℝ) :
    (D.rhs t (X * Lᵀ))ᵀ * X = D.lRhs X t L := by
  simp only [rhs, op, lRhs, ang, Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.sum_mul,
    Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_neg, Matrix.transpose_sum,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end FEData

variable [DecidableEq m] [DecidableEq n]

/-- The map `K ↦ K Vᵀ` from the factor to `MassSpace`. -/
noncomputable def liftK (Mx : Matrix m m ℝ) (Mv : Matrix n n ℝ) [Fact Mx.PosDef] [Fact Mv.PosDef]
    (V : Matrix n r ℝ) : Matrix m r ℝ →L[ℝ] MassSpace Mx Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun K => ofMat Mx Mv (K * Vᵀ)
      map_add' := fun A B => by simp [Matrix.add_mul]
      map_smul' := fun c A => by simp [Matrix.smul_mul] }

/-- The map `S ↦ X S Vᵀ` from the factor to `MassSpace`. -/
noncomputable def liftS (Mx : Matrix m m ℝ) (Mv : Matrix n n ℝ) [Fact Mx.PosDef] [Fact Mv.PosDef]
    (X : Matrix m r ℝ) (V : Matrix n r' ℝ) : Matrix r r' ℝ →L[ℝ] MassSpace Mx Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun S => ofMat Mx Mv (X * S * Vᵀ)
      map_add' := fun A B => by simp [Matrix.add_mul, Matrix.mul_add]
      map_smul' := fun c A => by simp [Matrix.smul_mul, Matrix.mul_smul] }

/-- The map `L ↦ X Lᵀ` from the factor to `MassSpace`. -/
noncomputable def liftL (Mx : Matrix m m ℝ) (Mv : Matrix n n ℝ) [Fact Mx.PosDef] [Fact Mv.PosDef]
    (X : Matrix m r ℝ) : Matrix n r ℝ →L[ℝ] MassSpace Mx Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => ofMat Mx Mv (X * Lᵀ)
      map_add' := fun A B => by simp [Matrix.mul_add]
      map_smul' := fun c A => by simp [Matrix.mul_smul] }

namespace FEData

variable (D : FEData ι κ m n)

/-- The K-equation (20a) solved for `K̇`: `M_x K̇ = kRhs - δ C_x K` (`mx_mul_kField`). -/
noncomputable def kField (V : Matrix n r ℝ) (δ t : ℝ) (K : Matrix m r ℝ) : Matrix m r ℝ :=
  D.Mx⁻¹ * (D.kRhs V t K - δ • (D.Cx * K))

/-- The L-equation (20c) solved for `L̇`: `M_v L̇ = lRhs - δ C_v L` (`mv_mul_lField`). -/
noncomputable def lField (X : Matrix m r ℝ) (δ t : ℝ) (L : Matrix n r ℝ) : Matrix n r ℝ :=
  D.Mv⁻¹ * (D.lRhs X t L - δ • (D.Cv * L))

variable [Fact D.Mx.PosDef] [Fact D.Mv.PosDef]

/-- The unstabilised field `F(t, f) = M_x⁻¹ R(t, f) M_v⁻¹`, the Riesz representative of the weak
residual in `MassSpace` (`riesz`, `weakField_res`). -/
noncomputable def field (t : ℝ) (Y : MassSpace D.Mx D.Mv) : MassSpace D.Mx D.Mv :=
  ofMat D.Mx D.Mv (D.Mx⁻¹ * D.rhs t ((ofMat D.Mx D.Mv).symm Y) * D.Mv⁻¹)

/-- `F` represents the weak residual: `⟪W, F(t, Y)⟫ = tr(Wᵀ R(t, Y))`. -/
lemma riesz (W Y : Matrix m n ℝ) (t : ℝ) :
    ⟪ofMat D.Mx D.Mv W, D.field t (ofMat D.Mx D.Mv Y)⟫ = Matrix.trace (Wᵀ * D.rhs t Y) := by
  have hx : D.Mx * D.Mx⁻¹ = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Fact.out : D.Mx.PosDef).isUnit)
  have hv : D.Mv⁻¹ * D.Mv = 1 := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Fact.out : D.Mv.PosDef).isUnit)
  simp only [field, LinearEquiv.symm_apply_apply, inner_ofMat]
  congr 1
  calc Wᵀ * D.Mx * (D.Mx⁻¹ * D.rhs t Y * D.Mv⁻¹) * D.Mv
      = Wᵀ * (D.Mx * D.Mx⁻¹) * D.rhs t Y * (D.Mv⁻¹ * D.Mv) := by simp only [Matrix.mul_assoc]
    _ = Wᵀ * D.rhs t Y := by rw [hx, hv, Matrix.mul_one, Matrix.mul_one]

/-- The operator `Y ↦ M_x⁻¹ C_x Y` of the stabilisation term of the K-step. -/
noncomputable def stabX : MassSpace D.Mx D.Mv →L[ℝ] MassSpace D.Mx D.Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => ofMat D.Mx D.Mv (D.Mx⁻¹ * D.Cx * (ofMat D.Mx D.Mv).symm Y)
      map_add' := fun A B => by simp [Matrix.mul_add]
      map_smul' := fun c A => by simp [Matrix.mul_smul] }

/-- The operator `Y ↦ Y C_vᵀ M_v⁻¹` of the stabilisation term of the L-step (`C_v` is symmetric
in the paper, but this is not needed). -/
noncomputable def stabV : MassSpace D.Mx D.Mv →L[ℝ] MassSpace D.Mx D.Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => ofMat D.Mx D.Mv ((ofMat D.Mx D.Mv).symm Y * D.Cvᵀ * D.Mv⁻¹)
      map_add' := fun A B => by simp [Matrix.add_mul]
      map_smul' := fun c A => by simp [Matrix.smul_mul] }

/-- `stabX` on a matrix. -/
lemma stabX_ofMat (A : Matrix m n ℝ) :
    D.stabX (ofMat D.Mx D.Mv A) = ofMat D.Mx D.Mv (D.Mx⁻¹ * D.Cx * A) := rfl

/-- `stabV` on a matrix. -/
lemma stabV_ofMat (A : Matrix m n ℝ) :
    D.stabV (ofMat D.Mx D.Mv A) = ofMat D.Mx D.Mv (A * D.Cvᵀ * D.Mv⁻¹) := rfl

/-- `M_x M_x⁻¹ = 1`. -/
lemma mx_mul_inv : D.Mx * D.Mx⁻¹ = 1 := Matrix.mul_nonsing_inv _
  ((Matrix.isUnit_iff_isUnit_det _).1 (Fact.out : D.Mx.PosDef).isUnit)

/-- `M_v⁻¹ M_v = 1`. -/
lemma mv_inv_mul : D.Mv⁻¹ * D.Mv = 1 := Matrix.nonsing_inv_mul _
  ((Matrix.isUnit_iff_isUnit_det _).1 (Fact.out : D.Mv.PosDef).isUnit)

/-- Cancellation of `M_v⁻¹ M_v`. -/
lemma mul_mv_inv_mul {a : Type*} [Fintype a] (A : Matrix a n ℝ) : A * D.Mv⁻¹ * D.Mv = A := by
  rw [Matrix.mul_assoc, mv_inv_mul, Matrix.mul_one]

/-- Cancellation of `M_x M_x⁻¹`. -/
lemma mx_mul_inv_mul {a : Type*} [Fintype a] (A : Matrix m a ℝ) : D.Mx * (D.Mx⁻¹ * A) = A := by
  rw [← Matrix.mul_assoc, mx_mul_inv, Matrix.one_mul]

/-- `F` on a matrix. -/
lemma field_ofMat (t : ℝ) (A : Matrix m n ℝ) :
    D.field t (ofMat D.Mx D.Mv A) = ofMat D.Mx D.Mv (D.Mx⁻¹ * D.rhs t A * D.Mv⁻¹) := by
  simp [field]

/-- `M_v⁻¹` is symmetric. -/
lemma mv_inv_transpose : (D.Mv⁻¹)ᵀ = D.Mv⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, transpose_eq_of_posDef (Fact.out : D.Mv.PosDef)]

omit [DecidableEq m] [DecidableEq n] [Fact D.Mx.PosDef] [Fact D.Mv.PosDef] in
/-- `op` is additive. -/
lemma op_add (A B : Matrix m n ℝ) : D.op (A + B) = D.op A + D.op B := by
  simp only [op, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

omit [DecidableEq m] [DecidableEq n] [Fact D.Mx.PosDef] [Fact D.Mv.PosDef] in
/-- `op` is homogeneous. -/
lemma op_smul (c : ℝ) (A : Matrix m n ℝ) : D.op (c • A) = c • D.op A := by
  simp only [op, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, ← smul_sub, smul_add,
    smul_neg]

/-- The bounded linear operator `f ↦ M_x⁻¹ op(f) M_v⁻¹`; the field is affine with this linear
part. -/
noncomputable def fieldOp : MassSpace D.Mx D.Mv →L[ℝ] MassSpace D.Mx D.Mv :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => ofMat D.Mx D.Mv (D.Mx⁻¹ * D.op ((ofMat D.Mx D.Mv).symm Y) * D.Mv⁻¹)
      map_add' := fun A B => by simp [op_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c A => by simp [op_smul, Matrix.mul_smul, Matrix.smul_mul] }

/-- The field is affine. -/
lemma field_sub (t : ℝ) (Y Z : MassSpace D.Mx D.Mv) :
    D.field t Y - D.field t Z = D.fieldOp (Y - Z) := by
  obtain ⟨A, rfl⟩ := (ofMat D.Mx D.Mv).surjective Y
  obtain ⟨B, rfl⟩ := (ofMat D.Mx D.Mv).surjective Z
  rw [field_ofMat, field_ofMat, ← map_sub, ← map_sub]
  change _ = ofMat D.Mx D.Mv (D.Mx⁻¹ * D.op (A - B) * D.Mv⁻¹)
  congr 1
  have h : D.op (A - B) = D.op A - D.op B := by
    have := D.op_add (A - B) B
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  rw [h]
  simp only [rhs, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The field of arXiv 2303.01856, Sec. 3, with frozen electric field is Lipschitz with the
constant `‖fieldOp‖`, in the norm of `L²(Ω_x × Ω_v)`.  The constant is finite for each mesh, but
it grows as the mesh is refined, since it contains the transport matrices. -/
theorem isLipschitzField_field : IsLipschitzField D.field ‖D.fieldOp‖ := fun t x y => by
  rw [field_sub]
  exact D.fieldOp.le_opNorm _

/-- `kField` solves the K-equation (20a) of arXiv 2303.01856 for `K̇`. -/
lemma mx_mul_kField (V : Matrix n r ℝ) (δ t : ℝ) (K : Matrix m r ℝ) :
    D.Mx * D.kField V δ t K = D.kRhs V t K - δ • (D.Cx * K) :=
  D.mx_mul_inv_mul _

/-- `lField` solves the L-equation (20c) of arXiv 2303.01856 for `L̇`. -/
lemma mv_mul_lField (X : Matrix m r ℝ) (δ t : ℝ) (L : Matrix n r ℝ) :
    D.Mv * D.lField X δ t L = D.lRhs X t L - δ • (D.Cv * L) := by
  have hv : D.Mv * D.Mv⁻¹ = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Fact.out : D.Mv.PosDef).isUnit)
  rw [lField, ← Matrix.mul_assoc, hv, Matrix.one_mul]

/-- Non-vacuity of the bound on the tube: the affine field is unbounded on `MassSpace`, unless
its linear part vanishes, but it is bounded on every tube around a continuous curve if the
source is continuous in time.  This is why the error bounds below only ask for
`IsBoundedOnTube`. -/
theorem exists_isBoundedOnTube {A : ℝ → MassSpace D.Mx D.Mv} {t₀ t₁ ρ : ℝ}
    (hA : ContinuousOn A (Icc t₀ t₁)) (hG : ContinuousOn (fun t => D.field t 0) (Icc t₀ t₁)) :
    ∃ B, 0 ≤ B ∧ IsBoundedOnTube D.field A t₀ t₁ ρ B := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  refine ⟨max 0 (K + ‖D.fieldOp‖ * (ρ + R)), le_max_left _ _, fun t ht x hx => ?_⟩
  refine le_trans ?_ (le_max_right _ _)
  have h1 := D.isLipschitzField_field t x 0
  rw [sub_zero] at h1
  have h2 : ‖x‖ ≤ ρ + R := by
    have h3 := norm_add_le (x - A t) (A t)
    rw [sub_add_cancel] at h3
    linarith [hR t ht]
  have h3 : ‖D.field t x‖ ≤ ‖D.field t 0‖ + ‖D.field t x - D.field t 0‖ := by
    have := norm_add_le (D.field t 0) (D.field t x - D.field t 0)
    rwa [add_sub_cancel] at this
  have h4 : ‖D.fieldOp‖ * ‖x‖ ≤ ‖D.fieldOp‖ * (ρ + R) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  linarith [hK t ht]

/-- The K-equation (20a) in `MassSpace`: `Y' = Q₀ F(t, Y) - δ M_x⁻¹ C_x Y` for `Y = K V₀ᵀ`. -/
lemma liftK_kField (V : Matrix n r ℝ) (δ t : ℝ) (K : Matrix m r ℝ) :
    liftK D.Mx D.Mv V (D.kField V δ t K) =
      massRight V (D.field t (liftK D.Mx D.Mv V K)) - δ • D.stabX (liftK D.Mx D.Mv V K) := by
  change ofMat D.Mx D.Mv (D.kField V δ t K * Vᵀ) =
    massRight V (D.field t (ofMat D.Mx D.Mv (K * Vᵀ))) -
      δ • D.stabX (ofMat D.Mx D.Mv (K * Vᵀ))
  rw [field_ofMat, massRight_ofMat, stabX_ofMat, ← map_smul, ← map_sub]
  congr 1
  simp only [kField, ← rhs_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  · rw [mul_mv_inv_mul]
    simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]

/-- The L-equation (20c) in `MassSpace`: `Y' = P₁ F(t, Y) - δ Y C_vᵀ M_v⁻¹` for `Y = X₁ Lᵀ`. -/
lemma liftL_lField (X : Matrix m r ℝ) (δ t : ℝ) (L : Matrix n r ℝ) :
    liftL D.Mx D.Mv X (D.lField X δ t L) =
      massLeft X (D.field t (liftL D.Mx D.Mv X L)) - δ • D.stabV (liftL D.Mx D.Mv X L) := by
  change ofMat D.Mx D.Mv (X * (D.lField X δ t L)ᵀ) =
    massLeft X (D.field t (ofMat D.Mx D.Mv (X * Lᵀ))) -
      δ • D.stabV (ofMat D.Mx D.Mv (X * Lᵀ))
  rw [field_ofMat, massLeft_ofMat, stabV_ofMat, ← map_smul, ← map_sub]
  congr 1
  simp only [lField, ← rhs_transpose_mul, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_transpose, mv_inv_transpose, Matrix.mul_sub,
    Matrix.mul_smul]
  congr 1
  · simp only [Matrix.mul_assoc, D.mx_mul_inv_mul]
  · simp only [Matrix.mul_assoc]

/-- The S-equation (20b) in `MassSpace`: `Y' = -P₁ Q₀ F(t, Y)` for `Y = X₁ S V₀ᵀ`. -/
lemma liftS_sRhs (X : Matrix m r ℝ) (V : Matrix n r' ℝ) (t : ℝ) (S : Matrix r r' ℝ) :
    liftS D.Mx D.Mv X V (D.sRhs X V t S) =
      -massLeft X (massRight V (D.field t (liftS D.Mx D.Mv X V S))) := by
  change ofMat D.Mx D.Mv (X * D.sRhs X V t S * Vᵀ) =
    -massLeft X (massRight V (D.field t (ofMat D.Mx D.Mv (X * S * Vᵀ))))
  rw [field_ofMat, massRight_ofMat, massLeft_ofMat, ← map_neg]
  congr 1
  have h : D.sRhs X V t S = -(Xᵀ * D.rhs t (X * S * Vᵀ) * V) := by
    rw [transpose_mul_rhs_mul, neg_neg]
  rw [h]
  simp only [Matrix.mul_neg, Matrix.neg_mul]
  congr 1
  rw [mul_mv_inv_mul]
  simp only [Matrix.mul_assoc, D.mx_mul_inv_mul]

end FEData

/-- One step of Algorithm 1 of arXiv 2303.01856 (first-order projector splitting) from `t₀` to
`t₁`, for the frozen field in `D`: `M_x`- and `M_v`-orthonormal input; the K-step (20a), an
`M_x`-orthonormal factorisation `X₁ Ŝ = K(t₁)`; the S-step (20b); the L-step (20c), an
`M_v`-orthonormal factorisation `V₁ S₁ᵀ = L(t₁)`.  As in the paper, `δ` enters the K- and
L-steps, but not the S-step. -/
structure IsAlg1Step [DecidableEq r] (D : FEData ι κ m n) (δ t₀ t₁ : ℝ) (X₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (K : ℝ → Matrix m r ℝ) (X₁ : Matrix m r ℝ)
    (Ŝ : Matrix r r ℝ) (S : ℝ → Matrix r r ℝ) (Lf : ℝ → Matrix n r ℝ) (V₁ : Matrix n r ℝ)
    (S₁ : Matrix r r ℝ) : Prop where
  orthX₀ : X₀ᵀ * D.Mx * X₀ = 1
  orthV₀ : V₀ᵀ * D.Mv * V₀ = 1
  kSol : ODESolution (D.kField V₀ δ) K t₀ t₁
  kStart : K t₀ = X₀ * S₀
  orthX₁ : X₁ᵀ * D.Mx * X₁ = 1
  kQR : X₁ * Ŝ = K t₁
  sSol : ODESolution (D.sRhs X₁ V₀) S t₀ t₁
  sStart : S t₀ = Ŝ
  lSol : ODESolution (D.lField X₁ δ) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * (S t₁)ᵀ
  orthV₁ : V₁ᵀ * D.Mv * V₁ = 1
  lQR : V₁ * S₁ᵀ = Lf t₁

namespace IsAlg1Step

variable [DecidableEq r] {D : FEData ι κ m n} [Fact D.Mx.PosDef] [Fact D.Mv.PosDef]
  {δ t₀ t₁ ε : ℝ} {X₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
  {K : ℝ → Matrix m r ℝ} {X₁ : Matrix m r ℝ} {Ŝ : Matrix r r ℝ} {S : ℝ → Matrix r r ℝ}
  {Lf : ℝ → Matrix n r ℝ} {V₁ : Matrix n r ℝ} {S₁ : Matrix r r ℝ}

/-- The output of Algorithm 1 is `X₁ S₁ V₁ᵀ`. -/
theorem liftL_end (hs : IsAlg1Step D δ t₀ t₁ X₀ S₀ V₀ K X₁ Ŝ S Lf V₁ S₁) :
    liftL D.Mx D.Mv X₁ (Lf t₁) = ofMat D.Mx D.Mv (X₁ * S₁ * V₁ᵀ) := by
  change ofMat D.Mx D.Mv (X₁ * (Lf t₁)ᵀ) = _
  rw [← hs.lQR, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- arXiv 2303.01856, Alg. 1: for `δ = 0`, Algorithm 1 is a step of the first-order
projector-splitting integrator (`IsKSLStep`) in the inner product `M_x ⊗ M_v`.  `ε` bounds the
normal component, as everywhere in the robust analysis.  For `δ > 0` the K- and L-steps have
extra terms: see `FEData.ksl_fields_sum` and `IsAlg1Step.local_error_stabilised`. -/
theorem isKSLStep (hs : IsAlg1Step D 0 t₀ t₁ X₀ S₀ V₀ K X₁ Ŝ S Lf V₁ S₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - massLeft X₁) ((1 - massRight V₀)
      (D.field t (liftK D.Mx D.Mv V₀ (K t₁))))‖ ≤ ε) :
    IsKSLStep D.field ε (massLeft X₁) (massRight V₀) t₀ t₁ (ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ))
      (fun t => liftK D.Mx D.Mv V₀ (K t)) (fun t => liftS D.Mx D.Mv X₁ V₀ (S t))
      (fun t => liftL D.Mx D.Mv X₁ (Lf t)) where
  projP₁ := isOrthProj_massLeft hs.orthX₁
  projQ₀ := isOrthProj_massRight hs.orthV₀
  kSol := MatrixKSL.odeSolution_comp_clm hs.kSol (liftK D.Mx D.Mv V₀) fun t x => by
    rw [D.liftK_kField]; simp
  kStart := by
    change ofMat D.Mx D.Mv (K t₀ * V₀ᵀ) = _
    rw [hs.kStart]
  kCap := by
    change massLeft X₁ (ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)) = ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)
    rw [massLeft_ofMat, ← hs.kQR]
    congr 1
    calc X₁ * X₁ᵀ * D.Mx * (X₁ * Ŝ * V₀ᵀ) = X₁ * (X₁ᵀ * D.Mx * X₁) * Ŝ * V₀ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = X₁ * Ŝ * V₀ᵀ := by rw [hs.orthX₁, Matrix.mul_one]
  kNormal := hε
  sSol := MatrixKSL.odeSolution_comp_clm hs.sSol (liftS D.Mx D.Mv X₁ V₀) fun t x => by
    rw [D.liftS_sRhs]
  sStart := by
    change ofMat D.Mx D.Mv (X₁ * S t₀ * V₀ᵀ) = ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)
    rw [hs.sStart, hs.kQR]
  lSol := MatrixKSL.odeSolution_comp_clm hs.lSol (liftL D.Mx D.Mv X₁) fun t x => by
    rw [D.liftL_lField]; simp
  lStart := by
    change ofMat D.Mx D.Mv (X₁ * (Lf t₀)ᵀ) = ofMat D.Mx D.Mv (X₁ * S t₁ * V₀ᵀ)
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end IsAlg1Step

namespace IsAlg1Step

variable [DecidableEq r] {D : FEData ι κ m n} [Fact D.Mx.PosDef] [Fact D.Mv.PosDef]
  {δ t₀ t₁ ε : ℝ} {X₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
  {K : ℝ → Matrix m r ℝ} {X₁ : Matrix m r ℝ} {Ŝ : Matrix r r ℝ} {S : ℝ → Matrix r r ℝ}
  {Lf : ℝ → Matrix n r ℝ} {V₁ : Matrix n r ℝ} {S₁ : Matrix r r ℝ}

/-- arXiv 2303.01856, Alg. 1, consistency (not stated in the paper): for `δ = 0`, `‖X₁ S₁ V₁ᵀ -
A(t₁)‖ ≤ h (11 ‖fieldOp‖ B h + ε)` in `L²(Ω_x × Ω_v)`, independently of the singular values,
where `A` solves the full semi-discrete problem with the same frozen field.  `B` only bounds the
field on a tube, see `FEData.exists_isBoundedOnTube`. -/
theorem local_error (hs : IsAlg1Step D 0 t₀ t₁ X₀ S₀ V₀ K X₁ Ŝ S Lf V₁ S₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - massLeft X₁) ((1 - massRight V₀)
      (D.field t (liftK D.Mx D.Mv V₀ (K t₁))))‖ ≤ ε)
    {A : ℝ → MassSpace D.Mx D.Mv} {B ρ h : ℝ} (hA : ODESolution D.field A t₀ t₁)
    (hA₀ : A t₀ = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ))
    (hFB : IsBoundedOnTube D.field A t₀ t₁ ρ B) (hB : 0 ≤ B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hsmall : 4 * B * h < ρ) :
    ‖ofMat D.Mx D.Mv (X₁ * S₁ * V₁ᵀ) - A t₁‖ ≤ h * (11 * ‖D.fieldOp‖ * B * h + ε) := by
  rw [← hs.liftL_end]
  exact ksl_local_error_of_tube (hs.isKSLStep hε) D.isLipschitzField_field (norm_nonneg _) hFB hB
    ht₁ hh hA hA₀ hsmall

end IsAlg1Step

/-- The discarded weight `∑_{i ≥ r₁} σ_i²` (0-indexed) of arXiv 2303.01856, Alg. 2, line 12. -/
noncomputable def tailSum {N : ℕ} (σ : Fin N → ℝ) (r₁ : ℕ) : ℝ :=
  ∑ i : Fin N, if r₁ ≤ i.val then σ i ^ 2 else 0

/-- The first `r₁` columns of `Q`, written `Q(:, 1:r₁)` in arXiv 2303.01856, Alg. 2. -/
def head {N r₁ : ℕ} (hr : r₁ ≤ N) (Q : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin r₁) ℝ :=
  Q.submatrix id (Fin.castLE hr)

/-- `diag(σ_i)_{i < r₁}`. -/
def headDiag {N r₁ : ℕ} (hr : r₁ ≤ N) (σ : Fin N → ℝ) : Matrix (Fin r₁) (Fin r₁) ℝ :=
  Matrix.diagonal fun i => σ (Fin.castLE hr i)

/-- The first columns of an orthogonal matrix are orthonormal. -/
lemma head_transpose_mul_head {N r₁ : ℕ} (hr : r₁ ≤ N) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Qᵀ * Q = 1) : (head hr Q)ᵀ * head hr Q = 1 := by
  ext i j
  have := congrFun (congrFun hQ (Fin.castLE hr i)) (Fin.castLE hr j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.castLE_inj] at this
  simpa [head, Matrix.mul_apply, Matrix.one_apply] using this

/-- The truncated SVD as a product of full matrices with the tail of `σ` set to zero. -/
lemma head_mul_headDiag_mul {N r₁ : ℕ} (hr : r₁ ≤ N) (P Q : Matrix (Fin N) (Fin N) ℝ)
    (σ : Fin N → ℝ) :
    head hr P * headDiag hr σ * (head hr Q)ᵀ =
      P * Matrix.diagonal (fun i : Fin N => if i.val < r₁ then σ i else 0) * Qᵀ := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [head, headDiag, Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.submatrix_apply, id]
  have h : (Finset.univ.map (Fin.castLEEmb hr)) =
      Finset.univ.filter fun i : Fin N => i.val < r₁ := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨j, rfl⟩; simp
    · intro hi; exact ⟨⟨i.val, hi⟩, by ext; simp⟩
  have h2 : ∑ i : Fin N, P a i * (if i.val < r₁ then σ i else 0) * Q b i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < r₁), P a i * σ i * Q b i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [h2, ← h, Finset.sum_map]
  simp

/-- `S ↦ X S Vᵀ` is an isometry from the Frobenius norm to `MassSpace` for `M`-orthonormal
bases. -/
lemma norm_sq_liftS {Mx : Matrix m m ℝ} {Mv : Matrix n n ℝ} [Fact Mx.PosDef] [Fact Mv.PosDef]
    [DecidableEq r] [DecidableEq r'] {X : Matrix m r ℝ} {V : Matrix n r' ℝ}
    (hX : Xᵀ * Mx * X = 1) (hV : Vᵀ * Mv * V = 1) (T : Matrix r r' ℝ) :
    ‖liftS Mx Mv X V T‖ ^ 2 = Matrix.trace (Tᵀ * T) := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪ofMat Mx Mv (X * T * Vᵀ), ofMat Mx Mv (X * T * Vᵀ)⟫ = _
  rw [inner_ofMat]
  have e : (X * T * Vᵀ)ᵀ * Mx * (X * T * Vᵀ) * Mv = V * (Tᵀ * (Xᵀ * Mx * X) * T * (Vᵀ * Mv)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, hX, Matrix.mul_one, Matrix.trace_mul_comm,
    show Tᵀ * T * (Vᵀ * Mv) * V = Tᵀ * T * (Vᵀ * Mv * V) by simp only [Matrix.mul_assoc],
    hV, Matrix.mul_one]

/-- `‖P diag(d) Qᵀ‖_F² = ∑ dᵢ²` for orthogonal `P`, `Q`. -/
lemma trace_tail {N : ℕ} {P Q : Matrix (Fin N) (Fin N) ℝ} (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (d : Fin N → ℝ) :
    Matrix.trace ((P * Matrix.diagonal d * Qᵀ)ᵀ * (P * Matrix.diagonal d * Qᵀ)) =
      ∑ i, d i ^ 2 := by
  have e : (P * Matrix.diagonal d * Qᵀ)ᵀ * (P * Matrix.diagonal d * Qᵀ) =
      Q * ((Matrix.diagonal d)ᵀ * (Pᵀ * P) * Matrix.diagonal d * Qᵀ) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, hP, Matrix.mul_one, Matrix.trace_mul_comm,
    show (Matrix.diagonal d)ᵀ * Matrix.diagonal d * Qᵀ * Q =
      (Matrix.diagonal d)ᵀ * Matrix.diagonal d * (Qᵀ * Q) by simp only [Matrix.mul_assoc],
    hQ, Matrix.mul_one, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- arXiv 2303.01856, Alg. 2, lines 11–13: the truncation of `X̂ S V̂ᵀ`, `S = Q_x diag(σ) Q_vᵀ`,
to the first `r₁` singular triples has squared `L²(Ω_x × Ω_v)` error exactly `∑_{i ≥ r₁} σ_i²`. -/
theorem norm_sq_truncation {Mx : Matrix m m ℝ} {Mv : Matrix n n ℝ} [Fact Mx.PosDef]
    [Fact Mv.PosDef] {N r₁ : ℕ} (hr : r₁ ≤ N) {Xa : Matrix m (Fin N) ℝ} {Va : Matrix n (Fin N) ℝ}
    (hX : Xaᵀ * Mx * Xa = 1) (hV : Vaᵀ * Mv * Va = 1) {Qx Qv : Matrix (Fin N) (Fin N) ℝ}
    (hQx : Qxᵀ * Qx = 1) (hQv : Qvᵀ * Qv = 1) (σ : Fin N → ℝ) :
    ‖ofMat Mx Mv ((Xa * head hr Qx) * headDiag hr σ * (Va * head hr Qv)ᵀ) -
        liftS Mx Mv Xa Va (Qx * Matrix.diagonal σ * Qvᵀ)‖ ^ 2 = tailSum σ r₁ := by
  have h1 : ofMat Mx Mv ((Xa * head hr Qx) * headDiag hr σ * (Va * head hr Qv)ᵀ) =
      liftS Mx Mv Xa Va (head hr Qx * headDiag hr σ * (head hr Qv)ᵀ) := by
    change _ = ofMat Mx Mv (Xa * (head hr Qx * headDiag hr σ * (head hr Qv)ᵀ) * Vaᵀ)
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  set dh : Fin N → ℝ := fun i => if i.val < r₁ then σ i else 0 with hdh
  set dt : Fin N → ℝ := fun i => if r₁ ≤ i.val then σ i else 0 with hdt
  have hd : Matrix.diagonal σ = Matrix.diagonal dh + Matrix.diagonal dt := by
    rw [Matrix.diagonal_add]
    congr 1
    ext i
    by_cases hi : i.val < r₁
    · simp [hdh, hdt, hi, not_le.2 hi]
    · simp [hdh, hdt, hi, not_lt.1 hi]
  have h2 : head hr Qx * headDiag hr σ * (head hr Qv)ᵀ - Qx * Matrix.diagonal σ * Qvᵀ =
      -(Qx * Matrix.diagonal dt * Qvᵀ) := by
    rw [head_mul_headDiag_mul, hd, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [h1, ← map_sub, h2, map_neg, norm_neg, norm_sq_liftS hX hV, trace_tail hQx hQv, tailSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : r₁ ≤ i.val <;> simp [hdt, hi]

/-- arXiv 2303.01856, Alg. 2, line 12: for `ϑ > 0` the minimal `r₁ ≤ N` with `∑_{i ≥ r₁} σ_i² <
ϑ²` exists. (For `ϑ = 0` there is none, as the inequality is strict; hence `tol_pos` in
`IsAlg2Step`.) -/
theorem exists_minRank {N : ℕ} (σ : Fin N → ℝ) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ r₁ ≤ N, tailSum σ r₁ < ϑ ^ 2 ∧ ∀ r' < r₁, ϑ ^ 2 ≤ tailSum σ r' := by
  classical
  have hex : ∃ r₁, r₁ ≤ N ∧ tailSum σ r₁ < ϑ ^ 2 := by
    refine ⟨N, le_rfl, ?_⟩
    have : tailSum σ N = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [i.isLt]
    rw [this]
    positivity
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun r' hr' => ?_⟩
  by_contra hlt
  exact Nat.find_min hex hr' ⟨hr'.le.trans (Nat.find_spec hex).1, not_le.1 hlt⟩

/-- One step of Algorithm 2 of arXiv 2303.01856 (rank-adaptive unconventional integrator) with
tolerance `ϑ`, the paper's `ϵ`: the K-step (20a) and the L-step (20c) from the same data,
`M`-orthonormal augmented bases `Xa`, `Va` with `Xa [Rx, Rx'] = [X₀, K(t₁)]` and `Va [Rv, Rv'] =
[V₀, L(t₁)]`, the forward S-step (21) from `Rx S₀ Rvᵀ`, an SVD with decreasing `σ`, and the
minimal rank `r₁`.  The paper has `N = 2 r₀`; `N` is arbitrary here.  The output is
`IsAlg2Step.output`. -/
structure IsAlg2Step [DecidableEq r] (D : FEData ι κ m n) (δ ϑ t₀ t₁ : ℝ) (X₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (K : ℝ → Matrix m r ℝ) (Lf : ℝ → Matrix n r ℝ) {N : ℕ}
    (Xa : Matrix m (Fin N) ℝ) (Va : Matrix n (Fin N) ℝ) (Rx Rx' Rv Rv' : Matrix (Fin N) r ℝ)
    (Ŝ : ℝ → Matrix (Fin N) (Fin N) ℝ) (Qx Qv : Matrix (Fin N) (Fin N) ℝ) (σ : Fin N → ℝ)
    (r₁ : ℕ) : Prop where
  tol_pos : 0 < ϑ
  orthX₀ : X₀ᵀ * D.Mx * X₀ = 1
  orthV₀ : V₀ᵀ * D.Mv * V₀ = 1
  kSol : ODESolution (D.kField V₀ δ) K t₀ t₁
  kStart : K t₀ = X₀ * S₀
  orthXa : Xaᵀ * D.Mx * Xa = 1
  xAug₀ : Xa * Rx = X₀
  xAug₁ : Xa * Rx' = K t₁
  lSol : ODESolution (D.lField X₀ δ) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthVa : Vaᵀ * D.Mv * Va = 1
  vAug₀ : Va * Rv = V₀
  vAug₁ : Va * Rv' = Lf t₁
  sSol : ODESolution (fun t S => -D.sRhs Xa Va t S) Ŝ t₀ t₁
  sStart : Ŝ t₀ = Rx * S₀ * Rvᵀ
  svd : Ŝ t₁ = Qx * Matrix.diagonal σ * Qvᵀ
  orthQx : Qxᵀ * Qx = 1
  orthQv : Qvᵀ * Qv = 1
  σ_anti : Antitone σ
  σ_nonneg : ∀ i, 0 ≤ σ i
  rank_le : r₁ ≤ N
  tail_lt : tailSum σ r₁ < ϑ ^ 2
  tail_min : ∀ r' < r₁, ϑ ^ 2 ≤ tailSum σ r'

namespace IsAlg2Step

variable [DecidableEq r] {D : FEData ι κ m n} [Fact D.Mx.PosDef] [Fact D.Mv.PosDef]
  {δ ϑ t₀ t₁ ε : ℝ} {X₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
  {K : ℝ → Matrix m r ℝ} {Lf : ℝ → Matrix n r ℝ} {N : ℕ}
  {Xa : Matrix m (Fin N) ℝ} {Va : Matrix n (Fin N) ℝ} {Rx Rx' Rv Rv' : Matrix (Fin N) r ℝ}
  {Ŝ : ℝ → Matrix (Fin N) (Fin N) ℝ} {Qx Qv : Matrix (Fin N) (Fin N) ℝ} {σ : Fin N → ℝ} {r₁ : ℕ}

/-- arXiv 2303.01856, Alg. 2, line 13: the output `X¹ = Xa Q_x(:, 1:r₁)` is `M_x`-orthonormal. -/
theorem orth_left (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    (Xa * head hs.rank_le Qx)ᵀ * D.Mx * (Xa * head hs.rank_le Qx) = 1 := by
  rw [show (Xa * head hs.rank_le Qx)ᵀ * D.Mx * (Xa * head hs.rank_le Qx) =
    (head hs.rank_le Qx)ᵀ * (Xaᵀ * D.Mx * Xa) * head hs.rank_le Qx by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc], hs.orthXa, Matrix.mul_one,
    head_transpose_mul_head _ hs.orthQx]

/-- arXiv 2303.01856, Alg. 2, line 13: the output `V¹ = Va Q_v(:, 1:r₁)` is `M_v`-orthonormal. -/
theorem orth_right (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    (Va * head hs.rank_le Qv)ᵀ * D.Mv * (Va * head hs.rank_le Qv) = 1 := by
  rw [show (Va * head hs.rank_le Qv)ᵀ * D.Mv * (Va * head hs.rank_le Qv) =
    (head hs.rank_le Qv)ᵀ * (Vaᵀ * D.Mv * Va) * head hs.rank_le Qv by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc], hs.orthVa, Matrix.mul_one,
    head_transpose_mul_head _ hs.orthQv]

/-- arXiv 2303.01856, Alg. 2: the truncation changes the solution by less than `ϑ` in `L²(Ω_x ×
Ω_v)`. -/
theorem norm_trunc_lt
    (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    ‖ofMat D.Mx D.Mv ((Xa * head hs.rank_le Qx) * headDiag hs.rank_le σ *
        (Va * head hs.rank_le Qv)ᵀ) - liftS D.Mx D.Mv Xa Va (Ŝ t₁)‖ < ϑ := by
  have h := norm_sq_truncation (Mx := D.Mx) (Mv := D.Mv) hs.rank_le hs.orthXa hs.orthVa hs.orthQx
    hs.orthQv σ
  rw [hs.svd]
  have ht := hs.tail_lt
  rw [← h] at ht
  exact lt_of_pow_lt_pow_left₀ 2 hs.tol_pos.le ht

/-- arXiv 2303.01856, Alg. 2, line 9: the initial value `Rx S₀ Rvᵀ` of the forward S-step
represents the old approximation: `Xa Ŝ(t₀) Vaᵀ = X₀ S₀ V₀ᵀ`. -/
theorem start_eq (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    liftS D.Mx D.Mv Xa Va (Ŝ t₀) = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ) := by
  change ofMat D.Mx D.Mv (Xa * Ŝ t₀ * Vaᵀ) = _
  rw [hs.sStart, ← hs.xAug₀, ← hs.vAug₀]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The output `X¹ S¹ (V¹)ᵀ` of Algorithm 2, line 13. -/
noncomputable def output (D : FEData ι κ m n) [Fact D.Mx.PosDef] [Fact D.Mv.PosDef] {N r₁ : ℕ}
    (hr : r₁ ≤ N) (Xa : Matrix m (Fin N) ℝ) (Va : Matrix n (Fin N) ℝ)
    (Qx Qv : Matrix (Fin N) (Fin N) ℝ) (σ : Fin N → ℝ) : MassSpace D.Mx D.Mv :=
  ofMat D.Mx D.Mv ((Xa * head hr Qx) * headDiag hr σ * (Va * head hr Qv)ᵀ)

/-- The augmented left basis captures the old approximation. -/
theorem augP (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    massLeft Xa (ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ)) = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ) := by
  have := massLeft_fix (Mv := D.Mv) hs.orthXa (Rx * S₀ * V₀ᵀ)
  simpa only [← hs.xAug₀, Matrix.mul_assoc] using this

/-- The augmented right basis captures the old approximation. -/
theorem augQ (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    massRight Va (ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ)) = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ) := by
  have := massRight_fix (Mx := D.Mx) hs.orthVa (X₀ * S₀ * Rvᵀ)
  simpa only [← hs.vAug₀, Matrix.transpose_mul, Matrix.mul_assoc] using this

/-- The augmented left basis captures the K-step result. -/
theorem kCap (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    massLeft Xa (liftK D.Mx D.Mv V₀ (K t₁)) = liftK D.Mx D.Mv V₀ (K t₁) := by
  change massLeft Xa (ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)) = ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)
  have := massLeft_fix (Mv := D.Mv) hs.orthXa (Rx' * V₀ᵀ)
  simpa only [← hs.xAug₁, Matrix.mul_assoc] using this

/-- The augmented right basis captures the L-step result. -/
theorem lCap (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    massRight Va (liftL D.Mx D.Mv X₀ (Lf t₁)) = liftL D.Mx D.Mv X₀ (Lf t₁) := by
  change massRight Va (ofMat D.Mx D.Mv (X₀ * (Lf t₁)ᵀ)) = ofMat D.Mx D.Mv (X₀ * (Lf t₁)ᵀ)
  have := massRight_fix (Mx := D.Mx) hs.orthVa (X₀ * Rv'ᵀ)
  simpa only [← hs.vAug₁, Matrix.transpose_mul, Matrix.mul_assoc] using this

/-- The K-step starts at the old approximation. -/
theorem liftK_start (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    liftK D.Mx D.Mv V₀ (K t₀) = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ) := by
  change ofMat D.Mx D.Mv (K t₀ * V₀ᵀ) = _
  rw [hs.kStart]

/-- The L-step starts at the old approximation. -/
theorem liftL_start (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    liftL D.Mx D.Mv X₀ (Lf t₀) = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ) := by
  change ofMat D.Mx D.Mv (X₀ * (Lf t₀)ᵀ) = _
  rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The forward S-step (21) is the Galerkin ODE `Y' = P̂ Q̂ F(t, Y)`. -/
theorem sSol_lift (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁) :
    ODESolution (fun t x => massLeft Xa (massRight Va (D.field t x)))
      (fun t => liftS D.Mx D.Mv Xa Va (Ŝ t)) t₀ t₁ :=
  MatrixKSL.odeSolution_comp_clm hs.sSol (liftS D.Mx D.Mv Xa Va) fun t x => by
    rw [map_neg, D.liftS_sRhs, neg_neg]

/-- arXiv 2303.01856, Alg. 2: for `δ = 0`, Algorithm 2 is a step of the rank-adaptive BUG
integrator (`IsRankAdaptiveBUGStep`) with truncation tolerance `ϑ` in the inner product `M_x ⊗
M_v`.  For `δ > 0` see `IsAlg2Step.local_error_stabilised`. -/
theorem isRankAdaptiveBUGStep
    (hs : IsAlg2Step D 0 ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁)
    (hK : ∀ t ∈ Icc t₀ t₁, ‖(1 - massLeft Xa) ((1 - massRight V₀)
      (D.field t (liftK D.Mx D.Mv V₀ (K t₁))))‖ ≤ ε)
    (hL : ∀ t ∈ Icc t₀ t₁, ‖(1 - massRight Va) ((1 - massLeft X₀)
      (D.field t (liftL D.Mx D.Mv X₀ (Lf t₁))))‖ ≤ ε) :
    IsRankAdaptiveBUGStep D.field ε ϑ (massLeft X₀) (massRight V₀) (massLeft Xa) (massRight Va)
      t₀ t₁ (ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ)) (fun t => liftK D.Mx D.Mv V₀ (K t))
      (fun t => liftL D.Mx D.Mv X₀ (Lf t)) (fun t => liftS D.Mx D.Mv Xa Va (Ŝ t))
      (output D hs.rank_le Xa Va Qx Qv σ) := by
  exact
    { projP₀ := isOrthProj_massLeft hs.orthX₀
      projQ₀ := isOrthProj_massRight hs.orthV₀
      projP₁ := isOrthProj_massLeft hs.orthXa
      projQ₁ := isOrthProj_massRight hs.orthVa
      comm₁ := massLeft_massRight_comm Xa Va
      kSol := MatrixKSL.odeSolution_comp_clm hs.kSol (liftK D.Mx D.Mv V₀) fun t x => by
        rw [D.liftK_kField]; simp
      kStart := hs.liftK_start
      kCap := hs.kCap
      kNormal := hK
      lSol := MatrixKSL.odeSolution_comp_clm hs.lSol (liftL D.Mx D.Mv X₀) fun t x => by
        rw [D.liftL_lField]; simp
      lStart := hs.liftL_start
      lCap := hs.lCap
      lNormal := hL
      sSol := hs.sSol_lift
      sStart := by
        rw [hs.start_eq, hs.augQ, hs.augP]
      augP := hs.augP
      augQ := hs.augQ
      trunc := hs.norm_trunc_lt.le }

/-- arXiv 2303.01856, Alg. 2, consistency (not stated in the paper): for `δ = 0`, `‖Y₁ - A(t₁)‖
≤ h (c₁ ε + c₂ h) + ϑ` with constants independent of the singular values, in `L²(Ω_x × Ω_v)`,
where `B` only bounds the field on a tube. -/
theorem local_error
    (hs : IsAlg2Step D 0 ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁)
    (hK : ∀ t ∈ Icc t₀ t₁, ‖(1 - massLeft Xa) ((1 - massRight V₀)
      (D.field t (liftK D.Mx D.Mv V₀ (K t₁))))‖ ≤ ε)
    (hL : ∀ t ∈ Icc t₀ t₁, ‖(1 - massRight Va) ((1 - massLeft X₀)
      (D.field t (liftL D.Mx D.Mv X₀ (Lf t₁))))‖ ≤ ε)
    {A : ℝ → MassSpace D.Mx D.Mv} {B ρ h H : ℝ} (hA : ODESolution D.field A t₀ t₁)
    (hA₀ : A t₀ = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ))
    (hFB : IsBoundedOnTube D.field A t₀ t₁ ρ B) (hB : 0 ≤ B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hhH : h ≤ H) (hsmall : 4 * B * h < ρ) :
    ‖output D hs.rank_le Xa Va Qx Qv σ - A t₁‖ ≤
      h * (bugC₁ ‖D.fieldOp‖ H * ε + bugC₂ ‖D.fieldOp‖ B H * h) + ϑ := by
  have hρ : 0 ≤ ρ := by nlinarith [mul_nonneg hB hh]
  have hs' := hs.isRankAdaptiveBUGStep hK hL
  have hb := hs'.toIsBUGStep.tubeExt hFB hB hh le_rfl le_rfl ht₁ hA
    (by rw [hA₀]; simpa using hsmall)
  have ht : IsRankAdaptiveBUGStep (tubeExt D.field A t₀ t₁ ρ) ε ϑ (massLeft X₀) (massRight V₀)
      (massLeft Xa) (massRight Va) t₀ t₁ (ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ))
      (fun t => liftK D.Mx D.Mv V₀ (K t)) (fun t => liftL D.Mx D.Mv X₀ (Lf t))
      (fun t => liftS D.Mx D.Mv Xa Va (Ŝ t)) (output D hs.rank_le Xa Va Qx Qv σ) :=
    { toIsBUGStep := hb, augP := hs'.augP, augQ := hs'.augQ, trunc := hs'.trunc }
  exact ht.local_error_le (isLipschitzField_tubeExt
    (D.isLipschitzField_field.isLipschitzOnTube _ _ _ _) (norm_nonneg _) hρ) (norm_nonneg _)
    (isBoundedField_tubeExt hFB hB hρ) ht₁ hh hhH (hA.tubeExt_self hρ) hA₀

/-- arXiv 2303.01856, Alg. 2 with stabilisation (not stated in the paper).  The S-equation (21)
has no `δ`, so the value of Algorithm 2 is a Galerkin step of the *unstabilised* field in bases
that come from stabilised K- and L-steps.  This theorem compares it with the unstabilised
solution `A`: the terms `δ M_x⁻¹ C_x Y`, `δ Y C_vᵀ M_v⁻¹`, bounded by `Dd` on the tube, cost at
most `O(Dd h)` per step. The normal components are taken at the stabilised results `K(t₁)`,
`L(t₁)`. -/
theorem local_error_stabilised
    (hs : IsAlg2Step D δ ϑ t₀ t₁ X₀ S₀ V₀ K Lf Xa Va Rx Rx' Rv Rv' Ŝ Qx Qv σ r₁)
    (hK : ∀ t ∈ Icc t₀ t₁, ‖(1 - massLeft Xa) ((1 - massRight V₀)
      (D.field t (liftK D.Mx D.Mv V₀ (K t₁))))‖ ≤ ε)
    (hL : ∀ t ∈ Icc t₀ t₁, ‖(1 - massRight Va) ((1 - massLeft X₀)
      (D.field t (liftL D.Mx D.Mv X₀ (Lf t₁))))‖ ≤ ε)
    {A : ℝ → MassSpace D.Mx D.Mv} {B Dd ρ h : ℝ} (hA : ODESolution D.field A t₀ t₁)
    (hA₀ : A t₀ = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ))
    (hFB : IsBoundedOnTube D.field A t₀ t₁ ρ B) (hB : 0 ≤ B) (hDd0 : 0 ≤ Dd)
    (hDd : ∀ t ∈ Icc t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ →
      ‖δ • D.stabX x‖ ≤ Dd ∧ ‖δ • D.stabV x‖ ≤ Dd)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hsmall : (2 * B + Dd) * h < ρ) :
    ‖output D hs.rank_le Xa Va Qx Qv σ - A t₁‖ ≤ (Real.exp (‖D.fieldOp‖ * h) - 1) *
        (B * h + 2 * (h * (‖D.fieldOp‖ * (4 * B + 3 * Dd) * h + ε + Dd))) +
      2 * (h * (‖D.fieldOp‖ * (4 * B + 3 * Dd) * h + ε + Dd)) + ϑ := by
  have hG := perturbed_bug_local_error (a := fun x => -(δ • D.stabX x))
    (b := fun x => -(δ • D.stabV x)) (P₀ := massLeft X₀) (Q₀ := massRight V₀)
    (P₁ := massLeft Xa) (Q₁ := massRight Va) D.isLipschitzField_field (norm_nonneg _) hFB hB hDd0
    (fun t ht x hx => by simpa only [norm_neg] using hDd t ht x hx)
    (isOrthProj_massLeft hs.orthX₀) (isOrthProj_massRight hs.orthV₀)
    (isOrthProj_massLeft hs.orthXa) (isOrthProj_massRight hs.orthVa)
    (massLeft_massRight_comm Xa Va) ht₁ hh hA hA₀
    (MatrixKSL.odeSolution_comp_clm hs.kSol (liftK D.Mx D.Mv V₀) fun t x => by
      rw [D.liftK_kField, sub_eq_add_neg]) hs.liftK_start hs.kCap hK
    (MatrixKSL.odeSolution_comp_clm hs.lSol (liftL D.Mx D.Mv X₀) fun t x => by
      rw [D.liftL_lField, sub_eq_add_neg]) hs.liftL_start hs.lCap hL
    hs.sSol_lift hs.start_eq (by rw [hs.augQ, hs.augP]) hsmall
  have h1 := norm_sub_le_norm_sub_add_norm_sub (output D hs.rank_le Xa Va Qx Qv σ)
    (liftS D.Mx D.Mv Xa Va (Ŝ t₁)) (A t₁)
  have h2 := hs.norm_trunc_lt
  rw [show ofMat D.Mx D.Mv ((Xa * head hs.rank_le Qx) * headDiag hs.rank_le σ *
    (Va * head hs.rank_le Qv)ᵀ) = output D hs.rank_le Xa Va Qx Qv σ from rfl] at h2
  linarith

end IsAlg2Step

namespace IsAlg1Step

variable [DecidableEq r] {D : FEData ι κ m n} [Fact D.Mx.PosDef] [Fact D.Mv.PosDef]
  {δ t₀ t₁ ε : ℝ} {X₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
  {K : ℝ → Matrix m r ℝ} {X₁ : Matrix m r ℝ} {Ŝ : Matrix r r ℝ} {S : ℝ → Matrix r r ℝ}
  {Lf : ℝ → Matrix n r ℝ} {V₁ : Matrix n r ℝ} {S₁ : Matrix r r ℝ}

/-- arXiv 2303.01856, Alg. 1 with stabilisation (not stated in the paper).  For any `δ`, if the
terms `δ M_x⁻¹ C_x Y` and `δ Y C_vᵀ M_v⁻¹` are bounded by `Dd` on the tube, then the output is
within `h (‖fieldOp‖ (11 B + 7 Dd) h + ε + 3 Dd)` of the solution `A` of the *unstabilised*
semi-discrete problem.  So the stabilisation adds at most `O(Dd h)` per step, whatever `h`. -/
theorem local_error_stabilised (hs : IsAlg1Step D δ t₀ t₁ X₀ S₀ V₀ K X₁ Ŝ S Lf V₁ S₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - massLeft X₁) ((1 - massRight V₀)
      (D.field t (liftK D.Mx D.Mv V₀ (K t₁))))‖ ≤ ε)
    {A : ℝ → MassSpace D.Mx D.Mv} {B Dd ρ h : ℝ} (hA : ODESolution D.field A t₀ t₁)
    (hA₀ : A t₀ = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ))
    (hFB : IsBoundedOnTube D.field A t₀ t₁ ρ B) (hB : 0 ≤ B) (hDd0 : 0 ≤ Dd)
    (hDd : ∀ t ∈ Icc t₀ t₁, ∀ x, ‖x - A t‖ ≤ ρ →
      ‖δ • D.stabX x‖ ≤ Dd ∧ ‖δ • D.stabV x‖ ≤ Dd)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hsmall : (4 * B + 2 * Dd) * h < ρ) :
    ‖ofMat D.Mx D.Mv (X₁ * S₁ * V₁ᵀ) - A t₁‖ ≤
      h * (‖D.fieldOp‖ * (11 * B + 7 * Dd) * h + ε + 3 * Dd) := by
  rw [← hs.liftL_end]
  have hsk0 : liftK D.Mx D.Mv V₀ (K t₀) = ofMat D.Mx D.Mv (X₀ * S₀ * V₀ᵀ) := by
    change ofMat D.Mx D.Mv (K t₀ * V₀ᵀ) = _
    rw [hs.kStart]
  have hcap : massLeft X₁ (liftK D.Mx D.Mv V₀ (K t₁)) = liftK D.Mx D.Mv V₀ (K t₁) := by
    change massLeft X₁ (ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)) = ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)
    have := massLeft_fix (Mv := D.Mv) hs.orthX₁ (Ŝ * V₀ᵀ)
    simpa only [← hs.kQR, Matrix.mul_assoc] using this
  have hKs : ODESolution (fun t x => massRight V₀ (D.field t x) + -(δ • D.stabX x))
      (fun t => liftK D.Mx D.Mv V₀ (K t)) t₀ t₁ :=
    MatrixKSL.odeSolution_comp_clm hs.kSol (liftK D.Mx D.Mv V₀) fun t x => by
      rw [D.liftK_kField, sub_eq_add_neg]
  have hSs : ODESolution (fun t x => -massLeft X₁ (massRight V₀ (D.field t x)))
      (fun t => liftS D.Mx D.Mv X₁ V₀ (S t)) t₀ t₁ :=
    MatrixKSL.odeSolution_comp_clm hs.sSol (liftS D.Mx D.Mv X₁ V₀) fun t x => by
      rw [D.liftS_sRhs]
  have hLs : ODESolution (fun t x => massLeft X₁ (D.field t x) + -(δ • D.stabV x))
      (fun t => liftL D.Mx D.Mv X₁ (Lf t)) t₀ t₁ :=
    MatrixKSL.odeSolution_comp_clm hs.lSol (liftL D.Mx D.Mv X₁) fun t x => by
      rw [D.liftL_lField, sub_eq_add_neg]
  have hS0 : liftS D.Mx D.Mv X₁ V₀ (S t₀) = liftK D.Mx D.Mv V₀ (K t₁) := by
    change ofMat D.Mx D.Mv (X₁ * S t₀ * V₀ᵀ) = ofMat D.Mx D.Mv (K t₁ * V₀ᵀ)
    rw [hs.sStart, hs.kQR]
  have hL0 : liftL D.Mx D.Mv X₁ (Lf t₀) = liftS D.Mx D.Mv X₁ V₀ (S t₁) := by
    change ofMat D.Mx D.Mv (X₁ * (Lf t₀)ᵀ) = ofMat D.Mx D.Mv (X₁ * S t₁ * V₀ᵀ)
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  exact perturbed_ksl_local_error (F := D.field) (a := fun x => -(δ • D.stabX x))
    (b := fun x => -(δ • D.stabV x)) (P₁ := massLeft X₁) (Q₀ := massRight V₀)
    (YK := fun t => liftK D.Mx D.Mv V₀ (K t)) (YS := fun t => liftS D.Mx D.Mv X₁ V₀ (S t))
    (YL := fun t => liftL D.Mx D.Mv X₁ (Lf t)) D.isLipschitzField_field (norm_nonneg _) hFB hB
    hDd0 (fun t ht x hx => by simpa only [norm_neg] using hDd t ht x hx)
    (isOrthProj_massLeft hs.orthX₁) (isOrthProj_massRight hs.orthV₀) ht₁ hh hA hA₀
    hKs hsk0 hcap hε hSs hS0 hLs hL0 hsmall

end IsAlg1Step

/-- A matrix orthogonal to all matrices vanishes. -/
lemma eq_zero_of_forall_trace {a b : Type*} [Fintype a] [Fintype b] {Z : Matrix a b ℝ}
    (h : ∀ W : Matrix a b ℝ, Matrix.trace (Wᵀ * Z) = 0) : Z = 0 := by
  have h2 : Matrix.trace (Zᴴ * Z) = 0 := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h Z
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h2

namespace FEData

variable (D : FEData ι κ m n) [Fact D.Mx.PosDef] [Fact D.Mv.PosDef]

/-- The weak residual `W ↦ tr(Wᵀ R(t, Y))`, which is `ℓ(w) - a(t, f, w)` for FE functions
(`fe_weak_iff`). -/
noncomputable def res (t : ℝ) (Y : MassSpace D.Mx D.Mv) : MassSpace D.Mx D.Mv →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W => Matrix.trace (((ofMat D.Mx D.Mv).symm W)ᵀ *
        D.rhs t ((ofMat D.Mx D.Mv).symm Y))
      map_add' := fun A B => by simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun c A => by simp [Matrix.smul_mul, Matrix.trace_smul] }

/-- The weak residual on matrices. -/
lemma res_ofMat (t : ℝ) (Y W : Matrix m n ℝ) :
    D.res t (ofMat D.Mx D.Mv Y) (ofMat D.Mx D.Mv W) = Matrix.trace (Wᵀ * D.rhs t Y) := rfl

/-- arXiv 2303.01856, Secs. 2.2–2.4: `F` is the Riesz representative of the weak residual in
`MassSpace`. -/
theorem weakField_res : weakField D.res = D.field := by
  funext t Y
  refine ext_inner_right ℝ fun W => ?_
  obtain ⟨A, rfl⟩ := (ofMat D.Mx D.Mv).surjective Y
  obtain ⟨B, rfl⟩ := (ofMat D.Mx D.Mv).surjective W
  rw [inner_weakField, res_ofMat, real_inner_comm, riesz]

end FEData

/-- arXiv 2303.01856, Secs. 2.2–2.4 at the discrete level: for `δ = 0` the three substeps of
Algorithm 1 solve the weak form restricted to `T_{V⁰}`, the weak form with flipped sign
restricted to `T_{X¹,V⁰}`, and the weak form restricted to `T_{X¹}`. -/
theorem IsAlg1Step.isWeak [DecidableEq r] {D : FEData ι κ m n} [Fact D.Mx.PosDef]
    [Fact D.Mv.PosDef] {t₀ t₁ ε : ℝ} {X₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    {K : ℝ → Matrix m r ℝ} {X₁ : Matrix m r ℝ} {Ŝ : Matrix r r ℝ} {S : ℝ → Matrix r r ℝ}
    {Lf : ℝ → Matrix n r ℝ} {V₁ : Matrix n r ℝ} {S₁ : Matrix r r ℝ}
    (hs : IsAlg1Step D 0 t₀ t₁ X₀ S₀ V₀ K X₁ Ŝ S Lf V₁ S₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - massLeft X₁) ((1 - massRight V₀)
      (D.field t (liftK D.Mx D.Mv V₀ (K t₁))))‖ ≤ ε) :
    IsWeakSolution D.res (massRight V₀) (fun t => liftK D.Mx D.Mv V₀ (K t)) t₀ t₁ ∧
      IsWeakSolution (fun t y => -D.res t y) (massLeft X₁ * massRight V₀)
        (fun t => liftS D.Mx D.Mv X₁ V₀ (S t)) t₀ t₁ ∧
      IsWeakSolution D.res (massLeft X₁) (fun t => liftL D.Mx D.Mv X₁ (Lf t)) t₀ t₁ := by
  have h := hs.isKSLStep hε
  rw [← D.weakField_res] at h
  have h' := (isKSLStep_weakField_iff (isOrthProj_massLeft hs.orthX₁)
    (isOrthProj_massRight hs.orthV₀) (massLeft_massRight_comm X₁ V₀)).1 h
  exact ⟨h'.1.1, h'.2.1.1, h'.2.2.1⟩

section Ranges

variable {Mx : Matrix m m ℝ} {Mv : Matrix n n ℝ} [Fact Mx.PosDef] [Fact Mv.PosDef]
  [DecidableEq r] [DecidableEq r']

/-- arXiv 2303.01856, Sec. 2.2: the range of `massRight V` is the test space `T_V = {Φ Vᵀ}`. -/
theorem massRight_eq_self_iff {V : Matrix n r ℝ} (hV : Vᵀ * Mv * V = 1) (Z : MassSpace Mx Mv) :
    massRight V Z = Z ↔ ∃ Φ : Matrix m r ℝ, Z = ofMat Mx Mv (Φ * Vᵀ) := by
  constructor
  · intro h
    obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
    refine ⟨A * Mv * V, ?_⟩
    rw [← h, massRight_ofMat]
  · rintro ⟨Φ, rfl⟩
    exact massRight_fix hV Φ

/-- arXiv 2303.01856, Sec. 2.4: the range of `massLeft X` is the test space `T_X = {X Φᵀ}`. -/
theorem massLeft_eq_self_iff {X : Matrix m r ℝ} (hX : Xᵀ * Mx * X = 1) (Z : MassSpace Mx Mv) :
    massLeft X Z = Z ↔ ∃ Φ : Matrix n r ℝ, Z = ofMat Mx Mv (X * Φᵀ) := by
  constructor
  · intro h
    obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
    refine ⟨Aᵀ * Mxᵀ * X, ?_⟩
    rw [← h, massLeft_ofMat]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  · rintro ⟨Φ, rfl⟩
    exact massLeft_fix hX Φᵀ

/-- arXiv 2303.01856, Sec. 2.3: the range of the product is the test space `T_{X,V} = {X T Vᵀ}`. -/
theorem massLeft_massRight_eq_self_iff {X : Matrix m r ℝ} {V : Matrix n r' ℝ}
    (hX : Xᵀ * Mx * X = 1) (hV : Vᵀ * Mv * V = 1) (Z : MassSpace Mx Mv) :
    massLeft X (massRight V Z) = Z ↔ ∃ T : Matrix r r' ℝ, Z = ofMat Mx Mv (X * T * Vᵀ) := by
  constructor
  · intro h
    obtain ⟨A, rfl⟩ := (ofMat Mx Mv).surjective Z
    refine ⟨Xᵀ * Mx * A * Mv * V, ?_⟩
    rw [← h, massRight_ofMat, massLeft_ofMat]
    simp only [Matrix.mul_assoc]
  · rintro ⟨T, rfl⟩
    have h1 := massRight_fix (Mx := Mx) hV (X * T)
    have h2 := massLeft_fix (Mv := Mv) hX (T * Vᵀ)
    rw [h1]
    simpa only [Matrix.mul_assoc] using h2

end Ranges

namespace FEData

variable (D : FEData ι κ m n) [Fact D.Mx.PosDef] [Fact D.Mv.PosDef] [DecidableEq r] [DecidableEq r']

/-- arXiv 2303.01856, Eq. (20a): the semi-discrete weak form on `T_V`, with `δ tr(Φᵀ C_x K)`
added, is the K-equation.  (20c) adds a different term and (20b) none, so the three substeps are
not the restrictions of one stabilised form on the full space. -/
theorem weak_kRhs_iff {V : Matrix n r ℝ} (hV : Vᵀ * D.Mv * V = 1) (δ t : ℝ) (K K' : Matrix m r ℝ) :
    (∀ Φ : Matrix m r ℝ, ⟪ofMat D.Mx D.Mv (Φ * Vᵀ), ofMat D.Mx D.Mv (K' * Vᵀ)⟫ +
        δ * Matrix.trace (Φᵀ * D.Cx * K) =
        D.res t (ofMat D.Mx D.Mv (K * Vᵀ)) (ofMat D.Mx D.Mv (Φ * Vᵀ))) ↔
      D.Mx * K' = D.kRhs V t K - δ • (D.Cx * K) := by
  have key : ∀ Φ : Matrix m r ℝ,
      ⟪ofMat D.Mx D.Mv (Φ * Vᵀ), ofMat D.Mx D.Mv (K' * Vᵀ)⟫ + δ * Matrix.trace (Φᵀ * D.Cx * K) -
        D.res t (ofMat D.Mx D.Mv (K * Vᵀ)) (ofMat D.Mx D.Mv (Φ * Vᵀ)) =
      Matrix.trace (Φᵀ * (D.Mx * K' - (D.kRhs V t K - δ • (D.Cx * K)))) := by
    intro Φ
    have e1 : Matrix.trace ((Φ * Vᵀ)ᵀ * D.Mx * (K' * Vᵀ) * D.Mv) =
        Matrix.trace (Φᵀ * (D.Mx * K')) := by
      rw [show (Φ * Vᵀ)ᵀ * D.Mx * (K' * Vᵀ) * D.Mv = V * (Φᵀ * D.Mx * K' * (Vᵀ * D.Mv)) by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc],
        Matrix.trace_mul_comm, show Φᵀ * D.Mx * K' * (Vᵀ * D.Mv) * V =
          Φᵀ * D.Mx * K' * (Vᵀ * D.Mv * V) by simp only [Matrix.mul_assoc], hV, Matrix.mul_one,
        Matrix.mul_assoc]
    have e2 : Matrix.trace ((Φ * Vᵀ)ᵀ * D.rhs t (K * Vᵀ)) = Matrix.trace (Φᵀ * D.kRhs V t K) := by
      rw [show (Φ * Vᵀ)ᵀ * D.rhs t (K * Vᵀ) = V * (Φᵀ * D.rhs t (K * Vᵀ)) by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc],
        Matrix.trace_mul_comm, Matrix.mul_assoc, rhs_mul]
    rw [inner_ofMat, res_ofMat, e1, e2]
    simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_assoc]
    ring
  constructor
  · intro h
    have : D.Mx * K' - (D.kRhs V t K - δ • (D.Cx * K)) = 0 :=
      eq_zero_of_forall_trace fun Φ => by rw [← key Φ, h Φ, sub_self]
    exact sub_eq_zero.1 this
  · intro h Φ
    have := key Φ
    rw [h, sub_self, Matrix.mul_zero, Matrix.trace_zero] at this
    exact sub_eq_zero.1 this

/-- arXiv 2303.01856, Eq. (20c): the semi-discrete weak form on `T_X`, with `δ tr(Φᵀ C_v L)`
added, is the L-equation. -/
theorem weak_lRhs_iff {X : Matrix m r ℝ} (hX : Xᵀ * D.Mx * X = 1) (δ t : ℝ) (L L' : Matrix n r ℝ) :
    (∀ Φ : Matrix n r ℝ, ⟪ofMat D.Mx D.Mv (X * Φᵀ), ofMat D.Mx D.Mv (X * L'ᵀ)⟫ +
        δ * Matrix.trace (Φᵀ * D.Cv * L) =
        D.res t (ofMat D.Mx D.Mv (X * Lᵀ)) (ofMat D.Mx D.Mv (X * Φᵀ))) ↔
      D.Mv * L' = D.lRhs X t L - δ • (D.Cv * L) := by
  have key : ∀ Φ : Matrix n r ℝ,
      ⟪ofMat D.Mx D.Mv (X * Φᵀ), ofMat D.Mx D.Mv (X * L'ᵀ)⟫ + δ * Matrix.trace (Φᵀ * D.Cv * L) -
        D.res t (ofMat D.Mx D.Mv (X * Lᵀ)) (ofMat D.Mx D.Mv (X * Φᵀ)) =
      Matrix.trace (Φᵀ * (D.Mv * L' - (D.lRhs X t L - δ • (D.Cv * L)))) := by
    intro Φ
    have e1 : Matrix.trace ((X * Φᵀ)ᵀ * D.Mx * (X * L'ᵀ) * D.Mv) =
        Matrix.trace (Φᵀ * (D.Mv * L')) := by
      rw [show (X * Φᵀ)ᵀ * D.Mx * (X * L'ᵀ) * D.Mv = Φ * (Xᵀ * D.Mx * X) * L'ᵀ * D.Mv by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc], hX,
        Matrix.mul_one, ← Matrix.trace_transpose]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        transpose_eq_of_posDef (Fact.out : D.Mv.PosDef)]
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have e2 : Matrix.trace ((X * Φᵀ)ᵀ * D.rhs t (X * Lᵀ)) = Matrix.trace (Φᵀ * D.lRhs X t L) := by
      rw [← rhs_transpose_mul, ← Matrix.trace_transpose]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [inner_ofMat, res_ofMat, e1, e2]
    simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_assoc]
    ring
  constructor
  · intro h
    have : D.Mv * L' - (D.lRhs X t L - δ • (D.Cv * L)) = 0 :=
      eq_zero_of_forall_trace fun Φ => by rw [← key Φ, h Φ, sub_self]
    exact sub_eq_zero.1 this
  · intro h Φ
    have := key Φ
    rw [h, sub_self, Matrix.mul_zero, Matrix.trace_zero] at this
    exact sub_eq_zero.1 this

/-- The two sides of the weak form on `T_{X,V}` in the small matrices. -/
lemma res_S {X : Matrix m r ℝ} {V : Matrix n r' ℝ} (hX : Xᵀ * D.Mx * X = 1)
    (hV : Vᵀ * D.Mv * V = 1) (t : ℝ) (S S' T : Matrix r r' ℝ) :
    ⟪ofMat D.Mx D.Mv (X * T * Vᵀ), ofMat D.Mx D.Mv (X * S' * Vᵀ)⟫ = Matrix.trace (Tᵀ * S') ∧
      D.res t (ofMat D.Mx D.Mv (X * S * Vᵀ)) (ofMat D.Mx D.Mv (X * T * Vᵀ)) =
        -Matrix.trace (Tᵀ * D.sRhs X V t S) := by
  constructor
  · rw [inner_ofMat, show (X * T * Vᵀ)ᵀ * D.Mx * (X * S' * Vᵀ) * D.Mv =
      V * (Tᵀ * (Xᵀ * D.Mx * X) * S' * (Vᵀ * D.Mv)) by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc], hX,
      Matrix.mul_one, Matrix.trace_mul_comm, show Tᵀ * S' * (Vᵀ * D.Mv) * V =
        Tᵀ * S' * (Vᵀ * D.Mv * V) by simp only [Matrix.mul_assoc], hV, Matrix.mul_one]
  · rw [res_ofMat, show (X * T * Vᵀ)ᵀ * D.rhs t (X * S * Vᵀ) =
      V * (Tᵀ * (Xᵀ * D.rhs t (X * S * Vᵀ))) by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc],
      Matrix.trace_mul_comm, show Tᵀ * (Xᵀ * D.rhs t (X * S * Vᵀ)) * V =
        Tᵀ * (Xᵀ * D.rhs t (X * S * Vᵀ) * V) by simp only [Matrix.mul_assoc],
      transpose_mul_rhs_mul, Matrix.mul_neg, Matrix.trace_neg]

/-- arXiv 2303.01856, Eq. (20b): the weak form on `T_{X,V}` with all signs of the right-hand
side flipped is the S-equation. -/
theorem weak_sRhs_iff {X : Matrix m r ℝ} {V : Matrix n r' ℝ} (hX : Xᵀ * D.Mx * X = 1)
    (hV : Vᵀ * D.Mv * V = 1) (t : ℝ) (S S' : Matrix r r' ℝ) :
    (∀ T : Matrix r r' ℝ, ⟪ofMat D.Mx D.Mv (X * T * Vᵀ), ofMat D.Mx D.Mv (X * S' * Vᵀ)⟫ =
        -D.res t (ofMat D.Mx D.Mv (X * S * Vᵀ)) (ofMat D.Mx D.Mv (X * T * Vᵀ))) ↔
      S' = D.sRhs X V t S := by
  constructor
  · intro h
    refine sub_eq_zero.1 (eq_zero_of_forall_trace fun T => ?_)
    have h1 := h T
    rw [(D.res_S hX hV t S S' T).1, (D.res_S hX hV t S S' T).2, neg_neg] at h1
    rw [Matrix.mul_sub, Matrix.trace_sub, h1, sub_self]
  · rintro rfl T
    rw [(D.res_S hX hV t S (D.sRhs X V t S) T).1, (D.res_S hX hV t S (D.sRhs X V t S) T).2,
      neg_neg]

/-- arXiv 2303.01856, Eq. (21): the weak form on `T_{X,V}` is the forward S-equation. -/
theorem weak_sRhs_forward_iff {X : Matrix m r ℝ} {V : Matrix n r' ℝ} (hX : Xᵀ * D.Mx * X = 1)
    (hV : Vᵀ * D.Mv * V = 1) (t : ℝ) (S S' : Matrix r r' ℝ) :
    (∀ T : Matrix r r' ℝ, ⟪ofMat D.Mx D.Mv (X * T * Vᵀ), ofMat D.Mx D.Mv (X * S' * Vᵀ)⟫ =
        D.res t (ofMat D.Mx D.Mv (X * S * Vᵀ)) (ofMat D.Mx D.Mv (X * T * Vᵀ))) ↔
      S' = -D.sRhs X V t S := by
  constructor
  · intro h
    refine sub_eq_zero.1 (eq_zero_of_forall_trace fun T => ?_)
    have h1 := h T
    rw [(D.res_S hX hV t S S' T).1, (D.res_S hX hV t S S' T).2] at h1
    rw [Matrix.mul_sub, Matrix.trace_sub, h1, Matrix.mul_neg, Matrix.trace_neg, sub_self]
  · rintro rfl T
    rw [(D.res_S hX hV t S (-D.sRhs X V t S) T).1, (D.res_S hX hV t S (-D.sRhs X V t S) T).2,
      Matrix.mul_neg, Matrix.trace_neg]

/-- arXiv 2303.01856, Eqs. (20a)–(20c) (not stated in the paper).  The stabilisation field
`M_x⁻¹ C_x Y + Y C_vᵀ M_v⁻¹` is tangent at `Y = X S Vᵀ`: the tangent projector fixes it. -/
theorem tangent_stab {X : Matrix m r ℝ} {V : Matrix n r' ℝ} (hX : Xᵀ * D.Mx * X = 1)
    (hV : Vᵀ * D.Mv * V = 1) (S : Matrix r r' ℝ) :
    tangent (massLeft X) (massRight V) (D.stabX (ofMat D.Mx D.Mv (X * S * Vᵀ)) +
        D.stabV (ofMat D.Mx D.Mv (X * S * Vᵀ))) =
      D.stabX (ofMat D.Mx D.Mv (X * S * Vᵀ)) + D.stabV (ofMat D.Mx D.Mv (X * S * Vᵀ)) := by
  set a := D.stabX (ofMat D.Mx D.Mv (X * S * Vᵀ)) with ha
  set b := D.stabV (ofMat D.Mx D.Mv (X * S * Vᵀ)) with hb
  have h1 : massRight V a = a := by
    have := massRight_fix (Mx := D.Mx) hV (D.Mx⁻¹ * D.Cx * (X * S))
    rw [ha, stabX_ofMat]
    simpa only [Matrix.mul_assoc] using this
  have h2 : massLeft X b = b := by
    have := massLeft_fix (Mv := D.Mv) hX (S * Vᵀ * D.Cvᵀ * D.Mv⁻¹)
    rw [hb, stabV_ofMat]
    simpa only [Matrix.mul_assoc] using this
  rw [tangent_apply, map_add, map_add, map_add, h1, h2, massLeft_massRight_comm X V b, h2]
  abel

/-- Why `δ` may be missing in (20b), which the paper does not explain.  At `Y = X S Vᵀ` the
three fields of Algorithm 1, with `δ` in the K- and L-steps only, add up to the tangent
projection of the stabilised field `F - δ (M_x⁻¹ C_x + C_vᵀ M_v⁻¹)`.  So Algorithm 1 is a
consistent splitting of the stabilised projected dynamics, although for `δ > 0` it is not the
KSL splitting of this field. -/
theorem ksl_fields_sum {X : Matrix m r ℝ} {V : Matrix n r' ℝ} (hX : Xᵀ * D.Mx * X = 1)
    (hV : Vᵀ * D.Mv * V = 1) (S : Matrix r r' ℝ) (δ t : ℝ) :
    (massRight V (D.field t (ofMat D.Mx D.Mv (X * S * Vᵀ))) -
        δ • D.stabX (ofMat D.Mx D.Mv (X * S * Vᵀ))) +
      -massLeft X (massRight V (D.field t (ofMat D.Mx D.Mv (X * S * Vᵀ)))) +
      (massLeft X (D.field t (ofMat D.Mx D.Mv (X * S * Vᵀ))) -
        δ • D.stabV (ofMat D.Mx D.Mv (X * S * Vᵀ))) =
    tangent (massLeft X) (massRight V) (D.field t (ofMat D.Mx D.Mv (X * S * Vᵀ)) -
      δ • (D.stabX (ofMat D.Mx D.Mv (X * S * Vᵀ)) + D.stabV (ofMat D.Mx D.Mv (X * S * Vᵀ)))) := by
  have h := D.tangent_stab hX hV S
  rw [tangent_apply] at h
  set Y := ofMat D.Mx D.Mv (X * S * Vᵀ)
  set z := D.stabX Y + D.stabV Y with hz
  set Z := D.field t Y
  have e : massLeft X (Z - δ • z) + massRight V (Z - δ • z) - massLeft X (massRight V (Z - δ • z)) =
      (massLeft X Z + massRight V Z - massLeft X (massRight V Z)) -
        δ • (massLeft X z + massRight V z - massLeft X (massRight V z)) := by
    simp only [map_sub, map_smul, smul_sub, smul_add]
    abel
  rw [tangent_apply, e, h, hz, smul_add]
  abel

end FEData

end FE

section Vlasov

open MeasureTheory

/-- Euclidean `ℝ^d`, used for both position and velocity. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {κ a b : Type*} [Fintype κ] [Fintype a] [Fintype b]

/-- `Ω_v^{(ν)} = {v | n^{(ν)} · v < 0}` of arXiv 2303.01856, Sec. 2.  The velocity domain is
carried by the measure `μv`. -/
def velHalf (N : Rd d) : Set (Rd d) := {v | ⟪N, v⟫ < 0}

/-- The inflow boundary `Γ⁻ = {(x, v) | x ∈ ∂Ω_x, v · n(x) < 0}` of arXiv 2303.01856, Eq. (2),
with `∂Ω_x = ⋃_ν Γ^{(ν)}`. -/
def inflow (Γ : κ → Set (Rd d)) (n : Rd d → Rd d) : Set (Rd d × Rd d) :=
  {p | p.1 ∈ ⋃ ν, Γ ν ∧ ⟪n p.1, p.2⟫ < 0}

/-- arXiv 2303.01856, Sec. 2.2: for a piecewise linear boundary, i.e. a normal that is constant
on each piece, `Γ⁻ = ⋃_ν Γ^{(ν)} × Ω_v^{(ν)}`. -/
theorem inflow_eq_iUnion {Γ : κ → Set (Rd d)} {n : Rd d → Rd d} {N : κ → Rd d}
    (hn : ∀ ν, ∀ x ∈ Γ ν, n x = N ν) :
    inflow Γ n = ⋃ ν, Γ ν ×ˢ velHalf (N ν) := by
  ext ⟨x, v⟩
  simp only [inflow, velHalf, mem_ofPred_eq, mem_iUnion, mem_prod]
  constructor
  · rintro ⟨⟨ν, hx⟩, hv⟩
    exact ⟨ν, hx, by rwa [hn ν x hx] at hv⟩
  · rintro ⟨ν, hx, hv⟩
    exact ⟨⟨ν, hx⟩, by rwa [hn ν x hx]⟩

/-- `Ω_v^{(ν)}` is measurable. -/
lemma measurableSet_velHalf (N : Rd d) : MeasurableSet (velHalf N) :=
  measurableSet_lt (by fun_prop) measurable_const

/-- Integral of a finite sum of separated functions over a product measure. -/
lemma tensor_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] (S : Matrix a b ℝ) {F : a → α → ℝ} {G : b → β → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hG : ∀ j, Integrable (G j) ν) :
    Integrable (fun p : α × β => ∑ i, ∑ j, S i j * (F i p.1 * G j p.2)) (μ.prod ν) ∧
      ∫ p, ∑ i, ∑ j, S i j * (F i p.1 * G j p.2) ∂(μ.prod ν) =
        ∑ i, ∑ j, S i j * ((∫ x, F i x ∂μ) * ∫ y, G j y ∂ν) := by
  have h : ∀ i j, Integrable (fun p : α × β => S i j * (F i p.1 * G j p.2)) (μ.prod ν) :=
    fun i j => ((hF i).mul_prod (hG j)).const_mul _
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => h i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_prod_mul]

/-- The function `∑_{ij} S_{ij} X_i(x) V_j(v)`: a low-rank function, or an FE function. -/
def tensor (S : Matrix a b ℝ) (X : a → Rd d → ℝ) (V : b → Rd d → ℝ) (p : Rd d × Rd d) : ℝ :=
  ∑ i, ∑ j, S i j * (X i p.1 * V j p.2)

/-- The partial derivative `∂_k g = Dg(x) e_k`. -/
noncomputable def pd (k : Fin d) (g : Rd d → ℝ) (x : Rd d) : ℝ :=
  fderiv ℝ g x (EuclideanSpace.single k 1)

/-- `Dg(x) v = ∑_k v_k ∂_k g(x)`. -/
lemma fderiv_eq_sum_pd (g : Rd d → ℝ) (x v : Rd d) :
    fderiv ℝ g x v = ∑ k, v k * pd k g x := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [map_sum, pd]

/-- The `x`-derivative of a separated function. -/
lemma fderiv_tensor_fst {S : Matrix a b ℝ} {X : a → Rd d → ℝ} {V : b → Rd d → ℝ} {x : Rd d}
    (hx : ∀ i, DifferentiableAt ℝ (X i) x) (v w : Rd d) :
    fderiv ℝ (fun y => tensor S X V (y, v)) x w =
      ∑ i, ∑ j, S i j * (fderiv ℝ (X i) x w * V j v) := by
  have h : HasFDerivAt (fun y => tensor S X V (y, v))
      (∑ i, ∑ j, (S i j * V j v) • fderiv ℝ (X i) x) x := by
    unfold tensor
    refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
    have := ((hx i).hasFDerivAt.const_mul (S i j * V j v))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [h.fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `v`-derivative of a separated function. -/
lemma fderiv_tensor_snd {S : Matrix a b ℝ} {X : a → Rd d → ℝ} {V : b → Rd d → ℝ} {v : Rd d}
    (hv : ∀ j, DifferentiableAt ℝ (V j) v) (x w : Rd d) :
    fderiv ℝ (fun y => tensor S X V (x, y)) v w =
      ∑ i, ∑ j, S i j * (X i x * fderiv ℝ (V j) v w) := by
  have h : HasFDerivAt (fun y => tensor S X V (x, y))
      (∑ i, ∑ j, (S i j * X i x) • fderiv ℝ (V j) v) v := by
    unfold tensor
    refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
    have := ((hv j).hasFDerivAt.const_mul (S i j * X i x))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [h.fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (μx μv σ : Measure (Rd d)) (Γ : κ → Set (Rd d)) (n : Rd d → Rd d)

/-- The form `a` of arXiv 2303.01856, Eq. (5), at one time, with `E = E(t, ·)`: `a(u, w) = ∫_Ω
(v · ∇_x u - E · ∇_v u) w dx dv - ∫_{Γ⁻} (v · n) u w ds`.  `μx`, `μv` are the Lebesgue measures
on `Ω_x`, `Ω_v` and `σ` is the surface measure on `∂Ω_x`, all arbitrary here; `ds = σ ⊗ μv`. `v
· ∇_x u` is written as the classical directional derivative, which exists a.e. for FE functions
(`isSeparable_of_lipschitz`). -/
noncomputable def formA (E : Rd d → Rd d) (u w : Rd d × Rd d → ℝ) : ℝ :=
  ∫ p, (fderiv ℝ (fun y => u (y, p.2)) p.1 p.2 - fderiv ℝ (fun y => u (p.1, y)) p.2 (E p.1)) * w p
      ∂(μx.prod μv)
    - ∫ p in inflow Γ n, ⟪n p.1, p.2⟫ * u p * w p ∂(σ.prod μv)

/-- The functional `ℓ(w) = -∫_{Γ⁻} (v · n) g w ds` of arXiv 2303.01856, Eq. (5). -/
noncomputable def formL (g w : Rd d × Rd d → ℝ) : ℝ :=
  -∫ p in inflow Γ n, ⟪n p.1, p.2⟫ * g p * w p ∂(σ.prod μv)

variable {μx μv σ Γ n}

/-- arXiv 2303.01856, Sec. 2.2: **a piecewise linear boundary keeps the boundary term
separable.** For `u = ∑ S_{ij} X_i ⊗ V_j` and `w = Φ ⊗ Ψ`, the integral over `Γ⁻` is the finite
sum, over the pieces `ν`, of `S_{ij} (Φ, X_i)_{L²(Γ^{(ν)})} (Ψ, n^{(ν)} · v
V_j)_{L²(Ω_v^{(ν)})}`. The pieces are disjoint, so a corner belongs to one piece; corners are
null sets for `σ`. -/
theorem inflow_integral_tensor [SFinite σ] [SFinite μv] {N : κ → Rd d}
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n x = N ν) (S : Matrix a b ℝ) {X : a → Rd d → ℝ} {V : b → Rd d → ℝ}
    {Φ Ψ : Rd d → ℝ} (hX : ∀ ν i, IntegrableOn (fun x => Φ x * X i x) (Γ ν) σ)
    (hV : ∀ ν j, IntegrableOn (fun v => Ψ v * (⟪N ν, v⟫ * V j v)) (velHalf (N ν)) μv) :
    ∫ p in inflow Γ n, ⟪n p.1, p.2⟫ * tensor S X V p * (Φ p.1 * Ψ p.2) ∂(σ.prod μv) =
      ∑ ν, ∑ i, ∑ j, S i j * ((∫ x in Γ ν, Φ x * X i x ∂σ) *
        ∫ v in velHalf (N ν), Ψ v * (⟪N ν, v⟫ * V j v) ∂μv) := by
  classical
  set H : Rd d × Rd d → ℝ := fun p => ⟪n p.1, p.2⟫ * tensor S X V p * (Φ p.1 * Ψ p.2) with hH
  set R : κ → Rd d × Rd d → ℝ := fun ν p => ∑ i, ∑ j, S i j *
    ((Φ p.1 * X i p.1) * (Ψ p.2 * (⟪N ν, p.2⟫ * V j p.2))) with hR
  have hmeas : ∀ ν, MeasurableSet (Γ ν ×ˢ velHalf (N ν)) := fun ν =>
    (hΓ ν).prod (measurableSet_velHalf _)
  have heq : ∀ ν, EqOn H (R ν) (Γ ν ×ˢ velHalf (N ν)) := by
    rintro ν ⟨x, v⟩ ⟨hx, -⟩
    simp only [hH, hR, tensor, hn ν x hx, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrestr : ∀ ν, (σ.prod μv).restrict (Γ ν ×ˢ velHalf (N ν)) =
      (σ.restrict (Γ ν)).prod (μv.restrict (velHalf (N ν))) := fun ν =>
    (Measure.prod_restrict _ _).symm
  have hsep := fun ν => tensor_prod (μ := σ.restrict (Γ ν)) (ν := μv.restrict (velHalf (N ν))) S
    (F := fun i x => Φ x * X i x) (G := fun j v => Ψ v * (⟪N ν, v⟫ * V j v))
    (fun i => hX ν i) (fun j => hV ν j)
  rw [inflow_eq_iUnion hn, integral_iUnion_fintype hmeas]
  · refine Finset.sum_congr rfl fun ν _ => ?_
    rw [setIntegral_congr_fun (hmeas ν) (heq ν), hrestr ν]
    exact (hsep ν).2
  · intro ν ν' hνν'
    exact Set.disjoint_prod.2 (Or.inl (hdisj hνν'))
  · intro ν
    refine IntegrableOn.congr_fun ?_ (fun p hp => (heq ν hp).symm) (hmeas ν)
    rw [IntegrableOn, hrestr ν]
    exact (hsep ν).1

/-- The regularity used in `formA_tensor`: trial functions differentiable a.e., and all the
integrals that define the paper's coefficient matrices exist.  `isSeparable_of_lipschitz`
derives this for FE functions. -/
structure IsSeparable (μx μv σ : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (E : Rd d → Rd d) (X : a → Rd d → ℝ) (V : b → Rd d → ℝ) (Φ Ψ : Rd d → ℝ) : Prop where
  diffX : ∀ᵐ x ∂μx, ∀ i, DifferentiableAt ℝ (X i) x
  diffV : ∀ᵐ v ∂μv, ∀ j, DifferentiableAt ℝ (V j) v
  intTx : ∀ k i, Integrable (fun x => Φ x * pd k (X i) x) μx
  intMvk : ∀ k j, Integrable (fun v => Ψ v * (v k * V j v)) μv
  intMxE : ∀ k i, Integrable (fun x => Φ x * (E x k * X i x)) μx
  intTv : ∀ k j, Integrable (fun v => Ψ v * pd k (V j) v) μv
  intΓ : ∀ ν i, IntegrableOn (fun x => Φ x * X i x) (Γ ν) σ
  intΩ : ∀ ν j, IntegrableOn (fun v => Ψ v * (⟪N ν, v⟫ * V j v)) (velHalf (N ν)) μv

/-- Reordering of a triple sum. -/
lemma sum_rot {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ i, ∑ j, f i j k := by
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- arXiv 2303.01856, Secs. 2.2–2.4, the master formula: on a separated function and a separated
test function, the form `a` is a finite sum of products of integrals over `Ω_x`, `Ω_v`,
`Γ^{(ν)}`, `Ω_v^{(ν)}`.  All of Eqs. (14), (15), (17) and the assembly in Sec. 3 are instances
of it. -/
theorem formA_tensor [SFinite μx] [SFinite μv] [SFinite σ] {N : κ → Rd d} {E : Rd d → Rd d}
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n x = N ν) (S : Matrix a b ℝ) {X : a → Rd d → ℝ} {V : b → Rd d → ℝ}
    {Φ Ψ : Rd d → ℝ} (h : IsSeparable μx μv σ Γ N E X V Φ Ψ) :
    formA μx μv σ Γ n E (tensor S X V) (fun p => Φ p.1 * Ψ p.2) =
      ∑ k, (∑ i, ∑ j, S i j * ((∫ x, Φ x * pd k (X i) x ∂μx) * ∫ v, Ψ v * (v k * V j v) ∂μv)
        - ∑ i, ∑ j, S i j * ((∫ x, Φ x * (E x k * X i x) ∂μx) * ∫ v, Ψ v * pd k (V j) v ∂μv))
      - ∑ ν, ∑ i, ∑ j, S i j * ((∫ x in Γ ν, Φ x * X i x ∂σ) *
          ∫ v in velHalf (N ν), Ψ v * (⟪N ν, v⟫ * V j v) ∂μv) := by
  have hR1 := fun k => tensor_prod (μ := μx) (ν := μv) S (F := fun i x => Φ x * pd k (X i) x)
    (G := fun j v => Ψ v * (v k * V j v)) (h.intTx k) (h.intMvk k)
  have hR2 := fun k => tensor_prod (μ := μx) (ν := μv) S (F := fun i x => Φ x * (E x k * X i x))
    (G := fun j v => Ψ v * pd k (V j) v) (h.intMxE k) (h.intTv k)
  have hae : (fun p : Rd d × Rd d => (fderiv ℝ (fun y => tensor S X V (y, p.2)) p.1 p.2 -
      fderiv ℝ (fun y => tensor S X V (p.1, y)) p.2 (E p.1)) * (Φ p.1 * Ψ p.2)) =ᵐ[μx.prod μv]
      fun p => ∑ k, ((∑ i, ∑ j, S i j * ((Φ p.1 * pd k (X i) p.1) * (Ψ p.2 * (p.2 k * V j p.2)))) -
        ∑ i, ∑ j, S i j * ((Φ p.1 * (E p.1 k * X i p.1)) * (Ψ p.2 * pd k (V j) p.2))) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h.diffX,
      Measure.quasiMeasurePreserving_snd.ae h.diffV] with p hx hv
    obtain ⟨x, v⟩ := p
    simp only at hx hv ⊢
    rw [fderiv_tensor_fst hx, fderiv_tensor_snd hv, Finset.sum_sub_distrib, sub_mul]
    congr 1
    · simp only [fderiv_eq_sum_pd (X _) x v, Finset.sum_mul, Finset.mul_sum]
      rw [sum_rot]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [fderiv_eq_sum_pd (V _) v (E x), Finset.sum_mul, Finset.mul_sum]
      rw [sum_rot]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      ring
  have hI : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun p : Rd d × Rd d =>
      (∑ i, ∑ j, S i j * ((Φ p.1 * pd k (X i) p.1) * (Ψ p.2 * (p.2 k * V j p.2)))) -
        ∑ i, ∑ j, S i j * ((Φ p.1 * (E p.1 k * X i p.1)) * (Ψ p.2 * pd k (V j) p.2)))
      (μx.prod μv) := fun k _ => (hR1 k).1.sub (hR2 k).1
  unfold formA
  rw [integral_congr_ae hae, integral_finsetSum _ hI,
    inflow_integral_tensor hΓ hdisj hn S h.intΓ h.intΩ]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_sub (hR1 k).1 (hR2 k).1, (hR1 k).2, (hR2 k).2]

/-- The `L²(Ω)` product with a separated function. -/
theorem integral_tensor_mul [SFinite μx] [SFinite μv] (S : Matrix a b ℝ) {X : a → Rd d → ℝ}
    {V : b → Rd d → ℝ} {Φ Ψ : Rd d → ℝ} (hX : ∀ i, Integrable (fun x => Φ x * X i x) μx)
    (hV : ∀ j, Integrable (fun v => Ψ v * V j v) μv) :
    ∫ p, tensor S X V p * (Φ p.1 * Ψ p.2) ∂(μx.prod μv) =
      ∑ i, ∑ j, S i j * ((∫ x, Φ x * X i x ∂μx) * ∫ v, Ψ v * V j v ∂μv) := by
  rw [← (tensor_prod S hX hV).2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tensor, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- arXiv 2303.01856, Sec. 2: for separated inflow data, `ℓ` of a separated test function is a
finite sum of products; this is why the paper assumes `g = ∑_μ g_x^μ ⊗ g_v^μ`. -/
theorem formL_tensor [SFinite σ] [SFinite μv] {N : κ → Rd d}
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n x = N ν) (S : Matrix a b ℝ) {X : a → Rd d → ℝ} {V : b → Rd d → ℝ}
    {Φ Ψ : Rd d → ℝ} (hX : ∀ ν i, IntegrableOn (fun x => Φ x * X i x) (Γ ν) σ)
    (hV : ∀ ν j, IntegrableOn (fun v => Ψ v * (⟪N ν, v⟫ * V j v)) (velHalf (N ν)) μv) :
    formL μv σ Γ n (tensor S X V) (fun p => Φ p.1 * Ψ p.2) =
      -∑ ν, ∑ i, ∑ j, S i j * ((∫ x in Γ ν, Φ x * X i x ∂σ) *
          ∫ v in velHalf (N ν), Ψ v * (⟪N ν, v⟫ * V j v) ∂μv) := by
  unfold formL
  rw [inflow_integral_tensor hΓ hdisj hn S hX hV]

section Restriction

variable {r μ' : Type*} [Fintype r] [DecidableEq r] [Fintype μ'] [DecidableEq μ']

/-- A double sum weighted by the identity matrix. -/
lemma sum_one_mul {α : Type*} [Fintype α] [DecidableEq α] (f : α → α → ℝ) :
    ∑ i, ∑ j, (1 : Matrix α α ℝ) i j * f i j = ∑ i, f i i := by
  simp [Matrix.one_apply]

/-- Integrability of a double sum. -/
lemma integrable_sum_sum {α β X : Type*} [Fintype α] [Fintype β] [MeasurableSpace X]
    {μ : Measure X} {F : α → β → X → ℝ} (hF : ∀ k j, Integrable (F k j) μ) :
    Integrable (fun v => ∑ k, ∑ j, F k j v) μ :=
  integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hF k j

/-- Linearity of the integral for a double sum. -/
lemma integral_sum_sum_const_mul {α β X : Type*} [Fintype α] [Fintype β] [MeasurableSpace X]
    {μ : Measure X} (c : α → β → ℝ) (f : α → β → X → ℝ)
    (h : ∀ k j, Integrable (fun x => c k j * f k j x) μ) :
    ∫ x, ∑ k, ∑ j, c k j * f k j x ∂μ = ∑ k, ∑ j, c k j * ∫ x, f k j x ∂μ := by
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h k j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun j _ => h k j]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- Integral of a function given piecewise by indicators over a disjoint union. -/
lemma setIntegral_iUnion_indicator [DecidableEq κ] (hΓ : ∀ ν, MeasurableSet (Γ ν))
    (hdisj : Pairwise (Function.onFun Disjoint Γ)) {f : κ → Rd d → ℝ}
    (hf : ∀ ν, IntegrableOn (f ν) (Γ ν) σ) :
    ∫ x in ⋃ ν, Γ ν, ∑ ν, (Γ ν).indicator (1 : Rd d → ℝ) x * f ν x ∂σ =
      ∑ ν, ∫ x in Γ ν, f ν x ∂σ := by
  have heq : ∀ ν, EqOn (fun x => ∑ ν', (Γ ν').indicator (1 : Rd d → ℝ) x * f ν' x) (f ν) (Γ ν) := by
    intro ν x hx
    simp only
    rw [Finset.sum_eq_single ν]
    · simp [Set.indicator_of_mem hx]
    · intro ν' _ hne
      have : x ∉ Γ ν' := fun hx' => Set.disjoint_left.1 (hdisj hne.symm) hx hx'
      simp [Set.indicator_of_notMem this]
    · simp
  rw [integral_iUnion_fintype hΓ hdisj fun ν => (hf ν).congr_fun (heq ν).symm (hΓ ν)]
  exact Finset.sum_congr rfl fun ν _ => setIntegral_congr_fun (hΓ ν) (heq ν)

variable {K Kd V : r → Rd d → ℝ} {ψ : Rd d → ℝ} {gx gv : μ' → Rd d → ℝ}
  {N : κ → Rd d} {E : Rd d → Rd d}

/-- The symmetric matrix `𝒜_x^k = [∫ v_k V_j V_i dv]` of arXiv 2303.01856, Sec. 2.2. -/
noncomputable def matAx (μv : Measure (Rd d)) (V : r → Rd d → ℝ) (k : Fin d) : Matrix r r ℝ :=
  Matrix.of fun i j => ∫ v, V i v * (v k * V j v) ∂μv

/-- The matrix `𝒦_x(t, x) = [∑_k E_k(t, x) ∫ ∂_{v_k} V_j V_i dv]` of arXiv 2303.01856, Sec. 2.2. -/
noncomputable def matKx (μv : Measure (Rd d)) (E : Rd d → Rd d) (V : r → Rd d → ℝ) (x : Rd d) :
    Matrix r r ℝ :=
  Matrix.of fun i j => ∑ k, E x k * ∫ v, V i v * pd k (V j) v ∂μv

/-- The boundary matrix `ℬ_x(x) = [∑_ν χ_{Γ^{(ν)}}(x) ∫_{Ω_v^{(ν)}} n^{(ν)} · v V_j V_i dv]` of
arXiv 2303.01856, Sec. 2.2. -/
noncomputable def matBxx (μv : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (V : r → Rd d → ℝ) (x : Rd d) : Matrix r r ℝ :=
  Matrix.of fun i j => ∑ ν, (Γ ν).indicator (1 : Rd d → ℝ) x *
    ∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * V j v) ∂μv

/-- The vector `G_x(t, x)` of arXiv 2303.01856, Sec. 2.2, for `g = ∑_μ g_x^μ ⊗ g_v^μ`. -/
noncomputable def vecGx (μv : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (gx gv : μ' → Rd d → ℝ) (V : r → Rd d → ℝ) (x : Rd d) (i : r) : ℝ :=
  ∑ ν, (Γ ν).indicator (1 : Rd d → ℝ) x * ∑ μ, gx μ x *
    ∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * gv μ v) ∂μv

/-- arXiv 2303.01856, Eq. (14) (Sec. 2.2).  On `f = ∑_j K_j ⊗ V_j⁰` with `L²`-orthonormal `V⁰`
and the test function `ψ ⊗ V_i⁰` of `T_{V⁰}`, the residual of the weak form (5) equals `(∂_t K +
∑_k 𝒜_x^k ∂_k K - 𝒦_x K, ψ e_i)_{L²(Ω_x)} - (ℬ_x K, ψ e_i)_{L²(Γ_x)} + (G_x, ψ e_i)_{L²(Γ_x)}`.
So the restriction of (5) to `T_{V⁰}` is the Friedrichs system (14).  `Kd` stands for `∂_t K(t,
·)`. -/
theorem weak_K_restriction [SFinite μx] [SFinite μv] [SFinite σ] [DecidableEq κ]
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n x = N ν) (i : r)
    (hV : ∀ i j, ∫ v, V i v * V j v ∂μv = if i = j then 1 else 0)
    (hVi : ∀ j, Integrable (fun v => V i v * V j v) μv)
    (hsep : IsSeparable μx μv σ Γ N E K V ψ (V i))
    (hKd : ∀ j, Integrable (fun x => ψ x * Kd j x) μx)
    (hgx : ∀ ν μ, IntegrableOn (fun x => ψ x * gx μ x) (Γ ν) σ)
    (hgv : ∀ ν μ, IntegrableOn (fun v => V i v * (⟪N ν, v⟫ * gv μ v)) (velHalf (N ν)) μv) :
    ∫ p, tensor 1 Kd V p * (ψ p.1 * V i p.2) ∂(μx.prod μv) +
        formA μx μv σ Γ n E (tensor 1 K V) (fun p => ψ p.1 * V i p.2) -
        formL μv σ Γ n (tensor 1 gx gv) (fun p => ψ p.1 * V i p.2) =
      ∫ x, ψ x * (Kd i x + ∑ k, ∑ j, matAx μv V k i j * pd k (K j) x -
          ∑ j, matKx μv E V x i j * K j x) ∂μx
        - ∫ x in ⋃ ν, Γ ν, ψ x * ∑ j, matBxx μv Γ N V x i j * K j x ∂σ
        + ∫ x in ⋃ ν, Γ ν, ψ x * vecGx μv Γ N gx gv V x i ∂σ := by
  -- left-hand side
  rw [integral_tensor_mul 1 hKd hVi, formA_tensor hΓ hdisj hn 1 hsep,
    formL_tensor hΓ hdisj hn 1 hgx hgv]
  simp only [sum_one_mul]
  -- first integral on the right
  set cA : Fin d → r → ℝ := fun k j => ∫ v, V i v * (v k * V j v) ∂μv with hcA
  set cE : Fin d → r → ℝ := fun k j => ∫ v, V i v * pd k (V j) v ∂μv with hcE
  have hint1 : ∫ x, ψ x * (Kd i x + ∑ k, ∑ j, matAx μv V k i j * pd k (K j) x -
      ∑ j, matKx μv E V x i j * K j x) ∂μx =
      (∫ x, ψ x * Kd i x ∂μx) + ∑ k, (∑ j, cA k j * ∫ x, ψ x * pd k (K j) x ∂μx) -
        ∑ k, ∑ j, cE k j * ∫ x, ψ x * (E x k * K j x) ∂μx := by
    have h1 : ∀ k j, Integrable (fun x => cA k j * (ψ x * pd k (K j) x)) μx := fun k j =>
      (hsep.intTx k j).const_mul _
    have h2 : ∀ k j, Integrable (fun x => cE k j * (ψ x * (E x k * K j x))) μx := fun k j =>
      (hsep.intMxE k j).const_mul _
    have h1' : Integrable (fun x => ∑ k, ∑ j, cA k j * (ψ x * pd k (K j) x)) μx :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h1 k j
    have h2' : Integrable (fun x => ∑ k, ∑ j, cE k j * (ψ x * (E x k * K j x))) μx :=
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => h2 k j
    have e : ∀ x, ψ x * (Kd i x + ∑ k, ∑ j, matAx μv V k i j * pd k (K j) x -
        ∑ j, matKx μv E V x i j * K j x) =
        ψ x * Kd i x + ∑ k, ∑ j, cA k j * (ψ x * pd k (K j) x) -
          ∑ k, ∑ j, cE k j * (ψ x * (E x k * K j x)) := by
      intro x
      have e1 : ψ x * ∑ k, ∑ j, matAx μv V k i j * pd k (K j) x =
          ∑ k, ∑ j, cA k j * (ψ x * pd k (K j) x) := by
        simp only [Finset.mul_sum, matAx, Matrix.of_apply, hcA]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have e2 : ψ x * ∑ j, matKx μv E V x i j * K j x =
          ∑ k, ∑ j, cE k j * (ψ x * (E x k * K j x)) := by
        simp only [matKx, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, hcE]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [mul_sub, mul_add, e1, e2]
    have hadd : Integrable (fun x => ψ x * Kd i x + ∑ k, ∑ j, cA k j * (ψ x * pd k (K j) x)) μx :=
      (hKd i).add h1'
    simp only [e]
    rw [integral_sub hadd h2', integral_add (hKd i) h1', integral_sum_sum_const_mul _ _ h1,
      integral_sum_sum_const_mul _ _ h2]
  -- boundary integrals
  set dB : κ → r → ℝ := fun ν j => ∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * V j v) ∂μv with hdB
  have hb1 : ∫ x in ⋃ ν, Γ ν, ψ x * ∑ j, matBxx μv Γ N V x i j * K j x ∂σ =
      ∑ ν, ∑ j, dB ν j * ∫ x in Γ ν, ψ x * K j x ∂σ := by
    have e : ∀ x, ψ x * ∑ j, matBxx μv Γ N V x i j * K j x =
        ∑ ν, (Γ ν).indicator (1 : Rd d → ℝ) x * ∑ j, dB ν j * (ψ x * K j x) := by
      intro x
      simp only [matBxx, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, hdB]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [e]
    rw [setIntegral_iUnion_indicator hΓ hdisj fun ν =>
      integrable_finsetSum _ fun j _ => (hsep.intΓ ν j).const_mul _]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [integral_finsetSum _ fun j _ => (hsep.intΓ ν j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hb2 : ∫ x in ⋃ ν, Γ ν, ψ x * vecGx μv Γ N gx gv V x i ∂σ =
      ∑ ν, ∑ μ, (∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * gv μ v) ∂μv) *
        ∫ x in Γ ν, ψ x * gx μ x ∂σ := by
    have e : ∀ x, ψ x * vecGx μv Γ N gx gv V x i =
        ∑ ν, (Γ ν).indicator (1 : Rd d → ℝ) x * ∑ μ,
          (∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * gv μ v) ∂μv) * (ψ x * gx μ x) := by
      intro x
      simp only [vecGx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
      ring
    simp only [e]
    rw [setIntegral_iUnion_indicator hΓ hdisj fun ν =>
      integrable_finsetSum _ fun μ _ => (hgx ν μ).const_mul _]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [integral_finsetSum _ fun μ _ => (hgx ν μ).const_mul _]
    exact Finset.sum_congr rfl fun μ _ => integral_const_mul _ _
  rw [hint1, hb1, hb2]
  have hδ : ∑ j, (∫ x, ψ x * Kd j x ∂μx) * ∫ v, V i v * V j v ∂μv = ∫ x, ψ x * Kd i x ∂μx := by
    simp [hV]
  rw [hδ]
  have e1 : ∀ k, ∑ j, (∫ x, ψ x * pd k (K j) x ∂μx) * cA k j =
      ∑ j, cA k j * ∫ x, ψ x * pd k (K j) x ∂μx := fun k =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : ∀ k, ∑ j, (∫ x, ψ x * (E x k * K j x) ∂μx) * cE k j =
      ∑ j, cE k j * ∫ x, ψ x * (E x k * K j x) ∂μx := fun k =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e3 : ∀ ν, ∑ j, (∫ x in Γ ν, ψ x * K j x ∂σ) * dB ν j =
      ∑ j, dB ν j * ∫ x in Γ ν, ψ x * K j x ∂σ := fun ν =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e4 : ∀ ν, ∑ μ, (∫ x in Γ ν, ψ x * gx μ x ∂σ) *
      ∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * gv μ v) ∂μv =
      ∑ μ, (∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * gv μ v) ∂μv) *
        ∫ x in Γ ν, ψ x * gx μ x ∂σ := fun ν =>
    Finset.sum_congr rfl fun μ _ => mul_comm _ _
  simp only [hcA, hcE, hdB] at e1 e2 e3 ⊢
  simp only [Finset.sum_sub_distrib, e1, e2, e3, e4]
  ring

/-- The matrix `𝒜_v^k(t) = [∫ E_k X_j X_i dx]` of arXiv 2303.01856, Sec. 2.4. -/
noncomputable def matAv (μx : Measure (Rd d)) (E : Rd d → Rd d) (X : r → Rd d → ℝ) (k : Fin d) :
    Matrix r r ℝ :=
  Matrix.of fun i j => ∫ x, X i x * (E x k * X j x) ∂μx

/-- The matrix `𝒦_v(v) = [∑_k v_k ∫ ∂_k X_j X_i dx]` of arXiv 2303.01856, Sec. 2.4. -/
noncomputable def matKv (μx : Measure (Rd d)) (X : r → Rd d → ℝ) (v : Rd d) : Matrix r r ℝ :=
  Matrix.of fun i j => ∑ k, v k * ∫ x, X i x * pd k (X j) x ∂μx

/-- The boundary matrix `ℬ_v(v)` of arXiv 2303.01856, Sec. 2.4: a multiplication operator on all
of `Ω_v`, with `χ_{Ω_v^{(ν)}}(v) (n^{(ν)} · v) ∫_{Γ^{(ν)}} X_j X_i ds` in the sum over `ν`. -/
noncomputable def matBvv (σ : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (X : r → Rd d → ℝ) (v : Rd d) : Matrix r r ℝ :=
  Matrix.of fun i j => ∑ ν, (velHalf (N ν)).indicator (1 : Rd d → ℝ) v * (⟪N ν, v⟫ *
    ∫ x in Γ ν, X i x * X j x ∂σ)

/-- The vector `G_v(t, v)` of arXiv 2303.01856, Sec. 2.4, for `g = ∑_μ g_x^μ ⊗ g_v^μ`. -/
noncomputable def vecGv (σ : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (gx gv : μ' → Rd d → ℝ) (X : r → Rd d → ℝ) (v : Rd d) (i : r) : ℝ :=
  ∑ ν, (velHalf (N ν)).indicator (1 : Rd d → ℝ) v * (⟪N ν, v⟫ * ∑ μ, gv μ v *
    ∫ x in Γ ν, X i x * gx μ x ∂σ)

/-- Integral against an indicator. -/
lemma integral_indicator_one_mul {s : Set (Rd d)} (hs : MeasurableSet s) (h : Rd d → ℝ)
    (μ : Measure (Rd d)) : ∫ v, s.indicator (1 : Rd d → ℝ) v * h v ∂μ = ∫ v in s, h v ∂μ := by
  rw [← integral_indicator hs]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  by_cases hv : v ∈ s <;> simp [hv]

/-- Integrability against an indicator. -/
lemma integrable_indicator_one_mul {s : Set (Rd d)} (hs : MeasurableSet s) {h : Rd d → ℝ}
    {μ : Measure (Rd d)} (hh : IntegrableOn h s μ) :
    Integrable (fun v => s.indicator (1 : Rd d → ℝ) v * h v) μ := by
  refine (hh.integrable_indicator hs).congr (Eventually.of_forall fun v => ?_)
  by_cases hv : v ∈ s <;> simp [hv]

/-- arXiv 2303.01856, Eq. (17) (Sec. 2.4).  On `f = ∑_j X_j¹ ⊗ L_j` with `L²`-orthonormal `X¹`
and the test function `X_i¹ ⊗ ψ` of `T_{X¹}`, the residual of the weak form (5) equals `(∂_t L -
∑_k 𝒜_v^k ∂_k L + 𝒦_v L - ℬ_v L + G_v, ψ e_i)_{L²(Ω_v)}`.  There is no boundary integral: the
spatial boundary condition is a multiplication operator in velocity.  `Ld` stands for `∂_t L`. -/
theorem weak_L_restriction [SFinite μx] [SFinite μv] [SFinite σ]
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n x = N ν) {X L Ld : r → Rd d → ℝ} (i : r)
    (hX : ∀ i j, ∫ x, X i x * X j x ∂μx = if i = j then 1 else 0)
    (hXi : ∀ j, Integrable (fun x => X i x * X j x) μx)
    (hsep : IsSeparable μx μv σ Γ N E X L (X i) ψ)
    (hLd : ∀ j, Integrable (fun v => ψ v * Ld j v) μv)
    (hgx : ∀ ν μ, IntegrableOn (fun x => X i x * gx μ x) (Γ ν) σ)
    (hgv : ∀ ν μ, IntegrableOn (fun v => ψ v * (⟪N ν, v⟫ * gv μ v)) (velHalf (N ν)) μv) :
    ∫ p, tensor 1 X Ld p * (X i p.1 * ψ p.2) ∂(μx.prod μv) +
        formA μx μv σ Γ n E (tensor 1 X L) (fun p => X i p.1 * ψ p.2) -
        formL μv σ Γ n (tensor 1 gx gv) (fun p => X i p.1 * ψ p.2) =
      ∫ v, ψ v * (Ld i v - ∑ k, ∑ j, matAv μx E X k i j * pd k (L j) v +
          ∑ j, matKv μx X v i j * L j v - ∑ j, matBvv σ Γ N X v i j * L j v +
          vecGv σ Γ N gx gv X v i) ∂μv := by
  rw [integral_tensor_mul 1 hXi hLd, formA_tensor hΓ hdisj hn 1 hsep,
    formL_tensor hΓ hdisj hn 1 hgx hgv]
  simp only [sum_one_mul]
  have hδ : ∑ j, (∫ x, X i x * X j x ∂μx) * ∫ v, ψ v * Ld j v ∂μv = ∫ v, ψ v * Ld i v ∂μv := by
    simp [hX]
  rw [hδ]
  set ind : κ → Rd d → ℝ := fun ν => (velHalf (N ν)).indicator (1 : Rd d → ℝ) with hind
  have hI3 : ∀ ν j, Integrable (fun v => ind ν v * (ψ v * (⟪N ν, v⟫ * L j v))) μv := fun ν j =>
    integrable_indicator_one_mul (measurableSet_velHalf _) (hsep.intΩ ν j)
  have hI4 : ∀ ν μ, Integrable (fun v => ind ν v * (ψ v * (⟪N ν, v⟫ * gv μ v))) μv := fun ν μ =>
    integrable_indicator_one_mul (measurableSet_velHalf _) (hgv ν μ)
  set a : Fin d → r → ℝ := fun k j => ∫ x, X i x * (E x k * X j x) ∂μx with ha
  set c : Fin d → r → ℝ := fun k j => ∫ x, X i x * pd k (X j) x ∂μx with hc
  set b : κ → r → ℝ := fun ν j => ∫ x in Γ ν, X i x * X j x ∂σ with hb
  set f : κ → μ' → ℝ := fun ν μ => ∫ x in Γ ν, X i x * gx μ x ∂σ with hf
  have h1 : ∀ k j, Integrable (fun v => a k j * (ψ v * pd k (L j) v)) μv := fun k j =>
    (hsep.intTv k j).const_mul _
  have h2 : ∀ k j, Integrable (fun v => c k j * (ψ v * (v k * L j v))) μv := fun k j =>
    (hsep.intMvk k j).const_mul _
  have h3 : ∀ ν j, Integrable (fun v => b ν j * (ind ν v * (ψ v * (⟪N ν, v⟫ * L j v)))) μv :=
    fun ν j => (hI3 ν j).const_mul _
  have h4 : ∀ ν μ, Integrable (fun v => f ν μ * (ind ν v * (ψ v * (⟪N ν, v⟫ * gv μ v)))) μv :=
    fun ν μ => (hI4 ν μ).const_mul _
  have e : ∀ v, ψ v * (Ld i v - ∑ k, ∑ j, matAv μx E X k i j * pd k (L j) v +
      ∑ j, matKv μx X v i j * L j v - ∑ j, matBvv σ Γ N X v i j * L j v +
      vecGv σ Γ N gx gv X v i) =
      ψ v * Ld i v - ∑ k, ∑ j, a k j * (ψ v * pd k (L j) v) +
        ∑ k, ∑ j, c k j * (ψ v * (v k * L j v)) -
        ∑ ν, ∑ j, b ν j * (ind ν v * (ψ v * (⟪N ν, v⟫ * L j v))) +
        ∑ ν, ∑ μ, f ν μ * (ind ν v * (ψ v * (⟪N ν, v⟫ * gv μ v))) := by
    intro v
    have e1 : ψ v * ∑ k, ∑ j, matAv μx E X k i j * pd k (L j) v =
        ∑ k, ∑ j, a k j * (ψ v * pd k (L j) v) := by
      simp only [Finset.mul_sum, matAv, Matrix.of_apply, ha]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e2 : ψ v * ∑ j, matKv μx X v i j * L j v = ∑ k, ∑ j, c k j * (ψ v * (v k * L j v)) := by
      simp only [matKv, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, hc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e3 : ψ v * ∑ j, matBvv σ Γ N X v i j * L j v =
        ∑ ν, ∑ j, b ν j * (ind ν v * (ψ v * (⟪N ν, v⟫ * L j v))) := by
      simp only [matBvv, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, hb, hind]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e4 : ψ v * vecGv σ Γ N gx gv X v i =
        ∑ ν, ∑ μ, f ν μ * (ind ν v * (ψ v * (⟪N ν, v⟫ * gv μ v))) := by
      simp only [vecGv, Finset.mul_sum, hf, hind]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [mul_add, mul_sub, mul_add, mul_sub, e1, e2, e3, e4]
  simp only [e]
  have h01 : Integrable (fun v => ψ v * Ld i v - ∑ k, ∑ j, a k j * (ψ v * pd k (L j) v)) μv :=
    (hLd i).sub (integrable_sum_sum h1)
  have h012 : Integrable (fun v => ψ v * Ld i v - ∑ k, ∑ j, a k j * (ψ v * pd k (L j) v) +
      ∑ k, ∑ j, c k j * (ψ v * (v k * L j v))) μv := h01.add (integrable_sum_sum h2)
  have h0123 : Integrable (fun v => ψ v * Ld i v - ∑ k, ∑ j, a k j * (ψ v * pd k (L j) v) +
      ∑ k, ∑ j, c k j * (ψ v * (v k * L j v)) -
      ∑ ν, ∑ j, b ν j * (ind ν v * (ψ v * (⟪N ν, v⟫ * L j v)))) μv :=
    h012.sub (integrable_sum_sum h3)
  rw [integral_add h0123 (integrable_sum_sum h4), integral_sub h012 (integrable_sum_sum h3),
    integral_add h01 (integrable_sum_sum h2), integral_sub (hLd i) (integrable_sum_sum h1),
    integral_sum_sum_const_mul _ _ h1, integral_sum_sum_const_mul _ _ h2,
    integral_sum_sum_const_mul _ _ h3, integral_sum_sum_const_mul _ _ h4]
  simp only [hind, integral_indicator_one_mul (measurableSet_velHalf _), ha, hc, hb, hf,
    Finset.sum_sub_distrib]
  ring

/-- arXiv 2303.01856, Sec. 2.2: `𝒜_x^k` is symmetric, as a Friedrichs system requires. -/
theorem matAx_transpose (μv : Measure (Rd d)) (V : r → Rd d → ℝ) (k : Fin d) :
    (matAx μv V k)ᵀ = matAx μv V k := by
  ext i j
  simp only [matAx, Matrix.transpose_apply, Matrix.of_apply]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  ring

/-- arXiv 2303.01856, Sec. 2.2: `ℬ_x(x)` is symmetric. -/
theorem matBxx_transpose (μv : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (V : r → Rd d → ℝ) (x : Rd d) : (matBxx μv Γ N V x)ᵀ = matBxx μv Γ N V x := by
  ext i j
  simp only [matBxx, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  ring

/-- Sign of the boundary term of the Friedrichs system (not stated in the paper): `ℬ_x(x)` is
negative semidefinite, for every basis, since `n^{(ν)} · v < 0` on `Ω_v^{(ν)}`. -/
theorem matBxx_nonpos (μv : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (V : r → Rd d → ℝ) (hV : ∀ ν i j,
      IntegrableOn (fun v => V i v * (⟪N ν, v⟫ * V j v)) (velHalf (N ν)) μv)
    (x : Rd d) (c : r → ℝ) : ∑ i, ∑ j, c i * matBxx μv Γ N V x i j * c j ≤ 0 := by
  have e : ∑ i, ∑ j, c i * matBxx μv Γ N V x i j * c j =
      ∑ ν, (Γ ν).indicator (1 : Rd d → ℝ) x *
        ∫ v in velHalf (N ν), ⟪N ν, v⟫ * (∑ i, c i * V i v) ^ 2 ∂μv := by
    have e1 : ∀ ν, ∫ v in velHalf (N ν), ⟪N ν, v⟫ * (∑ i, c i * V i v) ^ 2 ∂μv =
        ∑ i, ∑ j, (c i * c j) * ∫ v in velHalf (N ν), V i v * (⟪N ν, v⟫ * V j v) ∂μv := by
      intro ν
      rw [← integral_sum_sum_const_mul _ _ fun i j => (hV ν i j).const_mul _]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [sq, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [e1, matBxx, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Finset.sum_nonpos fun ν _ => ?_
  refine mul_nonpos_of_nonneg_of_nonpos ?_ ?_
  · by_cases hx : x ∈ Γ ν <;> simp [hx]
  · refine setIntegral_nonpos (measurableSet_velHalf _) fun v hv => ?_
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hv) (sq_nonneg _)

end Restriction

section Pairing

variable {a' b' : Type*} [Fintype a'] [Fintype b']

/-- The rectangular matrix `[(Φ_α, ∂_k X_i)]`; `T_{x,k}` for the FE basis, `D^{(k,1)}` for `X¹`. -/
noncomputable def matDk (μx : Measure (Rd d)) (Φ : a' → Rd d → ℝ) (X : a → Rd d → ℝ) (k : Fin d) :
    Matrix a' a ℝ := Matrix.of fun α i => ∫ x, Φ α x * pd k (X i) x ∂μx

/-- The rectangular matrix `[(Φ_α, E_k X_i)]`; `M_{x,E_k}` for the FE basis, `D^{(k,2)}` for
`X¹`. -/
noncomputable def matDE (μx : Measure (Rd d)) (E : Rd d → Rd d) (Φ : a' → Rd d → ℝ)
    (X : a → Rd d → ℝ) (k : Fin d) : Matrix a' a ℝ :=
  Matrix.of fun α i => ∫ x, Φ α x * (E x k * X i x) ∂μx

/-- The rectangular matrix `[(Ψ_β, v_k V_j)]`; `M_{v,k}` for the FE basis, `C^{(k,1)}` for `V⁰`. -/
noncomputable def matCk (μv : Measure (Rd d)) (Ψ : b' → Rd d → ℝ) (V : b → Rd d → ℝ) (k : Fin d) :
    Matrix b' b ℝ := Matrix.of fun β j => ∫ v, Ψ β v * (v k * V j v) ∂μv

/-- The rectangular matrix `[(Ψ_β, ∂_{v_k} V_j)]`; `T_{v,k}` for the FE basis, `C^{(k,2)}` for
`V⁰`. -/
noncomputable def matCT (μv : Measure (Rd d)) (Ψ : b' → Rd d → ℝ) (V : b → Rd d → ℝ) (k : Fin d) :
    Matrix b' b ℝ := Matrix.of fun β j => ∫ v, Ψ β v * pd k (V j) v ∂μv

/-- The rectangular matrix `[(Φ_α, X_i)_{L²(Γ^{(ν)})}]`; `M_{x,Γ^{(ν)}}` for the FE basis,
`B^{(ν,x)}` for `X¹`. -/
noncomputable def matBx (σ : Measure (Rd d)) (Γ : κ → Set (Rd d)) (Φ : a' → Rd d → ℝ)
    (X : a → Rd d → ℝ) (ν : κ) : Matrix a' a ℝ :=
  Matrix.of fun α i => ∫ x in Γ ν, Φ α x * X i x ∂σ

/-- The rectangular matrix `[(Ψ_β, n^{(ν)} · v V_j)_{L²(Ω_v^{(ν)})}]`; `M_{v,Ω^{(ν)}}` for the
FE basis, `B^{(ν,v)}` for `V⁰`. -/
noncomputable def matBv (μv : Measure (Rd d)) (N : κ → Rd d) (Ψ : b' → Rd d → ℝ)
    (V : b → Rd d → ℝ) (ν : κ) : Matrix b' b ℝ :=
  Matrix.of fun β j => ∫ v in velHalf (N ν), Ψ β v * (⟪N ν, v⟫ * V j v) ∂μv

/-- The rectangular mass matrix `[(Φ_α, X_i)]`. -/
noncomputable def matM (μ : Measure (Rd d)) (Φ : a' → Rd d → ℝ) (X : a → Rd d → ℝ) :
    Matrix a' a ℝ := Matrix.of fun α i => ∫ x, Φ α x * X i x ∂μ

/-- The inflow matrix `∑_{νμ} g^{(ν,μ,x)} (g^{(ν,μ,v)})ᵀ`: `G_S` of arXiv 2303.01856, Sec. 2.3,
for the bases `X¹`, `V⁰`, and the assembled `G(t)` for the FE basis. -/
noncomputable def matG {μ' : Type*} [Fintype μ'] (μv σ : Measure (Rd d)) (Γ : κ → Set (Rd d))
    (N : κ → Rd d) (gx gv : μ' → Rd d → ℝ) (Φ : a' → Rd d → ℝ) (Ψ : b' → Rd d → ℝ) :
    Matrix a' b' ℝ :=
  Matrix.of fun α β => ∑ ν, ∑ μ, (∫ x in Γ ν, Φ α x * gx μ x ∂σ) *
    ∫ v in velHalf (N ν), Ψ β v * (⟪N ν, v⟫ * gv μ v) ∂μv

/-- Entries of `A S Bᵀ`. -/
lemma mul_mul_transpose_apply (A : Matrix a' a ℝ) (S : Matrix a b ℝ) (B : Matrix b' b ℝ)
    (α : a') (β : b') : (A * S * Bᵀ) α β = ∑ i, ∑ j, S i j * (A α i * B β j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- arXiv 2303.01856, Sec. 3: the matrix of `a` between two tensor bases. -/
theorem formA_matrix [SFinite μx] [SFinite μv] [SFinite σ] {N : κ → Rd d} {E : Rd d → Rd d}
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n x = N ν) (S : Matrix a b ℝ) {X : a → Rd d → ℝ} {V : b → Rd d → ℝ}
    {Φ : a' → Rd d → ℝ} {Ψ : b' → Rd d → ℝ}
    (h : ∀ α β, IsSeparable μx μv σ Γ N E X V (Φ α) (Ψ β)) :
    (Matrix.of fun α β => formA μx μv σ Γ n E (tensor S X V) (fun p => Φ α p.1 * Ψ β p.2)) =
      ∑ k, (matDk μx Φ X k * S * (matCk μv Ψ V k)ᵀ - matDE μx E Φ X k * S * (matCT μv Ψ V k)ᵀ)
        - ∑ ν, matBx σ Γ Φ X ν * S * (matBv μv N Ψ V ν)ᵀ := by
  ext α β
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.sum_apply, mul_mul_transpose_apply]
  exact formA_tensor hΓ hdisj hn S (h α β)

end Pairing

end Vlasov

section Assembly

open MeasureTheory MassSpace

variable {d : ℕ} {κ m n μ' : Type*} [Fintype κ] [Fintype m] [Fintype n] [Fintype μ']

/-- The FE matrices of arXiv 2303.01856, Sec. 3, as integrals of the basis functions `φ`, `ψ`,
for a frozen field `E`.  The CIP matrices are arbitrary input. -/
noncomputable def assemble (μx μv σ : Measure (Rd d)) (Γ : κ → Set (Rd d)) (N : κ → Rd d)
    (E : Rd d → Rd d) (φ : m → Rd d → ℝ) (ψ : n → Rd d → ℝ) (gx gv : ℝ → μ' → Rd d → ℝ)
    (Cx : Matrix m m ℝ) (Cv : Matrix n n ℝ) : FEData (Fin d) κ m n where
  Mx := matM μx φ φ
  Mv := matM μv ψ ψ
  Tx := matDk μx φ φ
  MxE := matDE μx E φ φ
  Mvk := matCk μv ψ ψ
  Tv := matCT μv ψ ψ
  MxΓ := matBx σ Γ φ φ
  MvΩ := matBv μv N ψ ψ
  G t := matG μv σ Γ N (gx t) (gv t) φ ψ
  Cx := Cx
  Cv := Cv

/-- Mass matrices are symmetric. -/
lemma matM_transpose (μ : Measure (Rd d)) (φ : m → Rd d → ℝ) :
    (matM μ φ φ)ᵀ = matM μ φ φ := by
  ext i j
  simp only [matM, Matrix.transpose_apply, Matrix.of_apply]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

variable {μx μv σ : Measure (Rd d)} {Γ : κ → Set (Rd d)} {n' : Rd d → Rd d} {N : κ → Rd d}
  {E : Rd d → Rd d} {φ : m → Rd d → ℝ} {ψ : n → Rd d → ℝ} {gx gv : ℝ → μ' → Rd d → ℝ}
  {Cx : Matrix m m ℝ} {Cv : Matrix n n ℝ}

/-- `tr(Bᵀ Z) = ∑ B_{kl} Z_{kl}`. -/
lemma trace_transpose_mul (B Z : Matrix m n ℝ) :
    Matrix.trace (Bᵀ * Z) = ∑ k, ∑ l, B k l * Z k l := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- arXiv 2303.01856, Sec. 3: the weak form (5), restricted to the tensor FE space and tested
with all `φ_α ⊗ ψ_β`, is the matrix equation `M_x ḟ M_v = R(t, f)` for the coefficient matrix
`f`, with the assembled matrices.  This is the semi-discrete problem behind (20a)–(20c). -/
theorem fe_weak_iff [SFinite μx] [SFinite μv] [SFinite σ] [DecidableEq μ']
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n' x = N ν)
    (hφ : ∀ α i, Integrable (fun x => φ α x * φ i x) μx)
    (hψ : ∀ β j, Integrable (fun v => ψ β v * ψ j v) μv)
    (hsep : ∀ α β, IsSeparable μx μv σ Γ N E φ ψ (φ α) (ψ β))
    (hgx : ∀ t ν α μ, IntegrableOn (fun x => φ α x * gx t μ x) (Γ ν) σ)
    (hgv : ∀ t ν β μ, IntegrableOn (fun v => ψ β v * (⟪N ν, v⟫ * gv t μ v)) (velHalf (N ν)) μv)
    (t : ℝ) (f fd : Matrix m n ℝ) :
    (∀ α β, ∫ p, tensor fd φ ψ p * (φ α p.1 * ψ β p.2) ∂(μx.prod μv) +
        formA μx μv σ Γ n' E (tensor f φ ψ) (fun p => φ α p.1 * ψ β p.2) =
        formL μv σ Γ n' (tensor 1 (gx t) (gv t)) (fun p => φ α p.1 * ψ β p.2)) ↔
      (assemble μx μv σ Γ N E φ ψ gx gv Cx Cv).Mx * fd *
          (assemble μx μv σ Γ N E φ ψ gx gv Cx Cv).Mv =
        (assemble μx μv σ Γ N E φ ψ gx gv Cx Cv).rhs t f := by
  set D := assemble μx μv σ Γ N E φ ψ gx gv Cx Cv with hD
  have hM : ∀ α β, ∫ p, tensor fd φ ψ p * (φ α p.1 * ψ β p.2) ∂(μx.prod μv) =
      (D.Mx * fd * D.Mv) α β := by
    intro α β
    rw [integral_tensor_mul fd (hφ α) (hψ β)]
    have hv : D.Mv = D.Mvᵀ := (matM_transpose μv ψ).symm
    rw [hv, mul_mul_transpose_apply]
    rfl
  have hA := formA_matrix (n := n') (S := f) hΓ hdisj hn hsep
  have hL : ∀ α β, formL μv σ Γ n' (tensor 1 (gx t) (gv t)) (fun p => φ α p.1 * ψ β p.2) =
      -D.G t α β := by
    intro α β
    rw [formL_tensor hΓ hdisj hn 1 (hgx t · α) (hgv t · β)]
    simp only [sum_one_mul]
    rfl
  have hA' : ∀ α β, formA μx μv σ Γ n' E (tensor f φ ψ) (fun p => φ α p.1 * ψ β p.2) =
      -(D.op f) α β := by
    intro α β
    have := congrFun (congrFun hA α) β
    simp only [Matrix.of_apply] at this
    rw [this]
    simp only [FEData.op, Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply, neg_add_rev,
      neg_neg]
    simp only [hD, assemble]
    abel
  constructor
  · intro h
    ext α β
    have := h α β
    rw [hM, hA', hL] at this
    simp only [FEData.rhs, Matrix.sub_apply]
    linarith
  · intro h α β
    rw [hM, hA', hL, h]
    simp only [FEData.rhs, Matrix.sub_apply]
    ring

/-- arXiv 2303.01856, Sec. 3: the `L²(Ω)` inner product of two FE functions is `tr(Aᵀ M_x B
M_v)`, so `MassSpace` is the FE space with the norm of `L²(Ω)`. -/
theorem integral_tensor_tensor [SFinite μx] [SFinite μv]
    (hφ : ∀ α i, Integrable (fun x => φ α x * φ i x) μx)
    (hψ : ∀ β j, Integrable (fun v => ψ β v * ψ j v) μv) (A B : Matrix m n ℝ) :
    ∫ p, tensor A φ ψ p * tensor B φ ψ p ∂(μx.prod μv) =
      Matrix.trace (Aᵀ * matM μx φ φ * B * matM μv ψ ψ) := by
  classical
  have h1 : ∀ k l, Integrable (fun p : Rd d × Rd d => tensor A φ ψ p * (φ k p.1 * ψ l p.2))
      (μx.prod μv) := by
    intro k l
    refine ((tensor_prod A (hφ k) (hψ l)).1).congr (Eventually.of_forall fun p => ?_)
    simp only [tensor, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∀ p, tensor A φ ψ p * tensor B φ ψ p =
      ∑ k, ∑ l, B k l * (tensor A φ ψ p * (φ k p.1 * ψ l p.2)) := by
    intro p
    have hB : tensor B φ ψ p = ∑ k, ∑ l, B k l * (φ k p.1 * ψ l p.2) := rfl
    rw [hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only [h2]
  rw [integral_sum_sum_const_mul (fun k l => B k l)
    (fun k l p => tensor A φ ψ p * (φ k p.1 * ψ l p.2)) fun k l => (h1 k l).const_mul _]
  simp only [integral_tensor_mul A (hφ _) (hψ _)]
  have e : Matrix.trace (Aᵀ * matM μx φ φ * B * matM μv ψ ψ) =
      Matrix.trace (Bᵀ * (matM μx φ φ * A * (matM μv ψ ψ)ᵀ)) := by
    rw [← Matrix.trace_transpose,
      show (Aᵀ * matM μx φ φ * B * matM μv ψ ψ)ᵀ =
        (matM μv ψ ψ)ᵀ * (Bᵀ * (matM μx φ φ)ᵀ * A) by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc],
      Matrix.trace_mul_comm, matM_transpose μx φ]
    simp only [Matrix.mul_assoc]
  rw [e, trace_transpose_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_mul_transpose_apply]
  rfl

/-- arXiv 2303.01856, Sec. 3: for a basis with positive definite mass matrices, the FE weak form
is the ODE `ḟ = F(t, f)` on `MassSpace`. -/
theorem fe_weak_iff_field [SFinite μx] [SFinite μv] [SFinite σ] [DecidableEq μ'] [DecidableEq m]
    [DecidableEq n] [Fact (assemble μx μv σ Γ N E φ ψ gx gv Cx Cv).Mx.PosDef]
    [Fact (assemble μx μv σ Γ N E φ ψ gx gv Cx Cv).Mv.PosDef]
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n' x = N ν)
    (hφ : ∀ α i, Integrable (fun x => φ α x * φ i x) μx)
    (hψ : ∀ β j, Integrable (fun v => ψ β v * ψ j v) μv)
    (hsep : ∀ α β, IsSeparable μx μv σ Γ N E φ ψ (φ α) (ψ β))
    (hgx : ∀ t ν α μ, IntegrableOn (fun x => φ α x * gx t μ x) (Γ ν) σ)
    (hgv : ∀ t ν β μ, IntegrableOn (fun v => ψ β v * (⟪N ν, v⟫ * gv t μ v)) (velHalf (N ν)) μv)
    (t : ℝ) (f fd : Matrix m n ℝ) :
    (∀ α β, ∫ p, tensor fd φ ψ p * (φ α p.1 * ψ β p.2) ∂(μx.prod μv) +
        formA μx μv σ Γ n' E (tensor f φ ψ) (fun p => φ α p.1 * ψ β p.2) =
        formL μv σ Γ n' (tensor 1 (gx t) (gv t)) (fun p => φ α p.1 * ψ β p.2)) ↔
      ofMat _ _ fd = (assemble μx μv σ Γ N E φ ψ gx gv Cx Cv).field t (ofMat _ _ f) := by
  rw [fe_weak_iff hΓ hdisj hn hφ hψ hsep hgx hgv t f fd (Cx := Cx) (Cv := Cv)]
  set D := assemble μx μv σ Γ N E φ ψ gx gv Cx Cv with hD
  rw [D.field_ofMat]
  have hxi : D.Mx⁻¹ * D.Mx = 1 := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Fact.out : D.Mx.PosDef).isUnit)
  have hvi : D.Mv * D.Mv⁻¹ = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Fact.out : D.Mv.PosDef).isUnit)
  constructor
  · intro h
    congr 1
    rw [← h]
    calc fd = (D.Mx⁻¹ * D.Mx) * fd * (D.Mv * D.Mv⁻¹) := by
          rw [hxi, hvi, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro h
    have h' := (ofMat D.Mx D.Mv).injective h
    rw [h']
    calc D.Mx * (D.Mx⁻¹ * D.rhs t f * D.Mv⁻¹) * D.Mv
        = (D.Mx * D.Mx⁻¹) * D.rhs t f * (D.Mv⁻¹ * D.Mv) := by simp only [Matrix.mul_assoc]
      _ = D.rhs t f := by rw [D.mx_mul_inv, D.mv_inv_mul, Matrix.one_mul, Matrix.mul_one]

/-- A partial derivative of a `C`-Lipschitz function is bounded by `C`. -/
lemma norm_pd_le {g : Rd d → ℝ} {C : NNReal} (h : LipschitzWith C g) (k : Fin d) (x : Rd d) :
    ‖pd k g x‖ ≤ C := by
  calc ‖pd k g x‖ ≤ ‖fderiv ℝ g x‖ * ‖(EuclideanSpace.single k 1 : Rd d)‖ :=
        (fderiv ℝ g x).le_opNorm _
    _ ≤ C * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ h
        · simp
    _ = C := mul_one _

/-- Partial derivatives are measurable. -/
lemma measurable_pd (g : Rd d → ℝ) (k : Fin d) : Measurable (pd k g) :=
  measurable_fderiv_apply_const ℝ g _

/-- A coordinate is bounded by the Euclidean norm. -/
lemma norm_coord_le (v : Rd d) (k : Fin d) : ‖v k‖ ≤ ‖v‖ := PiLp.norm_apply_le v k

/-- arXiv 2303.01856, Sec. 3: `IsSeparable` holds for the paper's discretisation.  Linear FE
functions on a bounded polygon are bounded and Lipschitz.  Then they are differentiable a.e. by
Rademacher's theorem, and all coefficient integrals exist, for finite measures, a bounded
electric field and a bounded velocity domain. -/
theorem isSeparable_of_lipschitz {a b : Type*} [Fintype a] [Fintype b] [IsFiniteMeasure μx]
    [IsFiniteMeasure μv] [IsFiniteMeasure σ] (hμx : μx ≪ volume) (hμv : μv ≪ volume) {R CE : ℝ}
    (hR : ∀ᵐ v ∂μv, ‖v‖ ≤ R) (hE : Measurable E) (hEb : ∀ x, ‖E x‖ ≤ CE)
    {X : a → Rd d → ℝ} {V : b → Rd d → ℝ} {Φ Ψ : Rd d → ℝ}
    (hXl : ∀ i, ∃ C, LipschitzWith C (X i)) (hVl : ∀ j, ∃ C, LipschitzWith C (V j))
    (hΦl : ∃ C, LipschitzWith C Φ) (hΨl : ∃ C, LipschitzWith C Ψ)
    (hXb : ∀ i, ∃ C, ∀ x, ‖X i x‖ ≤ C) (hVb : ∀ j, ∃ C, ∀ v, ‖V j v‖ ≤ C)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (hΨb : ∃ C, ∀ v, ‖Ψ v‖ ≤ C) :
    IsSeparable μx μv σ Γ N E X V Φ Ψ := by
  obtain ⟨CΦ', hΦ'⟩ := hΦl
  obtain ⟨CΨ', hΨ'⟩ := hΨl
  obtain ⟨CΦ, hΦ⟩ := hΦb
  obtain ⟨CΨ, hΨ⟩ := hΨb
  have hCΦ : 0 ≤ CΦ := (norm_nonneg _).trans (hΦ 0)
  have hCΨ : 0 ≤ CΨ := (norm_nonneg _).trans (hΨ 0)
  have hCE : 0 ≤ CE := (norm_nonneg _).trans (hEb 0)
  have hΦm : Measurable Φ := hΦ'.continuous.measurable
  have hΨm : Measurable Ψ := hΨ'.continuous.measurable
  have hXm : ∀ i, Measurable (X i) := fun i => by
    obtain ⟨C, hC⟩ := hXl i
    exact hC.continuous.measurable
  have hVm : ∀ j, Measurable (V j) := fun j => by
    obtain ⟨C, hC⟩ := hVl j
    exact hC.continuous.measurable
  have hEk : ∀ k, Measurable fun x => E x k := fun k =>
    (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable.comp hE
  have hcoord : ∀ k : Fin d, Measurable fun v : Rd d => v k := fun k =>
    (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable
  have hinn : ∀ ν, Measurable fun v : Rd d => ⟪N ν, v⟫ := fun ν =>
    (continuous_const.inner continuous_id).measurable
  have hRn : 0 ≤ max R 0 := le_max_right _ _
  have hR' : ∀ᵐ v ∂μv, ‖v‖ ≤ max R 0 := hR.mono fun v hv => hv.trans (le_max_left _ _)
  refine
    { diffX := ?_
      diffV := ?_
      intTx := fun k i => ?_
      intMvk := fun k j => ?_
      intMxE := fun k i => ?_
      intTv := fun k j => ?_
      intΓ := fun ν i => ?_
      intΩ := fun ν j => ?_ }
  · refine hμx.ae_le (ae_all_iff.2 fun i => ?_)
    obtain ⟨C, hC⟩ := hXl i
    exact hC.ae_differentiableAt
  · refine hμv.ae_le (ae_all_iff.2 fun j => ?_)
    obtain ⟨C, hC⟩ := hVl j
    exact hC.ae_differentiableAt
  · obtain ⟨C, hC⟩ := hXl i
    refine Integrable.of_bound (hΦm.mul (measurable_pd _ _)).aestronglyMeasurable (CΦ * C)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (hΦ x) (norm_pd_le hC k x) (norm_nonneg _) hCΦ
  · obtain ⟨C, hC⟩ := hVb j
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    refine Integrable.of_bound (hΨm.mul ((hcoord k).mul (hVm j))).aestronglyMeasurable
      (CΨ * (max R 0 * C)) (hR'.mono fun v hv => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul (hΨ v) (mul_le_mul ((norm_coord_le v k).trans hv) (hC v) (norm_nonneg _) hRn)
      (by positivity) hCΨ
  · obtain ⟨C, hC⟩ := hXb i
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    refine Integrable.of_bound (hΦm.mul ((hEk k).mul (hXm i))).aestronglyMeasurable
      (CΦ * (CE * C)) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul (hΦ x) (mul_le_mul ((norm_coord_le (E x) k).trans (hEb x)) (hC x)
      (norm_nonneg _) hCE) (by positivity) hCΦ
  · obtain ⟨C, hC⟩ := hVl j
    refine Integrable.of_bound (hΨm.mul (measurable_pd _ _)).aestronglyMeasurable (CΨ * C)
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul]
    exact mul_le_mul (hΨ v) (norm_pd_le hC k v) (norm_nonneg _) hCΨ
  · obtain ⟨C, hC⟩ := hXb i
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    refine Integrable.integrableOn (Integrable.of_bound (hΦm.mul (hXm i)).aestronglyMeasurable
      (CΦ * C) (Eventually.of_forall fun x => ?_))
    rw [norm_mul]
    exact mul_le_mul (hΦ x) (hC x) (norm_nonneg _) hCΦ
  · obtain ⟨C, hC⟩ := hVb j
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    refine Integrable.integrableOn (Integrable.of_bound
      (hΨm.mul ((hinn ν).mul (hVm j))).aestronglyMeasurable
      (CΨ * ((‖N ν‖ * max R 0) * C)) (hR'.mono fun v hv => ?_))
    rw [norm_mul, norm_mul]
    have h1 : ‖⟪N ν, v⟫‖ ≤ ‖N ν‖ * max R 0 :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    exact mul_le_mul (hΨ v) (mul_le_mul h1 (hC v) (norm_nonneg _) (by positivity))
      (by positivity) hCΨ

section SStep

variable {r r' : Type*} [Fintype r] [Fintype r'] [DecidableEq r] [DecidableEq r'] [DecidableEq μ']
  {X : r → Rd d → ℝ} {V : r' → Rd d → ℝ} {gx' gv' : μ' → Rd d → ℝ}

/-- `S` is recovered by testing against `L²`-orthonormal bases. -/
lemma integral_tensor_orthonormal [SFinite μx] [SFinite μv]
    (hX : ∀ i j, ∫ x, X i x * X j x ∂μx = if i = j then 1 else 0)
    (hV : ∀ i j, ∫ v, V i v * V j v ∂μv = if i = j then 1 else 0)
    (hXi : ∀ i j, Integrable (fun x => X i x * X j x) μx)
    (hVi : ∀ i j, Integrable (fun v => V i v * V j v) μv) (Sd : Matrix r r' ℝ) (α : r) (β : r') :
    ∫ p, tensor Sd X V p * (X α p.1 * V β p.2) ∂(μx.prod μv) = Sd α β := by
  rw [integral_tensor_mul Sd (hXi α) (hVi β)]
  simp [hX, hV]

/-- arXiv 2303.01856, Eq. (15) (Sec. 2.3).  For `L²`-orthonormal `X`, `V`, the weak form (5) on
`T_{X,V}` with all signs of the right-hand side flipped is `Ṡ = ∑_k (D^{(k,1)} S C^{(k,1)ᵀ} -
D^{(k,2)} S C^{(k,2)ᵀ}) - ∑_ν B^{(ν,x)} S B^{(ν,v)ᵀ} + G_S`. -/
theorem weak_S_restriction [SFinite μx] [SFinite μv] [SFinite σ]
    (hΓ : ∀ ν, MeasurableSet (Γ ν)) (hdisj : Pairwise (Function.onFun Disjoint Γ))
    (hn : ∀ ν, ∀ x ∈ Γ ν, n' x = N ν)
    (hX : ∀ i j, ∫ x, X i x * X j x ∂μx = if i = j then 1 else 0)
    (hV : ∀ i j, ∫ v, V i v * V j v ∂μv = if i = j then 1 else 0)
    (hXi : ∀ i j, Integrable (fun x => X i x * X j x) μx)
    (hVi : ∀ i j, Integrable (fun v => V i v * V j v) μv)
    (hsep : ∀ α β, IsSeparable μx μv σ Γ N E X V (X α) (V β))
    (hgx : ∀ ν α μ, IntegrableOn (fun x => X α x * gx' μ x) (Γ ν) σ)
    (hgv : ∀ ν β μ, IntegrableOn (fun v => V β v * (⟪N ν, v⟫ * gv' μ v)) (velHalf (N ν)) μv)
    (S Sd : Matrix r r' ℝ) :
    (∀ α β, ∫ p, tensor Sd X V p * (X α p.1 * V β p.2) ∂(μx.prod μv) -
        formA μx μv σ Γ n' E (tensor S X V) (fun p => X α p.1 * V β p.2) +
        formL μv σ Γ n' (tensor 1 gx' gv') (fun p => X α p.1 * V β p.2) = 0) ↔
      Sd = ∑ k, (matDk μx X X k * S * (matCk μv V V k)ᵀ -
          matDE μx E X X k * S * (matCT μv V V k)ᵀ) -
        ∑ ν, matBx σ Γ X X ν * S * (matBv μv N V V ν)ᵀ + matG μv σ Γ N gx' gv' X V := by
  have hA := formA_matrix (n := n') (S := S) hΓ hdisj hn hsep
  have hL : ∀ α β, formL μv σ Γ n' (tensor 1 gx' gv') (fun p => X α p.1 * V β p.2) =
      -matG μv σ Γ N gx' gv' X V α β := by
    intro α β
    rw [formL_tensor hΓ hdisj hn 1 (hgx · α) (hgv · β)]
    simp only [sum_one_mul]
    rfl
  have hA' : ∀ α β, formA μx μv σ Γ n' E (tensor S X V) (fun p => X α p.1 * V β p.2) =
      (∑ k, (matDk μx X X k * S * (matCk μv V V k)ᵀ -
          matDE μx E X X k * S * (matCT μv V V k)ᵀ) -
        ∑ ν, matBx σ Γ X X ν * S * (matBv μv N V V ν)ᵀ) α β := fun α β =>
    congrFun (congrFun hA α) β
  constructor
  · intro h
    ext α β
    have := h α β
    rw [integral_tensor_orthonormal hX hV hXi hVi, hA', hL] at this
    rw [Matrix.add_apply]
    linarith
  · intro h α β
    rw [integral_tensor_orthonormal hX hV hXi hVi, hA', hL, h, Matrix.add_apply]
    ring

end SStep

end Assembly

section Examples

open MassSpace
open scoped LeanDLRA.Frobenius

/-- Data of the satisfiability examples: unit mass matrices, no transport, a constant source. -/
noncomputable def exData : FEData (Fin 1) (Fin 1) (Fin 2) (Fin 2) where
  Mx := 1
  Mv := 1
  Tx := 0
  MxE := 0
  Mvk := 0
  Tv := 0
  MxΓ := 0
  MvΩ := 0
  G _ := -Matrix.diagonal ![0, 1]
  Cx := 0
  Cv := 0

instance : Fact exData.Mx.PosDef := ⟨Matrix.PosDef.one⟩
instance : Fact exData.Mv.PosDef := ⟨Matrix.PosDef.one⟩

/-- The vector `e₁`. -/
def exE : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The core `S₀ = (2)`. -/
def exS : Matrix (Fin 1) (Fin 1) ℝ := !![2]

/-- `e₁` is orthonormal. -/
lemma exE_orth : exEᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) * exE = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [exE, Matrix.mul_apply, Fin.sum_univ_two]

/-- `e₁ (2) e₁ᵀ = diag(2, 0)`. -/
lemma ex_EST : exE * exS * exEᵀ = Matrix.diagonal ![2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exE, exS, Matrix.mul_apply]

/-- The source of `exData` vanishes on `e₁`. -/
lemma ex_G_E (t : ℝ) : exData.G t * exE = 0 := by
  ext i j
  have h : exData.G t = -Matrix.diagonal ![0, 1] := rfl
  rw [h, Matrix.neg_mul, Matrix.neg_apply, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [exE]

/-- The source of `exData` is symmetric. -/
lemma ex_G_transpose (t : ℝ) : (exData.G t)ᵀ = exData.G t := by
  have h : exData.G t = -Matrix.diagonal ![0, 1] := rfl
  rw [h, Matrix.transpose_neg, Matrix.diagonal_transpose]

/-- The K-field of `exData`. -/
lemma ex_kRhs {r : Type*} [Fintype r] (V : Matrix (Fin 2) r ℝ) (t : ℝ)
    (K : Matrix (Fin 2) r ℝ) : exData.kRhs V t K = -(exData.G t * V) := by
  simp [FEData.kRhs, exData]

/-- The L-field of `exData`. -/
lemma ex_lRhs {r : Type*} [Fintype r] (X : Matrix (Fin 2) r ℝ) (t : ℝ)
    (L : Matrix (Fin 2) r ℝ) : exData.lRhs X t L = -((exData.G t)ᵀ * X) := by
  simp [FEData.lRhs, exData]

/-- The S-field of `exData`. -/
lemma ex_sRhs {r r' : Type*} [Fintype r] [Fintype r'] (X : Matrix (Fin 2) r ℝ)
    (V : Matrix (Fin 2) r' ℝ) (t : ℝ) (S : Matrix r r' ℝ) :
    exData.sRhs X V t S = Xᵀ * exData.G t * V := by
  simp [FEData.sRhs, exData, ang]

/-- A rest point is a solution. -/
lemma odeSolution_of_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {y₀ : E} {a b : ℝ} (h : ∀ t, f t y₀ = 0) : ODESolution f (fun _ => y₀) a b where
  cont := continuousOn_const
  deriv t _ := by rw [h]; exact hasDerivWithinAt_const _ _ _

/-- Non-vacuity of `IsAlg1Step` (arXiv 2303.01856, Alg. 1). -/
theorem exists_isAlg1Step : ∃ K X₁ Ŝ S Lf V₁ S₁,
    IsAlg1Step exData 0 0 1 exE exS exE K X₁ Ŝ S Lf V₁ S₁ := by
  refine ⟨fun _ => exE * exS, exE, exS, fun _ => exS, fun _ => exE * exSᵀ, exE, exS, ?_⟩
  exact
    { orthX₀ := exE_orth
      orthV₀ := exE_orth
      kSol := odeSolution_of_zero fun t => by
        simp [FEData.kField, ex_kRhs, ex_G_E]
      kStart := rfl
      orthX₁ := exE_orth
      kQR := rfl
      sSol := odeSolution_of_zero fun t => by
        rw [ex_sRhs, Matrix.mul_assoc, ex_G_E, Matrix.mul_zero]
      sStart := rfl
      lSol := odeSolution_of_zero fun t => by
        simp [FEData.lField, ex_lRhs, ex_G_transpose, ex_G_E]
      lStart := rfl
      orthV₁ := exE_orth
      lQR := rfl }

/-- Non-vacuity of `IsAlg2Step` (arXiv 2303.01856, Alg. 2), with an active truncation: the
S-step creates the singular value `1`, and the tolerance `ϑ = 2` discards it, so `r₁ = 1 < N =
2`. -/
theorem exists_isAlg2Step : ∃ K Lf Rx Rx' Rv Rv' Ŝ σ,
    IsAlg2Step exData 0 2 0 1 exE exS exE K Lf (N := 2) 1 1 Rx Rx' Rv Rv' Ŝ 1 1 σ 1 := by
  have hSol := MatrixKSL.odeSolution_affine (exE * exS * exEᵀ)
    (Matrix.diagonal ![0, 1] : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  refine ⟨fun _ => exE * exS, fun _ => exE * exSᵀ, exE, exE * exS, exE, exE * exSᵀ,
    fun t => exE * exS * exEᵀ + (t - 0) • Matrix.diagonal ![0, 1], ![2, 1], ?_⟩
  exact
    { tol_pos := by norm_num
      orthX₀ := exE_orth
      orthV₀ := exE_orth
      kSol := odeSolution_of_zero fun t => by
        simp [FEData.kField, ex_kRhs, ex_G_E]
      kStart := rfl
      orthXa := by simp [exData]
      xAug₀ := Matrix.one_mul _
      xAug₁ := Matrix.one_mul _
      lSol := odeSolution_of_zero fun t => by
        simp [FEData.lField, ex_lRhs, ex_G_transpose, ex_G_E]
      lStart := rfl
      orthVa := by simp [exData]
      vAug₀ := Matrix.one_mul _
      vAug₁ := Matrix.one_mul _
      sSol := hSol.congr_field fun t _ => by
        rw [ex_sRhs]
        simp [exData]
      sStart := by simp
      svd := by
        rw [ex_EST]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      orthQx := by simp
      orthQv := by simp
      σ_anti := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp_all
      σ_nonneg := by
        intro i
        fin_cases i <;> simp
      rank_le := by norm_num
      tail_lt := by
        simp [tailSum, Fin.sum_univ_two]
      tail_min := by
        intro r' hr'
        obtain rfl : r' = 0 := by omega
        simp [tailSum, Fin.sum_univ_two] }

end Examples


end LeanDLRA.Literature.P2303_01856
