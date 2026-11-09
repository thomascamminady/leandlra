import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2304.05660: Parallel rank-adaptive BUG integrator

Section 3.2 of Ceruti–Kusch–Lubich, *A parallel rank-adaptive integrator for dynamical low-rank
approximation*: the parallel update `Ŷ₁ = Û Ŝ₁ V̂ᵀ` agrees with the (rank-augmented) BUG update
`Ŷ₁^BUG = Û Ŝ(t₁) V̂ᵀ`, whose S-step is a Galerkin step in the same augmented bases, up to
`O(h (h + ε))`.  Here the augmented BUG step is the Galerkin trajectory `YS' = P̂ Q̂ F(t, YS)`,
`YS t₀ = P̂ Q̂ Y₀`, for orthogonal projectors `P̂ = ÛÛᵀ·`, `Q̂ = ·V̂V̂ᵀ` onto the augmented bases
(`P̂` fixes `P₀` and the K-step end value, `Q̂` fixes `Q₀` and the L-step end value).  The
comparison is proved with explicit constants from the normal-component assumption at `Y₀` only
(`parallelBUG_vs_augmentedBUG`, `parallelBUG_vs_augmentedBUG_le`), blockwise, and it yields that
the
dropped `(1,1)` block `Ũ₁ᵀ (∫F) Ṽ₁` of the augmented BUG update, which the parallel integrator
sets to zero, is itself `O(h (h + ε))`.  The library's parallel local error
(`IsParallelBUGStep.local_error`, which contains the doubly normal block bound) and
`galerkin_step_error` are used.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2304_05660

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The explicit comparison bound `2θ + (e^{L h} - 1)(B h + θ)`, `θ = h (7 L B h + ε)`. -/
noncomputable def cmpBound (L B ε h : ℝ) : ℝ :=
  2 * (h * (7 * L * B * h + ε)) +
    (Real.exp (L * h) - 1) * (B * h + h * (7 * L * B * h + ε))

/-- `cmpBound L B ε h ≤ h (c₁ ε + c₂ h)` for `0 ≤ h ≤ H`, with `c₁ = 2 + L H e^{L H}` and
`c₂ = 14 L B + L B e^{L H} (1 + 7 L H)`. -/
lemma cmpBound_le {L B ε h H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hh : 0 ≤ h)
    (hhH : h ≤ H) :
    cmpBound L B ε h
      ≤ h * ((2 + L * H * Real.exp (L * H)) * ε +
          (14 * L * B + L * B * Real.exp (L * H) * (1 + 7 * L * H)) * h) := by
  unfold cmpBound
  set e := Real.exp (L * H) with he
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have hexp : Real.exp (L * h) ≤ e := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have h1 : Real.exp (L * h) - 1 ≤ L * h * e :=
    (exp_sub_one_le_mul_exp (L * h)).trans (mul_le_mul_of_nonneg_left hexp hLh)
  have hX : 0 ≤ B * h + h * (7 * L * B * h + ε) := by positivity
  have h2 : (Real.exp (L * h) - 1) * (B * h + h * (7 * L * B * h + ε))
      ≤ L * h * e * (B * h + h * (7 * L * B * h + ε)) :=
    mul_le_mul_of_nonneg_right h1 hX
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hHh : 0 ≤ H - h := by linarith
  have hgap : 0 ≤ L * e * h * ε * (H - h) + 7 * L ^ 2 * B * e * h ^ 2 * (H - h) := by positivity
  have hid : h * ((2 + L * H * e) * ε + (14 * L * B + L * B * e * (1 + 7 * L * H)) * h)
      = 2 * (h * (7 * L * B * h + ε)) + L * h * e * (B * h + h * (7 * L * B * h + ε))
        + (L * e * h * ε * (H - h) + 7 * L ^ 2 * B * e * h ^ 2 * (H - h)) := by ring
  rw [hid]
  linarith

/-- **Parallel vs. augmented BUG** (arXiv:2304.05660, Sec. 3.2: blocks agree up to `O(h²)`).
Let `Ŷ₁ = parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)` be the parallel update of a step
(`IsParallelBUGStep`) and let `Ys` be the S-step of the *augmented BUG integrator* in the augmented
bases: `Ys' = Ph Qh F(t, Ys)`, `Ys t₀ = Ph Qh Y₀` (the equation `Ŝ' = Ûᵀ F(t, Û Ŝ V̂ᵀ) V̂`,
`Ŝ(t₀) = Ûᵀ Y₀ V̂`, with `Ŷ₁^BUG = Ys t₁`).  Here `Ph`, `Qh` are commuting orthogonal projectors
(`ÛÛᵀ·`, `·V̂V̂ᵀ`), which commute with `Q₀`, `P₀` respectively, contain the old bases
(`Ph P₀ = P₀`, `Qh Q₀ = Q₀`) and capture the K- and L-step end values (`Ph (YK t₁) = YK t₁`,
`Qh (YL t₁) = YL t₁`, i.e. `Û` spans `[U₀, K(t₁)]`, `V̂` spans `[V₀, L(t₁)]`).  `A` is the exact
solution through `Y₀` (an auxiliary object, which exists for Lipschitz `F`, see
`Foundations/Existence.lean`; the conclusion does not mention it).  If `F` is `L`-Lipschitz, bounded
by `B`, and the normal component of `F(t, Y₀)` is `≤ ε` on `[t₀, t₁)`, then with `h = t₁ - t₀`,

    ‖Ŷ₁ - Ŷ₁^BUG‖ ≤ cmpBound L B ε h = 2θ + (e^{L h} - 1)(B h + θ),   θ = h (7 L B h + ε),

and the same bound holds for each of the four blocks `P₀Q₀`, `(1-P₀)Q₀`, `P₀(1-Q₀)`,
`(1-P₀)(1-Q₀)` of the difference with respect to the old bases.
This is the first display of Sec. 4.1, `‖Ŷ₁ - Ŷ₁^BUG‖ ≤ ĉ₁ h² + ĉ₂ h ε`, which the paper derives
from the heuristic block comparison of Sec. 3.2 with unspecified constants.
Differences from the paper: the constants are explicit; `F` is only Lipschitz and bounded (the paper
assumes bounded derivatives, and remarks that the constants depend only on a bound and a Lipschitz
constant); the normal-component bound is required at `Y₀` for all `t ∈ [t₀, t₁)`, while the
paper's (3.10) is at `t₀` only (the same for autonomous `F`); no bound at the augmented bases is
used. -/
theorem parallelBUG_vs_augmentedBUG {F : ℝ → E → E} {L B ε : ℝ} {P₀ Q₀ Ph Qh : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS Ys A : ℝ → E}
    (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hA0 : A t₀ = Y₀)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) ((1 - Q₀) (F t Y₀))‖ ≤ ε)
    (hPh : IsOrthProj Ph) (hQh : IsOrthProj Qh)
    (hc : ∀ x, Ph (Qh x) = Qh (Ph x)) (hcP₀ : ∀ x, P₀ (Qh x) = Qh (P₀ x))
    (hcQ₀ : ∀ x, Ph (Q₀ x) = Q₀ (Ph x))
    (hP₀Ph : ∀ x, Ph (P₀ x) = P₀ x) (hQ₀Qh : ∀ x, Qh (Q₀ x) = Q₀ x)
    (hKP : Ph (YK t₁) = YK t₁) (hLQ : Qh (YL t₁) = YL t₁)
    (hSs : ODESolution (fun t y => Ph (Qh (F t y))) Ys t₀ t₁) (hS0 : Ys t₀ = Ph (Qh Y₀)) :
    ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - Ys t₁‖ ≤ cmpBound L B ε (t₁ - t₀) ∧
      ‖P₀ (Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - Ys t₁))‖ ≤
        cmpBound L B ε (t₁ - t₀) ∧
      ‖(1 - P₀) (Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - Ys t₁))‖ ≤
        cmpBound L B ε (t₁ - t₀) ∧
      ‖P₀ ((1 - Q₀) (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - Ys t₁))‖ ≤
        cmpBound L B ε (t₁ - t₀) ∧
      ‖(1 - P₀) ((1 - Q₀) (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - Ys t₁))‖ ≤
        cmpBound L B ε (t₁ - t₀) := by
  set Yp := parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) with hYp
  set h := t₁ - t₀ with hh
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  -- range invariance of the substeps
  have hK := hs.solK.map_eq_of_idem hs.orthQ.idem (by rw [hs.initK, hs.fixQ]) t₁ ht₁
  have hL' := hs.solL.map_eq_of_idem hs.orthP.idem (by rw [hs.initL, hs.fixP]) t₁ ht₁
  have hPQ : IsOrthProj (P₀ * Q₀) := hs.orthP.mul hs.orthQ hs.comm
  have hS := ODESolution.map_eq_of_idem (R := P₀ * Q₀) hPQ.idem hs.solS
    (by rw [hs.initS]; change P₀ (Q₀ Y₀) = Y₀; rw [hs.fixQ, hs.fixP]) t₁ ht₁
  change P₀ (Q₀ (YS t₁)) = YS t₁ at hS
  have hSQ : Q₀ (YS t₁) = YS t₁ := by rw [← hS, ← hs.comm, hs.orthQ.idem]
  have hSP : P₀ (YS t₁) = YS t₁ := by rw [← hS, hs.orthP.idem]
  -- the parallel update lies in the range of Ph Qh
  have hR : IsOrthProj (Ph * Qh) := hPh.mul hQh hc
  have hfix : Ph (Qh Yp) = Yp := by
    have e1 : Ph (Qh (YS t₁)) = YS t₁ := by
      rw [← hSQ, hQ₀Qh, hSQ, ← hSP, hP₀Ph]
    have e2 : Ph (Qh ((1 - P₀) (YK t₁))) = (1 - P₀) (YK t₁) := by
      have : Qh ((1 - P₀) (YK t₁)) = (1 - P₀) (YK t₁) := by
        simp only [sub_apply, one_apply_eq_self, map_sub, ← hcP₀]
        rw [← hK, hQ₀Qh]
      rw [this]
      simp only [sub_apply, one_apply_eq_self, map_sub, hP₀Ph, hKP]
    have e3 : Ph (Qh ((1 - Q₀) (YL t₁))) = (1 - Q₀) (YL t₁) := by
      have : Ph ((1 - Q₀) (YL t₁)) = (1 - Q₀) (YL t₁) := by
        have hPy : Ph (YL t₁) = YL t₁ := by have := hP₀Ph (YL t₁); rwa [hL'] at this
        simp only [sub_apply, one_apply_eq_self, map_sub, hcQ₀, hPy]
      rw [show Qh ((1 - Q₀) (YL t₁)) = (1 - Q₀) (YL t₁) from by
        simp only [sub_apply, one_apply_eq_self, map_sub, hQ₀Qh, hLQ], this]
    simp only [hYp, parallelBUG, map_add, e1, e2, e3]
  -- capture of the exact solution
  have hcap : ‖A t₁ - (Ph * Qh) (A t₁)‖ ≤ h * (7 * L * B * h + ε) := by
    have hloc := hs.local_error hF hL hB ht hA hA0 hε
    have hd : A t₁ - (Ph * Qh) (A t₁) = (A t₁ - Yp) - (Ph * Qh) (A t₁ - Yp) := by
      rw [map_sub]
      change _ = _ - (Ph (Qh (A t₁)) - Ph (Qh Yp))
      rw [hfix]; abel
    rw [hd]
    refine (hR.norm_sub_le _).trans ?_
    rw [norm_sub_rev]; exact hloc
  have hGal := galerkin_step_error (R := Ph * Qh) hR hF hL hB (t₀ := t₀) (t₁ := t₁) (h := h)
    (by rw [hh]; ring) (by rw [hh]; linarith) hA hSs
    (by rw [hS0, hA0]; rfl) hcap
  have hloc := hs.local_error hF hL hB ht hA hA0 hε
  have htot : ‖Yp - Ys t₁‖ ≤ cmpBound L B ε h := by
    calc ‖Yp - Ys t₁‖ ≤ ‖Yp - A t₁‖ + ‖Ys t₁ - A t₁‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub Yp (A t₁) (Ys t₁)
          rwa [norm_sub_rev (A t₁)] at this
      _ ≤ h * (7 * L * B * h + ε) +
            ((Real.exp (L * h) - 1) * (B * h + h * (7 * L * B * h + ε)) +
              h * (7 * L * B * h + ε)) := add_le_add hloc hGal
      _ = cmpBound L B ε h := by unfold cmpBound; ring
  have hP := hs.orthP
  have hQ := hs.orthQ
  refine ⟨htot, ?_, ?_, ?_, ?_⟩
  · exact ((hP.norm_le _).trans (hQ.norm_le _)).trans htot
  · exact ((hP.compl.norm_le _).trans (hQ.norm_le _)).trans htot
  · exact ((hP.norm_le _).trans (hQ.compl.norm_le _)).trans htot
  · exact ((hP.compl.norm_le _).trans (hQ.compl.norm_le _)).trans htot

/-- **`O(h (h + ε))` form of the comparison** (arXiv:2304.05660, Sec. 3.2) and the
**dropped block**.
Under the hypotheses of `parallelBUG_vs_augmentedBUG`, for step sizes `h = t₁ - t₀ ≤ H` and
`B, ε ≥ 0`,

    ‖Ŷ₁ - Ŷ₁^BUG‖ ≤ h (c₁ ε + c₂ h),   c₁ = 2 + L H e^{L H},  c₂ = 14 L B + L B e^{L H}(1 + 7 L H),

and the `(1,1)` block of the augmented BUG update that the parallel integrator drops,
`(1 - P₀)(1 - Q₀) Ŷ₁^BUG` (the block `Ũ₁ᵀ (∫F) Ṽ₁` of `Ŝ`, (3.7)), satisfies the same bound, since
the corresponding block of `Ŷ₁` is zero (`IsParallelBUGStep.blocks`).  The paper states `O(h ε)`
for this block in Sec. 3.2 and `h η + O(h²)` in Sec. 3.3; the bound here is `O(h (h + ε))`, of the
latter form. -/
theorem parallelBUG_vs_augmentedBUG_le {F : ℝ → E → E} {L B ε H : ℝ} {P₀ Q₀ Ph Qh : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS Ys A : ℝ → E}
    (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hB0 : 0 ≤ B)
    (hε0 : 0 ≤ ε) (ht : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA0 : A t₀ = Y₀)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) ((1 - Q₀) (F t Y₀))‖ ≤ ε)
    (hPh : IsOrthProj Ph) (hQh : IsOrthProj Qh)
    (hc : ∀ x, Ph (Qh x) = Qh (Ph x)) (hcP₀ : ∀ x, P₀ (Qh x) = Qh (P₀ x))
    (hcQ₀ : ∀ x, Ph (Q₀ x) = Q₀ (Ph x))
    (hP₀Ph : ∀ x, Ph (P₀ x) = P₀ x) (hQ₀Qh : ∀ x, Qh (Q₀ x) = Q₀ x)
    (hKP : Ph (YK t₁) = YK t₁) (hLQ : Qh (YL t₁) = YL t₁)
    (hSs : ODESolution (fun t y => Ph (Qh (F t y))) Ys t₀ t₁) (hS0 : Ys t₀ = Ph (Qh Y₀)) :
    ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - Ys t₁‖ ≤
        (t₁ - t₀) * ((2 + L * H * Real.exp (L * H)) * ε +
          (14 * L * B + L * B * Real.exp (L * H) * (1 + 7 * L * H)) * (t₁ - t₀)) ∧
      ‖normal P₀ Q₀ (Ys t₁)‖ ≤
        (t₁ - t₀) * ((2 + L * H * Real.exp (L * H)) * ε +
          (14 * L * B + L * B * Real.exp (L * H) * (1 + 7 * L * H)) * (t₁ - t₀)) := by
  have hcmp := parallelBUG_vs_augmentedBUG hs hF hL hB ht hA hA0 hε hPh hQh hc hcP₀ hcQ₀ hP₀Ph
    hQ₀Qh hKP hLQ hSs hS0
  have hle := cmpBound_le (H := H) hL hB0 hε0 (sub_nonneg.2 ht) hH
  refine ⟨hcmp.1.trans hle, ?_⟩
  have hn : normal P₀ Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)) = 0 := (hs.blocks ht).2.2.2
  have hd := hcmp.2.2.2.2
  have : (1 - P₀) ((1 - Q₀) (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - Ys t₁)) =
      -(normal P₀ Q₀ (Ys t₁)) := by
    rw [map_sub, map_sub]
    have h2 : (1 - P₀) ((1 - Q₀) (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁))) = 0 := hn
    rw [h2]; simp [normal]
  rw [this, norm_neg] at hd
  exact hd.trans hle

/-- Non-vacuity: the hypotheses of `parallelBUG_vs_augmentedBUG` are satisfiable (rank-one case
on `E = ℝ`, all projectors the identity, `F ≡ 0`, everything stays at `0`). -/
example : ‖parallelBUG (1 : ℝ →L[ℝ] ℝ) 1 0 0 0 - 0‖ ≤ cmpBound 0 0 0 (1 - 0) := by
  have hz : ODESolution (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 1 :=
    ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩
  have hF : ODESolution (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 1 := hz
  have hs : IsParallelBUGStep (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (1 : ℝ →L[ℝ] ℝ) 1 0 1 0
      (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    ⟨IsOrthProj.one, IsOrthProj.one, fun _ => rfl, by simp, by simp,
      by simpa using hz, rfl, by simpa using hz, rfl, by simpa using hz, rfl⟩
  have := (parallelBUG_vs_augmentedBUG (L := 0) (B := 0) (ε := 0) (Ph := 1) (Qh := 1)
    (Ys := fun _ => 0) (A := fun _ => 0) hs (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp)
    zero_le_one hF rfl (fun _ _ => by simp) IsOrthProj.one IsOrthProj.one (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by simp) (by simp)
    (by simpa using hz) (by simp)).1
  simpa using this

end LeanDLRA.Literature.P2304_05660
