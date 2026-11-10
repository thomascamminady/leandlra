import LeanDLRA.Tensor.Steps
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.CommutingProjectorTelescoping

/-!
# Error bounds of the projector-splitting integrator for Tucker tensors and tree tensor networks

Projector level, on a real inner product space; the realization on tensors over a dimension tree
is `LeanDLRA/Tensor/TTN/ProjectorSplitting.lean` (`DimTree.IsProjectorSplittingStep`). One step
of the nested Tucker projector-splitting integrator is the predicate `IsTuckerKSLStep`, one step
of the recursive tree tensor network integrator of shape `τ : TreeShape` is `IsTTNKSLStep`
(`LeanDLRA/Tensor/Steps.lean`). This file proves the local error of a Tucker step with inexact
`K`-values, the local error of a tree tensor network step by induction over the tree, and the
global error bound. The constants depend on the tree, on the Lipschitz constant `L` and the bound
`B` of the field and on a bound of the step size, not on singular values.

## Main results

* `mem_take_ofFn`, `modePrefix_isOrthProj`, `modePrefix_comm`: the prefix products
  `modePrefix P k = P 0 ⋯ P (k - 1)` of commuting orthogonal projectors.
* `tucker_ksl_local_error_inexact`: a Tucker step whose `K`-values are within `ηᵢ` of the exact
  `K`-substep values has local error at most `c (h (h + ε) + ∑ᵢ ηᵢ)`.
* `ttn_ksl_local_error`: one step on a tree tensor network has local error at most
  `c h (h + ε)`.
* `ttn_ksl_global_error`: `‖Yₙ - A tₙ‖ ≤ c₀ δ + c₁ ε + c₂ h` [CerutiLubichWalach2021, Thm. 6.1].

## Implementation notes

The statements are over the step predicates of `LeanDLRA/Tensor/Steps.lean`; bases and
matricizations do not appear, only the orthogonal projectors they define. The constants are
existentially quantified. The field is assumed Lipschitz and bounded on the whole space.

## References

* [CerutiLubichWalach2021]
* [LubichOseledets2014]
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA

section ModePrefix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An operator among the first `k` entries of the list `List.ofFn P` is `P j` for some `j < k`. -/
theorem mem_take_ofFn {d k : ℕ} {P : Fin d → E →L[ℝ] E} {T : E →L[ℝ] E}
    (hT : T ∈ (List.ofFn P).take k) : ∃ j : Fin d, (j : ℕ) < k ∧ T = P j := by
  rw [List.mem_iff_getElem] at hT
  obtain ⟨n, hn, rfl⟩ := hT
  simp only [List.length_take, List.length_ofFn, lt_inf_iff] at hn
  exact ⟨⟨n, hn.2⟩, hn.1, by simp⟩

/-- Non-vacuity of `mem_take_ofFn` with nonzero data: the identity of `ℝ` in the first entry of
the list of two identities. -/
example : ∃ j : Fin 2, (j : ℕ) < 1 ∧ (1 : ℝ →L[ℝ] ℝ) = 1 :=
  mem_take_ofFn (P := fun _ : Fin 2 => (1 : ℝ →L[ℝ] ℝ)) (by simp [List.ofFn_succ])

/-- For commuting orthogonal projectors `P i`, every prefix product
`modePrefix P k = P 0 ⋯ P (k - 1)` is an orthogonal projector. -/
theorem modePrefix_isOrthProj {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) (hc : ∀ i j x, P i (P j x) = P j (P i x)) (k : ℕ) :
    IsOrthProj (modePrefix P k) :=
  IsOrthProj.listProd
    (fun T hT => by
      obtain ⟨i, -, rfl⟩ := mem_take_ofFn hT
      exact hP i)
    (fun S hS T hT x => by
      obtain ⟨i, -, rfl⟩ := mem_take_ofFn hS
      obtain ⟨j, -, rfl⟩ := mem_take_ofFn hT
      exact hc i j x)

/-- Non-vacuity of `modePrefix_isOrthProj` with nonzero data: two identities of `ℝ`. -/
example : IsOrthProj (modePrefix (fun _ : Fin 2 => (1 : ℝ →L[ℝ] ℝ)) 1) :=
  modePrefix_isOrthProj (fun _ => IsOrthProj.one) (fun _ _ _ => rfl) 1

/-- If the operators `P i` commute, every `P j` commutes with every prefix product
`modePrefix P k`. -/
theorem modePrefix_comm {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hc : ∀ i j x, P i (P j x) = P j (P i x)) (k : ℕ) (j : Fin d) (x : E) :
    P j (modePrefix P k x) = modePrefix P k (P j x) :=
  listProd_apply_comm (fun S hS y => by
    obtain ⟨i, -, rfl⟩ := mem_take_ofFn hS
    exact hc j i y) x

/-- Non-vacuity of `modePrefix_comm` with nonzero data: two copies of `2` on `ℝ`. -/
example (x : ℝ) :
    (2 : ℝ →L[ℝ] ℝ) (modePrefix (fun _ : Fin 2 => (2 : ℝ →L[ℝ] ℝ)) 1 x) =
      modePrefix (fun _ : Fin 2 => (2 : ℝ →L[ℝ] ℝ)) 1 ((2 : ℝ →L[ℝ] ℝ) x) :=
  modePrefix_comm (P := fun _ : Fin 2 => (2 : ℝ →L[ℝ] ℝ)) (fun _ _ _ => rfl) 1 0 x

end ModePrefix

section ProjectorSplitting

private theorem sub_modeProd_eq_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (P : Fin d → E →L[ℝ] E) (x : E) :
    x - modeProd P x = ∑ i : Fin d, modePrefix P i (x - P i x) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_succ, modeProd_succ]
    have h := ih (fun i => P i.succ)
    have hs : ∀ j : Fin d, modePrefix P ((j.succ : Fin (d + 1)) : ℕ) (x - P j.succ x)
        = P 0 (modePrefix (fun i => P i.succ) j (x - P j.succ x)) := by
      intro j
      rw [Fin.val_succ, modePrefix_succ]
      rfl
    simp only [hs, Fin.val_zero, modePrefix_zero, one_apply_eq_self]
    rw [← map_sum, ← h]
    simp only [map_sub]
    abel

private theorem fin_sum_telescope {M : Type*} [AddCommGroup M] :
    ∀ (n : ℕ) (f : Fin (n + 1) → M),
      ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0
  | 0, f => by simp
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have := fin_sum_telescope n (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this]
    simp

private theorem tucker_term_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P Q R : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (hR : ∀ y, ‖R y‖ ≤ ‖y‖) (hRP : ∀ y, R (P y) = P (R y)) {w fa fS fK : E}
    {r₁ r₂ r₃ ε : ℝ} (h₁ : ‖w - Q (R fa)‖ ≤ r₁) (h₂ : ‖fa - fS‖ ≤ r₂)
    (h₃ : ‖fa - fK‖ ≤ r₃) (hε : ‖(1 - P) ((1 - Q) (R fK))‖ ≤ ε) :
    ‖w - P (Q (R fS)) - R (fa - P fa)‖ ≤ r₁ + r₂ + r₃ + ε := by
  have heq : w - P (Q (R fS)) - R (fa - P fa)
      = (w - Q (R fa)) + P (Q (R (fa - fS))) - (1 - P) ((1 - Q) (R (fa - fK)))
        - (1 - P) ((1 - Q) (R fK)) := by
    simp only [map_sub, hRP, sub_apply, one_apply_eq_self]
    abel
  have b2 : ‖P (Q (R (fa - fS)))‖ ≤ r₂ :=
    (hP.norm_le _).trans ((hQ.norm_le _).trans ((hR _).trans h₂))
  have b3 : ‖(1 - P) ((1 - Q) (R (fa - fK)))‖ ≤ r₃ :=
    (hP.compl.norm_le _).trans ((hQ.compl.norm_le _).trans ((hR _).trans h₃))
  rw [heq]
  calc _ ≤ ‖(w - Q (R fa)) + P (Q (R (fa - fS))) - (1 - P) ((1 - Q) (R (fa - fK)))‖
        + ‖(1 - P) ((1 - Q) (R fK))‖ := norm_sub_le _ _
    _ ≤ (‖(w - Q (R fa)) + P (Q (R (fa - fS)))‖ + ‖(1 - P) ((1 - Q) (R (fa - fK)))‖)
        + ‖(1 - P) ((1 - Q) (R fK))‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖w - Q (R fa)‖ + ‖P (Q (R (fa - fS)))‖) + ‖(1 - P) ((1 - Q) (R (fa - fK)))‖)
        + ‖(1 - P) ((1 - Q) (R fK))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

private theorem tucker_node {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} {F : ℝ → E → E} {L B ε Λ δ η t₀ t₁ h : ℝ}
    {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E} {X : Fin (d + 1) → E} {K : Fin d → E}
    {YS : Fin d → ℝ → E} {YC : ℝ → E}
    (hs : IsTuckerKSLStep F ε Q₀ P₁ t₀ t₁ Y₀ X K YS YC)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ) (hη : 0 ≤ η) {ZK v : Fin d → ℝ → E}
    (hZc : ∀ i, ContinuousOn (ZK i) (Icc t₀ t₁))
    (hZd : ∀ i, ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (ZK i) (v i t) (Ici t) t)
    (hZ0 : ∀ i, ZK i t₀ = X i.castSucc) (hZ1 : ∀ i, ‖ZK i t₁ - K i‖ ≤ η)
    (hdef : ∀ i, ∀ t ∈ Ico t₀ t₁, ∀ a,
      ‖v i t - kslModeField Q₀ P₁ F i t a‖ ≤ Λ * ‖a - X i.castSucc‖ + δ) :
    ∃ z V : ℝ → E, ContinuousOn z (Icc t₀ t₁) ∧
      (∀ t ∈ Ico t₀ t₁, HasDerivWithinAt z (V t) (Ici t) t) ∧ z t₀ = Y₀ ∧
      ‖z t₁ - YC t₁‖ ≤ d * η ∧
      ∀ t ∈ Ico t₀ t₁, ∀ a, ‖V t - F t a‖ ≤ (L + d * (Λ + 2 * L)) * ‖a - Y₀‖ +
        ((L + d * (Λ + 2 * L)) * ((d + 1) * ((2 * B + δ) * h + η) + B * h) + d * δ + d * ε) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  have hB0 : 0 ≤ B := hB.nonneg
  have hRo : ∀ k, IsOrthProj (modePrefix P₁ k) := modePrefix_isOrthProj hs.projP₁ hs.comm₁
  have hR : ∀ k y, ‖modePrefix P₁ k y‖ ≤ ‖y‖ := fun k y => (hRo k).norm_le y
  have hProd : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hs.projP₁ hs.comm₁
  have hBG : ∀ i, IsBoundedField (kslModeField Q₀ P₁ F i) B := fun i t x => by
    simp only [kslModeField]
    exact ((hs.projQ₀ i).norm_le _).trans ((hR i _).trans (hB t x))
  have hv : ∀ i, ∀ t ∈ Ico t₀ t₁, ‖v i t‖ ≤ B + δ := by
    intro i t ht
    have h1 := hdef i t ht (X i.castSucc)
    simp only [sub_self, norm_zero, mul_zero, zero_add] at h1
    have h2 := norm_sub_norm_le (v i t) (kslModeField Q₀ P₁ F i t (X i.castSucc))
    have h3 := hBG i t (X i.castSucc)
    linarith
  have hZ : ∀ i, ‖ZK i t₁ - X i.castSucc‖ ≤ (B + δ) * h := fun i => by
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (hZc i) (hZd i) (hv i) t₁
      ⟨hle, le_rfl⟩
    rw [hZ0 i, hlen] at this
    exact this
  have hKX : ∀ i, ‖K i - X i.castSucc‖ ≤ (B + δ) * h + η := fun i => by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (K i) (ZK i t₁) (X i.castSucc)
    rw [norm_sub_rev (K i) (ZK i t₁)] at h1
    linarith [hZ1 i, hZ i]
  have hBS : ∀ i : Fin d, IsBoundedField
      (fun t x => -(P₁ i (Q₀ i (modePrefix P₁ (i : ℕ) (F t x))))) B := fun i =>
    isBoundedField_kslS (hB.comp_contraction (modePrefix P₁ i) (hR i)) (hs.projP₁ i)
      (hs.projQ₀ i)
  have hYS : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖YS i t - K i‖ ≤ B * h := fun i t ht => by
    have := (hs.sSol i).norm_sub_le_of_bounded (hBS i) t ht
    rw [hs.sStart i] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0)
  have hYC : ∀ t ∈ Icc t₀ t₁, ‖YC t - X (Fin.last d)‖ ≤ B * h := fun t ht => by
    have := hs.cSol.norm_sub_le_of_bounded
      (hB.comp_contraction (modeProd P₁) hProd.norm_le) t ht
    rw [hs.cStart] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0)
  have hBh : 0 ≤ B * h := mul_nonneg hB0 hh
  have hs0 : 0 ≤ (2 * B + δ) * h + η := by positivity
  have hstep : ∀ i : Fin d, ‖X i.succ - X i.castSucc‖ ≤ (2 * B + δ) * h + η := fun i => by
    have h3 : ‖X i.succ - K i‖ ≤ B * h := by
      rw [hs.next i]; exact hYS i t₁ ⟨hle, le_rfl⟩
    have h4 := norm_sub_le_norm_sub_add_norm_sub (X i.succ) (K i) (X i.castSucc)
    linarith [hKX i]
  have hXd : ∀ i : Fin (d + 1), ‖X i - Y₀‖ ≤ (i : ℕ) * ((2 * B + δ) * h + η) := by
    intro i
    induction i using Fin.induction with
    | zero => simp [hs.start]
    | succ j ih =>
      have h4 := norm_sub_le_norm_sub_add_norm_sub (X j.succ) (X j.castSucc) Y₀
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
      push_cast
      linarith [hstep j]
  have hXD : ∀ i : Fin (d + 1), ‖X i - Y₀‖ ≤ d * ((2 * B + δ) * h + η) := fun i =>
    (hXd i).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp i.2) hs0)
  have hDle : 0 ≤ ((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h := by positivity
  have hX_D : ∀ i : Fin (d + 1), ‖X i - Y₀‖
      ≤ ((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h := fun i => by
    have := hXD i; nlinarith
  have hK_D : ∀ i : Fin d, ‖K i - Y₀‖
      ≤ ((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h := fun i => by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (K i) (X i.castSucc) Y₀
    have := hXD i.castSucc
    have h2 := hKX i
    nlinarith
  have hYS_D : ∀ i : Fin d, ∀ t ∈ Icc t₀ t₁, ‖YS i t - Y₀‖
      ≤ ((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h := fun i t ht => by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (YS i t) (K i) Y₀
    have h2 := hYS i t ht
    have h3 := hXD i.castSucc
    have h4 := hKX i
    have h5 := norm_sub_le_norm_sub_add_norm_sub (K i) (X i.castSucc) Y₀
    nlinarith
  have hYC_D : ∀ t ∈ Icc t₀ t₁, ‖YC t - Y₀‖
      ≤ ((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h := fun t ht => by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (YC t) (X (Fin.last d)) Y₀
    have h2 := hYC t ht
    have h3 := hXD (Fin.last d)
    nlinarith
  refine ⟨fun t => Y₀ + ∑ i, ((YS i t - YS i t₀) + (ZK i t - ZK i t₀)) + (YC t - YC t₀),
    fun t => modeProd P₁ (F t (YC t)) +
      ∑ i : Fin d, (v i t - P₁ i (Q₀ i (modePrefix P₁ (i : ℕ) (F t (YS i t))))),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuousOn_const.add (continuousOn_finsetSum _ fun i _ =>
      ((hs.sSol i).cont.sub continuousOn_const).add ((hZc i).sub continuousOn_const))).add
      (hs.cSol.cont.sub continuousOn_const)
  · intro t ht
    have h1 : HasDerivWithinAt (fun t => ∑ i, ((YS i t - YS i t₀) + (ZK i t - ZK i t₀)))
        (∑ i, (-(P₁ i (Q₀ i (modePrefix P₁ (i : ℕ) (F t (YS i t))))) + v i t)) (Ici t) t :=
      HasDerivWithinAt.fun_sum fun i _ =>
        (((hs.sSol i).deriv t ht).sub_const _).add ((hZd i t ht).sub_const _)
    have h2 := (h1.const_add Y₀).add ((hs.cSol.deriv t ht).sub_const (YC t₀))
    refine h2.congr_deriv ?_
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by abel
  · simp
  · have hz : Y₀ + ∑ i, ((YS i t₁ - YS i t₀) + (ZK i t₁ - ZK i t₀)) + (YC t₁ - YC t₀)
        - YC t₁ = ∑ i, (ZK i t₁ - K i) := by
      have e1 : ∀ i, (YS i t₁ - YS i t₀) + (ZK i t₁ - ZK i t₀)
          = (X i.succ - X i.castSucc) + (ZK i t₁ - K i) := fun i => by
        rw [← hs.next i, hs.sStart i, hZ0 i]; abel
      simp only [e1, Finset.sum_add_distrib, fin_sum_telescope d X, hs.start, hs.cStart]
      abel
    change ‖Y₀ + ∑ i, ((YS i t₁ - YS i t₀) + (ZK i t₁ - ZK i t₀)) + (YC t₁ - YC t₀)
      - YC t₁‖ ≤ _
    rw [hz]
    calc _ ≤ ∑ i, ‖ZK i t₁ - K i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, η := Finset.sum_le_sum fun i _ => hZ1 i
      _ = d * η := by simp
  · intro t ht a
    have htI := Ico_subset_Icc_self ht
    have hx := sub_modeProd_eq_sum P₁ (F t a)
    have hdec : (modeProd P₁ (F t (YC t)) +
        ∑ i : Fin d, (v i t - P₁ i (Q₀ i (modePrefix P₁ (i : ℕ) (F t (YS i t))))))
        - F t a = modeProd P₁ (F t (YC t) - F t a) +
        ∑ i : Fin d, (v i t - P₁ i (Q₀ i (modePrefix P₁ (i : ℕ) (F t (YS i t))))
          - modePrefix P₁ (i : ℕ) (F t a - P₁ i (F t a))) := by
      simp only [Finset.sum_sub_distrib]; rw [← hx, map_sub]; abel
    have hd : ∀ y, ‖y - Y₀‖ ≤ ((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h →
        ‖a - y‖ ≤ ‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h) := fun y hy => by
      have := norm_sub_le_norm_sub_add_norm_sub a Y₀ y
      rw [norm_sub_rev Y₀ y] at this
      linarith
    have hFd : ∀ y, ‖y - Y₀‖ ≤ ((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h →
        ‖F t a - F t y‖ ≤ L * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) :=
      fun y hy => (hF t a y).trans (mul_le_mul_of_nonneg_left (hd y hy) hL)
    have hterm : ∀ i : Fin d, ‖v i t - P₁ i (Q₀ i (modePrefix P₁ (i : ℕ) (F t (YS i t))))
        - modePrefix P₁ (i : ℕ) (F t a - P₁ i (F t a))‖ ≤
        Λ * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) + δ
        + L * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h))
        + L * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) + ε := fun i => by
      have h₁ : ‖v i t - Q₀ i (modePrefix P₁ (i : ℕ) (F t a))‖ ≤
          Λ * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) + δ :=
        (hdef i t ht a).trans (add_le_add_left
          (mul_le_mul_of_nonneg_left (hd _ (hX_D i.castSucc)) hΛ) _)
      exact tucker_term_bound (hs.projP₁ i) (hs.projQ₀ i) (hR i)
        (fun y => (modePrefix_comm hs.comm₁ i i y).symm) h₁
        (hFd _ (hYS_D i t htI)) (hFd _ (hK_D i)) (hs.kNormal i t htI)
    have hcore : ‖modeProd P₁ (F t (YC t) - F t a)‖ ≤
        L * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) := by
      rw [← norm_neg, ← map_neg, neg_sub]
      exact (hProd.norm_le _).trans (hFd _ (hYC_D t htI))
    rw [hdec]
    calc _ ≤ ‖modeProd P₁ (F t (YC t) - F t a)‖ + ‖∑ i : Fin d, (v i t - P₁ i (Q₀ i
          (modePrefix P₁ (i : ℕ) (F t (YS i t)))) - modePrefix P₁ (i : ℕ)
          (F t a - P₁ i (F t a)))‖ := norm_add_le _ _
      _ ≤ L * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) +
          ∑ _i : Fin d, (Λ * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) + δ
            + L * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h))
            + L * (‖a - Y₀‖ + (((d : ℝ) + 1) * ((2 * B + δ) * h + η) + B * h)) + ε) :=
        add_le_add hcore ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i))
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private theorem path_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : ℝ → E → E} {z V A : ℝ → E} {t₀ t₁ h Λ Δ B : ℝ}
    (hzc : ContinuousOn z (Icc t₀ t₁))
    (hzd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt z (V t) (Ici t) t)
    (hA : ODESolution F A t₀ t₁) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hz0 : z t₀ = A t₀) (hΛ : 0 ≤ Λ)
    (hV : ∀ t ∈ Ico t₀ t₁, ‖V t - F t (A t)‖ ≤ Λ * ‖A t - A t₀‖ + Δ) :
    ‖z t₁ - A t₁‖ ≤ (Λ * (B * h) + Δ) * h := by
  have hle : t₀ ≤ t₁ := by linarith
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  have hB0 : 0 ≤ B := hB.nonneg
  have hgc : ContinuousOn (fun t => z t - A t) (Icc t₀ t₁) := hzc.sub hA.cont
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => z t - A t) (V t - F t (A t))
      (Ici t) t := fun t ht => (hzd t ht).sub (hA.deriv t ht)
  have hbd : ∀ t ∈ Ico t₀ t₁, ‖V t - F t (A t)‖ ≤ Λ * (B * h) + Δ := fun t ht => by
    have h1 := hA.norm_sub_le_of_bounded hB t (Ico_subset_Icc_self ht)
    have h2 : B * (t - t₀) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0
    have h3 : Λ * ‖A t - A t₀‖ ≤ Λ * (B * h) := mul_le_mul_of_nonneg_left (h1.trans h2) hΛ
    linarith [hV t ht]
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbd t₁ ⟨hle, le_rfl⟩
  simp only [hz0, sub_self, sub_zero] at this
  rwa [hlen] at this

private theorem poly_bound {p₁ p₂ p₃ p₄ p₅ h H ε η : ℝ} (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hp₃ : 0 ≤ p₃) (hp₄ : 0 ≤ p₄) (hp₅ : 0 ≤ p₅) (hh : 0 ≤ h) (hhH : h ≤ H) (hε : 0 ≤ ε)
    (hη : 0 ≤ η) :
    p₁ * h ^ 2 + p₂ * h ^ 3 + p₃ * (h * η) + p₄ * (h * ε) + p₅ * η
      ≤ (p₁ + p₂ * H + p₃ * H + p₄ + p₅) * (h * (h + ε) + η) := by
  have e1 : h ^ 3 ≤ H * h ^ 2 := by nlinarith [sq_nonneg h]
  have e2 : h * η ≤ H * η := mul_le_mul_of_nonneg_right hhH hη
  have e3 : 0 ≤ h * ε := mul_nonneg hh hε
  have e4 : 0 ≤ h ^ 2 := sq_nonneg h
  have f1 := mul_le_mul_of_nonneg_left e1 hp₂
  have f2 := mul_le_mul_of_nonneg_left e2 hp₃
  have hH : 0 ≤ H := hh.trans hhH
  have g1 : 0 ≤ H * (h * ε) := mul_nonneg hH e3
  have g2 : 0 ≤ H * η := mul_nonneg hH hη
  have g3 : 0 ≤ H * h ^ 2 := mul_nonneg hH e4
  have g4 : 0 ≤ H * η - h * η := by linarith
  have g5 : 0 ≤ H * h ^ 2 - h ^ 3 := by linarith
  nlinarith [mul_nonneg hp₁ e3, mul_nonneg hp₁ hη, mul_nonneg hp₂ g5, mul_nonneg hp₂ g1,
    mul_nonneg hp₂ g2, mul_nonneg hp₃ g3, mul_nonneg hp₃ g1, mul_nonneg hp₃ g4,
    mul_nonneg hp₄ e4, mul_nonneg hp₄ hη, mul_nonneg hp₅ e4, mul_nonneg hp₅ e3]

private theorem ksl_field_props {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} {F : ℝ → E → E} {L B : ℝ} (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    {Q₀ P₁ : Fin d → E →L[ℝ] E} (hP : ∀ i, IsOrthProj (P₁ i))
    (hc : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) (hQ : ∀ i, IsOrthProj (Q₀ i)) (i : Fin d) :
    IsLipschitzField (kslModeField Q₀ P₁ F i) L ∧ IsBoundedField (kslModeField Q₀ P₁ F i) B := by
  have hR : ∀ y, ‖modePrefix P₁ (i : ℕ) y‖ ≤ ‖y‖ := fun y =>
    (modePrefix_isOrthProj hP hc i).norm_le y
  exact ⟨(hF.comp_contraction (modePrefix P₁ i) hR).comp_contraction (Q₀ i) (hQ i).norm_le,
    (hB.comp_contraction (modePrefix P₁ i) hR).comp_contraction (Q₀ i) (hQ i).norm_le⟩

/-- A step of the nested Tucker projector-splitting integrator (`IsTuckerKSLStep`) whose
`K`-values `K i` are within `η i` of the exact `K`-substep values has local error at most
`c (h (h + ε) + ∑ᵢ ηᵢ)`, with a constant `c ≥ 0` that depends only on `d`, `L`, `B` and an upper
bound `H` of the step size, not on singular values. This is one level of the recursion in the
proof of [CerutiLubichWalach2021, Thm. 6.1], where this perturbation argument is not written
out; see also [LubichOseledets2014, §6]. -/
theorem tucker_ksl_local_error_inexact (d : ℕ) {L B H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hH : 0 ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {F : ℝ → E → E} {ε t₀ t₁ h : ℝ} {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E}
      {X : Fin (d + 1) → E} {K : Fin d → E} {YS YK : Fin d → ℝ → E} {YC A : ℝ → E}
      {η : Fin d → ℝ},
      IsLipschitzField F L → IsBoundedField F B → t₁ = t₀ + h → 0 ≤ h → h ≤ H →
      IsTuckerKSLStep F ε Q₀ P₁ t₀ t₁ Y₀ X K YS YC →
      (∀ i, ODESolution (kslModeField Q₀ P₁ F i) (YK i) t₀ t₁) →
      (∀ i, YK i t₀ = X i.castSucc) → (∀ i, ‖K i - YK i t₁‖ ≤ η i) →
      ODESolution F A t₀ t₁ → A t₀ = Y₀ →
      ‖YC t₁ - A t₁‖ ≤ c * (h * (h + ε) + ∑ i, η i) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, le_rfl, ?_⟩
    intro E _ _ F ε t₀ t₁ h Q₀ P₁ Y₀ X K YS YK YC A η hF hBf ht₁ hh hhH hs hK hK0 hKη hA hA0
    have hfield : (fun t x => modeProd P₁ (F t x)) = F := by funext t x; simp
    have hC := hs.cSol
    rw [hfield] at hC
    have hX : X (Fin.last 0) = Y₀ := hs.start
    have := hC.eqOn hA hF hL (by rw [hs.cStart, hX, hA0])
    simp [this (show t₁ ∈ Icc t₀ t₁ from ⟨by linarith, le_rfl⟩)]
  · refine ⟨((L + 3 * d * L) * B + 2 * (L + 3 * d * L) * (d + 1) * B + (L + 3 * d * L) * B
      + d * L * B) + ((L + 3 * d * L) * (d + 1) * L * B) * H + ((L + 3 * d * L) * (d + 1)) * H
      + d + d, by positivity, ?_⟩
    intro E _ _ F ε t₀ t₁ h Q₀ P₁ Y₀ X K YS YK YC A η hF hBf ht₁ hh hhH hs hK hK0 hKη hA hA0
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hs.kNormal ⟨0, hd⟩ t₀ ⟨le_rfl, by linarith⟩)
    have hη0 : ∀ i, 0 ≤ η i := fun i => (norm_nonneg _).trans (hKη i)
    have hηs : 0 ≤ ∑ i, η i := Finset.sum_nonneg fun i _ => hη0 i
    have hLBh : 0 ≤ L * B * h := mul_nonneg (mul_nonneg hL hB) hh
    obtain ⟨z, V, hzc, hzd, hz0, hzend, hV⟩ := tucker_node (Λ := L) (δ := L * B * h)
      (η := ∑ i, η i) (ZK := YK) (v := fun i t => kslModeField Q₀ P₁ F i t (YK i t)) hs hF hL
      hBf ht₁ hh hL hLBh hηs (fun i => (hK i).cont) (fun i t ht => (hK i).deriv t ht) hK0
      (fun i => by
        rw [norm_sub_rev]
        exact (hKη i).trans (Finset.single_le_sum (fun j _ => hη0 j) (Finset.mem_univ i)))
      (fun i t ht a => by
        obtain ⟨hG, hBG⟩ := ksl_field_props hF hBf hs.projP₁ hs.comm₁ hs.projQ₀ i
        have h1 := hG t (YK i t) a
        have h2 := (hK i).norm_sub_le_of_bounded hBG t ⟨ht.1, ht.2.le⟩
        rw [hK0 i] at h2
        have h2' : B * (t - t₀) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB
        have h3 := norm_sub_le_norm_sub_add_norm_sub (YK i t) (X i.castSucc) a
        rw [norm_sub_rev (X i.castSucc) a] at h3
        have h4 : ‖YK i t - a‖ ≤ ‖a - X i.castSucc‖ + B * h := by linarith
        have h5 := mul_le_mul_of_nonneg_left h4 hL
        linarith)
    have hAerr := path_error (F := F) (Λ := L + d * (L + 2 * L)) hzc hzd hA hBf ht₁ hh
      (hz0.trans hA0.symm) (by positivity) (fun t ht => by
        have := hV t ht (A t)
        rwa [hA0])
    have h1 := norm_sub_le_norm_sub_add_norm_sub (YC t₁) (z t₁) (A t₁)
    rw [norm_sub_rev (YC t₁) (z t₁)] at h1
    refine (h1.trans (add_le_add hzend hAerr)).trans ?_
    set ηs : ℝ := ∑ i, η i
    calc _ = ((L + 3 * d * L) * B + 2 * (L + 3 * d * L) * (d + 1) * B + (L + 3 * d * L) * B
          + d * L * B) * h ^ 2 + ((L + 3 * d * L) * (d + 1) * L * B) * h ^ 3
          + ((L + 3 * d * L) * (d + 1)) * (h * ηs) + (d : ℝ) * (h * ε) + (d : ℝ) * ηs := by ring
      _ ≤ _ := poly_bound (by positivity) (by positivity) (by positivity) (by positivity)
          (by positivity) hh hhH hε hηs

private theorem ttn_claim (τ : TreeShape) {L B H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    ∃ Λ C₁ C₂ : ℝ, 0 ≤ Λ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {G : ℝ → E → E}
        {ε t₀ t₁ h : ℝ} {Y₀ Y₁ : E},
        IsLipschitzField G L → IsBoundedField G B → t₁ = t₀ + h → 0 ≤ h → h ≤ H → 0 ≤ ε →
        IsTTNKSLStep τ G ε t₀ t₁ Y₀ Y₁ →
        ∃ z V : ℝ → E, ContinuousOn z (Icc t₀ t₁) ∧
          (∀ t ∈ Ico t₀ t₁, HasDerivWithinAt z (V t) (Ici t) t) ∧ z t₀ = Y₀ ∧ z t₁ = Y₁ ∧
          ∀ t ∈ Ico t₀ t₁, ∀ a, ‖V t - G t a‖ ≤ Λ * ‖a - Y₀‖ + (C₁ * h + C₂ * ε) := by
  induction τ with
  | leaf =>
    refine ⟨L, L * B, 0, hL, mul_nonneg hL hB, le_rfl, ?_⟩
    intro E _ _ G ε t₀ t₁ h Y₀ Y₁ hG hBG ht₁ hh hhH hε hstep
    obtain ⟨y, hy, hy0, hy1⟩ := hstep
    refine ⟨y, fun t => G t (y t), hy.cont, hy.deriv, hy0, hy1, fun t ht a => ?_⟩
    have h1 := hG t (y t) a
    have h2 := hy.norm_sub_le_of_bounded hBG t (Ico_subset_Icc_self ht)
    rw [hy0] at h2
    have h2' : B * (t - t₀) ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB
    have h3 := norm_sub_le_norm_sub_add_norm_sub (y t) Y₀ a
    rw [norm_sub_rev Y₀ a] at h3
    have h4 := mul_le_mul_of_nonneg_left (show ‖y t - a‖ ≤ ‖a - Y₀‖ + B * h by linarith) hL
    nlinarith
  | node m cs ih =>
    choose Λc C₁c C₂c hΛc hC₁c hC₂c hcl using ih
    set Λm : ℝ := ∑ i, Λc i with hΛm
    set C1m : ℝ := ∑ i, C₁c i with hC1m
    set C2m : ℝ := ∑ i, C₂c i with hC2m
    have hΛm0 : 0 ≤ Λm := Finset.sum_nonneg fun i _ => hΛc i
    have hC1m0 : 0 ≤ C1m := Finset.sum_nonneg fun i _ => hC₁c i
    have hC2m0 : 0 ≤ C2m := Finset.sum_nonneg fun i _ => hC₂c i
    have hΛle : ∀ i, Λc i ≤ Λm := fun i =>
      Finset.single_le_sum (fun j _ => hΛc j) (Finset.mem_univ i)
    have hC1le : ∀ i, C₁c i ≤ C1m := fun i =>
      Finset.single_le_sum (fun j _ => hC₁c j) (Finset.mem_univ i)
    have hC2le : ∀ i, C₂c i ≤ C2m := fun i =>
      Finset.single_le_sum (fun j _ => hC₂c j) (Finset.mem_univ i)
    have hΛ₀ : 0 ≤ L + m * (Λm + 2 * L) := by positivity
    refine ⟨L + m * (Λm + 2 * L),
      2 * (L + m * (Λm + 2 * L)) * (m + 1) * B + (L + m * (Λm + 2 * L)) * (m + 1) * C1m * H
        + (L + m * (Λm + 2 * L)) * B + m * C1m,
      (L + m * (Λm + 2 * L)) * (m + 1) * C2m * H + m * C2m + m, hΛ₀, by positivity,
      by positivity, ?_⟩
    intro E _ _ G ε t₀ t₁ h Y₀ Y₁ hG hBG ht₁ hh hhH hε hstep
    obtain ⟨Q₀, P₁, X, K, YS, YC, hs, hch, hend⟩ := hstep
    have hprops := fun i => ksl_field_props hG hBG hs.projP₁ hs.comm₁ hs.projQ₀ i
    choose ZK v hZc hZd hZ0 hZ1 hdefs using fun i => hcl i (hprops i).1 (hprops i).2 ht₁ hh hhH
      hε (hch i)
    have hδ0 : 0 ≤ C1m * h + C2m * ε := by positivity
    obtain ⟨z, V, hzc, hzd, hz0, hzend, hV⟩ := tucker_node (Λ := Λm) (δ := C1m * h + C2m * ε)
      (η := 0) (ZK := ZK) (v := v) hs hG hL hBG ht₁ hh hΛm0 hδ0 le_rfl hZc hZd
      (fun i => by rw [hZ0 i]) (fun i => by rw [hZ1 i]; simp) (fun i t ht a => by
        refine (hdefs i t ht a).trans ?_
        have e1 := mul_le_mul_of_nonneg_right (hΛle i) (norm_nonneg (a - X i.castSucc))
        have e2 := mul_le_mul_of_nonneg_right (hC1le i) hh
        have e3 := mul_le_mul_of_nonneg_right (hC2le i) hε
        linarith)
    have hzY : z t₁ = Y₁ := by
      have h0 : ‖z t₁ - YC t₁‖ ≤ 0 := by simpa using hzend
      rw [← hend]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
    refine ⟨z, V, hzc, hzd, hz0, hzY, fun t ht a => (hV t ht a).trans ?_⟩
    have e1 := mul_le_mul_of_nonneg_left (show h * h ≤ H * h by nlinarith)
      (show 0 ≤ (L + m * (Λm + 2 * L)) * (m + 1) * C1m by positivity)
    have e2 := mul_le_mul_of_nonneg_left (show h * ε ≤ H * ε by nlinarith)
      (show 0 ≤ (L + m * (Λm + 2 * L)) * (m + 1) * C2m by positivity)
    nlinarith

/-- One step of the recursive projector-splitting integrator on a tree tensor network of shape
`τ` (`IsTTNKSLStep`) from `Y₀ = A t₀` has local error at most `c h (h + ε)`, with a constant
`c ≥ 0` that depends only on the tree `τ`, `L`, `B` and an upper bound `H` of the step size: it
grows with the height and the arities of the tree, not with inverse singular values. This is the
local error in the proof of [CerutiLubichWalach2021, Thm. 6.1]; see also
[LubichOseledets2014, §6]. -/
theorem ttn_ksl_local_error (τ : TreeShape) {L B H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hH : 0 ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {F : ℝ → E → E} {ε t₀ t₁ h : ℝ} {Y₀ Y₁ : E} {A : ℝ → E},
      IsLipschitzField F L → IsBoundedField F B → t₁ = t₀ + h → 0 ≤ h → h ≤ H →
      IsTTNKSLStep τ F ε t₀ t₁ Y₀ Y₁ → ODESolution F A t₀ t₁ → A t₀ = Y₀ →
      ‖Y₁ - A t₁‖ ≤ c * (h * (h + ε)) := by
  cases τ with
  | leaf =>
    refine ⟨0, le_rfl, ?_⟩
    intro E _ _ F ε t₀ t₁ h Y₀ Y₁ A hF hBf ht₁ hh hhH hstep hA hA0
    obtain ⟨y, hy, hy0, hy1⟩ := hstep
    have := hy.eqOn hA hF hL (hy0.trans hA0.symm) (show t₁ ∈ Icc t₀ t₁ from ⟨by linarith, le_rfl⟩)
    rw [← hy1, this]
    simp
  | node m cs =>
    by_cases hm : m = 0
    · subst hm
      refine ⟨0, le_rfl, ?_⟩
      intro E _ _ F ε t₀ t₁ h Y₀ Y₁ A hF hBf ht₁ hh hhH hstep hA hA0
      obtain ⟨Q₀, P₁, X, K, YS, YC, hs, hch, hend⟩ := hstep
      have hfield : (fun t x => modeProd P₁ (F t x)) = F := by funext t x; simp
      have hC := hs.cSol
      rw [hfield] at hC
      have hX : X (Fin.last 0) = Y₀ := hs.start
      have := hC.eqOn hA hF hL (by rw [hs.cStart, hX, hA0])
        (show t₁ ∈ Icc t₀ t₁ from ⟨by linarith, le_rfl⟩)
      rw [← hend, this]
      simp
    · obtain ⟨Λ, C₁, C₂, hΛ, hC₁, hC₂, hcl⟩ := ttn_claim (TreeShape.node m cs) hL hB hH
      refine ⟨Λ * B + C₁ + C₂, by positivity, ?_⟩
      intro E _ _ F ε t₀ t₁ h Y₀ Y₁ A hF hBf ht₁ hh hhH hstep hA hA0
      have hε : 0 ≤ ε := by
        obtain ⟨Q₀, P₁, X, K, YS, YC, hs, hch, hend⟩ := hstep
        exact (norm_nonneg _).trans
          (hs.kNormal ⟨0, Nat.pos_of_ne_zero hm⟩ t₀ ⟨le_rfl, by linarith⟩)
      obtain ⟨z, V, hzc, hzd, hz0, hz1, hV⟩ := hcl hF hBf ht₁ hh hhH hε hstep
      have h1 := path_error (F := F) (Λ := Λ) (Δ := C₁ * h + C₂ * ε) hzc hzd hA hBf ht₁ hh
        (hz0.trans hA0.symm) hΛ (fun t ht => by
          have := hV t ht (A t)
          rwa [hA0])
      rw [hz1] at h1
      have e3 : 0 ≤ h * ε := mul_nonneg hh hε
      have e4 : 0 ≤ h * h := mul_nonneg hh hh
      refine h1.trans ?_
      nlinarith [mul_nonneg (mul_nonneg hΛ hB) e3, mul_nonneg hC₁ e3, mul_nonneg hC₂ e4]

/-- **Global error of the projector-splitting integrator for tree tensor networks.** `N` steps
of the recursive projector-splitting integrator of shape `τ` with step size `h` and `N h ≤ T`
satisfy `‖Yₙ - A tₙ‖ ≤ c₀ δ + c₁ ε + c₂ h`, with constants that depend only on `τ`, `L`, `B` and
`T` [CerutiLubichWalach2021, Thm. 6.1]. The field is Lipschitz and bounded on the whole space,
and `ε` enters through the step predicate `IsTTNKSLStep`. -/
theorem ttn_ksl_global_error (τ : TreeShape) {L B T : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hT : 0 ≤ T) :
    ∃ c₀ c₁ c₂ : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      {F : ℝ → E → E} {ε δ t₀ h : ℝ} {N : ℕ} {A : ℝ → E} {Y : ℕ → E} {Φ : ℕ → ℝ → E},
      IsLipschitzField F L → IsBoundedField F B → 0 ≤ ε → 0 ≤ h → (N : ℝ) * h ≤ T →
      ODESolution F A t₀ (t₀ + N * h) →
      (∀ n < N, IsTTNKSLStep τ F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1))) →
      (∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h)) →
      (∀ n < N, Φ n (t₀ + n * h) = Y n) → ‖Y 0 - A t₀‖ ≤ δ →
      ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ c₀ * δ + c₁ * ε + c₂ * h := by
  obtain ⟨c, hc0, hc⟩ := ttn_ksl_local_error τ hL hB hT
  refine ⟨Real.exp (L * T), Real.exp (L * T) * T * c, Real.exp (L * T) * T * c, ?_⟩
  intro E _ _ F ε δ t₀ h N A Y Φ hF hBf hε hh hNh hA hstep hΦ hΦ0 hδ n hn
  have hg : 0 ≤ c * (h + ε) := mul_nonneg hc0 (add_nonneg hh hε)
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * (c * (h + ε)) := by
    intro n hn
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hhT : h ≤ T := by nlinarith
    have := hc hF hBf (show t₀ + (n + 1) * h = t₀ + n * h + h by ring) hh hhT (hstep n hn)
      (hΦ n hn) (hΦ0 n hn)
    linarith
  have hnh : (n : ℝ) * h ≤ T := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    nlinarith
  have h1 := lady_windermere_of_le hF hL hh hA hΦ hΦ0 hg hloc (T := T) n hn hnh
  have hexp := (Real.exp_pos (L * T)).le
  calc _ ≤ _ := h1
    _ ≤ Real.exp (L * T) * (δ + T * (c * (h + ε))) :=
        mul_le_mul_of_nonneg_left (add_le_add hδ le_rfl) hexp
    _ = _ := by ring

end ProjectorSplitting

end LeanDLRA
