import LeanDLRA.Tensor.TTN.Abstract.RankAdaptiveBUG

/-!
# Error bounds of the parallel BUG integrator for tree tensor networks

Projector level, on a real inner product space; the realization on tensors over a dimension tree
is `LeanDLRA/Tensor/TTN/ParallelBUG.lean` (`DimTree.BasisFrame.IsParBUGStep.isParTTNBUGStep`,
`DimTree.BasisFrame.parBUG_global_error`). The parallel BUG integrator on a tree tensor network
is the recursive predicate `IsParTTNBUGStep` over a frame `TTNFrame`: at an inner node the
subtree steps and the core step in the old bases all start from `Y₀`, and the assembled augmented
tensor is truncated with tolerance `ϑ`. `ε` bounds `(1 - (P₀ i + Pa i)) ((1 - Q₀ i) (G t (K i)))`
and the distance of `G t₀ Y₀` from its image under `modeProdLeOne P₀ (1 - P₀)`; `L` and `B` are
the Lipschitz constant and the bound of the field, `Lₜ` is its Lipschitz constant in time.

## Main results

* `parTTN_local_error_le_size`: if `2 L h · height ≤ 1`, the error of one step is at most
  `3 · size · (h (2 ε + (9 L B + Lₜ) h) + ϑ)`.
* `parTTN_global_error_le`: for frames with at most `s` nodes and height at most `ℓ`,
  `2 L h ℓ ≤ 1`, initial error `δ` and `n h ≤ T`,
  `‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + 3 s T (2 ε + (9 L B + Lₜ) h) + 3 s n ϑ)` [CerutiEtAl2024, Thm. 4.5].

## Implementation notes

The statements are over the recursive step predicate of `LeanDLRA/Tensor/Steps.lean`; bases, QR
factorizations and matricizations do not appear, only the orthogonal projectors they define. The
constants are explicit. The field may depend on time and is Lipschitz in time with constant `Lₜ`
(`Lₜ = 0` for an autonomous field); it is assumed Lipschitz and bounded on the whole space.

## References

* [CerutiEtAl2024]
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section ParTTN

variable {G : ℝ → E → E} {L B Lt ε ϑ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

private theorem parTTN_local_aux [CompleteSpace E] {L B Lt ε ϑ h : ℝ}
    (hL : 0 ≤ L) (hB0 : 0 ≤ B) (hLt : 0 ≤ Lt) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h)
    (fr : TTNFrame E) :
    ∀ (G : ℝ → E → E) (t₀ t₁ : ℝ) (Y₀ Y₁ : E) (A : ℝ → E),
      IsLipschitzField G L → IsBoundedField G B → (∀ x, Continuous fun t => G t x) →
      (∀ s t x, s ≤ t → ‖G t x - G s x‖ ≤ Lt * (t - s)) →
      t₁ = t₀ + h → IsParTTNBUGStep fr G ε ϑ t₀ t₁ Y₀ Y₁ → ODESolution G A t₀ t₁ → A t₀ = Y₀ →
      ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) * (1 + L * h)) ^ fr.height *
        (((fr.size : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
          fr.size * ((Real.exp (L * h) - 1) * (B * h) + (ϑ + h * ((3 * L * B + Lt) * h + ε)))) := by
  induction fr with
  | leaf =>
    intro G t₀ t₁ Y₀ Y₁ A hG hB hc hGt ht₁ hs hA hA0
    obtain ⟨y, hy, h0, h1⟩ := hs
    have := hy.norm_sub_le_exp hG hL hA t₁ ⟨by linarith, le_rfl⟩
    rw [h0, ← hA0, sub_self, norm_zero, mul_zero] at this
    have hb0 : 0 ≤ (Real.exp (L * h) - 1) * (B * h) :=
      mul_nonneg (by linarith [Real.add_one_le_exp (L * h), mul_nonneg hL hh])
        (by positivity)
    have hp0 : 0 ≤ h * ((3 * L * B + Lt) * h + ε) := by positivity
    rw [← h1]
    refine this.trans ?_
    simp only [TTNFrame.height, TTNFrame.size, pow_zero, Nat.cast_one, sub_self, zero_mul,
      one_mul, zero_add]
    linarith
  | node m P₀ Q₀ 𝓛 cs ih =>
    intro G t₀ t₁ Y₀ Y₁ A hG hB hc hGt ht₁ hs hA hA0
    have hle : t₀ ≤ t₁ := by linarith
    obtain ⟨hP0o, hQ0o, hP₀, hQ0, Pa, K, YC, hPao, horth, hc00, hc0a, hcaa, hK, hcap, heps, hC,
      hC0, hnorm, hY⟩ := hs
    have hsp : ModeSplit P₀ Pa := ModeSplit.of_proj hP0o hPao horth hc00 hc0a hcaa
    have hPaug : ∀ i, IsOrthProj (P₀ i + Pa i) := fun i => (hP0o i).add_of_orth (hPao i) (horth i)
    have haugfix : ∀ i, (P₀ i + Pa i) Y₀ = Y₀ := fun i => by
      have h : Pa i Y₀ = 0 := by
        rw [← hP₀ i]
        exact congrArg (fun f : E →L[ℝ] E => f Y₀) (hsp.qp i)
      rw [add_apply, hP₀ i, h, add_zero]
    have hkex : ∀ i, ∃ YK : ℝ → E, ODESolution (fun t x => Q₀ i (G t x)) YK t₀ t₁ ∧
        YK t₀ = Y₀ ∧ ‖K i - YK t₁‖ ≤ (Real.exp (L * h) * (1 + L * h)) ^ (cs i).height *
          ((((cs i).size : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
            (cs i).size * ((Real.exp (L * h) - 1) * (B * h) +
              (ϑ + h * ((3 * L * B + Lt) * h + ε)))) := fun i => by
      obtain ⟨YK, hYK, hYK0⟩ := exists_ODESolution_clm hG hB hc (Q₀ i) hle Y₀
      exact ⟨YK, hYK, hYK0, ih i (fun t x => Q₀ i (G t x)) t₀ t₁ Y₀ (K i) YK
        (hG.comp_contraction _ (hQ0o i).norm_le) (hB.comp_contraction _ (hQ0o i).norm_le)
        (fun x => (Q₀ i).continuous.comp (hc x))
        (fun s t x hst => by
          rw [← map_sub]; exact ((hQ0o i).norm_le _).trans (hGt s t x hst))
        ht₁ (hK i) hYK hYK0⟩
    choose YK hYK hYK0 hKerr using hkex
    set η : Fin m → ℝ := fun i => (Real.exp (L * h) * (1 + L * h)) ^ (cs i).height *
          ((((cs i).size : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
            (cs i).size * ((Real.exp (L * h) - 1) * (B * h) +
              (ϑ + h * ((3 * L * B + Lt) * h + ε)))) with hη
    have hcapt : ∀ i, ‖A t₁ - (P₀ i + Pa i) (A t₁)‖ ≤
        h * (4 * L * B * h + L * η i + ε) + η i := fun i => by
      have := kstep_capture_inexact hG hL hB (hPaug i) (hQ0o i) ht₁ hh hA (hYK i)
        ((hYK0 i).trans hA0.symm) (hKerr i) (hcap i) (heps i)
      simpa [sub_apply] using this
    have hΘ : ‖A t₁ - modeProd (fun i => P₀ i + Pa i) (A t₁)‖ ≤
        ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i) :=
      (norm_sub_modeProd_apply_le (fun i y => (hPaug i).norm_le y) _).trans
        (Finset.sum_le_sum fun i _ => hcapt i)
    have hcommaug : ∀ i j x, (P₀ i + Pa i) ((P₀ j + Pa j) x) = (P₀ j + Pa j) ((P₀ i + Pa i) x) :=
      fun i j => fun x => Commute.clm_apply (hsp.commute_add i j) x
    have hproj : IsOrthProj (modeProd (fun i => P₀ i + Pa i)) :=
      IsOrthProj.modeProd hPaug hcommaug
    obtain ⟨YB, hYB, hYB0⟩ := exists_ODESolution_clm hG hB hc
      (modeProd (fun i => P₀ i + Pa i)) hle Y₀
    have hgal := galerkin_step_error hproj hG hL hB ht₁ hh hA hYB
      (by rw [hYB0, hA0, modeProd_apply_eq_self haugfix]) hΘ
    have app : ∀ {a b c : E →L[ℝ] E}, a * b = c → ∀ x, a (b x) = c x := fun h x =>
      congrArg (fun f : E →L[ℝ] E => f x) h
    have hpar := parallel_sub_galerkin_le hG hL hB hLt
      (IsOrthProj.modeProd hP0o hc00) (isOrthProj_modeProdLeOne hP0o hPao hsp)
      hproj (app hsp.modeProd_add_mul_modeProd) (app hsp.modeProd_add_mul_leOne)
      (fun y => (app hsp.modeProd_add_mul_tangent y).trans (app hsp.leOne_mul_tangent y).symm)
      hle hC hC0 hYB hYB0 hnorm (fun t ht => hGt t₀ t Y₀ ht.1)
    have hth : t₁ - t₀ = h := by rw [ht₁]; ring
    rw [hth] at hpar hY
    have hpar' : ‖parTuckerBUG P₀ Pa (YC t₁) h (G t₀ Y₀) - YB t₁‖ ≤
        h * ((3 * L * B + Lt) * h + ε) := hpar
    have harith := augTTN_arith (m := m) hL hB0 hε (add_nonneg hϑ (by positivity)) hh
      (sz := fun i => (cs i).size)
      (ht := fun i => (cs i).height) (H := Finset.univ.sup fun i => (cs i).height)
      (fun i => by cases cs i <;> simp [TTNFrame.size])
      (fun i => Finset.le_sup (f := fun i => (cs i).height) (Finset.mem_univ i)) (η := η)
      (ϑ := ϑ + h * ((3 * L * B + Lt) * h + ε)) (fun i => rfl)
    have h2 : ‖Y₁ - A t₁‖ ≤ ‖Y₁ - parTuckerBUG P₀ Pa (YC t₁) h (G t₀ Y₀)‖ +
        ‖parTuckerBUG P₀ Pa (YC t₁) h (G t₀ Y₀) - YB t₁‖ + ‖YB t₁ - A t₁‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub Y₁ (parTuckerBUG P₀ Pa (YC t₁) h (G t₀ Y₀)) (A t₁)
      have := norm_sub_le_norm_sub_add_norm_sub (parTuckerBUG P₀ Pa (YC t₁) h (G t₀ Y₀))
        (YB t₁) (A t₁)
      linarith
    simp only [TTNFrame.height, TTNFrame.size]
    linarith

/-- If `2 L h · height ≤ 1`, one step of the parallel BUG integrator on a tree tensor network
with truncation tolerance `ϑ ≥ 0` at every inner node has error at most
`3 · size · (h (2 ε + (9 L B + Lₜ) h) + ϑ)`, for a field that is `L`-Lipschitz, `B`-bounded and
Lipschitz in time with constant `Lₜ`; no singular value enters. This is the local error behind
[CerutiEtAl2024, Thm. 4.5], with explicit constants. -/
theorem parTTN_local_error_le_size [CompleteSpace E] {fr : TTNFrame E}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hcont : ∀ x, Continuous fun t => G t x) (hLt : 0 ≤ Lt)
    (hGt : ∀ s t x, s ≤ t → ‖G t x - G s x‖ ≤ Lt * (t - s)) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hLh : 2 * L * h * fr.height ≤ 1) {Y₀ Y₁ : E}
    (hs : IsParTTNBUGStep fr G ε ϑ t₀ t₁ Y₀ Y₁) (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ 3 * fr.size * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hLh0 : 0 ≤ L * h := mul_nonneg hL hh
  have hu : 0 ≤ h * (2 * ε + (9 * L * B + Lt) * h) + ϑ := by positivity
  have hsz : (1 : ℝ) ≤ fr.size := by
    have : 1 ≤ fr.size := by cases fr <;> simp only [TTNFrame.size] <;> omega
    exact_mod_cast this
  have haux := parTTN_local_aux hL hB0 hLt hε hϑ hh fr G t₀ t₁ Y₀ Y₁ A hG hB hcont hGt ht₁ hs hA
    hA₀
  cases fr with
  | leaf =>
    obtain ⟨y, hy, h0, h1⟩ := hs
    have := hy.norm_sub_le_exp hG hL hA t₁ ⟨by linarith, le_rfl⟩
    rw [h0, ← hA₀, sub_self, norm_zero, mul_zero] at this
    rw [← h1]
    exact this.trans (by simp only [TTNFrame.size, Nat.cast_one]; linarith)
  | node m P₀ Q₀ 𝓛 cs =>
    have hH : (1 : ℝ) ≤ ((TTNFrame.node m P₀ Q₀ 𝓛 cs).height : ℝ) := by
      simp only [TTNFrame.height]; exact_mod_cast Nat.le_add_left _ _
    have hx : L * h ≤ 1 / 2 := by nlinarith
    have hk := exp_mul_one_add_pow_le_three hLh0 (n := (TTNFrame.node m P₀ Q₀ 𝓛 cs).height)
      (by nlinarith)
    have hb : (Real.exp (L * h) - 1) * (B * h) ≤ 2 * (L * h) * (B * h) := by
      have habs := Real.abs_exp_sub_one_le (x := L * h) (abs_le.2 ⟨by linarith, by linarith⟩)
      rw [abs_of_nonneg hLh0] at habs
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans habs) (by positivity)
    set sz : ℝ := ((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ) with hsz'
    have hb0 : 0 ≤ (Real.exp (L * h) - 1) * (B * h) :=
      mul_nonneg (by linarith [Real.add_one_le_exp (L * h)]) (by positivity)
    have ha0 : 0 ≤ h * (4 * L * B * h + ε) := by positivity
    have hp0 : 0 ≤ h * ((3 * L * B + Lt) * h + ε) := by positivity
    have hV0 : 0 ≤ (sz - 1) * (h * (4 * L * B * h + ε)) +
        sz * ((Real.exp (L * h) - 1) * (B * h) + (ϑ + h * ((3 * L * B + Lt) * h + ε))) := by
      have : 0 ≤ sz - 1 := by linarith
      positivity
    have hV : (sz - 1) * (h * (4 * L * B * h + ε)) +
        sz * ((Real.exp (L * h) - 1) * (B * h) + (ϑ + h * ((3 * L * B + Lt) * h + ε))) ≤
        sz * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ) := by
      have e1 : (sz - 1) * (h * (4 * L * B * h + ε)) ≤ sz * (h * (4 * L * B * h + ε)) := by
        nlinarith
      have e2 : (Real.exp (L * h) - 1) * (B * h) + (ϑ + h * ((3 * L * B + Lt) * h + ε)) +
          h * (4 * L * B * h + ε) ≤ h * (2 * ε + (9 * L * B + Lt) * h) + ϑ := by nlinarith
      nlinarith
    calc ‖Y₁ - A t₁‖ ≤ _ := haux
      _ ≤ 3 * (sz * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ)) :=
        (mul_le_mul hk hV hV0 (by norm_num))
      _ = _ := by ring

end ParTTN

section ParTTNGlobal

variable {F : ℝ → E → E} {L B Lt ε ϑ : ℝ}

/-- **Robust error bound of the parallel BUG integrator for tree tensor networks.** For frames
with at most `s` nodes and height at most `ℓ`, `2 L h ℓ ≤ 1`, initial error `δ` and `n h ≤ T`,
`‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + 3 s T (2 ε + (9 L B + Lₜ) h) + 3 s n ϑ)`; no singular value of a
matricization of a connecting tensor enters. [CerutiEtAl2024, Thm. 4.5] states the form
`c₁ h + c₂ ε + c₃ δ + c₄ n ϑ`; here the constants are explicit, the field may depend on time
and is Lipschitz in time with constant `Lₜ` (`Lₜ = 0` for an autonomous field), and `ε` enters
through the step predicate `IsParTTNBUGStep`. -/
theorem parTTN_global_error_le [CompleteSpace E] (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → ‖F t x - F s x‖ ≤ Lt * (t - s)) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {fr : ℕ → TTNFrame E} {Y : ℕ → E} {s ℓ : ℕ} (hsize : ∀ n < N, (fr n).size ≤ s)
    (hheight : ∀ n < N, (fr n).height ≤ ℓ) (hLh : 2 * L * h * ℓ ≤ 1)
    (hstep : ∀ n < N,
      IsParTTNBUGStep (fr n) F ε ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
        (δ + T * (3 * s * (2 * ε + (9 * L * B + Lt) * h)) + 3 * s * (n * ϑ)) := by
  intro n hn hT
  have hex : ∀ n < N, ∃ Φ : ℝ → E, ODESolution F Φ (t₀ + n * h) (t₀ + (n + 1) * h) ∧
      Φ (t₀ + n * h) = Y n := fun n _ => by
    obtain ⟨Φ, hΦ, hΦ0⟩ := exists_ODESolution hF hB hcont (a := t₀ + n * h)
      (b := t₀ + (n + 1) * h) (by nlinarith) (Y n)
    exact ⟨Φ, hΦ, hΦ0⟩
  choose! Φ hΦ hΦ₀ using hex
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hu : 0 ≤ h * (2 * ε + (9 * L * B + Lt) * h) + ϑ := by positivity
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      3 * s * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ) := by
    intro n hn
    have h1 : 2 * L * h * ((fr n).height : ℝ) ≤ 1 := by
      have : ((fr n).height : ℝ) ≤ ℓ := by exact_mod_cast hheight n hn
      have h2 : 0 ≤ 2 * L * h := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h2]
    have h3 := parTTN_local_error_le_size hF hL hB hcont hLt hFt hε hϑ (by ring) hh h1
      (hstep n hn) (hΦ n hn) (hΦ₀ n hn)
    have h4 : ((fr n).size : ℝ) ≤ s := by exact_mod_cast hsize n hn
    exact h3.trans (mul_le_mul_of_nonneg_right (by linarith) hu)
  have h1 := lady_windermere_sum hF hL hh hA hΦ hΦ₀
    (ℓ := fun _ => 3 * s * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ)) hloc n hn
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hc0 : 0 ≤ 3 * (s : ℝ) * (2 * ε + (9 * L * B + Lt) * h) := by positivity
  have hin : ‖Y 0 - A t₀‖ + n * (3 * s * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ)) ≤
      δ + T * (3 * s * (2 * ε + (9 * L * B + Lt) * h)) + 3 * s * (n * ϑ) := by
    have := mul_le_mul_of_nonneg_right hT hc0
    nlinarith
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (3 * s * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ)) := by
    have : 0 ≤ (n : ℝ) * (3 * s * (h * (2 * ε + (9 * L * B + Lt) * h) + ϑ)) := by positivity
    have := norm_nonneg (Y 0 - A t₀)
    linarith
  exact h1.trans (mul_le_mul hexp hin hin0 (Real.exp_pos _).le)

end ParTTNGlobal

end LeanDLRA
