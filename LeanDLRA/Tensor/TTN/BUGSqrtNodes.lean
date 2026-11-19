import LeanDLRA.Tensor.TTN.BUG
import LeanDLRA.Tensor.TTN.Defs
import LeanDLRA.Stability.Conservation

/-!
# The TTN BUG error bound with the square root of the number of nodes

The robust error bound of the fixed-rank BUG integrator on tree tensor networks
(`ttn_global_error_le`, `DimTree.BasisFrame.bug_global_error`) multiplies the doubly-normal bound
`ε` by the number of nodes `s` of the tree. This file replaces that factor by `√(s - 1)`:

    ‖Yₙ - A(tₙ)‖ ≤ e^{L T} (δ + 3 T (√(s - 1) ε + 6 s L B h)).

Two orthogonalities are used. At one inner node the capture defects of the commuting new mode
projectors add in squares (`norm_sub_modeProd_apply_le_sqrt`). Along a branch, the defect
`(1 - P₁) A(t₁)` of a child splits with the co-range projector `Q₀` of that child into the part
`(1 - Q₀)`, which is the doubly-normal part of the field (size `h ε`), and the part `Q₀`, which
is the error of the subtree (size `η`); if `P₁` commutes with `Q₀` these are orthogonal, so the
defect is `√((h ε)² + η²)` up to `O(L h (B h + η))` (`kstep_capture_inexact_sqrt`). On tensors
the commutation holds because `P₁` acts on the modes of the subtree and `Q₀` on the other modes
(`DimTree.BasisFrame.isCoRangeCommuting_toTTNFrame`).

## Main results

* `kstep_capture_inexact_sqrt`: the capture lemma with `√((h ε)² + η²) + h (4 L B h + L η)`.
* `ttn_local_error_le_sqrt`: one step has error at most
  `κ ^ height * (√(s - 1) h ε + s (e^{L h} - 1) B h + (s - 1) 4 L B h²)`, `κ = e^{L h} (1 + L h)`.
* `ttn_local_error_le_sqrt_size`: `3 h (√(s - 1) ε + 6 s L B h)` if `2 L h · height ≤ 1`.
* `ttn_global_error_le_sqrt`, `DimTree.BasisFrame.bug_global_error_sqrt`: the global bounds.

## References

* [CerutiLubichWalach2021]
-/

open Set Finset
open scoped RealInnerProductSpace

universe u v

namespace LeanDLRA

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Capture

variable {F : ℝ → E → E} {L B ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {A YK : ℝ → E}

/-- **K-step capture lemma with orthogonal splitting.** As `kstep_capture_inexact`, with the
additional assumptions that the new mode projector `P₁` commutes with the co-range projector
`Q₀` and that `Q₀` fixes the start value. Then the doubly-normal part (size `h ε`) and the error
`ηK` of the computed `K`-value lie in the orthogonal ranges of `1 - Q₀` and `Q₀`, and

    ‖(1 - P₁) A(t₁)‖ ≤ √((h ε)² + ηK²) + h (4 L B h + L ηK). -/
theorem kstep_capture_inexact_sqrt (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀)
    (hPQ : ∀ x, Q₀ (P₁ x) = P₁ (Q₀ x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : Q₀ (A t₀) = A t₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀) {K₁ : E} {ηK : ℝ}
    (hKerr : ‖K₁ - YK t₁‖ ≤ ηK) (hKcap : P₁ K₁ = K₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t K₁))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ √((h * ε) ^ 2 + ηK ^ 2) + h * (4 * L * B * h + L * ηK) := by
  have hle : t₀ ≤ t₁ := by linarith
  have ht₁I : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
  have hη0 : 0 ≤ ηK := (norm_nonneg _).trans hKerr
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε t₁ ht₁I)
  have hBK : IsBoundedField (fun t x => Q₀ (F t x)) B := hB.comp_contraction Q₀ hQ₀.norm_le
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  -- the part in the range of `1 - Q₀`
  set u : ℝ → E := fun t => (1 - P₁) ((1 - Q₀) (A t)) with hu
  have huc : ContinuousOn u (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn ((1 - Q₀).continuous.comp_continuousOn hA.cont)
  have hud : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt u ((1 - P₁) ((1 - Q₀) (F t (A t)))) (Ici t) t :=
    fun t ht => (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t
      ((1 - Q₀).hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht))
  have hub : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (A t)))‖ ≤ L * (2 * B * h + ηK) + ε := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have hd2 : ‖A t - K₁‖ ≤ 2 * B * h + ηK := by
      have e1 := norm_sub_le_two_mul_of_start hB hBK ht₁ hA hK hK₀.symm t htI t₁ ht₁I
      have e2 := norm_sub_le_norm_sub_add_norm_sub (A t) (YK t₁) K₁
      rw [norm_sub_rev (YK t₁)] at e2
      linarith
    have hsplit : (1 - P₁) ((1 - Q₀) (F t (A t))) =
        (1 - P₁) ((1 - Q₀) (F t (A t) - F t K₁)) + (1 - P₁) ((1 - Q₀) (F t K₁)) := by
      rw [← map_add, ← map_add]; congr 2; abel
    have hc : ‖(1 - P₁) ((1 - Q₀) (F t (A t) - F t K₁))‖ ≤ L * (2 * B * h + ηK) :=
      calc _ ≤ ‖(1 - Q₀) (F t (A t) - F t K₁)‖ := hP₁.compl.norm_le _
        _ ≤ ‖F t (A t) - F t K₁‖ := hQ₀.compl.norm_le _
        _ ≤ L * ‖A t - K₁‖ := hF t _ _
        _ ≤ L * (2 * B * h + ηK) := mul_le_mul_of_nonneg_left hd2 hL
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hc (hε t htI))
  have hu₀ : u t₀ = 0 := by simp [hu, hA₀]
  have hq := norm_image_sub_le_of_norm_deriv_right_le_segment huc hud hub t₁ ht₁I
  rw [hu₀, sub_zero, hlen] at hq
  -- the part in the range of `Q₀`
  set w : ℝ → E := fun t => Q₀ (A t) - YK t with hw
  have hwc : ContinuousOn w (Icc t₀ t₁) :=
    (Q₀.continuous.comp_continuousOn hA.cont).sub hK.cont
  have hwd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt w (Q₀ (F t (A t)) - Q₀ (F t (YK t))) (Ici t) t :=
    fun t ht => (Q₀.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)).sub (hK.deriv t ht)
  have hwb : ∀ t ∈ Ico t₀ t₁, ‖Q₀ (F t (A t)) - Q₀ (F t (YK t))‖ ≤ L * (2 * B * h) := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have hd1 : ‖A t - YK t‖ ≤ 2 * B * h :=
      norm_sub_le_two_mul_of_start hB hBK ht₁ hA hK hK₀.symm t htI t htI
    rw [← map_sub]
    calc _ ≤ ‖F t (A t) - F t (YK t)‖ := hQ₀.norm_le _
      _ ≤ L * ‖A t - YK t‖ := hF t _ _
      _ ≤ L * (2 * B * h) := mul_le_mul_of_nonneg_left hd1 hL
  have hw₀ : w t₀ = 0 := by simp [hw, hA₀, hK₀]
  have hp := norm_image_sub_le_of_norm_deriv_right_le_segment hwc hwd hwb t₁ ht₁I
  rw [hw₀, sub_zero, hlen] at hp
  -- the two parts of the defect
  set v : E := (1 - P₁) (A t₁) with hv
  have hQv : Q₀ v = (1 - P₁) (w t₁) + (1 - P₁) (YK t₁ - K₁) := by
    simp only [hv, hw, map_sub, sub_apply, one_apply_eq_self, hPQ, hKcap]
    abel
  have hQv' : v - Q₀ v = u t₁ := by
    simp only [hv, hu, map_sub, sub_apply, one_apply_eq_self, hPQ]
  have hpn : ‖Q₀ v‖ ≤ ηK + L * (2 * B * h) * h := by
    rw [hQv]
    have h1 : ‖(1 - P₁) (w t₁)‖ ≤ L * (2 * B * h) * h := (hP₁.compl.norm_le _).trans hp
    have h2 : ‖(1 - P₁) (YK t₁ - K₁)‖ ≤ ηK := by
      refine (hP₁.compl.norm_le _).trans ?_
      rw [norm_sub_rev]; exact hKerr
    exact (norm_add_le _ _).trans (by linarith)
  have hqn : ‖v - Q₀ v‖ ≤ (L * (2 * B * h + ηK) + ε) * h := by rw [hQv']; exact hq
  have hpyth := hQ₀.norm_sq_add v
  -- arithmetic
  set S := √((h * ε) ^ 2 + ηK ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = (h * ε) ^ 2 + ηK ^ 2 := Real.sq_sqrt (by positivity)
  have hSa : h * ε ≤ S := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ηK])
  have hSη : ηK ≤ S := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (h * ε)])
  set b := L * (2 * B * h) * h with hb
  have hb0 : 0 ≤ b := by positivity
  have hxη : 0 ≤ L * h * ηK := by positivity
  have hR0 : 0 ≤ h * (4 * L * B * h + L * ηK) := by positivity
  have h1 : ‖Q₀ v‖ ^ 2 ≤ (ηK + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpn 2
  have h2 : ‖v - Q₀ v‖ ^ 2 ≤ (h * ε + (b + L * h * ηK)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hqn.trans_eq (by rw [hb]; ring)) 2
  have e1 : 0 ≤ (S - h * ε) * (b + L * h * ηK) := mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ (S - ηK) * b := mul_nonneg (by linarith) hb0
  have e3 : 0 ≤ b * (b + L * h * ηK) := mul_nonneg hb0 (by linarith)
  have hRb : h * (4 * L * B * h + L * ηK) = 2 * b + L * h * ηK := by rw [hb]; ring
  refine (pow_le_pow_iff_left₀ (norm_nonneg v) (by positivity) two_ne_zero).1 ?_
  rw [hRb]
  nlinarith

end Capture

section Arithmetic

/-- Induction step of the square-root bound at one inner node, in real numbers: child errors
`η i ≤ k (√(s i - 1) a + s i g + (s i - 1) c)` and capture defects
`θ i ≤ √(a² + (η i)²) + (c + x η i)` give
`√(∑ θ²) ≤ (1 + x) k (√(∑ s) a + (∑ s) g + (∑ s - m) c) + m c`. -/
theorem sqrt_sum_sq_capture_le {m : ℕ} {a c g x k : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hg : 0 ≤ g)
    (hx : 0 ≤ x) (hk : 1 ≤ k) {s η θ : Fin m → ℝ} (hs : ∀ i, 1 ≤ s i) (hη0 : ∀ i, 0 ≤ η i)
    (hη : ∀ i, η i ≤ k * (√(s i - 1) * a + s i * g + (s i - 1) * c)) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ i, θ i ≤ √(a ^ 2 + η i ^ 2) + (c + x * η i)) :
    √(∑ i, θ i ^ 2) ≤
      (1 + x) * k * (√(∑ i, s i) * a + (∑ i, s i) * g + (∑ i, s i - m) * c) + m * c := by
  have hk0 : 0 ≤ k := by linarith
  have hsum0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => by linarith [hs i]
  set N : Fin m → ℝ := fun i => s i * g + (s i - 1) * c with hN
  have hN0 : ∀ i, 0 ≤ N i := fun i =>
    add_nonneg (mul_nonneg (by linarith [hs i]) hg) (mul_nonneg (by linarith [hs i]) hc)
  set P := (1 + x) * k * a * √(∑ i, s i) with hP
  set β : Fin m → ℝ := fun i => (1 + x) * k * N i + c with hβ
  set Q := ∑ i, β i with hQ
  have hP0 : 0 ≤ P := by positivity
  have hβ0 : ∀ i, 0 ≤ β i := fun i => by
    have := hN0 i
    simp only [hβ]; positivity
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => hβ0 i
  have hβQ : ∀ i, β i ≤ Q := fun i =>
    Finset.single_le_sum (fun j _ => hβ0 j) (Finset.mem_univ i)
  -- the bound of one capture defect
  have hterm : ∀ i, θ i ≤ (1 + x) * k * a * √(s i) + β i := by
    intro i
    have hr0 : 0 ≤ √(s i - 1) := Real.sqrt_nonneg _
    have hr2 : √(s i - 1) ^ 2 = s i - 1 := Real.sq_sqrt (by linarith [hs i])
    have hR2 : √(s i) ^ 2 = s i := Real.sq_sqrt (by linarith [hs i])
    have hrR : √(s i - 1) ≤ √(s i) := Real.sqrt_le_sqrt (by linarith)
    have hη' : η i ≤ k * (√(s i - 1) * a + N i) := by
      refine (hη i).trans_eq ?_
      simp only [hN]; ring
    have hη'' : η i ≤ k * (√(s i) * a + N i) :=
      hη'.trans (mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_right hrR ha]) hk0)
    have hsq : √(a ^ 2 + η i ^ 2) ≤ k * (√(s i) * a + N i) := by
      rw [Real.sqrt_le_iff]
      refine ⟨mul_nonneg hk0 (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) ha) (hN0 i)), ?_⟩
      have h1 : η i ^ 2 ≤ (k * (√(s i - 1) * a + N i)) ^ 2 := pow_le_pow_left₀ (hη0 i) hη' 2
      have h2 : a ^ 2 ≤ k ^ 2 * a ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg a) (one_le_pow₀ hk)
      have h3 : 0 ≤ 2 * k ^ 2 * a * N i * (√(s i) - √(s i - 1)) :=
        mul_nonneg (mul_nonneg (by positivity) (hN0 i)) (sub_nonneg.2 hrR)
      have h4 : (k * (√(s i) * a + N i)) ^ 2 = (k * (√(s i - 1) * a + N i)) ^ 2 +
          k ^ 2 * a ^ 2 * (√(s i) ^ 2 - √(s i - 1) ^ 2) +
          2 * k ^ 2 * a * N i * (√(s i) - √(s i - 1)) := by ring
      rw [h4, hR2, hr2]
      linarith
    have hxη : x * η i ≤ x * (k * (√(s i) * a + N i)) := mul_le_mul_of_nonneg_left hη'' hx
    calc θ i ≤ √(a ^ 2 + η i ^ 2) + (c + x * η i) := hθ i
      _ ≤ k * (√(s i) * a + N i) + (c + x * (k * (√(s i) * a + N i))) := by linarith
      _ = _ := by simp only [hβ]; ring
  have hαP : ∀ i, (1 + x) * k * a * √(s i) ≤ P := fun i =>
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => by linarith [hs j]) (Finset.mem_univ i))) (by positivity)
  have hα2 : ∑ i, ((1 + x) * k * a * √(s i)) ^ 2 = P ^ 2 := by
    have : ∀ i, ((1 + x) * k * a * √(s i)) ^ 2 = ((1 + x) * k * a) ^ 2 * s i := fun i => by
      rw [mul_pow, Real.sq_sqrt (by linarith [hs i])]
    have h5 : ((1 + x) * k * a * √(∑ i, s i)) ^ 2 = ((1 + x) * k * a) ^ 2 * ∑ i, s i := by
      rw [mul_pow, Real.sq_sqrt hsum0]
    rw [hP, h5]
    simp only [this, ← Finset.mul_sum]
  have hsq : ∑ i, θ i ^ 2 ≤ (P + Q) ^ 2 := by
    have h1 : ∀ i, θ i ^ 2 ≤
        ((1 + x) * k * a * √(s i)) ^ 2 + 2 * P * β i + Q * β i := by
      intro i
      have hα0 : 0 ≤ (1 + x) * k * a * √(s i) := by positivity
      have h2 : θ i ^ 2 ≤ ((1 + x) * k * a * √(s i) + β i) ^ 2 :=
        pow_le_pow_left₀ (hθ0 i) (hterm i) 2
      have h3 := mul_le_mul_of_nonneg_right (hαP i) (hβ0 i)
      have h4 := mul_le_mul_of_nonneg_right (hβQ i) (hβ0 i)
      nlinarith
    calc ∑ i, θ i ^ 2
        ≤ ∑ i, (((1 + x) * k * a * √(s i)) ^ 2 + 2 * P * β i + Q * β i) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = (P + Q) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hα2, ← Finset.mul_sum,
            ← Finset.mul_sum]
          ring
  have hfin : P + Q =
      (1 + x) * k * (√(∑ i, s i) * a + (∑ i, s i) * g + (∑ i, s i - m) * c) + m * c := by
    simp only [hQ, hβ, hN, hP, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    ring
  rw [← hfin]
  exact Real.sqrt_le_iff.2 ⟨by positivity, hsq⟩

end Arithmetic

section TTN

variable {G : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- The size of a frame is at least one. -/
theorem TTNFrame.one_le_size (fr : TTNFrame E) : 1 ≤ fr.size := by
  cases fr <;> simp [TTNFrame.size]

/-- **Local error of the TTN BUG step with the square root of the number of nodes.** On a frame
whose mode operators commute with the co-range projectors (`TTNFrame.IsCoRangeCommuting`), with
`s` nodes, one step of the fixed-rank BUG integrator from `Y₀ = A t₀` has error at most

    κ ^ height * (√(s - 1) h ε + s (e^{L h} - 1) B h + (s - 1) 4 L B h²),  κ = e^{L h} (1 + L h).

For `L = 0` this is `√(s - 1) h ε`. -/
theorem ttn_local_error_le_sqrt [CompleteSpace E] (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) {fr : TTNFrame E} (hfr : fr.IsCoRangeCommuting)
    (hG : IsLipschitzField G L) (hB : IsBoundedField G B)
    (hcont : ∀ x, Continuous fun t => G t x) {Y₀ Y₁ : E}
    (hs : IsTTNBUGStep fr G ε t₀ t₁ Y₀ Y₁) (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) * (1 + L * h)) ^ fr.height *
      (√((fr.size : ℝ) - 1) * (h * ε) + fr.size * ((Real.exp (L * h) - 1) * (B * h)) +
        ((fr.size : ℝ) - 1) * (h * (4 * L * B * h))) := by
  have hle : t₀ ≤ t₁ := by linarith
  have hx : 0 ≤ L * h := mul_nonneg hL hh
  have ha : 0 ≤ h * ε := mul_nonneg hh hε
  have hex1 : 1 ≤ Real.exp (L * h) := Real.one_le_exp hx
  have hκ1 : 1 ≤ Real.exp (L * h) * (1 + L * h) :=
    one_le_mul_of_one_le_of_one_le hex1 (by linarith)
  induction fr generalizing G A Y₀ Y₁ with
  | leaf =>
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
    obtain ⟨y, hy, hy0, hy1⟩ := hs
    have := hy.eqOn hA hG hL (hy0.trans hA₀.symm) ⟨hle, le_rfl⟩
    rw [← hy1, this]
    simp only [TTNFrame.height, TTNFrame.size, pow_zero, Nat.cast_one, sub_self,
      Real.sqrt_zero, zero_mul, add_zero, one_mul, zero_add, norm_zero]
    exact mul_nonneg (by linarith) (by positivity)
  | node m P₀ Q₀ 𝓛 cs ih =>
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
    have hc0 : 0 ≤ h * (4 * L * B * h) := by positivity
    have hg0 : 0 ≤ (Real.exp (L * h) - 1) * (B * h) :=
      mul_nonneg (by linarith) (by positivity)
    rw [IsTTNBUGStep] at hs
    obtain ⟨-, hQ₀, -, hQY, P₁, K, YS, hP₁, hP₁L, hc, hsub, hKcap, hεn, hYS, hYS0, hYS1⟩ := hs
    have hex : ∀ i, ∃ y : ℝ → E, ODESolution (fun t x => Q₀ i (G t x)) y t₀ t₁ ∧ y t₀ = Y₀ :=
      fun i => exists_ODESolution_clm hG hB hcont (Q₀ i) hle Y₀
    choose YK hYK hYK0 using hex
    set H := Finset.univ.sup fun i => (cs i).height with hH
    set k := (Real.exp (L * h) * (1 + L * h)) ^ H with hk
    have hk1 : 1 ≤ k := one_le_pow₀ hκ1
    have hs1 : ∀ i, (1 : ℝ) ≤ (cs i).size := fun i => by
      exact_mod_cast (cs i).one_le_size
    have hη : ∀ i, ‖K i - YK i t₁‖ ≤ k * (√(((cs i).size : ℝ) - 1) * (h * ε) +
        (cs i).size * ((Real.exp (L * h) - 1) * (B * h)) +
        (((cs i).size : ℝ) - 1) * (h * (4 * L * B * h))) := fun i =>
      (ih i (hfr i).2 (hG.comp_contraction (Q₀ i) (hQ₀ i).norm_le)
        (hB.comp_contraction (Q₀ i) (hQ₀ i).norm_le)
        (fun x => (Q₀ i).continuous.comp (hcont x)) (hsub i) (hYK i) (hYK0 i)).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hκ1 (Finset.le_sup (f := fun i => (cs i).height) (Finset.mem_univ i)))
          (add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) ha)
            (mul_nonneg (by linarith [hs1 i]) hg0)) (mul_nonneg (by linarith [hs1 i]) hc0)))
    have hθ : ∀ i, ‖A t₁ - P₁ i (A t₁)‖ ≤ √((h * ε) ^ 2 + ‖K i - YK i t₁‖ ^ 2) +
        (h * (4 * L * B * h) + L * h * ‖K i - YK i t₁‖) := fun i => by
      have := kstep_capture_inexact_sqrt hG hL hB (hP₁ i) (hQ₀ i)
        (fun x => (hfr i).1 _ (hP₁L i) x) ht₁ hh hA (by rw [hA₀]; exact hQY i) (hYK i)
        ((hYK0 i).trans hA₀.symm) le_rfl (hKcap i) (hεn i)
      refine (le_of_eq ?_).trans (this.trans_eq (by ring))
      simp
    have hΘ := (norm_sub_modeProd_apply_le_sqrt hP₁ (x := A t₁)
      (δ := fun i => ‖A t₁ - P₁ i (A t₁)‖) fun _ => le_rfl).trans
      (sqrt_sum_sq_capture_le (x := L * h) (s := fun i => ((cs i).size : ℝ))
        (η := fun i => ‖K i - YK i t₁‖) (θ := fun i => ‖A t₁ - P₁ i (A t₁)‖) ha hc0 hg0 hx hk1
        hs1 (fun i => norm_nonneg _) hη (fun i => norm_nonneg _) hθ)
    have hPi := IsOrthProj.modeProd hP₁ hc
    have hgal := galerkin_step_error hPi hG hL hB ht₁ hh hA hYS (by rw [hYS0, hA₀]) hΘ
    rw [hYS1] at hgal
    refine hgal.trans ?_
    simp only [TTNFrame.height, TTNFrame.size]
    push_cast
    rw [← hH, pow_succ, ← hk]
    set S := ∑ i, ((cs i).size : ℝ) with hS
    set W := √S * (h * ε) + S * ((Real.exp (L * h) - 1) * (B * h)) +
      (S - m) * (h * (4 * L * B * h)) with hW
    have hk0 : 0 ≤ k := by linarith
    have hKK : 1 ≤ k * (Real.exp (L * h) * (1 + L * h)) :=
      one_le_mul_of_one_le_of_one_le hk1 hκ1
    have hKe : Real.exp (L * h) ≤ k * (Real.exp (L * h) * (1 + L * h)) := by
      have h1 : Real.exp (L * h) ≤ Real.exp (L * h) * (1 + L * h) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      exact h1.trans (le_mul_of_one_le_left (by positivity) hk1)
    have hmc : 0 ≤ (m : ℝ) * (h * (4 * L * B * h)) := by positivity
    have e1 := mul_le_mul_of_nonneg_right hKK hg0
    have e2 := mul_le_mul_of_nonneg_right hKe hmc
    have e3 : (1 : ℝ) + S - 1 = S := by ring
    rw [e3]
    nlinarith

/-- If `2 L h · height ≤ 1`, one step of the fixed-rank BUG integrator on a frame with `s` nodes
whose mode operators commute with the co-range projectors has error at most
`3 h (√(s - 1) ε + 6 s L B h)`: the doubly-normal bound `ε` is multiplied by `3 √(s - 1)`
instead of the `3 s` of `ttn_local_error_le_size`. -/
theorem ttn_local_error_le_sqrt_size [CompleteSpace E] {fr : TTNFrame E}
    (hfr : fr.IsCoRangeCommuting) (hG : IsLipschitzField G L) (hL : 0 ≤ L)
    (hB : IsBoundedField G B) (hcont : ∀ x, Continuous fun t => G t x) (hε : 0 ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hLh : 2 * L * h * fr.height ≤ 1) {Y₀ Y₁ : E}
    (hs : IsTTNBUGStep fr G ε t₀ t₁ Y₀ Y₁) (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (3 * (√((fr.size : ℝ) - 1) * ε + 6 * fr.size * L * B * h)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
  have hbd := ttn_local_error_le_sqrt ht₁ hh hL hε hfr hG hB hcont hs hA hA₀
  rcases fr with _ | ⟨m, P₀, Q₀, 𝓛, cs⟩
  · refine (ttn_local_error hG hL hB hcont ht₁ hh hs hA hA₀).trans ?_
    simp only [ttnErrBound]
    positivity
  · refine hbd.trans ?_
    set fr := TTNFrame.node m P₀ Q₀ 𝓛 cs with hfr'
    have hH : (1 : ℝ) ≤ (fr.height : ℝ) := by
      simp only [hfr', TTNFrame.height]
      exact_mod_cast Nat.le_add_left 1 _
    have hx : 0 ≤ L * h := mul_nonneg hL hh
    have hx2 : L * h ≤ 1 / 2 := by nlinarith
    have hκ : (Real.exp (L * h) * (1 + L * h)) ^ fr.height ≤ 3 := by
      have h1 : Real.exp (L * h) * (1 + L * h) ≤ Real.exp (2 * (L * h)) := by
        rw [two_mul, Real.exp_add]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (L * h)])
          (Real.exp_pos _).le
      calc _ ≤ Real.exp (2 * (L * h)) ^ fr.height := pow_le_pow_left₀ (by positivity) h1 _
        _ = Real.exp ((fr.height : ℕ) * (2 * (L * h))) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by nlinarith)
        _ ≤ 3 := Real.exp_one_lt_three.le
    have hg : (Real.exp (L * h) - 1) * (B * h) ≤ 2 * (L * h) * (B * h) := by
      have := Real.exp_bound_div_one_sub_of_interval hx (by linarith : L * h < 1)
      have h2 : Real.exp (L * h) - 1 ≤ 2 * (L * h) := by
        have h3 : 1 / (1 - L * h) ≤ 1 + 2 * (L * h) := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
        linarith
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hs1 : (1 : ℝ) ≤ fr.size := by exact_mod_cast fr.one_le_size
    have hc0 : 0 ≤ h * (4 * L * B * h) := by positivity
    have hg0 : 0 ≤ (Real.exp (L * h) - 1) * (B * h) :=
      mul_nonneg (sub_nonneg.2 (Real.one_le_exp hx)) (by positivity)
    have hr0 : 0 ≤ √((fr.size : ℝ) - 1) * (h * ε) := by positivity
    have hW : √((fr.size : ℝ) - 1) * (h * ε) + fr.size * ((Real.exp (L * h) - 1) * (B * h)) +
        ((fr.size : ℝ) - 1) * (h * (4 * L * B * h)) ≤
        h * (√((fr.size : ℝ) - 1) * ε + 6 * fr.size * L * B * h) := by
      have e1 := mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℝ) ≤ fr.size)
      nlinarith
    have hnn : 0 ≤ √((fr.size : ℝ) - 1) * (h * ε) +
        fr.size * ((Real.exp (L * h) - 1) * (B * h)) +
        ((fr.size : ℝ) - 1) * (h * (4 * L * B * h)) :=
      add_nonneg (add_nonneg hr0 (mul_nonneg (by linarith) hg0))
        (mul_nonneg (by linarith) hc0)
    calc _ ≤ 3 * (h * (√((fr.size : ℝ) - 1) * ε + 6 * fr.size * L * B * h)) :=
          mul_le_mul hκ hW hnn (by norm_num)
      _ = _ := by ring

end TTN

section TTNGlobal

variable {F : ℝ → E → E} {L B ε : ℝ}

/-- **Robust error bound of the fixed-rank TTN BUG integrator with the square root of the number
of nodes.** For frames with at most `s` nodes and height at most `ℓ` whose mode operators commute
with the co-range projectors, `2 L h ℓ ≤ 1`, initial error `δ` and `n h ≤ T`,

    ‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + 3 T (√(s - 1) ε + 6 s L B h)).

Compare `ttn_global_error_le`, where `ε` is multiplied by `3 s T`. -/
theorem ttn_global_error_le_sqrt [CompleteSpace E] (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {fr : ℕ → TTNFrame E} {Y : ℕ → E} {s ℓ : ℕ} (hfr : ∀ n < N, (fr n).IsCoRangeCommuting)
    (hsize : ∀ n < N, (fr n).size ≤ s) (hheight : ∀ n < N, (fr n).height ≤ ℓ)
    (hLh : 2 * L * h * ℓ ≤ 1)
    (hstep : ∀ n < N, IsTTNBUGStep (fr n) F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + T * (3 * (√((s : ℝ) - 1) * ε + 6 * s * L * B * h))) := by
  intro n hn hT
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
  have hex : ∀ k : ℕ, ∃ y : ℝ → E, ODESolution F y (t₀ + k * h) (t₀ + (k + 1) * h) ∧
      y (t₀ + k * h) = Y k := fun k =>
    exists_ODESolution hF hB hcont (by nlinarith) (Y k)
  choose Φ hΦ hΦ₀ using hex
  have hg : 0 ≤ 3 * (√((s : ℝ) - 1) * ε + 6 * s * L * B * h) := by positivity
  have hloc : ∀ k < N, ‖Y (k + 1) - Φ k (t₀ + (k + 1) * h)‖ ≤
      h * (3 * (√((s : ℝ) - 1) * ε + 6 * s * L * B * h)) := by
    intro k hk
    have hLh' : 2 * L * h * ((fr k).height : ℝ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hheight k hk)
        (by positivity)) hLh
    have h1 := ttn_local_error_le_sqrt_size (hfr k hk) hF hL hB hcont hε (t₀ := t₀ + k * h)
      (t₁ := t₀ + (k + 1) * h) (h := h) (by ring) hh hLh' (hstep k hk) (hΦ k) (hΦ₀ k)
    refine h1.trans ?_
    have hs : ((fr k).size : ℝ) ≤ s := by exact_mod_cast hsize k hk
    have hsq : √(((fr k).size : ℝ) - 1) ≤ √((s : ℝ) - 1) := Real.sqrt_le_sqrt (by linarith)
    have e1 := mul_le_mul_of_nonneg_right hsq hε
    have e2 : 6 * ((fr k).size : ℝ) * L * B * h ≤ 6 * (s : ℝ) * L * B * h := by
      have : 0 ≤ L * B * h := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_left (by linarith) hh
  have hfan := lady_windermere_of_le hF hL hh hA (fun k hk => hΦ k) (fun k hk => hΦ₀ k) hg hloc
    n hn hT
  exact hfan.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)

end TTNGlobal

/-! ### The bound is attained: a star with `m` leaves -/

namespace SqrtNodesExample

variable {m : ℕ} {n : Fin m → E}

/-- The frame of a star with `m` leaves in which the old projectors, the co-range projectors and
the admissible new projectors of leaf `i` are all the projector `1 - nᵢ nᵢᵀ` that removes one
direction `n i`. -/
noncomputable def starFrame (n : Fin m → E) : TTNFrame E :=
  .node m (fun i => 1 - rankOneProj (n i)) (fun i => 1 - rankOneProj (n i))
    (fun i => {1 - rankOneProj (n i)}) fun _ => .leaf

/-- The star has `m + 1` nodes. -/
theorem starFrame_size (n : Fin m → E) : (starFrame n).size = m + 1 := by
  simp [starFrame, TTNFrame.size, add_comm]

/-- The star frame satisfies the commutation hypothesis of the square-root bound. -/
theorem starFrame_isCoRangeCommuting (n : Fin m → E) : (starFrame n).IsCoRangeCommuting :=
  fun _ => ⟨fun M hM x => by rw [Set.mem_singleton_iff.1 hM], trivial⟩

/-- The component of `ε ∑ⱼ nⱼ` along `nᵢ` is `ε`. -/
theorem inner_smul_sum (hn : Orthonormal ℝ n) (ε : ℝ) (i : Fin m) :
    ⟪n i, ε • ∑ j, n j⟫ = ε := by
  rw [inner_smul_right, inner_sum]
  simp [orthonormal_iff_ite.1 hn]

/-- The projectors that remove orthonormal directions commute. -/
theorem compl_rankOneProj_comm (hn : Orthonormal ℝ n) (i j : Fin m) (x : E) :
    (1 - rankOneProj (n i)) ((1 - rankOneProj (n j)) x) =
      (1 - rankOneProj (n j)) ((1 - rankOneProj (n i)) x) := by
  by_cases hij : i = j
  · subst hij; rfl
  · simp [inner_sub_right, inner_smul_right, hn.2 hij, hn.2 (Ne.symm hij)]
    abel

/-- The product of the projectors removes every direction `n j`. -/
theorem modeProd_compl_rankOneProj_apply (hn : Orthonormal ℝ n) (j : Fin m) :
    modeProd (fun i => 1 - rankOneProj (n i)) (n j) = 0 := by
  have hP : ∀ i, IsOrthProj (1 - rankOneProj (n i)) := fun i =>
    (isOrthProj_rankOneProj (hn.1 i)).compl
  have hc := compl_rankOneProj_comm hn
  have h1 := apply_modeProd_eq_self (fun i x => (hP i).idem x) hc j (n j)
  have h2 : Commute (1 - rankOneProj (n j)) (modeProd fun i => 1 - rankOneProj (n i)) :=
    commute_modeProd fun i => ContinuousLinearMap.ext fun x => hc j i x
  have h3 : (1 - rankOneProj (n j)) (modeProd (fun i => 1 - rankOneProj (n i)) (n j)) =
      modeProd (fun i => 1 - rankOneProj (n i)) ((1 - rankOneProj (n j)) (n j)) :=
    DFunLike.congr_fun h2.eq (n j)
  have h4 : (1 - rankOneProj (n j)) (n j) = 0 := by
    simp [hn.1 j]
  rw [← h1, h3, h4, map_zero]

/-- **A step on the star whose error is `√m h ε`.** For orthonormal directions `n i` orthogonal
to `Y₀` and the constant field `g = ε ∑ᵢ nᵢ`, the step of the fixed-rank BUG integrator on the
star frame with doubly-normal bound `ε` stays at `Y₀`: every `K`-step moves along
`(1 - nᵢ nᵢᵀ) g`, the new projectors `1 - nᵢ nᵢᵀ` capture the `K`-values, the doubly-normal parts
are `ε nᵢ`, and the Galerkin field vanishes. -/
theorem isTTNBUGStep_starFrame (hn : Orthonormal ℝ n) {Y₀ : E} (hY : ∀ i, ⟪n i, Y₀⟫ = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (h : ℝ) :
    IsTTNBUGStep (starFrame n) (fun _ _ => ε • ∑ i, n i) ε 0 h Y₀ Y₀ := by
  have hP : ∀ i, IsOrthProj (1 - rankOneProj (n i)) := fun i =>
    (isOrthProj_rankOneProj (hn.1 i)).compl
  have hPY : ∀ i, (1 - rankOneProj (n i)) Y₀ = Y₀ := fun i => by simp [hY i]
  have hprod : modeProd (fun i => 1 - rankOneProj (n i)) (ε • ∑ i, n i) = 0 := by
    rw [map_smul, map_sum]
    simp [modeProd_compl_rankOneProj_apply hn]
  have hcompl : ∀ i (y : E), (1 - (1 - rankOneProj (n i))) y = ⟪n i, y⟫ • n i := fun i y => by
    simp
  rw [starFrame, IsTTNBUGStep]
  refine ⟨hP, hP, hPY, hPY, fun i => 1 - rankOneProj (n i),
    fun i => Y₀ + h • (1 - rankOneProj (n i)) (ε • ∑ j, n j), fun t => Y₀ + t • (0 : E), hP,
    fun i => Set.mem_singleton _, compl_rankOneProj_comm hn, fun i => ?_, fun i => ?_,
    fun i t _ => ?_, ?_, ?_, ?_⟩
  · exact ⟨fun t => Y₀ + t • (1 - rankOneProj (n i)) (ε • ∑ j, n j),
      Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 h, by simp, rfl⟩
  · rw [map_add, map_smul, hPY, (hP i).idem]
  · rw [hcompl, hcompl, inner_smul_sum hn, inner_smul_right, real_inner_self_eq_norm_sq, hn.1 i]
    simp [norm_smul, hn.1 i, abs_of_nonneg hε]
  · exact Exactness.odeSolution_add_smul_of_const (fun _ _ => hprod) Y₀ 0 h
  · rw [modeProd_apply_eq_self hPY]; simp
  · simp

/-- The exact solution `A(t) = Y₀ + t g` of the star example is at distance `√m h ε` from the
result `Y₀` of the step `isTTNBUGStep_starFrame`. With `s = m + 1` nodes and `L = 0` this is the
bound `√(s - 1) h ε` of `ttn_local_error_le_sqrt`, which is therefore attained on frames. -/
theorem norm_sub_starFrame_exact (hn : Orthonormal ℝ n) (Y₀ : E) {ε h : ℝ} (hε : 0 ≤ ε)
    (hh : 0 ≤ h) : ‖Y₀ - (Y₀ + h • ε • ∑ i, n i)‖ = √(m : ℝ) * (h * ε) := by
  have h2 : ‖∑ i, n i‖ ^ 2 = m := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp [inner_sum, orthonormal_iff_ite.1 hn]
  have h1 : ‖∑ i, n i‖ = √(m : ℝ) := by
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [sub_add_cancel_left, norm_neg, norm_smul, norm_smul, h1, Real.norm_of_nonneg hh,
    Real.norm_of_nonneg hε]
  ring

/-- Non-vacuity of the star example in `ℝ^{m+1}`: `Y₀ = e₀`, `n i = e_{i+1}`. -/
example (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (h : ℝ) :
    IsTTNBUGStep (starFrame fun i : Fin m => EuclideanSpace.basisFun (Fin (m + 1)) ℝ i.succ)
      (fun _ _ => ε • ∑ i : Fin m, EuclideanSpace.basisFun (Fin (m + 1)) ℝ i.succ) ε 0 h
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) :=
  isTTNBUGStep_starFrame
    ((EuclideanSpace.basisFun (Fin (m + 1)) ℝ).orthonormal.comp Fin.succ (Fin.succ_injective _))
    (fun i => (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).orthonormal.2 (Fin.succ_ne_zero i)) hε h

end SqrtNodesExample

/-! ### Concrete tree tensor networks -/

namespace DimTree

variable {κ : Type u} [DecidableEq κ] [Fintype κ] {ι : κ → Type v} [∀ k, Fintype (ι k)]

namespace BasisFrame

/-- The abstract frame of a basis frame satisfies the commutation hypothesis of the square-root
bound: the admissible operators of a child act on the modes of its subtree, the co-range
projector on the other modes. -/
theorem isCoRangeCommuting_toTTNFrame : ∀ {τ : DimTree κ} (f : BasisFrame ι τ),
    f.toTTNFrame.IsCoRangeCommuting
  | _, .leaf _ => trivial
  | _, .node _ _ _ _ fs => fun i => ⟨fun M hM x => by
      obtain ⟨M', rfl⟩ := hM
      exact (Tensor.actOn_comm_of_disjoint _ (fun _ hk hk' => hk' hk) _ _ x).symm,
    isCoRangeCommuting_toTTNFrame (fs i)⟩

/-- **Robust global error of the fixed-rank TTN BUG integrator on concrete tree tensor networks
with the square root of the number of nodes.** In the setting of `bug_global_error` (valid tree
`τ` with `s` nodes and height `ℓ`, `2 L h ℓ ≤ 1`),

    ‖Yₙ - A(tₙ)‖ ≤ e^{L T} (δ + 3 T (√(s - 1) ε + 6 s L B h)). -/
theorem bug_global_error_sqrt {τ : DimTree κ} (hv : τ.IsValid) {F : ℝ → Tensor ι → Tensor ι}
    {L B ε : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) (hLh : 2 * L * h * τ.treeHeight ≤ 1) {N : ℕ}
    {A : ℝ → Tensor ι} (hA : ODESolution F A t₀ (t₀ + N * h)) {f : ℕ → BasisFrame ι τ}
    {Y : ℕ → Tensor ι}
    (hstep : ∀ n < N, (f n).IsBUGStep F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
        (δ + T * (3 * (√((τ.nodeCount : ℝ) - 1) * ε + 6 * τ.nodeCount * L * B * h))) :=
  ttn_global_error_le_sqrt hF hL hB hcont hε hh hA (fr := fun n => (f n).toTTNFrame)
    (fun n _ => isCoRangeCommuting_toTTNFrame (f n))
    (fun n _ => (toTTNFrame_size (f n)).le) (fun n _ => (toTTNFrame_height (f n)).le) hLh
    (fun n hn => (hstep n hn).isTTNBUGStep (f n) hv) hδ

end BasisFrame

namespace BUGExample

open Tensor

/-- Non-vacuity of `BasisFrame.bug_global_error_sqrt` on a tree with three nodes and an error
that is not zero: the step `isBUGStep_frame` (`L = 0`, `B = ‖g‖`, `ε = ‖e₁ ⊗ e₁‖`, `δ = 0`)
against the exact solution `A(t) = e₀ ⊗ e₀ + t g`; the left-hand side at `n = 1` is
`‖e₁ ⊗ e₁‖`. -/
example : ∀ n : ℕ, n ≤ 1 → (n : ℝ) * 1 ≤ 1 →
    ‖(if n = 0 then elem ![1, 0] ![1, 0] else (3 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0] +
        (1 : ℝ) • ((22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0])) -
      (elem ![1, 0] ![1, 0] + (0 + (n : ℝ) * 1) • field)‖ ≤
      Real.exp (0 * 1) * (0 + 1 * (3 *
        (√(((node fun i : Fin 2 => leaf i).nodeCount : ℝ) - 1) * ‖elem ![0, 1] ![0, 1]‖ +
          6 * (node fun i : Fin 2 => leaf i).nodeCount * 0 * ‖field‖ * 1))) :=
  BasisFrame.bug_global_error_sqrt isValid_node (F := fun _ _ => field) (L := 0) (B := ‖field‖)
    (ε := ‖elem ![0, 1] ![0, 1]‖) (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl)
    (fun _ => continuous_const) (norm_nonneg _) (t₀ := 0) (h := 1) zero_le_one (by simp)
    (N := 1) (A := fun t => elem ![1, 0] ![1, 0] + t • field)
    (Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ _ _) (f := fun _ => frame)
    (Y := fun n => if n = 0 then elem ![1, 0] ![1, 0] else (3 / 5 : ℝ) •
      elem ![3 / 5, 4 / 5] ![1, 0] + (1 : ℝ) • ((22 / 5 : ℝ) • elem ![3 / 5, 4 / 5] ![1, 0]))
    (fun n hn => by
      obtain rfl : n = 0 := by omega
      simpa using isBUGStep_frame)
    (δ := 0) (T := 1) (by simp)

end BUGExample

end DimTree

end LeanDLRA
