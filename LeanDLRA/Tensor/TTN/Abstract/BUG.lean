import LeanDLRA.Tensor.Steps
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.CommutingProjectorTelescoping
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.Existence
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ProjectorSplitting
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Error bounds and exactness of the fixed-rank BUG integrator for tree tensor networks

Projector level, on a real inner product space; on tensors over a dimension tree, the step of one
inner node with exact `K`-steps is `DimTree.IsValid.isTuckerBUGStep` in
`LeanDLRA/Tensor/TTN/Integrators.lean`. The fixed-rank BUG integrator on a tree tensor network is
the recursive predicate `IsTTNBUGStep` over a frame `TTNFrame` (the tree with its old projectors
and the classes of admissible new projectors): a leaf is the exact flow, an inner node runs the
subtree steps for the `K`-step fields and then a Galerkin step in the new Tucker space. This file
proves that one step has a local error of size `h (ε + h)` with constants that are linear in the
number of nodes of the tree and contain no singular values, the resulting global error bound,
and exactness for a field that is the derivative of a recoverable curve. `ε` bounds
`(1 - P₁ i) ((1 - Q₀ i) (G t (K i)))`, the part of the field at the computed `K`-values that
lies outside the range of the old `K`-step projector and of the new mode projector; `L` and `B`
are the Lipschitz constant and the bound of the field.

## Main results

* `tucker_local_error_inexact`: a Tucker BUG step whose new bases capture computed `K`-values
  `K i` within `η i` of the exact `K`-step values has error at most
  `(e^{L h} - 1)(B h + Θ) + Θ` with `Θ = ∑ᵢ (h (4 L B h + L ηᵢ + ε) + ηᵢ)`. This is the step at
  one inner node in the induction over the tree.
* `ttn_capture`: at an inner node the new mode projectors fix the result and capture the exact
  solution up to `h (4 L B h + L ηᵢ + ε) + ηᵢ`, with `ηᵢ` the error bound of the subtree `i`.
* `ttn_local_error`: one step from `Y₀ = A t₀` has error at most `ttnErrBound L B ε h fr`.
* `ttn_local_error_le_size`: if `2 L h · height ≤ 1`, the error of one step is at most
  `3 · size · h (ε + 6 L B h)`.
* `ttn_global_error_le`: for frames with at most `s` nodes and height at most `ℓ`, `2 L h ℓ ≤ 1`,
  initial error `δ` and `n h ≤ T`, `‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h))`.
* `ttn_exact`: for `F(t, Y) = Ȧ(t)` and `Y₀ = A t₀`, if `A t₁` is recoverable along the frame
  (`IsTTNRecoverable`), one step gives `A t₁`.

## Implementation notes

The statements are over the recursive step predicate of `LeanDLRA/Tensor/Steps.lean`; bases, QR
factorizations and matricizations do not appear, only the orthogonal projectors they define.
[CerutiLubichWalach2021, Thm. 5.1 and Thm. 6.1] treat the projector-splitting integrator on tree
tensor networks; the statements here are the analogues for the BUG integrator, with explicit
constants. The field is assumed Lipschitz and bounded on the whole space.

## References

* [CerutiLubich2022]
* [CerutiLubichSulz2023]
* [CerutiLubichWalach2021]
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Inexact

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- A Tucker BUG step whose new mode bases capture computed `K`-values `K i` that are within
`η i` of the exact `K`-step values has local error at most `(e^{L h} - 1)(B h + Θ) + Θ` with
`Θ = ∑ᵢ (h (4 L B h + L ηᵢ + ε) + ηᵢ)`; no singular value enters. This is the step at one inner
node of a tree, where the `K i` are computed by the integrators of the subtrees. It is the
analogue for the BUG integrator of the induction step in the proof of
[CerutiLubichWalach2021, Thm. 6.1], which treats the projector-splitting integrator. -/
theorem tucker_local_error_inexact {d : ℕ} {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E}
    {YK : Fin d → ℝ → E} {K : Fin d → E} {η : Fin d → ℝ} {YS : ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : ∀ i, IsOrthProj (P₁ i)) (hQ₀ : ∀ i, IsOrthProj (Q₀ i))
    (hc : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = Y₀)
    (hKerr : ∀ i, ‖K i - YK i t₁‖ ≤ η i) (hKcap : ∀ i, P₁ i (K i) = K i)
    (hε : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (K i)))‖ ≤ ε)
    (hS : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = modeProd P₁ Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) *
        (B * h + ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i)) +
      ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i) := by
  have hcap : ‖A t₁ - modeProd P₁ (A t₁)‖ ≤
      ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i) := by
    refine (norm_sub_modeProd_apply_le (fun i => (hP₁ i).norm_le) (A t₁)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    have := kstep_capture_inexact hF hL hB (hP₁ i) (hQ₀ i) ht₁ hh hA (hK i)
      ((hK₀ i).trans hA₀.symm) (hKerr i) (hKcap i) (hε i)
    simpa using this
  exact galerkin_step_error (IsOrthProj.modeProd hP₁ hc) hF hL hB ht₁ hh hA hS
    (by rw [hS₀, hA₀]) hcap

end Inexact

section TTN

variable {G : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- Induction hypothesis shape for the local error over the children of a node. -/
private def TTNLocalIH (L B ε t₀ t₁ h : ℝ) (fr : TTNFrame E) : Prop :=
  ∀ (G : ℝ → E → E) (A : ℝ → E) (Y₀ Y₁ : E), IsLipschitzField G L → IsBoundedField G B →
    (∀ x, Continuous fun t => G t x) → IsTTNBUGStep fr G ε t₀ t₁ Y₀ Y₁ →
    ODESolution G A t₀ t₁ → A t₀ = Y₀ → ‖Y₁ - A t₁‖ ≤ ttnErrBound L B ε h fr

/-- Capture and Galerkin data of one inner node, given the local error for the children. -/
private theorem ttn_node_data [CompleteSpace E] {m : ℕ} {P₀ Q₀ : Fin m → E →L[ℝ] E}
    {𝓛 : Fin m → Set (E →L[ℝ] E)} {cs : Fin m → TTNFrame E}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hcont : ∀ x, Continuous fun t => G t x) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {Y₀ Y₁ : E}
    (hs : IsTTNBUGStep (.node m P₀ Q₀ 𝓛 cs) G ε t₀ t₁ Y₀ Y₁)
    (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (ih : ∀ i, TTNLocalIH L B ε t₀ t₁ h (cs i)) :
    ∃ (P₁ : Fin m → E →L[ℝ] E) (YS : ℝ → E), (∀ i, IsOrthProj (P₁ i)) ∧
      (∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) ∧ modeProd P₁ Y₁ = Y₁ ∧
      (∀ i, ‖(1 - P₁ i) (A t₁)‖ ≤
        h * (4 * L * B * h + L * ttnErrBound L B ε h (cs i) + ε) + ttnErrBound L B ε h (cs i)) ∧
      ODESolution (fun t x => modeProd P₁ (G t x)) YS t₀ t₁ ∧ YS t₀ = modeProd P₁ Y₀ ∧
      YS t₁ = Y₁ := by
  have hle : t₀ ≤ t₁ := by linarith
  rw [IsTTNBUGStep] at hs
  obtain ⟨-, hQ₀, -, -, P₁, K, YS, hP₁, -, hc, hsub, hKcap, hε, hYS, hYS0, hYS1⟩ := hs
  have hex : ∀ i, ∃ y : ℝ → E, ODESolution (fun t x => Q₀ i (G t x)) y t₀ t₁ ∧ y t₀ = Y₀ :=
    fun i => exists_ODESolution_clm hG hB hcont (Q₀ i) hle Y₀
  choose YK hYK hYK0 using hex
  have hKerr : ∀ i, ‖K i - YK i t₁‖ ≤ ttnErrBound L B ε h (cs i) := fun i =>
    ih i (fun t x => Q₀ i (G t x)) (YK i) Y₀ (K i) (hG.comp_contraction (Q₀ i) (hQ₀ i).norm_le)
      (hB.comp_contraction (Q₀ i) (hQ₀ i).norm_le)
      (fun x => (Q₀ i).continuous.comp (hcont x)) (hsub i) (hYK i) (hYK0 i)
  have hPi := IsOrthProj.modeProd hP₁ hc
  refine ⟨P₁, YS, hP₁, hc, ?_, fun i => ?_, hYS, hYS0, hYS1⟩
  · rw [← hYS1]
    exact hYS.fixed_of_fixed_field (fun t x => hPi.idem _) (by rw [hYS0]; exact hPi.idem _) t₁
      ⟨hle, le_rfl⟩
  · exact kstep_capture_inexact hG hL hB (hP₁ i) (hQ₀ i) ht₁ hh hA (hYK i)
      ((hYK0 i).trans hA₀.symm) (hKerr i) (hKcap i) (hε i)

/-- Local error of the TTN BUG step, by induction over the frame. -/
private theorem ttn_local_error_aux [CompleteSpace E] (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hL : 0 ≤ L) (fr : TTNFrame E) : TTNLocalIH L B ε t₀ t₁ h fr := by
  induction fr with
  | leaf =>
    intro G A Y₀ Y₁ hG hB hcont hs hA hA₀
    obtain ⟨y, hy, hy0, hy1⟩ := hs
    have hle : t₀ ≤ t₁ := by linarith
    have := hy.eqOn hA hG hL (hy0.trans hA₀.symm)
      ⟨hle, le_rfl⟩
    rw [← hy1, this]
    simp [ttnErrBound]
  | node m P₀ Q₀ 𝓛 cs ih =>
    intro G A Y₀ Y₁ hG hB hcont hs hA hA₀
    obtain ⟨P₁, YS, hP₁, hc, -, hcap, hYS, hYS0, hYS1⟩ :=
      ttn_node_data hG hL hB hcont ht₁ hh hs hA hA₀ ih
    have hPi := IsOrthProj.modeProd hP₁ hc
    have hcap' : ‖A t₁ - modeProd P₁ (A t₁)‖ ≤ ∑ i, (h * (4 * L * B * h + L *
        ttnErrBound L B ε h (cs i) + ε) + ttnErrBound L B ε h (cs i)) := by
      refine (norm_sub_modeProd_apply_le (fun i => (hP₁ i).norm_le) (A t₁)).trans ?_
      exact Finset.sum_le_sum fun i _ => by simpa using hcap i
    have := galerkin_step_error hPi hG hL hB ht₁ hh hA hYS (by rw [hYS0, hA₀]) hcap'
    rw [hYS1] at this
    simpa only [ttnErrBound] using this

/-- At an inner node of a step of the fixed-rank BUG integrator on a tree tensor network there
are orthogonal mode projectors `P₁ i` that fix the result, `modeProd P₁ Y₁ = Y₁`, and capture the
exact solution up to `‖(1 - P₁ i) (A t₁)‖ ≤ h (4 L B h + L ηᵢ + ε) + ηᵢ`, where
`ηᵢ = ttnErrBound L B ε h (cs i)` bounds the error of the `K`-step computed on the subtree
`i`. -/
theorem ttn_capture [CompleteSpace E] {m : ℕ} {P₀ Q₀ : Fin m → E →L[ℝ] E}
    {𝓛 : Fin m → Set (E →L[ℝ] E)} {cs : Fin m → TTNFrame E}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hcont : ∀ x, Continuous fun t => G t x) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {Y₀ Y₁ : E}
    (hs : IsTTNBUGStep (.node m P₀ Q₀ 𝓛 cs) G ε t₀ t₁ Y₀ Y₁)
    (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ∃ P₁ : Fin m → E →L[ℝ] E, (∀ i, IsOrthProj (P₁ i)) ∧ modeProd P₁ Y₁ = Y₁ ∧
      ∀ i, ‖(1 - P₁ i) (A t₁)‖ ≤
        h * (4 * L * B * h + L * ttnErrBound L B ε h (cs i) + ε) + ttnErrBound L B ε h (cs i) := by
  have ih : ∀ i, TTNLocalIH L B ε t₀ t₁ h (cs i) := fun i => ttn_local_error_aux ht₁ hh hL (cs i)
  obtain ⟨P₁, -, hP₁, -, hfix, hcap, -⟩ := ttn_node_data hG hL hB hcont ht₁ hh hs hA hA₀ ih
  exact ⟨P₁, hP₁, hfix, hcap⟩

/-- For an `L`-Lipschitz, `B`-bounded field and the exact solution `A` with `A t₀ = Y₀`, one
step of the fixed-rank BUG integrator on a tree tensor network has error
`‖Y₁ - A t₁‖ ≤ ttnErrBound L B ε h fr`. The recursive bound contains no singular values of
matricizations of connecting tensors; `ttn_local_error_le_size` gives its size. Analogue for the
BUG integrator of the local error in the proof of [CerutiLubichWalach2021, Thm. 6.1], which
treats the projector-splitting integrator. -/
theorem ttn_local_error [CompleteSpace E] {fr : TTNFrame E} (hG : IsLipschitzField G L)
    (hL : 0 ≤ L) (hB : IsBoundedField G B) (hcont : ∀ x, Continuous fun t => G t x)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {Y₀ Y₁ : E} (hs : IsTTNBUGStep fr G ε t₀ t₁ Y₀ Y₁)
    (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ ttnErrBound L B ε h fr :=
  ttn_local_error_aux ht₁ hh hL fr G A Y₀ Y₁ hG hB hcont hs hA hA₀

private theorem ttn_arith {m : ℕ} {x c g : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hg : 0 ≤ g) {H : ℕ}
    {s e : Fin m → ℝ} (he : ∀ i, e i ≤ (Real.exp x * (1 + x)) ^ H * (s i * g + (s i - 1) * c)) :
    g + Real.exp x * ∑ i, (c + (1 + x) * e i) ≤
      (Real.exp x * (1 + x)) ^ (H + 1) * ((1 + ∑ i, s i) * g + (∑ i, s i) * c) := by
  set κ := Real.exp x * (1 + x) with hκ
  have hex : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hκ1 : 1 ≤ κ := one_le_mul_of_one_le_of_one_le hex (by linarith)
  have hpow : 1 ≤ κ ^ (H + 1) := one_le_pow₀ hκ1
  have hexpκ : Real.exp x ≤ κ ^ (H + 1) :=
    calc Real.exp x ≤ κ := le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ κ ^ (H + 1) := le_self_pow₀ hκ1 (by omega)
  have hstep : ∑ i, (c + (1 + x) * e i) ≤
      ∑ i, (c + (1 + x) * (κ ^ H * (s i * g + (s i - 1) * c))) :=
    Finset.sum_le_sum fun i _ => by gcongr; exact he i
  have hsum : ∑ i, (c + (1 + x) * (κ ^ H * (s i * g + (s i - 1) * c))) =
      m * c + (1 + x) * κ ^ H * (g * ∑ i, s i + c * (∑ i, s i - m)) := by
    have e1 : ∑ i, (s i * g + (s i - 1) * c) = g * ∑ i, s i + c * (∑ i, s i - m) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    have e2 : ∀ i, c + (1 + x) * (κ ^ H * (s i * g + (s i - 1) * c)) =
        c + ((1 + x) * κ ^ H) * (s i * g + (s i - 1) * c) := fun i => by ring
    simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, e1, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hκH : Real.exp x * ((1 + x) * κ ^ H) = κ ^ (H + 1) := by rw [hκ]; ring
  have h1 : g ≤ κ ^ (H + 1) * g := le_mul_of_one_le_left hg hpow
  have h2 : Real.exp x * (m * c) ≤ κ ^ (H + 1) * (m * c) :=
    mul_le_mul_of_nonneg_right hexpκ (by positivity)
  calc g + Real.exp x * ∑ i, (c + (1 + x) * e i)
      ≤ g + Real.exp x * (m * c + (1 + x) * κ ^ H * (g * ∑ i, s i + c * (∑ i, s i - m))) := by
        rw [← hsum]; gcongr
    _ = g + Real.exp x * (m * c) + κ ^ (H + 1) * (g * ∑ i, s i + c * (∑ i, s i - m)) := by
        rw [← hκH]; ring
    _ ≤ κ ^ (H + 1) * g + κ ^ (H + 1) * (m * c) +
          κ ^ (H + 1) * (g * ∑ i, s i + c * (∑ i, s i - m)) := by linarith
    _ = _ := by ring

private theorem ttn_size_pos (fr : TTNFrame E) : 1 ≤ fr.size := by
  cases fr <;> simp [TTNFrame.size]

private theorem ttnErrBound_le_aux {L B ε h : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hh : 0 ≤ h) (fr : TTNFrame E) :
    ttnErrBound L B ε h fr ≤ (Real.exp (L * h) * (1 + L * h)) ^ fr.height *
      (fr.size * ((Real.exp (L * h) - 1) * (B * h)) +
        (fr.size - 1) * (h * (4 * L * B * h + ε))) := by
  have hx : 0 ≤ L * h := mul_nonneg hL hh
  have hc : 0 ≤ h * (4 * L * B * h + ε) := by positivity
  have hg : 0 ≤ (Real.exp (L * h) - 1) * (B * h) :=
    mul_nonneg (sub_nonneg.2 (Real.one_le_exp hx)) (by positivity)
  have hκ1 : 1 ≤ Real.exp (L * h) * (1 + L * h) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp hx) (by linarith)
  induction fr with
  | leaf =>
    simp only [ttnErrBound, TTNFrame.height, TTNFrame.size, pow_zero, Nat.cast_one, sub_self,
      zero_mul, add_zero, one_mul]
    exact hg
  | node m P₀ Q₀ 𝓛 cs ih =>
    have hs1 : ∀ i, (1 : ℝ) ≤ (cs i).size := fun i => by exact_mod_cast ttn_size_pos (cs i)
    have he : ∀ i, ttnErrBound L B ε h (cs i) ≤
        (Real.exp (L * h) * (1 + L * h)) ^ (Finset.univ.sup fun i => (cs i).height) *
          (((cs i).size : ℝ) * ((Real.exp (L * h) - 1) * (B * h)) +
            (((cs i).size : ℝ) - 1) * (h * (4 * L * B * h + ε))) := fun i =>
      (ih i).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hκ1 (Finset.le_sup (f := fun i => (cs i).height) (Finset.mem_univ i)))
        (by nlinarith [hs1 i]))
    have key := ttn_arith hx hc hg he
    have hΘ : ∀ i, h * (4 * L * B * h + L * ttnErrBound L B ε h (cs i) + ε) +
        ttnErrBound L B ε h (cs i) =
        h * (4 * L * B * h + ε) + (1 + L * h) * ttnErrBound L B ε h (cs i) := fun i => by ring
    simp only [ttnErrBound, TTNFrame.height, TTNFrame.size, hΘ]
    push_cast
    convert key using 1
    · ring
    · ring

/-- If `2 L h · height ≤ 1`, one step of the fixed-rank BUG integrator on a tree tensor network
has error at most `3 · size · h (ε + 6 L B h)`: the constants are linear in the number of nodes
`fr.size` of the tree (leaves included). In [CerutiLubichWalach2021, Thm. 6.1], which treats the
projector-splitting integrator, the constants depend on the tree; here the dependence is
explicit. -/
theorem ttn_local_error_le_size [CompleteSpace E] {fr : TTNFrame E} (hG : IsLipschitzField G L)
    (hL : 0 ≤ L) (hB : IsBoundedField G B) (hcont : ∀ x, Continuous fun t => G t x)
    (hε : 0 ≤ ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hLh : 2 * L * h * fr.height ≤ 1) {Y₀ Y₁ : E}
    (hs : IsTTNBUGStep fr G ε t₀ t₁ Y₀ Y₁) (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ 3 * fr.size * (h * (ε + 6 * L * B * h)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
  refine (ttn_local_error hG hL hB hcont ht₁ hh hs hA hA₀).trans ?_
  have hbd := ttnErrBound_le_aux hL hB0 hε hh fr
  have hD : 0 ≤ h * (ε + 6 * L * B * h) := by positivity
  rcases fr with _ | ⟨m, P₀, Q₀, 𝓛, cs⟩
  · simp only [ttnErrBound, TTNFrame.size, Nat.cast_one, mul_one]
    positivity
  · have hH : (1 : ℝ) ≤ ((TTNFrame.node m P₀ Q₀ 𝓛 cs).height : ℝ) := by
      simp only [TTNFrame.height]
      exact_mod_cast Nat.le_add_left 1 _
    have hx : 0 ≤ L * h := mul_nonneg hL hh
    have hx2 : L * h ≤ 1 / 2 := by nlinarith
    have hκ : (Real.exp (L * h) * (1 + L * h)) ^ (TTNFrame.node m P₀ Q₀ 𝓛 cs).height ≤ 3 := by
      have h1 : Real.exp (L * h) * (1 + L * h) ≤ Real.exp (2 * (L * h)) := by
        rw [two_mul, Real.exp_add]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (L * h)])
          (Real.exp_pos _).le
      calc _ ≤ Real.exp (2 * (L * h)) ^ (TTNFrame.node m P₀ Q₀ 𝓛 cs).height :=
            pow_le_pow_left₀ (by positivity) h1 _
        _ = Real.exp (((TTNFrame.node m P₀ Q₀ 𝓛 cs).height : ℕ) * (2 * (L * h))) :=
            (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by nlinarith)
        _ ≤ 3 := Real.exp_one_lt_three.le
    have hg : (Real.exp (L * h) - 1) * (B * h) ≤ 2 * (L * h) * (B * h) := by
      have := Real.exp_bound_div_one_sub_of_interval hx (by linarith : L * h < 1)
      have h2 : Real.exp (L * h) - 1 ≤ 2 * (L * h) := by
        have h3 : 1 / (1 - L * h) ≤ 1 + 2 * (L * h) := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
        linarith
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hs1 : (1 : ℝ) ≤ (TTNFrame.node m P₀ Q₀ 𝓛 cs).size := by
      exact_mod_cast ttn_size_pos _
    have hW : (((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ)) * ((Real.exp (L * h) - 1) * (B * h)) +
        (((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ) - 1) * (h * (4 * L * B * h + ε)) ≤
        ((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ) * (h * (ε + 6 * L * B * h)) := by
      have hc : 0 ≤ h * (4 * L * B * h + ε) := by positivity
      have hcg : (Real.exp (L * h) - 1) * (B * h) + h * (4 * L * B * h + ε) ≤
          h * (ε + 6 * L * B * h) := by nlinarith
      nlinarith
    have hnn : 0 ≤ (((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ)) *
        ((Real.exp (L * h) - 1) * (B * h)) +
        (((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ) - 1) * (h * (4 * L * B * h + ε)) := by
      have hc : 0 ≤ h * (4 * L * B * h + ε) := by positivity
      have hg0 : 0 ≤ (Real.exp (L * h) - 1) * (B * h) :=
        mul_nonneg (sub_nonneg.2 (Real.one_le_exp hx)) (by positivity)
      have : (0 : ℝ) ≤ ((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ) - 1 := by linarith
      positivity
    calc _ ≤ _ := hbd
      _ ≤ 3 * (((TTNFrame.node m P₀ Q₀ 𝓛 cs).size : ℝ) * (h * (ε + 6 * L * B * h))) :=
          mul_le_mul hκ hW hnn (by norm_num)
      _ = _ := by ring

end TTN

section TTNGlobal

variable {F : ℝ → E → E} {L B ε : ℝ}

/-- **Robust error bound of the fixed-rank BUG integrator for tree tensor networks.** For
frames with at most `s` nodes and height at most `ℓ`, `2 L h ℓ ≤ 1`, initial error `δ` and
`n h ≤ T`, `‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h))`; no singular value of a
matricization of a connecting tensor enters. Analogue for the BUG integrator of
[CerutiLubichWalach2021, Thm. 6.1], which states `c₀ δ + c₁ ε + c₂ h` for the
projector-splitting integrator; here the constants are explicit, `ε` enters through the step
predicate `IsTTNBUGStep`, and the field is Lipschitz and bounded on the whole space. -/
theorem ttn_global_error_le [CompleteSpace E] (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {fr : ℕ → TTNFrame E} {Y : ℕ → E} {s ℓ : ℕ} (hsize : ∀ n < N, (fr n).size ≤ s)
    (hheight : ∀ n < N, (fr n).height ≤ ℓ) (hLh : 2 * L * h * ℓ ≤ 1)
    (hstep : ∀ n < N, IsTTNBUGStep (fr n) F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (δ + T * (3 * s * (ε + 6 * L * B * h))) := by
  intro n hn hT
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ 0)
  have hex : ∀ k : ℕ, ∃ y : ℝ → E, ODESolution F y (t₀ + k * h) (t₀ + (k + 1) * h) ∧
      y (t₀ + k * h) = Y k := fun k =>
    exists_ODESolution hF hB hcont (by nlinarith) (Y k)
  choose Φ hΦ hΦ₀ using hex
  have hg : 0 ≤ 3 * (s : ℝ) * (ε + 6 * L * B * h) := by positivity
  have hloc : ∀ k < N, ‖Y (k + 1) - Φ k (t₀ + (k + 1) * h)‖ ≤
      h * (3 * (s : ℝ) * (ε + 6 * L * B * h)) := by
    intro k hk
    have hLh' : 2 * L * h * ((fr k).height : ℝ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hheight k hk)
        (by positivity)) hLh
    have h1 := ttn_local_error_le_size hF hL hB hcont hε (t₀ := t₀ + k * h)
      (t₁ := t₀ + (k + 1) * h) (h := h) (by ring) hh hLh' (hstep k hk) (hΦ k) (hΦ₀ k)
    refine h1.trans ?_
    have hs : ((fr k).size : ℝ) ≤ s := by exact_mod_cast hsize k hk
    have hD : 0 ≤ h * (ε + 6 * L * B * h) := by positivity
    nlinarith
  have hfan := lady_windermere_of_le hF hL hh hA (fun k hk => hΦ k) (fun k hk => hΦ₀ k) hg hloc
    n hn hT
  exact hfan.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)

end TTNGlobal

section Exact

variable {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ}

private theorem ttn_exact_aux {t₀ t₁ ε : ℝ} (ht : t₀ ≤ t₁) (fr : TTNFrame E) :
    ∀ (F : ℝ → E → E) (A : ℝ → E) (Y₁ : E), IsDerivRHS F A t₀ t₁ →
      IsTTNBUGStep fr F ε t₀ t₁ (A t₀) Y₁ → IsTTNRecoverable fr (A t₁) → Y₁ = A t₁ := by
  induction fr with
  | leaf =>
    intro F A Y₁ hA hs _
    obtain ⟨y, hy, hy0, hy1⟩ := hs
    rw [← hy1]
    exact Exactness.galerkin_exact (Pg := 1) ht hA (y := y) hy (Y₀ := A t₀) hy0 rfl rfl
  | node m P₀ Q₀ 𝓛 cs ih =>
    intro F A Y₁ hA hs hrec
    rw [IsTTNBUGStep] at hs
    obtain ⟨-, hQ₀, -, hQ₀Y, P₁, K, YS, hP₁, hP₁L, hc, hsub, hKcap, -, hYS, hYS0, hYS1⟩ := hs
    have hK : ∀ i, K i = Q₀ i (A t₁) := fun i => by
      have hd : IsDerivRHS (fun t x => Q₀ i (F t x)) (fun t => Q₀ i (A t)) t₀ t₁ :=
        ⟨(Q₀ i).continuous.comp_continuousOn hA.cont, fun t ht' Y =>
          (Q₀ i).hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht' Y)⟩
      exact ih i _ _ _ hd (by simpa [hQ₀Y i] using hsub i) (hrec i).2
    have hP1 : ∀ i, P₁ i (A t₁) = A t₁ := fun i =>
      Exactness.apply_eq_self_of_isRecoverable (hP₁L i) (by rw [← hK i]; exact hKcap i)
        (hrec i).1
    rw [← hYS1]
    exact Exactness.galerkin_exact ht hA hYS hYS0 rfl (modeProd_apply_eq_self hP1)

/-- **Exactness of the fixed-rank BUG integrator for tree tensor networks.** For
`F(t, Y) = Ȧ(t)` and `Y₀ = A t₀`, if `A t₁` is recoverable along the frame (`IsTTNRecoverable`,
the form of the overlap condition at every inner node), one step gives `Y₁ = A t₁`. Analogue for
the BUG integrator of [CerutiLubichWalach2021, Thm. 5.1], which treats the projector-splitting
integrator; the case of one level is [CerutiLubich2022, Thm. 6]. The recoverability hypothesis
takes the place of the non-degeneracy condition of the papers. -/
theorem ttn_exact {fr : TTNFrame E} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {ε : ℝ}
    {Y₁ : E} (hs : IsTTNBUGStep fr F ε t₀ t₁ (A t₀) Y₁) (hrec : IsTTNRecoverable fr (A t₁)) :
    Y₁ = A t₁ :=
  ttn_exact_aux ht fr F A Y₁ hA hs hrec

end Exact

end LeanDLRA
