import LeanDLRA.Tensor.Steps
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.CommutingProjectorTelescoping
import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ProjectorSplitting
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Error bounds and exactness of the rank-adaptive BUG integrator for tree tensor networks

Projector level, on a real inner product space; the frames of a dimension tree with given bases
are `DimTree.BasisFrame.toTTNFrame` in `LeanDLRA/Tensor/TTN/ParallelBUG.lean`. The rank-adaptive
BUG integrator on a tree tensor network is the recursive predicate `IsAugTTNBUGStep` over a frame
`TTNFrame`: at an inner node the new bases contain the old ones, the subtree steps are again
rank-adaptive, the Galerkin step starts from `Y₀`, and the result is truncated with tolerance
`ϑ`. `ε` bounds `(1 - P₁ i) ((1 - Q₀ i) (G t (K i)))` as for the fixed-rank integrator, `L` and
`B` are the Lipschitz constant and the bound of the field.

## Main results

* `augTTN_exact`: for `F(t, Y) = Ȧ(t)`, `Y₀ = A t₀` and `ϑ = 0`, one step gives `A t₁` if
  `A t₁` is recoverable from its `K`-step projections together with the old bases
  (`IsTTNAugRecoverable`).
* `augTTN_local_error_le_size`: if `2 L h · height ≤ 1`, the error of one step is at most
  `3 · size · (h (ε + 6 L B h) + ϑ)`.
* `augTTN_norm_sub_le`: if `⟪G t x, x⟫ = 0`, then `|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`.
* `augTTN_energy_le`: for `G t x = -∇ℰ(x)` with `‖∇ℰ(x)‖ ≤ β`, `ℰ(Y₁) ≤ ℰ(Y₀) + β ϑ`.
* `augTTN_global_error_le`: for frames with at most `s` nodes and height at most `ℓ`,
  `2 L h ℓ ≤ 1`, initial error `δ` and `n h ≤ T`,
  `‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h) + 3 s n ϑ)`.
* `exp_mul_one_add_pow_le_three`, `augTTN_arith`: the two arithmetic facts behind the constant
  `3` and the factor `size`; the parallel integrator uses them as well.

## Implementation notes

The statements are over the recursive step predicate of `LeanDLRA/Tensor/Steps.lean`; bases, QR
factorizations and matricizations do not appear, only the orthogonal projectors they define, and
the truncation is any `Y₁` with `‖Y₁ - YS t₁‖ ≤ ϑ`. The constants are explicit, and the field is
assumed Lipschitz and bounded on the whole space.

## References

* [CerutiKuschLubich2022]
* [CerutiLubichSulz2023]
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Exact

variable {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ}

private theorem augTTN_exact_aux (fr : TTNFrame E) :
    ∀ (F : ℝ → E → E) (A : ℝ → E) (t₀ t₁ : ℝ) (ε : ℝ) (Y₀ Y₁ : E), t₀ ≤ t₁ →
      IsDerivRHS F A t₀ t₁ → Y₀ = A t₀ → IsAugTTNBUGStep fr F ε 0 t₀ t₁ Y₀ Y₁ →
      IsTTNAugRecoverable fr (A t₁) → Y₁ = A t₁ := by
  induction fr with
  | leaf =>
    intro F A t₀ t₁ ε Y₀ Y₁ ht hA hY₀ hs _
    obtain ⟨y, hy, h0, h1⟩ := hs
    have hy' : ODESolution (fun t Y => (1 : E →L[ℝ] E) (F t Y)) y t₀ t₁ := by simpa using hy
    rw [← h1]
    exact Exactness.galerkin_exact (Pg := 1) (Y₀ := Y₀) ht hA hy' (by simp [h0, hY₀])
      (by simp [hY₀]) (by simp)
  | node m P₀ Q₀ 𝓛 cs ih =>
    intro F A t₀ t₁ ε Y₀ Y₁ ht hA hY₀ hs hrec
    obtain ⟨-, -, hP₀, hQ₀, P₁, K, YS, hP₁, hP𝓛, hc, haug, hK, hcap, -, hS, hS0, hY⟩ := hs
    have hfix : ∀ i, P₁ i Y₀ = Y₀ := fun i => by rw [← hP₀ i, haug i, hP₀ i]
    have hKeq : ∀ i, K i = Q₀ i (A t₁) := fun i => by
      have hAi : IsDerivRHS (fun t x => Q₀ i (F t x)) (fun t => Q₀ i (A t)) t₀ t₁ :=
        ⟨(Q₀ i).continuous.comp_continuousOn hA.cont, fun t ht Y =>
          (Q₀ i).hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht Y)⟩
      exact ih i (fun t x => Q₀ i (F t x)) (fun t => Q₀ i (A t)) t₀ t₁ ε Y₀ (K i) ht hAi
        (by simp only [← hY₀, hQ₀ i]) (hK i) (hrec i).2
    have hP1 : ∀ i, P₁ i (A t₁) = A t₁ := fun i => by
      obtain ⟨T, S, hT, hSS, z, hz⟩ := (hrec i).1
      have hcap' : P₁ i (Q₀ i (A t₁)) = Q₀ i (A t₁) := by rw [← hKeq i]; exact hcap i
      have hPz : P₁ i (P₀ i z) = P₀ i z := haug i z
      conv_lhs => rw [hz]
      rw [map_add, hT _ (hP𝓛 i), hSS _ (hP𝓛 i), hcap', hPz, ← hz]
    have hproj : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hP₁ hc
    have hS' : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁ := hS
    have := Exactness.galerkin_exact (Pg := modeProd P₁) ht hA hS' (Y₀ := Y₀)
      (by rw [hS0, modeProd_apply_eq_self hfix])
      (by rw [← hY₀, modeProd_apply_eq_self hfix]) (modeProd_apply_eq_self hP1)
    have h0 : Y₁ - YS t₁ = 0 := norm_le_zero_iff.1 (by simpa using hY)
    rw [sub_eq_zero.1 h0, this]

/-- **Exactness of the rank-adaptive BUG integrator for tree tensor networks.** For
`F(t, Y) = Ȧ(t)`, `Y₀ = A t₀` and truncation tolerance `ϑ = 0`, one step gives `Y₁ = A t₁` if
`A t₁` is augmented-recoverable along the frame (`IsTTNAugRecoverable`): at every inner node it
is recovered from its `K`-step projection together with the old basis, see `IsAugRecoverable`.
The exactness property of the rank-adaptive Tucker integrator is stated in
[CerutiKuschLubich2022, §4.2]; here the recoverability hypothesis takes the place of the
non-degeneracy condition. -/
theorem augTTN_exact {fr : TTNFrame E} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {ε : ℝ}
    {Y₁ : E} (hs : IsAugTTNBUGStep fr F ε 0 t₀ t₁ (A t₀) Y₁)
    (hrec : IsTTNAugRecoverable fr (A t₁)) : Y₁ = A t₁ :=
  augTTN_exact_aux fr F A t₀ t₁ ε (A t₀) Y₁ ht hA rfl hs hrec

end Exact

section AugTTN

variable {G : ℝ → E → E} {L B ε ϑ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- If `0 ≤ x` and `2 x n ≤ 1`, then `(e^x (1 + x))^n ≤ 3`. With `x = L h` and `n` the height of
the tree, this bounds the factor that the recursion over the tree accumulates in
`augTTN_local_error_le_size` and in the corresponding bound for the parallel integrator. -/
theorem exp_mul_one_add_pow_le_three {x : ℝ} (h0 : 0 ≤ x) {n : ℕ} (hn : 2 * x * n ≤ 1) :
    (Real.exp x * (1 + x)) ^ n ≤ 3 := by
  have hk : Real.exp x * (1 + x) ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp x
    rw [two_mul, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hk0 : 0 ≤ Real.exp x * (1 + x) := by positivity
  calc (Real.exp x * (1 + x)) ^ n ≤ Real.exp (2 * x) ^ n := pow_le_pow_left₀ hk0 hk n
    _ = Real.exp (2 * x * n) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp 1 := Real.exp_le_exp.2 hn
    _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith

/-- Non-vacuity of `exp_mul_one_add_pow_le_three` with nonzero data: `x = 1 / 4` and `n = 2`. -/
example : (Real.exp (1 / 4 : ℝ) * (1 + 1 / 4)) ^ 2 ≤ 3 :=
  exp_mul_one_add_pow_le_three (by norm_num) (by norm_num)

/-- The arithmetic of one inner node in the local error recursion of the rank-adaptive and of
the parallel BUG integrator on a tree. Let `κ = e^{L h} (1 + L h)`, `a = h (4 L B h + ε)`,
`b = (e^{L h} - 1) B h` and `Θ = ∑ i, (h (4 L B h + L η i + ε) + η i)`. If the error bounds of
the `m` subtrees are `η i = κ ^ ht i * ((sz i - 1) a + sz i (b + ϑ))`, then the bound
`(e^{L h} - 1) (B h + Θ) + Θ` of the Galerkin step at the node (`galerkin_step_error`) plus the
tolerance `ϑ` is at most `κ ^ (H + 1) * ((s - 1) a + s (b + ϑ))` with `s = 1 + ∑ i, sz i`, for
every `H` with `ht i ≤ H`. -/
theorem augTTN_arith {m : ℕ} {L B h ε ϑ : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) {sz ht : Fin m → ℕ} {H : ℕ} (hsz : ∀ i, 1 ≤ sz i)
    (hH : ∀ i, ht i ≤ H) {η : Fin m → ℝ}
    (hη : ∀ i, η i = (Real.exp (L * h) * (1 + L * h)) ^ ht i *
      (((sz i : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
        sz i * ((Real.exp (L * h) - 1) * (B * h) + ϑ))) :
    (Real.exp (L * h) - 1) * (B * h + ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i)) +
        ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i) + ϑ ≤
      (Real.exp (L * h) * (1 + L * h)) ^ (H + 1) *
        ((((1 + ∑ i, sz i : ℕ) : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
          ((1 + ∑ i, sz i : ℕ) : ℝ) * ((Real.exp (L * h) - 1) * (B * h) + ϑ)) := by
  set x := L * h with hx
  have hx0 : 0 ≤ x := mul_nonneg hL hh
  set a := h * (4 * L * B * h + ε) with ha
  have ha0 : 0 ≤ a := by positivity
  set b := (Real.exp x - 1) * (B * h) with hb
  have hb0 : 0 ≤ b := mul_nonneg (by linarith [Real.add_one_le_exp x]) (by positivity)
  set κ := Real.exp x * (1 + x) with hκ
  have hex : 1 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hκ1 : 1 ≤ κ := by rw [hκ]; nlinarith
  have hexκ : Real.exp x ≤ κ := by rw [hκ]; nlinarith [Real.exp_pos x]
  set c := κ ^ H with hc
  have hc1 : 1 ≤ c := one_le_pow₀ hκ1
  set X : Fin m → ℝ := fun i => ((sz i : ℝ) - 1) * a + sz i * (b + ϑ) with hX
  have hX0 : ∀ i, 0 ≤ X i := fun i => by
    have : (1 : ℝ) ≤ sz i := by exact_mod_cast hsz i
    simp only [hX]; nlinarith
  have hηle : ∀ i, η i ≤ c * X i := fun i => by
    rw [hη i]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hκ1 (hH i)) (hX0 i)
  have hη0 : ∀ i, 0 ≤ η i := fun i => by
    rw [hη i]; exact mul_nonneg (by positivity) (hX0 i)
  have hΘ : ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i) = m * a + (1 + x) * ∑ i, η i := by
    have : ∀ i, h * (4 * L * B * h + L * η i + ε) + η i = a + (1 + x) * η i := fun i => by
      rw [ha, hx]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hsum : ∑ i, η i ≤ c * ∑ i, X i := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hηle i
  have hsumX : ∑ i, X i = (∑ i, (sz i : ℝ)) * a - m * a + (∑ i, (sz i : ℝ)) * (b + ϑ) := by
    simp only [hX, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
    simp
    ring
  have hSX : 0 ≤ ∑ i, X i := Finset.sum_nonneg fun i _ => hX0 i
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hΘ]
  have hcast : (((1 + ∑ i, sz i : ℕ) : ℝ)) = 1 + ∑ i, (sz i : ℝ) := by push_cast; ring
  rw [hcast, pow_succ, ← hc]
  have hmain : (Real.exp x - 1) * (B * h + (m * a + (1 + x) * ∑ i, η i)) +
      (m * a + (1 + x) * ∑ i, η i) + ϑ =
      Real.exp x * (m * a + (1 + x) * ∑ i, η i) + b + ϑ := by rw [hb]; ring
  rw [hmain]
  have e1 : Real.exp x * ((1 + x) * ∑ i, η i) ≤ κ * (c * ∑ i, X i) := by
    rw [hκ]
    calc _ = (Real.exp x * (1 + x)) * ∑ i, η i := by ring
      _ ≤ (Real.exp x * (1 + x)) * (c * ∑ i, X i) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
  have hRHS : c * κ * ((1 + ∑ i, (sz i : ℝ) - 1) * a + (1 + ∑ i, (sz i : ℝ)) * (b + ϑ)) =
      κ * (c * ∑ i, X i) + c * κ * (m * a + b + ϑ) := by
    rw [hsumX]; ring
  rw [hRHS]
  have e2 : Real.exp x * (m * a) + b + ϑ ≤ c * κ * (m * a + b + ϑ) := by
    have h1 : 1 ≤ c * κ := by nlinarith
    have h2 : Real.exp x ≤ c * κ := by nlinarith
    have : 0 ≤ (m : ℝ) * a := mul_nonneg hm ha0
    nlinarith [mul_le_mul_of_nonneg_right h2 this, mul_le_mul_of_nonneg_right h1 hb0,
      mul_le_mul_of_nonneg_right h1 hϑ]
  nlinarith [e1, e2]

/-- Non-vacuity of `augTTN_arith` with nonzero data: one subtree of size `1` and height `0`, and
`L = B = h = ε = ϑ = 1`. -/
example := augTTN_arith (m := 1) (L := 1) (B := 1) (h := 1) (ε := 1) (ϑ := 1) zero_le_one
  zero_le_one zero_le_one zero_le_one zero_le_one (sz := fun _ => 1) (ht := fun _ => 0) (H := 0)
  (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl)

private theorem augTTN_local_aux [CompleteSpace E] {L B ε ϑ h : ℝ}
    (hL : 0 ≤ L) (hB0 : 0 ≤ B) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (hh : 0 ≤ h) (fr : TTNFrame E) :
    ∀ (G : ℝ → E → E) (t₀ t₁ : ℝ) (Y₀ Y₁ : E) (A : ℝ → E),
      IsLipschitzField G L → IsBoundedField G B → (∀ x, Continuous fun t => G t x) →
      t₁ = t₀ + h → IsAugTTNBUGStep fr G ε ϑ t₀ t₁ Y₀ Y₁ → ODESolution G A t₀ t₁ → A t₀ = Y₀ →
      ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) * (1 + L * h)) ^ fr.height *
        (((fr.size : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
          fr.size * ((Real.exp (L * h) - 1) * (B * h) + ϑ)) := by
  induction fr with
  | leaf =>
    intro G t₀ t₁ Y₀ Y₁ A hG hB hc ht₁ hs hA hA0
    obtain ⟨y, hy, h0, h1⟩ := hs
    have := hy.norm_sub_le_exp hG hL hA t₁ ⟨by linarith, le_rfl⟩
    rw [h0, ← hA0, sub_self, norm_zero, mul_zero] at this
    have hb0 : 0 ≤ (Real.exp (L * h) - 1) * (B * h) :=
      mul_nonneg (by linarith [Real.add_one_le_exp (L * h), mul_nonneg hL hh])
        (by positivity)
    rw [← h1]
    refine this.trans ?_
    simp only [TTNFrame.height, TTNFrame.size, pow_zero, Nat.cast_one, sub_self, zero_mul,
      one_mul, zero_add]
    linarith
  | node m P₀ Q₀ 𝓛 cs ih =>
    intro G t₀ t₁ Y₀ Y₁ A hG hB hc ht₁ hs hA hA0
    have hle : t₀ ≤ t₁ := by linarith
    obtain ⟨-, hQ0o, hP₀, hQ0, P₁, K, YS, hP1o, -, hcomm, haug, hK, hcap, heps, hS, hS0, hY⟩ := hs
    have hfix : ∀ i, P₁ i Y₀ = Y₀ := fun i => by rw [← hP₀ i, haug i, hP₀ i]
    have hkex : ∀ i, ∃ YK : ℝ → E, ODESolution (fun t x => Q₀ i (G t x)) YK t₀ t₁ ∧
        YK t₀ = Y₀ ∧ ‖K i - YK t₁‖ ≤ (Real.exp (L * h) * (1 + L * h)) ^ (cs i).height *
          ((((cs i).size : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
            (cs i).size * ((Real.exp (L * h) - 1) * (B * h) + ϑ)) := fun i => by
      obtain ⟨YK, hYK, hYK0⟩ := exists_ODESolution_clm hG hB hc (Q₀ i) hle Y₀
      exact ⟨YK, hYK, hYK0, ih i (fun t x => Q₀ i (G t x)) t₀ t₁ Y₀ (K i) YK
        (hG.comp_contraction _ (hQ0o i).norm_le) (hB.comp_contraction _ (hQ0o i).norm_le)
        (fun x => (Q₀ i).continuous.comp (hc x)) ht₁ (hK i) hYK hYK0⟩
    choose YK hYK hYK0 hKerr using hkex
    set η : Fin m → ℝ := fun i => (Real.exp (L * h) * (1 + L * h)) ^ (cs i).height *
          ((((cs i).size : ℝ) - 1) * (h * (4 * L * B * h + ε)) +
            (cs i).size * ((Real.exp (L * h) - 1) * (B * h) + ϑ)) with hη
    have hcapt : ∀ i, ‖A t₁ - P₁ i (A t₁)‖ ≤ h * (4 * L * B * h + L * η i + ε) + η i := fun i => by
      have := kstep_capture_inexact hG hL hB (hP1o i) (hQ0o i) ht₁ hh hA (hYK i)
        ((hYK0 i).trans hA0.symm) (hKerr i) (hcap i) (heps i)
      simpa [sub_apply] using this
    have hΘ : ‖A t₁ - modeProd P₁ (A t₁)‖ ≤
        ∑ i, (h * (4 * L * B * h + L * η i + ε) + η i) :=
      (norm_sub_modeProd_apply_le (fun i y => (hP1o i).norm_le y) _).trans
        (Finset.sum_le_sum fun i _ => hcapt i)
    have hproj : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hP1o hcomm
    have hgal := galerkin_step_error hproj hG hL hB ht₁ hh hA hS
      (by rw [hS0, hA0, modeProd_apply_eq_self hfix]) hΘ
    have harith := augTTN_arith (m := m) hL hB0 hε hϑ hh (sz := fun i => (cs i).size)
      (ht := fun i => (cs i).height) (H := Finset.univ.sup fun i => (cs i).height)
      (fun i => by cases cs i <;> simp [TTNFrame.size])
      (fun i => Finset.le_sup (f := fun i => (cs i).height) (Finset.mem_univ i)) (η := η)
      (fun i => rfl)
    have h2 : ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YS t₁‖ + ‖YS t₁ - A t₁‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    simp only [TTNFrame.height, TTNFrame.size]
    linarith

/-- If `2 L h · height ≤ 1`, one step of the rank-adaptive BUG integrator on a tree tensor
network with truncation tolerance `ϑ ≥ 0` at every inner node has error at most
`3 · size · (h (ε + 6 L B h) + ϑ)`; no singular value enters. The rank-adaptive integrator on
tree tensor networks is that of [CerutiLubichSulz2023]; the constants here are explicit. -/
theorem augTTN_local_error_le_size [CompleteSpace E] {fr : TTNFrame E}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hB : IsBoundedField G B)
    (hcont : ∀ x, Continuous fun t => G t x) (hε : 0 ≤ ε) (hϑ : 0 ≤ ϑ) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hLh : 2 * L * h * fr.height ≤ 1) {Y₀ Y₁ : E}
    (hs : IsAugTTNBUGStep fr G ε ϑ t₀ t₁ Y₀ Y₁) (hA : ODESolution G A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ 3 * fr.size * (h * (ε + 6 * L * B * h) + ϑ) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hLh0 : 0 ≤ L * h := mul_nonneg hL hh
  have hu : 0 ≤ h * (ε + 6 * L * B * h) + ϑ := by positivity
  have hsz : (1 : ℝ) ≤ fr.size := by
    have : 1 ≤ fr.size := by cases fr <;> simp only [TTNFrame.size] <;> omega
    exact_mod_cast this
  have haux := augTTN_local_aux hL hB0 hε hϑ hh fr G t₀ t₁ Y₀ Y₁ A hG hB hcont ht₁ hs hA hA₀
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
    have hV0 : 0 ≤ (sz - 1) * (h * (4 * L * B * h + ε)) +
        sz * ((Real.exp (L * h) - 1) * (B * h) + ϑ) := by
      have : 0 ≤ sz - 1 := by linarith
      positivity
    have hV : (sz - 1) * (h * (4 * L * B * h + ε)) +
        sz * ((Real.exp (L * h) - 1) * (B * h) + ϑ) ≤ sz * (h * (ε + 6 * L * B * h) + ϑ) := by
      have e1 : (sz - 1) * (h * (4 * L * B * h + ε)) ≤ sz * (h * (4 * L * B * h + ε)) := by
        nlinarith
      have e2 : (Real.exp (L * h) - 1) * (B * h) + ϑ + h * (4 * L * B * h + ε) ≤
          h * (ε + 6 * L * B * h) + ϑ := by nlinarith
      nlinarith
    calc ‖Y₁ - A t₁‖ ≤ _ := haux
      _ ≤ 3 * (sz * (h * (ε + 6 * L * B * h) + ϑ)) :=
        (mul_le_mul hk hV hV0 (by norm_num))
      _ = _ := by ring

/-- **Norm conservation up to the truncation tolerance.** If `⟪G t x, x⟫ = 0` for all `t` and
`x`, one step of the rank-adaptive BUG integrator on a tree tensor network satisfies
`|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`. The matrix case is [CerutiKuschLubich2022, Thm. 4]. -/
theorem augTTN_norm_sub_le {fr : TTNFrame E} (h01 : t₀ ≤ t₁) (hϑ : 0 ≤ ϑ)
    (hG : ∀ t x, ⟪G t x, x⟫ = 0) {Y₀ Y₁ : E} (hs : IsAugTTNBUGStep fr G ε ϑ t₀ t₁ Y₀ Y₁) :
    |‖Y₁‖ - ‖Y₀‖| ≤ ϑ := by
  cases fr with
  | leaf =>
    obtain ⟨y, hy, rfl, rfl⟩ := hs
    have hy' : ODESolution (fun t x => (1 : E →L[ℝ] E) (G t x)) y t₀ t₁ := by simpa using hy
    have h := hy'.galerkin_norm_eq IsOrthProj.one (by simp) (fun t _ => hG t _) t₁
      ⟨h01, le_rfl⟩
    rw [h]; simpa using hϑ
  | node m P₀ Q₀ 𝓛 cs =>
    obtain ⟨-, -, hP₀, -, P₁, K, YS, hP₁, -, hc, haug, -, -, -, hS, hS0, hY⟩ := hs
    have hfix : ∀ i, P₁ i Y₀ = Y₀ := fun i => by rw [← hP₀ i, haug i, hP₀ i]
    have hproj : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hP₁ hc
    have h0 : modeProd P₁ (YS t₀) = YS t₀ := by
      rw [hS0]; exact modeProd_apply_eq_self hfix
    have h := hS.galerkin_norm_eq hproj h0 (fun t _ => hG t _) t₁ ⟨h01, le_rfl⟩
    rw [hS0] at h
    rw [← h]
    exact (abs_norm_sub_norm_le _ _).trans hY

/-- **Energy decay up to the truncation tolerance.** For a gradient field `G t x = -∇ℰ(x)` with
`‖∇ℰ(x)‖ ≤ β` for all `x`, one step of the rank-adaptive BUG integrator on a tree tensor network
satisfies `ℰ(Y₁) ≤ ℰ(Y₀) + β ϑ`. The matrix case is [CerutiKuschLubich2022, Thm. 5], which has
in addition a decay term `-α² h`; here that term is dropped and `β` bounds the gradient on the
whole space. -/
theorem augTTN_energy_le {fr : TTNFrame E} (h01 : t₀ ≤ t₁) (hϑ : 0 ≤ ϑ) {ℰ : E → ℝ}
    {g : E → E} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hGg : ∀ t x, G t x = -g x)
    {β : ℝ} (hβ : ∀ x, ‖g x‖ ≤ β) {Y₀ Y₁ : E} (hs : IsAugTTNBUGStep fr G ε ϑ t₀ t₁ Y₀ Y₁) :
    ℰ Y₁ ≤ ℰ Y₀ + β * ϑ := by
  have hfun : (fun t x => G t x) = fun _ x => -g x := by
    funext t x; exact hGg t x
  cases fr with
  | leaf =>
    obtain ⟨y, hy, rfl, rfl⟩ := hs
    have hy' : ODESolution (fun _ x => -(1 : E →L[ℝ] E) (g x)) y t₀ t₁ := by
      simpa [hfun] using hy
    have h := hy'.energy_le_gradFlow IsOrthProj.one hℰ t₁ ⟨h01, le_rfl⟩
    have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0)
    nlinarith [mul_nonneg hβ0 hϑ]
  | node m P₀ Q₀ 𝓛 cs =>
    obtain ⟨-, -, hP₀, -, P₁, K, YS, hP₁, -, hc, haug, -, -, -, hS, hS0, hY⟩ := hs
    have hfix : ∀ i, P₁ i Y₀ = Y₀ := fun i => by rw [← hP₀ i, haug i, hP₀ i]
    have hproj : IsOrthProj (modeProd P₁) := IsOrthProj.modeProd hP₁ hc
    have hS' : ODESolution (fun _ x => -(modeProd P₁) (g x)) YS t₀ t₁ := by
      simpa [hGg] using hS
    have h1 := hS'.energy_le_gradFlow hproj hℰ t₁ ⟨h01, le_rfl⟩
    rw [hS0] at h1
    have h2 := abs_energy_sub_le hℰ (fun w _ => hβ w) (z := YS t₁) (x := Y₁)
    have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0)
    have h3 : β * ‖Y₁ - YS t₁‖ ≤ β * ϑ := mul_le_mul_of_nonneg_left hY hβ0
    have h4 := (abs_le.1 h2).2
    linarith

end AugTTN

section AugTTNGlobal

variable {F : ℝ → E → E} {L B ε ϑ : ℝ}

/-- **Robust error bound of the rank-adaptive BUG integrator for tree tensor networks.** For
frames with at most `s` nodes and height at most `ℓ`, `2 L h ℓ ≤ 1`, initial error `δ` and
`n h ≤ T`, `‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + 3 s T (ε + 6 L B h) + 3 s n ϑ)`; no singular value of a
matricization of a connecting tensor enters. The rank-adaptive integrator on tree tensor
networks is that of [CerutiLubichSulz2023]; here the constants are explicit, `ε` enters through
the step predicate `IsAugTTNBUGStep`, and the field is Lipschitz and bounded on the whole
space. -/
theorem augTTN_global_error_le [CompleteSpace E] (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε)
    (hϑ : 0 ≤ ϑ) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {fr : ℕ → TTNFrame E} {Y : ℕ → E} {s ℓ : ℕ}
    (hsize : ∀ n < N, (fr n).size ≤ s) (hheight : ∀ n < N, (fr n).height ≤ ℓ)
    (hLh : 2 * L * h * ℓ ≤ 1)
    (hstep : ∀ n < N,
      IsAugTTNBUGStep (fr n) F ε ϑ (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (Y (n + 1)))
    {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + T * (3 * s * (ε + 6 * L * B * h)) + 3 * s * (n * ϑ)) := by
  intro n hn hT
  have hex : ∀ n < N, ∃ Φ : ℝ → E, ODESolution F Φ (t₀ + n * h) (t₀ + (n + 1) * h) ∧
      Φ (t₀ + n * h) = Y n := fun n _ => by
    obtain ⟨Φ, hΦ, hΦ0⟩ := exists_ODESolution hF hB hcont (a := t₀ + n * h)
      (b := t₀ + (n + 1) * h) (by nlinarith) (Y n)
    exact ⟨Φ, hΦ, hΦ0⟩
  choose! Φ hΦ hΦ₀ using hex
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hu : 0 ≤ h * (ε + 6 * L * B * h) + ϑ := by
    have : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
    positivity
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      3 * s * (h * (ε + 6 * L * B * h) + ϑ) := by
    intro n hn
    have h1 : 2 * L * h * ((fr n).height : ℝ) ≤ 1 := by
      have : ((fr n).height : ℝ) ≤ ℓ := by exact_mod_cast hheight n hn
      have h2 : 0 ≤ 2 * L * h := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h2]
    have h3 := augTTN_local_error_le_size hF hL hB hcont hε hϑ (by ring) hh h1 (hstep n hn)
      (hΦ n hn) (hΦ₀ n hn)
    have h4 : ((fr n).size : ℝ) ≤ s := by exact_mod_cast hsize n hn
    exact h3.trans (mul_le_mul_of_nonneg_right (by linarith) hu)
  have h1 := lady_windermere_sum hF hL hh hA hΦ hΦ₀
    (ℓ := fun _ => 3 * s * (h * (ε + 6 * L * B * h) + ϑ)) hloc n hn
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hnh : (n : ℝ) * h ≤ T := hT
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hc0 : 0 ≤ 3 * (s : ℝ) * (ε + 6 * L * B * h) := by positivity
  have hin : ‖Y 0 - A t₀‖ + n * (3 * s * (h * (ε + 6 * L * B * h) + ϑ)) ≤
      δ + T * (3 * s * (ε + 6 * L * B * h)) + 3 * s * (n * ϑ) := by
    have := mul_le_mul_of_nonneg_right hnh hc0
    nlinarith
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (3 * s * (h * (ε + 6 * L * B * h) + ϑ)) := by
    have : 0 ≤ (n : ℝ) * (3 * s * (h * (ε + 6 * L * B * h) + ϑ)) := by positivity
    have := norm_nonneg (Y 0 - A t₀)
    linarith
  exact h1.trans (mul_le_mul hexp hin hin0 (Real.exp_pos _).le)

end AugTTNGlobal

end LeanDLRA
