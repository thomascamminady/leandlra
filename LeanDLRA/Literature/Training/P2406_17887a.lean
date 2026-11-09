import LeanDLRA.Training.Descent
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.OpenProblems.TensorNetworks.Part2a

/-!
# Results of arXiv 2406.17887: Federated dynamical low-rank training

Schotthöfer–Laiu, *Federated dynamical low-rank training with global loss convergence guarantees*.
This module states FeDLRT on actual matrix factors: client losses `ℒ_c` on `ℝ^{m × n}` with the
Frobenius inner product and `ℒ = (1/C) ∑_c ℒ_c` (`avgLoss`); all gradients are Mathlib `gradient`s
of the maps in question, e.g. `∇_S̃ ℒ_c` (`coeffGrad`) is the gradient of `S ↦ ℒ_c(Ũ S Ṽᵀ)`, and
`coeffGrad_eq` derives `∇_S̃ ℒ_c = Ũᵀ ∇ℒ_c Ṽ`; `L`-smooth (`IsLSmooth`) means `L`-Lipschitz gradient
(the paper's Lemma 4), and the smoothness of `ℒ` is derived from that of the `ℒ_c`.  It defines the
client iteration eq. (8) (`clientIter`), the aggregation eq. (10) (`roundCoeff`), the compression
step (`IsTruncation`), one iteration of Algorithm 1 (`IsFeDLRTRound`) and of Algorithm 5 with the
simplified correction eq. (9) (`simpClientIter`, `IsSimpRound`), and proves:
Lemma 1 and Lemma 7 (`lemma1_augmented_coeff`, `lemma7_augmented_weights`); Lemma 2 (`lemma2_K`,
`lemma2_L`); Theorem 1 (`theorem1_drift`); Theorem 8 (`theorem8_aggregate_descent`); Theorem 2
(`theorem2_loss_descent`, `theorem2_loss_descent'`, `theorem2_loss_descent_smooth`); Theorem 3
(`theorem3_convergence_general`, `theorem3_convergence`); corrected Theorem 4 and Corollary 1
(`theorem4_corrected_general`, `theorem4_corrected`, `corollary1_corrected`,
`assumption1Sq_of_assumption1`).  The estimates in the weights are those of the library
(`norm_fedClientIter_sub_le_exp`, `loss_fedRound_le`, `fedDLRT_span_eq`), which are used here and
not repeated; `mul_clientIter_mul` and `mul_roundCoeff_mul` identify them with the algorithm on
factors.

**False claims of the paper**, each with a formal counterexample on `ℝ^{2 × 2}`:
* Theorem 2 as stated, for merely `L`-smooth losses (`theorem2_false_of_smooth_only`): step (36) of
  its proof needs `‖∇ℒ‖ ≤ L`.  Hence `G ϑ`, with `‖∇ℒ‖ ≤ G` on the truncation segment, replaces
  `L ϑ`; `G = L` is `theorem2_loss_descent'`, and `theorem2_loss_descent_smooth` is the form under
  smoothness alone.  The same applies to `48 L² ϑ` in Theorem 3, which becomes `48 L G ϑ`.
* Theorem 3 for all `λ ≤ 1/(12 L s⋆)` (`theorem3_false_of_small_lr`): the proof takes
  `λ = 1/(24 L s⋆)`, the only learning rate for which the constant `48` follows from Theorem 2.
* Theorem 4 and Corollary 1 under Assumption 1 as printed (`theorem4_false`): eq. (14) compares
  norms, so a large gradient in the block of `S` hides a large gradient in the augmented blocks, and
  the loss can increase.  The proof in Appendix G.1 also uses `δ²` where eq. (14) gives `δ`, uses
  `‖Uᵀ F V‖ ≤ ‖Ũᵀ F Ṽ‖` in the wrong direction, and the term `δ² s⋆ λ` in `C` is dimensionally
  inconsistent.  With eq. (14) for squared norms (`Assumption1Sq`, the blocks themselves are small)
  and `δ ≤ 1/6`, Algorithm 5 has the descent of Theorem 2 (`theorem4_corrected`).

Other differences from the paper: the bases `Ū, V̄` are any orthonormal extension, of any size, and
`S` need not have full rank (the analysis uses neither the gradient augmentation nor the rank);
`IsTruncation` only requires `‖S̃⋆ - P S' Qᵀ‖ ≤ ϑ`, which the truncated SVD satisfies; the learning
rate restriction is relaxed to `λ L s⋆ ≤ 1` where possible; iterations are numbered from `0`, and
`min_t` is written `∃ t < T`.  Not formalised: Theorem 5 (cited from another paper, see
`Training/GradientFlowConvergence.lean`), and the remark after Theorem 3 on stationary points.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2406_17887

open LeanDLRA

/-! ### Simplified variance correction: abstract form -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {β lr : ℝ} {P T : E →L[ℝ] E}

/-- Client iterates of FeDLRT with simplified variance correction (arXiv 2406.17887, eq. (40), with
the sign and the factor `λ` of the correction as in eq. (45), see `simpClientIter`) in full weights:
`z⁰ = x`, `z^{s+1} = z^s - λ (Π ∇ℒ_c(z^s) + Π₀ (∇ℒ(x) - ∇ℒ_c(x)))`, where `Π` is the Galerkin
projector of the augmented bases and `T = Π₀` the one of the original bases. -/
def simpClientIterE (P T : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ) (x : E) (c : ι) :
    ℕ → E
  | 0 => x
  | s + 1 => simpClientIterE P T gc g lr x c s -
      lr • (P (gc c (simpClientIterE P T gc g lr x c s)) + T (g x - gc c x))

lemma simpClientIterE_succ (P T : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ) (x : E) (c : ι)
    (s : ℕ) : simpClientIterE P T gc g lr x c (s + 1) = simpClientIterE P T gc g lr x c s -
      lr • (P (gc c (simpClientIterE P T gc g lr x c s)) + T (g x - gc c x)) := rfl

/-- Closed form of the simplified client iterates: as for the full correction, up to the term
`(Π - Π₀)(∇ℒ_c(x) - ∇ℒ(x))`, which has mean zero over the clients. -/
lemma simpClientIterE_eq (P T : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ) (x : E) (c : ι)
    (s : ℕ) :
    simpClientIterE P T gc g lr x c s = x - ((s : ℝ) * lr) • P (g x) -
      lr • ∑ j ∈ range s, P (gc c (simpClientIterE P T gc g lr x c j) - gc c x) -
      ((s : ℝ) * lr) • (P (gc c x - g x) - T (gc c x - g x)) := by
  induction s with
  | zero => simp [simpClientIterE]
  | succ s ih =>
    rw [simpClientIterE_succ, sum_range_succ]
    nth_rw 1 [ih]
    have e : T (g x - gc c x) = - T (gc c x - g x) := by rw [← map_neg, neg_sub]
    rw [e, map_sub P (gc c (simpClientIterE P T gc g lr x c s)) (gc c x),
      map_sub P (gc c x) (g x)]
    push_cast
    module

/-- The aggregated round with simplified variance correction. -/
noncomputable def simpRoundE [Fintype ι] (P T : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ)
    (sstar : ℕ) (x : E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c, simpClientIterE P T gc g lr x c sstar

/-- The client-averaged accumulated gradient difference of the simplified round. -/
noncomputable def simpDrift [Fintype ι] (P T : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ)
    (sstar : ℕ) (x : E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c, ∑ j ∈ range sstar,
    (gc c (simpClientIterE P T gc g lr x c j) - gc c x)

/-- If `∇ℒ` is the client average, the correction terms cancel in the aggregation:
`x⋆ = x - s⋆ λ Π ∇ℒ(x) - λ Π w`. -/
lemma simpRoundE_eq [Fintype ι] [Nonempty ι] (P T : E →L[ℝ] E) (gc : ι → E → E) (g : E → E)
    (lr : ℝ) (sstar : ℕ) (x : E) (hg : g x = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c x) :
    simpRoundE P T gc g lr sstar x =
      x - ((sstar : ℝ) * lr) • P (g x) - lr • P (simpDrift P T gc g lr sstar x) := by
  have hC : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hzero : ∑ c, (gc c x - g x) = 0 := by
    rw [sum_sub_distrib, sum_const, card_univ, ← Nat.cast_smul_eq_nsmul ℝ, hg, smul_smul,
      mul_inv_cancel₀ hC, one_smul, sub_self]
  have hP0 : ∑ c, P (gc c x - g x) = 0 := by rw [← map_sum, hzero, map_zero]
  have hT0 : ∑ c, T (gc c x - g x) = 0 := by rw [← map_sum, hzero, map_zero]
  have e : ∑ c, simpClientIterE P T gc g lr x c sstar = ∑ c, (x - ((sstar : ℝ) * lr) • P (g x) -
      lr • ∑ j ∈ range sstar, P (gc c (simpClientIterE P T gc g lr x c j) - gc c x) -
      ((sstar : ℝ) * lr) • (P (gc c x - g x) - T (gc c x - g x))) :=
    sum_congr rfl fun c _ => simpClientIterE_eq P T gc g lr x c sstar
  rw [simpRoundE, e, simpDrift, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, sum_const,
    sum_const, card_univ, ← smul_sum, ← smul_sum, sum_sub_distrib, hP0, hT0, map_smul, map_sum]
  simp_rw [map_sum]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
  match_scalars <;> field_simp

/-- Drift of the simplified client iterates: if the augmented block `(Π - Π₀) ∇ℒ_c` stays below
`δ ‖Π ∇ℒ(x)‖` along the iterates, then `‖z^s - x‖ ≤ s λ (1 + λ β)^s (1 + δ) ‖Π ∇ℒ(x)‖`. -/
lemma norm_simpClientIterE_sub_le (hT : IsOrthProj T) (hTP : ∀ v, T (P v) = T v)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {δ : ℝ}
    (hδ : 0 ≤ δ) (x : E) (c : ι) {sstar : ℕ}
    (hblock : ∀ s < sstar, ‖P (gc c (simpClientIterE P T gc g lr x c s)) -
      T (gc c (simpClientIterE P T gc g lr x c s))‖ ≤ δ * ‖P (g x)‖)
    {s : ℕ} (hs : s ≤ sstar) :
    ‖simpClientIterE P T gc g lr x c s - x‖ ≤
      s * lr * (1 + lr * β) ^ s * ((1 + δ) * ‖P (g x)‖) := by
  induction s with
  | zero => simp [simpClientIterE]
  | succ s ih =>
    have ih' := ih (by omega)
    set z := simpClientIterE P T gc g lr x c s
    set a := ‖P (g x)‖
    have h1 : simpClientIterE P T gc g lr x c (s + 1) - x =
        (z - x) - lr • T (gc c z - gc c x) - lr • (T (g x) + (P (gc c z) - T (gc c z))) := by
      rw [simpClientIterE_succ, map_sub, map_sub]
      module
    have h2 : ‖T (gc c z - gc c x)‖ ≤ β * ‖z - x‖ := (hT.norm_le _).trans (hgc c z x)
    have h3 : ‖T (g x) + (P (gc c z) - T (gc c z))‖ ≤ (1 + δ) * a := by
      have h4 : ‖T (g x)‖ ≤ a := by rw [← hTP]; exact hT.norm_le _
      have h5 := hblock s (by omega)
      calc _ ≤ ‖T (g x)‖ + ‖P (gc c z) - T (gc c z)‖ := norm_add_le _ _
        _ ≤ a + δ * a := add_le_add h4 h5
        _ = _ := by ring
    have ha : 0 ≤ (1 + δ) * a := by positivity
    have hq : 1 ≤ (1 + lr * β) ^ (s + 1) := one_le_pow₀ (by nlinarith [mul_nonneg hlr hβ])
    have hb : 0 ≤ 1 + lr * β := by nlinarith [mul_nonneg hlr hβ]
    rw [h1]
    calc ‖(z - x) - lr • T (gc c z - gc c x) - lr • (T (g x) + (P (gc c z) - T (gc c z)))‖
        ≤ ‖z - x‖ + lr * (β * ‖z - x‖) + lr * ((1 + δ) * a) := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add le_rfl ?_)) ?_)
          · rw [norm_smul, Real.norm_of_nonneg hlr]; exact mul_le_mul_of_nonneg_left h2 hlr
          · rw [norm_smul, Real.norm_of_nonneg hlr]; exact mul_le_mul_of_nonneg_left h3 hlr
      _ = (1 + lr * β) * ‖z - x‖ + lr * ((1 + δ) * a) := by ring
      _ ≤ (1 + lr * β) * (s * lr * (1 + lr * β) ^ s * ((1 + δ) * a)) + lr * ((1 + δ) * a) := by
          gcongr
      _ ≤ ((s + 1 : ℕ) : ℝ) * lr * (1 + lr * β) ^ (s + 1) * ((1 + δ) * a) := by
          have ha' : 0 ≤ lr * ((1 + δ) * a) := mul_nonneg hlr ha
          have := mul_le_mul_of_nonneg_left hq ha'
          rw [pow_succ] at this ⊢
          push_cast
          nlinarith

/-- A step `x - A Π ∇ℒ(x) - λ Π w` with a perturbation `λ ‖w‖ ≤ y β A² ‖Π ∇ℒ(x)‖` decreases the loss
by `A (1 - (y + (1 + y)²/2) A β) ‖Π ∇ℒ(x)‖²` (the estimate behind Thm 8 of arXiv 2406.17887, with
the factor `y` kept free). -/
theorem loss_perturbedStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) (hβ : 0 ≤ β) {A y : ℝ}
    (hA0 : 0 ≤ A) (hy : 0 ≤ y) (hβA : β * A ≤ 1) (hlr : 0 ≤ lr) (x w : E)
    (hw : lr * ‖w‖ ≤ y * β * A ^ 2 * ‖P (g x)‖) :
    ℒ (x - A • P (g x) - lr • P w) ≤
      ℒ x - A * (1 - (y + (1 + y) ^ 2 / 2) * A * β) * ‖P (g x)‖ ^ 2 := by
  set a := ‖P (g x)‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hd := descent_lemma hℒ hg x (x - A • P (g x) - lr • P w)
  have hdx : x - A • P (g x) - lr • P w - x = -(A • P (g x) + lr • P w) := by abel
  rw [hdx, inner_neg_right, inner_add_right, inner_smul_right, inner_smul_right, norm_neg] at hd
  have h1 : ⟪g x, P (g x)⟫ = a ^ 2 := by rw [real_inner_comm, hP.inner_self_apply]
  have h2 : -(lr * ⟪g x, P w⟫) ≤ lr * (a * ‖w‖) := by
    rw [← hP.symm]
    have h := abs_real_inner_le_norm (P (g x)) w
    have h' := neg_abs_le ⟪P (g x), w⟫
    nlinarith
  have h3 : ‖A • P (g x) + lr • P w‖ ≤ A * a + lr * ‖w‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg hA0]
    · rw [norm_smul, Real.norm_of_nonneg hlr]
      exact mul_le_mul_of_nonneg_left (hP.norm_le w) hlr
  have hω0 : 0 ≤ lr * ‖w‖ := mul_nonneg hlr (norm_nonneg _)
  have h4 : A * a + lr * ‖w‖ ≤ (1 + y) * (A * a) := by
    have : y * β * A ^ 2 * a ≤ y * (A * a) := by
      have := mul_le_mul_of_nonneg_left hβA (mul_nonneg hy (mul_nonneg hA0 ha0))
      nlinarith
    nlinarith
  have h5 : ‖A • P (g x) + lr • P w‖ ^ 2 ≤ (1 + y) ^ 2 * (A * a) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h3.trans h4) 2
  have h6 : a * (lr * ‖w‖) ≤ y * β * A ^ 2 * a ^ 2 := by
    have := mul_le_mul_of_nonneg_left hw ha0
    nlinarith
  have h7 : β / 2 * ‖A • P (g x) + lr • P w‖ ^ 2 ≤ β / 2 * ((1 + y) ^ 2 * (A * a) ^ 2) :=
    mul_le_mul_of_nonneg_left h5 (by linarith)
  rw [h1] at hd
  nlinarith

/-- `(1 + λ β)^s ≤ e` for `s ≤ s⋆` and `λ β s⋆ ≤ 1`. -/
private lemma one_add_pow_le_exp (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {s sstar : ℕ}
    (hs : lr * β * sstar ≤ 1) (hss : s ≤ sstar) : (1 + lr * β) ^ s ≤ Real.exp 1 := by
  calc (1 + lr * β) ^ s ≤ Real.exp (lr * β) ^ s :=
        pow_le_pow_left₀ (by nlinarith [mul_nonneg hlr hβ])
          (by linarith [Real.add_one_le_exp (lr * β)]) s
    _ = Real.exp (s * (lr * β)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp 1 := by
        refine Real.exp_le_exp.2 ?_
        have : (s : ℝ) ≤ sstar := by exact_mod_cast hss
        nlinarith [mul_nonneg hlr hβ]

/-- The constant of the simplified round: `κ(δ) = y + (1 + y)²/2` with `y = e (1 + δ)`. -/
noncomputable def kappa (δ : ℝ) : ℝ :=
  Real.exp 1 * (1 + δ) + (1 + Real.exp 1 * (1 + δ)) ^ 2 / 2

/-- For `δ ≤ 1/6` the constant `κ(δ)` stays below the constant `12` of the full correction. -/
lemma kappa_le_twelve {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 6) : kappa δ ≤ 12 := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hy : Real.exp 1 * (1 + δ) ≤ 3.18 := by nlinarith
  have hy0 : 0 ≤ Real.exp 1 * (1 + δ) := by positivity
  rw [kappa]
  nlinarith

/-- **Descent of the aggregated round with simplified variance correction**, abstract form.  If
the augmented block `(Π - Π₀) ∇ℒ_c` stays below `δ ‖Π ∇ℒ(x)‖` along the client iterates, then
`ℒ(x⋆) ≤ ℒ(x) - s⋆ λ (1 - κ(δ) s⋆ λ β) ‖Π ∇ℒ(x)‖²`.  This is the corrected form of Thm 4 of
arXiv 2406.17887 (see `theorem4_corrected`). -/
theorem loss_simpRoundE_le [Fintype ι] [Nonempty ι] (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hT : IsOrthProj T) (hTP : ∀ v, T (P v) = T v) (hβ : 0 ≤ β) (hlr : 0 ≤ lr)
    {δ : ℝ} (hδ : 0 ≤ δ) {sstar : ℕ} (hs : lr * β * sstar ≤ 1) (x : E)
    (havg : g x = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gc c x)
    (hblock : ∀ c, ∀ s < sstar, ‖P (gc c (simpClientIterE P T gc g lr x c s)) -
      T (gc c (simpClientIterE P T gc g lr x c s))‖ ≤ δ * ‖P (g x)‖) :
    ℒ (simpRoundE P T gc g lr sstar x) ≤
      ℒ x - sstar * lr * (1 - kappa δ * (sstar * lr) * β) * ‖P (g x)‖ ^ 2 := by
  set A : ℝ := sstar * lr with hA
  set a := ‖P (g x)‖ with ha
  set w := simpDrift P T gc g lr sstar x with hwdef
  have hA0 : 0 ≤ A := by positivity
  have ha0 : 0 ≤ a := norm_nonneg _
  have hβA : β * A ≤ 1 := by rw [hA]; linarith
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  set d := β * (Real.exp 1 * A * ((1 + δ) * a)) with hd
  have hterm : ∀ c, ∀ j ∈ range sstar,
      ‖gc c (simpClientIterE P T gc g lr x c j) - gc c x‖ ≤ d := by
    intro c j hj
    have hj' := (mem_range.1 hj).le
    refine (hgc c _ _).trans (mul_le_mul_of_nonneg_left ?_ hβ)
    have h1 := norm_simpClientIterE_sub_le hT hTP hgc hβ hlr hδ x c (hblock c) hj'
    have h2 := one_add_pow_le_exp hβ hlr hs hj'
    have hjr : (j : ℝ) ≤ sstar := by exact_mod_cast hj'
    have hb : 0 ≤ (1 + δ) * a := by positivity
    calc _ ≤ j * lr * (1 + lr * β) ^ j * ((1 + δ) * a) := h1
      _ = (1 + lr * β) ^ j * (j * lr * ((1 + δ) * a)) := by ring
      _ ≤ Real.exp 1 * (sstar * lr * ((1 + δ) * a)) := by gcongr
      _ = _ := by rw [hA]; ring
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hwb : ‖w‖ ≤ sstar * d := by
    rw [hwdef, simpDrift, norm_smul, norm_inv, Real.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ c, ∑ j ∈ range sstar,
          (gc c (simpClientIterE P T gc g lr x c j) - gc c x)‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _c : ι, ∑ _j ∈ range sstar, d := by
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum fun c _ =>
            (norm_sum_le _ _).trans (sum_le_sum (hterm c)))
      _ = sstar * d := by
          rw [sum_const, sum_const, card_range, card_univ, nsmul_eq_mul, nsmul_eq_mul]
          field_simp
  have hw : lr * ‖w‖ ≤ (Real.exp 1 * (1 + δ)) * β * A ^ 2 * a := by
    refine (mul_le_mul_of_nonneg_left hwb hlr).trans (le_of_eq ?_)
    rw [hd, hA]; ring
  have hstep := loss_perturbedStep_le hℒ hg hP hβ hA0 (by positivity) hβA hlr x w hw
  have e : simpRoundE P T gc g lr sstar x = x - A • P (g x) - lr • P w :=
    simpRoundE_eq P T gc g lr sstar x havg
  rw [e]
  have hk : kappa δ = Real.exp 1 * (1 + δ) + (1 + Real.exp 1 * (1 + δ)) ^ 2 / 2 := rfl
  rw [hk]
  exact hstep

end Abstract

/-! ### Gradients of factorized losses -/

section Matrix

open scoped LeanDLRA.Frobenius

/-- Chain rule for gradients along a continuous linear map. -/
lemma hasGradientAt_comp_clm {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    {f : Y → ℝ} {G : Y} (A : X →L[ℝ] Y) {x : X} (h : HasGradientAt f G (A x)) {G' : X}
    (hadj : ∀ D, ⟪G, A D⟫ = ⟪G', D⟫) : HasGradientAt (fun y => f (A y)) G' x := by
  have h1 := h.hasFDerivAt.comp x A.hasFDerivAt
  have e : InnerProductSpace.toDual ℝ X G' = (InnerProductSpace.toDual ℝ Y G).comp A := by
    ext D
    simp [hadj]
  rw [hasGradientAt_iff_hasFDerivAt, e]
  exact h1

variable {m n k l ι : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

/-- The coefficient gradient `∇_S̃ f(Ũ S̃ Ṽᵀ)`: the gradient of `S ↦ f(Ũ S Ṽᵀ)`. -/
noncomputable def coeffGrad (Ut : Matrix m k ℝ) (Vt : Matrix n l ℝ) (f : Matrix m n ℝ → ℝ)
    (S : Matrix k l ℝ) : Matrix k l ℝ :=
  gradient (fun S' => f (Ut * S' * Vtᵀ)) S

/-- The chain rule for the coefficients used throughout arXiv 2406.17887 (the projected gradient in
Appendix G.1): `∇_S̃ f(Ũ S̃ Ṽᵀ) = Ũᵀ ∇f(Ũ S̃ Ṽᵀ) Ṽ`; no orthonormality is needed. -/
theorem coeffGrad_eq {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ} {f : Matrix m n ℝ → ℝ}
    {S : Matrix k l ℝ} (hf : DifferentiableAt ℝ f (Ut * S * Vtᵀ)) :
    coeffGrad Ut Vt f S = Utᵀ * gradient f (Ut * S * Vtᵀ) * Vt := by
  have h : HasGradientAt (fun S' => f (Ut * S' * Vtᵀ))
      (Utᵀ * gradient f (Ut * S * Vtᵀ) * Vt) S := by
    refine hasGradientAt_comp_clm
      ((Frobenius.rightMulCLM Vtᵀ).comp (Frobenius.leftMulCLM Ut)) hf.hasGradientAt ?_
    intro D
    change ⟪gradient f (Ut * S * Vtᵀ), Ut * D * Vtᵀ⟫ = ⟪Utᵀ * gradient f (Ut * S * Vtᵀ) * Vt, D⟫
    rw [Frobenius.inner_mul_right', Matrix.transpose_transpose, Frobenius.inner_mul_left',
      Matrix.mul_assoc Utᵀ]
  exact h.gradient

/-- The `L`-smooth losses of arXiv 2406.17887 (`L`-Lipschitz gradient, the property used in its
Lemma 4). -/
structure IsLSmooth (f : Matrix m n ℝ → ℝ) (L : ℝ) : Prop where
  differentiable : Differentiable ℝ f
  lipschitz : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- The global loss `ℒ = (1/C) ∑_c ℒ_c`, eq. (1) of arXiv 2406.17887. -/
noncomputable def avgLoss [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) : Matrix m n ℝ → ℝ :=
  fun W => (Fintype.card ι : ℝ)⁻¹ * ∑ c, ℒc c W

lemma hasGradientAt_avgLoss [Fintype ι] {ℒc : ι → Matrix m n ℝ → ℝ} {W : Matrix m n ℝ}
    (h : ∀ c, DifferentiableAt ℝ (ℒc c) W) :
    HasGradientAt (avgLoss ℒc) ((Fintype.card ι : ℝ)⁻¹ • ∑ c, gradient (ℒc c) W) W := by
  have h1 := (HasFDerivAt.fun_sum (u := univ) fun c _ => (h c).hasGradientAt.hasFDerivAt).const_mul
    (Fintype.card ι : ℝ)⁻¹
  rw [hasGradientAt_iff_hasFDerivAt, map_smul, map_sum]
  exact h1

lemma gradient_avgLoss [Fintype ι] {ℒc : ι → Matrix m n ℝ → ℝ} {W : Matrix m n ℝ}
    (h : ∀ c, DifferentiableAt ℝ (ℒc c) W) :
    gradient (avgLoss ℒc) W = (Fintype.card ι : ℝ)⁻¹ • ∑ c, gradient (ℒc c) W :=
  (hasGradientAt_avgLoss h).gradient

/-- The average of `L`-smooth client losses is `L`-smooth (arXiv 2406.17887, §3.2, assumes this
separately). -/
theorem IsLSmooth.avgLoss [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ} {L : ℝ}
    (h : ∀ c, IsLSmooth (ℒc c) L) : IsLSmooth (avgLoss ℒc) L where
  differentiable W := (hasGradientAt_avgLoss fun c => (h c).differentiable W).differentiableAt
  lipschitz x y := by
    have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
    rw [gradient_avgLoss fun c => (h c).differentiable x,
      gradient_avgLoss fun c => (h c).differentiable y, ← smul_sub, ← sum_sub_distrib, norm_smul,
      norm_inv, Real.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ c, (gradient (ℒc c) x - gradient (ℒc c) y)‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _c : ι, (L * ‖x - y‖) := by
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum fun c _ => (h c).lipschitz x y)
      _ = L * ‖x - y‖ := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          field_simp

/-! ### Augmented bases: Lemmas 1, 2 and 7 of the paper -/

section Augmentation

variable {r a b : Type*}

/-- The block form of the orthonormality of the augmented basis `Ũ = [U | Ū]`. -/
lemma blocks_of_orthonormal [DecidableEq r] [DecidableEq a] {U : Matrix m r ℝ}
    {Ubar : Matrix m a ℝ}
    (h : (Matrix.fromCols U Ubar)ᵀ * Matrix.fromCols U Ubar = 1) :
    Uᵀ * U = 1 ∧ Uᵀ * Ubar = 0 ∧ Ubarᵀ * U = 0 ∧ Ubarᵀ * Ubar = 1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj] at h
  exact h

/-- **Lemma 1 of arXiv 2406.17887**: the coefficients projected onto the augmented bases are
`Ũᵀ U S Vᵀ Ṽ = [S 0; 0 0]`.  (Stated for arbitrary rectangular `S` and any orthonormal extension
`Ũ = [U | Ū]`, `Ṽ = [V | V̄]`.) -/
theorem lemma1_augmented_coeff [Fintype r] [DecidableEq r] [DecidableEq a] [DecidableEq b]
    {U : Matrix m r ℝ} {V : Matrix n r ℝ} {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ}
    (hU : (Matrix.fromCols U Ubar)ᵀ * Matrix.fromCols U Ubar = 1)
    (hV : (Matrix.fromCols V Vbar)ᵀ * Matrix.fromCols V Vbar = 1) (S : Matrix r r ℝ) :
    (Matrix.fromCols U Ubar)ᵀ * (U * S * Vᵀ) * Matrix.fromCols V Vbar =
      Matrix.fromBlocks S 0 0 0 := by
  obtain ⟨h1, -, h3, -⟩ := blocks_of_orthonormal hU
  obtain ⟨h1', h2', -, -⟩ := blocks_of_orthonormal hV
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  have e1 : Uᵀ * (U * S * Vᵀ) = S * Vᵀ := by
    rw [Matrix.mul_assoc U, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e2 : Ubarᵀ * (U * S * Vᵀ) = 0 := by
    rw [Matrix.mul_assoc U, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
  rw [e1, e2, Matrix.mul_assoc, Matrix.mul_assoc, h1', h2', Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.zero_mul]

omit [Fintype m] [Fintype n] in
/-- **Lemma 7 of arXiv 2406.17887** (without any orthonormality): `Ũ [S 0; 0 0] Ṽᵀ = U S Vᵀ`, so
augmentation does not change the weights or the loss. -/
theorem lemma7_augmented_weights [Fintype r] [Fintype a] [Fintype b] {U : Matrix m r ℝ}
    {V : Matrix n r ℝ} {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ} (S : Matrix r r ℝ) :
    Matrix.fromCols U Ubar * (Matrix.fromBlocks S 0 0 0 : Matrix (r ⊕ a) (r ⊕ b) ℝ) *
      (Matrix.fromCols V Vbar)ᵀ = U * S * Vᵀ := by
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  simp

omit [Fintype m] in
/-- Columns of a product are combinations of the columns of the left factor. -/
private lemma colSpan_mul_le {p q : Type*} [Fintype p] (A : Matrix m p ℝ) (M : Matrix p q ℝ) :
    colSpan (A * M) ≤ colSpan A := by
  rw [colSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h : WithLp.toLp 2 ((A * M).col j) = ∑ i, M i j • WithLp.toLp 2 (A.col i) := by
    ext x
    simp [Matrix.mul_apply, mul_comm]
  change WithLp.toLp 2 ((A * M).col j) ∈ _
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (toLp_col_mem_colSpan A i)

omit [Fintype m] in
/-- Replacing `G` by `U₀ Y - λ G` (`λ ≠ 0`) does not change `span[U₀ | ·]`. -/
private lemma colSpan_fromCols_sub_smul {p : Type*} [Fintype p]
    (U₀ : Matrix m p ℝ) (G : Matrix m p ℝ) (Y : Matrix p p ℝ) {lr : ℝ} (hlr : lr ≠ 0) :
    colSpan (Matrix.fromCols U₀ (U₀ * Y - lr • G)) = colSpan (Matrix.fromCols U₀ G) := by
  classical
  apply le_antisymm
  · have e : Matrix.fromCols U₀ (U₀ * Y - lr • G) = Matrix.fromCols U₀ G *
        (Matrix.fromBlocks 1 Y 0 (-lr • 1) : Matrix (p ⊕ p) (p ⊕ p) ℝ) := by
      rw [Matrix.fromCols_mul_fromBlocks]
      simp [sub_eq_add_neg]
    rw [e]
    exact colSpan_mul_le _ _
  · have e : Matrix.fromCols U₀ G = Matrix.fromCols U₀ (U₀ * Y - lr • G) *
        (Matrix.fromBlocks 1 (lr⁻¹ • Y) 0 (-lr⁻¹ • 1) : Matrix (p ⊕ p) (p ⊕ p) ℝ) := by
      rw [Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.mul_smul]
      congr 1
      rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hlr, one_smul]
      abel
    rw [e]
    exact colSpan_mul_le _ _

/-- **Lemma 2 of arXiv 2406.17887, `K` part**: for invertible `S₀`, `λ ≠ 0` and `K(t₁) = K(0) -
λ ∇_K ℒ(K(0) V₀ᵀ)`, `K(0) = U₀ S₀`, one has `span[U₀ | K(t₁)] = span[U₀ | ∇_U ℒ(U₀ S₀ V₀ᵀ)]`.
Both partial gradients are the actual gradients of `K ↦ ℒ(K V₀ᵀ)` and `U ↦ ℒ(U S₀ V₀ᵀ)`; the chain
rule `∇_K ℒ = ∇ℒ V₀`, `∇_U ℒ = ∇ℒ V₀ S₀ᵀ` is proved here, and the core span identity is
`fedDLRT_span_eq`.  The proof in the paper derives `∇_K ℒ = ∇ℒ V₀` from the continuous `K`
equation; orthonormality of `U₀, V₀` is not needed. -/
theorem lemma2_K {r : ℕ} {ℒ : Matrix m n ℝ → ℝ} (U₀ : Matrix m (Fin r) ℝ)
    {S₀ : Matrix (Fin r) (Fin r) ℝ} (V₀ : Matrix n (Fin r) ℝ)
    (hℒ : DifferentiableAt ℝ ℒ (U₀ * S₀ * V₀ᵀ)) (hS : IsUnit S₀.det) {lr : ℝ} (hlr : lr ≠ 0) :
    colSpan (Matrix.fromCols U₀
        (U₀ * S₀ - lr • gradient (fun K : Matrix m (Fin r) ℝ => ℒ (K * V₀ᵀ)) (U₀ * S₀))) =
      colSpan (Matrix.fromCols U₀
        (gradient (fun U : Matrix m (Fin r) ℝ => ℒ (U * S₀ * V₀ᵀ)) U₀)) := by
  set G := gradient ℒ (U₀ * S₀ * V₀ᵀ) with hG
  have hK : gradient (fun K : Matrix m (Fin r) ℝ => ℒ (K * V₀ᵀ)) (U₀ * S₀) = G * V₀ := by
    refine (hasGradientAt_comp_clm (Frobenius.rightMulCLM V₀ᵀ) hℒ.hasGradientAt ?_).gradient
    intro D
    change ⟪G, D * V₀ᵀ⟫ = ⟪G * V₀, D⟫
    rw [Frobenius.inner_mul_right', Matrix.transpose_transpose]
  have hU : gradient (fun U : Matrix m (Fin r) ℝ => ℒ (U * S₀ * V₀ᵀ)) U₀ = G * V₀ * S₀ᵀ := by
    have hℒ' : DifferentiableAt ℝ ℒ
        ((Frobenius.rightMulCLM (S₀ * V₀ᵀ) : Matrix m (Fin r) ℝ →L[ℝ] Matrix m n ℝ) U₀) := by
      simpa [Matrix.mul_assoc] using hℒ
    have h := (hasGradientAt_comp_clm (Frobenius.rightMulCLM (S₀ * V₀ᵀ)) hℒ'.hasGradientAt
      (G' := G * V₀ * S₀ᵀ) ?_).gradient
    · simpa [Matrix.mul_assoc] using h
    · intro D
      have e : gradient ℒ ((Frobenius.rightMulCLM (S₀ * V₀ᵀ) :
          Matrix m (Fin r) ℝ →L[ℝ] Matrix m n ℝ) U₀) = G := by
        simp [hG, Matrix.mul_assoc]
      rw [e, Frobenius.rightMulCLM_apply, Frobenius.inner_mul_right', Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hK, hU, colSpan_fromCols_sub_smul U₀ (G * V₀) S₀ hlr]
  exact (OpenProblems.TensorNetworks.fedDLRT_span_eq U₀ G V₀ hS).symm

/-- **Lemma 2 of arXiv 2406.17887, `L` part**: for invertible `S₀`, `λ ≠ 0` and `L(t₁) = L(0) -
λ ∇_L ℒ(U₀ L(0)ᵀ)`, `L(0) = V₀ S₀ᵀ`, one has `span[V₀ | L(t₁)] = span[V₀ | ∇_V ℒ(U₀ S₀ V₀ᵀ)]`. -/
theorem lemma2_L {r : ℕ} {ℒ : Matrix m n ℝ → ℝ} (U₀ : Matrix m (Fin r) ℝ)
    {S₀ : Matrix (Fin r) (Fin r) ℝ} (V₀ : Matrix n (Fin r) ℝ)
    (hℒ : DifferentiableAt ℝ ℒ (U₀ * S₀ * V₀ᵀ)) (hS : IsUnit S₀.det) {lr : ℝ} (hlr : lr ≠ 0) :
    colSpan (Matrix.fromCols V₀
        (V₀ * S₀ᵀ - lr • gradient (fun Λ : Matrix n (Fin r) ℝ => ℒ (U₀ * Λᵀ)) (V₀ * S₀ᵀ))) =
      colSpan (Matrix.fromCols V₀
        (gradient (fun V : Matrix n (Fin r) ℝ => ℒ (U₀ * S₀ * Vᵀ)) V₀)) := by
  set G := gradient ℒ (U₀ * S₀ * V₀ᵀ) with hG
  have hW : U₀ * (V₀ * S₀ᵀ)ᵀ = U₀ * S₀ * V₀ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hL : gradient (fun Λ : Matrix n (Fin r) ℝ => ℒ (U₀ * Λᵀ)) (V₀ * S₀ᵀ) = Gᵀ * U₀ := by
    have hℒ' : DifferentiableAt ℝ ℒ ((Frobenius.leftMulCLM U₀).comp Frobenius.transposeCLM
        (V₀ * S₀ᵀ)) := by
      change DifferentiableAt ℝ ℒ (U₀ * (V₀ * S₀ᵀ)ᵀ)
      rwa [hW]
    refine (hasGradientAt_comp_clm ((Frobenius.leftMulCLM U₀).comp Frobenius.transposeCLM)
      hℒ'.hasGradientAt ?_).gradient
    intro D
    change ⟪gradient ℒ (U₀ * (V₀ * S₀ᵀ)ᵀ), U₀ * Dᵀ⟫ = ⟪Gᵀ * U₀, D⟫
    rw [hW, ← hG, Frobenius.inner_mul_left', ← Frobenius.inner_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hV : gradient (fun V : Matrix n (Fin r) ℝ => ℒ (U₀ * S₀ * Vᵀ)) V₀ = Gᵀ * U₀ * S₀ := by
    have hℒ' : DifferentiableAt ℝ ℒ ((Frobenius.leftMulCLM (U₀ * S₀)).comp Frobenius.transposeCLM
        V₀) := hℒ
    refine (hasGradientAt_comp_clm ((Frobenius.leftMulCLM (U₀ * S₀)).comp Frobenius.transposeCLM)
      hℒ'.hasGradientAt ?_).gradient
    intro D
    change ⟪gradient ℒ (U₀ * S₀ * V₀ᵀ), U₀ * S₀ * Dᵀ⟫ = ⟪Gᵀ * U₀ * S₀, D⟫
    rw [← hG, Frobenius.inner_mul_left', ← Frobenius.inner_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hS' : IsUnit S₀ᵀ.det := by rwa [Matrix.det_transpose]
  have h := OpenProblems.TensorNetworks.fedDLRT_span_eq V₀ Gᵀ U₀ hS'
  rw [Matrix.transpose_transpose] at h
  rw [hL, hV, colSpan_fromCols_sub_smul V₀ (Gᵀ * U₀) S₀ᵀ hlr]
  exact h.symm

end Augmentation

/-! ### The FeDLRT algorithm on factors -/

section Algorithm

/-- The Galerkin projector `Π = Ũ Ũᵀ (·) Ṽ Ṽᵀ`. -/
noncomputable def gal (Ut : Matrix m k ℝ) (Vt : Matrix n l ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  leftProj Ut * rightProj Vt

lemma gal_apply (Ut : Matrix m k ℝ) (Vt : Matrix n l ℝ) (X : Matrix m n ℝ) :
    gal Ut Vt X = Ut * (Utᵀ * X * Vt) * Vtᵀ :=
  leftProj_rightProj_apply Ut Vt X

/-- The variance correction `V_c = G_S̃ - G_S̃,c` of arXiv 2406.17887 (before eq. (8)):
`G_S̃,c = ∇_S̃ ℒ_c(Ũ S̃ Ṽᵀ)` and `G_S̃ = (1/C) ∑_c G_S̃,c`. -/
noncomputable def varCorr [Fintype ι] (Ut : Matrix m k ℝ) (Vt : Matrix n l ℝ)
    (ℒc : ι → Matrix m n ℝ → ℝ) (St : Matrix k l ℝ) (c : ι) : Matrix k l ℝ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c', coeffGrad Ut Vt (ℒc c') St - coeffGrad Ut Vt (ℒc c) St

/-- The variance-corrected client iteration, eq. (8) of arXiv 2406.17887:
`S̃_c^{s+1} = S̃_c^s - λ (∇_S̃ ℒ_c(Ũ S̃_c^s Ṽᵀ) + V_c)`, `S̃_c^0 = S̃`. -/
noncomputable def clientIter [Fintype ι] (Ut : Matrix m k ℝ) (Vt : Matrix n l ℝ)
    (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ) (St : Matrix k l ℝ) (c : ι) : ℕ → Matrix k l ℝ
  | 0 => St
  | s + 1 => clientIter Ut Vt ℒc lr St c s -
      lr • (coeffGrad Ut Vt (ℒc c) (clientIter Ut Vt ℒc lr St c s) + varCorr Ut Vt ℒc St c)

/-- The aggregated coefficients `S̃⋆ = (1/C) ∑_c S̃_c^{s⋆}`, eq. (10) of arXiv 2406.17887. -/
noncomputable def roundCoeff [Fintype ι] (Ut : Matrix m k ℝ) (Vt : Matrix n l ℝ)
    (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ) (sstar : ℕ) (St : Matrix k l ℝ) : Matrix k l ℝ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c, clientIter Ut Vt ℒc lr St c sstar

/-- `V_c` is the Galerkin projection of `∇ℒ - ∇ℒ_c` at `Ũ S̃ Ṽᵀ`. -/
lemma varCorr_eq [Fintype ι] {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ}
    {ℒc : ι → Matrix m n ℝ → ℝ} (hd : ∀ c, Differentiable ℝ (ℒc c)) (St : Matrix k l ℝ) (c : ι) :
    varCorr Ut Vt ℒc St c = Utᵀ * (gradient (avgLoss ℒc) (Ut * St * Vtᵀ) -
      gradient (ℒc c) (Ut * St * Vtᵀ)) * Vt := by
  rw [varCorr, gradient_avgLoss fun c => hd c _, Matrix.mul_sub, Matrix.sub_mul]
  simp_rw [coeffGrad_eq ((hd _) _)]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]

/-- In the weights, eq. (8) is the iteration `fedClientIter` of the library. -/
lemma mul_clientIter_mul [Fintype ι] {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ}
    {ℒc : ι → Matrix m n ℝ → ℝ} (hd : ∀ c, Differentiable ℝ (ℒc c)) (lr : ℝ)
    (St : Matrix k l ℝ) (c : ι) (s : ℕ) :
    Ut * clientIter Ut Vt ℒc lr St c s * Vtᵀ =
      fedClientIter (gal Ut Vt) (fun c => gradient (ℒc c)) (gradient (avgLoss ℒc)) lr
        (Ut * St * Vtᵀ) c s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [fedClientIter_succ, ← ih, clientIter, varCorr_eq hd, coeffGrad_eq ((hd c) _), gal_apply]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    abel_nf

/-- In the weights, eq. (10) is the round `fedRound` of the library. -/
lemma mul_roundCoeff_mul [Fintype ι] {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ}
    {ℒc : ι → Matrix m n ℝ → ℝ} (hd : ∀ c, Differentiable ℝ (ℒc c)) (lr : ℝ) (sstar : ℕ)
    (St : Matrix k l ℝ) :
    Ut * roundCoeff Ut Vt ℒc lr sstar St * Vtᵀ =
      fedRound (gal Ut Vt) (fun c => gradient (ℒc c)) (gradient (avgLoss ℒc)) lr sstar
        (Ut * St * Vtᵀ) := by
  rw [roundCoeff, fedRound, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [mul_clientIter_mul hd]

variable [DecidableEq k] [DecidableEq l]

lemma isOrthProj_gal {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ} (hU : Utᵀ * Ut = 1)
    (hV : Vtᵀ * Vt = 1) : IsOrthProj (gal Ut Vt) :=
  isOrthProj_leftProj_mul_rightProj hU hV

/-- `‖Ũ X Ṽᵀ‖ = ‖X‖` for orthonormal `Ũ, Ṽ`. -/
lemma norm_mul_mul_transpose {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ} (hU : Utᵀ * Ut = 1)
    (hV : Vtᵀ * Vt = 1) (X : Matrix k l ℝ) : ‖Ut * X * Vtᵀ‖ = ‖X‖ := by
  rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]

lemma norm_gal {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ} (hU : Utᵀ * Ut = 1)
    (hV : Vtᵀ * Vt = 1) (X : Matrix m n ℝ) : ‖gal Ut Vt X‖ = ‖Utᵀ * X * Vt‖ := by
  rw [gal_apply, norm_mul_mul_transpose hU hV]

/-- **Theorem 1 of arXiv 2406.17887 (coefficient drift of the clients)**: for all orthonormal `Ũ`,
`Ṽ`, every `S̃`, all clients `c` and all `s ≤ s⋆`,
`‖S̃_c^s - S̃‖ ≤ e s⋆ λ ‖∇_S̃ ℒ(Ũ S̃ Ṽᵀ)‖`.  The paper assumes `0 < λ ≤ 1/(L s⋆)` and `s < s⋆`; here
`0 ≤ λ`, `λ L s⋆ ≤ 1` and `s ≤ s⋆` suffice.  The smoothness of `ℒ` is derived from that of the
`ℒ_c`.  The core estimate in the weights is `norm_fedClientIter_sub_le_exp` of the library. -/
theorem theorem1_drift [Fintype ι] {Ut : Matrix m k ℝ} {Vt : Matrix n l ℝ} (hU : Utᵀ * Ut = 1)
    (hV : Vtᵀ * Vt = 1) {ℒc : ι → Matrix m n ℝ → ℝ} {L lr : ℝ}
    (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 ≤ L) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : lr * L * sstar ≤ 1) (St : Matrix k l ℝ) (c : ι) {s : ℕ} (hss : s ≤ sstar) :
    ‖clientIter Ut Vt ℒc lr St c s - St‖ ≤
      Real.exp 1 * (sstar * lr) * ‖coeffGrad Ut Vt (avgLoss ℒc) St‖ := by
  have hd := fun c => (hL c).differentiable
  have hdg : DifferentiableAt ℝ (avgLoss ℒc) (Ut * St * Vtᵀ) :=
    (hasGradientAt_avgLoss fun c => hd c _).differentiableAt
  have h := norm_fedClientIter_sub_le_exp (isOrthProj_gal hU hV) (gc := fun c => gradient (ℒc c))
    (fun c x y => (hL c).lipschitz x y) hL0 hlr hs (g := gradient (avgLoss ℒc))
    (Ut * St * Vtᵀ) c hss
  rw [← mul_clientIter_mul hd, norm_gal hU hV, ← coeffGrad_eq hdg, ← Matrix.sub_mul,
    ← Matrix.mul_sub, norm_mul_mul_transpose hU hV] at h
  refine h.trans ?_
  have : (s : ℝ) ≤ sstar := by exact_mod_cast hss
  have he := Real.exp_pos 1
  gcongr

/-- **Theorem 8 of arXiv 2406.17887 (loss descent before truncation)**: for orthonormal `Ũ`, `Ṽ`,
`ℒ(Ũ S̃⋆ Ṽᵀ) ≤ ℒ(Ũ S̃ Ṽᵀ) - s⋆ λ (1 - 12 s⋆ λ L) ‖∇_S̃ ℒ(Ũ S̃ Ṽᵀ)‖²`.  The paper assumes
`λ ≤ 1/(12 L s⋆)`; `λ L s⋆ ≤ 1` suffices.  The core estimate in the weights is `loss_fedRound_le` of
the library. -/
theorem theorem8_aggregate_descent [Fintype ι] [Nonempty ι] {Ut : Matrix m k ℝ}
    {Vt : Matrix n l ℝ} (hU : Utᵀ * Ut = 1) (hV : Vtᵀ * Vt = 1) {ℒc : ι → Matrix m n ℝ → ℝ}
    {L lr : ℝ} (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 ≤ L) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : lr * L * sstar ≤ 1) (St : Matrix k l ℝ) :
    avgLoss ℒc (Ut * roundCoeff Ut Vt ℒc lr sstar St * Vtᵀ) ≤ avgLoss ℒc (Ut * St * Vtᵀ) -
      sstar * lr * (1 - 12 * (sstar * lr) * L) * ‖coeffGrad Ut Vt (avgLoss ℒc) St‖ ^ 2 := by
  have hd := fun c => (hL c).differentiable
  have hg := IsLSmooth.avgLoss hL
  have h := loss_fedRound_le (ℒ := avgLoss ℒc) (g := gradient (avgLoss ℒc))
    (gc := fun c => gradient (ℒc c)) (P := gal Ut Vt)
    (hasFDerivAt_of_hasGradientAt fun x => (hg.differentiable x).hasGradientAt) hg.lipschitz
    (fun c x y => (hL c).lipschitz x y) (isOrthProj_gal hU hV) hL0 hlr hs (Ut * St * Vtᵀ)
  rw [← mul_roundCoeff_mul hd, norm_gal hU hV, ← coeffGrad_eq (hg.differentiable _)] at h
  exact h

/-- The compression step of Algorithm 1 of arXiv 2406.17887: `U' = Ũ P`, `V' = Ṽ Q` with orthonormal
`P, Q`, and `‖S̃⋆ - P S' Qᵀ‖ ≤ ϑ`.  The truncated SVD of the paper (`S' = Σ_{r₁}`, threshold
`‖[σ_{r₁+1}, …]‖ ≤ ϑ`) is the main instance; only the error bound is used. -/
def IsTruncation {q : Type*} [Fintype q] [DecidableEq q] (Ut : Matrix m k ℝ) (Vt : Matrix n l ℝ)
    (Sstar : Matrix k l ℝ) (ϑ : ℝ) (U' : Matrix m q ℝ) (S' : Matrix q q ℝ) (V' : Matrix n q ℝ) :
    Prop :=
  ∃ (P : Matrix k q ℝ) (Q : Matrix l q ℝ), Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧
    ‖Sstar - P * S' * Qᵀ‖ ≤ ϑ ∧ U' = Ut * P ∧ V' = Vt * Q

/-- The truncation error in the weights is the truncation error in the coefficients. -/
lemma IsTruncation.norm_sub_le {q : Type*} [Fintype q] [DecidableEq q] {Ut : Matrix m k ℝ}
    {Vt : Matrix n l ℝ} (hU : Utᵀ * Ut = 1) (hV : Vtᵀ * Vt = 1) {Sstar : Matrix k l ℝ} {ϑ : ℝ}
    {U' : Matrix m q ℝ} {S' : Matrix q q ℝ} {V' : Matrix n q ℝ}
    (h : IsTruncation Ut Vt Sstar ϑ U' S' V') : ‖U' * S' * V'ᵀ - Ut * Sstar * Vtᵀ‖ ≤ ϑ := by
  obtain ⟨P, Q, -, -, herr, rfl, rfl⟩ := h
  have e : Ut * P * S' * (Vt * Q)ᵀ - Ut * Sstar * Vtᵀ = Ut * (P * S' * Qᵀ - Sstar) * Vtᵀ := by
    rw [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  rw [e, norm_mul_mul_transpose hU hV, norm_sub_rev]
  exact herr

/-- A minimiser of a mean: if `c a_t ≤ u_t - u_{t+1} + e` for `t < T`, then
`a_t ≤ (u_0 - u_T)/(T c) + e/c` for some `t < T`. -/
private lemma exists_le_of_descent {u a : ℕ → ℝ} {c e : ℝ} (hc : 0 < c) {T : ℕ} (hT : 0 < T)
    (h : ∀ t < T, c * a t ≤ u t - u (t + 1) + e) :
    ∃ t < T, a t ≤ (u 0 - u T) / (T * c) + e / c := by
  refine exists_le_of_mul_sum_le hc hT ?_
  have h1 : c * ∑ t ∈ range T, a t ≤ ∑ t ∈ range T, ((u t - u (t + 1)) + e) := by
    rw [mul_sum]
    exact sum_le_sum fun t ht => h t (mem_range.1 ht)
  rw [sum_add_distrib, sum_range_sub', sum_const, card_range, nsmul_eq_mul] at h1
  exact h1

end Algorithm

/-! ### One iteration of Algorithm 1 and global convergence -/

section Rounds

variable {r a b q : Type*} [Fintype r] [Fintype a] [Fintype b] [Fintype q]

/-- The coefficient gradient in the paper's Theorems 2 and 3, `∇_S̃ ℒ(U S Vᵀ) = ∇_S̃ ℒ(Ũ S̃ Ṽᵀ)`, at
the augmented coefficients `S̃ = [S 0; 0 0]`. -/
noncomputable def gradS (f : Matrix m n ℝ → ℝ) (U : Matrix m r ℝ) (S : Matrix r r ℝ)
    (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ) (Vbar : Matrix n b ℝ) : Matrix (r ⊕ a) (r ⊕ b) ℝ :=
  coeffGrad (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) f (Matrix.fromBlocks S 0 0 0)

/-- The weights `W̃⋆ = Ũ S̃⋆ Ṽᵀ` after aggregation and before truncation. -/
noncomputable def preTruncWeights [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ) (sstar : ℕ)
    (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ)
    (Vbar : Matrix n b ℝ) : Matrix m n ℝ :=
  Matrix.fromCols U Ubar * roundCoeff (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) ℒc lr sstar
    (Matrix.fromBlocks S 0 0 0) * (Matrix.fromCols V Vbar)ᵀ

variable [DecidableEq r] [DecidableEq a] [DecidableEq b] [DecidableEq q]

/-- One iteration of Algorithm 1 of arXiv 2406.17887 (FeDLRT with full variance correction) from
`U S Vᵀ` to `U' S' V'ᵀ`: orthonormal augmented bases `Ũ = [U | Ū]`, `Ṽ = [V | V̄]`, `s⋆` variance
corrected client steps from `S̃ = [S 0; 0 0]`, averaging, and truncation with tolerance `ϑ`.  The
augmentation `Ū, V̄` may be any orthonormal extension (the paper's choice from the basis gradients
is one) and `S` need not have full rank: the convergence analysis uses neither. -/
structure IsFeDLRTRound [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr ϑ : ℝ) (sstar : ℕ)
    (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ)
    (Vbar : Matrix n b ℝ) (U' : Matrix m q ℝ) (S' : Matrix q q ℝ) (V' : Matrix n q ℝ) : Prop where
  orthU : (Matrix.fromCols U Ubar)ᵀ * Matrix.fromCols U Ubar = 1
  orthV : (Matrix.fromCols V Vbar)ᵀ * Matrix.fromCols V Vbar = 1
  trunc : IsTruncation (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar)
    (roundCoeff (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) ℒc lr sstar
      (Matrix.fromBlocks S 0 0 0)) ϑ U' S' V'

/-- **Theorem 2 of arXiv 2406.17887 (global loss descent), general form.**  For one iteration of
Algorithm 1, `L`-smooth client losses and `‖∇ℒ‖ ≤ G` on the segment between the weights before and
after truncation,
`ℒ(U' S' V'ᵀ) - ℒ(U S Vᵀ) ≤ -s⋆ λ (1 - 12 s⋆ λ L) ‖∇_S̃ ℒ(U S Vᵀ)‖² + G ϑ`.
Differences from the paper: the term `L ϑ` is replaced by `G ϑ`, since `L`-smoothness alone gives no
bound on `∇ℒ` (the paper's step (36) uses `‖F‖ ≤ L`; the literal claim is false, see
`theorem2_false_of_smooth_only`, and `theorem2_loss_descent'` is the paper's form under this extra
assumption); the restriction `λ ≤ 1/(12 L s⋆)` is relaxed to `λ L s⋆ ≤ 1`. -/
theorem theorem2_loss_descent [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ} {L lr ϑ G : ℝ}
    (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 ≤ L) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : lr * L * sstar ≤ 1) {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ} {U' : Matrix m q ℝ} {S' : Matrix q q ℝ}
    {V' : Matrix n q ℝ} (h : IsFeDLRTRound ℒc lr ϑ sstar U S V Ubar Vbar U' S' V')
    (hG : ∀ W ∈ segment ℝ (preTruncWeights ℒc lr sstar U S V Ubar Vbar) (U' * S' * V'ᵀ),
      ‖gradient (avgLoss ℒc) W‖ ≤ G) :
    avgLoss ℒc (U' * S' * V'ᵀ) - avgLoss ℒc (U * S * Vᵀ) ≤
      -(sstar * lr) * (1 - 12 * (sstar * lr) * L) * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2 +
        G * ϑ := by
  have hg := IsLSmooth.avgLoss hL
  have h8 := theorem8_aggregate_descent h.orthU h.orthV hL hL0 hlr hs
    (Matrix.fromBlocks S 0 0 0 : Matrix (r ⊕ a) (r ⊕ b) ℝ)
  rw [lemma7_augmented_weights] at h8
  have h8' : avgLoss ℒc (preTruncWeights ℒc lr sstar U S V Ubar Vbar) ≤ _ := h8
  have hn : ‖U' * S' * V'ᵀ - preTruncWeights ℒc lr sstar U S V Ubar Vbar‖ ≤ ϑ :=
    h.trunc.norm_sub_le h.orthU h.orthV
  have hen := abs_energy_sub_le
    (hasFDerivAt_of_hasGradientAt fun x => (hg.differentiable x).hasGradientAt) hG
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG _ (left_mem_segment ℝ _ _))
  have h3 := mul_le_mul_of_nonneg_left hn hG0
  have h4 := (abs_le.1 hen).2
  change avgLoss ℒc _ ≤ _ - _ * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2 at h8'
  linarith

/-- **Theorem 2 of arXiv 2406.17887, eq. (12), in the paper's form**, under the assumption
`‖∇ℒ‖ ≤ L` that its proof uses in step (36): with `0 < λ ≤ 1/(12 L s⋆)`,
`ℒ(U' S' V'ᵀ) - ℒ(U S Vᵀ) ≤ -s⋆ λ (1 - 12 s⋆ λ L) ‖∇_S̃ ℒ(U S Vᵀ)‖² + L ϑ`. -/
theorem theorem2_loss_descent' [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ} {L lr ϑ : ℝ}
    (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 < L) (hlr0 : 0 < lr) {sstar : ℕ} (hs0 : 0 < sstar)
    (hlr : lr ≤ 1 / (12 * L * sstar)) (hbd : ∀ W, ‖gradient (avgLoss ℒc) W‖ ≤ L)
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ} {U' : Matrix m q ℝ} {S' : Matrix q q ℝ}
    {V' : Matrix n q ℝ} (h : IsFeDLRTRound ℒc lr ϑ sstar U S V Ubar Vbar U' S' V') :
    avgLoss ℒc (U' * S' * V'ᵀ) - avgLoss ℒc (U * S * Vᵀ) ≤
      -(sstar * lr) * (1 - 12 * (sstar * lr) * L) * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2 +
        L * ϑ := by
  have hs0' : (0 : ℝ) < sstar := Nat.cast_pos.2 hs0
  have hpos : 0 < 12 * L * sstar := by positivity
  have h1 : lr * (12 * L * sstar) ≤ 1 := by
    rw [le_div_iff₀ hpos] at hlr
    exact hlr
  have hs : lr * L * sstar ≤ 1 := by nlinarith [mul_pos (mul_pos hlr0 hL0) hs0']
  exact theorem2_loss_descent hL hL0.le hlr0.le hs h fun W _ => hbd W

/-- **Theorem 2 of arXiv 2406.17887 under `L`-smoothness alone**: without a bound on `∇ℒ` the
truncation contributes `‖∇ℒ(W̃⋆)‖ ϑ + L ϑ²/2` (descent lemma) instead of the paper's `L ϑ`. -/
theorem theorem2_loss_descent_smooth [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    {L lr ϑ : ℝ} (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 ≤ L) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : lr * L * sstar ≤ 1) {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ} {U' : Matrix m q ℝ} {S' : Matrix q q ℝ}
    {V' : Matrix n q ℝ} (h : IsFeDLRTRound ℒc lr ϑ sstar U S V Ubar Vbar U' S' V') :
    avgLoss ℒc (U' * S' * V'ᵀ) - avgLoss ℒc (U * S * Vᵀ) ≤
      -(sstar * lr) * (1 - 12 * (sstar * lr) * L) * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2 +
        ‖gradient (avgLoss ℒc) (preTruncWeights ℒc lr sstar U S V Ubar Vbar)‖ * ϑ +
          L / 2 * ϑ ^ 2 := by
  have hg := IsLSmooth.avgLoss hL
  have h8 := theorem8_aggregate_descent h.orthU h.orthV hL hL0 hlr hs
    (Matrix.fromBlocks S 0 0 0 : Matrix (r ⊕ a) (r ⊕ b) ℝ)
  rw [lemma7_augmented_weights] at h8
  have h8' : avgLoss ℒc (preTruncWeights ℒc lr sstar U S V Ubar Vbar) ≤ _ := h8
  have hn : ‖U' * S' * V'ᵀ - preTruncWeights ℒc lr sstar U S V Ubar Vbar‖ ≤ ϑ :=
    h.trunc.norm_sub_le h.orthU h.orthV
  have hd := descent_lemma
    (hasFDerivAt_of_hasGradientAt fun x => (hg.differentiable x).hasGradientAt) hg.lipschitz
    (preTruncWeights ℒc lr sstar U S V Ubar Vbar) (U' * S' * V'ᵀ)
  have h1 := real_inner_le_norm (gradient (avgLoss ℒc)
    (preTruncWeights ℒc lr sstar U S V Ubar Vbar))
    (U' * S' * V'ᵀ - preTruncWeights ℒc lr sstar U S V Ubar Vbar)
  have h2 := mul_le_mul_of_nonneg_left hn
    (norm_nonneg (gradient (avgLoss ℒc) (preTruncWeights ℒc lr sstar U S V Ubar Vbar)))
  have h3 : ‖U' * S' * V'ᵀ - preTruncWeights ℒc lr sstar U S V Ubar Vbar‖ ^ 2 ≤ ϑ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ L / 2)
  change avgLoss ℒc _ ≤ _ - _ * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2 at h8'
  linarith

/-- **Theorem 3 of arXiv 2406.17887 (global convergence), general learning rate.**  For `T > 0`
iterations of Algorithm 1 with iteration-dependent ranks and augmentations, `L`-smooth client
losses, `‖∇ℒ‖ ≤ G` on the truncation segments and `c = s⋆ λ (1 - 12 s⋆ λ L) > 0`, some iteration
`t < T` satisfies `‖∇_S̃ ℒ(U^t S^t V^{t,ᵀ})‖² ≤ (ℒ(W⁰) - ℒ(W^T))/(T c) + G ϑ/c`.
(The iterations are numbered from `0`, not from `1`.)  The library contains the analogue in the
weights, `exists_fedGrad_sq_le`. -/
theorem theorem3_convergence_general [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    {L lr ϑ G : ℝ} (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 ≤ L) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hpos : 0 < sstar * lr * (1 - 12 * (sstar * lr) * L)) {rk ak bk : ℕ → ℕ}
    {U : ∀ t, Matrix m (Fin (rk t)) ℝ} {S : ∀ t, Matrix (Fin (rk t)) (Fin (rk t)) ℝ}
    {V : ∀ t, Matrix n (Fin (rk t)) ℝ} {Ubar : ∀ t, Matrix m (Fin (ak t)) ℝ}
    {Vbar : ∀ t, Matrix n (Fin (bk t)) ℝ} {T : ℕ} (hT : 0 < T)
    (h : ∀ t < T, IsFeDLRTRound ℒc lr ϑ sstar (U t) (S t) (V t) (Ubar t) (Vbar t) (U (t + 1))
      (S (t + 1)) (V (t + 1)))
    (hG : ∀ t < T, ∀ W ∈ segment ℝ
      (preTruncWeights ℒc lr sstar (U t) (S t) (V t) (Ubar t) (Vbar t))
      (U (t + 1) * S (t + 1) * (V (t + 1))ᵀ), ‖gradient (avgLoss ℒc) W‖ ≤ G) :
    ∃ t < T, ‖gradS (avgLoss ℒc) (U t) (S t) (V t) (Ubar t) (Vbar t)‖ ^ 2 ≤
      (avgLoss ℒc (U 0 * S 0 * (V 0)ᵀ) - avgLoss ℒc (U T * S T * (V T)ᵀ)) /
          (T * (sstar * lr * (1 - 12 * (sstar * lr) * L))) +
        G * ϑ / (sstar * lr * (1 - 12 * (sstar * lr) * L)) := by
  have hA0 : 0 ≤ (sstar : ℝ) * lr := by positivity
  have hs : lr * L * sstar ≤ 1 := by
    have h12 : 0 < 1 - 12 * (sstar * lr) * L := by
      by_contra hcon
      have := not_lt.1 hcon
      nlinarith
    nlinarith
  refine exists_le_of_descent (u := fun t => avgLoss ℒc (U t * S t * (V t)ᵀ)) hpos hT ?_
  intro t ht
  have := theorem2_loss_descent hL hL0 hlr hs (h t ht) (hG t ht)
  linarith

/-- **Theorem 3 of arXiv 2406.17887, eq. (13)**, at the learning rate `λ = 1/(24 L s⋆)` of its
proof: `min_{t<T} ‖∇_S̃ ℒ(U^t S^t V^{t,ᵀ})‖² ≤ 48 L/T (ℒ(W⁰) - ℒ(W^T)) + 48 L G ϑ`, the paper's
`48 L² ϑ` with one factor `L` read as the bound `G` of `∇ℒ` on the truncation segments (`G = L`
gives the paper's formula).  Differences from the paper: the paper states this for every
`λ ≤ 1/(12 L s⋆)`, which is false, see `theorem3_false_of_small_lr`; in fact `48` needs
`s⋆ λ L = 1/24` exactly, since `a (1 - 12 a) ≤ 1/48` with equality only at `a = 1/24`.  The
iterations are numbered from `0`. -/
theorem theorem3_convergence [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    {L lr ϑ G : ℝ} (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 < L) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hlr24 : sstar * lr * L = 1 / 24) {rk ak bk : ℕ → ℕ}
    {U : ∀ t, Matrix m (Fin (rk t)) ℝ} {S : ∀ t, Matrix (Fin (rk t)) (Fin (rk t)) ℝ}
    {V : ∀ t, Matrix n (Fin (rk t)) ℝ} {Ubar : ∀ t, Matrix m (Fin (ak t)) ℝ}
    {Vbar : ∀ t, Matrix n (Fin (bk t)) ℝ} {T : ℕ} (hT : 0 < T)
    (h : ∀ t < T, IsFeDLRTRound ℒc lr ϑ sstar (U t) (S t) (V t) (Ubar t) (Vbar t) (U (t + 1))
      (S (t + 1)) (V (t + 1)))
    (hG : ∀ t < T, ∀ W ∈ segment ℝ
      (preTruncWeights ℒc lr sstar (U t) (S t) (V t) (Ubar t) (Vbar t))
      (U (t + 1) * S (t + 1) * (V (t + 1))ᵀ), ‖gradient (avgLoss ℒc) W‖ ≤ G) :
    ∃ t < T, ‖gradS (avgLoss ℒc) (U t) (S t) (V t) (Ubar t) (Vbar t)‖ ^ 2 ≤
      48 * L / T * (avgLoss ℒc (U 0 * S 0 * (V 0)ᵀ) - avgLoss ℒc (U T * S T * (V T)ᵀ)) +
        48 * L * G * ϑ := by
  have hA : (sstar : ℝ) * lr = 1 / (24 * L) := by
    rw [eq_div_iff (by positivity)]; linarith
  have hc : (sstar : ℝ) * lr * (1 - 12 * (sstar * lr) * L) = 1 / (48 * L) := by
    rw [hA]; field_simp; ring
  obtain ⟨t, ht, hle⟩ := theorem3_convergence_general hL hL0.le hlr
    (by rw [hc]; positivity) hT h hG
  refine ⟨t, ht, hle.trans (le_of_eq ?_)⟩
  rw [hc]
  have : (0 : ℝ) < T := Nat.cast_pos.2 hT
  field_simp

end Rounds


/-! ### Simplified variance correction: the corrected Theorem 4 and Corollary 1 -/

section Simplified

/-- `‖P y - T y‖² = ‖P y‖² - ‖T y‖²` for orthogonal projectors with `T P = T`. -/
private lemma norm_sub_sq_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P T : E →L[ℝ] E} (hT : IsOrthProj T) (hTP : ∀ v, T (P v) = T v) (y : E) :
    ‖P y - T y‖ ^ 2 = ‖P y‖ ^ 2 - ‖T y‖ ^ 2 := by
  have h1 : ⟪P y, T y⟫ = ‖T y‖ ^ 2 := by
    rw [← hT.symm, hTP, ← hT.idem y, hT.symm, hT.idem, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, h1]
  ring

variable {r a b q : Type*} [Fintype r] [Fintype a] [Fintype b] [Fintype q]

/-- The simplified correction `V̌_c = [∇_S ℒ - ∇_S ℒ_c, 0; 0, 0]` at `U S Vᵀ`, eq. (9) of
arXiv 2406.17887. -/
noncomputable def simpVarCorr [Fintype ι] (U : Matrix m r ℝ) (V : Matrix n r ℝ)
    (ℒc : ι → Matrix m n ℝ → ℝ) (S : Matrix r r ℝ) (c : ι) : Matrix (r ⊕ a) (r ⊕ b) ℝ :=
  Matrix.fromBlocks (varCorr U V ℒc S c) 0 0 0

/-- The client iteration of Algorithm 5 of arXiv 2406.17887 (line 9 of Algorithm 2 with the
correction term `V̌_c`): `S̃_c^{s+1} = S̃_c^s - λ (∇_S̃ ℒ_c(Ũ S̃_c^s Ṽᵀ) + V̌_c)` from
`S̃ = [S 0; 0 0]`.  This agrees with eq. (45) of the paper; eq. (40) misprints the sign and the
factor `λ` of `V̌_c`. -/
noncomputable def simpClientIter [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ)
    (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ)
    (Vbar : Matrix n b ℝ) (c : ι) : ℕ → Matrix (r ⊕ a) (r ⊕ b) ℝ
  | 0 => Matrix.fromBlocks S 0 0 0
  | s + 1 => simpClientIter ℒc lr U S V Ubar Vbar c s -
      lr • (coeffGrad (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) (ℒc c)
        (simpClientIter ℒc lr U S V Ubar Vbar c s) + simpVarCorr U V ℒc S c)

/-- The aggregated coefficients of Algorithm 5. -/
noncomputable def simpRoundCoeff [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ) (sstar : ℕ)
    (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ)
    (Vbar : Matrix n b ℝ) : Matrix (r ⊕ a) (r ⊕ b) ℝ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ c, simpClientIter ℒc lr U S V Ubar Vbar c sstar

/-- The weights `Ũ S̃⋆ Ṽᵀ` of Algorithm 5 before truncation. -/
noncomputable def simpPreTruncWeights [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ)
    (sstar : ℕ) (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ)
    (Vbar : Matrix n b ℝ) : Matrix m n ℝ :=
  Matrix.fromCols U Ubar * simpRoundCoeff ℒc lr sstar U S V Ubar Vbar * (Matrix.fromCols V Vbar)ᵀ

/-- **Assumption 1 of arXiv 2406.17887, eq. (14), literally**: at each client update (client `c`,
`s ≤ s⋆`, so the final iterate is included too) and for `G = ℒ` and all `G = ℒ_{c'}`,
`|‖∇_S̃ G(Ũ S̃_c^s Ṽᵀ)‖ - ‖∇_S G(Ũ S̃_c^s Ṽᵀ)‖| < δ ‖∇_S̃ ℒ(Ũ S̃ Ṽᵀ)‖`, where `∇_S G = Uᵀ ∇G V` is
the block of `∇_S̃ G = Ũᵀ ∇G Ṽ` that belongs to the original bases.  This does not imply the
paper's Theorem 4 (`theorem4_false`). -/
def Assumption1 [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ) (sstar : ℕ) (U : Matrix m r ℝ)
    (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ) (Vbar : Matrix n b ℝ) (δ : ℝ) :
    Prop :=
  ∀ c, ∀ s ≤ sstar, ∀ G ∈ insert (avgLoss ℒc) (Set.range ℒc),
    |‖coeffGrad (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) G
        (simpClientIter ℒc lr U S V Ubar Vbar c s)‖ -
      ‖Uᵀ * gradient G (Matrix.fromCols U Ubar * simpClientIter ℒc lr U S V Ubar Vbar c s *
        (Matrix.fromCols V Vbar)ᵀ) * V‖| < δ * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖

/-- The repaired form of Assumption 1: eq. (14) with squared norms, only for `G = ℒ_c` on the
iterates of client `c`.  Since `‖∇_S̃ G‖² - ‖∇_S G‖²` is the squared norm of the augmented blocks of
`∇_S̃ G`, this says that these blocks are at most `δ ‖∇_S̃ ℒ(Ũ S̃ Ṽᵀ)‖`, which is how the paper's
proof uses Assumption 1. -/
def Assumption1Sq [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr : ℝ) (sstar : ℕ) (U : Matrix m r ℝ)
    (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ) (Vbar : Matrix n b ℝ) (δ : ℝ) :
    Prop :=
  ∀ c, ∀ s < sstar,
    ‖coeffGrad (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) (ℒc c)
        (simpClientIter ℒc lr U S V Ubar Vbar c s)‖ ^ 2 -
      ‖Uᵀ * gradient (ℒc c) (Matrix.fromCols U Ubar * simpClientIter ℒc lr U S V Ubar Vbar c s *
        (Matrix.fromCols V Vbar)ᵀ) * V‖ ^ 2 ≤ δ ^ 2 * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2

/-- In the weights, eq. (40) is the iteration `simpClientIterE`. -/
lemma mul_simpClientIter_mul [Fintype ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    (hd : ∀ c, Differentiable ℝ (ℒc c)) (lr : ℝ) (U : Matrix m r ℝ) (S : Matrix r r ℝ)
    (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ) (Vbar : Matrix n b ℝ) (c : ι) (s : ℕ) :
    Matrix.fromCols U Ubar * simpClientIter ℒc lr U S V Ubar Vbar c s * (Matrix.fromCols V Vbar)ᵀ =
      simpClientIterE (gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar)) (gal U V)
        (fun c => gradient (ℒc c)) (gradient (avgLoss ℒc)) lr (U * S * Vᵀ) c s := by
  induction s with
  | zero => exact lemma7_augmented_weights S
  | succ s ih =>
    have e : Matrix.fromCols U Ubar * (simpVarCorr U V ℒc S c : Matrix (r ⊕ a) (r ⊕ b) ℝ) *
        (Matrix.fromCols V Vbar)ᵀ = gal U V (gradient (avgLoss ℒc) (U * S * Vᵀ) -
          gradient (ℒc c) (U * S * Vᵀ)) := by
      rw [simpVarCorr, lemma7_augmented_weights, varCorr_eq hd, gal_apply]
    rw [simpClientIterE_succ, ← ih, simpClientIter, coeffGrad_eq ((hd c) _), gal_apply,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, e]

lemma mul_simpRoundCoeff_mul [Fintype ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    (hd : ∀ c, Differentiable ℝ (ℒc c)) (lr : ℝ) (sstar : ℕ) (U : Matrix m r ℝ)
    (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ) (Vbar : Matrix n b ℝ) :
    simpPreTruncWeights ℒc lr sstar U S V Ubar Vbar =
      simpRoundE (gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar)) (gal U V)
        (fun c => gradient (ℒc c)) (gradient (avgLoss ℒc)) lr sstar (U * S * Vᵀ) := by
  rw [simpPreTruncWeights, simpRoundCoeff, simpRoundE, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [mul_simpClientIter_mul hd]

variable [DecidableEq r] [DecidableEq a] [DecidableEq b] [DecidableEq q]

/-- The original Galerkin projector is contained in the augmented one: `Π₀ Π = Π₀`. -/
lemma gal_gal {U : Matrix m r ℝ} {V : Matrix n r ℝ} {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ}
    (hU : (Matrix.fromCols U Ubar)ᵀ * Matrix.fromCols U Ubar = 1)
    (hV : (Matrix.fromCols V Vbar)ᵀ * Matrix.fromCols V Vbar = 1) (X : Matrix m n ℝ) :
    gal U V (gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) X) = gal U V X := by
  obtain ⟨h1, h2, -, -⟩ := blocks_of_orthonormal hU
  obtain ⟨h1', -, h3', -⟩ := blocks_of_orthonormal hV
  have hL : Uᵀ * Matrix.fromCols U Ubar * (Matrix.fromCols U Ubar)ᵀ = Uᵀ := by
    rw [Matrix.mul_fromCols, h1, h2, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
    simp
  have hR : Matrix.fromCols V Vbar * (Matrix.fromCols V Vbar)ᵀ * V = V := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, Matrix.add_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, h1', h3']
    simp
  have e : Uᵀ * (Matrix.fromCols U Ubar * ((Matrix.fromCols U Ubar)ᵀ * X *
      Matrix.fromCols V Vbar) * (Matrix.fromCols V Vbar)ᵀ) * V = Uᵀ * X * V := by
    calc _ = (Uᵀ * Matrix.fromCols U Ubar * (Matrix.fromCols U Ubar)ᵀ) * X *
          (Matrix.fromCols V Vbar * (Matrix.fromCols V Vbar)ᵀ * V) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL, hR]
  rw [gal_apply, gal_apply, gal_apply, e]

/-- What is missing in Assumption 1 of arXiv 2406.17887: together with a bound
`‖∇_S̃ ℒ_c(Ũ S̃_c^s Ṽᵀ)‖ ≤ ρ ‖∇_S̃ ℒ(Ũ S̃ Ṽᵀ)‖` on the client gradients (in `theorem4_false` one
needs `ρ` of order `1/δ`), the literal Assumption 1 with `δ` implies the repaired one with
`√(2 ρ δ)`, so that `theorem4_corrected_general` applies. -/
theorem assumption1Sq_of_assumption1 [Fintype ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    (hd : ∀ c, Differentiable ℝ (ℒc c)) {lr : ℝ} {sstar : ℕ} {U : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ}
    (hU : (Matrix.fromCols U Ubar)ᵀ * Matrix.fromCols U Ubar = 1)
    (hV : (Matrix.fromCols V Vbar)ᵀ * Matrix.fromCols V Vbar = 1) {δ ρ : ℝ} (hδ : 0 ≤ δ)
    (hρ : 0 ≤ ρ) (hA : Assumption1 ℒc lr sstar U S V Ubar Vbar δ)
    (hb : ∀ c, ∀ s < sstar, ‖coeffGrad (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) (ℒc c)
      (simpClientIter ℒc lr U S V Ubar Vbar c s)‖ ≤ ρ * ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖) :
    Assumption1Sq ℒc lr sstar U S V Ubar Vbar (Real.sqrt (2 * ρ * δ)) := by
  intro c s hs
  obtain ⟨hU0, -, -, -⟩ := blocks_of_orthonormal hU
  obtain ⟨hV0, -, -, -⟩ := blocks_of_orthonormal hV
  have h1 := abs_lt.1 (hA c s hs.le (ℒc c) (Set.mem_insert_of_mem _ ⟨c, rfl⟩))
  have h2 := hb c s hs
  set a := ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ with ha
  set Y := gradient (ℒc c) (Matrix.fromCols U Ubar * simpClientIter ℒc lr U S V Ubar Vbar c s *
    (Matrix.fromCols V Vbar)ᵀ) with hY
  have e : coeffGrad (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) (ℒc c)
      (simpClientIter ℒc lr U S V Ubar Vbar c s) =
      (Matrix.fromCols U Ubar)ᵀ * Y * Matrix.fromCols V Vbar := coeffGrad_eq ((hd c) _)
  rw [e] at h1 h2 ⊢
  have h3 : ‖Uᵀ * Y * V‖ ≤ ‖(Matrix.fromCols U Ubar)ᵀ * Y * Matrix.fromCols V Vbar‖ := by
    rw [← norm_gal hU hV, ← norm_gal hU0 hV0, ← gal_gal hU hV]
    exact (isOrthProj_gal hU0 hV0).norm_le _
  have ha0 : 0 ≤ a := norm_nonneg _
  have h4 := norm_nonneg (Uᵀ * Y * V)
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg ha0 ha0, mul_nonneg hδ ha0, mul_nonneg hρ ha0]

/-- One iteration of Algorithm 5 of arXiv 2406.17887 (simplified variance correction). -/
structure IsSimpRound [Fintype ι] (ℒc : ι → Matrix m n ℝ → ℝ) (lr ϑ : ℝ) (sstar : ℕ)
    (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Ubar : Matrix m a ℝ)
    (Vbar : Matrix n b ℝ) (U' : Matrix m q ℝ) (S' : Matrix q q ℝ) (V' : Matrix n q ℝ) : Prop where
  orthU : (Matrix.fromCols U Ubar)ᵀ * Matrix.fromCols U Ubar = 1
  orthV : (Matrix.fromCols V Vbar)ᵀ * Matrix.fromCols V Vbar = 1
  trunc : IsTruncation (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar)
    (simpRoundCoeff ℒc lr sstar U S V Ubar Vbar) ϑ U' S' V'

/-- **Corrected Theorem 4 of arXiv 2406.17887, any `δ`.**  Under the repaired Assumption 1
(`Assumption1Sq`) and with `κ(δ) = y + (1 + y)²/2`, `y = e (1 + δ)`, one iteration of Algorithm 5
satisfies `ℒ(U' S' V'ᵀ) - ℒ(U S Vᵀ) ≤ -s⋆ λ (1 - κ(δ) s⋆ λ L) ‖∇_S̃ ℒ(U S Vᵀ)‖² + G ϑ`, with `G` as
in `theorem2_loss_descent`.  The paper's constant `C` is false (`theorem4_false`). -/
theorem theorem4_corrected_general [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    {L lr ϑ G δ : ℝ} (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 ≤ L) (hlr : 0 ≤ lr) (hδ : 0 ≤ δ)
    {sstar : ℕ} (hs : lr * L * sstar ≤ 1) {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ} {U' : Matrix m q ℝ} {S' : Matrix q q ℝ}
    {V' : Matrix n q ℝ} (h : IsSimpRound ℒc lr ϑ sstar U S V Ubar Vbar U' S' V')
    (hA : Assumption1Sq ℒc lr sstar U S V Ubar Vbar δ)
    (hG : ∀ W ∈ segment ℝ (simpPreTruncWeights ℒc lr sstar U S V Ubar Vbar) (U' * S' * V'ᵀ),
      ‖gradient (avgLoss ℒc) W‖ ≤ G) :
    avgLoss ℒc (U' * S' * V'ᵀ) - avgLoss ℒc (U * S * Vᵀ) ≤
      -(sstar * lr) * (1 - kappa δ * (sstar * lr) * L) *
        ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2 + G * ϑ := by
  have hg := IsLSmooth.avgLoss hL
  have hd := fun c => (hL c).differentiable
  obtain ⟨hU0, -, -, -⟩ := blocks_of_orthonormal h.orthU
  obtain ⟨hV0, -, -, -⟩ := blocks_of_orthonormal h.orthV
  have hx : Matrix.fromCols U Ubar * (Matrix.fromBlocks S 0 0 0 : Matrix (r ⊕ a) (r ⊕ b) ℝ) *
      (Matrix.fromCols V Vbar)ᵀ = U * S * Vᵀ := lemma7_augmented_weights S
  have hgS : ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ =
      ‖gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) (gradient (avgLoss ℒc)
        (U * S * Vᵀ))‖ := by
    rw [norm_gal h.orthU h.orthV, gradS, coeffGrad_eq (hg.differentiable _), hx]
  have hTP := gal_gal (U := U) (V := V) h.orthU h.orthV
  have hT := isOrthProj_gal hU0 hV0
  have hb : ∀ c, ∀ s < sstar,
      ‖gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) (gradient (ℒc c)
          (simpClientIterE (gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar)) (gal U V)
            (fun c => gradient (ℒc c)) (gradient (avgLoss ℒc)) lr (U * S * Vᵀ) c s)) -
        gal U V (gradient (ℒc c)
          (simpClientIterE (gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar)) (gal U V)
            (fun c => gradient (ℒc c)) (gradient (avgLoss ℒc)) lr (U * S * Vᵀ) c s))‖ ≤
      δ * ‖gal (Matrix.fromCols U Ubar) (Matrix.fromCols V Vbar) (gradient (avgLoss ℒc)
        (U * S * Vᵀ))‖ := by
    intro c s hs'
    have h1 := hA c s hs'
    rw [coeffGrad_eq ((hd c) _), mul_simpClientIter_mul hd, ← norm_gal h.orthU h.orthV,
      ← norm_gal hU0 hV0, ← norm_sub_sq_of_le hT hTP, hgS, ← mul_pow] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
  have h8 := loss_simpRoundE_le (ℒ := avgLoss ℒc) (g := gradient (avgLoss ℒc))
    (gc := fun c => gradient (ℒc c))
    (hasFDerivAt_of_hasGradientAt fun x => (hg.differentiable x).hasGradientAt) hg.lipschitz
    (fun c x y => (hL c).lipschitz x y) (isOrthProj_gal h.orthU h.orthV) hT hTP hL0 hlr hδ hs
    (U * S * Vᵀ) (gradient_avgLoss fun c => hd c _) hb
  rw [← mul_simpRoundCoeff_mul hd, ← hgS] at h8
  have hn : ‖U' * S' * V'ᵀ - simpPreTruncWeights ℒc lr sstar U S V Ubar Vbar‖ ≤ ϑ :=
    h.trunc.norm_sub_le h.orthU h.orthV
  have hen := abs_energy_sub_le
    (hasFDerivAt_of_hasGradientAt fun x => (hg.differentiable x).hasGradientAt) hG
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG _ (left_mem_segment ℝ _ _))
  have h3 := mul_le_mul_of_nonneg_left hn hG0
  have h4 := (abs_le.1 hen).2
  linarith

/-- **Corrected Theorem 4 of arXiv 2406.17887.**  Under the repaired Assumption 1 with `δ ≤ 1/6`,
one iteration of Algorithm 5 has the descent of the full correction (Theorem 2):
`ℒ(U' S' V'ᵀ) - ℒ(U S Vᵀ) ≤ -s⋆ λ (1 - 12 s⋆ λ L) ‖∇_S̃ ℒ(U S Vᵀ)‖² + G ϑ`, which for `s⋆ λ ≤ 1` is
stronger than the claim of the paper.  Differences from the paper: its Assumption 1 and its
constant `C = s⋆ λ (1 - δ² - 12 s⋆ λ L + δ² s⋆ λ)` do not work (`theorem4_false`); the assumption
is replaced by `Assumption1Sq`, `L ϑ` by `G ϑ` as in `theorem2_loss_descent`. -/
theorem theorem4_corrected [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    {L lr ϑ G δ : ℝ} (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 ≤ L) (hlr : 0 ≤ lr) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 6)
    {sstar : ℕ} (hs : lr * L * sstar ≤ 1) {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    {Ubar : Matrix m a ℝ} {Vbar : Matrix n b ℝ} {U' : Matrix m q ℝ} {S' : Matrix q q ℝ}
    {V' : Matrix n q ℝ} (h : IsSimpRound ℒc lr ϑ sstar U S V Ubar Vbar U' S' V')
    (hA : Assumption1Sq ℒc lr sstar U S V Ubar Vbar δ)
    (hG : ∀ W ∈ segment ℝ (simpPreTruncWeights ℒc lr sstar U S V Ubar Vbar) (U' * S' * V'ᵀ),
      ‖gradient (avgLoss ℒc) W‖ ≤ G) :
    avgLoss ℒc (U' * S' * V'ᵀ) - avgLoss ℒc (U * S * Vᵀ) ≤
      -(sstar * lr) * (1 - 12 * (sstar * lr) * L) *
        ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖ ^ 2 + G * ϑ := by
  refine (theorem4_corrected_general hL hL0 hlr hδ hs h hA hG).trans ?_
  have hk := kappa_le_twelve hδ hδ1
  have hA0 : 0 ≤ (sstar : ℝ) * lr := by positivity
  have : kappa δ * ((sstar : ℝ) * lr) * L ≤ 12 * (sstar * lr) * L := by gcongr
  have h1 := mul_le_mul_of_nonneg_left this
    (mul_nonneg hA0 (sq_nonneg ‖gradS (avgLoss ℒc) U S V Ubar Vbar‖))
  nlinarith

/-- **Corrected Corollary 1 of arXiv 2406.17887.**  For `T > 0` iterations of Algorithm 5 under the
repaired Assumption 1 with `δ ≤ 1/6` and `s⋆ λ L ∈ [1/80, 1/16]`, some `t < T` satisfies
`‖∇_S̃ ℒ(U^t S^t V^{t,ᵀ})‖² ≤ 96 L/T (ℒ(W⁰) - ℒ(W^T)) + 96 L G ϑ`, the paper's bound with `96 L² ϑ`
for `G = L`.  The paper claims this under Assumption 1 for all `λ ≤ 1/(s⋆ (12 L + δ²))`; this is
false (`theorem4_false`, which violates eq. (47) for `T = 1`).  The iterations are numbered from
`0`. -/
theorem corollary1_corrected [Fintype ι] [Nonempty ι] {ℒc : ι → Matrix m n ℝ → ℝ}
    {L lr ϑ G δ : ℝ} (hL : ∀ c, IsLSmooth (ℒc c) L) (hL0 : 0 < L) (hlr : 0 ≤ lr) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 6) {sstar : ℕ} (hlr1 : 1 / 80 ≤ sstar * lr * L) (hlr2 : sstar * lr * L ≤ 1 / 16)
    {rk ak bk : ℕ → ℕ}
    {U : ∀ t, Matrix m (Fin (rk t)) ℝ} {S : ∀ t, Matrix (Fin (rk t)) (Fin (rk t)) ℝ}
    {V : ∀ t, Matrix n (Fin (rk t)) ℝ} {Ubar : ∀ t, Matrix m (Fin (ak t)) ℝ}
    {Vbar : ∀ t, Matrix n (Fin (bk t)) ℝ} {T : ℕ} (hT : 0 < T)
    (h : ∀ t < T, IsSimpRound ℒc lr ϑ sstar (U t) (S t) (V t) (Ubar t) (Vbar t) (U (t + 1))
      (S (t + 1)) (V (t + 1)))
    (hA : ∀ t < T, Assumption1Sq ℒc lr sstar (U t) (S t) (V t) (Ubar t) (Vbar t) δ)
    (hG : ∀ t < T, ∀ W ∈ segment ℝ
      (simpPreTruncWeights ℒc lr sstar (U t) (S t) (V t) (Ubar t) (Vbar t))
      (U (t + 1) * S (t + 1) * (V (t + 1))ᵀ), ‖gradient (avgLoss ℒc) W‖ ≤ G) :
    ∃ t < T, ‖gradS (avgLoss ℒc) (U t) (S t) (V t) (Ubar t) (Vbar t)‖ ^ 2 ≤
      96 * L / T * (avgLoss ℒc (U 0 * S 0 * (V 0)ᵀ) - avgLoss ℒc (U T * S T * (V T)ᵀ)) +
        96 * L * G * ϑ := by
  have hs : lr * L * sstar ≤ 1 := by nlinarith
  set A : ℝ := sstar * lr with hAdef
  have hc : 1 / (96 * L) ≤ A * (1 - 12 * A * L) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hlr1) (sub_nonneg.2 hlr2)]
  have hc0 : 0 < 1 / (96 * L) := by positivity
  obtain ⟨t, ht, hle⟩ := exists_le_of_descent (u := fun t => avgLoss ℒc (U t * S t * (V t)ᵀ))
    (a := fun t => ‖gradS (avgLoss ℒc) (U t) (S t) (V t) (Ubar t) (Vbar t)‖ ^ 2)
    (e := G * ϑ) hc0 hT (fun t ht => by
      have h1 := theorem4_corrected hL hL0.le hlr hδ hδ1 hs (h t ht) (hA t ht) (hG t ht)
      have h2 := mul_le_mul_of_nonneg_right hc
        (sq_nonneg ‖gradS (avgLoss ℒc) (U t) (S t) (V t) (Ubar t) (Vbar t)‖)
      simp only [← hAdef] at h1
      linarith)
  refine ⟨t, ht, hle.trans (le_of_eq ?_)⟩
  have : (0 : ℝ) < T := Nat.cast_pos.2 hT
  field_simp

end Simplified

end Matrix

/-! ### Counterexamples: the setting -/

section Counterexamples

open scoped LeanDLRA.Frobenius

/-- The index type of `2 × 2` matrices with blocks of size `1`. -/
abbrev Two : Type := Unit ⊕ Unit

/-- `ℝ^{2 × 2}`. -/
abbrev M2 : Type := Matrix Two Two ℝ

/-- The original basis `U = V = e₁`. -/
def e₁ : Matrix Two Unit ℝ := Matrix.fromRows 1 0

/-- The augmentation `Ū = V̄ = e₂`. -/
def e₂ : Matrix Two Unit ℝ := Matrix.fromRows 0 1

/-- A `1 × 1` matrix. -/
def sc (s : ℝ) : Matrix Unit Unit ℝ := fun _ _ => s

/-- `e₁ e₁ᵀ`. -/
def E00 : M2 := Matrix.fromBlocks 1 0 0 0

/-- `e₁ e₂ᵀ`. -/
def E01 : M2 := Matrix.fromBlocks 0 1 0 0

/-- `e₂ e₂ᵀ`. -/
def E11 : M2 := Matrix.fromBlocks 0 0 0 1

/-- The swap of the two coordinates. -/
def Xm : M2 := Matrix.fromBlocks 0 1 1 0

lemma fromCols_e₁_e₂ : Matrix.fromCols e₁ e₂ = 1 := by
  rw [e₁, e₂, Matrix.fromCols_fromRows_eq_fromBlocks, Matrix.fromBlocks_one]

lemma orth_e : (Matrix.fromCols e₁ e₂)ᵀ * Matrix.fromCols e₁ e₂ = 1 := by
  rw [fromCols_e₁_e₂]; simp

lemma orth_e₁ : e₁ᵀ * e₁ = 1 := (blocks_of_orthonormal orth_e).1

lemma E00_mul_Xm : E00 * Xm = E01 := by
  simp [E00, E01, Xm, Matrix.fromBlocks_multiply]

lemma E01_mul_Xm : E01 * Xm = E00 := by
  simp [E00, E01, Xm, Matrix.fromBlocks_multiply]

lemma Xm_transpose : Xmᵀ = Xm := by
  simp [Xm, Matrix.fromBlocks_transpose]

lemma Xm_orth : Xmᵀ * Xm = 1 := by
  rw [Xm_transpose]
  simp [Xm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

lemma e₁_mul_transpose (s : ℝ) : e₁ * sc s * e₁ᵀ = s • E00 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [e₁, E00, sc, Matrix.mul_apply]

lemma e₁_transpose_mul_row (x y : ℝ) : e₁ᵀ * (x • E00 + y • E01) * e₁ = sc x := by
  ext i j
  simp [e₁, E00, E01, sc, Matrix.mul_apply, Fintype.sum_sum_type]

lemma fromBlocks_sc (s : ℝ) :
    (Matrix.fromBlocks (sc s) 0 0 0 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ) = s • E00 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [E00, sc]

lemma norm_sq_row (x y : ℝ) : ‖x • E00 + y • E01‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp [E00, E01, Fintype.sum_sum_type]

lemma norm_sc (x : ℝ) : ‖sc x‖ = |x| := by
  have h : ‖sc x‖ ^ 2 = x ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [sc]
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq_eq_abs]

lemma norm_E00 : ‖E00‖ = 1 := by
  have h : ‖E00‖ ^ 2 = 1 := by
    have := norm_sq_row 1 0
    simpa using this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

lemma norm_E11 : ‖E11‖ = 1 := by
  have h : ‖E11‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [E11, Fintype.sum_sum_type]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

lemma coeffGrad_one (f : M2 → ℝ) (S : M2) : coeffGrad (1 : M2) 1 f S = gradient f S := by
  simp [coeffGrad]

/-- A quadratic loss `W ↦ ⟪B, W⟫ + σ/2 ⟪W, W X⟫`. -/
noncomputable def quadLoss (X B : M2) (σ : ℝ) (W : M2) : ℝ :=
  ⟪B, W⟫ + σ / 2 * ⟪W, W * X⟫

lemma hasGradientAt_quadLoss {X : M2} (hX : Xᵀ = X) (B : M2) (σ : ℝ) (W : M2) :
    HasGradientAt (quadLoss X B σ) (B + σ • (W * X)) W := by
  have h1 := (hasFDerivAt_id W).inner ℝ (Frobenius.rightMulCLM X : M2 →L[ℝ] M2).hasFDerivAt
  have h2 : HasFDerivAt (fun W : M2 => ⟪B, W⟫) (innerSL ℝ B) W :=
    (innerSL ℝ B).hasFDerivAt
  have h3 := h2.add (h1.const_mul (σ / 2))
  have e : InnerProductSpace.toDual ℝ M2 (B + σ • (W * X)) = innerSL ℝ B + (σ / 2) •
      (fderivInnerCLM ℝ (id W, (Frobenius.rightMulCLM X : M2 →L[ℝ] M2) W)).comp
        ((ContinuousLinearMap.id ℝ M2).prod (Frobenius.rightMulCLM X)) := by
    refine ContinuousLinearMap.ext fun D => ?_
    change ⟪B + σ • (W * X), D⟫ = ⟪B, D⟫ + (σ / 2) * (⟪W, D * X⟫ + ⟪D, W * X⟫)
    rw [inner_add_left, real_inner_smul_left, Frobenius.inner_mul_right' W D X, hX,
      real_inner_comm D (W * X)]
    ring
  rw [hasGradientAt_iff_hasFDerivAt, e]
  exact h3

lemma isLSmooth_quadLoss {X : M2} (hX : Xᵀ = X) (hXX : Xᵀ * X = 1) (B : M2) {σ : ℝ}
    (hσ : |σ| ≤ 1) : IsLSmooth (quadLoss X B σ) 1 where
  differentiable W := (hasGradientAt_quadLoss hX B σ W).differentiableAt
  lipschitz x y := by
    rw [(hasGradientAt_quadLoss hX B σ x).gradient, (hasGradientAt_quadLoss hX B σ y).gradient]
    have e : B + σ • (x * X) - (B + σ • (y * X)) = σ • ((x - y) * X) := by
      rw [Matrix.sub_mul, smul_sub]; abel
    have h : ‖(x - y) * X‖ = ‖x - y‖ := by
      have := Frobenius.norm_mul_transpose_of_orthonormal hXX (x - y)
      rwa [hX] at this
    rw [e, norm_smul, Real.norm_eq_abs, h]
    exact mul_le_mul_of_nonneg_right hσ (norm_nonneg _)

/-! ### Theorems 2 and 3 of the paper are false as stated -/

/-- The single client loss `W ↦ ‖W‖²/2 - ⟪A, W⟫` (up to a constant `‖W - A‖²/2`). -/
noncomputable def sqLoss (A : M2) : Unit → M2 → ℝ := fun _ => quadLoss 1 (-A) 1

lemma isLSmooth_sqLoss (A : M2) (c : Unit) : IsLSmooth (sqLoss A c) 1 :=
  isLSmooth_quadLoss (by simp) (by simp) _ (by simp)

lemma gradient_sqLoss (A W : M2) (c : Unit) : gradient (sqLoss A c) W = W - A := by
  have h := (hasGradientAt_quadLoss (X := 1) (by simp) (-A) 1 W).gradient
  have e : sqLoss A c = quadLoss 1 (-A) 1 := rfl
  rw [e, h]
  simp
  abel

lemma avgLoss_sqLoss (A W : M2) : avgLoss (sqLoss A) W = quadLoss 1 (-A) 1 W := by
  simp [avgLoss, sqLoss]

lemma gradient_avgLoss_sqLoss (A W : M2) : gradient (avgLoss (sqLoss A)) W = W - A := by
  rw [gradient_avgLoss fun c => (isLSmooth_sqLoss A c).differentiable W]
  simp [gradient_sqLoss]

lemma roundCoeff_sqLoss (A St : M2) (lr : ℝ) :
    roundCoeff (Matrix.fromCols e₁ e₂) (Matrix.fromCols e₁ e₂) (sqLoss A) lr 1 St =
      St - lr • (St - A) := by
  rw [fromCols_e₁_e₂]
  simp [roundCoeff, clientIter, varCorr, coeffGrad_one, gradient_sqLoss]

/-- **Theorem 2 of arXiv 2406.17887 is false for losses that are merely `L`-smooth** (`L`-Lipschitz
gradient, the meaning of Lemma 4 of the paper): the term `L ϑ` needs a bound on `∇ℒ`, which step
(36) of the paper's proof uses without assuming it.  Here `C = s⋆ = 1`, `L = 1`, `λ = 1/24 ≤
1/(12 L s⋆)`, `ℒ(W) = ‖W - A‖²/2 + const` with `A = diag(1, 4)`, and `U S Vᵀ = diag(1, 0)` with
`S = 1` of full rank.  The aggregation gives `S̃⋆ = diag(1, 1/6)` and the singular value truncation
with threshold `ϑ = 1/5 > 1/6` returns to `U S Vᵀ`.  The loss does not change, while eq. (12) would
claim `0 ≤ -1/3 + 1/5`.  Correct forms: `theorem2_loss_descent`, `theorem2_loss_descent'`,
`theorem2_loss_descent_smooth`. -/
theorem theorem2_false_of_smooth_only :
    ∃ ℒc : Unit → M2 → ℝ, (∀ c, IsLSmooth (ℒc c) 1) ∧ (1 / 24 : ℝ) ≤ 1 / (12 * 1 * 1) ∧
      IsFeDLRTRound ℒc (1 / 24) (1 / 5) 1 e₁ (sc 1) e₁ e₂ e₂ e₁ (sc 1) e₁ ∧
      ¬ (avgLoss ℒc (e₁ * sc 1 * e₁ᵀ) - avgLoss ℒc (e₁ * sc 1 * e₁ᵀ) ≤
        -(((1 : ℕ) : ℝ) * (1 / 24)) * (1 - 12 * (((1 : ℕ) : ℝ) * (1 / 24)) * 1) *
          ‖gradS (avgLoss ℒc) e₁ (sc 1) e₁ e₂ e₂‖ ^ 2 + 1 * (1 / 5)) := by
  set A : M2 := E00 + (4 : ℝ) • E11 with hA
  have hSt : (Matrix.fromBlocks (sc 1) 0 0 0 : M2) = E00 := by
    rw [fromBlocks_sc, one_smul]
  have hc : (Matrix.fromBlocks (sc 1) 0 0 0 : M2) -
      (1 / 24 : ℝ) • ((Matrix.fromBlocks (sc 1) 0 0 0 : M2) - A) = E00 + (1 / 6 : ℝ) • E11 := by
    rw [hSt, hA]; module
  refine ⟨sqLoss A, isLSmooth_sqLoss A, by norm_num, ⟨orth_e, orth_e, ?_⟩, ?_⟩
  · refine ⟨e₁, e₁, orth_e₁, orth_e₁, ?_, by rw [fromCols_e₁_e₂]; simp,
      by rw [fromCols_e₁_e₂]; simp⟩
    rw [roundCoeff_sqLoss, hc, e₁_mul_transpose, one_smul, add_sub_cancel_left, norm_smul,
      norm_E11]
    norm_num
  · have hg : gradS (avgLoss (sqLoss A)) e₁ (sc 1) e₁ e₂ e₂ = (-4 : ℝ) • E11 := by
      rw [gradS, fromCols_e₁_e₂, coeffGrad_one, gradient_avgLoss_sqLoss, hSt, hA]
      module
    rw [hg, norm_smul, norm_E11]
    norm_num

/-- **Theorem 3 of arXiv 2406.17887 is false for general `λ ≤ 1/(12 L s⋆)`**: its proof only treats
`λ = 1/(24 L s⋆)`.  One client, `s⋆ = T = 1`, `L = 1`, no truncation (`ϑ = 0`), `λ = 1/100`,
`ℒ(W) = ‖W‖²/2`, `U S Vᵀ = diag(1, 0)`; the gradient is bounded by `L` on the (trivial) truncation
segment.  The minimum over the single iteration is `1`, while eq. (13) would give
`48 (1/2 - (99/100)²/2) < 1`.  Correct forms: `theorem3_convergence_general` and
`theorem3_convergence`. -/
theorem theorem3_false_of_small_lr :
    ∃ ℒc : Unit → M2 → ℝ, (∀ c, IsLSmooth (ℒc c) 1) ∧ (1 / 100 : ℝ) ≤ 1 / (12 * 1 * 1) ∧
      IsFeDLRTRound ℒc (1 / 100) 0 1 e₁ (sc 1) e₁ e₂ e₂ e₁ (sc (99 / 100)) e₁ ∧
      (∀ W ∈ segment ℝ (preTruncWeights ℒc (1 / 100) 1 e₁ (sc 1) e₁ e₂ e₂)
        (e₁ * sc (99 / 100) * e₁ᵀ), ‖gradient (avgLoss ℒc) W‖ ≤ 1) ∧
      ¬ (‖gradS (avgLoss ℒc) e₁ (sc 1) e₁ e₂ e₂‖ ^ 2 ≤
        48 * 1 / ((1 : ℕ) : ℝ) * (avgLoss ℒc (e₁ * sc 1 * e₁ᵀ) -
          avgLoss ℒc (e₁ * sc (99 / 100) * e₁ᵀ)) + 48 * 1 ^ 2 * 0) := by
  have hSt : (Matrix.fromBlocks (sc 1) 0 0 0 : M2) = E00 := by
    rw [fromBlocks_sc, one_smul]
  have hc : roundCoeff (Matrix.fromCols e₁ e₂) (Matrix.fromCols e₁ e₂) (sqLoss 0) (1 / 100) 1
      (Matrix.fromBlocks (sc 1) 0 0 0) = (99 / 100 : ℝ) • E00 := by
    rw [roundCoeff_sqLoss, hSt]; module
  have hW : e₁ * sc (99 / 100) * e₁ᵀ = (99 / 100 : ℝ) • E00 := e₁_mul_transpose _
  have hP : preTruncWeights (sqLoss 0) (1 / 100) 1 e₁ (sc 1) e₁ e₂ e₂ = (99 / 100 : ℝ) • E00 := by
    rw [preTruncWeights, hc, fromCols_e₁_e₂]; simp
  refine ⟨sqLoss 0, isLSmooth_sqLoss 0, by norm_num, ⟨orth_e, orth_e, ?_⟩, ?_, ?_⟩
  · refine ⟨e₁, e₁, orth_e₁, orth_e₁, ?_, by rw [fromCols_e₁_e₂]; simp,
      by rw [fromCols_e₁_e₂]; simp⟩
    rw [hc, e₁_mul_transpose, sub_self, norm_zero]
  · intro W hW'
    rw [hP, hW, segment_same, Set.mem_singleton_iff] at hW'
    rw [hW', gradient_avgLoss_sqLoss, sub_zero, norm_smul, norm_E00]
    norm_num
  · have hg : gradS (avgLoss (sqLoss 0)) e₁ (sc 1) e₁ e₂ e₂ = E00 := by
      rw [gradS, fromCols_e₁_e₂, coeffGrad_one, gradient_avgLoss_sqLoss, hSt, sub_zero]
    have hval (s : ℝ) : avgLoss (sqLoss 0) (e₁ * sc s * e₁ᵀ) = s ^ 2 / 2 := by
      rw [avgLoss_sqLoss, e₁_mul_transpose, quadLoss]
      simp only [neg_zero, inner_zero_left, zero_add, Matrix.mul_one, one_div]
      rw [real_inner_self_eq_norm_sq, norm_smul, norm_E00, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    rw [hg, norm_E00, hval, hval]
    norm_num

/-- The repaired Assumption 1 of arXiv 2406.17887 (`Assumption1Sq`) is not vacuous: it holds with
`δ = 0` and a nonzero gradient for one client with the linear loss `W ↦ W₁₁` and any `λ`, `s⋆`. -/
theorem assumption1Sq_nonvacuous (lr : ℝ) (sstar : ℕ) :
    ∃ ℒc : Unit → M2 → ℝ, (∀ c, IsLSmooth (ℒc c) 1) ∧
      0 < ‖gradS (avgLoss ℒc) e₁ (sc 1) e₁ e₂ e₂‖ ∧
      Assumption1Sq ℒc lr sstar e₁ (sc 1) e₁ e₂ e₂ 0 := by
  have hs : IsLSmooth (quadLoss 1 E00 0) 1 := isLSmooth_quadLoss (by simp) (by simp) _ (by simp)
  have hg (W : M2) : gradient (quadLoss 1 E00 0) W = E00 := by
    rw [(hasGradientAt_quadLoss (X := 1) (by simp) E00 0 W).gradient]
    simp
  have hga (W : M2) : gradient (avgLoss fun _ : Unit => quadLoss 1 E00 0) W = E00 := by
    rw [gradient_avgLoss fun _ => hs.differentiable W]
    simp [hg]
  have hS : gradS (avgLoss fun _ : Unit => quadLoss 1 E00 0) e₁ (sc 1) e₁ e₂ e₂ = E00 := by
    rw [gradS, fromCols_e₁_e₂, coeffGrad_one, hga]
  refine ⟨fun _ => quadLoss 1 E00 0, fun _ => hs, by rw [hS, norm_E00]; norm_num, ?_⟩
  intro c s _
  have e : E00 = (1 : ℝ) • E00 + (0 : ℝ) • E01 := by simp
  rw [fromCols_e₁_e₂, coeffGrad_one, hg, hg, e, e₁_transpose_mul_row, ← e, norm_sc, norm_E00]
  simp

/-! ### Theorem 4 and Corollary 1 of the paper are false as stated -/

/-- The sign of a client. -/
def sgn : Bool → ℝ
  | true => 1
  | false => -1

lemma abs_sgn (c : Bool) : |sgn c| = 1 := by cases c <;> simp [sgn]

/-- The two client losses of the counterexample to Theorem 4:
`ℒ_± (W) = W₁₁ ± (M W₁₁ + 119 W₁₂ + ⟪W, W X⟫/2)`, with `X` the swap of coordinates, so that
`ℒ(W) = W₁₁` and `∇ℒ_± (W) = E₁₁ ± (M E₁₁ + 119 E₁₂ + W X)`. -/
noncomputable def cxLoss (M : ℝ) (c : Bool) : M2 → ℝ :=
  quadLoss Xm (E00 + sgn c • (M • E00 + (119 : ℝ) • E01)) (sgn c)

lemma isLSmooth_cxLoss (M : ℝ) (c : Bool) : IsLSmooth (cxLoss M c) 1 :=
  isLSmooth_quadLoss Xm_transpose Xm_orth _ (abs_sgn c).le

lemma gradient_cxLoss (M : ℝ) (c : Bool) (W : M2) : gradient (cxLoss M c) W =
    E00 + sgn c • (M • E00 + (119 : ℝ) • E01) + sgn c • (W * Xm) :=
  (hasGradientAt_quadLoss Xm_transpose _ _ W).gradient

lemma gradient_cxLoss_row (M : ℝ) (c : Bool) (p q : ℝ) :
    gradient (cxLoss M c) (p • E00 + q • E01) =
      (1 + sgn c * (M + q)) • E00 + (sgn c * (119 + p)) • E01 := by
  rw [gradient_cxLoss, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, E00_mul_Xm, E01_mul_Xm]
  module

lemma gradient_avgLoss_cx (M : ℝ) (W : M2) : gradient (avgLoss (cxLoss M)) W = E00 := by
  rw [gradient_avgLoss fun c => (isLSmooth_cxLoss M c).differentiable W, Fintype.card_bool,
    Fintype.sum_bool, gradient_cxLoss, gradient_cxLoss]
  simp only [sgn]
  push_cast
  module

lemma avgLoss_cx (M : ℝ) (s : ℝ) : avgLoss (cxLoss M) (e₁ * sc s * e₁ᵀ) = s := by
  rw [e₁_mul_transpose]
  simp only [avgLoss, Fintype.card_bool, Fintype.sum_bool, cxLoss, quadLoss, sgn]
  simp only [inner_add_left, inner_smul_left, conj_trivial, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_E00]
  push_cast
  ring

lemma varCorr_cx (M : ℝ) (c : Bool) :
    varCorr e₁ e₁ (cxLoss M) (sc 1) c = sc (-(sgn c * M)) := by
  rw [varCorr_eq fun c => (isLSmooth_cxLoss M c).differentiable, e₁_mul_transpose,
    gradient_avgLoss_cx]
  have e : (1 : ℝ) • E00 = (1 : ℝ) • E00 + (0 : ℝ) • E01 := by simp
  rw [e, gradient_cxLoss_row]
  have e2 : E00 - ((1 + sgn c * (M + 0)) • E00 + (sgn c * (119 + 1)) • E01) =
      (-(sgn c * M)) • E00 + (-(sgn c * 120)) • E01 := by
    rw [add_zero]; norm_num; module
  rw [e2, e₁_transpose_mul_row]

/-- The client iterates of the counterexample. -/
lemma simpClientIter_cx_succ (M : ℝ) (c : Bool) (s : ℕ) :
    simpClientIter (cxLoss M) (1 / 30) e₁ (sc 1) e₁ e₂ e₂ c (s + 1) =
      simpClientIter (cxLoss M) (1 / 30) e₁ (sc 1) e₁ e₂ e₂ c s - (1 / 30 : ℝ) •
        (gradient (cxLoss M c) (simpClientIter (cxLoss M) (1 / 30) e₁ (sc 1) e₁ e₂ e₂ c s) +
          (-(sgn c * M)) • E00) := by
  rw [simpClientIter, fromCols_e₁_e₂, coeffGrad_one, simpVarCorr, varCorr_cx, fromBlocks_sc]

lemma simpClientIter_cx_zero (M : ℝ) (c : Bool) :
    simpClientIter (cxLoss M) (1 / 30) e₁ (sc 1) e₁ e₂ e₂ c 0 = (1 : ℝ) • E00 + (0 : ℝ) • E01 := by
  rw [simpClientIter, fromBlocks_sc]
  simp

lemma simpClientIter_cx_one (M : ℝ) (c : Bool) :
    simpClientIter (cxLoss M) (1 / 30) e₁ (sc 1) e₁ e₂ e₂ c 1 =
      (29 / 30 : ℝ) • E00 + (-(4 * sgn c)) • E01 := by
  rw [simpClientIter_cx_succ, simpClientIter_cx_zero, gradient_cxLoss_row]
  module

lemma simpClientIter_cx_two (M : ℝ) (c : Bool) :
    simpClientIter (cxLoss M) (1 / 30) e₁ (sc 1) e₁ e₂ e₂ c 2 =
      (16 / 15 : ℝ) • E00 + (-(sgn c * (4 + 3599 / 900))) • E01 := by
  rw [simpClientIter_cx_succ, simpClientIter_cx_one, gradient_cxLoss_row]
  cases c <;> simp only [sgn] <;> module

lemma simpRoundCoeff_cx (M : ℝ) :
    simpRoundCoeff (cxLoss M) (1 / 30) 2 e₁ (sc 1) e₁ e₂ e₂ = (16 / 15 : ℝ) • E00 := by
  rw [simpRoundCoeff, Fintype.card_bool, Fintype.sum_bool, simpClientIter_cx_two,
    simpClientIter_cx_two]
  simp only [sgn]
  push_cast
  module

lemma gradS_cx (M : ℝ) : gradS (avgLoss (cxLoss M)) e₁ (sc 1) e₁ e₂ e₂ = E00 := by
  rw [gradS, fromCols_e₁_e₂, coeffGrad_one, gradient_avgLoss_cx]

/-- A matrix row `(x, y)` with `|x|` large compared with `y²`: the difference between the norm of
the whole row and of its first entry is small. -/
private lemma abs_norm_row_sub_lt {δ x y : ℝ} (hδ : 0 < δ) (hx : 10000 / δ ≤ |x|)
    (hy : y ^ 2 ≤ 15000) : abs (‖x • E00 + y • E01‖ - |x|) < δ := by
  set A := ‖x • E00 + y • E01‖ with hA
  have hA2 : A ^ 2 = x ^ 2 + y ^ 2 := norm_sq_row x y
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ |x| := abs_nonneg x
  have hB2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hBδ : 10000 ≤ |x| * δ := by rwa [div_le_iff₀ hδ] at hx
  have hge : |x| ≤ A := by
    refine (pow_le_pow_iff_left₀ hB0 hA0 two_ne_zero).1 ?_
    rw [hA2, hB2]; nlinarith [sq_nonneg y]
  rw [abs_of_nonneg (sub_nonneg.2 hge), sub_lt_iff_lt_add]
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [hA2]
  nlinarith [sq_nonneg δ, sq_nonneg (|x| + δ)]

/-- Assumption 1 at a row `p E₁₁ + q E₁₂`. -/
private lemma assumption1_row {δ : ℝ} (hδ : 0 < δ) {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2)
    (hq : |q| ≤ 8) {G : M2 → ℝ}
    (hG : G ∈ insert (avgLoss (cxLoss (10000 / δ + 10))) (Set.range (cxLoss (10000 / δ + 10)))) :
    |‖coeffGrad (Matrix.fromCols e₁ e₂) (Matrix.fromCols e₁ e₂) G (p • E00 + q • E01)‖ -
      ‖e₁ᵀ * gradient G (Matrix.fromCols e₁ e₂ * (p • E00 + q • E01) *
        (Matrix.fromCols e₁ e₂)ᵀ) * e₁‖| < δ := by
  rw [fromCols_e₁_e₂, coeffGrad_one]
  simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  rcases hG with rfl | ⟨c, rfl⟩
  · have e : E00 = (1 : ℝ) • E00 + (0 : ℝ) • E01 := by simp
    rw [gradient_avgLoss_cx, e, e₁_transpose_mul_row, ← e, norm_sc, norm_E00]
    simpa using hδ
  · rw [gradient_cxLoss_row, e₁_transpose_mul_row, norm_sc]
    refine abs_norm_row_sub_lt hδ ?_ ?_
    · have hδ' : 0 < 10000 / δ := by positivity
      have hq' := abs_le.1 hq
      cases c with
      | true =>
        simp only [sgn]
        exact (by linarith : 10000 / δ ≤ 1 + 1 * (10000 / δ + 10 + q)).trans (le_abs_self _)
      | false =>
        simp only [sgn]
        exact (by linarith : 10000 / δ ≤ -(1 + -1 * (10000 / δ + 10 + q))).trans (neg_le_abs _)
    · cases c <;> simp only [sgn] <;> nlinarith

/-- **Theorem 4 and Corollary 1 of arXiv 2406.17887 are false as stated.**  For every `δ ∈ (0, 1]`
there are two clients with `1`-smooth quadratic losses, `s⋆ = 2`, `λ = 1/30` (which satisfies both
`λ ≤ 1/(12 L s⋆)` and `λ ≤ 1/(s⋆ (12 L + δ²))`), and a full rank start `U S Vᵀ = diag(1, 0)`, such
that Assumption 1, eq. (14), holds at all client updates, Algorithm 5 runs without truncation
(`ϑ = 0`), and the global loss *increases* from `1` to `16/15`.  So eq. (41) and, for `T = 1`,
eq. (47) fail.  The reason: eq. (14) compares norms, so a large gradient in the block of `S` hides
a large gradient in the augmented blocks.  The client drift in these blocks is not corrected by
`V̌_c`, while the proof of the paper needs it to be small.  See `assumption1Sq_of_assumption1`,
`theorem4_corrected` and `corollary1_corrected`. -/
theorem theorem4_false {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ ℒc : Bool → M2 → ℝ, (∀ c, IsLSmooth (ℒc c) 1) ∧
      (1 / 30 : ℝ) ≤ 1 / (12 * 1 * ((2 : ℕ) : ℝ)) ∧
      (1 / 30 : ℝ) ≤ 1 / (((2 : ℕ) : ℝ) * (12 * 1 + δ ^ 2)) ∧
      Assumption1 ℒc (1 / 30) 2 e₁ (sc 1) e₁ e₂ e₂ δ ∧
      IsSimpRound ℒc (1 / 30) 0 2 e₁ (sc 1) e₁ e₂ e₂ e₁ (sc (16 / 15)) e₁ ∧
      avgLoss ℒc (e₁ * sc 1 * e₁ᵀ) < avgLoss ℒc (e₁ * sc (16 / 15) * e₁ᵀ) ∧
      ¬ (avgLoss ℒc (e₁ * sc (16 / 15) * e₁ᵀ) - avgLoss ℒc (e₁ * sc 1 * e₁ᵀ) ≤
        -(((2 : ℕ) : ℝ) * (1 / 30) * (1 - δ ^ 2 - 12 * (((2 : ℕ) : ℝ) * (1 / 30)) * 1 +
          δ ^ 2 * (((2 : ℕ) : ℝ) * (1 / 30)))) * ‖gradS (avgLoss ℒc) e₁ (sc 1) e₁ e₂ e₂‖ ^ 2 +
          1 * 0) ∧
      ¬ (‖gradS (avgLoss ℒc) e₁ (sc 1) e₁ e₂ e₂‖ ^ 2 ≤
        96 * 1 / ((1 : ℕ) : ℝ) * (avgLoss ℒc (e₁ * sc 1 * e₁ᵀ) -
          avgLoss ℒc (e₁ * sc (16 / 15) * e₁ᵀ)) + 96 * 1 ^ 2 * 0) := by
  set M : ℝ := 10000 / δ + 10 with hM
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  refine ⟨cxLoss M, isLSmooth_cxLoss M, by norm_num, ?_, ?_, ⟨orth_e, orth_e, ?_⟩, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    push_cast
    nlinarith
  · intro c s hs G hG
    rw [gradS_cx, norm_E00, mul_one]
    have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by omega
    rcases hs' with rfl | rfl | rfl
    · rw [simpClientIter_cx_zero]
      exact assumption1_row hδ0 (by norm_num) (by norm_num) (by norm_num) hG
    · rw [simpClientIter_cx_one]
      refine assumption1_row hδ0 (by norm_num) (by norm_num) ?_ hG
      cases c <;> norm_num [sgn]
    · rw [simpClientIter_cx_two]
      refine assumption1_row hδ0 (by norm_num) (by norm_num) ?_ hG
      cases c <;> norm_num [sgn, abs_le]
  · refine ⟨e₁, e₁, orth_e₁, orth_e₁, ?_, by rw [fromCols_e₁_e₂]; simp,
      by rw [fromCols_e₁_e₂]; simp⟩
    rw [simpRoundCoeff_cx, e₁_mul_transpose, sub_self, norm_zero]
  · rw [avgLoss_cx, avgLoss_cx]; norm_num
  · rw [avgLoss_cx, avgLoss_cx, gradS_cx, norm_E00]
    intro h
    push_cast at h
    nlinarith
  · rw [avgLoss_cx, avgLoss_cx, gradS_cx, norm_E00]
    norm_num

end Counterexamples

end LeanDLRA.Literature.P2406_17887
