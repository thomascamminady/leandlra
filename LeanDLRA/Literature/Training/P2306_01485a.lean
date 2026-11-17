import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.SVD
import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Curated.Classicalb
import LeanDLRA.Training.Descent

/-!
# Robust low-rank training via approximate orthonormal constraints (arXiv 2306.01485)

Savostianova, Zangrando, Ceruti and Tudisco train weights `W = U S Vᵀ` with `S ∈ Σ_s(ε)` (singular
values in `[s - ε, s + ε]`), to keep the condition number of the network small.  This module
proves the choice of `s` and `ε` (`secondMoment_isMin`, `eq_secondMoment_of_isMin`,
`choice_of_eps`, `singularValues_div_le`, `cond_lowRank_le`) and that line 9 of Algorithm 1 is a
nearest-point projection (`clamp_isNearest`); defines the condition number of a map and proves
Lemma 2 (`condAt_comp_le`, `condOn_comp_le`), Proposition 1 (`condOn_layerNet_le`, `proposition1`,
`condOn_layerNet_lowRank_le`) and the scalar activation bounds (`condOn_leakyReLU`,
`condOn_hardTanh`, `condOn_tanh_le`, `condOn_sigmoid_le`, `condOn_softplus_le`, `condOn_siLU_le`);
and proves Theorem 1 in the form its proof supports (`theorem1_frozen_gradient`,
`theorem1_one_step`, `theorem1_steps`) and for the actual flow under a Lipschitz gradient
(`theorem1_lipschitz`), together with counterexamples to the statements below.

## False statements of the paper, each refuted here

1. **Theorem 1 for `k` steps.**  `‖U_k S_k V_kᵀ - W(λ k)‖ ≤ 3 λ η` does not grow with `k` and fails
   for `k = 4`, for a linear loss: `theorem1_false_many_steps`.  The proof only treats `[0, λ]`.
2. **Theorem 1 for the flow (5), already for `k = 1`.**  The theorem has no Lipschitz hypothesis on
   `∇ℒ`, and the first line of its proof, `Ẏ = P(Y) Ẇ̃ + P(Y) Ė`, replaces `∇ℒ(Y)` by `∇ℒ(W(t))`.
   A polynomial loss, with `Y` stationary for (5) and for Algorithm 1, violates the bound:
   `theorem1_false_gradient_flow`.  What the proof does show is `theorem1_frozen_gradient`, for
   the frozen flow `Ẏ = -P(Y) ∇ℒ(W(t))`.
3. **Proposition 1 with `cond(W) = ‖W‖ ‖W⁺‖`**, and "when `f(x) = A x` we have
   `cond(f, x) = cond(A)`": every rank-deficient nonzero layer has `cond = ∞` on the whole space
   (`condOn_eq_top_of_ker`, `proposition1_false_with_pinv`).  This is the case of interest of the
   paper.  The bound holds with the condition numbers of the maps, as in the paper's proof
   (`proposition1`), and with `‖W‖ ‖W⁺‖` when the features lie in the row spaces
   (`condOn_layerNet_lowRank_le`).
4. **The activation part of Proposition 1 for vectors.**  The reduction of entrywise maps to one
   dimension fails: on `ℝ²` with the Euclidean norm, entrywise tanh, sigmoid and hard tanh have
   `cond = ∞` on the nonnegative orthant (`entrywise_activations_eq_top`).  The bounds of Appendix B
   are true for scalars.
5. **Two values of Appendix B.**  For the leaky ReLU `cond(σ) = max(α, 1)` is false for `α > 1`; the
   value is `1`, as Section 3 says (`condOn_leakyReLU_lt_appendix`).  For the hard tanh
   `cond(σ) ≤ a` is false for `a < 1`; the value is `1` (`condOn_hardTanh_ne_appendix`).

## Differences from the paper

* `cond` takes values in `[0, ∞]`, with `a / 0 = ∞` for `a ≠ 0` and `0 / 0 = 0`.  The limit `ε ↓ 0`
  is an infimum (`tendsto_condEps`).  Lemma 2 assumes finiteness, as the paper's proof does; this
  excludes the product `0 · ∞`.  Continuity of `φ` and finite dimension are not needed.
* Theorem 1 is stated for matrices with Frobenius norms.  "`W̃ ∈ ℳ_r ∩ Σ_s(ε)`" is
  `lowRankBand`; `s` and `ε` are constants.  Tangency of `Ẇ̃` is derived (`tangent_deriv`), and
  `W̃ = W - E` is differentiable by construction.  The paper's `E(0) = 0` is implicit; in general
  the term `‖E(0)‖` appears.  Exact integration is assumed as in the paper ("no numerical errors"),
  so the steps of Algorithm 1 are the flow, and `Y` is given with orthonormal factors along the
  trajectory.  `GaugeODE.factorODE_solution_isDLRA_tangentProj` and `factorFlow_eq` show that a
  solution of (5) has this form.
* The Riccati comparison uses a barrier instead of the paper's `tan`, and the curvature constant
  `2` of `Curvature.koch_lubich_normal`, `Curvature.koch_lubich_tangent_frob` instead of `32`.
  Lemma 1 of the paper is `Curvature.koch_lubich_tangent_frob`.
* Parts of the choice of `s` and `ε` reuse `LeanDLRA.norm_sub_bestMultiple_le` and
  `LeanDLRA.div_le_one_add_of_mem_Icc`.
* `clamp_isNearest` is not claimed in the paper beyond the word "project"; it is included since
  the algorithm relies on it.  It assumes that the SVD of `S` is given, which is the case in line 9.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix ENNReal

namespace LeanDLRA.Literature.P2306_01485

/-! ### Condition numbers of maps -/

section Condition

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]

/-- The relative error ratio `R(f, x; δ)` of eq. (1) of arXiv 2306.01485, in `[0, ∞]`. -/
noncomputable def relRatio (f : X → Y) (x δ : X) : ℝ≥0∞ :=
  (‖f (x + δ) - f x‖ₑ / ‖f x‖ₑ) / (‖δ‖ₑ / ‖x‖ₑ)

/-- `sup {R(f, x; δ) : δ ≠ 0, ‖δ‖ ≤ ε ‖x‖}`. -/
noncomputable def condEps (f : X → Y) (x : X) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ (δ : X) (_ : δ ≠ 0 ∧ ‖δ‖ ≤ ε * ‖x‖), relRatio f x δ

/-- The local condition number `cond(f; x) = lim_{ε ↓ 0} sup_{0 < ‖δ‖ ≤ ε ‖x‖} R(f, x; δ)`.  The
supremum is monotone in `ε`, so the limit is an infimum (`tendsto_condEps`). -/
noncomputable def condAt (f : X → Y) (x : X) : ℝ≥0∞ :=
  ⨅ (ε : ℝ) (_ : 0 < ε), condEps f x ε

/-- The global condition number `cond(f) = sup_{x ∈ 𝒳 \ {0}} cond(f; x)` on a feature space `𝒳`. -/
noncomputable def condOn (A : Set X) (f : X → Y) : ℝ≥0∞ :=
  ⨆ x ∈ A \ {0}, condAt f x

lemma condEps_mono (f : X → Y) (x : X) : Monotone (condEps f x) := fun _ _ h =>
  iSup₂_mono' fun δ hδ =>
    ⟨δ, ⟨hδ.1, hδ.2.trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))⟩, le_rfl⟩

/-- The infimum defining `condAt` is the limit `ε ↓ 0` of arXiv 2306.01485, Section 3. -/
theorem tendsto_condEps (f : X → Y) (x : X) :
    Tendsto (condEps f x) (𝓝[>] 0) (𝓝 (condAt f x)) := by
  have h := (condEps_mono f x).tendsto_nhdsGT 0
  rwa [sInf_image] at h

lemma condAt_le_condEps (f : X → Y) (x : X) {ε : ℝ} (hε : 0 < ε) :
    condAt f x ≤ condEps f x ε :=
  iInf₂_le ε hε

lemma relRatio_le_condEps (f : X → Y) {x δ : X} {ε : ℝ} (hδ : δ ≠ 0) (hle : ‖δ‖ ≤ ε * ‖x‖) :
    relRatio f x δ ≤ condEps f x ε :=
  le_iSup₂ (f := fun δ (_ : δ ≠ 0 ∧ ‖δ‖ ≤ ε * ‖x‖) => relRatio f x δ) δ ⟨hδ, hle⟩

lemma condAt_le_condOn {A : Set X} (f : X → Y) {x : X} (hx : x ∈ A \ {0}) :
    condAt f x ≤ condOn A f :=
  le_iSup₂ (f := fun x (_ : x ∈ A \ {0}) => condAt f x) x hx

lemma condAt_id_le (x : X) : condAt id x ≤ 1 := by
  refine (condAt_le_condEps _ _ one_pos).trans (iSup₂_le fun δ _ => ?_)
  have : relRatio id x δ = (‖δ‖ₑ / ‖x‖ₑ) / (‖δ‖ₑ / ‖x‖ₑ) := by simp [relRatio]
  rw [this]
  exact ENNReal.div_self_le_one

lemma condOn_id_le (A : Set X) : condOn A (id : X → X) ≤ 1 :=
  iSup₂_le fun x _ => condAt_id_le x

/-- The factorization of the proof of Lemma 2 of arXiv 2306.01485. -/
lemma relRatio_comp {φ : Y → Z} {ψ : X → Y} {x δ : X} (hy : ψ x ≠ 0)
    (hη : ψ (x + δ) - ψ x ≠ 0) :
    relRatio (φ ∘ ψ) x δ = relRatio φ (ψ x) (ψ (x + δ) - ψ x) * relRatio ψ x δ := by
  have e : ψ x + (ψ (x + δ) - ψ x) = ψ (x + δ) := by abel
  simp only [relRatio, Function.comp_apply, e]
  have h0 : ‖ψ (x + δ) - ψ x‖ₑ / ‖ψ x‖ₑ ≠ 0 :=
    ENNReal.div_ne_zero.2 ⟨eNorm_ne_zero.2 hη, eNorm_ne_top⟩
  have ht : ‖ψ (x + δ) - ψ x‖ₑ / ‖ψ x‖ₑ ≠ ∞ :=
    ENNReal.div_ne_top eNorm_ne_top (eNorm_ne_zero.2 hy)
  generalize ‖ψ (x + δ) - ψ x‖ₑ / ‖ψ x‖ₑ = h at h0 ht
  rw [div_eq_mul_inv _ h, div_eq_mul_inv h, mul_assoc, ← mul_assoc h⁻¹,
    ENNReal.inv_mul_cancel h0 ht, one_mul, div_eq_mul_inv]

/-- One perturbation size: the estimate behind Lemma 2. -/
lemma condAt_comp_le_condEps {φ : Y → Z} {ψ : X → Y} {x : X} (hx : x ≠ 0) (hy : ψ x ≠ 0)
    (hψ : ContinuousAt ψ x) {ε : ℝ} (hε : 0 < ε) :
    condAt (φ ∘ ψ) x ≤ condEps φ (ψ x) ε * condEps ψ x ε := by
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hyp : 0 < ‖ψ x‖ := norm_pos_iff.2 hy
  obtain ⟨ρ, hρ, hc⟩ := Metric.continuousAt_iff.1 hψ (ε * ‖ψ x‖) (by positivity)
  set ε' : ℝ := min ε (ρ / (2 * ‖x‖)) with hε'
  have hε'p : 0 < ε' := lt_min hε (by positivity)
  refine (condAt_le_condEps _ _ hε'p).trans (iSup₂_le fun δ hδ => ?_)
  have h1 : ‖δ‖ ≤ ε * ‖x‖ :=
    hδ.2.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg x))
  have h2 : ‖δ‖ < ρ := by
    have : ε' * ‖x‖ ≤ ρ / (2 * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg x)
    have e : ρ / (2 * ‖x‖) * ‖x‖ = ρ / 2 := by field_simp
    linarith [hδ.2]
  by_cases hη : ψ (x + δ) - ψ x = 0
  · have e : ψ (x + δ) = ψ x := sub_eq_zero.1 hη
    have : relRatio (φ ∘ ψ) x δ = 0 := by simp [relRatio, e]
    rw [this]
    exact zero_le
  · rw [relRatio_comp hy hη]
    have h3 : ‖ψ (x + δ) - ψ x‖ ≤ ε * ‖ψ x‖ := by
      have := hc (x := x + δ) (by simpa [dist_eq_norm] using h2)
      rw [dist_eq_norm] at this
      exact this.le
    exact mul_le_mul' (relRatio_le_condEps φ hη h3) (relRatio_le_condEps ψ hδ.1 h1)

/-- If `ψ x = 0` and `cond(ψ; x) < ∞`, then `ψ` vanishes near `x`, so `φ ∘ ψ` is locally constant
and `cond(φ ∘ ψ; x) = 0`. -/
lemma condAt_comp_eq_zero {φ : Y → Z} {ψ : X → Y} {x : X} (hx : x ≠ 0) (hy : ψ x = 0)
    (h₁ : condAt ψ x ≠ ∞) : condAt (φ ∘ ψ) x = 0 := by
  obtain ⟨ε, hε, hlt⟩ : ∃ ε : ℝ, 0 < ε ∧ condEps ψ x ε < ∞ := by
    have := lt_top_iff_ne_top.2 h₁
    simpa [condAt, iInf_lt_iff] using this
  refine le_antisymm ((condAt_le_condEps _ _ hε).trans (iSup₂_le fun δ hδ => ?_)) (zero_le)
  have hxp : ‖x‖ₑ ≠ 0 := eNorm_ne_zero.2 hx
  by_cases h : ψ (x + δ) = 0
  · simp [relRatio, h, hy]
  · exfalso
    have h2 := (relRatio_le_condEps ψ hδ.1 hδ.2).trans_lt hlt
    have h3 : relRatio ψ x δ = ∞ := by
      have hne : ‖δ‖ₑ / ‖x‖ₑ ≠ ∞ := ENNReal.div_ne_top eNorm_ne_top hxp
      simp only [relRatio, hy, sub_zero, eNorm_zero]
      rw [ENNReal.div_zero (eNorm_ne_zero.2 h), ENNReal.top_div_of_ne_top hne]
    rw [h3] at h2
    exact lt_irrefl _ h2

/-- **Lemma 2 of arXiv 2306.01485, pointwise form**: `cond(φ ∘ ψ; x) ≤ cond(φ; ψ x) cond(ψ; x)`
at `x ≠ 0` when `ψ` is continuous at `x` and both factors are finite (the paper's standing
hypothesis: "by hypothesis, `cond(φ)` and `cond(ψ)` are finite").  The finiteness is needed only
to exclude the product `0 · ∞`.  Spaces are arbitrary normed groups, not necessarily
finite-dimensional, and `φ` need not be continuous. -/
theorem condAt_comp_le {φ : Y → Z} {ψ : X → Y} {x : X} (hx : x ≠ 0) (hψ : ContinuousAt ψ x)
    (h₁ : condAt ψ x ≠ ∞) (h₂ : condAt φ (ψ x) ≠ ∞) :
    condAt (φ ∘ ψ) x ≤ condAt φ (ψ x) * condAt ψ x := by
  by_cases hy : ψ x = 0
  · rw [condAt_comp_eq_zero hx hy h₁]
    exact zero_le
  · have lim := ENNReal.Tendsto.mul (tendsto_condEps φ (ψ x)) (Or.inr h₁) (tendsto_condEps ψ x)
      (Or.inr h₂)
    exact ge_of_tendsto lim
      (eventually_mem_nhdsWithin.mono fun ε hε => condAt_comp_le_condEps hx hy hψ hε)

/-- **Lemma 2 of arXiv 2306.01485**: `cond(φ ∘ ψ) ≤ cond(φ) cond(ψ)`, for the global condition
numbers on feature sets `A` and `B` with `ψ(A) ⊆ B`.  Paper: `A`, `B` are the whole spaces, and the
maps are continuous maps between finite-dimensional Banach spaces with finite condition numbers. -/
theorem condOn_comp_le {φ : Y → Z} {ψ : X → Y} {A : Set X} {B : Set Y} (hmaps : MapsTo ψ A B)
    (hψ : ∀ x ∈ A \ {0}, ContinuousAt ψ x) (h₁ : condOn A ψ ≠ ∞) (h₂ : condOn B φ ≠ ∞) :
    condOn A (φ ∘ ψ) ≤ condOn B φ * condOn A ψ := by
  refine iSup₂_le fun x hx => ?_
  have hx0 : x ≠ 0 := hx.2
  have hxA := condAt_le_condOn ψ hx
  have hfin : condAt ψ x ≠ ∞ := ne_top_of_le_ne_top h₁ hxA
  by_cases hy : ψ x = 0
  · rw [condAt_comp_eq_zero hx0 hy hfin]
    exact zero_le
  · have hyB : ψ x ∈ B \ {0} := ⟨hmaps hx.1, hy⟩
    have hyA := condAt_le_condOn φ hyB
    exact (condAt_comp_le hx0 (hψ x hx) hfin (ne_top_of_le_ne_top h₂ hyA)).trans
      (mul_le_mul' hyA hxA)

end Condition

section Network

variable {E F : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]

/-- A feed-forward network `z_{i+1} = σ_i(T_i z_i)`, truncated to its first `n` layers, as a
function of the input `z_0`. -/
def layerNet (T : ∀ i, E i → F i) (σ : ∀ i, F i → E (i + 1)) : ∀ n, E 0 → E n
  | 0 => id
  | n + 1 => σ n ∘ T n ∘ layerNet T σ n

lemma continuous_layerNet {T : ∀ i, E i → F i} {σ : ∀ i, F i → E (i + 1)}
    (hT : ∀ i, Continuous (T i)) (hσ : ∀ i, Continuous (σ i)) (n : ℕ) :
    Continuous (layerNet T σ n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact (hσ n).comp ((hT n).comp ih)

omit [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)] in
lemma mapsTo_layerNet {T : ∀ i, E i → F i} {σ : ∀ i, F i → E (i + 1)} {Z : ∀ i, Set (E i)}
    {A : ∀ i, Set (F i)} {n : ℕ} (hZ : ∀ i < n, MapsTo (T i) (Z i) (A i))
    (hA : ∀ i < n, MapsTo (σ i) (A i) (Z (i + 1))) :
    MapsTo (layerNet T σ n) (Z 0) (Z n) := by
  induction n with
  | zero => exact mapsTo_id _
  | succ n ih =>
    exact (hA n (by omega)).comp ((hZ n (by omega)).comp
      (ih (fun i hi => hZ i (by omega)) (fun i hi => hA i (by omega))))

/-- **Proposition 1 of arXiv 2306.01485**, general form: for a feed-forward network
`z_{i+1} = σ_i(T_i z_i)`, `i < L`, with continuous layers, and for feature sets `Z i` of the inputs
of `T_i` and `A i` of the inputs of `σ_i`, stable under the layers,
`cond(f) ≤ ∏_i cond(σ_i) ∏_i cond(T_i)`.  Here `cond(T_i)` is the condition number of the *map*
`T_i`, as in the paper's proof; see `condOn_eq_top_of_ker` for why it cannot be replaced by
`‖W‖ ‖W⁺‖` on the whole space.  The finiteness hypotheses are those of the paper. -/
theorem condOn_layerNet_le {T : ∀ i, E i → F i} {σ : ∀ i, F i → E (i + 1)}
    (hT : ∀ i, Continuous (T i)) (hσ : ∀ i, Continuous (σ i)) {Z : ∀ i, Set (E i)}
    {A : ∀ i, Set (F i)} (L : ℕ) (hZ : ∀ i < L, MapsTo (T i) (Z i) (A i))
    (hA : ∀ i < L, MapsTo (σ i) (A i) (Z (i + 1)))
    (hTf : ∀ i < L, condOn (Z i) (T i) ≠ ∞) (hσf : ∀ i < L, condOn (A i) (σ i) ≠ ∞) :
    condOn (Z 0) (layerNet T σ L) ≤
      (∏ i ∈ Finset.range L, condOn (A i) (σ i)) * ∏ i ∈ Finset.range L, condOn (Z i) (T i) := by
  induction L with
  | zero =>
    have e : layerNet T σ 0 = id := rfl
    simpa [e] using condOn_id_le (Z 0)
  | succ L ih =>
    have ih' := ih (fun i hi => hZ i (by omega)) (fun i hi => hA i (by omega))
      (fun i hi => hTf i (by omega)) (fun i hi => hσf i (by omega))
    have hmaps : MapsTo (layerNet T σ L) (Z 0) (Z L) :=
      mapsTo_layerNet (fun i hi => hZ i (by omega)) (fun i hi => hA i (by omega))
    have hprod : (∏ i ∈ Finset.range L, condOn (A i) (σ i)) *
        ∏ i ∈ Finset.range L, condOn (Z i) (T i) ≠ ∞ :=
      ENNReal.mul_ne_top
        (ENNReal.prod_ne_top fun i hi => hσf i (by simp at hi; omega))
        (ENNReal.prod_ne_top fun i hi => hTf i (by simp at hi; omega))
    have hψ := ne_top_of_le_ne_top hprod ih'
    have hcont := continuous_layerNet hT hσ L
    have h1 := condOn_comp_le (φ := T L) (hmaps := hmaps)
      (fun x _ => hcont.continuousAt) hψ (hTf L (by omega))
    have h1f : condOn (Z 0) (T L ∘ layerNet T σ L) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (hTf L (by omega)) hψ) h1
    have h2 := condOn_comp_le (φ := σ L) (hmaps := (hZ L (by omega)).comp hmaps)
      (fun x _ => ((hT L).comp hcont).continuousAt) h1f (hσf L (by omega))
    have e : layerNet T σ (L + 1) = σ L ∘ (T L ∘ layerNet T σ L) := rfl
    rw [e, Finset.prod_range_succ, Finset.prod_range_succ]
    calc condOn (Z 0) (σ L ∘ (T L ∘ layerNet T σ L))
        ≤ condOn (A L) (σ L) * condOn (Z 0) (T L ∘ layerNet T σ L) := h2
      _ ≤ condOn (A L) (σ L) * (condOn (Z L) (T L) * condOn (Z 0) (layerNet T σ L)) := by
          gcongr
      _ ≤ condOn (A L) (σ L) * (condOn (Z L) (T L) *
            ((∏ i ∈ Finset.range L, condOn (A i) (σ i)) *
              ∏ i ∈ Finset.range L, condOn (Z i) (T i))) := by
          gcongr
      _ = _ := by ring

end Network

/-- **Proposition 1 of arXiv 2306.01485**, for matrices: for the network
`z_{i+1} = σ_i(W_i z_i)`, `i < L`, on `ℝ^{d_0}` with continuous activations and finite condition
numbers, `cond(f) ≤ ∏_i sup_{x ≠ 0} cond(σ_i; x) ∏_i cond(W_i)`, where `cond(W_i)` is the condition
number of the map `x ↦ W_i x`, as in the paper's proof.  (`condOn_layerNet_le` allows feature sets.)
For the matrix condition number `‖W‖ ‖W⁺‖` see `proposition1_false_with_pinv`. -/
theorem proposition1 {d : ℕ → ℕ} (W : ∀ i, Matrix (Fin (d (i + 1))) (Fin (d i)) ℝ)
    {σ : ∀ i, EuclideanSpace ℝ (Fin (d (i + 1))) → EuclideanSpace ℝ (Fin (d (i + 1)))}
    (hσ : ∀ i, Continuous (σ i)) (L : ℕ)
    (hW : ∀ i < L, condOn univ (Matrix.toEuclideanLin (W i)) ≠ ∞)
    (hσf : ∀ i < L, condOn univ (σ i) ≠ ∞) :
    condOn univ (layerNet (E := fun i => EuclideanSpace ℝ (Fin (d i)))
        (F := fun i => EuclideanSpace ℝ (Fin (d (i + 1))))
        (fun i => Matrix.toEuclideanLin (W i)) σ L) ≤
      (∏ i ∈ Finset.range L, condOn univ (σ i)) *
        ∏ i ∈ Finset.range L, condOn univ (Matrix.toEuclideanLin (W i)) :=
  condOn_layerNet_le (E := fun i => EuclideanSpace ℝ (Fin (d i)))
    (F := fun i => EuclideanSpace ℝ (Fin (d (i + 1))))
    (T := fun i => Matrix.toEuclideanLin (W i)) (σ := σ) (Z := fun _ => univ) (A := fun _ => univ)
    (fun i => (Matrix.toEuclideanLin (W i)).continuous_of_finiteDimensional) hσ L
    (fun _ _ => mapsTo_univ _ _) (fun _ _ => mapsTo_univ _ _) hW hσf

/-! ### Linear layers -/

section Linear

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ X]
  [NormedSpace ℝ Y]

/-- For a linear map, `cond(T; x) ≤ ‖T‖ ‖x‖ / ‖T x‖`, with an upper bound `b` for `‖T‖`. -/
lemma condAt_linear_le (T : X →ₗ[ℝ] Y) {b : ℝ} (hup : ∀ v, ‖T v‖ ≤ b * ‖v‖) (hb : 0 ≤ b) {x : X}
    (hx : x ≠ 0) : condAt T x ≤ ENNReal.ofReal b * ‖x‖ₑ / ‖T x‖ₑ := by
  refine (condAt_le_condEps _ _ one_pos).trans (iSup₂_le fun δ hδ => ?_)
  have hd0 : ‖δ‖ₑ ≠ 0 := eNorm_ne_zero.2 hδ.1
  have hx0 : ‖x‖ₑ ≠ 0 := eNorm_ne_zero.2 hx
  have h1 : ‖T δ‖ₑ ≤ ENNReal.ofReal b * ‖δ‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hb]
    exact ENNReal.ofReal_le_ofReal (hup δ)
  have e : T (x + δ) - T x = T δ := by rw [map_add, add_sub_cancel_left]
  simp only [relRatio, e]
  calc ‖T δ‖ₑ / ‖T x‖ₑ / (‖δ‖ₑ / ‖x‖ₑ)
      ≤ ENNReal.ofReal b * ‖δ‖ₑ / ‖T x‖ₑ / (‖δ‖ₑ / ‖x‖ₑ) := by gcongr
    _ = ENNReal.ofReal b * ‖x‖ₑ / ‖T x‖ₑ := by
        rw [ENNReal.div_eq_inv_mul (b := ‖δ‖ₑ / ‖x‖ₑ),
          ENNReal.inv_div (Or.inr eNorm_ne_top) (Or.inr hd0), ENNReal.div_eq_inv_mul,
          ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        calc ‖δ‖ₑ⁻¹ * ‖x‖ₑ * ((‖T x‖ₑ)⁻¹ * (ENNReal.ofReal b * ‖δ‖ₑ))
            = (‖δ‖ₑ⁻¹ * ‖δ‖ₑ) * ((‖T x‖ₑ)⁻¹ * (ENNReal.ofReal b * ‖x‖ₑ)) := by ring
          _ = _ := by rw [ENNReal.inv_mul_cancel hd0 eNorm_ne_top, one_mul]

/-- **The linear case of Section 3 of arXiv 2306.01485**: if `‖T v‖ ≤ b ‖v‖` for all `v` and
`a ‖x‖ ≤ ‖T x‖` on the feature set `A`, `a > 0`, then `cond(T) ≤ b / a` on `A`.  With `b = s_max`
and `a = s_min` this is `cond(x ↦ W x) ≤ s_max(W) / s_min(W)` on the orthogonal complement of the
kernel of `W`.  Off this complement the bound fails: `condOn_eq_top_of_ker`. -/
theorem condOn_linear_le (T : X →ₗ[ℝ] Y) {a b : ℝ} (hup : ∀ v, ‖T v‖ ≤ b * ‖v‖) (hb : 0 ≤ b)
    (ha : 0 < a) {A : Set X} (hlow : ∀ x ∈ A, a * ‖x‖ ≤ ‖T x‖) :
    condOn A T ≤ ENNReal.ofReal (b / a) := by
  refine iSup₂_le fun x hx => ?_
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx.2
  have hT : 0 < ‖T x‖ := lt_of_lt_of_le (by positivity) (hlow x hx.1)
  refine (condAt_linear_le T hup hb hx.2).trans ?_
  rw [← ofReal_norm x, ← ofReal_norm (T x), ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_div_of_pos hT]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ hT ha]
  nlinarith [hlow x hx.1]

/-- At a nonzero kernel vector of a nonzero linear map the local condition number of arXiv
2306.01485 is infinite: the perturbation `δ` is compared with `f(x) = 0`. -/
theorem condAt_eq_top_of_ker (T : X →ₗ[ℝ] Y) (hT : T ≠ 0) {x : X} (hx : x ≠ 0) (hTx : T x = 0) :
    condAt T x = ∞ := by
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
    by_contra! h
    exact hT (LinearMap.ext h)
  have hv0 : v ≠ 0 := fun h => hv (by simp [h])
  have hvp : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine top_le_iff.1 (le_iInf₂ fun ε hε => ?_)
  set c : ℝ := ε * ‖x‖ / ‖v‖ with hc
  have hc0 : 0 < c := by positivity
  have hδ : c • v ≠ 0 := smul_ne_zero hc0.ne' hv0
  have hle : ‖c • v‖ ≤ ε * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc0.le, hc]
    exact (div_mul_cancel₀ _ hvp.ne').le
  refine le_trans ?_ (relRatio_le_condEps T hδ hle)
  have hTδ : T (x + c • v) = c • T v := by simp [hTx]
  have hne : ‖c • v‖ₑ / ‖x‖ₑ ≠ ∞ := ENNReal.div_ne_top eNorm_ne_top (eNorm_ne_zero.2 hx)
  have e : relRatio T x (c • v) = ‖c • T v‖ₑ / 0 / (‖c • v‖ₑ / ‖x‖ₑ) := by
    simp only [relRatio, hTδ, hTx, sub_zero, eNorm_zero]
  rw [e, ENNReal.div_zero (eNorm_ne_zero.2 (smul_ne_zero hc0.ne' hv)),
    ENNReal.top_div_of_ne_top hne]

/-- **A rank-deficient layer has infinite condition number on the whole space**: if `A` contains
a nonzero kernel vector of a nonzero linear map `T`, then `cond(T) = ∞` on `A`.  This contradicts
the sentence "when `f(x) = A x` we have `cond(f, x) = cond(A)`" of arXiv 2306.01485, Section 3, for
the paper's `cond(A) = ‖A‖ ‖A⁺‖`, which is finite (`proposition1_false_with_pinv`). -/
theorem condOn_eq_top_of_ker (T : X →ₗ[ℝ] Y) (hT : T ≠ 0) {A : Set X} {x : X} (hxA : x ∈ A)
    (hx : x ≠ 0) (hTx : T x = 0) : condOn A T = ∞ :=
  top_le_iff.1 ((condAt_eq_top_of_ker T hT hx hTx).ge.trans (condAt_le_condOn _ ⟨hxA, hx⟩))

end Linear

/-! ### Activation functions (scalar case) -/

section Activations

lemma relRatio_real {σ : ℝ → ℝ} {x δ : ℝ} (hx : x ≠ 0) (hδ : δ ≠ 0) (hσ : σ x ≠ 0) :
    relRatio σ x δ = ENNReal.ofReal (|δ⁻¹ • (σ (x + δ) - σ x)| * |x| / |σ x|) := by
  have hx' : 0 < |x| := abs_pos.2 hx
  have hδ' : 0 < |δ| := abs_pos.2 hδ
  have hσ' : 0 < |σ x| := abs_pos.2 hσ
  simp only [relRatio, Real.eNorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_div_of_pos hσ', ← ENNReal.ofReal_div_of_pos hx',
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  rw [smul_eq_mul, abs_mul, abs_inv]
  field_simp

/-- If `R(σ, x; δ) → L` as `δ → 0`, then `cond(σ; x) = L`. -/
lemma condAt_eq_of_tendsto {σ : ℝ → ℝ} {x : ℝ} {L : ℝ≥0∞} (hx : x ≠ 0)
    (h : Tendsto (relRatio σ x) (𝓝[≠] 0) (𝓝 L)) : condAt σ x = L := by
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
    have hev := h.eventually (Iio_mem_nhds ha)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, hball⟩ := hev
    refine (condAt_le_condEps _ _ (ε := r / (2 * ‖x‖)) (by positivity)).trans
      (iSup₂_le fun δ hδ => ?_)
    have hδr : ‖δ‖ < r := by
      have e : r / (2 * ‖x‖) * ‖x‖ = r / 2 := by field_simp
      linarith [hδ.2]
    exact (hball (by simpa [dist_eq_norm] using hδr) hδ.1).le
  · refine le_iInf₂ fun ε hε => le_of_tendsto h ?_
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨ε * ‖x‖, by positivity, fun δ hδ hδ0 => relRatio_le_condEps σ hδ0 ?_⟩
    have : ‖δ‖ < ε * ‖x‖ := by simpa [dist_eq_norm] using hδ
    exact this.le

/-- **The scalar formula of arXiv 2306.01485, Section 3**: for `σ` differentiable at `x ≠ 0` with
`σ x ≠ 0`, `cond(σ; x) = |σ'(x)| |x| / |σ(x)|`. -/
theorem condAt_eq_of_hasDerivAt {σ : ℝ → ℝ} {d x : ℝ} (h : HasDerivAt σ d x) (hx : x ≠ 0)
    (hσ : σ x ≠ 0) : condAt σ x = ENNReal.ofReal (|d| * |x| / |σ x|) := by
  refine condAt_eq_of_tendsto hx ?_
  have hs := hasDerivAt_iff_tendsto_slope_zero.1 h
  have h2 : Tendsto (fun t : ℝ => ENNReal.ofReal (|t⁻¹ • (σ (x + t) - σ x)| * |x| / |σ x|))
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (|d| * |x| / |σ x|))) :=
    ENNReal.tendsto_ofReal ((hs.abs.mul_const _).div_const _)
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (relRatio_real hx ht hσ).symm

/-- At a point where `σ` is `c`-Lipschitz, `cond(σ; x) ≤ c |x| / |σ(x)|`. -/
lemma condAt_le_of_lipschitz {σ : ℝ → ℝ} {x c : ℝ} (hx : x ≠ 0) (hσ : σ x ≠ 0)
    (h : ∀ δ, |σ (x + δ) - σ x| ≤ c * |δ|) :
    condAt σ x ≤ ENNReal.ofReal (c * |x| / |σ x|) := by
  refine (condAt_le_condEps _ _ one_pos).trans (iSup₂_le fun δ hδ => ?_)
  rw [relRatio_real hx hδ.1 hσ]
  refine ENNReal.ofReal_le_ofReal ?_
  have hδ' : 0 < |δ| := abs_pos.2 hδ.1
  have : |δ⁻¹ • (σ (x + δ) - σ x)| ≤ c := by
    rw [smul_eq_mul, abs_mul, abs_inv, inv_mul_le_iff₀ hδ']
    linarith [h δ]
  gcongr

/-- The leaky ReLU `σ(x) = max{0, x} + α min{0, x}` of Appendix B of arXiv 2306.01485. -/
noncomputable def leakyReLU (α x : ℝ) : ℝ := max 0 x + α * min 0 x

/-- `cond(σ; x) = 1` for the leaky ReLU of arXiv 2306.01485 with slope `α > 0`, at each `x ≠ 0`. -/
theorem condAt_leakyReLU {α x : ℝ} (hα : 0 < α) (hx : x ≠ 0) : condAt (leakyReLU α) x = 1 := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd : HasDerivAt (leakyReLU α) α x := by
      have h0 : HasDerivAt (fun y => α * y) α x := by simpa using (hasDerivAt_id x).const_mul α
      refine h0.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hneg] with y hy
      have hy' : y < 0 := hy
      simp [leakyReLU, max_eq_left hy'.le, min_eq_right hy'.le]
    have hv : leakyReLU α x = α * x := by
      simp [leakyReLU, max_eq_left hneg.le, min_eq_right hneg.le]
    rw [condAt_eq_of_hasDerivAt hd hx (by rw [hv]; exact mul_ne_zero hα.ne' hx), hv, abs_mul]
    have : |α| * |x| / (|α| * |x|) = 1 :=
      div_self (mul_ne_zero (abs_ne_zero.2 hα.ne') (abs_ne_zero.2 hx))
    rw [this, ENNReal.ofReal_one]
  · have hd : HasDerivAt (leakyReLU α) 1 x := by
      refine (hasDerivAt_id x).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      have hy' : 0 < y := hy
      simp [leakyReLU, max_eq_right hy'.le, min_eq_left hy'.le]
    have hv : leakyReLU α x = x := by
      simp [leakyReLU, max_eq_right hpos.le, min_eq_left hpos.le]
    rw [condAt_eq_of_hasDerivAt hd hx (by rw [hv]; exact hx), hv, abs_one, one_mul,
      div_self (abs_ne_zero.2 hx), ENNReal.ofReal_one]

/-- **Leaky ReLU** (arXiv 2306.01485, Section 3): `cond(σ) = 1` on `ℝ \ {0}` for slope `α > 0`.
Appendix B states `cond(σ) = max(α, 1)` instead, which is false for `α > 1`
(`condOn_leakyReLU_lt_appendix`). -/
theorem condOn_leakyReLU {α : ℝ} (hα : 0 < α) : condOn univ (leakyReLU α) = 1 := by
  apply le_antisymm
  · exact iSup₂_le fun x hx => (condAt_leakyReLU hα hx.2).le
  · rw [← condAt_leakyReLU hα (one_ne_zero)]
    exact condAt_le_condOn _ ⟨mem_univ _, one_ne_zero⟩

/-- The value `cond(σ) = max(α, 1)` of Appendix B of arXiv 2306.01485 for the leaky ReLU is wrong
for `α > 1`: the true value is `1`.  It is only an upper bound. -/
theorem condOn_leakyReLU_lt_appendix {α : ℝ} (hα : 1 < α) :
    condOn univ (leakyReLU α) < ENNReal.ofReal (max α 1) := by
  rw [condOn_leakyReLU (by linarith), max_eq_left hα.le, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hα

/-- The hard tanh of Appendix B of arXiv 2306.01485:
`σ(x) = a 𝟙_{x > a} - a 𝟙_{x < -a} + x 𝟙_{x ∈ [-a, a]}`. -/
noncomputable def hardTanh (a x : ℝ) : ℝ := if a < x then a else if x < -a then -a else x

lemma hardTanh_of_mem {a x : ℝ} (h₁ : -a ≤ x) (h₂ : x ≤ a) : hardTanh a x = x := by
  simp [hardTanh, not_lt.2 h₁, not_lt.2 h₂]

lemma abs_hardTanh_le {a : ℝ} (ha : 0 < a) (x : ℝ) : |hardTanh a x| ≤ a := by
  rw [abs_le]
  simp only [hardTanh]
  split_ifs <;> constructor <;> linarith

lemma abs_hardTanh_sub_le {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    |hardTanh a y - hardTanh a x| ≤ |y - x| := by
  have h1 := le_abs_self (y - x)
  have h2 := neg_abs_le (y - x)
  rw [abs_le]
  simp only [hardTanh]
  split_ifs <;> constructor <;> linarith

lemma hasDerivAt_hardTanh {a x : ℝ} (h₁ : -a < x) (h₂ : x < a) : HasDerivAt (hardTanh a) 1 x := by
  refine (hasDerivAt_id x).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds h₁ h₂] with y hy
  exact hardTanh_of_mem hy.1.le hy.2.le

lemma condAt_hardTanh_le {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) : condAt (hardTanh a) x ≤ 1 := by
  by_cases h₁ : a < x
  · have hd : HasDerivAt (hardTanh a) 0 x := by
      refine (hasDerivAt_const x a).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h₁] with y hy
      simp [hardTanh, show a < y from hy]
    rw [condAt_eq_of_hasDerivAt hd hx (by
      rw [show hardTanh a x = a by simp [hardTanh, h₁]]; exact ha.ne')]
    simp
  by_cases h₂ : x < -a
  · have hd : HasDerivAt (hardTanh a) 0 x := by
      refine (hasDerivAt_const x (-a)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h₂] with y hy
      have hy' : y < -a := hy
      simp [hardTanh, hy', not_lt.2 (show y ≤ a by linarith)]
    rw [condAt_eq_of_hasDerivAt hd hx (by
      rw [show hardTanh a x = -a by simp [hardTanh, h₁, h₂]]; exact neg_ne_zero.2 ha.ne')]
    simp
  · have hv : hardTanh a x = x := hardTanh_of_mem (not_lt.1 h₂) (not_lt.1 h₁)
    refine (condAt_le_of_lipschitz (c := 1) hx (by rw [hv]; exact hx) fun δ => ?_).trans ?_
    · simpa using abs_hardTanh_sub_le ha x (x + δ)
    · rw [hv, one_mul, div_self (abs_ne_zero.2 hx), ENNReal.ofReal_one]

/-- **Hard tanh**: `cond(σ) = 1` on `ℝ \ {0}`, for every `a > 0`.  Appendix B of arXiv 2306.01485
states `cond(σ) ≤ sup |x| / |σ(x)| = a`, which is an arithmetic slip (`|σ(x)| = |x|` on `[-a, a]`):
see `condOn_hardTanh_ne_appendix`. -/
theorem condOn_hardTanh {a : ℝ} (ha : 0 < a) : condOn univ (hardTanh a) = 1 := by
  apply le_antisymm
  · exact iSup₂_le fun x hx => condAt_hardTanh_le ha hx.2
  · have hx : a / 2 ≠ 0 := by positivity
    have hd := hasDerivAt_hardTanh (a := a) (x := a / 2) (by linarith) (by linarith)
    have hv : hardTanh a (a / 2) = a / 2 := hardTanh_of_mem (by linarith) (by linarith)
    have h1 : condAt (hardTanh a) (a / 2) = 1 := by
      rw [condAt_eq_of_hasDerivAt hd hx (by rw [hv]; exact hx), hv, abs_one, one_mul,
        div_self (abs_ne_zero.2 hx), ENNReal.ofReal_one]
    rw [← h1]
    exact condAt_le_condOn _ ⟨mem_univ _, hx⟩

/-- The value `a` of Appendix B of arXiv 2306.01485 for the hard tanh is wrong unless `a = 1`. -/
theorem condOn_hardTanh_ne_appendix {a : ℝ} (ha : 0 < a) (h1 : a ≠ 1) :
    condOn univ (hardTanh a) ≠ ENNReal.ofReal a := by
  rw [condOn_hardTanh ha, ← ENNReal.ofReal_one]
  exact fun h => h1 ((ENNReal.ofReal_eq_ofReal_iff zero_le_one ha.le).1 h).symm

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have e : Real.sinh / Real.cosh = Real.tanh :=
    funext fun y => (Real.tanh_eq_sinh_div_cosh y).symm
  have e2 : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    nlinarith [Real.cosh_sq x]
  rwa [e, e2] at h

lemma abs_tanh_le (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x), Real.abs_sinh,
    div_le_one (Real.cosh_pos x), ← Real.cosh_abs x]
  exact (Real.sinh_lt_cosh _).le

/-- **Tanh** (Appendix B of arXiv 2306.01485): `cond(σ) ≤ 1` on `ℝ \ {0}`.  (The paper's `= 1`
concerns the continuous extension to `x = 0`, which is excluded here.) -/
theorem condOn_tanh_le : condOn univ Real.tanh ≤ 1 := by
  refine iSup₂_le fun x hx => ?_
  have hx0 : x ≠ 0 := hx.2
  have hs : Real.sinh x ≠ 0 := by simpa [Real.sinh_eq_zero] using hx0
  have hc := Real.cosh_pos x
  have ht : Real.tanh x ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero hs hc.ne'
  rw [condAt_eq_of_hasDerivAt (hasDerivAt_tanh x) hx0 ht, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS : 0 < |Real.sinh x| := abs_pos.2 hs
  have h1 : |x| ≤ |Real.sinh x| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.2 (abs_nonneg x)
  have hc1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  rw [Real.tanh_eq_sinh_div_cosh, abs_div (Real.sinh x), abs_of_pos hc,
    abs_of_pos (show 0 < 1 / Real.cosh x ^ 2 by positivity), div_le_one (by positivity)]
  have e : 1 / Real.cosh x ^ 2 * |x| = |x| / Real.cosh x ^ 2 := by ring
  rw [e, div_le_div_iff₀ (by positivity) hc]
  have h2 : |x| * Real.cosh x ≤ |Real.sinh x| * Real.cosh x :=
    mul_le_mul_of_nonneg_right h1 hc.le
  have h3 := mul_nonneg (mul_nonneg hS.le hc.le) (sub_nonneg.2 hc1)
  nlinarith

/-- The logistic sigmoid `σ(x) = (1 + e^{-x})⁻¹`. -/
noncomputable def sigmoid (x : ℝ) : ℝ := (1 + Real.exp (-x))⁻¹

lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := inv_pos.2 (by positivity)

lemma sigmoid_le_one (x : ℝ) : sigmoid x ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith [Real.exp_pos (-x)])

lemma one_sub_sigmoid_le (x : ℝ) : 1 - sigmoid x ≤ Real.exp (-x) := by
  have h := Real.exp_pos (-x)
  have e : 1 - sigmoid x = Real.exp (-x) * sigmoid x := by
    simp only [sigmoid]
    field_simp
    ring
  rw [e]
  exact mul_le_of_le_one_right h.le (sigmoid_le_one x)

lemma one_sub_sigmoid_nonneg (x : ℝ) : 0 ≤ 1 - sigmoid x := sub_nonneg.2 (sigmoid_le_one x)

lemma hasDerivAt_sigmoid (x : ℝ) : HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  have h1 : HasDerivAt (fun y => 1 + Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_add 1
  have hne : 1 + Real.exp (-x) ≠ 0 := by positivity
  have h2 : HasDerivAt sigmoid (-(-Real.exp (-x)) / (1 + Real.exp (-x)) ^ 2) x := h1.fun_inv hne
  convert h2 using 1
  simp only [sigmoid]
  field_simp
  ring

/-- `x e^{-x} ≤ e⁻¹`. -/
lemma mul_exp_neg_le (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (x - 1)
  have e : Real.exp (-1) = Real.exp (x - 1) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- **Logistic sigmoid** (Appendix B of arXiv 2306.01485): `cond(σ) ≤ 1/e` on `(0, ∞)`.  The paper
restricts to `x ≥ 0`; on all of `ℝ` the formula `|x| (1 - σ(x))` is unbounded. -/
theorem condOn_sigmoid_le : condOn (Ici 0) sigmoid ≤ ENNReal.ofReal (Real.exp (-1)) := by
  refine iSup₂_le fun x hx => ?_
  have hx0 : x ≠ 0 := hx.2
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hS := sigmoid_pos x
  rw [condAt_eq_of_hasDerivAt (hasDerivAt_sigmoid x) hx0 hS.ne']
  refine ENNReal.ofReal_le_ofReal ?_
  rw [abs_of_pos hxp, abs_of_pos hS, abs_of_nonneg (mul_nonneg hS.le (one_sub_sigmoid_nonneg x)),
    div_le_iff₀ hS]
  have h1 := mul_exp_neg_le x
  have h2 := one_sub_sigmoid_le x
  have h3 : (1 - sigmoid x) * x ≤ Real.exp (-1) := by nlinarith
  nlinarith

/-- The softplus `σ(x) = ln(1 + eˣ)`. -/
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

lemma self_le_softplus (x : ℝ) : x ≤ softplus x := by
  rw [softplus, Real.le_log_iff_exp_le (by positivity)]
  linarith

lemma hasDerivAt_softplus (x : ℝ) : HasDerivAt softplus (sigmoid x) x := by
  have h1 : HasDerivAt (fun y => 1 + Real.exp y) (Real.exp x) x :=
    (Real.hasDerivAt_exp x).const_add 1
  have hne : 1 + Real.exp x ≠ 0 := by positivity
  have h2 : HasDerivAt softplus (Real.exp x / (1 + Real.exp x)) x := h1.log hne
  convert h2 using 1
  simp only [sigmoid, Real.exp_neg]
  have := Real.exp_pos x
  field_simp
  ring

/-- **Softplus** (Appendix B of arXiv 2306.01485): `cond(σ) ≤ 1` on `(0, ∞)`. -/
theorem condOn_softplus_le : condOn (Ici 0) softplus ≤ 1 := by
  refine iSup₂_le fun x hx => ?_
  have hx0 : x ≠ 0 := hx.2
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hσ : 0 < softplus x := hxp.trans_le (self_le_softplus x)
  rw [condAt_eq_of_hasDerivAt (hasDerivAt_softplus x) hx0 hσ.ne', ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [abs_of_pos hxp, abs_of_pos hσ, abs_of_pos (sigmoid_pos x), div_le_one hσ]
  have h1 := self_le_softplus x
  have h2 := sigmoid_le_one x
  nlinarith

/-- The SiLU `σ(x) = x (1 + e^{-x})⁻¹`. -/
noncomputable def siLU (x : ℝ) : ℝ := x * sigmoid x

lemma hasDerivAt_siLU (x : ℝ) :
    HasDerivAt siLU (sigmoid x + x * (sigmoid x * (1 - sigmoid x))) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_sigmoid x)
  have e : id * sigmoid = siLU := rfl
  rw [e] at h
  simpa using h

/-- **SiLU** (Appendix B of arXiv 2306.01485): `cond(σ) ≤ 1 + 1/e` on `(0, ∞)`. -/
theorem condOn_siLU_le : condOn (Ici 0) siLU ≤ ENNReal.ofReal (1 + Real.exp (-1)) := by
  refine iSup₂_le fun x hx => ?_
  have hx0 : x ≠ 0 := hx.2
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hS := sigmoid_pos x
  have hσ : 0 < siLU x := mul_pos hxp hS
  rw [condAt_eq_of_hasDerivAt (hasDerivAt_siLU x) hx0 hσ.ne']
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 := one_sub_sigmoid_nonneg x
  have h1 := mul_exp_neg_le x
  have h2 := one_sub_sigmoid_le x
  have h3 : x * (1 - sigmoid x) ≤ Real.exp (-1) := by nlinarith
  rw [abs_of_pos hxp, abs_of_pos hσ, abs_of_nonneg (by positivity), div_le_iff₀ hσ]
  have e : (sigmoid x + x * (sigmoid x * (1 - sigmoid x))) * x =
      (1 + x * (1 - sigmoid x)) * siLU x := by
    simp only [siLU]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) hσ.le

/-- The entrywise application of an activation function. -/
noncomputable def entrywise {n : ℕ} (σ : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => σ (z i)

/-- **The reduction to one dimension of arXiv 2306.01485, Section 3, fails for vectors.**  If `σ` is
bounded and `σ'(0) ≠ 0`, then the entrywise map on `ℝ²` with the Euclidean norm has `cond(σ) = ∞`
already on the nonnegative orthant: at `z = (M, 0)` a perturbation of the second entry sees the
slope `σ'(0)`, while `‖z‖ / ‖σ(z)‖` grows with `M`. -/
theorem condOn_entrywise_eq_top {σ : ℝ → ℝ} {d K : ℝ} (hd : HasDerivAt σ d 0) (hd0 : d ≠ 0)
    (hK0 : 0 < K) (hK : ∀ x, |σ x| ≤ K) :
    condOn {z : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ z i} (entrywise σ) = ∞ := by
  have hdp : 0 < |d| := abs_pos.2 hd0
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  set M : ℝ := 4 * K * ((r : ℝ) + 1) / |d| with hM
  have hMp : 0 < M := by positivity
  set z : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![M, 0] with hz
  have hz0 : ‖z‖ = M := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_iff_mul_self_eq_of_pos hMp]
    simp [Fin.sum_univ_two, hz, pow_two]
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz0
    exact hMp.ne hz0
  have hzmem : z ∈ {z : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ z i} \ {0} := by
    refine ⟨fun i => ?_, hzne⟩
    fin_cases i <;> simp [hz, hMp.le]
  refine le_trans ?_ (condAt_le_condOn _ hzmem)
  refine le_iInf₂ fun ε hε => ?_
  -- the slope of `σ` at `0`
  have hs := (hasDerivAt_iff_tendsto_slope_zero.1 hd).abs
  have hev := hs.eventually (lt_mem_nhds (show |d| / 2 < |d| by linarith))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨r₀, hr₀, hball⟩ := hev
  set t : ℝ := min (r₀ / 2) (ε * M) with ht
  have htp : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ ε * M := min_le_right _ _
  have ht2 : t < r₀ := (min_le_left _ _).trans_lt (by linarith)
  have hslope : |d| / 2 * t ≤ |σ t - σ 0| := by
    have h := hball (y := t) (by simpa [abs_of_pos htp] using ht2) htp.ne'
    simp only [zero_add, smul_eq_mul, abs_mul, abs_inv, abs_of_pos htp] at h
    rw [lt_inv_mul_iff₀ htp] at h
    linarith
  set δ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, t] with hδ
  have hδn : ‖δ‖ = t := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_iff_mul_self_eq_of_pos htp]
    simp [Fin.sum_univ_two, hδ, pow_two]
  have hδne : δ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hδn
    exact htp.ne hδn
  have hΔ : ‖entrywise σ (z + δ) - entrywise σ z‖ = |σ t - σ 0| := by
    have hv : ∀ i, (entrywise σ (z + δ) - entrywise σ z) i = ![0, σ t - σ 0] i := by
      intro i
      fin_cases i <;> simp [entrywise, hz, hδ]
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, hv, hv]
    simp [Real.sqrt_sq_eq_abs]
  have hσz : ‖entrywise σ z‖ ≤ 2 * K := by
    rw [← abs_of_nonneg (norm_nonneg (entrywise σ z)), ← abs_of_pos (show 0 < 2 * K by positivity)]
    refine sq_le_sq.1 ?_
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, entrywise, Real.norm_eq_abs]
    have h1 := hK (z 0)
    have h2 := hK (z 1)
    have h3 := abs_nonneg (σ (z 0))
    have h4 := abs_nonneg (σ (z 1))
    nlinarith
  refine le_trans ?_ (relRatio_le_condEps _ hδne (by rw [hδn, hz0]; exact ht1))
  have hRe : ENNReal.ofReal (|σ t - σ 0| / (2 * K) / (t / M)) ≤ relRatio (entrywise σ) z δ := by
    simp only [relRatio]
    rw [← ofReal_norm (entrywise σ (z + δ) - entrywise σ z), hΔ, ← ofReal_norm δ, hδn,
      ← ofReal_norm z, hz0, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_div_of_pos (show 0 < 2 * K by positivity),
      ENNReal.ofReal_div_of_pos hMp]
    gcongr
    rw [← ofReal_norm (entrywise σ z)]
    exact ENNReal.ofReal_le_ofReal hσz
  refine le_trans ?_ hRe
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : |σ t - σ 0| / (2 * K) / (t / M) = |σ t - σ 0| * M / (2 * K * t) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  have hMd : |d| * M = 4 * K * ((r : ℝ) + 1) := by
    rw [hM]
    field_simp
  have hr0 : (0 : ℝ) ≤ r := r.2
  have h5 : |d| / 2 * t * M ≤ |σ t - σ 0| * M := mul_le_mul_of_nonneg_right hslope hMp.le
  have h6 : |d| / 2 * t * M = 2 * K * t * ((r : ℝ) + 1) := by
    calc |d| / 2 * t * M = (|d| * M) * t / 2 := by ring
      _ = _ := by rw [hMd]; ring
  have h7 : 0 ≤ 2 * K * t := by positivity
  nlinarith

/-- **The activation part of Proposition 1 of arXiv 2306.01485 fails for vector features.**  The
bounds of Appendix B are about scalar `x`.  For the entrywise tanh, logistic sigmoid and hard tanh
on `ℝ²` with the Euclidean norm, `sup_x cond(σ; x) = ∞` on the nonnegative orthant, so no constant
`C` depending only on `σ` exists.  (The scalar bounds are `condOn_tanh_le`, `condOn_sigmoid_le`,
`condOn_hardTanh`.) -/
theorem entrywise_activations_eq_top {a : ℝ} (ha : 0 < a) :
    condOn {z : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ z i} (entrywise Real.tanh) = ∞ ∧
    condOn {z : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ z i} (entrywise sigmoid) = ∞ ∧
    condOn {z : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ z i} (entrywise (hardTanh a)) = ∞ := by
  refine ⟨condOn_entrywise_eq_top (d := 1 / Real.cosh 0 ^ 2) (K := 1) (hasDerivAt_tanh 0)
      (by simp) one_pos abs_tanh_le, ?_, ?_⟩
  · have h0 : sigmoid 0 = 1 / 2 := by norm_num [sigmoid]
    refine condOn_entrywise_eq_top (K := 1) (hasDerivAt_sigmoid 0) ?_ one_pos fun x => ?_
    · rw [h0]
      norm_num
    · rw [abs_of_pos (sigmoid_pos x)]
      exact sigmoid_le_one x
  · exact condOn_entrywise_eq_top (K := a) (hasDerivAt_hardTanh (by linarith) ha) one_ne_zero ha
      (abs_hardTanh_le ha)

end Activations

/-! ### The choice of `s` and `ε`, and low-rank layers -/

section Band

open Matrix LeanDLRA.Curvature
open scoped LeanDLRA.Frobenius

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The second moment `s = √(∑_j s_j(S)² / r)` of the singular values of `S ∈ ℝ^{r × r}`
(arXiv 2306.01485, Section 4.2 and Algorithm 1, line 7). -/
noncomputable def secondMoment (S : Matrix k k ℝ) : ℝ :=
  √((∑ j ∈ Finset.range (Fintype.card k), (toEuclideanLin S).singularValues j ^ 2) /
    Fintype.card k)

lemma secondMoment_sq (S : Matrix k k ℝ) :
    secondMoment S ^ 2 = ‖S‖ ^ 2 / Fintype.card k := by
  rw [secondMoment, Real.sq_sqrt (by positivity), EckartYoung.sq_norm_eq_sum_sq_singularValues]

lemma secondMoment_nonneg (S : Matrix k k ℝ) : 0 ≤ secondMoment S := Real.sqrt_nonneg _

lemma inner_bestMultiple (S : Matrix k k ℝ) :
    ⟪Sᵀ * S, (1 : Matrix k k ℝ)⟫ / ‖(1 : Matrix k k ℝ)‖ ^ 2 = secondMoment S ^ 2 := by
  rw [secondMoment_sq, frob_sq_eq_trace (1 : Matrix k k ℝ), Frobenius.inner_eq_trace,
    transpose_mul, transpose_transpose, Matrix.mul_one, frob_sq_eq_trace S]
  simp [Matrix.trace_one]

/-- **The choice of `s`** (arXiv 2306.01485, Section 4.2): the second moment of the singular
values is the best constant approximation, `s = argmin_α ‖SᵀS - α² I‖_F`. -/
theorem secondMoment_isMin (S : Matrix k k ℝ) (α : ℝ) :
    ‖Sᵀ * S - secondMoment S ^ 2 • (1 : Matrix k k ℝ)‖ ≤ ‖Sᵀ * S - α ^ 2 • (1 : Matrix k k ℝ)‖ := by
  simpa only [inner_bestMultiple] using
    norm_sub_bestMultiple_le (Sᵀ * S) (1 : Matrix k k ℝ) (α ^ 2)

/-- The minimiser of `secondMoment_isMin` (arXiv 2306.01485, Section 4.2) is unique among
nonnegative `α`, for `r ≥ 1`. -/
theorem eq_secondMoment_of_isMin [Nonempty k] (S : Matrix k k ℝ) {α : ℝ} (hα : 0 ≤ α)
    (h : ‖Sᵀ * S - α ^ 2 • (1 : Matrix k k ℝ)‖ ≤
      ‖Sᵀ * S - secondMoment S ^ 2 • (1 : Matrix k k ℝ)‖) : α = secondMoment S := by
  have h1 : (1 : Matrix k k ℝ) ≠ 0 := one_ne_zero
  have hq := norm_sub_smul_sq_eq_add (Sᵀ * S) (1 : Matrix k k ℝ) h1 (α ^ 2)
  rw [inner_bestMultiple] at hq
  have hn : 0 < ‖(1 : Matrix k k ℝ)‖ ^ 2 := by positivity
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  have h2 : (α ^ 2 - secondMoment S ^ 2) ^ 2 * ‖(1 : Matrix k k ℝ)‖ ^ 2 ≤ 0 := by linarith
  have h3 : (α ^ 2 - secondMoment S ^ 2) ^ 2 ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos (not_le.1 hc) hn) (not_lt.2 h2)
  have h4 : α ^ 2 - secondMoment S ^ 2 = 0 := by nlinarith [sq_nonneg (α ^ 2 - secondMoment S ^ 2)]
  exact (pow_left_inj₀ hα (secondMoment_nonneg S) two_ne_zero).1 (sub_eq_zero.1 h4)

variable (k) in
/-- `Σ_s(ε)`: the `r × r` matrices with all singular values in `[s - ε, s + ε]`. -/
def sigmaBand (s ε : ℝ) : Set (Matrix k k ℝ) :=
  {S | ∀ i < Fintype.card k, (toEuclideanLin S).singularValues i ∈ Icc (s - ε) (s + ε)}

omit [DecidableEq k] in
lemma card_pred_lt [Nonempty k] : Fintype.card k - 1 < Fintype.card k :=
  Nat.sub_lt Fintype.card_pos one_pos

/-- Singular values in `[a, b]` give `a ‖v‖ ≤ ‖S v‖`. -/
lemma lower_of_mem_sigmaBand {S : Matrix k k ℝ} {s ε : ℝ} (hS : S ∈ sigmaBand k s ε)
    (v : EuclideanSpace ℝ k) : (s - ε) * ‖v‖ ≤ ‖toEuclideanLin S v‖ := by
  rcases isEmpty_or_nonempty k with hk | hk
  · rw [Subsingleton.elim v 0]
    simp
  · exact (SVD.forall_mul_norm_le_iff S).2 (hS _ card_pred_lt).1 v

/-- Singular values in `[a, b]` give `‖S v‖ ≤ b ‖v‖`. -/
lemma upper_of_mem_sigmaBand {S : Matrix k k ℝ} {s ε : ℝ} (hS : S ∈ sigmaBand k s ε)
    (v : EuclideanSpace ℝ k) : ‖toEuclideanLin S v‖ ≤ (s + ε) * ‖v‖ := by
  rcases isEmpty_or_nonempty k with hk | hk
  · rw [Subsingleton.elim v 0]
    simp
  · have h0 : specNorm S ≤ s + ε := by
      rw [EckartYoung.specNorm_eq_singularValues_zero]
      exact (hS 0 Fintype.card_pos).2
    exact (norm_toEuclideanLin_le S v).trans (mul_le_mul_of_nonneg_right h0 (norm_nonneg v))

/-- **The choice of `ε`** (arXiv 2306.01485, Section 4.2 and Algorithm 1, line 8): for `s > 0` and
`τ ≥ 0`, `ε = τ s / (2 + τ)` satisfies `0 ≤ ε < s`, `(s + ε) / (s - ε) = 1 + τ` and
`τ = 2 (s - ε)⁻¹ ε`. -/
theorem choice_of_eps {s τ : ℝ} (hs : 0 < s) (hτ : 0 ≤ τ) :
    0 ≤ τ * s / (2 + τ) ∧ τ * s / (2 + τ) < s ∧
    (s + τ * s / (2 + τ)) / (s - τ * s / (2 + τ)) = 1 + τ ∧
    τ = 2 * (s - τ * s / (2 + τ))⁻¹ * (τ * s / (2 + τ)) := by
  have h2 : 0 < 2 + τ := by linarith
  have hlow : s - τ * s / (2 + τ) = 2 * s / (2 + τ) := by field_simp; ring
  have hup : s + τ * s / (2 + τ) = 2 * s * (1 + τ) / (2 + τ) := by field_simp; ring
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have : 0 < 2 * s / (2 + τ) := by positivity
    linarith
  · rw [hlow, hup]
    field_simp
  · rw [hlow]
    field_simp

/-- **Conditioning on `Σ_s(ε)`** (arXiv 2306.01485, Section 4.2): with `ε = τ s / (2 + τ)`, the
ratio of any two singular values of `S ∈ Σ_s(ε)`, in particular `cond₂(S) = s_max / s_min`, is at
most `1 + τ`.  (`LeanDLRA.div_le_one_add_of_mem_Icc` is the scalar core.) -/
theorem singularValues_div_le {S : Matrix k k ℝ} {s τ : ℝ} (hs : 0 < s) (hτ : 0 ≤ τ)
    (hS : S ∈ sigmaBand k s (τ * s / (2 + τ))) {i j : ℕ} (hi : i < Fintype.card k)
    (hj : j < Fintype.card k) :
    (toEuclideanLin S).singularValues i / (toEuclideanLin S).singularValues j ≤ 1 + τ :=
  div_le_one_add_of_mem_Icc hs hτ (hS i hi) (hS j hj)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [Fintype m] in
lemma toEuclideanLin_mul_apply {l : Type*} [Fintype l] [DecidableEq l] (A : Matrix m n ℝ)
    (B : Matrix n l ℝ) (v : EuclideanSpace ℝ l) :
    toEuclideanLin (A * B) v = toEuclideanLin A (toEuclideanLin B v) := by
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

/-- `‖U S Vᵀ v‖ ≤ (s + ε) ‖v‖` for `S ∈ Σ_s(ε)`. -/
lemma lowRank_upper {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} {s ε : ℝ}
    (hε : 0 ≤ s + ε) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : S ∈ sigmaBand k s ε)
    (v : EuclideanSpace ℝ n) :
    ‖toEuclideanLin (U * S * Vᵀ) v‖ ≤ (s + ε) * ‖v‖ := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hU]
  refine (upper_of_mem_sigmaBand hS _).trans (mul_le_mul_of_nonneg_left ?_ hε)
  have h1 : specNorm Vᵀ ≤ 1 := by
    rw [specNorm_transpose]
    exact specNorm_le_one_of_orthonormal hV
  calc ‖toEuclideanLin Vᵀ v‖ ≤ specNorm Vᵀ * ‖v‖ := norm_toEuclideanLin_le _ _
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- `(s - ε) ‖x‖ ≤ ‖U S Vᵀ x‖` for `S ∈ Σ_s(ε)` and `x` in the row space of `U S Vᵀ`. -/
lemma lowRank_lower {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} {s ε : ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : S ∈ sigmaBand k s ε)
    (y : EuclideanSpace ℝ k) :
    (s - ε) * ‖toEuclideanLin V y‖ ≤
      ‖toEuclideanLin (U * S * Vᵀ) (toEuclideanLin V y)‖ := by
  have e : toEuclideanLin (U * S * Vᵀ) (toEuclideanLin V y) =
      toEuclideanLin U (toEuclideanLin S y) := by
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, Matrix.mul_assoc (U * S),
      hV, Matrix.mul_one]
  rw [e, SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hU,
    SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hV]
  exact lower_of_mem_sigmaBand hS y

/-- **`cond₂(W) ≤ 1 + τ` for the weights of the constrained problem (3) of arXiv 2306.01485.**  For
`W = U S Vᵀ` with `S ∈ Σ_s(ε)`, `ε = τ s / (2 + τ)`, the matrix condition number
`cond(W) = ‖W‖₂ ‖W⁺‖₂` is at most `1 + τ`.  Here `W⁺ = V S⁻¹ Uᵀ` is the Moore–Penrose inverse
(`Curvature.factor_ginv_factor`, `Curvature.ginv_factor_ginv`). -/
theorem cond_lowRank_le [DecidableEq m] {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    {s τ : ℝ} (hs : 0 < s) (hτ : 0 ≤ τ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : S ∈ sigmaBand k s (τ * s / (2 + τ))) :
    specNorm (U * S * Vᵀ) * specNorm (V * S⁻¹ * Uᵀ) ≤ 1 + τ := by
  obtain ⟨h0, hlt, hq, -⟩ := choice_of_eps hs hτ
  set ε := τ * s / (2 + τ) with hε
  have hρ : 0 < s - ε := by linarith
  have hup : specNorm (U * S * Vᵀ) ≤ s + ε :=
    specNorm_le_of (by linarith) (lowRank_upper (by linarith) hU hV hS)
  have hlo : specNorm (V * S⁻¹ * Uᵀ) ≤ (s - ε)⁻¹ :=
    specNorm_ginv_le hρ hU hV (lower_of_mem_sigmaBand hS)
  calc specNorm (U * S * Vᵀ) * specNorm (V * S⁻¹ * Uᵀ)
      ≤ (s + ε) * (s - ε)⁻¹ :=
        mul_le_mul hup hlo (specNorm_nonneg _) (by linarith)
    _ = 1 + τ := by rw [← div_eq_mul_inv, hq]

/-- **The linear part of Proposition 1 of arXiv 2306.01485 for low-rank layers**: on the row space
of `W = U S Vᵀ`, `S ∈ Σ_s(ε)`, `ε = τ s / (2 + τ)`, the map `x ↦ W x` has `cond ≤ 1 + τ`.  The
restriction to the row space is necessary (`condOn_eq_top_of_ker`). -/
theorem condOn_rowSpace_le {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} {s τ : ℝ}
    (hs : 0 < s) (hτ : 0 ≤ τ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : S ∈ sigmaBand k s (τ * s / (2 + τ))) :
    condOn (Set.range (toEuclideanLin V)) (toEuclideanLin (U * S * Vᵀ)) ≤
      ENNReal.ofReal (1 + τ) := by
  obtain ⟨h0, hlt, hq, -⟩ := choice_of_eps hs hτ
  set ε := τ * s / (2 + τ) with hε
  have hρ : 0 < s - ε := by linarith
  rw [← hq]
  refine condOn_linear_le _ (lowRank_upper (by linarith) hU hV hS) (by linarith) hρ ?_
  rintro _ ⟨y, rfl⟩
  exact lowRank_lower hU hV hS y

omit [Fintype k] [DecidableEq k] [Fintype m] [Fintype n] [DecidableEq n] in
lemma condOn_mono {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {A B : Set X}
    (h : A ⊆ B) (f : X → Y) : condOn A f ≤ condOn B f :=
  biSup_mono fun _ hx => ⟨h hx.1, hx.2⟩

/-- **Proposition 1 of arXiv 2306.01485 for a network with low-rank layers**
`W_i = U_i S_i V_iᵀ`, `S_i ∈ Σ_{s_i}(ε_i)`, `ε_i = τ s_i / (2 + τ)`:
`cond(f) ≤ (∏_i sup cond(σ_i)) (1 + τ)^L`, provided the feature sets `Z i` of the layer inputs lie
in the row spaces of the `W_i`.  This hypothesis is not in the paper, whose bound with
`cond(W_i) = ‖W_i‖ ‖W_i⁺‖` is false without it (`proposition1_false_with_pinv`). -/
theorem condOn_layerNet_lowRank_le {d r : ℕ → ℕ} {τ : ℝ} (hτ : 0 ≤ τ) {s : ℕ → ℝ}
    (hs : ∀ i, 0 < s i) {U : ∀ i, Matrix (Fin (d (i + 1))) (Fin (r i)) ℝ}
    {S : ∀ i, Matrix (Fin (r i)) (Fin (r i)) ℝ} {V : ∀ i, Matrix (Fin (d i)) (Fin (r i)) ℝ}
    (hU : ∀ i, (U i)ᵀ * U i = 1) (hV : ∀ i, (V i)ᵀ * V i = 1)
    (hS : ∀ i, S i ∈ sigmaBand (Fin (r i)) (s i) (τ * s i / (2 + τ)))
    {σ : ∀ i, EuclideanSpace ℝ (Fin (d (i + 1))) → EuclideanSpace ℝ (Fin (d (i + 1)))}
    (hσ : ∀ i, Continuous (σ i)) {Z : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))}
    {A : ∀ i, Set (EuclideanSpace ℝ (Fin (d (i + 1))))} (L : ℕ)
    (hZrow : ∀ i < L, Z i ⊆ Set.range (toEuclideanLin (V i)))
    (hZ : ∀ i < L, MapsTo (toEuclideanLin (U i * S i * (V i)ᵀ)) (Z i) (A i))
    (hA : ∀ i < L, MapsTo (σ i) (A i) (Z (i + 1)))
    (hσf : ∀ i < L, condOn (A i) (σ i) ≠ ∞) :
    condOn (Z 0) (layerNet (E := fun i => EuclideanSpace ℝ (Fin (d i)))
        (F := fun i => EuclideanSpace ℝ (Fin (d (i + 1))))
        (fun i => toEuclideanLin (U i * S i * (V i)ᵀ)) σ L) ≤
      (∏ i ∈ Finset.range L, condOn (A i) (σ i)) * ENNReal.ofReal (1 + τ) ^ L := by
  have hT : ∀ i < L, condOn (Z i) (toEuclideanLin (U i * S i * (V i)ᵀ)) ≤
      ENNReal.ofReal (1 + τ) := fun i hi =>
    (condOn_mono (hZrow i hi) _).trans (condOn_rowSpace_le (hs i) hτ (hU i) (hV i) (hS i))
  have h := condOn_layerNet_le (E := fun i => EuclideanSpace ℝ (Fin (d i)))
    (F := fun i => EuclideanSpace ℝ (Fin (d (i + 1))))
    (T := fun i => toEuclideanLin (U i * S i * (V i)ᵀ)) (σ := σ) (Z := Z) (A := A)
    (fun i => (toEuclideanLin (U i * S i * (V i)ᵀ)).continuous_of_finiteDimensional) hσ L hZ hA
    (fun i hi => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hT i hi)) hσf
  refine h.trans (mul_le_mul_right ?_ _)
  calc ∏ i ∈ Finset.range L, condOn (Z i) (toEuclideanLin (U i * S i * (V i)ᵀ))
      ≤ ∏ _i ∈ Finset.range L, ENNReal.ofReal (1 + τ) :=
        Finset.prod_le_prod fun i hi => hT i (by simpa using hi)
    _ = ENNReal.ofReal (1 + τ) ^ L := by simp

/-- **Proposition 1 of arXiv 2306.01485 is false with the paper's matrix condition number
`cond(W) = ‖W‖ ‖W⁺‖`.**  For `W = diag(1, 0)` we have `W⁺ = W` (the Moore–Penrose equations reduce
to `W W W = W` and the symmetry of `W W`) and `‖W‖₂ ‖W⁺‖₂ ≤ 1`, while the one-layer network
`x ↦ W x` has `cond = ∞` on `ℝ²`.  So "when `f(x) = A x` we have `cond(f, x) = cond(A)`"
(Section 3) fails, and it fails for every rank-deficient nonzero layer (`condOn_eq_top_of_ker`),
which is the case of interest of the paper.  What holds is `condOn_layerNet_le` with the condition
numbers of the maps, and `condOn_layerNet_lowRank_le` on the row spaces. -/
theorem proposition1_false_with_pinv :
    let W : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    W * W * W = W ∧ (W * W)ᵀ = W * W ∧ specNorm W * specNorm W ≤ 1 ∧
      condOn univ (toEuclideanLin W) = ∞ := by
  intro W
  have hW : W * W = W := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W, Matrix.mul_apply, Fin.sum_univ_two]
  have hs : Wᵀ = W := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W]
  have hP : IsOrthProjMat W := ⟨hs, hW⟩
  refine ⟨by rw [hW, hW], by rw [hW, hs], ?_, ?_⟩
  · have h := hP.specNorm_le_one
    have h0 := specNorm_nonneg W
    nlinarith
  · have hT : toEuclideanLin W ≠ 0 := by
      intro h
      have h1 := congrArg (fun T => (T (WithLp.toLp 2 ![1, 0]) : EuclideanSpace ℝ (Fin 2)) 0) h
      simp [W, Matrix.toLpLin_apply] at h1
    have hx : (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h
      simp at h1
    refine condOn_eq_top_of_ker _ hT (mem_univ _) hx ?_
    ext i
    fin_cases i <;> simp [W, Matrix.toLpLin_apply]

end Band

/-! ### Line 9 of Algorithm 1 is a projection -/

section Clamp

open Matrix LeanDLRA.Curvature
open scoped LeanDLRA.Frobenius

variable {r : ℕ}

/-- Clamping a singular value to `[a, b]`: "set to `s + ε` or `s - ε` the singular values that fall
outside the interval" (arXiv 2306.01485, Section 4.2). -/
noncomputable def clamp (a b x : ℝ) : ℝ := max a (min x b)

lemma clamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clamp a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma sq_sub_clamp_le {a b x y : ℝ} (hy : y ∈ Icc a b) : (x - clamp a b x) ^ 2 ≤ (x - y) ^ 2 := by
  obtain ⟨h1, h2⟩ := hy
  have hab : a ≤ b := h1.trans h2
  rcases le_total x a with hx | hx
  · have e : clamp a b x = a := by simp [clamp, min_eq_left (hx.trans hab), hx]
    rw [e]
    nlinarith
  rcases le_total x b with hx' | hx'
  · have e : clamp a b x = x := by simp [clamp, hx, hx']
    rw [e, sub_self]
    simpa using sq_nonneg (x - y)
  · have e : clamp a b x = b := by simp [clamp, hx', hab]
    rw [e]
    nlinarith

lemma norm_sq_orthogonal_diagonal {P Q : Matrix (Fin r) (Fin r) ℝ} (hP : Pᵀ * P = 1)
    (hQ : Qᵀ * Q = 1) (d : Fin r → ℝ) :
    ‖P * diagonal d * Qᵀ‖ ^ 2 = ∑ i, d i ^ 2 := by
  have h1 : (P * diagonal d * Qᵀ)ᵀ * (P * diagonal d * Qᵀ) =
      Q * (diagonal d * diagonal d * Qᵀ) := by
    calc (P * diagonal d * Qᵀ)ᵀ * (P * diagonal d * Qᵀ)
        = Q * diagonal d * (Pᵀ * P) * diagonal d * Qᵀ := by
          simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [frob_sq_eq_trace, h1, Matrix.trace_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one,
    diagonal_mul_diagonal, trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => (pow_two _).symm

/-- `P diag(c) Qᵀ` with `P, Q` orthogonal and `c ∈ [a, b]` lies in `Σ_s(ε)`, `[a, b] = [s-ε, s+ε]`,
`a ≥ 0`. -/
lemma orthogonal_diagonal_mem_sigmaBand {P Q : Matrix (Fin r) (Fin r) ℝ} (hP : Pᵀ * P = 1)
    (hQ : Qᵀ * Q = 1) {c : Fin r → ℝ} {s ε : ℝ} (hε : 0 ≤ s - ε)
    (hc : ∀ i, c i ∈ Icc (s - ε) (s + ε)) :
    P * diagonal c * Qᵀ ∈ sigmaBand (Fin r) s ε := by
  have hQt : (Qᵀ)ᵀ * Qᵀ = 1 := by
    rw [transpose_transpose]
    exact mul_eq_one_comm.1 hQ
  have happ : ∀ v, ‖toEuclideanLin (P * diagonal c * Qᵀ) v‖ =
      ‖toEuclideanLin (diagonal c) (toEuclideanLin Qᵀ v)‖ := fun v => by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
      SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hP]
  have hlow : ∀ v, (s - ε) * ‖v‖ ≤ ‖toEuclideanLin (P * diagonal c * Qᵀ) v‖ := fun v => by
    rw [happ, ← SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hQt v]
    exact diagonal_bounded_below hε (fun i => (hc i).1) _
  have hs0 : 0 ≤ s + ε ∨ IsEmpty (Fin r) := by
    rcases isEmpty_or_nonempty (Fin r) with h | ⟨⟨i⟩⟩
    · exact Or.inr h
    · exact Or.inl (hε.trans ((hc i).1.trans (hc i).2))
  intro i hi
  rw [Fintype.card_fin] at hi
  have hne : Nonempty (Fin r) := ⟨⟨i, hi⟩⟩
  have hb : 0 ≤ s + ε := hs0.resolve_right (not_isEmpty_iff.2 hne)
  have hanti := (toEuclideanLin (P * diagonal c * Qᵀ)).singularValues_antitone
  refine ⟨?_, ?_⟩
  · have h1 := (SVD.forall_mul_norm_le_iff (P * diagonal c * Qᵀ)).1 hlow
    rw [Fintype.card_fin] at h1
    exact h1.trans (hanti (by omega))
  · refine (hanti (Nat.zero_le i)).trans ?_
    rw [← EckartYoung.specNorm_eq_singularValues_zero]
    refine specNorm_le_of hb fun v => ?_
    rw [happ]
    have h2 : specNorm (diagonal c) ≤ s + ε := by
      refine specNorm_le_of hb fun w => ?_
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hj : |c j| ≤ s + ε := by
        rw [abs_of_nonneg (hε.trans (hc j).1)]
        exact (hc j).2
      simp only [toLpLin_apply, Real.norm_eq_abs, sq_abs, mulVec_diagonal, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (by rw [← sq_abs (c j)]; exact pow_le_pow_left₀ (abs_nonneg _) hj 2) (sq_nonneg _)
    calc ‖toEuclideanLin (diagonal c) (toEuclideanLin Qᵀ v)‖
        ≤ specNorm (diagonal c) * ‖toEuclideanLin Qᵀ v‖ := norm_toEuclideanLin_le _ _
      _ = specNorm (diagonal c) * ‖v‖ := by
          rw [SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hQt]
      _ ≤ (s + ε) * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg v)

/-- **Line 9 of Algorithm 1 of arXiv 2306.01485 is a nearest-point projection onto `Σ_s(ε)`.**  For
an SVD `S = P diag(σ) Qᵀ` with `σ` the sorted singular values (for invertible `S` it exists by
`SVD.exists_svd`), and `0 ≤ s - ε`, `0 ≤ ε`, clamping `σ` to `[s - ε, s + ε]` gives `C ∈ Σ_s(ε)`
with `‖S - C‖_F ≤ ‖S - Z‖_F` for all `Z ∈ Σ_s(ε)`.  The paper calls this step a projection without
proof; the argument is Mirsky's inequality (`Mirsky.sum_sq_singularValues_sub_le`). -/
theorem clamp_isNearest {S P Q : Matrix (Fin r) (Fin r) ℝ} {σ : Fin r → ℝ} {s ε : ℝ}
    (hε : 0 ≤ ε) (hsε : 0 ≤ s - ε) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (hσ : ∀ i : Fin r, σ i = (toEuclideanLin S).singularValues i)
    (hS : S = P * diagonal σ * Qᵀ) :
    P * diagonal (fun i => clamp (s - ε) (s + ε) (σ i)) * Qᵀ ∈ sigmaBand (Fin r) s ε ∧
    ∀ Z ∈ sigmaBand (Fin r) s ε,
      ‖S - P * diagonal (fun i => clamp (s - ε) (s + ε) (σ i)) * Qᵀ‖ ≤ ‖S - Z‖ := by
  have hab : s - ε ≤ s + ε := by linarith
  refine ⟨orthogonal_diagonal_mem_sigmaBand hP hQ hsε fun i => clamp_mem hab _, fun Z hZ => ?_⟩
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  have e : S - P * diagonal (fun i => clamp (s - ε) (s + ε) (σ i)) * Qᵀ =
      P * diagonal (fun i => σ i - clamp (s - ε) (s + ε) (σ i)) * Qᵀ := by
    rw [hS, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rw [e, norm_sq_orthogonal_diagonal hP hQ]
  refine le_trans ?_ (Mirsky.sum_sq_singularValues_sub_le S Z)
  rw [Fintype.card_fin, ← Fin.sum_univ_eq_sum_range
    (fun i => ((toEuclideanLin S).singularValues i - (toEuclideanLin Z).singularValues i) ^ 2) r]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hσ i]
  exact sq_sub_clamp_le (hZ i (by simp))

end Clamp

/-! ### Theorem 1 -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If a linear map `N` kills `x t` and `N (x u)` is quadratically small in `x u - x t`, then `N`
kills the right derivative of `x` at `t`.  This turns the curvature estimate into the statement
that the velocity of a curve in the manifold is tangent. -/
lemma clm_apply_deriv_eq_zero (N : E →L[ℝ] E) {x : ℝ → E} {x' : E} {t C : ℝ}
    (hx : HasDerivWithinAt x x' (Ici t) t) (h0 : N (x t) = 0)
    (hq : ∀ᶠ u in 𝓝[>] t, ‖N (x u)‖ ≤ C * ‖x u - x t‖ ^ 2) : N x' = 0 := by
  have hs : Tendsto (slope x t) (𝓝[>] t) (𝓝 x') :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hx.Ioi_of_Ici
  have h1 : Tendsto (fun u => N (slope x t u)) (𝓝[>] t) (𝓝 (N x')) :=
    (N.continuous.tendsto x').comp hs
  have hid : Tendsto (fun u : ℝ => u - t) (𝓝[>] t) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 (t - t)) :=
      (continuous_id.sub continuous_const).tendsto t
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun u => C * ‖slope x t u‖ ^ 2 * (u - t)) (𝓝[>] t) (𝓝 0) := by
    simpa using (((hs.norm.pow 2).const_mul C).mul hid)
  have h3 : Tendsto (fun u => N (slope x t u)) (𝓝[>] t) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [hq, self_mem_nhdsWithin] with u hu hut
    have hp : 0 < u - t := sub_pos.2 hut
    rw [slope_def_module, map_smul, map_sub, h0, sub_zero, norm_smul, norm_smul, mul_pow,
      Real.norm_of_nonneg (inv_nonneg.2 hp.le)]
    have e : C * ((u - t)⁻¹ ^ 2 * ‖x u - x t‖ ^ 2) * (u - t) =
        (u - t)⁻¹ * (C * ‖x u - x t‖ ^ 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hu (inv_nonneg.2 hp.le)
  exact tendsto_nhds_unique h1 h3

/-- Comparison with a barrier: if `‖D‖ = z` forces `⟪D, D'⟫ < z z'`, then `‖D‖` stays below `z`. -/
lemma norm_le_of_barrier {D D' : ℝ → E} {z z' : ℝ → ℝ} {T : ℝ}
    (hDc : ContinuousOn D (Icc 0 T)) (hD : ∀ t ∈ Ico 0 T, HasDerivWithinAt D (D' t) (Ici t) t)
    (hzc : ContinuousOn z (Icc 0 T)) (hz : ∀ t ∈ Ico 0 T, HasDerivWithinAt z (z' t) (Ici t) t)
    (hpos : ∀ t ∈ Icc 0 T, 0 < z t) (h0 : ‖D 0‖ ≤ z 0)
    (hb : ∀ t ∈ Ico 0 T, ‖D t‖ = z t → ⟪D t, D' t⟫ < z t * z' t) :
    ∀ t ∈ Icc 0 T, ‖D t‖ ≤ z t := by
  intro t ht
  have hT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun t => ‖D t‖ ^ 2)
    (f' := fun t => 2 * ⟪D t, D' t⟫) (a := 0) (b := T) (B := fun t => z t ^ 2)
    (B' := fun t => 2 * z t * z' t) (hDc.norm.pow 2) (fun t ht => (hD t ht).norm_sq)
    (pow_le_pow_left₀ (norm_nonneg _) h0 2) (hzc.pow 2)
    (fun t ht => by simpa using (hz t ht).fun_pow 2)
    (fun t ht he => by
      have hzt := hpos t (Ico_subset_Icc_self ht)
      have heq : ‖D t‖ = z t := (pow_left_inj₀ (norm_nonneg _) hzt.le two_ne_zero).1 he
      have := hb t ht heq
      linarith)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hpos t ht).le two_ne_zero).1 (key ht)

/-- `⟪D, P (a + b) - a⟫ = -⟪(1 - P) D, (1 - P) a⟫ + ⟪D, P b⟫` for an orthogonal projector `P`. -/
lemma inner_apply_add_sub {P : E →L[ℝ] E} (hP : IsOrthProj P) (D a b : E) :
    ⟪D, P (a + b) - a⟫ = -⟪D - P D, a - P a⟫ + ⟪D, P b⟫ := by
  have h0 : ⟪P D, a - P a⟫ = 0 := hP.inner_sub_self D a
  rw [map_add, inner_sub_left, h0, sub_zero, ← inner_neg_right, ← inner_add_right]
  congr 1
  abel

end Abstract

section Theorem1

open Matrix LeanDLRA.Curvature
open scoped LeanDLRA.Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]

variable (m n k) in
/-- `ℳ_r ∩ Σ_s(ε)`: the matrices `W = U S Vᵀ` with `r` orthonormal left and right factors and
`S ∈ Σ_s(ε)`.  For `s - ε > 0` such `S` is invertible, so these matrices have rank exactly `r`. -/
def lowRankBand (s ε : ℝ) : Set (Matrix m n ℝ) :=
  {X | ∃ (U : Matrix m k ℝ) (S : Matrix k k ℝ) (V : Matrix n k ℝ),
    Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ S ∈ sigmaBand k s ε ∧ X = U * S * Vᵀ}

/-- The right-hand sides of (5) of arXiv 2306.01485 in the form of `LeanDLRA.GaugeODE`.  With
`Z = ∇ℒ(U S Vᵀ)` we have `∇_U ℒ = Z V Sᵀ` and `∇_V ℒ = Zᵀ U S`, and for invertible `S`:
`∇_U ℒ (S Sᵀ)⁻¹ = Z V S⁻¹` and `∇_V ℒ (Sᵀ S)⁻¹ = Zᵀ U S⁻ᵀ`. -/
theorem factorFlow_eq {S : Matrix k k ℝ} (hS : IsUnit S.det) (Z : Matrix m n ℝ) (U : Matrix m k ℝ)
    (V : Matrix n k ℝ) :
    Z * V * Sᵀ * (S * Sᵀ)⁻¹ = Z * V * S⁻¹ ∧ Zᵀ * U * S * (Sᵀ * S)⁻¹ = Zᵀ * U * S⁻¹ᵀ := by
  have hSt : IsUnit Sᵀ.det := by rwa [det_transpose]
  constructor
  · rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc Sᵀ, Matrix.mul_nonsing_inv _ hSt,
      Matrix.one_mul]
  · rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc S, Matrix.mul_nonsing_inv _ hS,
      Matrix.one_mul, transpose_nonsing_inv]

/-- The standing assumptions of Section 4.3 of arXiv 2306.01485 on `[0, T]`: `W` is the full
gradient flow `Ẇ = -G(W)`, `G = ∇ℒ`; `W̃ := W - E` lies in `ℳ_r ∩ Σ_s(ε)`; `‖Ė‖ ≤ η`; and
`‖∇ℒ(W(t))‖ ≤ μ` along the flow.  All norms are Frobenius norms.  The loss itself enters only
through `G`.  Derivatives are right derivatives on `[0, T)`, as in `ODESolution`.  The derivative of
`W̃` and its tangency are not assumed: they follow (`tangent_deriv`). -/
structure IsTrainingFlow (G : Matrix m n ℝ → Matrix m n ℝ) (W E E' : ℝ → Matrix m n ℝ)
    (μ η s ε T : ℝ) : Prop where
  flow : ODESolution (fun _ w => -G w) W 0 T
  band : ∀ t ∈ Icc 0 T, W t - E t ∈ lowRankBand m n k s ε
  Econt : ContinuousOn E (Icc 0 T)
  Ederiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t
  Ebound : ∀ t ∈ Ico 0 T, ‖E' t‖ ≤ η
  grad : ∀ t ∈ Icc 0 T, ‖G (W t)‖ ≤ μ

/-- A differentiable curve in `ℳ_r ∩ Σ_s(ε)` has a tangent velocity: `P^⊥(X(t)) Ẋ(t) = 0`.  The
paper uses this as `Ẇ̃ = P(W̃) Ẇ̃`; here it is derived from the curvature bound. -/
lemma tangent_deriv [DecidableEq m] [DecidableEq n] {X : ℝ → Matrix m n ℝ} {X' : Matrix m n ℝ}
    {s ε t T : ℝ} (hρ : 0 < s - ε)
    (ht : t ∈ Ico 0 T) (hX : HasDerivWithinAt X X' (Ici t) t)
    (hband : ∀ u ∈ Icc 0 T, X u ∈ lowRankBand m n k s ε)
    {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hXt : X t = U * S * Vᵀ) : (1 - U * Uᵀ) * X' * (1 - V * Vᵀ) = 0 := by
  set N : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := normal (leftProj U) (rightProj V) with hN
  have hNa : ∀ Z, N Z = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := normal_leftProj_rightProj_apply U V
  have h0 : N (X t) = 0 := by
    rw [hNa, hXt, Matrix.sub_mul, Matrix.one_mul, colProj_mul_factor hU, sub_self, Matrix.zero_mul]
  have hq : ∀ᶠ u in 𝓝[>] t, ‖N (X u)‖ ≤ (s - ε)⁻¹ * ‖X u - X t‖ ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT ht.2] with u hu
    obtain ⟨U₂, S₂, V₂, hU₂, hV₂, hS₂, hXu⟩ := hband u ⟨ht.1.trans hu.1.le, hu.2.le⟩
    have h := koch_lubich_normal hρ hU₂ hV₂ hU hV (S := S₂) (S' := S)
      (lower_of_mem_sigmaBand hS₂)
    rw [← hXu, ← hXt, ← hNa, map_sub, h0, zero_sub, norm_neg, norm_sub_rev] at h
    exact h
  rw [← hNa]
  exact clm_apply_deriv_eq_zero N hX h0 hq

/-- The energy estimate of the proof of Theorem 1 of arXiv 2306.01485:
`⟪Y - X, P(Y)(Ẋ + f) - Ẋ⟫ ≤ ‖Y - X‖ (2 ρ⁻² ‖Ẋ‖ ‖Y - X‖² + ‖f‖)` for tangent `Ẋ`, with
`σ_r(X) ≥ ρ`.  (The paper has the constant `32` from Koch–Lubich, Lemma 4.2; the sharper constant
`2` is from `koch_lubich_normal` and `koch_lubich_tangent_frob`.) -/
lemma inner_tangent_sub_le [DecidableEq m] [DecidableEq n] {U U' : Matrix m k ℝ}
    {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖toEuclideanLin S v‖)
    {X' f : Matrix m n ℝ} (hX' : (1 - U * Uᵀ) * X' * (1 - V * Vᵀ) = 0) :
    ⟪U' * S' * V'ᵀ - U * S * Vᵀ, tangentProj U' V' (X' + f) - X'⟫ ≤
      ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ *
        (2 * ρ⁻¹ ^ 2 * ‖X'‖ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 + ‖f‖) := by
  set D := U' * S' * V'ᵀ - U * S * Vᵀ with hD
  set P : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := tangentProj U' V' with hPdef
  have hP : IsOrthProj P := isOrthProj_tangentProj hU' hV'
  have hρi : 0 < ρ⁻¹ := inv_pos.2 hρ
  -- `X'` is tangent at `X`
  have hQ : tangentProjMat (U * Uᵀ) (V * Vᵀ) X' = X' := by
    have := sub_tangentProjMat (U * Uᵀ) (V * Vᵀ) X'
    rw [hX', sub_eq_zero] at this
    exact this.symm
  have h1 : ‖X' - P X'‖ ≤ 2 * ρ⁻¹ * ‖D‖ * ‖X'‖ := by
    have h := koch_lubich_tangent_frob (S' := S') hρ hU hV hU' hV' hS X'
    rw [hQ, tangentProjMat_eq_tangentProj, norm_sub_rev] at h
    exact h
  have h2 : ‖D - P D‖ ≤ ρ⁻¹ * ‖D‖ ^ 2 := by
    have h := koch_lubich_normal hρ hU hV hU' hV' (S' := S') hS
    rw [← hD, ← sub_tangentProjMat, tangentProjMat_eq_tangentProj] at h
    exact h
  have h3 : ⟪D, P (X' + f) - X'⟫ = -⟪D - P D, X' - P X'⟫ + ⟪D, P f⟫ :=
    inner_apply_add_sub hP D X' f
  have h4 : -⟪D - P D, X' - P X'⟫ ≤ ‖D - P D‖ * ‖X' - P X'‖ := by
    have := abs_real_inner_le_norm (D - P D) (X' - P X')
    linarith [neg_abs_le ⟪D - P D, X' - P X'⟫]
  have h5 : ⟪D, P f⟫ ≤ ‖D‖ * ‖f‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hP.norm_le f) (norm_nonneg D))
  have h6 : ‖D - P D‖ * ‖X' - P X'‖ ≤ ρ⁻¹ * ‖D‖ ^ 2 * (2 * ρ⁻¹ * ‖D‖ * ‖X'‖) :=
    mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
  rw [h3]
  calc -⟪D - P D, X' - P X'⟫ + ⟪D, P f⟫
      ≤ ρ⁻¹ * ‖D‖ ^ 2 * (2 * ρ⁻¹ * ‖D‖ * ‖X'‖) + ‖D‖ * ‖f‖ := by linarith
    _ = _ := by ring

/-- **The Riccati comparison of the proof of Theorem 1 of arXiv 2306.01485**, in a form that also
covers a gradient evaluated at `Y`.  Let `Ẏ = P(Y)(-G(W) + r)` with `‖r‖ ≤ β (‖Y - W̃‖ + η t)`,
`Y(0) = W̃(0)` and `8 (μ + η) η T² e^{βT} < (s - ε)²`.  Then `‖Y(t) - W̃(t)‖ ≤ 2 η t e^{βt}`.
The paper compares with `z = √(η/γ) tan(t √(ηγ))`; the barrier here is polynomial times
exponential, which suffices because of the sharper curvature constant. -/
theorem norm_sub_band_le {G : Matrix m n ℝ → Matrix m n ℝ} {W E E' Y Y' r : ℝ → Matrix m n ℝ}
    {U : ℝ → Matrix m k ℝ} {S : ℝ → Matrix k k ℝ} {V : ℝ → Matrix n k ℝ} {μ η s ε β T : ℝ}
    (h : IsTrainingFlow (k := k) G W E E' μ η s ε T) (hρ : 0 < s - ε) (hη : 0 < η) (hβ : 0 ≤ β)
    (hYc : ContinuousOn Y (Icc 0 T)) (hY : ∀ t ∈ Ico 0 T, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hfac : ∀ t ∈ Ico 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hform : ∀ t ∈ Ico 0 T, Y' t = tangentProj (U t) (V t) (-G (W t) + r t))
    (hr : ∀ t ∈ Ico 0 T, ‖r t‖ ≤ β * (‖Y t - (W t - E t)‖ + η * t))
    (h0 : Y 0 = W 0 - E 0)
    (hT : 8 * (μ + η) * η * T ^ 2 * Real.exp (β * T) < (s - ε) ^ 2) :
    ∀ t ∈ Icc 0 T, ‖Y t - (W t - E t)‖ ≤ 2 * η * t * Real.exp (β * t) := by
  classical
  intro t ht
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  have hμ : 0 ≤ μ := (norm_nonneg _).trans (h.grad 0 ⟨le_rfl, hT0⟩)
  set ρ := s - ε with hρdef
  set γ : ℝ := 2 * ρ⁻¹ ^ 2 * (μ + η) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  set X : ℝ → Matrix m n ℝ := fun t => W t - E t with hX
  set X' : ℝ → Matrix m n ℝ := fun t => -G (W t) - E' t with hX'
  have hXd : ∀ t ∈ Ico 0 T, HasDerivWithinAt X (X' t) (Ici t) t := fun t ht =>
    (h.flow.deriv t ht).sub (h.Ederiv t ht)
  have hXc : ContinuousOn X (Icc 0 T) := h.flow.cont.sub h.Econt
  set D : ℝ → Matrix m n ℝ := fun t => Y t - X t with hD
  set D' : ℝ → Matrix m n ℝ := fun t => Y' t - X' t with hD'
  have hDd : ∀ t ∈ Ico 0 T, HasDerivWithinAt D (D' t) (Ici t) t := fun t ht =>
    (hY t ht).sub (hXd t ht)
  have hDc : ContinuousOn D (Icc 0 T) := hYc.sub hXc
  have hD0 : D 0 = 0 := by simp [hD, hX, h0]
  have hinner : ∀ t ∈ Ico 0 T, ⟪D t, D' t⟫ ≤
      ‖D t‖ * (γ * ‖D t‖ ^ 2 + η + β * (‖D t‖ + η * t)) := by
    intro t ht
    obtain ⟨Ut, St, Vt, hUt, hVt, hSt, hXt⟩ := h.band t (Ico_subset_Icc_self ht)
    obtain ⟨hU, hV, hYt⟩ := hfac t ht
    have htan := tangent_deriv (k := k) hρ ht (hXd t ht) h.band hUt hVt hXt
    have hform' : Y' t = tangentProj (U t) (V t) (X' t + (E' t + r t)) := by
      rw [hform t ht]
      congr 1
      simp only [hX']
      abel
    have hkey := inner_tangent_sub_le (S' := S t) hρ hUt hVt hU hV (lower_of_mem_sigmaBand hSt)
      (f := E' t + r t) htan
    rw [← hYt, ← hXt, ← hform'] at hkey
    have hDt : Y t - (W t - E t) = D t := rfl
    have hDt' : Y' t - X' t = D' t := rfl
    rw [hDt, hDt'] at hkey
    refine hkey.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have hX'n : ‖X' t‖ ≤ μ + η := (norm_sub_le _ _).trans (by
      rw [norm_neg]
      exact add_le_add (h.grad t (Ico_subset_Icc_self ht)) (h.Ebound t ht))
    have hf : ‖E' t + r t‖ ≤ η + β * (‖D t‖ + η * t) :=
      (norm_add_le _ _).trans (add_le_add (h.Ebound t ht) (hr t ht))
    have hρ2 : 2 * ρ⁻¹ ^ 2 * ‖X' t‖ * ‖D t‖ ^ 2 ≤ γ * ‖D t‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hX'n (by positivity)
    linarith
  -- a strict barrier for every small shift `δ`
  have hbar : ∀ δ : ℝ, 0 < δ → 4 * γ * η * (T + δ) ^ 2 * Real.exp (β * T) < 1 →
      ‖D t‖ ≤ 2 * η * (t + δ) * Real.exp (β * t) := by
    intro δ hδ hκ
    refine norm_le_of_barrier (D := D) (D' := D') hDc hDd
      (z := fun u => 2 * η * (u + δ) * Real.exp (β * u))
      (z' := fun u => 2 * η * Real.exp (β * u) * (1 + β * (u + δ))) (Continuous.continuousOn
        (by fun_prop)) (fun u _ => ?_) (fun u hu => ?_) ?_ (fun u hu he => ?_) t ht
    · have h1 : HasDerivAt (fun u => 2 * η * (u + δ)) (2 * η) u := by
        simpa using ((hasDerivAt_id u).add_const δ).const_mul (2 * η)
      have h2 : HasDerivAt (fun u => Real.exp (β * u)) (Real.exp (β * u) * β) u := by
        simpa using ((hasDerivAt_id u).const_mul β).exp
      exact ((h1.mul h2).hasDerivWithinAt).congr_deriv (by ring)
    · have := hu.1
      positivity
    · rw [hD0, norm_zero]
      have : 0 ≤ 2 * η * (0 + δ) * Real.exp (β * 0) := by positivity
      exact this
    · have hu0 : 0 ≤ u := hu.1
      have huT : u ≤ T := hu.2.le
      set w : ℝ := Real.exp (β * u) with hw
      set Z : ℝ := u + δ with hZ
      have hZp : 0 < Z := by positivity
      have hwp : 0 < w := Real.exp_pos _
      have hw1 : 1 + β * u ≤ w := by
        have := Real.add_one_le_exp (β * u)
        linarith
      have hwT : w ≤ Real.exp (β * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left huT hβ)
      have hZT : Z ≤ T + δ := by simp only [hZ]; linarith
      have hκu : 4 * γ * η * Z ^ 2 * w < 1 := by
        refine lt_of_le_of_lt ?_ hκ
        have : Z ^ 2 ≤ (T + δ) ^ 2 := pow_le_pow_left₀ hZp.le hZT 2
        gcongr
      have hz : 2 * η * Z * w = ‖D u‖ := he.symm
      have hzp : 0 < 2 * η * Z * w := by positivity
      refine (hinner u (hu)).trans_lt ?_
      rw [← hz]
      refine mul_lt_mul_of_pos_left ?_ hzp
      have hmul : 4 * γ * η * Z ^ 2 * w * w < 1 * w := mul_lt_mul_of_pos_right hκu hwp
      have key : 2 * η * w * (1 + β * Z) - (γ * (2 * η * Z * w) ^ 2 + η +
          β * (2 * η * Z * w + η * u)) = η * (2 * w - 1 - β * u - 4 * γ * η * Z ^ 2 * w * w) := by
        ring
      have : 0 < 2 * w - 1 - β * u - 4 * γ * η * Z ^ 2 * w * w := by linarith
      nlinarith [mul_pos hη this]
  -- let the shift tend to zero
  have hκ0 : 4 * γ * η * (T + 0) ^ 2 * Real.exp (β * T) < 1 := by
    have hρ2 : 0 < ρ ^ 2 := by positivity
    have e : 4 * γ * η * (T + 0) ^ 2 * Real.exp (β * T) =
        (8 * (μ + η) * η * T ^ 2 * Real.exp (β * T)) / ρ ^ 2 := by
      simp only [hγ, add_zero]
      field_simp
      ring
    rw [e, div_lt_one hρ2]
    exact hT
  have hcont : Continuous fun δ : ℝ => 4 * γ * η * (T + δ) ^ 2 * Real.exp (β * T) := by fun_prop
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 4 * γ * η * (T + δ) ^ 2 * Real.exp (β * T) < 1 :=
    nhdsWithin_le_nhds ((hcont.tendsto 0).eventually_lt_const hκ0)
  have hcont2 : Continuous fun δ : ℝ => 2 * η * (t + δ) * Real.exp (β * t) := by fun_prop
  have hlim : Tendsto (fun δ : ℝ => 2 * η * (t + δ) * Real.exp (β * t)) (𝓝[>] 0)
      (𝓝 (2 * η * t * Real.exp (β * t))) := by
    simpa using (hcont2.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev, self_mem_nhdsWithin] with δ hκ hδ
  exact hbar δ hδ hκ

lemma IsTrainingFlow.norm_E_le {G : Matrix m n ℝ → Matrix m n ℝ} {W E E' : ℝ → Matrix m n ℝ}
    {μ η s ε T t : ℝ} (h : IsTrainingFlow (k := k) G W E E' μ η s ε T) (ht : t ∈ Icc 0 T) :
    ‖E t‖ ≤ ‖E 0‖ + η * t := by
  have h1 := norm_image_sub_le_of_norm_deriv_right_le_segment h.Econt h.Ederiv h.Ebound t ht
  have h2 : ‖E t‖ ≤ ‖E t - E 0‖ + ‖E 0‖ := by simpa using norm_add_le (E t - E 0) (E 0)
  rw [sub_zero] at h1
  linarith

/-- **Theorem 1 of arXiv 2306.01485, as its proof shows it: the gradient is frozen on the full
trajectory.**  Let `Y = U S Vᵀ` solve `Ẏ = -P(Y) ∇ℒ(W(t))`, i.e. `Ẏ = P(Y) Ẇ`, the Koch–Lubich
approximation flow of the data `W(t)`, with `Y(0) = W̃(0)` (first bullet of the theorem), let
`‖Ė‖ ≤ η`, `‖∇ℒ(W(t))‖ ≤ μ`, `W̃(t) ∈ ℳ_r ∩ Σ_s(ε)` on `[0, T]` and
`T ≤ (s - ε) / (4 √(2 μ η))`.  Then `‖Y(t) - W(t)‖ ≤ ‖E(0)‖ + 3 t η` on `[0, T]`.

Differences from the paper.
* The flow is **not** the flow (5) of the paper, which evaluates the gradient at `Y`.  The first
  line of the paper's proof, `Ẏ = P(Y) Ẇ̃ + P(Y) Ė`, is the flow here.  For the flow (5) the
  statement is false (`theorem1_false_gradient_flow`); see `theorem1_lipschitz` for a correct form.
* The term `‖E(0)‖` is equality at `t = 0`, so it cannot be dropped.  The paper's proof uses
  `E(0) = 0` silently (`E(t) = ∫₀ᵗ Ė`); see `theorem1_one_step`.
* The paper bounds the curvature term with `‖Ẇ̃‖ ≤ μ`, while only `‖Ẇ̃‖ ≤ μ + η` follows.  The
  stated constants survive: for `2 μ ≤ 3 η` the bound follows from `‖Ẏ‖, ‖Ẇ‖ ≤ μ` alone, and
  otherwise from the sharper curvature constant `2` in place of `32`.
* `S(t)` need not be invertible and `σ_min(Y)` plays no role, only `σ_min(W̃) ≥ s - ε`. -/
theorem theorem1_frozen_gradient {G : Matrix m n ℝ → Matrix m n ℝ} {W E E' Y : ℝ → Matrix m n ℝ}
    {U : ℝ → Matrix m k ℝ} {S : ℝ → Matrix k k ℝ} {V : ℝ → Matrix n k ℝ} {μ η s ε T : ℝ}
    (h : IsTrainingFlow (k := k) G W E E' μ η s ε T) (hs : ε < s) (hμ : 0 < μ) (hη : 0 < η)
    (hfac : ∀ t ∈ Ico 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (-G (W t))) Y 0 T)
    (h0 : Y 0 = W 0 - E 0) (hT : T ≤ (s - ε) / (4 * √(2 * μ * η))) :
    ∀ t ∈ Icc 0 T, ‖Y t - W t‖ ≤ ‖E 0‖ + 3 * t * η := by
  classical
  intro t ht
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  have hρ : 0 < s - ε := sub_pos.2 hs
  have hsq : 0 < √(2 * μ * η) := Real.sqrt_pos.2 (by positivity)
  have h32 : 32 * μ * η * T ^ 2 ≤ (s - ε) ^ 2 := by
    have h1 : T * (4 * √(2 * μ * η)) ≤ s - ε := (le_div_iff₀ (by positivity)).1 hT
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : √(2 * μ * η) ^ 2 = 2 * μ * η := Real.sq_sqrt (by positivity)
    calc 32 * μ * η * T ^ 2 = 16 * T ^ 2 * (2 * μ * η) := by ring
      _ = (T * (4 * √(2 * μ * η))) ^ 2 := by rw [mul_pow, mul_pow, h3]; ring
      _ ≤ (s - ε) ^ 2 := h2
  have hEt := h.norm_E_le ht
  by_cases hc : 2 * μ ≤ 3 * η
  · have hYb : ∀ u ∈ Ico 0 T, ‖tangentProj (U u) (V u) (-G (W u))‖ ≤ μ := fun u hu => by
      obtain ⟨hU, hV, -⟩ := hfac u hu
      refine (isOrthProj_tangentProj hU hV).norm_le _ |>.trans ?_
      rw [norm_neg]
      exact h.grad u (Ico_subset_Icc_self hu)
    have hWb : ∀ u ∈ Ico 0 T, ‖-G (W u)‖ ≤ μ := fun u hu => by
      rw [norm_neg]
      exact h.grad u (Ico_subset_Icc_self hu)
    have h1 := norm_image_sub_le_of_norm_deriv_right_le_segment hY.cont hY.deriv hYb t ht
    have h2 := norm_image_sub_le_of_norm_deriv_right_le_segment h.flow.cont h.flow.deriv hWb t ht
    rw [sub_zero] at h1 h2
    have e : Y t - W t = (Y t - Y 0) - (W t - W 0) - E 0 := by rw [h0]; abel
    have h3 : ‖Y t - W t‖ ≤ ‖Y t - Y 0‖ + ‖W t - W 0‖ + ‖E 0‖ := by
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    have h4 : μ * t * 2 ≤ 3 * η * t := by nlinarith [ht.1]
    nlinarith
  · have hlt : 3 * η < 2 * μ := not_le.1 hc
    have hT' : 8 * (μ + η) * η * T ^ 2 * Real.exp (0 * T) < (s - ε) ^ 2 := by
      have hρ2 : 0 < (s - ε) ^ 2 := by positivity
      rw [zero_mul, Real.exp_zero, mul_one]
      have h5 : (μ + η) ≤ 5 / 3 * μ := by linarith
      have h6 : 8 * (μ + η) * η * T ^ 2 ≤ 8 * (5 / 3 * μ) * η * T ^ 2 := by gcongr
      nlinarith
    have hb := norm_sub_band_le (β := 0) (r := fun _ => 0)
      (Y' := fun t => tangentProj (U t) (V t) (-G (W t))) h hρ hη le_rfl hY.cont hY.deriv hfac
      (fun t _ => by simp) (fun t _ => by simp) h0 hT' t ht
    rw [zero_mul, Real.exp_zero, mul_one] at hb
    have e : Y t - W t = (Y t - (W t - E t)) - E t := by abel
    have h3 : ‖Y t - W t‖ ≤ ‖Y t - (W t - E t)‖ + ‖E t‖ := by
      rw [e]
      exact norm_sub_le _ _
    linarith

/-- **Theorem 1 of arXiv 2306.01485, the bound `3 λ η`**, for one step of length `λ`, under the
hypotheses of `theorem1_frozen_gradient` with `T = λ` and `E(0) = 0`.  This is what the paper's
proof gives ("for `t ∈ [0, λ]`"): the flow is the frozen-gradient flow and `k = 1`. -/
theorem theorem1_one_step {G : Matrix m n ℝ → Matrix m n ℝ} {W E E' Y : ℝ → Matrix m n ℝ}
    {U : ℝ → Matrix m k ℝ} {S : ℝ → Matrix k k ℝ} {V : ℝ → Matrix n k ℝ} {μ η s ε lam : ℝ}
    (h : IsTrainingFlow (k := k) G W E E' μ η s ε lam) (hlam : 0 ≤ lam) (hs : ε < s) (hμ : 0 < μ)
    (hη : 0 < η)
    (hfac : ∀ t ∈ Ico 0 lam, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (-G (W t))) Y 0 lam)
    (h0 : Y 0 = W 0) (hE0 : E 0 = 0) (hT : lam ≤ (s - ε) / (4 * √(2 * μ * η))) :
    ‖Y lam - W lam‖ ≤ 3 * lam * η := by
  have := theorem1_frozen_gradient h hs hμ hη hfac hY (by rw [hE0, sub_zero, h0]) hT lam
    ⟨hlam, le_rfl⟩
  simpa [hE0] using this

/-- **Theorem 1 of arXiv 2306.01485 for `j` steps, with the correct growth**: for the frozen
gradient flow, `‖Y(j λ) - W(j λ)‖ ≤ 3 j λ η` as long as `j λ ≤ T`.  The paper's `3 λ η` for all `k`
is false (`theorem1_false_many_steps`). -/
theorem theorem1_steps {G : Matrix m n ℝ → Matrix m n ℝ} {W E E' Y : ℝ → Matrix m n ℝ}
    {U : ℝ → Matrix m k ℝ} {S : ℝ → Matrix k k ℝ} {V : ℝ → Matrix n k ℝ} {μ η s ε T lam : ℝ}
    (h : IsTrainingFlow (k := k) G W E E' μ η s ε T) (hlam : 0 ≤ lam) (hs : ε < s) (hμ : 0 < μ)
    (hη : 0 < η)
    (hfac : ∀ t ∈ Ico 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (-G (W t))) Y 0 T)
    (h0 : Y 0 = W 0) (hE0 : E 0 = 0) (hT : T ≤ (s - ε) / (4 * √(2 * μ * η))) {j : ℕ}
    (hj : j * lam ≤ T) : ‖Y (j * lam) - W (j * lam)‖ ≤ 3 * (j * lam) * η := by
  have := theorem1_frozen_gradient h hs hμ hη hfac hY (by rw [hE0, sub_zero, h0]) hT (j * lam)
    ⟨by positivity, hj⟩
  simpa [hE0] using this

/-- **A correct form of Theorem 1 of arXiv 2306.01485 for the actual flow (5).**  If the gradient
`G = ∇ℒ` is `β`-Lipschitz, `Y = U S Vᵀ` solves `Ẏ = -P(Y) G(Y)` with `Y(0) = W(0)`, `E(0) = 0`, and
`8 (μ + η) η T² e^{βT} < (s - ε)²`, then `‖Y(t) - W(t)‖ ≤ 3 t η e^{βt}` on `[0, T]`.  Factor
solutions of (5) give such `Y`: `GaugeODE.factorODE_solution_isDLRA_tangentProj` with
`Ȧ(t) = -G(Y(t))`.  Some dependence on the variation of `G` is needed, since the bound without it
is false (`theorem1_false_gradient_flow`).  For `β = 0` and `η ≤ μ`, the time condition is implied
by the paper's `T ≤ (s - ε) / (4 √(2 μ η))`. -/
theorem theorem1_lipschitz {G : Matrix m n ℝ → Matrix m n ℝ} {W E E' Y : ℝ → Matrix m n ℝ}
    {U : ℝ → Matrix m k ℝ} {S : ℝ → Matrix k k ℝ} {V : ℝ → Matrix n k ℝ} {μ η s ε β T : ℝ}
    (h : IsTrainingFlow (k := k) G W E E' μ η s ε T) (hG : ∀ A B, ‖G A - G B‖ ≤ β * ‖A - B‖)
    (hβ : 0 ≤ β) (hs : ε < s) (hη : 0 < η)
    (hfac : ∀ t ∈ Ico 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (-G (Y t))) Y 0 T)
    (h0 : Y 0 = W 0) (hE0 : E 0 = 0)
    (hT : 8 * (μ + η) * η * T ^ 2 * Real.exp (β * T) < (s - ε) ^ 2) :
    ∀ t ∈ Icc 0 T, ‖Y t - W t‖ ≤ 3 * t * η * Real.exp (β * t) := by
  classical
  have hEn : ∀ t ∈ Icc 0 T, ‖E t‖ ≤ η * t := fun t ht => by
    simpa [hE0] using h.norm_E_le ht
  have hb := norm_sub_band_le (β := β) (r := fun t => G (W t) - G (Y t))
    (Y' := fun t => tangentProj (U t) (V t) (-G (Y t))) h (sub_pos.2 hs) hη hβ hY.cont hY.deriv hfac
    (fun t _ => by congr 1; abel) (fun t ht => ?_) (by rw [hE0, sub_zero, h0]) hT
  · intro t ht
    have hexp : 1 ≤ Real.exp (β * t) := Real.one_le_exp (mul_nonneg hβ ht.1)
    have e : Y t - W t = (Y t - (W t - E t)) - E t := by abel
    have h3 : ‖Y t - W t‖ ≤ ‖Y t - (W t - E t)‖ + ‖E t‖ := by
      rw [e]
      exact norm_sub_le _ _
    have h4 := hb t ht
    have h5 := hEn t ht
    have h6 : η * t ≤ η * t * Real.exp (β * t) :=
      le_mul_of_one_le_right (mul_nonneg hη.le ht.1) hexp
    linarith
  · refine (hG _ _).trans (mul_le_mul_of_nonneg_left ?_ hβ)
    have e : W t - Y t = -(Y t - (W t - E t)) + E t := by abel
    rw [e]
    exact (norm_add_le _ _).trans (by
      rw [norm_neg]
      exact add_le_add_right (hEn t (Ico_subset_Icc_self ht)) _)

end Theorem1

/-! ### Counterexamples to Theorem 1 as stated -/

section Counterexamples

open Matrix LeanDLRA.Curvature
open scoped LeanDLRA.Frobenius

/-- `diag(a, b)`. -/
def diag2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]

/-- The factor `U = V = e₁ ∈ ℝ^{2 × 1}`. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

lemma e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

lemma norm_sq_diag2 (a b : ℝ) : ‖diag2 a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [frob_sq]
  simp [diag2, Fin.sum_univ_two]

lemma norm_diag2_le {a b c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 + b ^ 2 ≤ c ^ 2) : ‖diag2 a b‖ ≤ c := by
  rw [← norm_sq_diag2] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).1 h

lemma diag2_factor (a : ℝ) : diag2 a 0 = e₁ * !![a] * e₁ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2, e₁, Matrix.mul_apply]

lemma e₁_mul_transpose : e₁ * e₁ᵀ = diag2 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2, e₁, Matrix.mul_apply]

lemma diag2_mul (a b c d : ℝ) : diag2 a b * diag2 c d = diag2 (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2, Matrix.mul_apply, Fin.sum_univ_two]

lemma tangentProj_diag2 (a b : ℝ) : tangentProj e₁ e₁ (diag2 a b) = diag2 a 0 := by
  rw [tangentProj_apply, Matrix.mul_assoc (diag2 a b), Matrix.mul_assoc (e₁ * e₁ᵀ * diag2 a b),
    e₁_mul_transpose, diag2_mul, diag2_mul, diag2_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

lemma diag2_sub (a b c d : ℝ) : diag2 a b - diag2 c d = diag2 (a - c) (b - d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

lemma neg_diag2 (a b : ℝ) : -diag2 a b = diag2 (-a) (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

lemma mem_sigmaBand_one {a s ε : ℝ} (ha : 0 ≤ a) (h : a ∈ Icc (s - ε) (s + ε)) :
    !![a] ∈ sigmaBand (Fin 1) s ε := by
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  have h1 := EckartYoung.sq_norm_eq_sum_sq_singularValues (!![a] : Matrix (Fin 1) (Fin 1) ℝ)
  rw [frob_sq] at h1
  simp only [Fintype.card_fin, Finset.sum_range_one] at h1
  have h2 : (toEuclideanLin (!![a] : Matrix (Fin 1) (Fin 1) ℝ)).singularValues 0 = a := by
    refine (pow_left_inj₀ (LinearMap.singularValues_nonneg _ 0) ha two_ne_zero).1 ?_
    rw [← h1]
    simp
  rw [h2]
  exact h

lemma diag2_mem_band {a s ε : ℝ} (ha : 0 ≤ a) (h : a ∈ Icc (s - ε) (s + ε)) :
    diag2 a 0 ∈ lowRankBand (Fin 2) (Fin 2) (Fin 1) s ε :=
  ⟨e₁, !![a], e₁, e₁_orth, e₁_orth, mem_sigmaBand_one ha h, diag2_factor a⟩

lemma hasDerivAt_diag2 {a b : ℝ → ℝ} {a' b' t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun t => diag2 (a t) (b t)) (diag2 a' b') t := by
  have e : ∀ x y : ℝ, diag2 x y = x • diag2 1 0 + y • diag2 0 1 := fun x y => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2]
  simp only [e a', e (a _)]
  exact (ha.smul_const _).add (hb.smul_const _)

/-- The numerical check of the step-size condition in the counterexamples. -/
lemma one_le_div_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : 16 * b ≤ a ^ 2) :
    (1 : ℝ) ≤ a / (4 * √b) := by
  have hs : √b ≤ a / 4 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hp : 0 < √b := Real.sqrt_pos.2 hb
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `condOn_layerNet_lowRank_le` applies to a rank-one layer `W = diag(1, 0)` with features on the
first axis: its hypotheses can hold (non-vacuity). -/
example : condOn (Set.range (toEuclideanLin e₁))
    (layerNet (E := fun _ => EuclideanSpace ℝ (Fin 2)) (F := fun _ => EuclideanSpace ℝ (Fin 2))
      (fun _ => toEuclideanLin (e₁ * !![(1 : ℝ)] * e₁ᵀ)) (fun _ => id) 1) ≤
    (∏ _i ∈ Finset.range 1, condOn (univ : Set (EuclideanSpace ℝ (Fin 2))) id) *
      ENNReal.ofReal (1 + 0) ^ 1 :=
  condOn_layerNet_lowRank_le (d := fun _ => 2) (r := fun _ => 1) (τ := 0) le_rfl
    (s := fun _ => 1) (fun _ => one_pos) (U := fun _ => e₁) (S := fun _ => !![1])
    (V := fun _ => e₁) (fun _ => e₁_orth) (fun _ => e₁_orth)
    (fun _ => mem_sigmaBand_one zero_le_one (by norm_num)) (fun _ => continuous_id)
    (Z := fun i => if i = 0 then Set.range (toEuclideanLin e₁) else univ) (A := fun _ => univ) 1
    (fun i hi => by simp [Nat.lt_one_iff.1 hi]) (fun _ _ => mapsTo_univ _ _)
    (fun i hi => by simp [Nat.lt_one_iff.1 hi])
    (fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top (condOn_id_le _))

/-- The linear loss `ℒ(W) = -W₂₂`. -/
def linLoss (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := -W 1 1

/-- The (constant) gradient of `linLoss`. -/
def linGrad (_ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diag2 0 (-1)

/-- The full gradient flow of `linLoss`, starting at `diag(7, 0)`. -/
def linW (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diag2 7 t

/-- The perturbation `E(t) = diag(0, t)`. -/
def linE (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diag2 0 t

/-- `Ė`. -/
def linE' (_ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diag2 0 1

/-- The rank-one solution, at rest. -/
def linY : Matrix (Fin 2) (Fin 2) ℝ := diag2 7 0

lemma linE_zero : linE 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linE, diag2]

lemma hasFDerivAt_linLoss (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt linLoss (innerSL ℝ (linGrad W)) W := by
  have e : linLoss = innerSL ℝ (diag2 0 (-1)) := by
    ext Z
    simp [linLoss, innerSL_apply_apply, Frobenius.inner_def, diag2, Fin.sum_univ_two]
  rw [e]
  exact (innerSL ℝ (diag2 0 (-1))).hasFDerivAt

lemma linFlow {T : ℝ} : IsTrainingFlow (k := Fin 1) linGrad linW linE linE' 1 1 7 1 T where
  flow := by
    have hd : ∀ t, HasDerivAt linW (diag2 0 1) t := fun t =>
      hasDerivAt_diag2 (a := fun _ => 7) (hasDerivAt_const t 7) (hasDerivAt_id t)
    have hg : ∀ w, -linGrad w = diag2 0 1 := fun w => by simp [linGrad, neg_diag2]
    refine ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => ?_⟩
    simpa [hg] using (hd t).hasDerivWithinAt
  band := fun t _ => by
    simp only [linW, linE, diag2_sub, sub_zero, sub_self]
    exact diag2_mem_band (by norm_num) (by norm_num)
  Econt := fun t _ =>
    (hasDerivAt_diag2 (a := fun _ => 0) (hasDerivAt_const t 0)
      (hasDerivAt_id t)).continuousAt.continuousWithinAt
  Ederiv := fun t _ =>
    (hasDerivAt_diag2 (a := fun _ => 0) (hasDerivAt_const t 0) (hasDerivAt_id t)).hasDerivWithinAt
  Ebound := fun t _ => norm_diag2_le zero_le_one (by norm_num)
  grad := fun t _ => norm_diag2_le zero_le_one (by norm_num)

lemma linY_solution {T : ℝ} :
    ODESolution (fun _ _ => tangentProj e₁ e₁ (-linGrad linY)) (fun _ => linY) 0 T := by
  have e : tangentProj e₁ e₁ (-linGrad linY) = 0 := by
    rw [linGrad, neg_diag2, tangentProj_diag2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2]
  refine ⟨continuousOn_const, fun t _ => ?_⟩
  simpa [e] using hasDerivWithinAt_const t (Ici t) linY

/-- `theorem1_frozen_gradient` applies: its hypotheses can hold (non-vacuity).  Here the gradient is
constant, so the frozen and the true flow coincide. -/
example : ‖linY - linW 1‖ ≤ ‖linE 0‖ + 3 * 1 * 1 :=
  theorem1_frozen_gradient (k := Fin 1) (G := linGrad) (W := linW) (E := linE) (E' := linE')
    (Y := fun _ => linY) (U := fun _ => e₁) (V := fun _ => e₁) (S := fun _ => !![7]) (T := 1)
    linFlow (by norm_num) one_pos one_pos (fun _ _ => ⟨e₁_orth, e₁_orth, diag2_factor 7⟩)
    linY_solution (by simp [linY, linW, linE, diag2_sub])
    (one_le_div_sqrt (by norm_num) (by norm_num) (by norm_num)) 1 ⟨zero_le_one, le_rfl⟩

/-- `theorem1_lipschitz` applies: its hypotheses can hold (non-vacuity). -/
example : ‖linY - linW 1‖ ≤ 3 * 1 * 1 * Real.exp (0 * 1) :=
  theorem1_lipschitz (k := Fin 1) (G := linGrad) (W := linW) (E := linE) (E' := linE')
    (Y := fun _ => linY) (U := fun _ => e₁) (V := fun _ => e₁) (S := fun _ => !![7]) (T := 1)
    linFlow (fun _ _ => by simp [linGrad]) le_rfl (by norm_num) one_pos
    (fun _ _ => ⟨e₁_orth, e₁_orth, diag2_factor 7⟩) linY_solution rfl linE_zero
    (by norm_num) 1 ⟨zero_le_one, le_rfl⟩

/-- **The bound `3 λ η` of Theorem 1 of arXiv 2306.01485 is false for `k ≥ 4` steps.**  For the
linear loss `ℒ(W) = -W₂₂` on `ℝ^{2 × 2}`, `r = 1`, `s = 7`, `ε = 1` (so `τ = 1/3`), `μ = η = λ = 1`,
the flow is `W(t) = diag(7, t) = W̃ + E`, with `W̃ = diag(7, 0)`, `E(t) = diag(0, t)`, and all
hypotheses hold, on every `[0, T]`.  The rank-one point `Y = diag(7, 0) = e₁ (7) e₁ᵀ` is stationary
for (5) (here the gradient at `Y` and at `W(t)` coincide) and for Algorithm 1.  But
`‖Y - W(4 λ)‖ = 4 > 3 = 3 λ η`.  The paper's proof only treats `t ∈ [0, λ]`, and the correct bound
grows with the number of steps (`theorem1_steps`). -/
theorem theorem1_false_many_steps :
    IsTrainingFlow (k := Fin 1) linGrad linW linE linE' 1 1 7 1 (4 * 1) ∧
    (∀ W, HasFDerivAt linLoss (innerSL ℝ (linGrad W)) W) ∧
    ODESolution (fun _ _ => tangentProj e₁ e₁ (-linGrad linY)) (fun _ => linY) 0 (4 * 1) ∧
    linY = e₁ * !![(7 : ℝ)] * e₁ᵀ ∧ linY = linW 0 - linE 0 ∧ linE 0 = 0 ∧
    (1 : ℝ) ≤ (7 - 1) / (4 * √(2 * 1 * 1)) ∧
    3 * 1 * 1 < ‖linY - linW (4 * 1)‖ := by
  refine ⟨linFlow, hasFDerivAt_linLoss, linY_solution, diag2_factor 7,
    by simp [linY, linW, linE, diag2_sub], linE_zero,
    one_le_div_sqrt (by norm_num) (by norm_num) (by norm_num), ?_⟩
  · have h : ‖linY - linW (4 * 1)‖ ^ 2 = 16 := by
      simp only [linY, linW, diag2_sub, norm_sq_diag2]
      norm_num
    have hn := norm_nonneg (linY - linW (4 * 1))
    nlinarith

/-- A polynomial loss for which the true flow (5) leaves `W(t)` alone at the rank-one point
`diag(23, 0)`: `ℒ(W) = -W₂₂ + 6 W₂₂³ - 6 W₂₂ (W₁₁ - 23)`. -/
def cexLoss (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  -W 1 1 + 6 * W 1 1 ^ 3 - 6 * (W 1 1 * (W 0 0 - 23))

/-- The gradient of `cexLoss`. -/
def cexGrad (W : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diag2 (-6 * W 1 1) (-1 + 18 * W 1 1 ^ 2 - 6 * (W 0 0 - 23))

/-- The full gradient flow of `cexLoss`: `W(t) = diag(23 + 3 t², t)`. -/
def cexW (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diag2 (23 + 3 * t ^ 2) t

/-- The rank-one stationary point of the flow (5). -/
def cexY : Matrix (Fin 2) (Fin 2) ℝ := diag2 23 0

lemma cexGrad_diag2 (a b : ℝ) :
    cexGrad (diag2 a b) = diag2 (-6 * b) (-1 + 18 * b ^ 2 - 6 * (a - 23)) := by
  simp [cexGrad, diag2]

lemma hasFDerivAt_cexLoss (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt cexLoss (innerSL ℝ (cexGrad W)) W := by
  have ha : HasFDerivAt (fun W : Matrix (Fin 2) (Fin 2) ℝ => W 0 0) (innerSL ℝ (diag2 1 0)) W := by
    have e : (fun W : Matrix (Fin 2) (Fin 2) ℝ => W 0 0) = innerSL ℝ (diag2 1 0) := by
      ext Z
      simp [innerSL_apply_apply, Frobenius.inner_def, diag2, Fin.sum_univ_two]
    rw [e]
    exact (innerSL ℝ (diag2 1 0)).hasFDerivAt
  have hb : HasFDerivAt (fun W : Matrix (Fin 2) (Fin 2) ℝ => W 1 1) (innerSL ℝ (diag2 0 1)) W := by
    have e : (fun W : Matrix (Fin 2) (Fin 2) ℝ => W 1 1) = innerSL ℝ (diag2 0 1) := by
      ext Z
      simp [innerSL_apply_apply, Frobenius.inner_def, diag2, Fin.sum_univ_two]
    rw [e]
    exact (innerSL ℝ (diag2 0 1)).hasFDerivAt
  have h := (hb.neg.add ((hb.pow 3).const_mul 6)).sub ((hb.mul (ha.sub_const 23)).const_mul 6)
  refine h.congr_fderiv ?_
  ext Z
  simp [cexGrad, innerSL_apply_apply, Frobenius.inner_def, diag2, Fin.sum_univ_two]
  ring

lemma cexFlow : IsTrainingFlow (k := Fin 1) cexGrad cexW linE linE' 7 1 23 3 1 where
  flow := by
    have hd : ∀ t, HasDerivAt cexW (diag2 (6 * t) 1) t := fun t => by
      refine hasDerivAt_diag2 (a := fun t => 23 + 3 * t ^ 2) ?_ (hasDerivAt_id t)
      have h : HasDerivAt (fun t : ℝ => 23 + 3 * t ^ 2) (3 * (2 * t)) t := by
        simpa using ((hasDerivAt_id t).pow 2).const_mul 3 |>.const_add 23
      exact h.congr_deriv (by ring)
    have hg : ∀ t, -cexGrad (cexW t) = diag2 (6 * t) 1 := fun t => by
      rw [cexW, cexGrad_diag2, neg_diag2]
      congr 1 <;> ring
    refine ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => ?_⟩
    simpa only [hg] using (hd t).hasDerivWithinAt
  band := fun t ht => by
    simp only [cexW, linE, diag2_sub, sub_zero, sub_self]
    have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    exact diag2_mem_band (by positivity) ⟨by nlinarith [sq_nonneg t], by nlinarith⟩
  Econt := fun t _ =>
    (hasDerivAt_diag2 (a := fun _ => 0) (hasDerivAt_const t 0)
      (hasDerivAt_id t)).continuousAt.continuousWithinAt
  Ederiv := fun t _ =>
    (hasDerivAt_diag2 (a := fun _ => 0) (hasDerivAt_const t 0) (hasDerivAt_id t)).hasDerivWithinAt
  Ebound := fun t _ => norm_diag2_le zero_le_one (by norm_num)
  grad := fun t ht => by
    rw [cexW, cexGrad_diag2]
    refine norm_diag2_le (by norm_num) ?_
    have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith

lemma cexY_grad : cexGrad cexY = diag2 0 (-1) := by
  rw [cexY, cexGrad_diag2]
  congr 1 <;> norm_num

/-- **Theorem 1 of arXiv 2306.01485 is false for the flow (5), already for `k = 1`.**  Theorem 1 has
no Lipschitz hypothesis on `∇ℒ`, and its proof replaces `∇ℒ(Y)` by `∇ℒ(W(t))`.  Take
`ℒ(W) = -W₂₂ + 6 W₂₂³ - 6 W₂₂ (W₁₁ - 23)` on `ℝ^{2 × 2}`, `r = 1`, `s = 23`, `ε = 3` (`τ = 3/10`),
`μ = 7`, `η = λ = 1`.  The gradient flow from `diag(23, 0)` is `W(t) = diag(23 + 3 t², t) = W̃ + E`
with `W̃ = diag(23 + 3 t², 0)`, `E(t) = diag(0, t)`, and all the hypotheses hold, with `E(0) = 0`.
But `∇ℒ(Y)` at `Y = W̃(0) = diag(23, 0) = e₁ (23) e₁ᵀ` is `diag(0, -1)`, which is normal.  Hence
all three right-hand sides of (5) vanish (they contain `∇ℒ(Y) V` or `Uᵀ ∇ℒ(Y)`), `U, S, V` stay put,
Algorithm 1 changes nothing (here `S` is `1 × 1`, so `s = |S|` and the clamp in line 9 is the
identity), and `‖Y - W(λ)‖ = √10 > 3 = 3 λ η`. -/
theorem theorem1_false_gradient_flow :
    IsTrainingFlow (k := Fin 1) cexGrad cexW linE linE' 7 1 23 3 1 ∧
    (∀ W, HasFDerivAt cexLoss (innerSL ℝ (cexGrad W)) W) ∧
    cexGrad cexY * e₁ = 0 ∧ e₁ᵀ * cexGrad cexY = 0 ∧
    ODESolution (fun _ _ => tangentProj e₁ e₁ (-cexGrad cexY)) (fun _ => cexY) 0 1 ∧
    cexY = e₁ * !![(23 : ℝ)] * e₁ᵀ ∧ cexY = cexW 0 - linE 0 ∧ linE 0 = 0 ∧
    (1 : ℝ) ≤ (23 - 3) / (4 * √(2 * 7 * 1)) ∧
    3 * 1 * 1 < ‖cexY - cexW 1‖ := by
  refine ⟨cexFlow, hasFDerivAt_cexLoss, ?_, ?_, ?_, diag2_factor 23, ?_, linE_zero,
    one_le_div_sqrt (by norm_num) (by norm_num) (by norm_num), ?_⟩
  · rw [cexY_grad]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2, e₁, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [cexY_grad]
    ext i j
    fin_cases i
    fin_cases j <;> simp [diag2, e₁, Matrix.mul_apply, Fin.sum_univ_succ]
  · have e : tangentProj e₁ e₁ (-cexGrad cexY) = 0 := by
      rw [cexY_grad, neg_diag2, tangentProj_diag2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diag2]
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    simpa [e] using hasDerivWithinAt_const t (Ici t) cexY
  · simp [cexY, cexW, linE, diag2_sub]
  · have h : ‖cexY - cexW 1‖ ^ 2 = 10 := by
      simp only [cexY, cexW, diag2_sub, norm_sq_diag2]
      norm_num
    have hn := norm_nonneg (cexY - cexW 1)
    nlinarith

end Counterexamples

end LeanDLRA.Literature.P2306_01485
