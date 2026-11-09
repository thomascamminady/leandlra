import LeanDLRA.Literature.Kinetic.P2106_09445a
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Partially regularized entropy closures (arXiv 2404.14312)

Schotthöfer, Laiu and Frank, *Structure-preserving neural networks for the regularized
entropy-based closure of the Boltzmann moment system* (arXiv 2404.14312).  To keep the neural
network closure away from the boundary of the realizable set, the paper regularizes the higher
moments `u_# = (u₁, …, u_n)` of the minimal-entropy closure (Eq. (31)); the dual objective is

    ϕ^γ(α; u) = ⟨exp(α · m)⟩ - α · u + (u₀ γ / 2) ‖α_#‖²        (Eq. (34)),

the multiplier `α^γ_u` is its minimizer (33) and the entropy is `h^γ(u) = -ϕ^γ(α^γ_u; u)` (35).
The paper proves that the multiplier of a normalized moment is obtained from a reduced problem in
`ℝⁿ`, that `h^γ` scales with `u₀`, computes the gradient of `h^γ` and bounds the moment
reconstruction error.  This module formalizes these statements on the velocity quadrature of
`P2106_09445a` (whose dual objective is the case `γ = 0`, `regDualObj_zero`), with `m₀ ≡ c > 0`.

## Main results

* `regDualObj_cons_sub`, **Lemma 1** (`IsRegMultiplier.zeroth_eq`): for a normalized moment,
  `α^γ_{ū,0} = ϑ((α^γ_ū)_#)` with `ϑ(β) = -(log m₀ + log ⟨exp(β · m_#)⟩) / m₀` (Eqs. (39)–(40)).
* **Lemma 2** (`reducedObj_eq`, `convexOn_reducedObj`, `strictConvexOn_reducedObj`): the reduced
  objective `ϕ̂^γ(β; w) = ϕ^γ((ϑ(β), β); (1, w))` equals
  `1/m₀ + (log m₀ + log ⟨exp(β · m_#)⟩)/m₀ - β · w + γ/2 ‖β‖²` (Eq. (44)), is convex, and strictly
  convex for `γ > 0` (log-sum-exp is convex: `convexOn_logAvgExp`, by the weighted
  arithmetic–geometric inequality instead of the paper's Hölder argument).
* **Lemma 3** (`isRegMultiplier_cons_of_isMinOn`, `IsRegMultiplier.isMinOn_reducedObj`): `β`
  minimizes `ϕ̂^γ(·; ū_#)` iff `(ϑ(β), β)` minimizes `ϕ^γ(·; ū)`, with the same minimal value.
* **Lemma 4** (`rayleigh_le_of_psd_add`): the condition number bound `1 + λ̂_max / γ` for
  `Ĥ^γ = Ĥ^0 + γ I` with `Ĥ^0` positive semidefinite, in Rayleigh-quotient form.
* **Theorem 2** (`regEntropy_subgradient`, `regEntropy_fderiv_eq`): `g^γ_u = α^γ_u -
  [γ/2 ‖(α^γ_u)_#‖², 0]` (Eq. (36), `entropyGrad`) is a subgradient of `h^γ` at `u`, hence its
  gradient wherever `h^γ` is differentiable (the envelope argument of B.1, derivative-free).
* **Corollary 1**, convexity part (`convexOn_regEntropy`): `h^γ` is convex on every convex set of
  moments that have multipliers.
* **Theorem 3** (`regDualObj_add_single`, `isRegMultiplier_add_single_iff`,
  `regEntropy_scaling`): `α^γ_u = α^γ_ū + [log u₀ / m₀, 0]` (Eq. (47)) and
  `h^γ(u) = u₀ ĥ^γ(ū_#) + u₀ log u₀ / m₀` (Eq. (49)); `regEntropy_normalized`: `h^γ(ū) = ĥ^γ(ū_#)`.
* **Theorem 4** (`moments_ansatz_of_isRegMultiplier`, `norm_regMoments_sub`,
  `ansatz_entropyGrad`, `moments_ansatz_entropyGrad`, `norm_moments_entropyGrad_sub`,
  `norm_moments_entropyGrad_sub_le`): `ũ^γ = u - u₀ γ [0, β]` (Eq. (51)), `‖ũ^γ - u‖ = u₀ γ ‖β‖`
  (Eq. (52)), `u^γ = exp(-γ m₀ ‖β‖² / 2) ũ^γ` (Eq. (106)) and
  `‖u^γ - u‖ ≤ u₀ γ M + (1 - exp(-γ m₀ M² / 2)) ‖ũ^γ‖` for `‖β‖ ≤ M` (Eqs. (53), (107)), with
  `β = (α^γ_u)_#`; `norm_psi_sub` is Eq. (67).
* **Theorem 5**, entropy dissipation (`entropyGrad_dot_moments_le`, Eq. (113)): with the ansatz
  `f^γ_u = exp(g^γ_u · m)`, `∇h^γ · ⟨m Q(f^γ_u)⟩ = ⟨η'(f^γ_u) Q(f^γ_u)⟩ ≤ 0` whenever the
  collision term dissipates the kinetic entropy (Eq. (6), a hypothesis on `Q` as in the paper).

## Differences from the paper

The velocity integral is a quadrature with positive weights.  Multipliers are given minimizers
(existence and strong duality (35) are quoted by the paper from [16]; here `h^γ` is *defined* as
`-ϕ^γ` at a multiplier).  Theorem 2 is stated through the subgradient inequality; the paper's
differentiability of `h^γ` is assumed where the gradient is identified.  Lemma 4 is proved for any
positive semidefinite `Ĥ^0`; that `Ĥ^γ = Ĥ^0 + γ I` is the Hessian of (44) is not formalized.
Not formalized: Theorem 1 (divergence of `h` at `∂R`, a statement about measures), the strict
convexity of `ĥ^γ` and `h^γ` (Theorem 3, Corollary 1; only convexity is proved), the
hyperbolicity part of Theorem 5, the spherical-harmonics bound (108)–(109) and the neural network
results.  **Printed formulas without `m₀`**: Eq. (38) reads `f^γ_u = exp(-γ/2 ‖(α^γ_u)_#‖²) f̃^γ_u`
and Eq. (53) has `exp(-γ M²/2)`, while the proof ((106)–(107)) has the factor `m₀` in the
exponent.  We prove the version with `m₀`; `ansatz_entropyGrad_eq_printed_iff` shows that (38) as
printed holds iff `m₀ = 1` or `(α^γ_u)_# = 0` (for `γ > 0`);
`norm_moments_entropyGrad_sub_le_of_le_one`
recovers the printed (53) when `m₀ ≤ 1`, which is the case for the normalized spherical harmonics
used in the paper (`m₀ = (4π)^{-1/2}`), so (53) itself is correct in the paper's setting.
-/

open Finset
open scoped Matrix

namespace LeanDLRA.Literature.P2404_14312

open LeanDLRA LeanDLRA.Literature.P2106_09445

variable {V : Type*} [Fintype V] {n : ℕ}

/-! ### The partially regularized dual problem -/

/-- The **partially regularized dual objective** (Eq. (34)):
`ϕ^γ(α; u) = ⟨exp(α · m)⟩ - α · u + (u₀ γ / 2) ‖α_#‖²`. -/
noncomputable def regDualObj (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (γ : ℝ)
    (α u : Fin (n + 1) → ℝ) : ℝ :=
  dualObj w m α u + u 0 * γ / 2 * (Fin.tail α ⬝ᵥ Fin.tail α)

/-- `α` is the **regularized multiplier** of `u`: a minimizer of `ϕ^γ(·; u)` (Eq. (33)); the
entropy is `h^γ(u) = -ϕ^γ(α; u)` (Eq. (35)). -/
def IsRegMultiplier (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (γ : ℝ) (u α : Fin (n + 1) → ℝ) :
    Prop :=
  ∀ β, regDualObj w m γ α u ≤ regDualObj w m γ β u

/-- Bridge to the unregularized closure of `P2106_09445a`: `ϕ^0 = ϕ`. -/
@[simp] theorem regDualObj_zero (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (α u : Fin (n + 1) → ℝ) :
    regDualObj w m 0 α u = dualObj w m α u := by
  simp [regDualObj]

/-- Bridge: for `γ = 0` the regularized multipliers are the multipliers of `P2106_09445a`. -/
theorem isRegMultiplier_zero_iff (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (u α : Fin (n + 1) → ℝ) :
    IsRegMultiplier w m 0 u α ↔ IsMultiplier w m u α := by
  simp [IsRegMultiplier, IsMultiplier]

/-- The reduced partition function `S(β) = ⟨exp(β · m_#)⟩`. -/
noncomputable def partFun (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (β : Fin n → ℝ) : ℝ :=
  avg w fun v => Real.exp (β ⬝ᵥ reducedBasis m v)

/-- The **reduced objective** `ϕ̂^γ(β; x) = ϕ^γ((ϑ(β), β); (1, x))` (Eq. (41)). -/
noncomputable def reducedObj (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (c γ : ℝ) (β x : Fin n → ℝ) :
    ℝ :=
  regDualObj w m γ (Fin.cons (zerothMultiplier w c (reducedBasis m) β) β) (Fin.cons 1 x)

/-- The **gradient of the regularized entropy** (Eq. (36)):
`g^γ = α - [γ/2 ‖α_#‖², 0]`. -/
noncomputable def entropyGrad (γ : ℝ) (α : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  α - Pi.single 0 (γ / 2 * (Fin.tail α ⬝ᵥ Fin.tail α))

lemma partFun_pos [Nonempty V] {w : V → ℝ} (hw : ∀ v, 0 < w v) (m : V → Fin (n + 1) → ℝ)
    (β : Fin n → ℝ) : 0 < partFun w m β :=
  avg_pos hw fun _ => Real.exp_pos _

section Zeroth

variable {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c : ℝ}

/-- `⟨exp((a, β) · m)⟩ = exp(c a) S(β)` when `m₀ ≡ c`. -/
lemma avg_ansatz_cons (hm0 : ∀ v, m v 0 = c) (a : ℝ) (β : Fin n → ℝ) :
    avg w (ansatz m (Fin.cons a β)) = Real.exp (c * a) * partFun w m β := by
  simp only [avg, ansatz, cons_dotProduct, hm0, partFun, reducedBasis, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [Real.exp_add, mul_comm a c]; ring

/-- `exp(c ϑ(β)) S(β) = 1 / c`. -/
lemma exp_mul_zerothMultiplier [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c) (β : Fin n → ℝ) :
    Real.exp (c * zerothMultiplier w c (reducedBasis m) β) * partFun w m β = 1 / c := by
  have hS := partFun_pos hw m β
  have : c * zerothMultiplier w c (reducedBasis m) β = -(Real.log c + Real.log (partFun w m β)) :=
    by rw [zerothMultiplier]; field_simp; rfl
  rw [this, Real.exp_neg, Real.exp_add, Real.exp_log hc, Real.exp_log hS]
  field_simp

/-- **The zeroth multiplier is a one-dimensional minimization**: for a normalized moment
(`u₀ = 1`),
`ϕ^γ((a, β); u) - ϕ^γ((ϑ(β), β); u) = (exp(c (a - ϑ(β))) - 1 - c (a - ϑ(β))) / c ≥ 0`. -/
theorem regDualObj_cons_sub [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c) (hm0 : ∀ v, m v 0 = c)
    (γ : ℝ) {u : Fin (n + 1) → ℝ} (hu : u 0 = 1) (a : ℝ) (β : Fin n → ℝ) :
    regDualObj w m γ (Fin.cons a β) u -
        regDualObj w m γ (Fin.cons (zerothMultiplier w c (reducedBasis m) β) β) u =
      (Real.exp (c * (a - zerothMultiplier w c (reducedBasis m) β)) - 1 -
        c * (a - zerothMultiplier w c (reducedBasis m) β)) / c := by
  set θ := zerothMultiplier w c (reducedBasis m) β
  have h1 : Real.exp (c * a) * partFun w m β = Real.exp (c * (a - θ)) / c := by
    have h := exp_mul_zerothMultiplier (m := m) hw hc β
    have : Real.exp (c * a) = Real.exp (c * (a - θ)) * Real.exp (c * θ) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, mul_assoc, h]; ring
  have h2 : Real.exp (c * θ) * partFun w m β = 1 / c := exp_mul_zerothMultiplier hw hc β
  simp only [regDualObj, dualObj, avg_ansatz_cons hm0, cons_dotProduct, hu, Fin.tail_cons, h1, h2]
  field_simp
  ring

/-- The regularized objective is bounded below by the reduced objective of its tail. -/
theorem reducedObj_le_regDualObj [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c)
    (hm0 : ∀ v, m v 0 = c) (γ : ℝ) (x : Fin n → ℝ) (α : Fin (n + 1) → ℝ) :
    reducedObj w m c γ (Fin.tail α) x ≤ regDualObj w m γ α (Fin.cons 1 x) := by
  have h := regDualObj_cons_sub hw hc hm0 γ (u := Fin.cons 1 x) (by simp) (α 0) (Fin.tail α)
  rw [Fin.cons_self_tail] at h
  rw [reducedObj, ← sub_nonneg, h]
  refine div_nonneg ?_ hc.le
  linarith [Real.add_one_le_exp (c * (α 0 - zerothMultiplier w c (reducedBasis m) (Fin.tail α)))]

/-- **Lemma 1** (arXiv 2404.14312): for a normalized moment `ū = (1, x)` and `m₀ ≡ c > 0`, the
regularized multiplier satisfies `α_{ū,0} = ϑ((α_ū)_#)` (Eq. (39)). -/
theorem IsRegMultiplier.zeroth_eq [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c)
    (hm0 : ∀ v, m v 0 = c) {γ : ℝ} {x : Fin n → ℝ} {α : Fin (n + 1) → ℝ}
    (hα : IsRegMultiplier w m γ (Fin.cons 1 x) α) :
    α 0 = zerothMultiplier w c (reducedBasis m) (Fin.tail α) := by
  set θ := zerothMultiplier w c (reducedBasis m) (Fin.tail α)
  have h := regDualObj_cons_sub hw hc hm0 γ (u := Fin.cons 1 x) (by simp) (α 0) (Fin.tail α)
  rw [Fin.cons_self_tail] at h
  have hle := hα (Fin.cons θ (Fin.tail α))
  by_contra hne
  have hz : c * (α 0 - θ) ≠ 0 := mul_ne_zero hc.ne' (sub_ne_zero.2 hne)
  have := Real.add_one_lt_exp hz
  have hpos : 0 < (Real.exp (c * (α 0 - θ)) - 1 - c * (α 0 - θ)) / c := div_pos (by linarith) hc
  linarith

end Zeroth

/-! ### Lemma 2: the reduced objective -/

section Reduced

variable {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c : ℝ}

/-- **Lemma 2**, Eq. (44):
`ϕ̂^γ(β; x) = 1/c + (log c + log ⟨exp(β · m_#)⟩)/c - β · x + γ/2 ‖β‖²`. -/
theorem reducedObj_eq [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c) (hm0 : ∀ v, m v 0 = c)
    (γ : ℝ) (β x : Fin n → ℝ) :
    reducedObj w m c γ β x = 1 / c + (Real.log c + Real.log (partFun w m β)) / c - β ⬝ᵥ x +
      γ / 2 * (β ⬝ᵥ β) := by
  have h2 := exp_mul_zerothMultiplier (m := m) hw hc β
  simp only [reducedObj, regDualObj, dualObj, avg_ansatz_cons hm0, cons_dotProduct,
    Fin.cons_zero, Fin.tail_cons]
  rw [h2]
  simp only [zerothMultiplier, partFun]
  ring

/-- **Log-sum-exp is convex**: `β ↦ log ⟨exp(β · m_#)⟩` is convex (Lemma 2; the weighted
arithmetic–geometric mean inequality `exp(t a + s b) ≤ t exp a + s exp b` replaces Hölder). -/
theorem convexOn_logAvgExp [Nonempty V] (hw : ∀ v, 0 < w v) (mr : V → Fin n → ℝ) :
    ConvexOn ℝ Set.univ fun β : Fin n → ℝ => Real.log (avg w fun v => Real.exp (β ⬝ᵥ mr v)) := by
  refine ⟨convex_univ, fun β _ β' _ t s ht hs hts => ?_⟩
  set A := avg w fun v => Real.exp (β ⬝ᵥ mr v)
  set B := avg w fun v => Real.exp (β' ⬝ᵥ mr v)
  have hA : 0 < A := avg_pos hw fun _ => Real.exp_pos _
  have hB : 0 < B := avg_pos hw fun _ => Real.exp_pos _
  have hpt : ∀ v, Real.exp ((t • β + s • β') ⬝ᵥ mr v) ≤
      Real.exp (t * Real.log A + s * Real.log B) *
        (t * (Real.exp (β ⬝ᵥ mr v) / A) + s * (Real.exp (β' ⬝ᵥ mr v) / B)) := by
    intro v
    have hcv := convexOn_exp.2 (Set.mem_univ (β ⬝ᵥ mr v - Real.log A))
      (Set.mem_univ (β' ⬝ᵥ mr v - Real.log B)) ht hs hts
    simp only [smul_eq_mul] at hcv
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log hA, Real.exp_log hB] at hcv
    have : Real.exp ((t • β + s • β') ⬝ᵥ mr v) = Real.exp (t * Real.log A + s * Real.log B) *
        Real.exp (t * (β ⬝ᵥ mr v - Real.log A) + s * (β' ⬝ᵥ mr v - Real.log B)) := by
      rw [← Real.exp_add, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
        smul_eq_mul]
      ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_left hcv (Real.exp_pos _).le
  have hsum : (avg w fun v => Real.exp ((t • β + s • β') ⬝ᵥ mr v)) ≤
      Real.exp (t * Real.log A + s * Real.log B) := by
    calc (avg w fun v => Real.exp ((t • β + s • β') ⬝ᵥ mr v))
        ≤ avg w fun v => Real.exp (t * Real.log A + s * Real.log B) *
            (t * (Real.exp (β ⬝ᵥ mr v) / A) + s * (Real.exp (β' ⬝ᵥ mr v) / B)) :=
          sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hpt v) (hw v).le
      _ = Real.exp (t * Real.log A + s * Real.log B) * (t * (A / A) + s * (B / B)) := by
          simp only [avg, A, B, mul_add, sum_add_distrib, mul_sum, sum_div]
          congr 1 <;> refine sum_congr rfl fun v _ => by ring
      _ = Real.exp (t * Real.log A + s * Real.log B) := by
          rw [div_self hA.ne', div_self hB.ne', mul_one, mul_one, hts, mul_one]
  have hpos : 0 < avg w fun v => Real.exp ((t • β + s • β') ⬝ᵥ mr v) :=
    avg_pos hw fun _ => Real.exp_pos _
  calc Real.log (avg w fun v => Real.exp ((t • β + s • β') ⬝ᵥ mr v))
      ≤ Real.log (Real.exp (t * Real.log A + s * Real.log B)) := Real.log_le_log hpos hsum
    _ = t • Real.log A + s • Real.log B := by rw [Real.log_exp]; rfl

/-- `‖t β + s β'‖² = t ‖β‖² + s ‖β'‖² - t s ‖β - β'‖²` for `t + s = 1`. -/
lemma dotProduct_self_combo (β β' : Fin n → ℝ) {t s : ℝ} (hts : t + s = 1) :
    (t • β + s • β') ⬝ᵥ (t • β + s • β') =
      t * (β ⬝ᵥ β) + s * (β' ⬝ᵥ β') - t * s * ((β - β') ⬝ᵥ (β - β')) := by
  have hs : s = 1 - t := by linarith
  subst hs
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, sub_dotProduct,
    dotProduct_sub, smul_eq_mul, dotProduct_comm β' β]
  ring

/-- **Lemma 2**, convexity: `ϕ̂^γ(·; x)` is convex for `γ ≥ 0`. -/
theorem convexOn_reducedObj [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c) (hm0 : ∀ v, m v 0 = c)
    {γ : ℝ} (hγ : 0 ≤ γ) (x : Fin n → ℝ) :
    ConvexOn ℝ Set.univ fun β => reducedObj w m c γ β x := by
  refine ⟨convex_univ, fun β _ β' _ t s ht hs hts => ?_⟩
  have hL := (convexOn_logAvgExp hw (reducedBasis m)).2 (Set.mem_univ β) (Set.mem_univ β') ht hs hts
  simp only [smul_eq_mul] at hL ⊢
  rw [reducedObj_eq hw hc hm0, reducedObj_eq hw hc hm0, reducedObj_eq hw hc hm0,
    dotProduct_self_combo β β' hts]
  simp only [partFun, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hq : 0 ≤ t * s * ((β - β') ⬝ᵥ (β - β')) :=
    mul_nonneg (mul_nonneg ht hs) (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have hs1 : s = 1 - t := by linarith
  have key : (Real.log c + Real.log (avg w fun v => Real.exp ((t • β + s • β') ⬝ᵥ
      reducedBasis m v))) / c ≤ t * ((Real.log c + Real.log (avg w fun v =>
      Real.exp (β ⬝ᵥ reducedBasis m v))) / c) + s * ((Real.log c + Real.log (avg w fun v =>
      Real.exp (β' ⬝ᵥ reducedBasis m v))) / c) := by
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hc.le
    have hlc : t * Real.log c + s * Real.log c = Real.log c := by rw [← add_mul, hts, one_mul]
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hL ⊢
    linarith
  have hγq : 0 ≤ γ / 2 * (t * s * ((β - β') ⬝ᵥ (β - β'))) := mul_nonneg (by linarith) hq
  have h1c : t * (1 / c) + s * (1 / c) = 1 / c := by rw [← add_mul, hts, one_mul]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at key
  linarith

/-- **Lemma 2**, strict convexity: `ϕ̂^γ(·; x)` is strictly convex for `γ > 0`. -/
theorem strictConvexOn_reducedObj [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c)
    (hm0 : ∀ v, m v 0 = c) {γ : ℝ} (hγ : 0 < γ) (x : Fin n → ℝ) :
    StrictConvexOn ℝ Set.univ fun β => reducedObj w m c γ β x := by
  refine ⟨convex_univ, fun β _ β' _ hne t s ht hs hts => ?_⟩
  have hL := (convexOn_logAvgExp hw (reducedBasis m)).2 (Set.mem_univ β) (Set.mem_univ β')
    ht.le hs.le hts
  simp only [smul_eq_mul] at hL ⊢
  rw [reducedObj_eq hw hc hm0, reducedObj_eq hw hc hm0, reducedObj_eq hw hc hm0,
    dotProduct_self_combo β β' hts]
  simp only [partFun, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hd : 0 < (β - β') ⬝ᵥ (β - β') := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) ?_
    intro h
    exact hne (sub_eq_zero.1 (dotProduct_self_eq_zero.1 h.symm))
  have hq : 0 < t * s * ((β - β') ⬝ᵥ (β - β')) := mul_pos (mul_pos ht hs) hd
  have key : (Real.log c + Real.log (avg w fun v => Real.exp ((t • β + s • β') ⬝ᵥ
      reducedBasis m v))) / c ≤ t * ((Real.log c + Real.log (avg w fun v =>
      Real.exp (β ⬝ᵥ reducedBasis m v))) / c) + s * ((Real.log c + Real.log (avg w fun v =>
      Real.exp (β' ⬝ᵥ reducedBasis m v))) / c) := by
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hc.le
    have hlc : t * Real.log c + s * Real.log c = Real.log c := by rw [← add_mul, hts, one_mul]
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hL ⊢
    linarith
  have hγq : 0 < γ / 2 * (t * s * ((β - β') ⬝ᵥ (β - β'))) := mul_pos (by linarith) hq
  have h1c : t * (1 / c) + s * (1 / c) = 1 / c := by rw [← add_mul, hts, one_mul]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at key
  linarith

end Reduced

/-! ### Lemma 3: reduction to `ℝⁿ` -/

section Lemma3

variable {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c γ : ℝ}

/-- **Lemma 3** (arXiv 2404.14312): if `β` minimizes the reduced objective `ϕ̂^γ(·; x)`, then
`(ϑ(β), β)` is the regularized multiplier of the normalized moment `(1, x)` (Eq. (46)), and
`ϕ^γ(α^γ_ū; ū) = ϕ̂^γ(β; ū_#)`. -/
theorem isRegMultiplier_cons_of_isMinOn [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c)
    (hm0 : ∀ v, m v 0 = c) {x β : Fin n → ℝ}
    (hβ : IsMinOn (fun b => reducedObj w m c γ b x) Set.univ β) :
    IsRegMultiplier w m γ (Fin.cons 1 x) (Fin.cons (zerothMultiplier w c (reducedBasis m) β) β) ∧
      regDualObj w m γ (Fin.cons (zerothMultiplier w c (reducedBasis m) β) β) (Fin.cons 1 x) =
        reducedObj w m c γ β x :=
  ⟨fun α => (hβ (Set.mem_univ (Fin.tail α))).trans (reducedObj_le_regDualObj hw hc hm0 γ x α),
    rfl⟩

/-- **Lemma 3**, converse: the tail of a regularized multiplier of `(1, x)` minimizes the reduced
objective, and its zeroth entry is `ϑ` of the tail (so the multiplier is unique iff the reduced
minimizer is). -/
theorem IsRegMultiplier.isMinOn_reducedObj [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c)
    (hm0 : ∀ v, m v 0 = c) {x : Fin n → ℝ} {α : Fin (n + 1) → ℝ}
    (hα : IsRegMultiplier w m γ (Fin.cons 1 x) α) :
    IsMinOn (fun b => reducedObj w m c γ b x) Set.univ (Fin.tail α) ∧
      regDualObj w m γ α (Fin.cons 1 x) = reducedObj w m c γ (Fin.tail α) x := by
  have h0 := hα.zeroth_eq hw hc hm0
  have heq : regDualObj w m γ α (Fin.cons 1 x) = reducedObj w m c γ (Fin.tail α) x := by
    conv_lhs => rw [← Fin.cons_self_tail α, h0]
    rfl
  refine ⟨fun b _ => ?_, heq⟩
  change reducedObj w m c γ (Fin.tail α) x ≤ reducedObj w m c γ b x
  rw [← heq]
  exact hα (Fin.cons (zerothMultiplier w c (reducedBasis m) b) b)

end Lemma3

/-! ### Lemma 4: the condition number of the regularized Hessian -/

/-- **Lemma 4** (arXiv 2404.14312), Rayleigh-quotient form: if `Ĥ^0` is positive semidefinite
with largest Rayleigh quotient at most `λ̂_max`, then every Rayleigh quotient of
`Ĥ^γ = Ĥ^0 + γ I` is at most `1 + γ⁻¹ λ̂_max` times every other one, i.e.
`cond(Ĥ^γ) ≤ 1 + γ⁻¹ λ̂_max` (Eq. (98)). -/
theorem rayleigh_le_of_psd_add {H : Matrix (Fin n) (Fin n) ℝ} {γ lam : ℝ} (hγ : 0 < γ)
    (hpsd : ∀ y, 0 ≤ y ⬝ᵥ (H *ᵥ y)) (hmax : ∀ y, y ⬝ᵥ (H *ᵥ y) ≤ lam * (y ⬝ᵥ y))
    {x y : Fin n → ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ⬝ᵥ ((H + γ • 1) *ᵥ x) / (x ⬝ᵥ x) ≤
      (1 + lam / γ) * (y ⬝ᵥ ((H + γ • 1) *ᵥ y) / (y ⬝ᵥ y)) := by
  have hxx : 0 < x ⬝ᵥ x := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    (fun h => hx (dotProduct_self_eq_zero.1 h.symm))
  have hyy : 0 < y ⬝ᵥ y := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    (fun h => hy (dotProduct_self_eq_zero.1 h.symm))
  have e : ∀ z : Fin n → ℝ, z ⬝ᵥ ((H + γ • 1) *ᵥ z) = z ⬝ᵥ (H *ᵥ z) + γ * (z ⬝ᵥ z) := by
    intro z
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  rw [e, e]
  have hlam : 0 ≤ lam := by
    by_contra h
    have := hmax x
    nlinarith [hpsd x]
  have h1 : (x ⬝ᵥ (H *ᵥ x) + γ * (x ⬝ᵥ x)) / (x ⬝ᵥ x) ≤ lam + γ := by
    rw [div_le_iff₀ hxx]; nlinarith [hmax x]
  have h2 : γ ≤ (y ⬝ᵥ (H *ᵥ y) + γ * (y ⬝ᵥ y)) / (y ⬝ᵥ y) := by
    rw [le_div_iff₀ hyy]; nlinarith [hpsd y]
  calc (x ⬝ᵥ (H *ᵥ x) + γ * (x ⬝ᵥ x)) / (x ⬝ᵥ x) ≤ lam + γ := h1
    _ = (1 + lam / γ) * γ := by field_simp; ring
    _ ≤ (1 + lam / γ) * ((y ⬝ᵥ (H *ᵥ y) + γ * (y ⬝ᵥ y)) / (y ⬝ᵥ y)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ### Theorem 2 and Corollary 1: the gradient and convexity of `h^γ` -/

section Theorem2

variable {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {γ : ℝ}

/-- `ϕ^γ(α; ·)` is affine in the moments with slope `-g^γ(α)`. -/
lemma regDualObj_sub_regDualObj (α u u' : Fin (n + 1) → ℝ) :
    regDualObj w m γ α u' - regDualObj w m γ α u = -(entropyGrad γ α ⬝ᵥ (u' - u)) := by
  simp only [regDualObj, dualObj, entropyGrad, sub_dotProduct, dotProduct_sub, single_dotProduct]
  ring

/-- **Theorem 2** (arXiv 2404.14312), envelope form: for every `α` and every regularized
multiplier `α'` of `u'`, `-ϕ^γ(α; u) + g^γ(α) · (u' - u) ≤ -ϕ^γ(α'; u')`.  For `α = α^γ_u` this
says that `g^γ_u = α^γ_u - [γ/2 ‖(α^γ_u)_#‖², 0]` is a subgradient of `h^γ = -ϕ^γ(α^γ_·; ·)`:
`h^γ(u') ≥ h^γ(u) + g^γ_u · (u' - u)`. -/
theorem regEntropy_subgradient (α : Fin (n + 1) → ℝ) {u u' α' : Fin (n + 1) → ℝ}
    (hα' : IsRegMultiplier w m γ u' α') :
    -regDualObj w m γ α u + entropyGrad γ α ⬝ᵥ (u' - u) ≤ -regDualObj w m γ α' u' := by
  have h1 := hα' α
  have h2 := regDualObj_sub_regDualObj (w := w) (m := m) (γ := γ) α u u'
  linarith

/-- **Theorem 2** (arXiv 2404.14312), Eq. (36): if `h^γ` (any function equal to `-ϕ^γ` at
multipliers `A u'` near `u`) is differentiable at `u`, its derivative is `v ↦ g^γ_u · v`. -/
theorem regEntropy_fderiv_eq {H : (Fin (n + 1) → ℝ) → ℝ} {A : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {u : Fin (n + 1) → ℝ} {D : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hA : ∀ᶠ u' in nhds u, IsRegMultiplier w m γ u' (A u') ∧ H u' = -regDualObj w m γ (A u') u')
    (hD : HasFDerivAt H D u) (v : Fin (n + 1) → ℝ) : D v = entropyGrad γ (A u) ⬝ᵥ v := by
  set g := entropyGrad γ (A u)
  let L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ := ∑ i, g i • ContinuousLinearMap.proj i
  have hL : ∀ z, L z = g ⬝ᵥ z := by
    intro z; simp [L, dotProduct]
  obtain ⟨-, hHu⟩ := hA.self_of_nhds
  have hmin : IsLocalMin (fun u' => H u' - L u') u := by
    filter_upwards [hA] with u' ⟨hAu', hHu'⟩
    have h := regEntropy_subgradient (u := u) (A u) hAu'
    change H u - L u ≤ H u' - L u'
    rw [hL, hL, hHu, hHu']
    rw [dotProduct_sub] at h
    linarith
  have := hmin.hasFDerivAt_eq_zero (hD.sub L.hasFDerivAt)
  have hv := congrArg (fun T : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => T v) this
  have hv' : D v = L v := by simpa [sub_eq_zero] using hv
  rw [hv', hL]

/-- **Corollary 1**, convexity part: on a convex set `s` of moments with regularized multipliers
`A u`, the entropy `h^γ(u) = -ϕ^γ(A u; u)` is convex (strict convexity, which the paper derives
via the perspective of `ĥ^γ`, is not formalized). -/
theorem convexOn_regEntropy {s : Set (Fin (n + 1) → ℝ)} (hs : Convex ℝ s)
    {A : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hA : ∀ u ∈ s, IsRegMultiplier w m γ u (A u)) :
    ConvexOn ℝ s fun u => -regDualObj w m γ (A u) u := by
  refine ⟨hs, fun u hu u' hu' a b ha hb hab => ?_⟩
  set z := a • u + b • u'
  have hz : z ∈ s := hs hu hu' ha hb hab
  have h1 := regEntropy_subgradient (u := z) (A z) (hA u hu)
  have h2 := regEntropy_subgradient (u := z) (A z) (hA u' hu')
  have hcomb : a • (u - z) + b • (u' - z) = 0 := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul, sub_self]
  have hdot : a * (entropyGrad γ (A z) ⬝ᵥ (u - z)) + b * (entropyGrad γ (A z) ⬝ᵥ (u' - z)) = 0 := by
    have := congrArg (fun y => entropyGrad γ (A z) ⬝ᵥ y) hcomb
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] using this
  change -regDualObj w m γ (A z) z ≤ a * -regDualObj w m γ (A u) u + b * -regDualObj w m γ (A u') u'
  have e1 := mul_le_mul_of_nonneg_left h1 ha
  have e2 := mul_le_mul_of_nonneg_left h2 hb
  have e3 : a * -regDualObj w m γ (A z) z + b * -regDualObj w m γ (A z) z =
      -regDualObj w m γ (A z) z := by rw [← add_mul, hab, one_mul]
  nlinarith

end Theorem2

/-! ### Theorem 3: scaling with the zeroth moment -/

section Theorem3

variable {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {c γ : ℝ}

lemma tail_add_single_zero (α : Fin (n + 1) → ℝ) (s : ℝ) :
    Fin.tail (α + Pi.single 0 s) = Fin.tail α := by
  funext i
  simp [Fin.tail, Fin.succ_ne_zero]

/-- The regularized objective under normalization: with `s = log u₀ / c`,
`ϕ^γ(α + s e₀; u) = u₀ ϕ^γ(α; u / u₀) - u₀ log u₀ / c`. -/
theorem regDualObj_add_single (hc : c ≠ 0) (hm0 : ∀ v, m v 0 = c) {u : Fin (n + 1) → ℝ}
    (hu : 0 < u 0) (α : Fin (n + 1) → ℝ) :
    regDualObj w m γ (α + Pi.single 0 (Real.log (u 0) / c)) u =
      u 0 * regDualObj w m γ α ((u 0)⁻¹ • u) - u 0 * Real.log (u 0) / c := by
  rw [regDualObj, dualObj_add_single hc hm0 hu, tail_add_single_zero, regDualObj]
  simp only [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hu.ne']
  ring

/-- **Theorem 3** (arXiv 2404.14312), Eq. (47): `α^γ_u = α^γ_ū + [log u₀ / m₀, 0]`, in the form:
`α` is a regularized multiplier of `ū = u / u₀` iff `α + (log u₀ / c) e₀` is one of `u`. -/
theorem isRegMultiplier_add_single_iff (hc : c ≠ 0) (hm0 : ∀ v, m v 0 = c)
    {u : Fin (n + 1) → ℝ} (hu : 0 < u 0) (α : Fin (n + 1) → ℝ) :
    IsRegMultiplier w m γ ((u 0)⁻¹ • u) α ↔
      IsRegMultiplier w m γ u (α + Pi.single 0 (Real.log (u 0) / c)) := by
  constructor
  · intro h β
    have hβ := h (β - Pi.single 0 (Real.log (u 0) / c))
    have e := regDualObj_add_single (w := w) (γ := γ) hc hm0 hu
      (β - Pi.single 0 (Real.log (u 0) / c))
    rw [sub_add_cancel] at e
    rw [regDualObj_add_single hc hm0 hu, e]
    have := mul_le_mul_of_nonneg_left hβ hu.le
    linarith
  · intro h β
    have hβ := h (β + Pi.single 0 (Real.log (u 0) / c))
    rw [regDualObj_add_single hc hm0 hu, regDualObj_add_single hc hm0 hu] at hβ
    have : u 0 * regDualObj w m γ α ((u 0)⁻¹ • u) ≤ u 0 * regDualObj w m γ β ((u 0)⁻¹ • u) := by
      linarith
    exact le_of_mul_le_mul_left this hu

/-- The normalized moment `u / u₀` is `(1, u_# / u₀)`. -/
lemma smul_inv_eq_cons {u : Fin (n + 1) → ℝ} (hu : 0 < u 0) :
    (u 0)⁻¹ • u = Fin.cons 1 (Fin.tail ((u 0)⁻¹ • u)) := by
  conv_lhs => rw [← Fin.cons_self_tail ((u 0)⁻¹ • u)]
  simp [inv_mul_cancel₀ hu.ne']

/-- **Theorem 3**, `h^γ(ū) = ĥ^γ(ū_#)`: at a normalized moment the entropy is the reduced
entropy `ĥ^γ(x) = -ϕ̂^γ(β_x; x)` (Eq. (43)). -/
theorem regEntropy_normalized [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c)
    (hm0 : ∀ v, m v 0 = c) {x β : Fin n → ℝ} {α : Fin (n + 1) → ℝ}
    (hα : IsRegMultiplier w m γ (Fin.cons 1 x) α)
    (hβ : IsMinOn (fun b => reducedObj w m c γ b x) Set.univ β) :
    -regDualObj w m γ α (Fin.cons 1 x) = -reducedObj w m c γ β x := by
  obtain ⟨hmin, heq⟩ := hα.isMinOn_reducedObj hw hc hm0
  have h1 : reducedObj w m c γ (Fin.tail α) x ≤ reducedObj w m c γ β x := hmin (Set.mem_univ β)
  have h2 : reducedObj w m c γ β x ≤ reducedObj w m c γ (Fin.tail α) x := hβ (Set.mem_univ _)
  rw [heq, le_antisymm h1 h2]

/-- **Theorem 3** (arXiv 2404.14312), Eq. (49): `h^γ(u) = u₀ ĥ^γ(ū_#) + u₀ log u₀ / m₀`, for any
regularized multiplier `α'` of `u` and any minimizer `β` of the reduced problem at `ū_#`. -/
theorem regEntropy_scaling [Nonempty V] (hw : ∀ v, 0 < w v) (hc : 0 < c) (hm0 : ∀ v, m v 0 = c)
    {u α' : Fin (n + 1) → ℝ} (hu : 0 < u 0) (hα' : IsRegMultiplier w m γ u α') {β : Fin n → ℝ}
    (hβ : IsMinOn (fun b => reducedObj w m c γ b (Fin.tail ((u 0)⁻¹ • u))) Set.univ β) :
    -regDualObj w m γ α' u =
      u 0 * -reducedObj w m c γ β (Fin.tail ((u 0)⁻¹ • u)) + u 0 * Real.log (u 0) / c := by
  set x := Fin.tail ((u 0)⁻¹ • u)
  obtain ⟨hmul, hval⟩ := isRegMultiplier_cons_of_isMinOn (γ := γ) hw hc hm0 hβ
  set α := (Fin.cons (zerothMultiplier w c (reducedBasis m) β) β : Fin (n + 1) → ℝ)
  have hū : (u 0)⁻¹ • u = Fin.cons 1 x := smul_inv_eq_cons hu
  have hmul' : IsRegMultiplier w m γ ((u 0)⁻¹ • u) α := by rw [hū]; exact hmul
  have hshift := (isRegMultiplier_add_single_iff hc.ne' hm0 hu α).1 hmul'
  rw [le_antisymm (hα' _) (hshift α'), regDualObj_add_single hc.ne' hm0 hu, hū, hval]
  ring

end Theorem3

/-! ### Theorem 4: moment reconstruction errors -/

section Theorem4

variable {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} {γ : ℝ}

/-- The derivative of the regularized objective along a coordinate direction. -/
lemma hasDerivAt_regDualObj_line (α u : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    HasDerivAt (fun s : ℝ => regDualObj w m γ (α + s • Pi.single i 1) u)
      (moments w m (ansatz m α) i - u i +
        u 0 * γ * (Fin.cons 0 (Fin.tail α) : Fin (n + 1) → ℝ) i) (0 : ℝ) := by
  have h1 := hasDerivAt_dualObj_line w m α u i 0
  simp only [zero_smul, add_zero] at h1
  set a := Fin.tail α
  set b := Fin.tail (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)
  have hfun : (fun s : ℝ => regDualObj w m γ (α + s • Pi.single i 1) u) = fun s =>
      dualObj w m (α + s • Pi.single i 1) u +
        u 0 * γ / 2 * (a ⬝ᵥ a + s * (2 * (a ⬝ᵥ b)) + s * s * (b ⬝ᵥ b)) := by
    funext s
    have ht : Fin.tail (α + s • Pi.single i 1) = a + s • b := rfl
    rw [regDualObj, ht]
    congr 1
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm b a]
    ring
  have hq : HasDerivAt (fun s : ℝ => a ⬝ᵥ a + s * (2 * (a ⬝ᵥ b)) + s * s * (b ⬝ᵥ b))
      (2 * (a ⬝ᵥ b)) 0 := by
    have h0 := ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (2 * (a ⬝ᵥ b))).const_add (a ⬝ᵥ a)
    have h2 := ((hasDerivAt_id' (x := (0 : ℝ))).fun_mul (hasDerivAt_id' (x := (0 : ℝ)))).mul_const
      (b ⬝ᵥ b)
    convert h0.fun_add h2 using 1
    simp
  have hab : a ⬝ᵥ b = (Fin.cons 0 a : Fin (n + 1) → ℝ) i := by
    have := cons_dotProduct (0 : ℝ) a (Pi.single i 1)
    rw [dotProduct_single, mul_one] at this
    rw [this]; simp [b]
  rw [hfun]
  convert h1.fun_add (hq.const_mul (u 0 * γ / 2)) using 1
  rw [hab]; ring

/-- **The regularized moment condition** (Eqs. (93), (97), (99)): a regularized multiplier
satisfies `⟨m exp(α · m)⟩ = u - u₀ γ [0, α_#]`. -/
theorem moments_ansatz_of_isRegMultiplier {u α : Fin (n + 1) → ℝ}
    (hα : IsRegMultiplier w m γ u α) :
    moments w m (ansatz m α) = u - (u 0 * γ) • (Fin.cons 0 (Fin.tail α) : Fin (n + 1) → ℝ) := by
  funext i
  have hmin : IsLocalMin (fun s : ℝ => regDualObj w m γ (α + s • Pi.single i 1) u) 0 :=
    Filter.Eventually.of_forall fun s => by simpa using hα (α + s • Pi.single i 1)
  have := hmin.hasDerivAt_eq_zero (hasDerivAt_regDualObj_line α u i)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- The Euclidean norm of `[0, β]` is that of `β`. -/
lemma norm_toLp_cons_zero (β : Fin n → ℝ) :
    ‖(WithLp.toLp 2 (Fin.cons 0 β : Fin (n + 1) → ℝ) : EuclideanSpace ℝ (Fin (n + 1)))‖ =
      ‖(WithLp.toLp 2 β : EuclideanSpace ℝ (Fin n))‖ := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]

/-- **Theorem 4**, Eqs. (51)–(52): `ũ^γ = ⟨m f̃^γ_u⟩ = u - u₀ γ [0, β]` with `β = (α^γ_u)_#`, so
`‖ũ^γ - u‖ = u₀ γ ‖β‖ ≤ u₀ γ M` when `‖β‖ ≤ M`. -/
theorem norm_regMoments_sub {u α : Fin (n + 1) → ℝ} (hu : 0 ≤ u 0) (hγ : 0 ≤ γ)
    (hα : IsRegMultiplier w m γ u α) :
    ‖(WithLp.toLp 2 (moments w m (ansatz m α) - u) : EuclideanSpace ℝ (Fin (n + 1)))‖ =
      u 0 * γ * ‖(WithLp.toLp 2 (Fin.tail α) : EuclideanSpace ℝ (Fin n))‖ := by
  rw [moments_ansatz_of_isRegMultiplier hα, sub_sub_cancel_left, WithLp.toLp_neg, norm_neg,
    WithLp.toLp_smul, norm_smul, norm_toLp_cons_zero, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hu hγ)]

omit [Fintype V] in
/-- **The gradient ansatz** (Eqs. (37)–(38) with the factor `m₀ ≡ c`, as in the proof (106)):
`f^γ_u = exp(g^γ_u · m) = exp(-γ c ‖α_#‖² / 2) f̃^γ_u`. -/
theorem ansatz_entropyGrad {c : ℝ} (hm0 : ∀ v, m v 0 = c) (α : Fin (n + 1) → ℝ) :
    ansatz m (entropyGrad γ α) =
      Real.exp (-(γ * c * (Fin.tail α ⬝ᵥ Fin.tail α) / 2)) • ansatz m α := by
  funext v
  simp only [ansatz, entropyGrad, sub_dotProduct, single_dotProduct, hm0, Pi.smul_apply,
    smul_eq_mul, ← Real.exp_add]
  ring_nf

omit [Fintype V] in
/-- **Eq. (38) as printed** (`f^γ_u = exp(-γ/2 ‖(α^γ_u)_#‖²) f̃^γ_u`, without `m₀`) holds iff
`m₀ = 1` or `α_# = 0` (for `γ > 0` and a nonempty quadrature). -/
theorem ansatz_entropyGrad_eq_printed_iff [Nonempty V] {c : ℝ} (hm0 : ∀ v, m v 0 = c)
    (hγ : 0 < γ) (α : Fin (n + 1) → ℝ) :
    ansatz m (entropyGrad γ α) =
        Real.exp (-(γ * (Fin.tail α ⬝ᵥ Fin.tail α) / 2)) • ansatz m α ↔
      c = 1 ∨ Fin.tail α = 0 := by
  rw [ansatz_entropyGrad hm0]
  obtain ⟨v⟩ := ‹Nonempty V›
  constructor
  · intro h
    have hv := congrFun h v
    simp only [Pi.smul_apply, smul_eq_mul, ansatz] at hv
    have h1 := mul_right_cancel₀ (Real.exp_pos (α ⬝ᵥ m v)).ne' hv
    have h2 := Real.exp_injective h1
    have : γ * (Fin.tail α ⬝ᵥ Fin.tail α) * (c - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact Or.inr (dotProduct_self_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hγ.ne'))
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · rw [h, mul_one]
    · simp [h]

/-- **Theorem 4**, Eq. (106): `u^γ = ⟨m f^γ_u⟩ = exp(-γ c ‖α_#‖² / 2) ũ^γ`. -/
theorem moments_ansatz_entropyGrad {c : ℝ} (hm0 : ∀ v, m v 0 = c) (α : Fin (n + 1) → ℝ) :
    moments w m (ansatz m (entropyGrad γ α)) =
      Real.exp (-(γ * c * (Fin.tail α ⬝ᵥ Fin.tail α) / 2)) • moments w m (ansatz m α) := by
  rw [ansatz_entropyGrad hm0]
  funext i
  simp only [moments, avg, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun v _ => by ring

/-- **Theorem 4**, Eq. (107): `‖u^γ - ũ^γ‖ = (1 - exp(-γ c ‖β‖² / 2)) ‖ũ^γ‖`. -/
theorem norm_moments_entropyGrad_sub {c : ℝ} (hm0 : ∀ v, m v 0 = c) (hγc : 0 ≤ γ * c)
    (α : Fin (n + 1) → ℝ) :
    ‖(WithLp.toLp 2 (moments w m (ansatz m (entropyGrad γ α)) - moments w m (ansatz m α)) :
        EuclideanSpace ℝ (Fin (n + 1)))‖ =
      (1 - Real.exp (-(γ * c * (Fin.tail α ⬝ᵥ Fin.tail α) / 2))) *
        ‖(WithLp.toLp 2 (moments w m (ansatz m α)) : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
  set e := Real.exp (-(γ * c * (Fin.tail α ⬝ᵥ Fin.tail α) / 2))
  have he : e ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact div_nonneg (mul_nonneg hγc (Finset.sum_nonneg fun i _ => mul_self_nonneg _)) two_pos.le
  rw [moments_ansatz_entropyGrad hm0, show ∀ z : Fin (n + 1) → ℝ, e • z - z = -((1 - e) • z) by
    intro z; module, WithLp.toLp_neg, norm_neg, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.2 he)]

/-- **Theorem 4**, Eq. (53) with the factor `m₀ ≡ c` of the proof (107): if `‖(α^γ_u)_#‖ ≤ M`, then
`‖u^γ - u‖ ≤ u₀ γ M + (1 - exp(-γ c M² / 2)) ‖ũ^γ‖`. -/
theorem norm_moments_entropyGrad_sub_le {c : ℝ} (hm0 : ∀ v, m v 0 = c) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    {u α : Fin (n + 1) → ℝ} (hu : 0 ≤ u 0) (hα : IsRegMultiplier w m γ u α) {M : ℝ}
    (hM : ‖(WithLp.toLp 2 (Fin.tail α) : EuclideanSpace ℝ (Fin n))‖ ≤ M) :
    ‖(WithLp.toLp 2 (moments w m (ansatz m (entropyGrad γ α)) - u) :
        EuclideanSpace ℝ (Fin (n + 1)))‖ ≤
      u 0 * γ * M + (1 - Real.exp (-(γ * c * M ^ 2 / 2))) *
        ‖(WithLp.toLp 2 (moments w m (ansatz m α)) : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
  set ũ := moments w m (ansatz m α)
  have hsplit : moments w m (ansatz m (entropyGrad γ α)) - u =
      (moments w m (ansatz m (entropyGrad γ α)) - ũ) + (ũ - u) := by abel
  have hq : Fin.tail α ⬝ᵥ Fin.tail α ≤ M ^ 2 := by
    have h0 : ‖(WithLp.toLp 2 (Fin.tail α) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
        Fin.tail α ⬝ᵥ Fin.tail α := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [dotProduct, sq]
    rw [← h0]
    exact pow_le_pow_left₀ (norm_nonneg _) hM 2
  have hexp : Real.exp (-(γ * c * M ^ 2 / 2)) ≤
      Real.exp (-(γ * c * (Fin.tail α ⬝ᵥ Fin.tail α) / 2)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (mul_nonneg hγ hc))
      two_pos.le
  rw [hsplit, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  rw [norm_moments_entropyGrad_sub hm0 (mul_nonneg hγ hc), norm_regMoments_sub hu hγ hα]
  have h1 : u 0 * γ * ‖(WithLp.toLp 2 (Fin.tail α) : EuclideanSpace ℝ (Fin n))‖ ≤ u 0 * γ * M :=
    mul_le_mul_of_nonneg_left hM (mul_nonneg hu hγ)
  have h2 := mul_le_mul_of_nonneg_right (sub_le_sub_left hexp 1)
    (norm_nonneg (WithLp.toLp 2 ũ : EuclideanSpace ℝ (Fin (n + 1))))
  linarith

/-- **Theorem 4**, Eq. (53) as printed (`exp(-γ M² / 2)`), valid when `m₀ ≡ c ≤ 1` (normalized
spherical harmonics: `c = (4π)^{-1/2}`). -/
theorem norm_moments_entropyGrad_sub_le_of_le_one {c : ℝ} (hm0 : ∀ v, m v 0 = c) (hγ : 0 ≤ γ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) {u α : Fin (n + 1) → ℝ} (hu : 0 ≤ u 0)
    (hα : IsRegMultiplier w m γ u α) {M : ℝ}
    (hM : ‖(WithLp.toLp 2 (Fin.tail α) : EuclideanSpace ℝ (Fin n))‖ ≤ M) :
    ‖(WithLp.toLp 2 (moments w m (ansatz m (entropyGrad γ α)) - u) :
        EuclideanSpace ℝ (Fin (n + 1)))‖ ≤
      u 0 * γ * M + (1 - Real.exp (-(γ / 2 * M ^ 2))) *
        ‖(WithLp.toLp 2 (moments w m (ansatz m α)) : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
  refine (norm_moments_entropyGrad_sub_le hm0 hγ hc hu hα hM).trans ?_
  have : Real.exp (-(γ / 2 * M ^ 2)) ≤ Real.exp (-(γ * c * M ^ 2 / 2)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have : γ * c * M ^ 2 ≤ γ * M ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hγ hc1) (sq_nonneg M)
    linarith
  have := mul_le_mul_of_nonneg_right (sub_le_sub_left this 1)
    (norm_nonneg (WithLp.toLp 2 (moments w m (ansatz m α)) : EuclideanSpace ℝ (Fin (n + 1))))
  linarith

/-- The moment reconstruction map `ψ^γ(β) = ⟨m_# exp((ϑ(β), β) · m)⟩ + γ β` (Eq. (62)). -/
noncomputable def psi (w : V → ℝ) (m : V → Fin (n + 1) → ℝ) (c γ : ℝ) (β : Fin n → ℝ) :
    Fin n → ℝ :=
  Fin.tail (moments w m (ansatz m (Fin.cons (zerothMultiplier w c (reducedBasis m) β) β))) +
    γ • β

/-- **Eq. (67)**: `‖ψ(β) - ψ^γ(β)‖ = γ ‖β‖ ≤ γ M` for `‖β‖ ≤ M`, `γ ≥ 0`. -/
theorem norm_psi_sub {c : ℝ} (hγ : 0 ≤ γ) (β : Fin n → ℝ) {M : ℝ}
    (hM : ‖(WithLp.toLp 2 β : EuclideanSpace ℝ (Fin n))‖ ≤ M) :
    ‖(WithLp.toLp 2 (psi w m c 0 β - psi w m c γ β) : EuclideanSpace ℝ (Fin n))‖ ≤ γ * M := by
  have : psi w m c 0 β - psi w m c γ β = -(γ • β) := by simp [psi]
  rw [this, WithLp.toLp_neg, norm_neg, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hγ]
  exact mul_le_mul_of_nonneg_left hM hγ

end Theorem4

/-! ### Theorem 5: entropy dissipation -/

/-- **Theorem 5**, entropy dissipation (Eq. (113)): for the ansatz `f = exp(g · m)`,
`g · ⟨m Q⟩ = ⟨η'(f) Q⟩` with `η'(f) = log f`; hence `∇h^γ · ⟨m Q(f^γ_u)⟩ ≤ 0` whenever the
collision term dissipates the kinetic entropy, `⟨η'(f) Q(f)⟩ ≤ 0` (Eq. (6), hypothesis). -/
theorem entropyGrad_dot_moments_le {w : V → ℝ} {m : V → Fin (n + 1) → ℝ} (g : Fin (n + 1) → ℝ)
    (Q : V → ℝ) (hdiss : avg w (fun v => Real.log (ansatz m g v) * Q v) ≤ 0) :
    g ⬝ᵥ moments w m Q = avg w (fun v => Real.log (ansatz m g v) * Q v) ∧
      g ⬝ᵥ moments w m Q ≤ 0 := by
  have h : g ⬝ᵥ moments w m Q = avg w (fun v => Real.log (ansatz m g v) * Q v) := by
    simp only [dotProduct, moments, avg, ansatz, Real.log_exp, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_mul, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  exact ⟨h, h ▸ hdiss⟩

/-- Non-vacuity: with one velocity (`m = (1, 0)`, `n = 1`), `β = x / γ` minimizes the reduced
objective, so Lemma 3 and Theorem 3 apply. -/
example (γ : ℝ) (hγ : 0 < γ) (x : Fin 1 → ℝ) :
    IsMinOn (fun b => reducedObj (V := Unit) (fun _ => 1) (fun _ => Fin.cons 1 0) 1 γ b x)
      Set.univ (γ⁻¹ • x) := by
  have key : ∀ b : Fin 1 → ℝ,
      reducedObj (V := Unit) (fun _ => 1) (fun _ => Fin.cons 1 0) 1 γ b x =
        1 - b 0 * x 0 + γ / 2 * (b 0 * b 0) := by
    intro b
    rw [reducedObj_eq (fun _ => one_pos) one_pos (fun _ => rfl)]
    simp [partFun, avg, reducedBasis, dotProduct]
  intro b _
  change reducedObj (V := Unit) (fun _ => 1) (fun _ => Fin.cons 1 0) 1 γ (γ⁻¹ • x) x ≤
    reducedObj (V := Unit) (fun _ => 1) (fun _ => Fin.cons 1 0) 1 γ b x
  rw [key, key]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h : 0 ≤ (γ * b 0 - x 0) ^ 2 / (2 * γ) := by positivity
  have e : 1 - b 0 * x 0 + γ / 2 * (b 0 * b 0) -
      (1 - γ⁻¹ * x 0 * x 0 + γ / 2 * (γ⁻¹ * x 0 * (γ⁻¹ * x 0))) =
        (γ * b 0 - x 0) ^ 2 / (2 * γ) := by
    field_simp
    ring
  linarith

end LeanDLRA.Literature.P2404_14312
