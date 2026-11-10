import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Training.Descent
import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Literature.Training.P2209_13569a

/-!
# Results of arXiv 2306.00897: Gauss-Southwell descent for low-rank matrix optimization

Olikier, Uschmajew and Vandereycken, *Gauss-Southwell type descent methods for low-rank matrix
optimization*.  For a `λ`-smooth `f : ℝ^{m×n} → ℝ` (`IsSmooth`) this module formalizes the three
algorithms of the paper on actual matrices and proves its theorems: the step-size rules of Section 2
(`StepRule`, `StepRule.decrease`, `StepRule.exists_armijo`); Algorithm 1, balanced block descent
(`BalancedStep`, `IsBalanced`), with Theorem 3.1 (`balancedBlockDescent_decrease`) and Corollary 3.2
(`balancedBlockDescent_convergence`); Algorithm 2, Riemannian block descent (`RiemStep`,
`IsRiemRun`, `riemGrad`), with Theorem 3.4 (`riemBlockDescent_decrease`) and Corollary 3.5
(`riemBlockDescent_convergence`), lower semicontinuity of `‖grad f‖`
(`lowerSemicontinuous_norm_riemGrad`) and `‖grad f(X)‖ ≤ ‖P_{U,V} ∇f(X)‖` also at rank-deficient
iterates (`norm_riemGrad_le_tangentProj`); the comparison (3.16), (3.17)
(`IsBalanced.le_gradNorm_sq`, `IsBalanced.gradNorm_sq_le`); Lemma 3.6 for `M_k`
(`riemannian_pl`, `isolated_local_min`), Theorem 3.7 (`riemBlockDescent_linear_rate`) and
Theorem 3.8 (`riemBlockDescent_refined_rate`, `riemBlockDescent_refined_rate_exact`); and
Algorithm 3, ALS (`IsALSRun`), with Corollary 3.9 (`als_convergence`) and Theorem 3.10
(`als_linear_rate`).  Well-posedness: `exists_riemRun`, `exists_balancedRun`, `exists_isBalanced`,
`IsBalanced.of_qr_svd`; the hypotheses of the local theorems hold in `quadratic_instance`.

**False claims of the paper.**  Estimate (3.29) fails at `ℓ = 0`, and with it the two separate
estimates after Corollary 3.9 at `ℓ = 0` and the min-max estimate stated there at `j = 0`: the first
half-step of ALS only sees the block `T_{V₀}`, while the vanishing of the other block is only
available for `ℓ ≥ 1`, as the paper says itself (`als_counterexample`, for a convex quadratic).
Corollary 3.9 is correct: `als_convergence` uses the half-steps after the first one.  Two slips of
wording: line 7 of Algorithm 2 needs the transposed core (`RiemStep`), and "same singular values"
does not define balanced factorizations (`IsBalanced`).

**Differences from the paper.**  `λ > 0` and `ρ > 0` are assumed, since the step sizes divide by
them.  The Riemannian gradient is the projection onto `tangentSpaceAt X = {A X + X B}`, which is the
tangent space of `M_{rank X}`, and equals the range of `P_{U,V}` for `X = U S Vᵀ` with invertible
`S` (`tangentSpaceAt_eq_of_isUnit`).  QR factors are any factorizations with orthonormal columns.
`ϑ` in the corollaries is any positive lower bound of the `ϑ_ℓ`, which covers the infimum of the
paper (`theta_iInf_pos`).  Mathlib has no embedded Riemannian manifolds, so the Riemannian Hessian
of `f|M_k` is given by its formula (`riemHess`), which `taylor_on_rank_le` shows to be the
second-order term of `f` along `M_{≤k}` at a critical point, and Lemma 3.6 is proved for `M_k` only,
the one case the paper uses; our proof uses no charts, but the identity `eq_mul_inv_mul`.
Theorem 3.7 needs only differentiability of `∇f` at `X∗`, Theorems 3.8 and 3.10 need `∇f`
differentiable near `X∗` with continuous derivative at `X∗`.  **In Theorems 3.7 and 3.8 we assume
bounded step sizes** `h_ℓ ≤ hmax`.  This holds for fixed steps and backtracking
(`StepRule.step_le`); for exact line search the paper infers it from the boundedness of `N₀`, which
only bounds `h_ℓ ‖P_{1/2}‖` while `‖P_{1/2}‖ → 0`, so we could not follow that step and neither
prove nor refute it.

**Not formalized.**  The numerical experiments of Section 4, the angle and scaling conditions at the
start of Section 3.4, and the identification (3.12) with scaled gradient descent, which the theorems
do not use.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2306_00897

/-! ### Step-size rules (Section 2 of the paper) -/

/-- The Armijo condition (2.5) for the line function `φ t = ϕ(x - t ∇ϕ(x))`, where `d = ‖∇ϕ(x)‖²`:
`ϕ(x) - ϕ(x - t ∇ϕ(x)) ≥ γ t ‖∇ϕ(x)‖²`. -/
def Armijo (φ : ℝ → ℝ) (d γ t : ℝ) : Prop := γ * t * d ≤ φ 0 - φ t

/-- The three step-size rules of Theorems 3.1 and 3.4. -/
inductive StepRule
  /-- Fixed step `h = 2 α / Λ`, `α ∈ (0, 1)`. -/
  | fixed (α : ℝ)
  /-- Exact line search. -/
  | exact
  /-- Backtracking `h = h̄, h̄ β, h̄ β², …` until the Armijo condition with parameter `γ` holds. -/
  | armijo (hbar β γ : ℝ)

namespace StepRule

/-- `Admissible r Λ d φ h`: the step size `h` is produced by the rule `r`, for smoothness constant
`Λ`, squared slope `d = ‖∇ϕ(x)‖²` and line function `φ t = ϕ(x - t ∇ϕ(x))`.  Exact line search
minimizes `φ` over `t > 0`; backtracking stops at the *first* index `i` for which the Armijo
condition holds. -/
def Admissible : StepRule → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop
  | fixed α, Λ, _, _, h => 0 < α ∧ α < 1 ∧ h = 2 * α / Λ
  | exact, _, _, φ, h => 0 < h ∧ ∀ t, 0 < t → φ h ≤ φ t
  | armijo hbar β γ, _, d, φ, h =>
      0 < hbar ∧ 0 < β ∧ β < 1 ∧ 0 < γ ∧ γ < 1 ∧
        ∃ i : ℕ, h = hbar * β ^ i ∧ Armijo φ d γ (hbar * β ^ i) ∧
          ∀ j < i, ¬ Armijo φ d γ (hbar * β ^ j)

/-- The constant `ϑ` of Theorems 3.1 and 3.4 for smoothness constant `Λ`. -/
noncomputable def theta : StepRule → ℝ → ℝ
  | fixed α, _ => 2 * α * (1 - α)
  | exact, _ => 1 / 2
  | armijo hbar β γ, Λ => min (2 * β * γ * (1 - γ)) (Λ * γ * hbar)

/-- The largest trial step used in the analysis of a rule. -/
noncomputable def reach : StepRule → ℝ → ℝ
  | fixed α, Λ => 2 * α / Λ
  | exact, Λ => 1 / Λ
  | armijo hbar _ _, _ => hbar

/-- `ϑ_ℓ ≤ 1/2` in all cases (the note after Corollaries 3.2 and 3.5).  (arXiv 2306.00897.) -/
theorem theta_le_half {r : StepRule} {Λ d h : ℝ} {φ : ℝ → ℝ} (hr : r.Admissible Λ d φ h) :
    r.theta Λ ≤ 1 / 2 := by
  cases r with
  | fixed α => simp only [theta]; nlinarith [sq_nonneg (2 * α - 1)]
  | exact => simp [theta]
  | armijo hbar β γ =>
    obtain ⟨-, hβ, hβ1, hγ, hγ1, -⟩ := hr
    refine (min_le_left _ _).trans ?_
    have h1 : γ * (1 - γ) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * γ - 1)]
    have h2 : 0 < γ * (1 - γ) := mul_pos hγ (sub_pos.2 hγ1)
    nlinarith

/-- `0 < ϑ_ℓ` in all cases (the note after Corollaries 3.2 and 3.5).  (arXiv 2306.00897.) -/
theorem theta_pos {r : StepRule} {Λ d h : ℝ} {φ : ℝ → ℝ} (hΛ : 0 < Λ)
    (hr : r.Admissible Λ d φ h) : 0 < r.theta Λ := by
  cases r with
  | fixed α =>
    obtain ⟨h0, h1, -⟩ := hr
    simp only [theta]; have := sub_pos.2 h1; positivity
  | exact => simp [theta]
  | armijo hbar β γ =>
    obtain ⟨hb, hβ, -, hγ, hγ1, -⟩ := hr
    have := sub_pos.2 hγ1
    simp only [theta]
    exact lt_min (by positivity) (by positivity)

/-- **One step of the gradient method** (Section 2 of the paper, (2.3)-(2.6)): if the line function
satisfies the descent estimate `φ t ≤ φ 0 - t d + Λ / 2 t² d` on `[0, r.reach Λ]`, then a step
admissible for `r` decreases `φ` by at least `ϑ / Λ · d`.  (arXiv 2306.00897.) -/
theorem decrease {r : StepRule} {Λ d h : ℝ} {φ : ℝ → ℝ} (hΛ : 0 < Λ) (hd : 0 ≤ d)
    (hφ : ∀ t, 0 ≤ t → t ≤ r.reach Λ → φ t ≤ φ 0 - t * d + Λ / 2 * t ^ 2 * d)
    (hr : r.Admissible Λ d φ h) : r.theta Λ / Λ * d ≤ φ 0 - φ h := by
  cases r with
  | fixed α =>
    obtain ⟨h0, h1, rfl⟩ := hr
    have hh := hφ (2 * α / Λ) (by positivity) le_rfl
    simp only [theta]
    have e : 2 * (α : ℝ) * (1 - α) / Λ * d = 2 * α / Λ * d - Λ / 2 * (2 * α / Λ) ^ 2 * d := by
      field_simp
    rw [e]; linarith
  | exact =>
    obtain ⟨h0, hmin⟩ := hr
    have hh := hφ (1 / Λ) (by positivity) le_rfl
    have hm := hmin (1 / Λ) (by positivity)
    simp only [theta]
    have e : (1 / 2 : ℝ) / Λ * d = 1 / Λ * d - Λ / 2 * (1 / Λ) ^ 2 * d := by
      field_simp
      ring
    rw [e]; linarith
  | armijo hbar β γ =>
    obtain ⟨hb, hβ, hβ1, hγ, hγ1, i, rfl, hA, hmin⟩ := hr
    simp only [Armijo] at hA
    have hθ1 : min (2 * β * γ * (1 - γ)) (Λ * γ * hbar) ≤ 2 * β * γ * (1 - γ) := min_le_left _ _
    have hθ2 : min (2 * β * γ * (1 - γ)) (Λ * γ * hbar) ≤ Λ * γ * hbar := min_le_right _ _
    simp only [theta]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, mul_one] at hA
      calc min (2 * β * γ * (1 - γ)) (Λ * γ * hbar) / Λ * d
          ≤ (Λ * γ * hbar) / Λ * d := by gcongr
        _ = γ * hbar * d := by field_simp
        _ ≤ _ := by simpa using hA
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj := hmin j (Nat.lt_succ_self j)
      simp only [Armijo, not_le] at hj
      set t := hbar * β ^ j with ht
      have ht0 : 0 < t := by positivity
      have htle : t ≤ hbar := by
        have : β ^ j ≤ 1 := pow_le_one₀ hβ.le hβ1.le
        rw [ht]; nlinarith
      have hh := hφ t ht0.le htle
      have hstep : hbar * β ^ (j + 1) = β * t := by rw [ht, pow_succ]; ring
      rw [hstep] at hA ⊢
      have hd' : 0 < d := by
        rcases hd.eq_or_lt with h0 | h0
        · exfalso; rw [← h0] at hj hh; nlinarith
        · exact h0
      have ht2 : 2 * (1 - γ) / Λ ≤ t := by
        rw [div_le_iff₀ hΛ]
        have : t * d * (1 - γ) < t * d * (Λ / 2 * t) := by nlinarith
        have h3 := lt_of_mul_lt_mul_left this (by positivity)
        nlinarith
      calc min (2 * β * γ * (1 - γ)) (Λ * γ * hbar) / Λ * d
          ≤ (2 * β * γ * (1 - γ)) / Λ * d := by gcongr
        _ = γ * β * (2 * (1 - γ) / Λ) * d := by ring
        _ ≤ γ * β * t * d := by gcongr
        _ = γ * (β * t) * d := by ring
        _ ≤ _ := hA

/-- The Armijo condition holds once `h ≤ 2 (1 - γ) / Λ` (2.6).  (arXiv 2306.00897.) -/
theorem armijo_of_le {Λ d γ t : ℝ} {φ : ℝ → ℝ} (hΛ : 0 < Λ) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hφ : φ t ≤ φ 0 - t * d + Λ / 2 * t ^ 2 * d) (hle : t ≤ 2 * (1 - γ) / Λ) :
    Armijo φ d γ t := by
  rw [Armijo]
  have h1 : Λ * t ≤ 2 * (1 - γ) := by rwa [le_div_iff₀' hΛ] at hle
  have h2 : 0 ≤ t * d := mul_nonneg ht hd
  nlinarith

/-- **Termination of backtracking** (Theorems 3.1 and 3.4): the first index `i` satisfying the
Armijo condition exists and `i ≤ max {0, ⌈ln (2 / (h̄ Λ) (1 - γ)) / ln β⌉}`.  (arXiv 2306.00897.) -/
theorem exists_armijo {Λ d hbar β γ : ℝ} {φ : ℝ → ℝ} (hΛ : 0 < Λ) (hd : 0 ≤ d) (hb : 0 < hbar)
    (hβ : 0 < β) (hβ1 : β < 1) (hγ1 : γ < 1)
    (hφ : ∀ t, 0 ≤ t → t ≤ hbar → φ t ≤ φ 0 - t * d + Λ / 2 * t ^ 2 * d) :
    ∃ i : ℕ, Armijo φ d γ (hbar * β ^ i) ∧ (∀ j < i, ¬ Armijo φ d γ (hbar * β ^ j)) ∧
      (i : ℤ) ≤ max 0 ⌈Real.log (2 / (hbar * Λ) * (1 - γ)) / Real.log β⌉ := by
  classical
  set c := 2 / (hbar * Λ) * (1 - γ) with hc
  have hc0 : 0 < c := by have := sub_pos.2 hγ1; positivity
  set I : ℤ := max 0 ⌈Real.log c / Real.log β⌉ with hI
  have hI0 : 0 ≤ I := le_max_left _ _
  have hlogβ : Real.log β < 0 := Real.log_neg hβ hβ1
  have hpow : β ^ I.toNat ≤ c := by
    have h1 : Real.log c / Real.log β ≤ (I.toNat : ℝ) := by
      have : (⌈Real.log c / Real.log β⌉ : ℝ) ≤ (I : ℝ) := by
        exact_mod_cast le_max_right _ _
      have h2 : ((I.toNat : ℕ) : ℝ) = (I : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hI0
      calc Real.log c / Real.log β ≤ ⌈Real.log c / Real.log β⌉ := Int.le_ceil _
        _ ≤ (I : ℝ) := this
        _ = _ := h2.symm
    have h2 : (I.toNat : ℝ) * Real.log β ≤ Real.log c := by
      rwa [div_le_iff_of_neg hlogβ] at h1
    rw [← Real.log_le_log_iff (by positivity) hc0, Real.log_pow]
    exact h2
  have hA : ∃ i : ℕ, Armijo φ d γ (hbar * β ^ i) ∧ i ≤ I.toNat := by
    refine ⟨I.toNat, armijo_of_le hΛ hd (by positivity) (hφ _ (by positivity) ?_) ?_, le_rfl⟩
    · have : β ^ I.toNat ≤ 1 := pow_le_one₀ hβ.le hβ1.le
      nlinarith
    · have e : 2 * (1 - γ) / Λ = hbar * c := by rw [hc]; field_simp
      rw [e]; gcongr
  have hex : ∃ i : ℕ, Armijo φ d γ (hbar * β ^ i) := ⟨_, hA.choose_spec.1⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj, ?_⟩
  have h1 : Nat.find hex ≤ I.toNat := Nat.find_min' hex (Classical.choose_spec hA).1 |>.trans
    (Classical.choose_spec hA).2
  have h2 : ((I.toNat : ℕ) : ℤ) = I := Int.toNat_of_nonneg hI0
  rw [← h2]; exact_mod_cast h1

/-- The index found by backtracking obeys the bound of Theorems 3.1 and 3.4.  (arXiv 2306.00897.) -/
theorem armijo_index_le {Λ d hbar β γ : ℝ} {φ : ℝ → ℝ} {h : ℝ} (hΛ : 0 < Λ) (hd : 0 ≤ d)
    (hφ : ∀ t, 0 ≤ t → t ≤ hbar → φ t ≤ φ 0 - t * d + Λ / 2 * t ^ 2 * d)
    (hr : (armijo hbar β γ).Admissible Λ d φ h) :
    ∃ i : ℕ, h = hbar * β ^ i ∧
      (i : ℤ) ≤ max 0 ⌈Real.log (2 / (hbar * Λ) * (1 - γ)) / Real.log β⌉ := by
  obtain ⟨hb, hβ, hβ1, -, hγ1, i, rfl, hA, hmin⟩ := hr
  obtain ⟨i', hA', hmin', hle⟩ := exists_armijo hΛ hd hb hβ hβ1 hγ1 hφ
  refine ⟨i, rfl, ?_⟩
  have : i ≤ i' := by
    by_contra hlt
    exact hmin i' (by omega) hA'
  have h2 : (i : ℤ) ≤ i' := by exact_mod_cast this
  exact h2.trans hle

/-- Step sizes are nonnegative.  (arXiv 2306.00897.) -/
theorem step_nonneg {r : StepRule} {Λ d h : ℝ} {φ : ℝ → ℝ} (hΛ : 0 < Λ)
    (hr : r.Admissible Λ d φ h) : 0 < h := by
  cases r with
  | fixed α => obtain ⟨h0, -, rfl⟩ := hr; positivity
  | exact => exact hr.1
  | armijo hbar β γ => obtain ⟨hb, hβ, -, -, -, i, rfl, -⟩ := hr; positivity

end StepRule


/-! ### Sublinear rates from sufficient decrease -/

/-- The telescoping argument common to Corollaries 3.2, 3.5 and 3.9.  (arXiv 2306.00897.) -/
theorem rate_core {F a : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (ha : ∀ ℓ, 0 ≤ a ℓ)
    (hdec : ∀ ℓ, c * a ℓ ≤ F ℓ - F (ℓ + 1)) (hbdd : BddBelow (range F)) :
    Antitone F ∧ ∃ Fstar, Tendsto F atTop (𝓝 Fstar) ∧ (∀ ℓ, Fstar ≤ F ℓ) ∧
      Tendsto a atTop (𝓝 0) ∧ ∀ j : ℕ, ∃ ℓ ≤ j, c * a ℓ ≤ (F 0 - Fstar) / (j + 1) := by
  have hanti : Antitone F := antitone_nat_of_succ_le fun ℓ => by
    have := hdec ℓ
    have := mul_nonneg hc.le (ha ℓ)
    linarith
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hle : ∀ ℓ, ⨅ i, F i ≤ F ℓ := fun ℓ => ciInf_le hbdd ℓ
  refine ⟨hanti, ⨅ i, F i, hlim, hle, ?_, fun j => ?_⟩
  · have hdiff : Tendsto (fun ℓ => (F ℓ - F (ℓ + 1)) / c) atTop (𝓝 0) := by
      have := (hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))).div_const c
      simpa [Function.comp_def] using this
    refine squeeze_zero ha (fun ℓ => ?_) hdiff
    rw [le_div_iff₀' hc]
    exact hdec ℓ
  · by_contra hcon
    push Not at hcon
    have hsum : ∑ ℓ ∈ range (j + 1), c * a ℓ ≤ F 0 - ⨅ i, F i := by
      have h1 : ∑ ℓ ∈ range (j + 1), c * a ℓ ≤ ∑ ℓ ∈ range (j + 1), (F ℓ - F (ℓ + 1)) :=
        Finset.sum_le_sum fun ℓ _ => hdec ℓ
      rw [Finset.sum_range_sub'] at h1
      linarith [hle (j + 1)]
    have hlow : (∑ _ℓ ∈ range (j + 1), (F 0 - ⨅ i, F i) / ((j : ℝ) + 1)) <
        ∑ ℓ ∈ range (j + 1), c * a ℓ :=
      Finset.sum_lt_sum_of_nonempty (by simp) fun ℓ hℓ =>
        hcon ℓ (by simpa [Nat.lt_succ_iff] using hℓ)
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      at hlow
    rw [mul_div_cancel₀ _ hj] at hlow
    linarith

/-! ### Smooth functions on matrices and the Riemannian gradient -/

variable {m n : Type*} [Fintype m] [Fintype n] {k : ℕ}

/-- `f : ℝ^{m × n} → ℝ` is `λ`-smooth with gradient `G` for the Frobenius norm. -/
structure IsSmooth (f : Matrix m n ℝ → ℝ) (G : Matrix m n ℝ → Matrix m n ℝ) (lam : ℝ) : Prop where
  hasGrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X
  lipschitz : ∀ X Y, ‖G X - G Y‖ ≤ lam * ‖X - Y‖

/-- The tangent space at `X` to the manifold `M_{rank X}` of matrices of the rank of `X`, namely
`{A X + X B}` (the tangent space at `X` of the orbit of `GL_m × GL_n`).  For `X = U S Vᵀ` with
orthonormal `U`, `V` and invertible `S` this is the range of `P_{U,V}`, see
`tangentSpaceAt_eq_of_isUnit`. -/
def tangentSpaceAt (X : Matrix m n ℝ) : Submodule ℝ (Matrix m n ℝ) where
  carrier := {Z | ∃ (A : Matrix m m ℝ) (B : Matrix n n ℝ), Z = A * X + X * B}
  add_mem' := by
    rintro _ _ ⟨A, B, rfl⟩ ⟨A', B', rfl⟩
    exact ⟨A + A', B + B', by simp only [Matrix.add_mul, Matrix.mul_add]; abel⟩
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨A, B, rfl⟩
    exact ⟨c • A, c • B, by simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]⟩

/-- The Riemannian gradient of the paper's Definition: the orthogonal projection of `∇f(X)` onto
the tangent space to `M_{rank X}` at `X`. -/
noncomputable def riemGrad (G : Matrix m n ℝ → Matrix m n ℝ) (X : Matrix m n ℝ) : Matrix m n ℝ :=
  (tangentSpaceAt X).starProjection (G X)

/-- Membership in the tangent space. -/
lemma mem_tangentSpaceAt {X Z : Matrix m n ℝ} :
    Z ∈ tangentSpaceAt X ↔ ∃ (A : Matrix m m ℝ) (B : Matrix n n ℝ), Z = A * X + X * B := Iff.rfl

/-- The gradient and the Riemannian gradient agree on tangent vectors. -/
lemma inner_grad_eq_inner_riemGrad (G : Matrix m n ℝ → Matrix m n ℝ) {X τ : Matrix m n ℝ}
    (hτ : τ ∈ tangentSpaceAt X) : ⟪G X, τ⟫ = ⟪riemGrad G X, τ⟫ := by
  have h := Submodule.starProjection_inner_eq_zero (K := tangentSpaceAt X) (G X) τ hτ
  rw [inner_sub_left] at h
  rw [riemGrad]; linarith

/-- `‖∇f(X)‖` dominates the Riemannian gradient. -/
lemma norm_riemGrad_le_norm (G : Matrix m n ℝ → Matrix m n ℝ) (X : Matrix m n ℝ) :
    ‖riemGrad G X‖ ≤ ‖G X‖ := by
  have h := inner_grad_eq_inner_riemGrad G
    (Submodule.starProjection_apply_mem (tangentSpaceAt X) (G X))
  rw [show (tangentSpaceAt X).starProjection (G X) = riemGrad G X from rfl,
    real_inner_self_eq_norm_sq] at h
  have h2 := real_inner_le_norm (G X) (riemGrad G X)
  rw [h, sq] at h2
  by_cases h0 : ‖riemGrad G X‖ = 0
  · rw [h0]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right h2 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

/-- For `X = U S Vᵀ` the tangent space of `M_{rank X}` lies in `T_{U,V}` (Section 3.2).
(arXiv 2306.00897.) -/
theorem tangentProj_eq_of_mem {U : Matrix m (Fin k) ℝ} {S : Matrix (Fin k) (Fin k) ℝ}
    {V : Matrix n (Fin k) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {Z : Matrix m n ℝ}
    (hZ : Z ∈ tangentSpaceAt (U * S * Vᵀ)) : tangentProj U V Z = Z := by
  obtain ⟨A, B, rfl⟩ := hZ
  rw [tangentProj_eq_self_iff hU hV]
  exact ⟨S * Vᵀ * B, A * U * S, by simp only [Matrix.mul_assoc]; abel⟩

/-- **The Riemannian gradient is dominated by `P_{U,V}(∇f(X))`** for every `X = U S Vᵀ`, also for
rank-deficient `X` (the second inequality of (3.15)).  (arXiv 2306.00897.) -/
theorem norm_riemGrad_le_tangentProj (G : Matrix m n ℝ → Matrix m n ℝ)
    {U : Matrix m (Fin k) ℝ} {S : Matrix (Fin k) (Fin k) ℝ} {V : Matrix n (Fin k) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ‖riemGrad G (U * S * Vᵀ)‖ ≤ ‖tangentProj U V (G (U * S * Vᵀ))‖ := by
  set X := U * S * Vᵀ with hX
  have hmem : riemGrad G X ∈ tangentSpaceAt X :=
    Submodule.starProjection_apply_mem (tangentSpaceAt X) (G X)
  have hP := isOrthProj_tangentProj (m := m) (n := n) hU hV
  have h1 : ‖riemGrad G X‖ ^ 2 = ⟪tangentProj U V (G X), riemGrad G X⟫ := by
    rw [hP.symm, tangentProj_eq_of_mem hU hV hmem, inner_grad_eq_inner_riemGrad G hmem,
      real_inner_self_eq_norm_sq]
  have h2 := real_inner_le_norm (tangentProj U V (G X)) (riemGrad G X)
  rw [← h1, sq] at h2
  by_cases h0 : ‖riemGrad G X‖ = 0
  · rw [h0]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right h2 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

/-- For `X = U S Vᵀ` of rank `k` (`S` invertible), the tangent space is the range of `P_{U,V}`.
(arXiv 2306.00897.) -/
theorem tangentSpaceAt_eq_of_isUnit {U : Matrix m (Fin k) ℝ} {S : Matrix (Fin k) (Fin k) ℝ}
    {V : Matrix n (Fin k) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (Z : Matrix m n ℝ) : Z ∈ tangentSpaceAt (U * S * Vᵀ) ↔ tangentProj U V Z = Z := by
  refine ⟨tangentProj_eq_of_mem hU hV, fun h => ?_⟩
  obtain ⟨B, C, rfl⟩ := (tangentProj_eq_self_iff hU hV _).1 h
  refine ⟨C * S⁻¹ * Uᵀ, V * S⁻¹ * B, ?_⟩
  have h1 : C * S⁻¹ * Uᵀ * (U * S * Vᵀ) = C * Vᵀ := by
    calc C * S⁻¹ * Uᵀ * (U * S * Vᵀ) = C * S⁻¹ * (Uᵀ * U) * S * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = C * Vᵀ := by
          rw [hU, Matrix.mul_one, Matrix.mul_assoc C, Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]
  have h2 : U * S * Vᵀ * (V * S⁻¹ * B) = U * B := by
    calc U * S * Vᵀ * (V * S⁻¹ * B) = U * S * (Vᵀ * V) * S⁻¹ * B := by
          simp only [Matrix.mul_assoc]
      _ = U * B := by
          rw [hV, Matrix.mul_one, Matrix.mul_assoc U, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
  rw [h1, h2, add_comm]

/-- **`grad f(X) = P_{U,V}(∇f(X))` when `rank X = k`** (Section 3.2).  (arXiv 2306.00897.) -/
theorem riemGrad_eq_tangentProj (G : Matrix m n ℝ → Matrix m n ℝ) {U : Matrix m (Fin k) ℝ}
    {S : Matrix (Fin k) (Fin k) ℝ} {V : Matrix n (Fin k) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) :
    riemGrad G (U * S * Vᵀ) = tangentProj U V (G (U * S * Vᵀ)) := by
  have hP := isOrthProj_tangentProj (m := m) (n := n) hU hV
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((tangentSpaceAt_eq_of_isUnit hU hV hS _).2 (hP.idem _)) fun w hw => ?_
  have hw' := (tangentSpaceAt_eq_of_isUnit hU hV hS _).1 hw
  rw [inner_sub_left, hP.symm, hw', sub_self]

/-- The Riemannian gradient vanishes iff `Xᵀ ∇f(X) = 0` and `∇f(X) Xᵀ = 0`.  (arXiv 2306.00897.) -/
theorem riemGrad_eq_zero_iff (G : Matrix m n ℝ → Matrix m n ℝ) (X : Matrix m n ℝ) :
    riemGrad G X = 0 ↔ Xᵀ * G X = 0 ∧ G X * Xᵀ = 0 := by
  have horth : riemGrad G X = 0 ↔ ∀ τ ∈ tangentSpaceAt X, ⟪G X, τ⟫ = 0 := by
    constructor
    · intro h τ hτ
      rw [inner_grad_eq_inner_riemGrad G hτ, h, inner_zero_left]
    · intro h
      have hmem : riemGrad G X ∈ tangentSpaceAt X :=
        Submodule.starProjection_apply_mem (tangentSpaceAt X) (G X)
      have := h _ hmem
      rw [inner_grad_eq_inner_riemGrad G hmem, real_inner_self_eq_norm_sq] at this
      simpa using this
  rw [horth]
  constructor
  · intro h
    constructor
    · have h1 := h (X * (Xᵀ * G X)) ⟨0, Xᵀ * G X, by simp⟩
      rw [Frobenius.inner_mul_left', real_inner_self_eq_norm_sq] at h1
      simpa using h1
    · have h1 := h ((G X * Xᵀ) * X) ⟨G X * Xᵀ, 0, by simp⟩
      rw [Frobenius.inner_mul_right', real_inner_self_eq_norm_sq] at h1
      simpa using h1
  · rintro ⟨h1, h2⟩ _ ⟨A, B, rfl⟩
    rw [inner_add_right, Frobenius.inner_mul_right', Frobenius.inner_mul_left', h1, h2]
    simp

/-- **Lower semicontinuity of `X ↦ ‖grad f(X)‖`** (Section 3.2): the rank can only drop in the
limit, and each tangent vector at the limit is a limit of tangent vectors.  (arXiv 2306.00897.) -/
theorem lowerSemicontinuous_norm_riemGrad {G : Matrix m n ℝ → Matrix m n ℝ} (hG : Continuous G) :
    LowerSemicontinuous fun X => ‖riemGrad G X‖ := by
  intro X y hy
  have hy : y < ‖riemGrad G X‖ := hy
  change ∀ᶠ Y in 𝓝 X, y < ‖riemGrad G Y‖
  have hmem : riemGrad G X ∈ tangentSpaceAt X :=
    Submodule.starProjection_apply_mem (tangentSpaceAt X) (G X)
  by_cases h0 : ‖riemGrad G X‖ = 0
  · rw [h0] at hy
    exact Eventually.of_forall fun Y => hy.trans_le (norm_nonneg _)
  obtain ⟨A, B, hAB⟩ := id hmem
  have hcont : Continuous fun Y : Matrix m n ℝ => A * Y + Y * B :=
    ((Frobenius.leftMulCLM A).continuous).add ((Frobenius.rightMulCLM B).continuous)
  have hτne : (A * X + X * B) ≠ 0 := by
    rw [← hAB]; exact fun h => h0 (by rw [h, norm_zero])
  have hquot : ContinuousAt (fun Y : Matrix m n ℝ => ⟪G Y, A * Y + Y * B⟫ / ‖A * Y + Y * B‖) X := by
    refine ContinuousAt.div (by fun_prop) hcont.norm.continuousAt (norm_ne_zero_iff.2 hτne)
  have hval : ⟪G X, A * X + X * B⟫ / ‖A * X + X * B‖ = ‖riemGrad G X‖ := by
    rw [← hAB, inner_grad_eq_inner_riemGrad G hmem, real_inner_self_eq_norm_sq, sq]
    field_simp
  have h1 : ∀ᶠ Y in 𝓝 X, y < ⟪G Y, A * Y + Y * B⟫ / ‖A * Y + Y * B‖ :=
    hquot.eventually (lt_mem_nhds (by change y < _ / _; rwa [hval]))
  filter_upwards [h1] with Y hY
  refine hY.trans_le ?_
  have hτ : A * Y + Y * B ∈ tangentSpaceAt Y := ⟨A, B, rfl⟩
  rw [inner_grad_eq_inner_riemGrad G hτ]
  exact div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) (real_inner_le_norm _ _)


/-! ### Algorithm 2: Riemannian block gradient descent with Gauss-Southwell rule -/

/-- `‖P_{U,V}(Z)‖² ≤ ‖Z V Vᵀ‖² + ‖U Uᵀ Z‖²` (Section 3.2).  (arXiv 2306.00897.) -/
theorem norm_tangentProj_sq_le (U : Matrix m (Fin k) ℝ) {V : Matrix n (Fin k) ℝ}
    (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    ‖tangentProj U V Z‖ ^ 2 ≤ ‖rightProj V Z‖ ^ 2 + ‖leftProj U Z‖ ^ 2 := by
  have hR := isOrthProj_rightProj (m := m) hV
  have hT : tangentProj U V Z = rightProj V Z + (leftProj U Z - rightProj V (leftProj U Z)) := by
    rw [tangentProj, tangent_apply, leftProj_rightProj_comm]; abel
  have h1 := hR.inner_sub_self Z (leftProj U Z)
  have h2 := hR.norm_sub_le (leftProj U Z)
  rw [hT, norm_add_sq_real, h1]
  have := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

/-- The two blocks are dominated by the full projected gradient.  (arXiv 2306.00897.) -/
theorem norm_rightProj_le_tangentProj {U : Matrix m (Fin k) ℝ} {V : Matrix n (Fin k) ℝ}
    (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) : ‖rightProj V Z‖ ≤ ‖tangentProj U V Z‖ := by
  have hR := isOrthProj_rightProj (m := m) hV
  have h : rightProj V Z = rightProj V (tangentProj U V Z) := by
    rw [tangentProj, tangent_apply, leftProj_rightProj_comm, map_sub, map_add, hR.idem, hR.idem]
    abel
  rw [h]
  exact hR.norm_le _

/-- The two blocks are dominated by the full projected gradient.  (arXiv 2306.00897.) -/
theorem norm_leftProj_le_tangentProj {U : Matrix m (Fin k) ℝ} {V : Matrix n (Fin k) ℝ}
    (hU : Uᵀ * U = 1) (Z : Matrix m n ℝ) : ‖leftProj U Z‖ ≤ ‖tangentProj U V Z‖ := by
  have hL := isOrthProj_leftProj (n := n) hU
  have h : leftProj U Z = leftProj U (tangentProj U V Z) := by
    rw [tangentProj, tangent_apply, map_sub, map_add, hL.idem, hL.idem]
    abel
  rw [h]
  exact hL.norm_le _

/-- A `λ`-smooth function satisfies the descent estimate along every projected gradient. -/
lemma IsSmooth.line_descent {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}
    (hf : IsSmooth f G lam) {Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hQ : IsOrthProj Q)
    (X : Matrix m n ℝ) (t : ℝ) :
    f (X - t • Q (G X)) ≤ f (X - (0 : ℝ) • Q (G X)) - t * ‖Q (G X)‖ ^ 2 +
      lam / 2 * t ^ 2 * ‖Q (G X)‖ ^ 2 := by
  have := loss_projGradStep_le hf.hasGrad hf.lipschitz hQ t X
  rw [projGradStep] at this
  rw [zero_smul, sub_zero]
  linarith

/-- One step of Algorithm 2 at `X = U S Vᵀ`, with step size `h` chosen by the rule `r` for
smoothness constant `lam`.  With `P̂₁ = ∇f(X) V` and `P̂₂ = ∇f(X)ᵀ U`: if `‖P̂₁‖ ≥ ‖P̂₂‖ ` then
`U' S' = U S - h P̂₁` with `U'` orthonormal and `V' = V`, else `V' S'ᵀ = V Sᵀ - h P̂₂` with `V'`
orthonormal and `U' = U`.  Any such factorization is allowed; a QR factorization is one.  The
rule sees the line function along `P₁ = ∇f(X) V Vᵀ` resp. `P₂ = U Uᵀ ∇f(X)`.

The paper writes `(V', S') := qr(V S - h P̂₂)` in the second branch.  For `U S' V'ᵀ = X - h P₂`,
which is step (2) of Section 3.2, the core has to be transposed, as is done here. -/
def RiemStep (f : Matrix m n ℝ → ℝ) (G : Matrix m n ℝ → Matrix m n ℝ) (lam : ℝ) (r : StepRule)
    (h : ℝ) (X : Matrix m n ℝ) (U : Matrix m (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (V : Matrix n (Fin k) ℝ) (U' : Matrix m (Fin k) ℝ) (S' : Matrix (Fin k) (Fin k) ℝ)
    (V' : Matrix n (Fin k) ℝ) : Prop :=
  (‖(G X)ᵀ * U‖ ≤ ‖G X * V‖ ∧ U'ᵀ * U' = 1 ∧ U' * S' = U * S - h • (G X * V) ∧ V' = V ∧
    r.Admissible lam (‖rightProj V (G X)‖ ^ 2) (fun t => f (X - t • rightProj V (G X))) h) ∨
  (‖G X * V‖ < ‖(G X)ᵀ * U‖ ∧ V'ᵀ * V' = 1 ∧ V' * S'ᵀ = V * Sᵀ - h • ((G X)ᵀ * U) ∧ U' = U ∧
    r.Admissible lam (‖leftProj U (G X)‖ ^ 2) (fun t => f (X - t • leftProj U (G X))) h)

/-- The block norms of the Gauss-Southwell rule are those of `P₁`, `P₂`. -/
lemma norm_rightProj_eq {V : Matrix n (Fin k) ℝ} (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    ‖rightProj V Z‖ = ‖Z * V‖ := by
  rw [rightProj_apply, Frobenius.norm_mul_transpose_of_orthonormal hV]

/-- The block norms of the Gauss-Southwell rule are those of `P₁`, `P₂`. -/
lemma norm_leftProj_eq {U : Matrix m (Fin k) ℝ} (hU : Uᵀ * U = 1) (Z : Matrix m n ℝ) :
    ‖leftProj U Z‖ = ‖Zᵀ * U‖ := by
  rw [← norm_transpose_mul_eq hU, ← Frobenius.norm_transpose (Zᵀ * U), Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- What a step of Algorithm 2 does in the ambient space.  (arXiv 2306.00897.) -/
theorem RiemStep.spec {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}
    {r : StepRule} {h : ℝ} {X : Matrix m n ℝ} {U U' : Matrix m (Fin k) ℝ}
    {S S' : Matrix (Fin k) (Fin k) ℝ} {V V' : Matrix n (Fin k) ℝ}
    (hs : RiemStep f G lam r h X U S V U' S' V') (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hX : X = U * S * Vᵀ) :
    U'ᵀ * U' = 1 ∧ V'ᵀ * V' = 1 ∧ ∃ Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ, IsOrthProj Q ∧
      U' * S' * V'ᵀ = X - h • Q (G X) ∧
      r.Admissible lam (‖Q (G X)‖ ^ 2) (fun t => f (X - t • Q (G X))) h ∧
      ‖tangentProj U V (G X)‖ ^ 2 ≤ 2 * ‖Q (G X)‖ ^ 2 ∧ ‖Q (G X)‖ ≤ ‖tangentProj U V (G X)‖ ∧
      (Q = rightProj V ∨ Q = leftProj U) := by
  have hT := norm_tangentProj_sq_le U hV (G X)
  rcases hs with ⟨hsel, hU', hUS, hVeq, hadm⟩ | ⟨hsel, hV', hVS, hUeq, hadm⟩
  · have hVeq' := hVeq.symm
    subst hVeq'
    refine ⟨hU', hV, rightProj V, isOrthProj_rightProj hV, ?_, hadm, ?_,
      norm_rightProj_le_tangentProj hV _, Or.inl rfl⟩
    · rw [hUS, Matrix.sub_mul, Matrix.smul_mul, hX, rightProj_apply]
    · rw [norm_rightProj_eq hV] at hT ⊢
      rw [norm_leftProj_eq hU] at hT
      have := pow_le_pow_left₀ (norm_nonneg _) hsel 2
      linarith
  · have hUeq' := hUeq.symm
    subst hUeq'
    refine ⟨hU, hV', leftProj U, isOrthProj_leftProj hU, ?_, hadm, ?_,
      norm_leftProj_le_tangentProj hU _, Or.inr rfl⟩
    · have hVS' : S' * V'ᵀ = S * Vᵀ - h • (Uᵀ * G X) := by
        have := congrArg Matrix.transpose hVS
        simpa [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_smul] using this
      rw [Matrix.mul_assoc, hVS', Matrix.mul_sub, Matrix.mul_smul, hX, leftProj_apply,
        Matrix.mul_assoc U S, Matrix.mul_assoc U Uᵀ]
    · rw [norm_leftProj_eq hU] at hT ⊢
      rw [norm_rightProj_eq hV] at hT
      have := pow_le_pow_left₀ (norm_nonneg _) hsel.le 2
      linarith

/-- The first inequality of (3.15) for one step.  (arXiv 2306.00897.) -/
theorem riemStep_decrease {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}
    (hf : IsSmooth f G lam) (hlam : 0 < lam) {r : StepRule} {h : ℝ} {X : Matrix m n ℝ}
    {U U' : Matrix m (Fin k) ℝ} {S S' : Matrix (Fin k) (Fin k) ℝ} {V V' : Matrix n (Fin k) ℝ}
    (hs : RiemStep f G lam r h X U S V U' S' V') (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hX : X = U * S * Vᵀ) :
    r.theta lam / (2 * lam) * ‖tangentProj U V (G X)‖ ^ 2 ≤ f X - f (U' * S' * V'ᵀ) := by
  obtain ⟨-, -, Q, hQ, hit, hadm, hT, -⟩ := hs.spec hU hV hX
  have hdec := StepRule.decrease (r := r) (Λ := lam) (d := ‖Q (G X)‖ ^ 2)
    (φ := fun t => f (X - t • Q (G X))) hlam (sq_nonneg _)
    (fun t _ _ => hf.line_descent hQ X t) hadm
  simp only [zero_smul, sub_zero] at hdec
  rw [hit]
  have hθ := StepRule.theta_pos hlam hadm
  calc r.theta lam / (2 * lam) * ‖tangentProj U V (G X)‖ ^ 2
      ≤ r.theta lam / (2 * lam) * (2 * ‖Q (G X)‖ ^ 2) := by gcongr
    _ = r.theta lam / lam * ‖Q (G X)‖ ^ 2 := by field_simp
    _ ≤ _ := hdec

/-- A run of Algorithm 2 with `X ℓ = U ℓ S ℓ (V ℓ)ᵀ`, step sizes `h ℓ` and rules `rule ℓ`; any
combination of rules is allowed. -/
structure IsRiemRun (f : Matrix m n ℝ → ℝ) (G : Matrix m n ℝ → Matrix m n ℝ) (lam : ℝ)
    (rule : ℕ → StepRule) (h : ℕ → ℝ) (U : ℕ → Matrix m (Fin k) ℝ)
    (S : ℕ → Matrix (Fin k) (Fin k) ℝ) (V : ℕ → Matrix n (Fin k) ℝ) (X : ℕ → Matrix m n ℝ) :
    Prop where
  orthU : (U 0)ᵀ * U 0 = 1
  orthV : (V 0)ᵀ * V 0 = 1
  iter : ∀ ℓ, X ℓ = U ℓ * S ℓ * (V ℓ)ᵀ
  step : ∀ ℓ, RiemStep f G lam (rule ℓ) (h ℓ) (X ℓ) (U ℓ) (S ℓ) (V ℓ) (U (ℓ + 1)) (S (ℓ + 1))
    (V (ℓ + 1))

section Run

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ} {rule : ℕ → StepRule}
  {h : ℕ → ℝ} {U : ℕ → Matrix m (Fin k) ℝ} {S : ℕ → Matrix (Fin k) (Fin k) ℝ}
  {V : ℕ → Matrix n (Fin k) ℝ} {X : ℕ → Matrix m n ℝ}

/-- All iterates of Algorithm 2 have orthonormal factors.  (arXiv 2306.00897.) -/
theorem IsRiemRun.orth (hrun : IsRiemRun f G lam rule h U S V X) (ℓ : ℕ) :
    (U ℓ)ᵀ * U ℓ = 1 ∧ (V ℓ)ᵀ * V ℓ = 1 := by
  induction ℓ with
  | zero => exact ⟨hrun.orthU, hrun.orthV⟩
  | succ ℓ ih =>
    obtain ⟨h1, h2, -⟩ := (hrun.step ℓ).spec ih.1 ih.2 (hrun.iter ℓ)
    exact ⟨h1, h2⟩

/-- **Theorem 3.4** (arXiv 2306.00897), estimate (3.15): for the iterates `X ℓ = U ℓ S ℓ (V ℓ)ᵀ` of
Algorithm 2 and any `λ`-smooth `f`,
`f(X_ℓ) - f(X_{ℓ+1}) ≥ ϑ_ℓ/(2λ) ‖P_{U_ℓ,V_ℓ}(∇f(X_ℓ))‖² ≥ ϑ_ℓ/(2λ) ‖grad f(X_ℓ)‖²` with
`ϑ_ℓ = (rule ℓ).theta λ`, that is `2 α (1 - α)` for `h = 2 α / λ`, `1/2` for exact line search and
`min {2 β γ (1 - γ), λ γ h̄}` for backtracking, in which case `h_ℓ = h̄ βⁱ` with
`i ≤ max {0, ⌈ln (2 / (h̄ λ) (1 - γ)) / ln β⌉}`.  Rank-deficient iterates are allowed.  The
assumption that `f` is bounded below is not needed here.  Exact line search is any minimizer over
`t > 0` of the line function.  We assume `λ > 0`. -/
theorem riemBlockDescent_decrease (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hrun : IsRiemRun f G lam rule h U S V X) (ℓ : ℕ) :
    (rule ℓ).theta lam / (2 * lam) * ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ ^ 2 ≤
        f (X ℓ) - f (X (ℓ + 1)) ∧
      (rule ℓ).theta lam / (2 * lam) * ‖riemGrad G (X ℓ)‖ ^ 2 ≤
        (rule ℓ).theta lam / (2 * lam) * ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ ^ 2 ∧
      ∀ hbar β γ, rule ℓ = StepRule.armijo hbar β γ → ∃ i : ℕ, h ℓ = hbar * β ^ i ∧
        (i : ℤ) ≤ max 0 ⌈Real.log (2 / (hbar * lam) * (1 - γ)) / Real.log β⌉ := by
  obtain ⟨hU, hV⟩ := hrun.orth ℓ
  obtain ⟨-, -, Q, hQ, -, hadm, -, -⟩ := (hrun.step ℓ).spec hU hV (hrun.iter ℓ)
  have hθ := StepRule.theta_pos hlam hadm
  refine ⟨?_, ?_, fun hbar β γ hr => ?_⟩
  · have := riemStep_decrease hf hlam (hrun.step ℓ) hU hV (hrun.iter ℓ)
    rwa [← hrun.iter (ℓ + 1)] at this
  · have h1 : ‖riemGrad G (X ℓ)‖ ≤ ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ := by
      rw [hrun.iter ℓ]; exact norm_riemGrad_le_tangentProj G hU hV
    gcongr
  · rw [hr] at hadm
    refine StepRule.armijo_index_le hlam (sq_nonneg _) (fun t _ _ => ?_) hadm
    exact hf.line_descent hQ (X ℓ) t


end Run

/-- Convergence to zero from convergence of the squared norms. -/
lemma tendsto_zero_of_sq {E : Type*} [NormedAddCommGroup E] {u : ℕ → E}
    (h : Tendsto (fun ℓ => ‖u ℓ‖ ^ 2) atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := h.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- The iteration count of Corollaries 3.2 and 3.5. -/
lemma exists_le_of_rate {v : ℕ → ℝ} {A : ℝ}
    (h : ∀ j : ℕ, ∃ ℓ ≤ j, v ℓ ≤ √(A / ((j : ℝ) + 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ℓ ≤ ⌈A * (ε ^ 2)⁻¹ - 1⌉₊, v ℓ ≤ ε := by
  obtain ⟨ℓ, hℓ, hv⟩ := h ⌈A * (ε ^ 2)⁻¹ - 1⌉₊
  refine ⟨ℓ, hℓ, hv.trans ?_⟩
  have h1 := Nat.le_ceil (A * (ε ^ 2)⁻¹ - 1)
  set j := ⌈A * (ε ^ 2)⁻¹ - 1⌉₊
  refine Real.sqrt_le_iff.2 ⟨hε.le, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have h2 : A * (ε ^ 2)⁻¹ ≤ (j : ℝ) + 1 := by linarith
  calc A = A * (ε ^ 2)⁻¹ * ε ^ 2 := by field_simp
    _ ≤ ((j : ℝ) + 1) * ε ^ 2 := by gcongr
    _ = _ := by ring

/-- The cluster-point step of Corollaries 3.5 and 3.9: at an accumulation point of `X` the limit
of the function values is attained and, by lower semicontinuity, the Riemannian gradient
vanishes.  (arXiv 2306.00897.) -/
theorem cluster_spec {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}
    (hf : IsSmooth f G lam) {X : ℕ → Matrix m n ℝ} {fstar : ℝ}
    (hlim : Tendsto (fun ℓ => f (X ℓ)) atTop (𝓝 fstar))
    (hgrad : Tendsto (fun ℓ => riemGrad G (X ℓ)) atTop (𝓝 0)) {Xs : Matrix m n ℝ}
    (hc : MapClusterPt Xs atTop X) : f Xs = fstar ∧ riemGrad G Xs = 0 := by
  have hGc : Continuous G := by
    refine (LipschitzWith.of_dist_le_mul (K := lam.toNNReal) fun x y => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal']
    exact (hf.lipschitz x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨F, hF, hFX⟩ := mapClusterPt_iff_ultrafilter.1 hc
  constructor
  · have h1 : Tendsto (fun ℓ => f (X ℓ)) F (𝓝 (f Xs)) :=
      ((hf.hasGrad Xs).continuousAt).tendsto.comp hFX
    exact tendsto_nhds_unique h1 (hlim.mono_left hF)
  · have hlsc := lowerSemicontinuous_norm_riemGrad hGc
    have h2 : Tendsto (fun ℓ => ‖riemGrad G (X ℓ)‖) F (𝓝 0) := by
      have := (tendsto_zero_iff_norm_tendsto_zero.1 hgrad).mono_left hF
      simpa using this
    by_contra hne
    have hpos : 0 < ‖riemGrad G Xs‖ := norm_pos_iff.2 hne
    have hev := hFX.eventually (hlsc Xs _ (half_lt_self hpos))
    have hev2 := h2.eventually (gt_mem_nhds (half_pos hpos))
    obtain ⟨ℓ, h5, h6⟩ := (hev.and hev2).exists
    exact lt_asymm h5 h6

section Run

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ} {rule : ℕ → StepRule}
  {h : ℕ → ℝ} {U : ℕ → Matrix m (Fin k) ℝ} {S : ℕ → Matrix (Fin k) (Fin k) ℝ}
  {V : ℕ → Matrix n (Fin k) ℝ} {X : ℕ → Matrix m n ℝ}

/-- **Corollary 3.5** (arXiv 2306.00897).  For a `λ`-smooth `f` bounded below and iterates of
Algorithm 2 under any combination of the step-size rules, with `ϑ > 0` a lower bound of the
`ϑ_ℓ` (in particular `ϑ = inf_ℓ ϑ_ℓ`, see `theta_iInf_pos`): `f(X_ℓ)` is decreasing and converges to
some `f∗ ≥ inf_{M_{≤k}} f`; `P_{U_ℓ,V_ℓ}(∇f(X_ℓ)) → 0` and `grad f(X_ℓ) → 0`; every accumulation
point `X∗` has `f(X∗) = f∗` and `grad f(X∗) = 0`; `‖grad f(X_ℓ)‖ ≤ ‖P_{U_ℓ,V_ℓ}(∇f(X_ℓ))‖`, and for
every `j` some `ℓ ≤ j` has `‖P_{U_ℓ,V_ℓ}(∇f(X_ℓ))‖ ≤ (2 λ (f(X₀) - f∗) ϑ⁻¹ / (j + 1))^{1/2}`; given
`ε > 0`, some `ℓ ≤ ⌈2 λ (f(X₀) - f∗) ϑ⁻¹ ε⁻² - 1⌉` has `‖grad f(X_ℓ)‖ ≤ ε`. -/
theorem riemBlockDescent_convergence (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hbdd : BddBelow (range f)) (hrun : IsRiemRun f G lam rule h U S V X) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑle : ∀ ℓ, ϑ ≤ (rule ℓ).theta lam) :
    Antitone (fun ℓ => f (X ℓ)) ∧ ∃ fstar, Tendsto (fun ℓ => f (X ℓ)) atTop (𝓝 fstar) ∧
      sInf (f '' {Y | Y.rank ≤ k}) ≤ fstar ∧
      Tendsto (fun ℓ => tangentProj (U ℓ) (V ℓ) (G (X ℓ))) atTop (𝓝 0) ∧
      Tendsto (fun ℓ => riemGrad G (X ℓ)) atTop (𝓝 0) ∧
      (∀ Xs, MapClusterPt Xs atTop X → f Xs = fstar ∧ riemGrad G Xs = 0) ∧
      (∀ ℓ, ‖riemGrad G (X ℓ)‖ ≤ ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖) ∧
      (∀ j : ℕ, ∃ ℓ ≤ j, ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ ≤
        √(2 * lam * (f (X 0) - fstar) * ϑ⁻¹ / ((j : ℝ) + 1))) ∧
      ∀ ε > 0, ∃ ℓ ≤ ⌈2 * lam * (f (X 0) - fstar) * ϑ⁻¹ * (ε ^ 2)⁻¹ - 1⌉₊,
        ‖riemGrad G (X ℓ)‖ ≤ ε := by
  have hle : ∀ ℓ, ‖riemGrad G (X ℓ)‖ ≤ ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ := fun ℓ => by
    obtain ⟨hU, hV⟩ := hrun.orth ℓ
    rw [hrun.iter ℓ]; exact norm_riemGrad_le_tangentProj G hU hV
  have hc : 0 < ϑ / (2 * lam) := by positivity
  have hdec : ∀ ℓ, ϑ / (2 * lam) * ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ ^ 2 ≤
      f (X ℓ) - f (X (ℓ + 1)) := fun ℓ => by
    refine le_trans ?_ (riemBlockDescent_decrease hf hlam hrun ℓ).1
    have := hϑle ℓ
    gcongr
  obtain ⟨hanti, fstar, hlim, hlow, ha, hrate⟩ := rate_core (F := fun ℓ => f (X ℓ))
    (a := fun ℓ => ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ ^ 2) hc (fun ℓ => sq_nonneg _) hdec
    (hbdd.mono (range_comp_subset_range X f))
  have hP := tendsto_zero_of_sq ha
  have hg : Tendsto (fun ℓ => riemGrad G (X ℓ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm hle ?_
    exact tendsto_zero_iff_norm_tendsto_zero.1 hP
  have hrate' : ∀ j : ℕ, ∃ ℓ ≤ j, ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ ≤
      √(2 * lam * (f (X 0) - fstar) * ϑ⁻¹ / ((j : ℝ) + 1)) := fun j => by
    obtain ⟨ℓ, hℓ, hb⟩ := hrate j
    refine ⟨ℓ, hℓ, Real.le_sqrt_of_sq_le ?_⟩
    have e : 2 * lam * (f (X 0) - fstar) * ϑ⁻¹ / ((j : ℝ) + 1) =
        (ϑ / (2 * lam))⁻¹ * ((f (X 0) - fstar) / ((j : ℝ) + 1)) := by
      field_simp
    rw [e, ← div_eq_inv_mul, le_div_iff₀' hc]
    exact hb
  refine ⟨hanti, fstar, hlim, ?_, hP, hg, fun Xs hXs => cluster_spec hf hlim hg hXs, hle, hrate',
    fun ε hε => ?_⟩
  · refine ge_of_tendsto' hlim fun ℓ => ?_
    refine csInf_le (hbdd.mono (image_subset_range _ _)) ⟨X ℓ, ?_, rfl⟩
    change (X ℓ).rank ≤ k
    rw [hrun.iter ℓ]
    exact rank_mul_mul_transpose_le _ _ _
  · obtain ⟨ℓ, hℓ, hb⟩ := exists_le_of_rate (v := fun ℓ => ‖riemGrad G (X ℓ)‖)
      (fun j => by
        obtain ⟨ℓ, hℓ, hb⟩ := hrate' j
        exact ⟨ℓ, hℓ, (hle ℓ).trans hb⟩) hε
    exact ⟨ℓ, hℓ, hb⟩

end Run

/-- **The constant `ϑ = inf_ℓ ϑ_ℓ` of Corollaries 3.2, 3.5 is positive** under their assumption:
fixed step sizes `h_ℓ = 2 α_ℓ / Λ` use `α_ℓ ∈ [a, b] ⊂ (0, 1)`, and backtracking uses fixed
parameters.  (arXiv 2306.00897.) -/
theorem theta_iInf_pos {rule : ℕ → StepRule} {Λ a b hbar β γ : ℝ} (hΛ : 0 < Λ) (ha : 0 < a)
    (hb : b < 1) (hb0 : 0 < hbar) (hβ : 0 < β) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hrule : ∀ ℓ, (∃ α, a ≤ α ∧ α ≤ b ∧ rule ℓ = StepRule.fixed α) ∨ rule ℓ = StepRule.exact ∨
      rule ℓ = StepRule.armijo hbar β γ) :
    0 < ⨅ ℓ, (rule ℓ).theta Λ ∧ ∀ ℓ, ⨅ i, (rule i).theta Λ ≤ (rule ℓ).theta Λ := by
  set c := min (2 * a * (1 - b)) (min (1 / 2) (min (2 * β * γ * (1 - γ)) (Λ * γ * hbar))) with hc
  have h1b : 0 < 1 - b := sub_pos.2 hb
  have h1g : 0 < 1 - γ := sub_pos.2 hγ1
  have hc0 : 0 < c := by
    refine lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hbound : ∀ ℓ, c ≤ (rule ℓ).theta Λ := fun ℓ => by
    rcases hrule ℓ with ⟨α, h1, h2, hr⟩ | hr | hr <;> rw [hr]
    · have ha1 : a ≤ α := h1
      refine (min_le_left _ _).trans ?_
      simp only [StepRule.theta]
      have : 1 - b ≤ 1 - α := by linarith
      have h0 : 0 ≤ 1 - α := by linarith
      have ha0 : 0 ≤ α := by linarith
      calc 2 * a * (1 - b) ≤ 2 * α * (1 - b) := by gcongr
        _ ≤ 2 * α * (1 - α) := by gcongr
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hc0.trans_le (le_ciInf hbound), fun ℓ => ciInf_le ⟨c, ?_⟩ ℓ⟩
  rintro _ ⟨i, rfl⟩
  exact hbound i

/-- One step of Algorithm 2 exists, for fixed and for backtracking step sizes.
(arXiv 2306.00897.) -/
theorem exists_riemStep {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}
    (hf : IsSmooth f G lam) (hlam : 0 < lam) (hkm : k ≤ Fintype.card m) (hkn : k ≤ Fintype.card n)
    {r : StepRule}
    (hr : (∃ α, 0 < α ∧ α < 1 ∧ r = StepRule.fixed α) ∨
      ∃ hbar β γ, 0 < hbar ∧ 0 < β ∧ β < 1 ∧ 0 < γ ∧ γ < 1 ∧ r = StepRule.armijo hbar β γ)
    (X : Matrix m n ℝ) {U : Matrix m (Fin k) ℝ} (S : Matrix (Fin k) (Fin k) ℝ)
    {V : Matrix n (Fin k) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ∃ (h : ℝ) (U' : Matrix m (Fin k) ℝ) (S' : Matrix (Fin k) (Fin k) ℝ)
      (V' : Matrix n (Fin k) ℝ), RiemStep f G lam r h X U S V U' S' V' := by
  have hadm : ∀ {Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}, IsOrthProj Q →
      ∃ h, r.Admissible lam (‖Q (G X)‖ ^ 2) (fun t => f (X - t • Q (G X))) h := by
    intro Q hQ
    rcases hr with ⟨α, h0, h1, rfl⟩ | ⟨hbar, β, γ, hb, hβ, hβ1, hγ, hγ1, rfl⟩
    · exact ⟨2 * α / lam, h0, h1, rfl⟩
    · obtain ⟨i, hA, hmin, -⟩ := StepRule.exists_armijo (φ := fun t => f (X - t • Q (G X)))
        (d := ‖Q (G X)‖ ^ 2) (γ := γ) hlam (sq_nonneg _) hb hβ hβ1 hγ1
        (fun t _ _ => hf.line_descent hQ X t)
      exact ⟨hbar * β ^ i, hb, hβ, hβ1, hγ, hγ1, i, rfl, hA, hmin⟩
  rcases le_or_gt ‖(G X)ᵀ * U‖ ‖G X * V‖ with hsel | hsel
  · obtain ⟨h, hh⟩ := hadm (isOrthProj_rightProj (m := m) hV)
    obtain ⟨U', hU', hcap⟩ := exists_orthonormal_capture_of_le_card (U * S - h • (G X * V)) hkm
    refine ⟨h, U', U'ᵀ * (U * S - h • (G X * V)), V, Or.inl ⟨hsel, hU', ?_, rfl, hh⟩⟩
    rw [← Matrix.mul_assoc, hcap]
  · obtain ⟨h, hh⟩ := hadm (isOrthProj_leftProj (n := n) hU)
    obtain ⟨V', hV', hcap⟩ := exists_orthonormal_capture_of_le_card (V * Sᵀ - h • ((G X)ᵀ * U)) hkn
    refine ⟨h, U, (V'ᵀ * (V * Sᵀ - h • ((G X)ᵀ * U)))ᵀ, V', Or.inr ⟨hsel, hV', ?_, rfl, hh⟩⟩
    rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, hcap]

/-- **Algorithm 2 is well defined**: for fixed step sizes and for backtracking, and from every
start with orthonormal `U₀`, `V₀`, a run exists when `k ≤ min (m, n)`.  (arXiv 2306.00897.) -/
theorem exists_riemRun {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}
    (hf : IsSmooth f G lam) (hlam : 0 < lam) (hkm : k ≤ Fintype.card m) (hkn : k ≤ Fintype.card n)
    {rule : ℕ → StepRule}
    (hr : ∀ ℓ, (∃ α, 0 < α ∧ α < 1 ∧ rule ℓ = StepRule.fixed α) ∨
      ∃ hbar β γ, 0 < hbar ∧ 0 < β ∧ β < 1 ∧ 0 < γ ∧ γ < 1 ∧ rule ℓ = StepRule.armijo hbar β γ)
    {U₀ : Matrix m (Fin k) ℝ} (S₀ : Matrix (Fin k) (Fin k) ℝ) {V₀ : Matrix n (Fin k) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (h : ℕ → ℝ) (U : ℕ → Matrix m (Fin k) ℝ) (S : ℕ → Matrix (Fin k) (Fin k) ℝ)
      (V : ℕ → Matrix n (Fin k) ℝ) (X : ℕ → Matrix m n ℝ),
      IsRiemRun f G lam rule h U S V X ∧ U 0 = U₀ ∧ S 0 = S₀ ∧ V 0 = V₀ := by
  let State := {p : Matrix m (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ × Matrix n (Fin k) ℝ //
    p.1ᵀ * p.1 = 1 ∧ p.2.2ᵀ * p.2.2 = 1}
  have hstep : ∀ (ℓ : ℕ) (s : State), ∃ (hh : ℝ) (s' : State),
      RiemStep f G lam (rule ℓ) hh (s.1.1 * s.1.2.1 * s.1.2.2ᵀ) s.1.1 s.1.2.1 s.1.2.2
        s'.1.1 s'.1.2.1 s'.1.2.2 := by
    intro ℓ s
    obtain ⟨hh, U', S', V', hs⟩ := exists_riemStep hf hlam hkm hkn (hr ℓ)
      (s.1.1 * s.1.2.1 * s.1.2.2ᵀ) s.1.2.1 s.2.1 s.2.2
    obtain ⟨h1, h2, -⟩ := hs.spec s.2.1 s.2.2 rfl
    exact ⟨hh, ⟨(U', S', V'), h1, h2⟩, hs⟩
  choose hh nxt hnxt using hstep
  let seq : ℕ → State := fun ℓ => Nat.rec ⟨(U₀, S₀, V₀), hU₀, hV₀⟩ (fun ℓ s => nxt ℓ s) ℓ
  exact ⟨fun ℓ => hh ℓ (seq ℓ), fun ℓ => (seq ℓ).1.1, fun ℓ => (seq ℓ).1.2.1,
    fun ℓ => (seq ℓ).1.2.2, fun ℓ => (seq ℓ).1.1 * (seq ℓ).1.2.1 * (seq ℓ).1.2.2ᵀ,
    ⟨hU₀, hV₀, fun _ => rfl, fun ℓ => hnxt ℓ (seq ℓ)⟩, rfl, rfl, rfl⟩

/-! ### Algorithm 1: balanced block gradient descent with Gauss-Southwell rule -/

/-- `(L, R)` is a **balanced** factorization: `L = U Σ^{1/2}`, `R = V Σ^{1/2}` for an economy-size
SVD `L Rᵀ = U Σ Vᵀ` with `k` columns (Section 3.1; zero singular values are allowed).  The paper's
wording "`L` and `R` have the same singular values" is not enough: `L = [e₁, 0]`, `R = [0, e₁]`
have equal singular values, `L Rᵀ = 0` and `‖L‖₂² ≠ ‖L Rᵀ‖₂`.  The construction with an SVD,
which is what the paper uses and what Algorithm 1 produces (`IsBalanced.of_qr_svd`), is meant. -/
def IsBalanced (L : Matrix m (Fin k) ℝ) (R : Matrix n (Fin k) ℝ) : Prop :=
  ∃ (U : Matrix m (Fin k) ℝ) (V : Matrix n (Fin k) ℝ) (σ : Fin k → ℝ),
    Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, 0 ≤ σ i) ∧
      L = U * Matrix.diagonal (fun i => √(σ i)) ∧ R = V * Matrix.diagonal (fun i => √(σ i))

/-- `Σ^{1/2} (Σ^{1/2})ᵀ = Σ`. -/
lemma diagonal_sqrt_mul {σ : Fin k → ℝ} (hσ : ∀ i, 0 ≤ σ i) :
    Matrix.diagonal (fun i => √(σ i)) * (Matrix.diagonal (fun i => √(σ i)))ᵀ =
      Matrix.diagonal σ := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact Real.mul_self_sqrt (hσ i)

/-- Step 4 of Algorithm 1 produces a balanced factorization of `L₊ R₊ᵀ`: from `L₊ = Q₁ S₁`,
`R₊ = Q₂ S₂` and an SVD `S₁ S₂ᵀ = U Σ Vᵀ` of the core, `L' = Q₁ U Σ^{1/2}`, `R' = Q₂ V Σ^{1/2}`.
(arXiv 2306.00897.) -/
theorem IsBalanced.of_qr_svd {Lp Q₁ : Matrix m (Fin k) ℝ} {Rp Q₂ : Matrix n (Fin k) ℝ}
    {S₁ S₂ U V : Matrix (Fin k) (Fin k) ℝ} {σ : Fin k → ℝ} (hQ₁ : Q₁ᵀ * Q₁ = 1) (hQ₂ : Q₂ᵀ * Q₂ = 1)
    (hL : Lp = Q₁ * S₁) (hR : Rp = Q₂ * S₂) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hσ : ∀ i, 0 ≤ σ i)
    (hS : S₁ * S₂ᵀ = U * Matrix.diagonal σ * Vᵀ) :
    IsBalanced (Q₁ * U * Matrix.diagonal fun i => √(σ i))
        (Q₂ * V * Matrix.diagonal fun i => √(σ i)) ∧
      (Q₁ * U * Matrix.diagonal fun i => √(σ i)) * (Q₂ * V * Matrix.diagonal fun i => √(σ i))ᵀ =
        Lp * Rpᵀ := by
  refine ⟨⟨Q₁ * U, Q₂ * V, σ, ?_, ?_, hσ, rfl, rfl⟩, ?_⟩
  · calc (Q₁ * U)ᵀ * (Q₁ * U) = Uᵀ * (Q₁ᵀ * Q₁) * U := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ₁, Matrix.mul_one, hU]
  · calc (Q₂ * V)ᵀ * (Q₂ * V) = Vᵀ * (Q₂ᵀ * Q₂) * V := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ₂, Matrix.mul_one, hV]
  · rw [hL, hR]
    calc (Q₁ * U * Matrix.diagonal fun i => √(σ i)) * (Q₂ * V * Matrix.diagonal fun i => √(σ i))ᵀ
        = Q₁ * U * ((Matrix.diagonal fun i => √(σ i)) * (Matrix.diagonal fun i => √(σ i))ᵀ) *
            (Q₂ * V)ᵀ := by
          rw [Matrix.transpose_mul (Q₂ * V)]
          simp only [Matrix.mul_assoc]
      _ = Q₁ * (U * Matrix.diagonal σ * Vᵀ) * Q₂ᵀ := by
          rw [diagonal_sqrt_mul hσ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Q₁ * S₁ * (Q₂ * S₂)ᵀ := by
          rw [← hS, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]

/-- Every matrix of rank `≤ k ≤ min (m, n)` has a balanced factorization.  (arXiv 2306.00897.) -/
theorem exists_isBalanced (X : Matrix m n ℝ) (hX : X.rank ≤ k) (hkm : k ≤ Fintype.card m)
    (hkn : k ≤ Fintype.card n) :
    ∃ (L : Matrix m (Fin k) ℝ) (R : Matrix n (Fin k) ℝ), IsBalanced L R ∧ L * Rᵀ = X := by
  classical
  obtain ⟨U, σ, V, hs⟩ := P2209_13569.exists_isSVD_of_le X hX hkm hkn
  refine ⟨_, _, ⟨U, V, σ, hs.orthU, hs.orthV, hs.nonneg, rfl, rfl⟩, ?_⟩
  rw [hs.eq, Matrix.transpose_mul V]
  calc U * Matrix.diagonal (fun i => √(σ i)) * ((Matrix.diagonal fun i => √(σ i))ᵀ * Vᵀ)
      = U * (Matrix.diagonal (fun i => √(σ i)) * (Matrix.diagonal fun i => √(σ i))ᵀ) * Vᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [diagonal_sqrt_mul hs.nonneg]

/-- The identities satisfied by a balanced factorization.  (arXiv 2306.00897.) -/
theorem IsBalanced.exists_svd {L : Matrix m (Fin k) ℝ} {R : Matrix n (Fin k) ℝ}
    (hb : IsBalanced L R) :
    ∃ (U : Matrix m (Fin k) ℝ) (V : Matrix n (Fin k) ℝ) (σ : Fin k → ℝ)
      (D : Matrix (Fin k) (Fin k) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, 0 ≤ σ i) ∧ D = Matrix.diagonal (fun i => √(σ i)) ∧
      L = U * D ∧ R = V * D ∧ D * Dᵀ = Matrix.diagonal σ ∧ Dᵀ * D = Matrix.diagonal σ ∧
      L * Rᵀ = U * Matrix.diagonal σ * Vᵀ ∧ Lᵀ * L = Matrix.diagonal σ ∧
      Rᵀ * R = Matrix.diagonal σ := by
  obtain ⟨U, V, σ, hU, hV, hσ, hL, hR⟩ := hb
  have h1 := diagonal_sqrt_mul hσ
  have h2 : (Matrix.diagonal fun i => √(σ i))ᵀ * (Matrix.diagonal fun i => √(σ i)) =
      Matrix.diagonal σ := by
    rw [Matrix.diagonal_transpose] at h1 ⊢; exact h1
  refine ⟨U, V, σ, _, hU, hV, hσ, rfl, hL, hR, h1, h2, ?_, ?_, ?_⟩
  · rw [hL, hR, Matrix.transpose_mul V, Matrix.mul_assoc U, ← Matrix.mul_assoc _ _ Vᵀ, h1,
      Matrix.mul_assoc]
  · rw [hL, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, h2]
  · rw [hR, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, h2]

open Curvature in
/-- `‖L‖₂² ≤ ‖L Rᵀ‖₂` and `‖R‖₂² ≤ ‖L Rᵀ‖₂` for a balanced factorization.  (arXiv 2306.00897.) -/
theorem IsBalanced.specNorm_sq_le [DecidableEq n] {L : Matrix m (Fin k) ℝ}
    {R : Matrix n (Fin k) ℝ} (hb : IsBalanced L R) :
    specNorm L ^ 2 ≤ specNorm (L * Rᵀ) ∧ specNorm R ^ 2 ≤ specNorm (L * Rᵀ) := by
  classical
  obtain ⟨U, V, σ, D, hU, hV, -, -, -, -, -, -, hX, hLL, hRR⟩ := hb.exists_svd
  have hc : Uᵀ * (L * Rᵀ) * V = Matrix.diagonal σ := by
    rw [hX]
    calc Uᵀ * (U * Matrix.diagonal σ * Vᵀ) * V
        = (Uᵀ * U) * Matrix.diagonal σ * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
  have hd : specNorm (Matrix.diagonal σ) ≤ specNorm (L * Rᵀ) := by
    rw [← hc]
    have h1 := specNorm_mul_le (Uᵀ * (L * Rᵀ)) V
    have h2 := specNorm_mul_le Uᵀ (L * Rᵀ)
    have hUt : specNorm Uᵀ ≤ 1 := by
      rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU
    have hV1 := specNorm_le_one_of_orthonormal hV
    have h0 := specNorm_nonneg (L * Rᵀ)
    have h3 := specNorm_nonneg (Uᵀ * (L * Rᵀ))
    calc specNorm (Uᵀ * (L * Rᵀ) * V) ≤ specNorm (Uᵀ * (L * Rᵀ)) * specNorm V := h1
      _ ≤ specNorm (Uᵀ * (L * Rᵀ)) * 1 := by gcongr
      _ ≤ specNorm Uᵀ * specNorm (L * Rᵀ) := by rw [mul_one]; exact h2
      _ ≤ 1 * specNorm (L * Rᵀ) := by gcongr
      _ = _ := one_mul _
  constructor
  · rw [sq, ← specNorm_transpose_mul_self, hLL]; exact hd
  · rw [sq, ← specNorm_transpose_mul_self, hRR]; exact hd

open Curvature in
/-- For a balanced factorization `‖L‖₂² = ‖R‖₂² = ‖L Rᵀ‖₂`, used in the proof of Corollary 3.2.
(arXiv 2306.00897.) -/
theorem IsBalanced.specNorm_sq_eq [DecidableEq n] {L : Matrix m (Fin k) ℝ}
    {R : Matrix n (Fin k) ℝ} (hb : IsBalanced L R) :
    specNorm L ^ 2 = specNorm (L * Rᵀ) ∧ specNorm R ^ 2 = specNorm (L * Rᵀ) := by
  classical
  obtain ⟨h1, h2⟩ := hb.specNorm_sq_le
  have h3 := specNorm_mul_le L Rᵀ
  rw [specNorm_transpose] at h3
  have ha := specNorm_nonneg L
  have hb' := specNorm_nonneg R
  constructor <;> nlinarith [sq_nonneg (specNorm L - specNorm R)]

/-- Descent estimate along a direction `D` with `⟪∇f(X), D⟫ = d` and `‖D‖² ≤ c d`. -/
lemma IsSmooth.descent_along {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}
    (hf : IsSmooth f G lam) (hlam : 0 ≤ lam) {X D : Matrix m n ℝ} {d c : ℝ}
    (hin : ⟪G X, D⟫ = d) (hnorm : ‖D‖ ^ 2 ≤ c * d) (t : ℝ) :
    f (X - t • D) ≤ f X - t * d + lam * c / 2 * t ^ 2 * d := by
  have h := descent_lemma hf.hasGrad hf.lipschitz X (X - t • D)
  rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, hin, norm_neg, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at h
  have h2 : lam / 2 * (t ^ 2 * ‖D‖ ^ 2) ≤ lam / 2 * (t ^ 2 * (c * d)) := by gcongr
  nlinarith

/-- One step of Algorithm 1 at `X = L Rᵀ` with `G₁ = ∇f(X) R`, `G₂ = ∇f(X)ᵀ L`: the block with the
larger gradient takes a gradient step with step size `h` chosen by the rule `r` for the constant
`Λ = λ ρ`; then `(L', R')` is a balanced factorization of the updated product (step 4,
`IsBalanced.of_qr_svd`). -/
def BalancedStep (f : Matrix m n ℝ → ℝ) (G : Matrix m n ℝ → Matrix m n ℝ) (Λ : ℝ) (r : StepRule)
    (h : ℝ) (L : Matrix m (Fin k) ℝ) (R : Matrix n (Fin k) ℝ) (L' : Matrix m (Fin k) ℝ)
    (R' : Matrix n (Fin k) ℝ) : Prop :=
  IsBalanced L' R' ∧
    ((‖(G (L * Rᵀ))ᵀ * L‖ ≤ ‖G (L * Rᵀ) * R‖ ∧ L' * R'ᵀ = (L - h • (G (L * Rᵀ) * R)) * Rᵀ ∧
        r.Admissible Λ (‖G (L * Rᵀ) * R‖ ^ 2) (fun t => f ((L - t • (G (L * Rᵀ) * R)) * Rᵀ)) h) ∨
      (‖G (L * Rᵀ) * R‖ < ‖(G (L * Rᵀ))ᵀ * L‖ ∧ L' * R'ᵀ = L * (R - h • ((G (L * Rᵀ))ᵀ * L))ᵀ ∧
        r.Admissible Λ (‖(G (L * Rᵀ))ᵀ * L‖ ^ 2)
          (fun t => f (L * (R - t • ((G (L * Rᵀ))ᵀ * L))ᵀ)) h))

/-- A run of Algorithm 1. -/
structure IsBalancedRun (f : Matrix m n ℝ → ℝ) (G : Matrix m n ℝ → Matrix m n ℝ) (Λ : ℝ)
    (rule : ℕ → StepRule) (h : ℕ → ℝ) (L : ℕ → Matrix m (Fin k) ℝ)
    (R : ℕ → Matrix n (Fin k) ℝ) : Prop where
  balanced : IsBalanced (L 0) (R 0)
  step : ∀ ℓ, BalancedStep f G Λ (rule ℓ) (h ℓ) (L ℓ) (R ℓ) (L (ℓ + 1)) (R (ℓ + 1))

/-- The norm `‖∇g(L, R)‖_F = (‖∇f(X) R‖² + ‖∇f(X)ᵀ L‖²)^{1/2}` of the gradient of
`g(L, R) = f(L Rᵀ)`, by (3.5). -/
noncomputable def gradNorm (G : Matrix m n ℝ → Matrix m n ℝ) (L : Matrix m (Fin k) ℝ)
    (R : Matrix n (Fin k) ℝ) : ℝ :=
  √(‖G (L * Rᵀ) * R‖ ^ 2 + ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2)

/-- The square of `‖∇g(L, R)‖`. -/
lemma gradNorm_sq (G : Matrix m n ℝ → Matrix m n ℝ) (L : Matrix m (Fin k) ℝ)
    (R : Matrix n (Fin k) ℝ) :
    gradNorm G L R ^ 2 = ‖G (L * Rᵀ) * R‖ ^ 2 + ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

section Balanced

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam ρ : ℝ}

open Curvature in
/-- The line function of the `L`-block satisfies the descent estimate with `Λ = λ ρ` ((3.8)), in the
form used in the proof of Theorem 3.1. -/
lemma line_descent_left (hf : IsSmooth f G lam) (hlam : 0 < lam)
    {L : Matrix m (Fin k) ℝ} {R : Matrix n (Fin k) ℝ} (hρ : specNorm R ^ 2 ≤ ρ) (t : ℝ) :
    f ((L - t • (G (L * Rᵀ) * R)) * Rᵀ) ≤
      f ((L - (0 : ℝ) • (G (L * Rᵀ) * R)) * Rᵀ) - t * ‖G (L * Rᵀ) * R‖ ^ 2 +
        (lam * ρ) / 2 * t ^ 2 * ‖G (L * Rᵀ) * R‖ ^ 2 := by
  classical
  set G₁ := G (L * Rᵀ) * R with hG₁
  have hin : ⟪G (L * Rᵀ), G₁ * Rᵀ⟫ = ‖G₁‖ ^ 2 := by
    rw [Frobenius.inner_mul_right', Matrix.transpose_transpose, ← hG₁, real_inner_self_eq_norm_sq]
  have hnorm : ‖G₁ * Rᵀ‖ ^ 2 ≤ ρ * ‖G₁‖ ^ 2 := by
    have h1 := frob_mul_le' G₁ Rᵀ
    rw [specNorm_transpose] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow] at h2
    nlinarith [sq_nonneg ‖G₁‖]
  have h := hf.descent_along hlam.le hin hnorm t
  have e : ∀ s : ℝ, (L - s • G₁) * Rᵀ = L * Rᵀ - s • (G₁ * Rᵀ) := fun s => by
    rw [Matrix.sub_mul, Matrix.smul_mul]
  rw [e, e, zero_smul, sub_zero]
  linarith

open Curvature in
/-- The line function of the `R`-block satisfies the descent estimate with `Λ = λ ρ` ((3.9)). -/
lemma line_descent_right (hf : IsSmooth f G lam) (hlam : 0 < lam)
    {L : Matrix m (Fin k) ℝ} {R : Matrix n (Fin k) ℝ} (hρ : specNorm L ^ 2 ≤ ρ) (t : ℝ) :
    f (L * (R - t • ((G (L * Rᵀ))ᵀ * L))ᵀ) ≤
      f (L * (R - (0 : ℝ) • ((G (L * Rᵀ))ᵀ * L))ᵀ) - t * ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2 +
        (lam * ρ) / 2 * t ^ 2 * ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2 := by
  classical
  set G₂ := (G (L * Rᵀ))ᵀ * L with hG₂
  have hin : ⟪G (L * Rᵀ), L * G₂ᵀ⟫ = ‖G₂‖ ^ 2 := by
    rw [Frobenius.inner_mul_left', ← Frobenius.inner_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose, ← hG₂, Matrix.transpose_transpose, real_inner_self_eq_norm_sq]
  have hnorm : ‖L * G₂ᵀ‖ ^ 2 ≤ ρ * ‖G₂‖ ^ 2 := by
    have h1 := frob_mul_le L G₂ᵀ
    rw [Frobenius.norm_transpose] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow] at h2
    nlinarith [sq_nonneg ‖G₂‖]
  have h := hf.descent_along hlam.le hin hnorm t
  have e : ∀ s : ℝ, L * (R - s • G₂)ᵀ = L * Rᵀ - s • (L * G₂ᵀ) := fun s => by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.mul_sub, Matrix.mul_smul]
  rw [e, e, zero_smul, sub_zero]
  linarith

open Curvature in
/-- One step of Algorithm 1 from a balanced point with `‖X‖₂ ≤ ρ`: the estimate (3.10).
(arXiv 2306.00897.) -/
theorem balancedStep_decrease [DecidableEq n] (hf : IsSmooth f G lam)
    (hlam : 0 < lam) (hρ0 : 0 < ρ) {r : StepRule} {h : ℝ} {L L' : Matrix m (Fin k) ℝ}
    {R R' : Matrix n (Fin k) ℝ} (hb : IsBalanced L R) (hρ : specNorm (L * Rᵀ) ≤ ρ)
    (hs : BalancedStep f G (lam * ρ) r h L R L' R') :
    r.theta (lam * ρ) / (2 * (lam * ρ)) * gradNorm G L R ^ 2 ≤ f (L * Rᵀ) - f (L' * R'ᵀ) := by
  obtain ⟨hL, hR⟩ := hb.specNorm_sq_le
  have hΛ : 0 < lam * ρ := mul_pos hlam hρ0
  rw [gradNorm_sq]
  rcases hs.2 with ⟨hsel, hit, hadm⟩ | ⟨hsel, hit, hadm⟩
  · have hdec := StepRule.decrease (r := r) (Λ := lam * ρ) (d := ‖G (L * Rᵀ) * R‖ ^ 2)
      (φ := fun t => f ((L - t • (G (L * Rᵀ) * R)) * Rᵀ)) hΛ (sq_nonneg _)
      (fun t _ _ => line_descent_left hf hlam (hR.trans hρ) t) hadm
    simp only [zero_smul, sub_zero] at hdec
    rw [hit]
    have hθ := StepRule.theta_pos hΛ hadm
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hsel 2
    calc r.theta (lam * ρ) / (2 * (lam * ρ)) * (‖G (L * Rᵀ) * R‖ ^ 2 + ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2)
        ≤ r.theta (lam * ρ) / (2 * (lam * ρ)) * (2 * ‖G (L * Rᵀ) * R‖ ^ 2) := by
          gcongr; linarith
      _ = r.theta (lam * ρ) / (lam * ρ) * ‖G (L * Rᵀ) * R‖ ^ 2 := by field_simp
      _ ≤ _ := hdec
  · have hdec := StepRule.decrease (r := r) (Λ := lam * ρ) (d := ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2)
      (φ := fun t => f (L * (R - t • ((G (L * Rᵀ))ᵀ * L))ᵀ)) hΛ (sq_nonneg _)
      (fun t _ _ => line_descent_right hf hlam (hL.trans hρ) t) hadm
    simp only [zero_smul, sub_zero] at hdec
    rw [hit]
    have hθ := StepRule.theta_pos hΛ hadm
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hsel.le 2
    calc r.theta (lam * ρ) / (2 * (lam * ρ)) * (‖G (L * Rᵀ) * R‖ ^ 2 + ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2)
        ≤ r.theta (lam * ρ) / (2 * (lam * ρ)) * (2 * ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2) := by
          gcongr; linarith
      _ = r.theta (lam * ρ) / (lam * ρ) * ‖(G (L * Rᵀ))ᵀ * L‖ ^ 2 := by field_simp
      _ ≤ _ := hdec

variable {rule : ℕ → StepRule} {h : ℕ → ℝ} {L : ℕ → Matrix m (Fin k) ℝ}
  {R : ℕ → Matrix n (Fin k) ℝ}

open Curvature in
/-- The induction in the proof of Theorem 3.1: all iterates are balanced, lie in `N₀`, and decrease
as in (3.10).  (arXiv 2306.00897.) -/
theorem IsBalancedRun.invariant [DecidableEq n] (hf : IsSmooth f G lam)
    (hlam : 0 < lam) (hρ0 : 0 < ρ) (hrun : IsBalancedRun f G (lam * ρ) rule h L R)
    (hN : ∀ Y : Matrix m n ℝ, Y.rank ≤ k → f Y ≤ f (L 0 * (R 0)ᵀ) → specNorm Y ≤ ρ) (ℓ : ℕ) :
    IsBalanced (L ℓ) (R ℓ) ∧ f (L ℓ * (R ℓ)ᵀ) ≤ f (L 0 * (R 0)ᵀ) ∧ specNorm (L ℓ * (R ℓ)ᵀ) ≤ ρ ∧
      (rule ℓ).theta (lam * ρ) / (2 * (lam * ρ)) * gradNorm G (L ℓ) (R ℓ) ^ 2 ≤
        f (L ℓ * (R ℓ)ᵀ) - f (L (ℓ + 1) * (R (ℓ + 1))ᵀ) := by
  have hΛ : 0 < lam * ρ := mul_pos hlam hρ0
  have hrank : ∀ ℓ, (L ℓ * (R ℓ)ᵀ).rank ≤ k := fun ℓ =>
    (Matrix.rank_mul_le_left _ _).trans (by simpa using (L ℓ).rank_le_card_width)
  have key : ∀ ℓ, IsBalanced (L ℓ) (R ℓ) ∧ f (L ℓ * (R ℓ)ᵀ) ≤ f (L 0 * (R 0)ᵀ) := by
    intro ℓ
    induction ℓ with
    | zero => exact ⟨hrun.balanced, le_rfl⟩
    | succ ℓ ih =>
      refine ⟨(hrun.step ℓ).1, ?_⟩
      have hd := balancedStep_decrease hf hlam hρ0 ih.1 (hN _ (hrank ℓ) ih.2) (hrun.step ℓ)
      have hθ : 0 < (rule ℓ).theta (lam * ρ) := by
        rcases (hrun.step ℓ).2 with ⟨-, -, hadm⟩ | ⟨-, -, hadm⟩ <;>
          exact StepRule.theta_pos hΛ hadm
      have : 0 ≤ (rule ℓ).theta (lam * ρ) / (2 * (lam * ρ)) * gradNorm G (L ℓ) (R ℓ) ^ 2 := by
        positivity
      linarith [ih.2]
  obtain ⟨h1, h2⟩ := key ℓ
  have h3 := hN _ (hrank ℓ) h2
  exact ⟨h1, h2, h3, balancedStep_decrease hf hlam hρ0 h1 h3 (hrun.step ℓ)⟩

open Curvature in
/-- **Theorem 3.1** (arXiv 2306.00897).  Let `f` be `λ`-smooth and let `N₀ = {X ∈ M_{≤k} :
f(X) ≤ f(L₀ R₀ᵀ)}` lie in `{‖X‖₂ ≤ ρ}`.  The iterates of Algorithm 1 satisfy (3.10),
`g(L_ℓ, R_ℓ) - g(L_{ℓ+1}, R_{ℓ+1}) ≥ ϑ_ℓ / (2 λ ρ) ‖∇g(L_ℓ, R_ℓ)‖²`, with
`ϑ_ℓ = (rule ℓ).theta (λ ρ)`, that is `2 α (1 - α)` for `h = 2 α / (λ ρ)`, `1/2` for exact line
search and `min {2 β γ (1 - γ), λ ρ γ h̄}` for backtracking, in which case `h_ℓ = h̄ βⁱ` with
`i ≤ max {0, ⌈ln (2 / (h̄ λ ρ) (1 - γ)) / ln β⌉}`.  We assume `λ, ρ > 0`. -/
theorem balancedBlockDescent_decrease [DecidableEq n] (hf : IsSmooth f G lam)
    (hlam : 0 < lam) (hρ0 : 0 < ρ) (hrun : IsBalancedRun f G (lam * ρ) rule h L R)
    (hN : ∀ Y : Matrix m n ℝ, Y.rank ≤ k → f Y ≤ f (L 0 * (R 0)ᵀ) → specNorm Y ≤ ρ) (ℓ : ℕ) :
    (rule ℓ).theta (lam * ρ) / (2 * (lam * ρ)) * gradNorm G (L ℓ) (R ℓ) ^ 2 ≤
        f (L ℓ * (R ℓ)ᵀ) - f (L (ℓ + 1) * (R (ℓ + 1))ᵀ) ∧
      ∀ hbar β γ, rule ℓ = StepRule.armijo hbar β γ → ∃ i : ℕ, h ℓ = hbar * β ^ i ∧
        (i : ℤ) ≤ max 0 ⌈Real.log (2 / (hbar * (lam * ρ)) * (1 - γ)) / Real.log β⌉ := by
  obtain ⟨hb, -, hsp, hd⟩ := hrun.invariant hf hlam hρ0 hN ℓ
  refine ⟨hd, fun hbar β γ hr => ?_⟩
  have hΛ : 0 < lam * ρ := mul_pos hlam hρ0
  obtain ⟨hL, hR⟩ := hb.specNorm_sq_le
  rcases (hrun.step ℓ).2 with ⟨-, -, hadm⟩ | ⟨-, -, hadm⟩ <;> rw [hr] at hadm
  · exact StepRule.armijo_index_le hΛ (sq_nonneg _)
      (fun t _ _ => line_descent_left hf hlam (hR.trans hsp) t) hadm
  · exact StepRule.armijo_index_le hΛ (sq_nonneg _)
      (fun t _ _ => line_descent_right hf hlam (hL.trans hsp) t) hadm

/-- The gradient of a smooth function is continuous. -/
lemma IsSmooth.continuous_grad (hf : IsSmooth f G lam) : Continuous G := by
  refine (LipschitzWith.of_dist_le_mul (K := lam.toNNReal) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal']
  exact (hf.lipschitz x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- A smooth function is continuous. -/
lemma IsSmooth.continuous (hf : IsSmooth f G lam) : Continuous f :=
  continuous_iff_continuousAt.2 fun X => (hf.hasGrad X).continuousAt

/-- Matrix multiplication is continuous for the Frobenius topology. -/
lemma continuous_matrix_mul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] :
    Continuous fun p : Matrix a b ℝ × Matrix b c ℝ => p.1 * p.2 :=
  (Frobenius.mulCLM (m := a) (l := b) (n := c)).isBoundedBilinearMap.continuous

/-- `(L, R) ↦ ‖∇g(L, R)‖` is continuous. -/
lemma IsSmooth.continuous_gradNorm (hf : IsSmooth f G lam) :
    Continuous fun p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ => gradNorm G p.1 p.2 := by
  have hGc := hf.continuous_grad
  have hX : Continuous fun p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ => p.1 * p.2ᵀ :=
    continuous_matrix_mul.comp (continuous_fst.prodMk
      (Frobenius.transposeCLM.continuous.comp continuous_snd))
  have h1 : Continuous fun p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ =>
      G (p.1 * p.2ᵀ) * p.2 :=
    continuous_matrix_mul.comp ((hGc.comp hX).prodMk continuous_snd)
  have h2 : Continuous fun p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ =>
      (G (p.1 * p.2ᵀ))ᵀ * p.1 :=
    continuous_matrix_mul.comp
      ((Frobenius.transposeCLM.continuous.comp (hGc.comp hX)).prodMk continuous_fst)
  exact Real.continuous_sqrt.comp ((h1.norm.pow 2).add (h2.norm.pow 2))

open Curvature in
/-- A continuous `f` whose constrained sublevel set is bounded attains its minimum on `M_{≤k}`. -/
lemma exists_isMin_rank_le [DecidableEq n] (hfc : Continuous f) {X₀ : Matrix m n ℝ}
    (hX₀ : X₀.rank ≤ k) (hN : ∀ Y : Matrix m n ℝ, Y.rank ≤ k → f Y ≤ f X₀ → specNorm Y ≤ ρ) :
    ∃ Y : Matrix m n ℝ, Y.rank ≤ k ∧ ∀ Z : Matrix m n ℝ, Z.rank ≤ k → f Y ≤ f Z := by
  set N₀ : Set (Matrix m n ℝ) := {Y | Y.rank ≤ k} ∩ {Y | f Y ≤ f X₀} with hN₀
  have hclosed : IsClosed N₀ :=
    (Matrix.isClosed_setOf_rank_le k).inter (isClosed_le hfc continuous_const)
  have hbd : ∀ Y ∈ N₀, ‖Y‖ ≤ ρ * ‖(1 : Matrix n n ℝ)‖ := fun Y hY => by
    have h1 := frob_mul_le Y (1 : Matrix n n ℝ)
    rw [Matrix.mul_one] at h1
    exact h1.trans (by gcongr; exact hN Y hY.1 hY.2)
  have hcomp : IsCompact N₀ :=
    Metric.isCompact_of_isClosed_isBounded hclosed (isBounded_iff_forall_norm_le.2 ⟨_, hbd⟩)
  obtain ⟨Y, hY, hmin⟩ := hcomp.exists_isMinOn ⟨X₀, hX₀, (le_refl _ : f _ ≤ f _)⟩
    hfc.continuousOn
  refine ⟨Y, hY.1, fun Z hZ => ?_⟩
  by_cases h1 : f Z ≤ f X₀
  · exact hmin ⟨hZ, h1⟩
  · exact (show f Y ≤ f X₀ from hY.2).trans (not_le.1 h1).le

open Curvature in
/-- A sequence of factor pairs with bounded spectral norms has an accumulation point. -/
lemma exists_mapClusterPt_of_specNorm_le {L : ℕ → Matrix m (Fin k) ℝ}
    {R : ℕ → Matrix n (Fin k) ℝ} {c : ℝ} (hL : ∀ ℓ, specNorm (L ℓ) ≤ c)
    (hR : ∀ ℓ, specNorm (R ℓ) ≤ c) :
    ∃ p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ, MapClusterPt p atTop fun ℓ => (L ℓ, R ℓ) := by
  have hmem : ∀ ℓ, (L ℓ, R ℓ) ∈ Metric.closedBall
      (0 : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ) (c * ‖(1 : Matrix (Fin k) (Fin k) ℝ)‖) :=
    fun ℓ => by
      rw [mem_closedBall_zero_iff, Prod.norm_def]
      refine max_le ?_ ?_
      · have h1 := frob_mul_le (L ℓ) (1 : Matrix (Fin k) (Fin k) ℝ)
        rw [Matrix.mul_one] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right (hL ℓ) (norm_nonneg _))
      · have h1 := frob_mul_le (R ℓ) (1 : Matrix (Fin k) (Fin k) ℝ)
        rw [Matrix.mul_one] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right (hR ℓ) (norm_nonneg _))
  obtain ⟨a, -, φ, hφ, hlim'⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  exact ⟨a, MapClusterPt.of_comp hφ.tendsto_atTop hlim'.mapClusterPt⟩

/-- Accumulation points of `(L_ℓ, R_ℓ)` when `f(L_ℓ R_ℓᵀ) → f∗` and `∇g(L_ℓ, R_ℓ) → 0`. -/
lemma cluster_spec_factors (hf : IsSmooth f G lam) {L : ℕ → Matrix m (Fin k) ℝ}
    {R : ℕ → Matrix n (Fin k) ℝ} {fstar : ℝ}
    (hlim : Tendsto (fun ℓ => f (L ℓ * (R ℓ)ᵀ)) atTop (𝓝 fstar))
    (hg : Tendsto (fun ℓ => gradNorm G (L ℓ) (R ℓ)) atTop (𝓝 0))
    {p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ}
    (hp : MapClusterPt p atTop fun ℓ => (L ℓ, R ℓ)) :
    f (p.1 * p.2ᵀ) = fstar ∧ gradNorm G p.1 p.2 = 0 := by
  obtain ⟨F, hF, hFp⟩ := mapClusterPt_iff_ultrafilter.1 hp
  have hXc : Continuous fun q : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ => q.1 * q.2ᵀ :=
    continuous_matrix_mul.comp (continuous_fst.prodMk
      (Frobenius.transposeCLM.continuous.comp continuous_snd))
  constructor
  · have h1 : Tendsto (fun ℓ => f (L ℓ * (R ℓ)ᵀ)) F (𝓝 (f (p.1 * p.2ᵀ))) :=
      ((hf.continuous.comp hXc).tendsto p).comp hFp
    exact tendsto_nhds_unique h1 (hlim.mono_left hF)
  · have h0 := (hf.continuous_gradNorm (k := k)).tendsto p
    have h1 := h0.comp hFp
    have h2 : Tendsto (fun ℓ => gradNorm G (L ℓ) (R ℓ)) F (𝓝 (gradNorm G p.1 p.2)) := h1
    exact tendsto_nhds_unique h2 (hg.mono_left hF)

open Curvature in
/-- **Corollary 3.2** (arXiv 2306.00897).  Under the assumptions of Theorem 3.1, for any combination
of the step-size rules with `ϑ > 0` a lower bound of the `ϑ_ℓ` (in particular `ϑ = inf_ℓ ϑ_ℓ`, see
`theta_iInf_pos`): `g(L_ℓ, R_ℓ) = f(L_ℓ R_ℓᵀ)` is decreasing and converges to some
`f∗ ≥ min_{M_{≤k}} f` (the minimum exists); `∇g(L_ℓ, R_ℓ) → 0`; `(L_ℓ, R_ℓ)` has an accumulation
point, and every accumulation point `(L∗, R∗)` has `g(L∗, R∗) = f∗`, `∇g(L∗, R∗) = 0`; for every `j`
some `ℓ ≤ j` has `‖∇g(L_ℓ, R_ℓ)‖ ≤ (2 λ ρ (f(X₀) - f∗) ϑ⁻¹ / (j + 1))^{1/2}`, and given `ε > 0` some
`ℓ ≤ ⌈2 λ ρ (f(X₀) - f∗) ϑ⁻¹ ε⁻² - 1⌉` has `‖∇g(L_ℓ, R_ℓ)‖ ≤ ε`. -/
theorem balancedBlockDescent_convergence [DecidableEq n] (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hρ0 : 0 < ρ) (hrun : IsBalancedRun f G (lam * ρ) rule h L R)
    (hN : ∀ Y : Matrix m n ℝ, Y.rank ≤ k → f Y ≤ f (L 0 * (R 0)ᵀ) → specNorm Y ≤ ρ) {ϑ : ℝ}
    (hϑ : 0 < ϑ) (hϑle : ∀ ℓ, ϑ ≤ (rule ℓ).theta (lam * ρ)) :
    Antitone (fun ℓ => f (L ℓ * (R ℓ)ᵀ)) ∧
      ∃ fstar, Tendsto (fun ℓ => f (L ℓ * (R ℓ)ᵀ)) atTop (𝓝 fstar) ∧
      (∃ Y : Matrix m n ℝ, Y.rank ≤ k ∧ (∀ Z : Matrix m n ℝ, Z.rank ≤ k → f Y ≤ f Z) ∧
        f Y ≤ fstar) ∧
      Tendsto (fun ℓ => gradNorm G (L ℓ) (R ℓ)) atTop (𝓝 0) ∧
      (∃ p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ,
        MapClusterPt p atTop fun ℓ => (L ℓ, R ℓ)) ∧
      (∀ p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ,
        MapClusterPt p atTop (fun ℓ => (L ℓ, R ℓ)) →
          f (p.1 * p.2ᵀ) = fstar ∧ gradNorm G p.1 p.2 = 0) ∧
      (∀ j : ℕ, ∃ ℓ ≤ j, gradNorm G (L ℓ) (R ℓ) ≤
        √(2 * (lam * ρ) * (f (L 0 * (R 0)ᵀ) - fstar) * ϑ⁻¹ / ((j : ℝ) + 1))) ∧
      ∀ ε > 0, ∃ ℓ ≤ ⌈2 * (lam * ρ) * (f (L 0 * (R 0)ᵀ) - fstar) * ϑ⁻¹ * (ε ^ 2)⁻¹ - 1⌉₊,
        gradNorm G (L ℓ) (R ℓ) ≤ ε := by
  have hΛ : 0 < lam * ρ := mul_pos hlam hρ0
  have hrank : ∀ ℓ, (L ℓ * (R ℓ)ᵀ).rank ≤ k := fun ℓ =>
    (Matrix.rank_mul_le_left _ _).trans (by simpa using (L ℓ).rank_le_card_width)
  have hinv := hrun.invariant hf hlam hρ0 hN
  obtain ⟨Y, hYr, hYmin⟩ := exists_isMin_rank_le hf.continuous (hrank 0) hN
  have hc : 0 < ϑ / (2 * (lam * ρ)) := by positivity
  have hdec : ∀ ℓ, ϑ / (2 * (lam * ρ)) * gradNorm G (L ℓ) (R ℓ) ^ 2 ≤
      f (L ℓ * (R ℓ)ᵀ) - f (L (ℓ + 1) * (R (ℓ + 1))ᵀ) := fun ℓ => by
    refine le_trans ?_ (hinv ℓ).2.2.2
    have := hϑle ℓ
    gcongr
  have hbddF : BddBelow (range fun ℓ => f (L ℓ * (R ℓ)ᵀ)) :=
    ⟨f Y, by rintro _ ⟨ℓ, rfl⟩; exact hYmin _ (hrank ℓ)⟩
  obtain ⟨hanti, fstar, hlim, hlow, ha, hrate⟩ := rate_core (F := fun ℓ => f (L ℓ * (R ℓ)ᵀ))
    (a := fun ℓ => gradNorm G (L ℓ) (R ℓ) ^ 2) hc (fun ℓ => sq_nonneg _) hdec hbddF
  have hg : Tendsto (fun ℓ => gradNorm G (L ℓ) (R ℓ)) atTop (𝓝 0) := by
    have := ha.sqrt
    simpa [Real.sqrt_sq (Real.sqrt_nonneg _), gradNorm] using this
  have hrate' : ∀ j : ℕ, ∃ ℓ ≤ j, gradNorm G (L ℓ) (R ℓ) ≤
      √(2 * (lam * ρ) * (f (L 0 * (R 0)ᵀ) - fstar) * ϑ⁻¹ / ((j : ℝ) + 1)) := fun j => by
    obtain ⟨ℓ, hℓ, hb⟩ := hrate j
    refine ⟨ℓ, hℓ, Real.le_sqrt_of_sq_le ?_⟩
    have e : 2 * (lam * ρ) * (f (L 0 * (R 0)ᵀ) - fstar) * ϑ⁻¹ / ((j : ℝ) + 1) =
        (ϑ / (2 * (lam * ρ)))⁻¹ * ((f (L 0 * (R 0)ᵀ) - fstar) / ((j : ℝ) + 1)) := by
      field_simp
    rw [e, ← div_eq_inv_mul, le_div_iff₀' hc]
    exact hb
  refine ⟨hanti, fstar, hlim, ⟨Y, hYr, hYmin, ge_of_tendsto' hlim fun ℓ => hYmin _ (hrank ℓ)⟩, hg,
    ?_, fun p hp => cluster_spec_factors hf hlim hg hp, hrate',
    fun ε hε => exists_le_of_rate hrate' hε⟩
  refine exists_mapClusterPt_of_specNorm_le (c := √ρ) (fun ℓ => ?_) (fun ℓ => ?_)
  · exact Real.le_sqrt_of_sq_le ((hinv ℓ).1.specNorm_sq_le.1.trans (hinv ℓ).2.2.1)
  · exact Real.le_sqrt_of_sq_le ((hinv ℓ).1.specNorm_sq_le.2.trans (hinv ℓ).2.2.1)

end Balanced

/-! ### Section 3.3: comparison of `∇g` and the Riemannian gradient -/

/-- Cancel `a` in `a² ≤ b a`. -/
lemma le_of_sq_le_mul {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b * a) : a ≤ b := by
  by_contra hlt
  have hlt' := not_le.1 hlt
  have ha : 0 < a := hb.trans_lt hlt'
  nlinarith

open Curvature in
/-- **(3.17)** (arXiv 2306.00897): for a balanced factorization `X = L Rᵀ`,
`‖∇g(L, R)‖² ≤ 2 ‖X‖₂ ‖grad f(X)‖²`.  Rank-deficient `X` are allowed. -/
theorem IsBalanced.gradNorm_sq_le [DecidableEq n] (G : Matrix m n ℝ → Matrix m n ℝ)
    {L : Matrix m (Fin k) ℝ} {R : Matrix n (Fin k) ℝ} (hb : IsBalanced L R) :
    gradNorm G L R ^ 2 ≤ 2 * specNorm (L * Rᵀ) * ‖riemGrad G (L * Rᵀ)‖ ^ 2 := by
  classical
  obtain ⟨U, V, σ, D, hU, hV, -, -, hL, hR, hDD, -, hX, -, -⟩ := hb.exists_svd
  obtain ⟨hsL, hsR⟩ := hb.specNorm_sq_le
  rw [gradNorm_sq]
  set X := L * Rᵀ with hXdef
  set Z := G X with hZ
  set g := riemGrad G X with hg
  have hτ₁ : Z * R * Rᵀ ∈ tangentSpaceAt X := by
    refine ⟨Z * V * Uᵀ, 0, ?_⟩
    rw [Matrix.mul_zero, add_zero, hX]
    calc Z * R * Rᵀ = Z * V * (D * Dᵀ) * Vᵀ := by
          rw [hR, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Z * V * (Uᵀ * U) * Matrix.diagonal σ * Vᵀ := by
          rw [hDD, hU, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hτ₂ : L * (Lᵀ * Z) ∈ tangentSpaceAt X := by
    refine ⟨0, V * Uᵀ * Z, ?_⟩
    rw [Matrix.zero_mul, zero_add, hX]
    calc L * (Lᵀ * Z) = U * (D * Dᵀ) * Uᵀ * Z := by
          rw [hL, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal σ * (Vᵀ * V) * Uᵀ * Z := by
          rw [hDD, hV, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have h1 : ‖Z * R‖ ≤ ‖g‖ * specNorm R := by
    refine le_of_sq_le_mul (by have := specNorm_nonneg R; positivity) ?_
    have e1 : ‖Z * R‖ ^ 2 = ⟪Z, Z * R * Rᵀ⟫ := by
      rw [Frobenius.inner_mul_right', Matrix.transpose_transpose, real_inner_self_eq_norm_sq]
    have e2 : ⟪Z, Z * R * Rᵀ⟫ = ⟪g * R, Z * R⟫ := by
      rw [inner_grad_eq_inner_riemGrad G hτ₁, Frobenius.inner_mul_right',
        Matrix.transpose_transpose]
    rw [e1, e2]
    calc ⟪g * R, Z * R⟫ ≤ ‖g * R‖ * ‖Z * R‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * specNorm R * ‖Z * R‖ := by gcongr; exact frob_mul_le' _ _
  have h2 : ‖Lᵀ * Z‖ ≤ ‖g‖ * specNorm L := by
    refine le_of_sq_le_mul (by have := specNorm_nonneg L; positivity) ?_
    have e1 : ‖Lᵀ * Z‖ ^ 2 = ⟪Z, L * (Lᵀ * Z)⟫ := by
      rw [Frobenius.inner_mul_left', real_inner_self_eq_norm_sq]
    have e2 : ⟪Z, L * (Lᵀ * Z)⟫ = ⟪Lᵀ * g, Lᵀ * Z⟫ := by
      rw [inner_grad_eq_inner_riemGrad G hτ₂, Frobenius.inner_mul_left']
    rw [e1, e2]
    calc ⟪Lᵀ * g, Lᵀ * Z⟫ ≤ ‖Lᵀ * g‖ * ‖Lᵀ * Z‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * specNorm L * ‖Lᵀ * Z‖ := by
          gcongr
          have := frob_mul_le Lᵀ g
          rw [specNorm_transpose] at this
          linarith
  have hZL : ‖Zᵀ * L‖ = ‖Lᵀ * Z‖ := by
    rw [← Frobenius.norm_transpose (Zᵀ * L), Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hZL]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h3 h4
  have hg2 : 0 ≤ ‖g‖ ^ 2 := sq_nonneg _
  nlinarith

/-- The diagonal entries of an SVD with `k` columns dominate `σ_k` (index `k - 1` from zero). -/
lemma singularValue_le_sigma [DecidableEq n] {U : Matrix m (Fin k) ℝ} {V : Matrix n (Fin k) ℝ}
    {σ : Fin k → ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hσ : ∀ i, 0 ≤ σ i) (i : Fin k) :
    (Matrix.toEuclideanLin (U * Matrix.diagonal σ * Vᵀ)).singularValues (k - 1) ≤ σ i := by
  have hrk : (U * Matrix.diagonal σ * Vᵀ).rank ≤ k := rank_mul_mul_transpose_le U _ V
  rcases hrk.eq_or_lt with hk | hk
  · have h := SVD.singularValues_mul_norm_le_of_eq_mul hU hV rfl hk (EuclideanSpace.single i 1)
    have e : Matrix.toEuclideanLin (Matrix.diagonal σ) (EuclideanSpace.single i (1 : ℝ)) =
        EuclideanSpace.single i (σ i) := by
      ext j
      simp [Matrix.toLpLin_apply]
    rw [e] at h
    simpa [abs_of_nonneg (hσ i)] using h
  · have h0 : (Matrix.toEuclideanLin (U * Matrix.diagonal σ * Vᵀ)).singularValues (k - 1) = 0 := by
      rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range, ← SVD.rank_eq_finrank_range]
      omega
    rw [h0]; exact hσ i

/-- `‖A Σ^{1/2}‖² ≥ c ‖A‖²` when all singular values are at least `c`. -/
lemma le_norm_mul_diagonal_sq {a : Type*} [Fintype a] {A : Matrix a (Fin k) ℝ} {σ : Fin k → ℝ}
    {c : ℝ} (hσ : ∀ i, 0 ≤ σ i) (hc : ∀ i, c ≤ σ i) :
    c * ‖A‖ ^ 2 ≤ ‖A * Matrix.diagonal fun i => √(σ i)‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.mul_diagonal, mul_pow, Real.sq_sqrt (hσ j), mul_comm]
  exact mul_le_mul_of_nonneg_left (hc j) (sq_nonneg _)

/-- **(3.16)** (arXiv 2306.00897): for a balanced factorization `X = L Rᵀ`,
`σ_k(X) ‖grad f(X)‖² ≤ ‖∇g(L, R)‖²`, with `σ_k(X)` the `k`-th singular value (index `k - 1` from
zero, which is `0` when `rank X < k`). -/
theorem IsBalanced.le_gradNorm_sq [DecidableEq n] (G : Matrix m n ℝ → Matrix m n ℝ)
    {L : Matrix m (Fin k) ℝ} {R : Matrix n (Fin k) ℝ} (hb : IsBalanced L R) :
    (Matrix.toEuclideanLin (L * Rᵀ)).singularValues (k - 1) * ‖riemGrad G (L * Rᵀ)‖ ^ 2 ≤
      gradNorm G L R ^ 2 := by
  obtain ⟨U, V, σ, D, hU, hV, hσ, hD, hL, hR, -, -, hX, -, -⟩ := hb.exists_svd
  subst hD
  rw [gradNorm_sq]
  set Z := G (L * Rᵀ) with hZ
  set c := (Matrix.toEuclideanLin (L * Rᵀ)).singularValues (k - 1) with hc
  have hc0 : 0 ≤ c := LinearMap.singularValues_nonneg _ _
  have hcσ : ∀ i, c ≤ σ i := fun i => by
    rw [hc, hX]; exact singularValue_le_sigma hU hV hσ i
  have h1 : c * ‖Z * V‖ ^ 2 ≤ ‖Z * R‖ ^ 2 := by
    rw [hR, ← Matrix.mul_assoc]; exact le_norm_mul_diagonal_sq hσ hcσ
  have h2 : c * ‖Zᵀ * U‖ ^ 2 ≤ ‖Zᵀ * L‖ ^ 2 := by
    rw [hL, ← Matrix.mul_assoc]; exact le_norm_mul_diagonal_sq hσ hcσ
  have h3 := norm_tangentProj_sq_le U hV Z
  rw [norm_rightProj_eq hV, norm_leftProj_eq hU] at h3
  have h4 : ‖riemGrad G (L * Rᵀ)‖ ≤ ‖tangentProj U V Z‖ := by
    rw [hZ, hX]; exact norm_riemGrad_le_tangentProj G hU hV
  have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  calc c * ‖riemGrad G (L * Rᵀ)‖ ^ 2 ≤ c * (‖Z * V‖ ^ 2 + ‖Zᵀ * U‖ ^ 2) := by
        gcongr; exact h5.trans h3
    _ ≤ _ := by rw [mul_add]; linarith

/-! ### Algorithm 3: alternating least squares -/

/-- `Q` is a QR-factor of `A`: it has orthonormal columns and `A = Q T`.  Rank-deficient `A` are
allowed. -/
def IsQFactor {a : Type*} [Fintype a] (Q A : Matrix a (Fin k) ℝ) : Prop :=
  Qᵀ * Q = 1 ∧ ∃ T : Matrix (Fin k) (Fin k) ℝ, A = Q * T

/-- A run of Algorithm 3 with iterates `X_ℓ = U ℓ (V ℓ)ᵀ` and half-steps
`X_{ℓ+1/2} = Uh ℓ (Vq ℓ)ᵀ`:  line 2 replaces `V ℓ` by a QR-factor `Vq ℓ`, line 3 finds
`Uh ℓ ∈ argmin_W f(W (Vq ℓ)ᵀ)`, line 4 takes the QR-factor `U (ℓ + 1)` of `Uh ℓ`, and line 5 finds
`V (ℓ + 1) ∈ argmin_W f(U (ℓ + 1) Wᵀ)`. -/
structure IsALSRun (f : Matrix m n ℝ → ℝ) (U : ℕ → Matrix m (Fin k) ℝ)
    (V Vq : ℕ → Matrix n (Fin k) ℝ) (Uh : ℕ → Matrix m (Fin k) ℝ) : Prop where
  qr_V : ∀ ℓ, IsQFactor (Vq ℓ) (V ℓ)
  argmin_U : ∀ ℓ (W : Matrix m (Fin k) ℝ), f (Uh ℓ * (Vq ℓ)ᵀ) ≤ f (W * (Vq ℓ)ᵀ)
  qr_U : ∀ ℓ, IsQFactor (U (ℓ + 1)) (Uh ℓ)
  argmin_V : ∀ ℓ (W : Matrix n (Fin k) ℝ), f (U (ℓ + 1) * (V (ℓ + 1))ᵀ) ≤ f (U (ℓ + 1) * Wᵀ)

section ALS

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ}

/-- A point at least as good as the projected gradient step with `h = 1 / λ` decreases `f` by
`‖Π ∇f(X)‖² / (2 λ)`: the comparison argument of Section 3.5. -/
lemma decrease_of_le_step (hf : IsSmooth f G lam) (hlam : 0 < lam)
    {Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hQ : IsOrthProj Q) {X Y : Matrix m n ℝ}
    (hY : f Y ≤ f (X - (1 / lam) • Q (G X))) : 1 / (2 * lam) * ‖Q (G X)‖ ^ 2 ≤ f X - f Y := by
  have h := hf.line_descent hQ X (1 / lam)
  rw [zero_smul, sub_zero] at h
  have e : 1 / (2 * lam) * ‖Q (G X)‖ ^ 2 =
      1 / lam * ‖Q (G X)‖ ^ 2 - lam / 2 * (1 / lam) ^ 2 * ‖Q (G X)‖ ^ 2 := by
    field_simp
    ring
  rw [e]; linarith

/-- A minimizer over `{W Qᵀ}` compared with a point `X` of that space. -/
lemma decrease_of_min_right (hf : IsSmooth f G lam) (hlam : 0 < lam) {Q : Matrix n (Fin k) ℝ}
    (hQ : Qᵀ * Q = 1) {X Y : Matrix m n ℝ} {W₀ : Matrix m (Fin k) ℝ} (hX : X = W₀ * Qᵀ)
    (hY : ∀ W : Matrix m (Fin k) ℝ, f Y ≤ f (W * Qᵀ)) :
    1 / (2 * lam) * ‖rightProj Q (G X)‖ ^ 2 ≤ f X - f Y := by
  refine decrease_of_le_step hf hlam (isOrthProj_rightProj hQ) ?_
  have e : X - (1 / lam) • rightProj Q (G X) = (W₀ - (1 / lam) • (G X * Q)) * Qᵀ := by
    rw [Matrix.sub_mul, Matrix.smul_mul, rightProj_apply, ← hX]
  rw [e]
  exact hY _

/-- A minimizer over `{Q Wᵀ}` compared with a point `X` of that space. -/
lemma decrease_of_min_left (hf : IsSmooth f G lam) (hlam : 0 < lam) {Q : Matrix m (Fin k) ℝ}
    (hQ : Qᵀ * Q = 1) {X Y : Matrix m n ℝ} {W₀ : Matrix n (Fin k) ℝ} (hX : X = Q * W₀ᵀ)
    (hY : ∀ W : Matrix n (Fin k) ℝ, f Y ≤ f (Q * Wᵀ)) :
    1 / (2 * lam) * ‖leftProj Q (G X)‖ ^ 2 ≤ f X - f Y := by
  refine decrease_of_le_step hf hlam (isOrthProj_leftProj hQ) ?_
  have e : X - (1 / lam) • leftProj Q (G X) = Q * (W₀ - (1 / lam) • ((G X)ᵀ * Q))ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.transpose_mul, Matrix.transpose_transpose, leftProj_apply, ← hX, Matrix.mul_assoc]
  rw [e]
  exact hY _

variable {U : ℕ → Matrix m (Fin k) ℝ} {V Vq : ℕ → Matrix n (Fin k) ℝ}
  {Uh : ℕ → Matrix m (Fin k) ℝ}

/-- The half-step estimates of Section 3.5: (3.29) for the half-steps after the first one, in the
sharper form with `P_{U,V}`.  At `ℓ = 0` estimate (3.29) fails, see
`als_counterexample`: the first half-step only gives `als_first_half_step`.  (arXiv 2306.00897.) -/
theorem als_half_step_decrease (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hrun : IsALSRun f U V Vq Uh) (ℓ : ℕ) :
    1 / (2 * lam) * ‖riemGrad G (Uh ℓ * (Vq ℓ)ᵀ)‖ ^ 2 ≤
        1 / (2 * lam) * ‖tangentProj (U (ℓ + 1)) (Vq ℓ) (G (Uh ℓ * (Vq ℓ)ᵀ))‖ ^ 2 ∧
      1 / (2 * lam) * ‖tangentProj (U (ℓ + 1)) (Vq ℓ) (G (Uh ℓ * (Vq ℓ)ᵀ))‖ ^ 2 ≤
        f (Uh ℓ * (Vq ℓ)ᵀ) - f (U (ℓ + 1) * (V (ℓ + 1))ᵀ) ∧
      1 / (2 * lam) * ‖riemGrad G (U (ℓ + 1) * (V (ℓ + 1))ᵀ)‖ ^ 2 ≤
        1 / (2 * lam) * ‖tangentProj (U (ℓ + 1)) (Vq (ℓ + 1)) (G (U (ℓ + 1) * (V (ℓ + 1))ᵀ))‖ ^ 2 ∧
      1 / (2 * lam) * ‖tangentProj (U (ℓ + 1)) (Vq (ℓ + 1)) (G (U (ℓ + 1) * (V (ℓ + 1))ᵀ))‖ ^ 2 ≤
        f (U (ℓ + 1) * (V (ℓ + 1))ᵀ) - f (Uh (ℓ + 1) * (Vq (ℓ + 1))ᵀ) := by
  obtain ⟨hQU, T, hT⟩ := hrun.qr_U ℓ
  obtain ⟨hQV, -⟩ := hrun.qr_V ℓ
  obtain ⟨hQV', T', hT'⟩ := hrun.qr_V (ℓ + 1)
  have hc : 0 < 1 / (2 * lam) := by positivity
  -- the half step is a minimizer on `T_{V_ℓ}`
  have hXh : Uh ℓ * (Vq ℓ)ᵀ = U (ℓ + 1) * (Vq ℓ * Tᵀ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hT, Matrix.mul_assoc]
  have h0 := decrease_of_min_right hf hlam hQV (X := Uh ℓ * (Vq ℓ)ᵀ) rfl (hrun.argmin_U ℓ)
  have hC : rightProj (Vq ℓ) (G (Uh ℓ * (Vq ℓ)ᵀ)) = 0 := by
    rw [sub_self] at h0
    have h1 : ‖rightProj (Vq ℓ) (G (Uh ℓ * (Vq ℓ)ᵀ))‖ ^ 2 ≤ 0 := by
      by_contra hne
      have := mul_pos hc (not_le.1 hne)
      linarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _)))
  have hB := decrease_of_min_left hf hlam hQU hXh (hrun.argmin_V ℓ)
  -- the next iterate is a minimizer on `T_{U_{ℓ+1}}`
  have h0' := decrease_of_min_left hf hlam hQU (X := U (ℓ + 1) * (V (ℓ + 1))ᵀ) rfl (hrun.argmin_V ℓ)
  have hD : leftProj (U (ℓ + 1)) (G (U (ℓ + 1) * (V (ℓ + 1))ᵀ)) = 0 := by
    rw [sub_self] at h0'
    have h1 : ‖leftProj (U (ℓ + 1)) (G (U (ℓ + 1) * (V (ℓ + 1))ᵀ))‖ ^ 2 ≤ 0 := by
      by_contra hne
      have := mul_pos hc (not_le.1 hne)
      linarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _)))
  have hXf : U (ℓ + 1) * (V (ℓ + 1))ᵀ = (U (ℓ + 1) * T'ᵀ) * (Vq (ℓ + 1))ᵀ := by
    rw [hT', Matrix.transpose_mul, Matrix.mul_assoc]
  have hA := decrease_of_min_right hf hlam hQV' hXf (hrun.argmin_U (ℓ + 1))
  have h1 := norm_tangentProj_sq_le (U (ℓ + 1)) hQV (G (Uh ℓ * (Vq ℓ)ᵀ))
  rw [hC, norm_zero, zero_pow two_ne_zero, zero_add] at h1
  have h2 := norm_tangentProj_sq_le (U (ℓ + 1)) hQV' (G (U (ℓ + 1) * (V (ℓ + 1))ᵀ))
  rw [hD, norm_zero, zero_pow two_ne_zero, add_zero] at h2
  have hg1 : ‖riemGrad G (Uh ℓ * (Vq ℓ)ᵀ)‖ ≤
      ‖tangentProj (U (ℓ + 1)) (Vq ℓ) (G (Uh ℓ * (Vq ℓ)ᵀ))‖ := by
    have e : Uh ℓ * (Vq ℓ)ᵀ = U (ℓ + 1) * T * (Vq ℓ)ᵀ := by rw [hT]
    rw [e]; exact norm_riemGrad_le_tangentProj G hQU hQV
  have hg2 : ‖riemGrad G (U (ℓ + 1) * (V (ℓ + 1))ᵀ)‖ ≤
      ‖tangentProj (U (ℓ + 1)) (Vq (ℓ + 1)) (G (U (ℓ + 1) * (V (ℓ + 1))ᵀ))‖ := by
    have e : U (ℓ + 1) * (V (ℓ + 1))ᵀ = U (ℓ + 1) * T'ᵀ * (Vq (ℓ + 1))ᵀ := hXf
    rw [e]; exact norm_riemGrad_le_tangentProj G hQU hQV'
  refine ⟨by gcongr, ?_, by gcongr, ?_⟩
  · exact (mul_le_mul_of_nonneg_left h1 hc.le).trans hB
  · exact (mul_le_mul_of_nonneg_left h2 hc.le).trans hA

/-- The first half-step of Algorithm 3 only sees the block of `T_{V₀}`.  (arXiv 2306.00897.) -/
theorem als_first_half_step (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hrun : IsALSRun f U V Vq Uh) :
    1 / (2 * lam) * ‖rightProj (Vq 0) (G (U 0 * (V 0)ᵀ))‖ ^ 2 ≤
      f (U 0 * (V 0)ᵀ) - f (Uh 0 * (Vq 0)ᵀ) := by
  obtain ⟨hQ, T, hT⟩ := hrun.qr_V 0
  have hX : U 0 * (V 0)ᵀ = (U 0 * Tᵀ) * (Vq 0)ᵀ := by
    rw [hT, Matrix.transpose_mul, Matrix.mul_assoc]
  exact decrease_of_min_right hf hlam hQ hX (hrun.argmin_U 0)

/-- **Corollary 3.9** (arXiv 2306.00897).  Let `f` be `λ`-smooth and bounded below and let
`X_ℓ = U_ℓ V_ℓᵀ` be the iterates of Algorithm 3.  Then `f(X_ℓ)` is decreasing and converges to some
`f∗ ≥ inf_{M_{≤k}} f`; `P_{U_ℓ,V_ℓ}(∇f(X_ℓ)) → 0` and `grad f(X_ℓ) → 0` (with `V_ℓ` replaced by its
QR-factor); every accumulation point `X∗` has `f(X∗) = f∗` and `grad f(X∗) = 0`; for every `j`,
`min {‖grad f(X_ℓ)‖, ‖grad f(X_{ℓ+1/2})‖ : ℓ ≤ j} ≤ (2 λ (f(X₀) - f∗) / (2 j + 1))^{1/2}`; and given
`ε > 0` some `ℓ ≤ ⌈λ (f(X₀) - f∗) ε⁻² - 1/2⌉` has `‖grad f(X_ℓ)‖ ≤ ε` or `‖grad f(X_{ℓ+1/2})‖ ≤ ε`.

The paper derives this from (3.29), which fails at `ℓ = 0` (`als_counterexample`); here the
`2 j + 1` half-steps after the first one are used, and the corollary is unaffected. -/
theorem als_convergence (hf : IsSmooth f G lam) (hlam : 0 < lam) (hbdd : BddBelow (range f))
    (hrun : IsALSRun f U V Vq Uh) :
    Antitone (fun ℓ => f (U ℓ * (V ℓ)ᵀ)) ∧
      ∃ fstar, Tendsto (fun ℓ => f (U ℓ * (V ℓ)ᵀ)) atTop (𝓝 fstar) ∧
      sInf (f '' {Y | Y.rank ≤ k}) ≤ fstar ∧
      Tendsto (fun ℓ => tangentProj (U ℓ) (Vq ℓ) (G (U ℓ * (V ℓ)ᵀ))) atTop (𝓝 0) ∧
      Tendsto (fun ℓ => riemGrad G (U ℓ * (V ℓ)ᵀ)) atTop (𝓝 0) ∧
      (∀ Xs, MapClusterPt Xs atTop (fun ℓ => U ℓ * (V ℓ)ᵀ) → f Xs = fstar ∧ riemGrad G Xs = 0) ∧
      (∀ j : ℕ, ∃ ℓ ≤ j,
        ‖riemGrad G (U ℓ * (V ℓ)ᵀ)‖ ≤ √(2 * lam * ((f (U 0 * (V 0)ᵀ) - fstar) / (2 * j + 1))) ∨
        ‖riemGrad G (Uh ℓ * (Vq ℓ)ᵀ)‖ ≤ √(2 * lam * ((f (U 0 * (V 0)ᵀ) - fstar) / (2 * j + 1)))) ∧
      ∀ ε > 0, ∃ ℓ ≤ ⌈lam * (f (U 0 * (V 0)ᵀ) - fstar) * (ε ^ 2)⁻¹ - 1 / 2⌉₊,
        ‖riemGrad G (U ℓ * (V ℓ)ᵀ)‖ ≤ ε ∨ ‖riemGrad G (Uh ℓ * (Vq ℓ)ᵀ)‖ ≤ ε := by
  have hhalf := als_half_step_decrease hf hlam hrun
  have hc : 0 < 1 / (2 * lam) := by positivity
  set X : ℕ → Matrix m n ℝ := fun ℓ => U ℓ * (V ℓ)ᵀ with hX
  set Xh : ℕ → Matrix m n ℝ := fun ℓ => Uh ℓ * (Vq ℓ)ᵀ with hXh
  set b : ℕ → ℝ := fun ℓ => ‖tangentProj (U (ℓ + 1)) (Vq ℓ) (G (Xh ℓ))‖ ^ 2 with hb
  set c : ℕ → ℝ := fun ℓ => ‖tangentProj (U (ℓ + 1)) (Vq (ℓ + 1)) (G (X (ℓ + 1)))‖ ^ 2 with hcdef
  have hbc0 : ∀ ℓ, 0 ≤ b ℓ ∧ 0 ≤ c ℓ := fun ℓ => ⟨sq_nonneg _, sq_nonneg _⟩
  have h1 : ∀ ℓ, f (X (ℓ + 1)) ≤ f (Xh ℓ) := fun ℓ => by
    have := (hhalf ℓ).2.1
    have h0 : 0 ≤ 1 / (2 * lam) * b ℓ := mul_nonneg hc.le (hbc0 ℓ).1
    change 1 / (2 * lam) * b ℓ ≤ f (Xh ℓ) - f (X (ℓ + 1)) at this
    linarith
  have h2 : ∀ ℓ, f (Xh (ℓ + 1)) ≤ f (X (ℓ + 1)) := fun ℓ => by
    have := (hhalf ℓ).2.2.2
    have h0 : 0 ≤ 1 / (2 * lam) * c ℓ := mul_nonneg hc.le (hbc0 ℓ).2
    change 1 / (2 * lam) * c ℓ ≤ f (X (ℓ + 1)) - f (Xh (ℓ + 1)) at this
    linarith
  have h3 : f (Xh 0) ≤ f (X 0) := by
    have := als_first_half_step hf hlam hrun
    have h0 : 0 ≤ 1 / (2 * lam) * ‖rightProj (Vq 0) (G (U 0 * (V 0)ᵀ))‖ ^ 2 :=
      mul_nonneg hc.le (sq_nonneg _)
    linarith
  have h4 : ∀ ℓ, f (Xh ℓ) ≤ f (X ℓ) := fun ℓ => by
    cases ℓ with
    | zero => exact h3
    | succ ℓ => exact h2 ℓ
  have hdec : ∀ ℓ, 1 / (2 * lam) * (b ℓ + c ℓ) ≤ f (Xh ℓ) - f (Xh (ℓ + 1)) := fun ℓ => by
    have e1 := (hhalf ℓ).2.1
    have e2 := (hhalf ℓ).2.2.2
    change 1 / (2 * lam) * b ℓ ≤ f (Xh ℓ) - f (X (ℓ + 1)) at e1
    change 1 / (2 * lam) * c ℓ ≤ f (X (ℓ + 1)) - f (Xh (ℓ + 1)) at e2
    rw [mul_add]; linarith
  obtain ⟨-, fstar, hlim, hlow, ha, -⟩ := rate_core (F := fun ℓ => f (Xh ℓ))
    (a := fun ℓ => b ℓ + c ℓ) hc (fun ℓ => add_nonneg (hbc0 ℓ).1 (hbc0 ℓ).2) hdec
    (hbdd.mono (range_comp_subset_range Xh f))
  have hXlim : Tendsto (fun ℓ => f (X ℓ)) atTop (𝓝 fstar) := by
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim.comp (tendsto_add_atTop_nat 1)) hlim
      (fun ℓ => h2 ℓ) (fun ℓ => h1 ℓ)
  have hanti : Antitone fun ℓ => f (X ℓ) := antitone_nat_of_succ_le fun ℓ =>
    (h1 ℓ).trans (h4 ℓ)
  have hlowX : ∀ ℓ, fstar ≤ f (X ℓ) := fun ℓ => (hlow ℓ).trans (h4 ℓ)
  have hcTo : Tendsto c atTop (𝓝 0) := squeeze_zero (fun ℓ => (hbc0 ℓ).2)
    (fun ℓ => le_add_of_nonneg_left (hbc0 ℓ).1) ha
  have hP : Tendsto (fun ℓ => tangentProj (U ℓ) (Vq ℓ) (G (X ℓ))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 (tendsto_zero_of_sq hcTo)
  have hgrad : Tendsto (fun ℓ => riemGrad G (X ℓ)) atTop (𝓝 0) := by
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    refine squeeze_zero_norm (a := fun ℓ => ‖tangentProj (U (ℓ + 1)) (Vq (ℓ + 1)) (G (X (ℓ + 1)))‖)
      (fun ℓ => ?_) (tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_zero_of_sq hcTo))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (le_of_mul_le_mul_left (hhalf ℓ).2.2.1 hc)
  have hrate : ∀ j : ℕ, ∃ ℓ ≤ j,
      ‖riemGrad G (X ℓ)‖ ≤ √(2 * lam * ((f (X 0) - fstar) / (2 * j + 1))) ∨
      ‖riemGrad G (Xh ℓ)‖ ≤ √(2 * lam * ((f (X 0) - fstar) / (2 * j + 1))) := by
    intro j
    by_contra hcon
    push Not at hcon
    set T := 2 * lam * ((f (X 0) - fstar) / (2 * j + 1)) with hT
    have hT1 : ∀ ℓ, ‖riemGrad G (Xh ℓ)‖ ^ 2 ≤ 2 * lam * (f (Xh ℓ) - f (X (ℓ + 1))) := fun ℓ => by
      have e := (hhalf ℓ).1.trans (hhalf ℓ).2.1
      change 1 / (2 * lam) * ‖riemGrad G (Xh ℓ)‖ ^ 2 ≤ f (Xh ℓ) - f (X (ℓ + 1)) at e
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at e
      linarith
    have hT2 : ∀ ℓ, ‖riemGrad G (X (ℓ + 1))‖ ^ 2 ≤ 2 * lam * (f (X (ℓ + 1)) - f (Xh (ℓ + 1))) :=
      fun ℓ => by
        have e := (hhalf ℓ).2.2.1.trans (hhalf ℓ).2.2.2
        change 1 / (2 * lam) * ‖riemGrad G (X (ℓ + 1))‖ ^ 2 ≤ f (X (ℓ + 1)) - f (Xh (ℓ + 1)) at e
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at e
        linarith
    have hind : ∀ i ≤ j, (2 * (i : ℝ) + 1) * T < 2 * lam * (f (Xh 0) - f (X (i + 1))) := by
      intro i
      induction i with
      | zero =>
        intro _
        have h5 := Real.lt_sq_of_sqrt_lt (hcon 0 (Nat.zero_le _)).2
        have h6 := hT1 0
        norm_num
        linarith
      | succ i ih =>
        intro hi
        have h5 := Real.lt_sq_of_sqrt_lt (hcon (i + 1) hi).1
        have h6 := Real.lt_sq_of_sqrt_lt (hcon (i + 1) hi).2
        have h7 := hT2 i
        have h8 := hT1 (i + 1)
        have h9 := ih (by omega)
        push_cast
        nlinarith
    have hfin := hind j le_rfl
    have hj : (0 : ℝ) < 2 * j + 1 := by positivity
    have e : (2 * (j : ℝ) + 1) * T = 2 * lam * (f (X 0) - fstar) := by
      rw [hT]; field_simp
    rw [e] at hfin
    have h5 := hlow 0
    have h6 := hlowX (j + 1)
    have h7 := h3
    nlinarith
  refine ⟨hanti, fstar, hXlim, ?_, hP, hgrad, fun Xs hXs => cluster_spec hf hXlim hgrad hXs, hrate,
    fun ε hε => ?_⟩
  · refine ge_of_tendsto' hXlim fun ℓ => ?_
    refine csInf_le (hbdd.mono (image_subset_range _ _)) ⟨X ℓ, ?_, rfl⟩
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using (U ℓ).rank_le_card_width)
  · set j := ⌈lam * (f (X 0) - fstar) * (ε ^ 2)⁻¹ - 1 / 2⌉₊ with hj
    obtain ⟨ℓ, hℓ, hb'⟩ := hrate j
    have hle : √(2 * lam * ((f (X 0) - fstar) / (2 * j + 1))) ≤ ε := by
      refine Real.sqrt_le_iff.2 ⟨hε.le, ?_⟩
      have h5 := Nat.le_ceil (lam * (f (X 0) - fstar) * (ε ^ 2)⁻¹ - 1 / 2)
      rw [← hj] at h5
      have h6 : lam * (f (X 0) - fstar) * (ε ^ 2)⁻¹ ≤ (j : ℝ) + 1 / 2 := by linarith
      have h7 : lam * (f (X 0) - fstar) ≤ ((j : ℝ) + 1 / 2) * ε ^ 2 := by
        calc lam * (f (X 0) - fstar) = lam * (f (X 0) - fstar) * (ε ^ 2)⁻¹ * ε ^ 2 := by
              field_simp
          _ ≤ _ := by gcongr
      have hj0 : (0 : ℝ) < 2 * j + 1 := by positivity
      rw [mul_div_assoc', div_le_iff₀ hj0]
      linarith
    exact ⟨ℓ, hℓ, hb'.imp (fun h => h.trans hle) (fun h => h.trans hle)⟩

end ALS

/-! ### Estimate (3.29) fails for the first half-step -/

section Counterexample

/-- The cost function of `als_counterexample`: `f(X) = (X₀₁ - 1)² / 2`. -/
noncomputable def cexF (X : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (X 0 1 - 1) ^ 2 / 2

/-- The gradient of `cexF`. -/
noncomputable def cexG (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (X 0 1 - 1) • Matrix.single 0 1 (1 : ℝ)

/-- The entry `Z₀₁` as an inner product. -/
lemma inner_single_cex (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    ⟪Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℝ), Z⟫ = Z 0 1 := by
  simp [Frobenius.inner_def, Fin.sum_univ_two, Matrix.single_apply]

/-- `cexF` is `1`-smooth.  (arXiv 2306.00897.) -/
theorem cex_isSmooth : IsSmooth cexF cexG 1 := by
  set E : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℝ) with hE
  refine ⟨fun X => ?_, fun X Y => ?_⟩
  · have h1 : HasFDerivAt (fun Z : Matrix (Fin 2) (Fin 2) ℝ => ⟪E, Z⟫) (innerSL ℝ E) X :=
      (innerSL ℝ E).hasFDerivAt
    have h2 := ((h1.sub_const 1).pow 2).const_mul (1 / 2 : ℝ)
    have hfun : cexF = fun Z => (1 / 2 : ℝ) * (⟪E, Z⟫ - 1) ^ 2 := by
      funext Z
      rw [hE, inner_single_cex, cexF]
      ring
    rw [hfun]
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    have e : ⟪cexG X, Z⟫ = (X 0 1 - 1) * Z 0 1 := by
      rw [cexG, inner_smul_left, inner_single_cex]
      rfl
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, e, hE, inner_single_cex]
    norm_num
    ring
  · have hEn : ‖E‖ = 1 := by
      have h := real_inner_self_eq_norm_sq E
      rw [hE, inner_single_cex] at h
      have h' : ‖E‖ ^ 2 = 1 := by rw [hE, ← h]; simp
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'
    have e : cexG X - cexG Y = (X 0 1 - Y 0 1) • E := by
      simp only [cexG, ← hE]
      rw [← sub_smul]
      congr 1
      ring
    rw [e, norm_smul, hEn, mul_one, one_mul, Real.norm_eq_abs]
    exact Frobenius.abs_apply_le_norm (X - Y) 0 1

/-- `e₀ ∈ ℝ^{2×1}`. -/
def cexE₀ : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => if i = 0 then 1 else 0

/-- `e₁ ∈ ℝ^{2×1}`. -/
def cexE₁ : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => if i = 1 then 1 else 0

/-- `e₀` has norm one. -/
lemma cexE₀_orth : cexE₀ᵀ * cexE₀ = 1 := by
  ext i j
  rw [Subsingleton.elim j i]
  simp [Matrix.mul_apply, cexE₀]

/-- `e₁` has norm one. -/
lemma cexE₁_orth : cexE₁ᵀ * cexE₁ = 1 := by
  ext i j
  rw [Subsingleton.elim j i]
  simp [Matrix.mul_apply, cexE₁]

/-- `f` is constant on `T_{e₀}`, the matrices with vanishing second column. -/
lemma cexF_mul_E₀ (W : Matrix (Fin 2) (Fin 1) ℝ) : cexF (W * cexE₀ᵀ) = 1 / 2 := by
  simp [cexF, Matrix.mul_apply, cexE₀]

/-- `f` is constant on `T_{e₁}`, the matrices with vanishing first row. -/
lemma cexF_E₁_mul (W : Matrix (Fin 2) (Fin 1) ℝ) : cexF (cexE₁ * Wᵀ) = 1 / 2 := by
  simp [cexF, Matrix.mul_apply, cexE₁]

/-- **Estimate (3.29) fails at `ℓ = 0`, and so does the min-max estimate after Corollary 3.9**
(arXiv 2306.00897).  For `f(X) = (X₀₁ - 1)² / 2` (`1`-smooth, convex, bounded below) on `2 × 2`
matrices and `k = 1`, start from `X₀ = e₀ e₀ᵀ`.  Algorithm 3 may stay at `f = 1/2`: `e₁ e₀ᵀ` is a
minimizer on `T_{V₀}` and on `T_{U₁}`, so `X_ℓ = X_{ℓ+1/2} = e₁ e₀ᵀ` from then on.  Yet
`grad f(X₀) ≠ 0`.  Hence `f(X̃₀) - f(X̃₁) = 0 < ‖grad f(X̃₀)‖² / (2 λ)`, and for `j = 0` the
estimate `max {‖grad f(X₀)‖, ‖grad f(X_{1/2})‖} ≤ (2 λ (f(X₀) - f∗))^{1/2} = 0` fails.  The paper
only justifies `P_{2,ℓ} = 0` for `ℓ ≥ 1`.  Corollary 3.9 itself is correct (`als_convergence`). -/
theorem als_counterexample :
    ∃ (U V Vq Uh : ℕ → Matrix (Fin 2) (Fin 1) ℝ), IsALSRun cexF U V Vq Uh ∧
      (∀ ℓ, cexF (U ℓ * (V ℓ)ᵀ) = 1 / 2) ∧
      ¬ (1 / (2 * 1) * ‖riemGrad cexG (U 0 * (V 0)ᵀ)‖ ^ 2 ≤
        cexF (U 0 * (V 0)ᵀ) - cexF (Uh 0 * (Vq 0)ᵀ)) ∧
      ¬ (max ‖riemGrad cexG (U 0 * (V 0)ᵀ)‖ ‖riemGrad cexG (Uh 0 * (Vq 0)ᵀ)‖ ≤
        √(2 * 1 * ((cexF (U 0 * (V 0)ᵀ) - 1 / 2) / (0 + 1)))) := by
  have hne : riemGrad cexG (cexE₀ * cexE₀ᵀ) ≠ 0 := by
    intro h
    obtain ⟨h1, -⟩ := (riemGrad_eq_zero_iff cexG _).1 h
    have h2 := congrFun (congrFun h1 0) 1
    simp [cexG, Matrix.mul_apply, cexE₀, Matrix.single_apply] at h2
  have hpos : 0 < ‖riemGrad cexG (cexE₀ * cexE₀ᵀ)‖ := norm_pos_iff.2 hne
  refine ⟨fun ℓ => if ℓ = 0 then cexE₀ else cexE₁, fun _ => cexE₀, fun _ => cexE₀,
    fun _ => cexE₁, ⟨fun _ => ⟨cexE₀_orth, 1, by simp⟩, fun ℓ W => ?_, fun _ => ⟨?_, 1, ?_⟩,
      fun ℓ W => ?_⟩, fun ℓ => ?_, ?_, ?_⟩
  · simp only [cexF_mul_E₀, le_refl]
  · simpa using cexE₁_orth
  · simp
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, cexF_E₁_mul, le_refl]
  · simp only [cexF_mul_E₀]
  · change ¬ (1 / (2 * 1) * ‖riemGrad cexG (cexE₀ * cexE₀ᵀ)‖ ^ 2 ≤
      cexF (cexE₀ * cexE₀ᵀ) - cexF (cexE₁ * cexE₀ᵀ))
    rw [cexF_mul_E₀, cexF_mul_E₀, sub_self, not_le]
    positivity
  · change ¬ (max ‖riemGrad cexG (cexE₀ * cexE₀ᵀ)‖ ‖riemGrad cexG (cexE₁ * cexE₀ᵀ)‖ ≤
      √(2 * 1 * ((cexF (cexE₀ * cexE₀ᵀ) - 1 / 2) / (0 + 1))))
    have h0 : √(2 * 1 * (((1 / 2 : ℝ) - 1 / 2) / (0 + 1))) = 0 := by norm_num
    rw [cexF_mul_E₀, h0, not_le]
    exact lt_max_of_lt_left hpos

end Counterexample

/-! ### Local analysis at a critical point of rank `k` -/

section Hessian

/-- The **Riemannian Hessian** of `f|M_k` at `X = U S Vᵀ` of rank `k`, as a quadratic form on
`T_X M_k`, for the embedded metric: with `g = ∇f(X)` and `H = ∇²f(X)`,
`⟪H ξ, ξ⟫ + 2 ⟪g, (I - U Uᵀ) ξ V S⁻¹ Uᵀ ξ (I - V Vᵀ)⟫`,
the second term being the Weingarten term of `M_k`.  That this is the Hessian of `f|M_k` at a
critical point is checked by `taylor_on_rank_le`, which says that it is the second-order term of `f`
along `M_{≤k}`.  The paper defines it through [2, Chapter 5] of its bibliography, and does not need
a formula. -/
noncomputable def riemHess (g : Matrix m n ℝ) (H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
    (U : Matrix m (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ) (V : Matrix n (Fin k) ℝ)
    (ξ : Matrix m n ℝ) : ℝ :=
  ⟪H ξ, ξ⟫ + 2 * ⟪g, normal (leftProj U) (rightProj V) (ξ * V * S⁻¹ * Uᵀ * ξ)⟫

variable {U : Matrix m (Fin k) ℝ} {S : Matrix (Fin k) (Fin k) ℝ} {V : Matrix n (Fin k) ℝ}

/-- The normal projector kills `U Z`. -/
lemma normal_mul_left (hU : Uᵀ * U = 1) (V : Matrix n (Fin k) ℝ) (Z : Matrix (Fin k) n ℝ) :
    normal (leftProj U) (rightProj V) (U * Z) = 0 := by
  have h := tangent_apply_add_normal_apply (leftProj U) (rightProj V) (U * Z)
  have h2 : tangent (leftProj U) (rightProj V) (U * Z) = U * Z := tangentProj_mul_left hU V Z
  rw [h2] at h
  simpa using h

/-- The normal projector kills `Z Vᵀ`. -/
lemma normal_mul_right (U : Matrix m (Fin k) ℝ) (hV : Vᵀ * V = 1) (Z : Matrix m (Fin k) ℝ) :
    normal (leftProj U) (rightProj V) (Z * Vᵀ) = 0 := by
  have h := tangent_apply_add_normal_apply (leftProj U) (rightProj V) (Z * Vᵀ)
  have h2 : tangent (leftProj U) (rightProj V) (Z * Vᵀ) = Z * Vᵀ :=
    tangentProj_mul_transpose U hV Z
  rw [h2] at h
  simpa using h

/-- `P_{U,V}(d) V = d V`. -/
lemma tangentProj_mul_self (hV : Vᵀ * V = 1) (U : Matrix m (Fin k) ℝ) (d : Matrix m n ℝ) :
    tangentProj U V d * V = d * V := by
  have e : U * Uᵀ * d * V * Vᵀ * V = U * Uᵀ * d * V := by
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  have e2 : d * V * Vᵀ * V = d * V := by
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [tangentProj_apply, Matrix.sub_mul, Matrix.add_mul, e, e2]
  abel

/-- `Uᵀ P_{U,V}(d) = Uᵀ d`. -/
lemma transpose_mul_tangentProj (hU : Uᵀ * U = 1) (V : Matrix n (Fin k) ℝ) (d : Matrix m n ℝ) :
    Uᵀ * tangentProj U V d = Uᵀ * d := by
  have e : Uᵀ * (U * Uᵀ * d) = Uᵀ * d := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have e2 : Uᵀ * (U * Uᵀ * d * V * Vᵀ) = Uᵀ * d * V * Vᵀ := by
    rw [show U * Uᵀ * d * V * Vᵀ = U * (Uᵀ * d * V * Vᵀ) by simp only [Matrix.mul_assoc],
      ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have e3 : Uᵀ * (d * V * Vᵀ) = Uᵀ * d * V * Vᵀ := by simp only [Matrix.mul_assoc]
  rw [tangentProj_apply, Matrix.mul_sub, Matrix.mul_add, e, e2, e3]
  abel

/-- A critical point of rank `k`: `Uᵀ ∇f(X) = 0` and `∇f(X) V = 0`. -/
lemma crit_factor {G : Matrix m n ℝ → Matrix m n ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) (hc : riemGrad G (U * S * Vᵀ) = 0) :
    Uᵀ * G (U * S * Vᵀ) = 0 ∧ G (U * S * Vᵀ) * V = 0 := by
  obtain ⟨h1, h2⟩ := (riemGrad_eq_zero_iff G _).1 hc
  set g := G (U * S * Vᵀ)
  have hSt : IsUnit (Sᵀ).det := by rwa [Matrix.det_transpose]
  have ht : (U * S * Vᵀ)ᵀ = V * Sᵀ * Uᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [ht] at h1 h2
  constructor
  · have h3 : Sᵀ * (Uᵀ * g) = 0 := by
      have := congrArg (fun Z => Vᵀ * Z) h1
      simp only [Matrix.mul_zero] at this
      rw [← this]
      calc Sᵀ * (Uᵀ * g) = (Vᵀ * V) * Sᵀ * (Uᵀ * g) := by rw [hV, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    have h4 := congrArg (fun Z => (Sᵀ)⁻¹ * Z) h3
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSt] using h4
  · have h3 : (g * V) * Sᵀ = 0 := by
      have := congrArg (fun Z => Z * U) h2
      simp only [Matrix.zero_mul] at this
      rw [← this]
      calc (g * V) * Sᵀ = (g * V) * Sᵀ * (Uᵀ * U) := by rw [hU, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have h4 := congrArg (fun Z => Z * (Sᵀ)⁻¹) h3
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSt] using h4

/-- With `Uᵀ g = 0`, `g V = 0`, the matrix `g` is orthogonal to `T_{U,V}`. -/
lemma inner_tangentProj_eq_zero {g : Matrix m n ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (h1 : Uᵀ * g = 0) (h2 : g * V = 0) (Z : Matrix m n ℝ) : ⟪g, tangentProj U V Z⟫ = 0 := by
  have hT : tangentProj U V g = 0 := by
    have e1 : U * Uᵀ * g = 0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
    have e2 : g * V * Vᵀ = 0 := by rw [h2, Matrix.zero_mul]
    rw [tangentProj_apply, e1, e2, Matrix.zero_mul, Matrix.zero_mul, add_zero, sub_zero]
  rw [← (isOrthProj_tangentProj hU hV).symm, hT, inner_zero_left]

/-- The rank identity behind the second fundamental form: if `rank X ≤ k` and `A = Uᵀ X V` is
invertible (`k × k`), then `X = X V A⁻¹ Uᵀ X` (Wedderburn rank reduction).  (arXiv 2306.00897.) -/
theorem eq_mul_inv_mul {X : Matrix m n ℝ} (hrank : X.rank ≤ k)
    (hA : IsUnit (Uᵀ * X * V).det) :
    X = X * V * (Uᵀ * X * V)⁻¹ * Uᵀ * X := by
  classical
  set A := Uᵀ * X * V with hAdef
  set K := X * V with hK
  have hkA : A.rank = k := by
    have := Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 hA)
    simpa using this
  have hKk : k ≤ K.rank := by
    have h1 : A = Uᵀ * K := by rw [hAdef, hK, Matrix.mul_assoc]
    have h2 : A.rank ≤ K.rank := by rw [h1]; exact Matrix.rank_mul_le_right _ _
    omega
  have hle : LinearMap.range K.mulVecLin ≤ LinearMap.range X.mulVecLin := by
    rw [hK, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hrange : LinearMap.range K.mulVecLin = LinearMap.range X.mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    change X.rank ≤ K.rank
    omega
  have hcol : ∀ j, ∃ w : Fin k → ℝ, K.mulVec w = X.mulVec (Pi.single j 1) := fun j => by
    have h : X.mulVec (Pi.single j 1) ∈ LinearMap.range K.mulVecLin := by
      rw [hrange]; exact ⟨_, rfl⟩
    exact h
  choose w hw using hcol
  have hX : X = K * Matrix.of fun i j => w j i := by
    ext i j
    have h := congrFun (hw j) i
    rw [Matrix.mulVec_single_one] at h
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h.symm
  set W : Matrix (Fin k) n ℝ := Matrix.of fun i j => w j i with hW
  have hUX : Uᵀ * X = A * W := by
    calc Uᵀ * X = Uᵀ * (K * W) := by rw [← hX]
      _ = A * W := by rw [hAdef, hK]; simp only [Matrix.mul_assoc]
  have hWeq : W = A⁻¹ * (Uᵀ * X) := by
    rw [hUX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  calc X = K * W := hX
    _ = X * V * A⁻¹ * Uᵀ * X := by rw [hWeq]; simp only [hK, Matrix.mul_assoc]

/-- **Second-order Taylor expansion** at a point where the gradient is differentiable.
(arXiv 2306.00897.) -/
theorem taylor_second_order {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ}
    (hgrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X) {Xs : Matrix m n ℝ}
    {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hH : HasFDerivAt G H Xs) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X in 𝓝 Xs, |f X - f Xs - ⟪G Xs, X - Xs⟫ - ⟪H (X - Xs), X - Xs⟫ / 2| ≤
      η * ‖X - Xs‖ ^ 2 := by
  have h := hH.isLittleO.def hη
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 h
  filter_upwards [Metric.ball_mem_nhds Xs hr] with X hX
  set d := X - Xs with hd
  have hdr : ‖d‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hX
  let ψ : ℝ → ℝ := fun t => f (Xs + t • d) - t * ⟪G Xs, d⟫ - t ^ 2 / 2 * ⟪H d, d⟫
  let ψ' : ℝ → ℝ := fun t => ⟪G (Xs + t • d) - G Xs - t • H d, d⟫
  have hψ : ∀ t, HasDerivAt ψ (ψ' t) t := fun t => by
    have h1 := hasDerivAt_loss_line hgrad Xs d t
    have h2 := (hasDerivAt_id' t).mul_const ⟪G Xs, d⟫
    have h3 := ((hasDerivAt_pow 2 t).div_const 2).mul_const ⟪H d, d⟫
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    simp only [ψ', inner_sub_left, inner_smul_left, conj_trivial]
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖ψ' t‖ ≤ η * ‖d‖ ^ 2 := fun t ht => by
    have ht0 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
    have hnorm : ‖t • d‖ ≤ ‖d‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) ht0
    have hin : Xs + t • d ∈ Metric.ball Xs r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hnorm.trans_lt hdr
    have h1 := hball _ hin
    rw [add_sub_cancel_left, map_smul] at h1
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖G (Xs + t • d) - G Xs - t • H d‖ * ‖d‖ ≤ η * ‖t • d‖ * ‖d‖ := by gcongr
      _ ≤ η * ‖d‖ * ‖d‖ := by gcongr
      _ = η * ‖d‖ ^ 2 := by ring
  have h2 := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
    (fun t _ => (hψ t).hasDerivWithinAt) hbound 1 (right_mem_Icc.2 zero_le_one)
  have e : ψ 1 - ψ 0 = f X - f Xs - ⟪G Xs, d⟫ - ⟪H d, d⟫ / 2 := by
    simp only [ψ, one_smul, zero_smul, add_zero, hd, add_sub_cancel]
    ring
  rw [e, Real.norm_eq_abs, sub_zero, mul_one] at h2
  exact h2

/-- The triangle inequality in `local_expansion_value`. -/
lemma abs_expansion_aux {a gd Hdd Hxx x y gn gb E1 E2 E3 E4 : ℝ}
    (h1 : |a - gd - Hdd / 2| ≤ E1) (hgd : gd = gn) (h2 : |gn - gb| ≤ E2)
    (hH : Hdd - Hxx = x + y) (h3 : |x| ≤ E3) (h4 : |y| ≤ E4) :
    |a - (Hxx + 2 * gb) / 2| ≤ E1 + E2 + (E3 + E4) / 2 := by
  subst hgd
  obtain ⟨t1, t2⟩ := abs_le.1 h1
  obtain ⟨t3, t4⟩ := abs_le.1 h2
  obtain ⟨t5, t6⟩ := abs_le.1 h3
  obtain ⟨t7, t8⟩ := abs_le.1 h4
  rw [abs_le]
  constructor <;> linarith

/-- The normal part of `d = X - X∗`, for `X` of rank `≤ k` near `X∗ = U S Vᵀ`, is quadratic in `d`:
`(I - U Uᵀ) d (I - V Vᵀ) = (I - U Uᵀ) d V A⁻¹ Uᵀ d (I - V Vᵀ)` with `A = Uᵀ X V`.
(arXiv 2306.00897.) -/
theorem normal_sub_bounds {X : Matrix m n ℝ} {ζ K : ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hrank : X.rank ≤ k) (hA : IsUnit (Uᵀ * X * V).det)
    (hζ : ‖(Uᵀ * X * V)⁻¹ - S⁻¹‖ ≤ ζ) (hK1 : ‖(Uᵀ * X * V)⁻¹‖ ≤ K) :
    ‖normal (leftProj U) (rightProj V) (X - U * S * Vᵀ)‖ ≤ K * ‖X - U * S * Vᵀ‖ ^ 2 ∧
      ‖normal (leftProj U) (rightProj V) (X - U * S * Vᵀ) -
        normal (leftProj U) (rightProj V)
          (tangentProj U V (X - U * S * Vᵀ) * V * S⁻¹ * Uᵀ * tangentProj U V (X - U * S * Vᵀ))‖ ≤
        ζ * ‖X - U * S * Vᵀ‖ ^ 2 := by
  classical
  set Xs := U * S * Vᵀ with hXs
  set d := X - Xs with hd
  set e := ‖d‖ with he
  set Ai := (Uᵀ * X * V)⁻¹ with hAi
  set N := normal (leftProj U) (rightProj V) with hN
  set ξ := tangentProj U V d with hξ
  have hNorth : IsOrthProj N := isOrthProj_normal_leftProj_rightProj hU hV
  have hNXs : ∀ Z : Matrix n n ℝ, N (Xs * Z) = 0 := fun Z => by
    rw [show Xs * Z = U * (S * Vᵀ * Z) by rw [hXs]; simp only [Matrix.mul_assoc]]
    exact normal_mul_left hU V _
  have hNXs' : ∀ Z : Matrix m m ℝ, N (Z * Xs) = 0 := fun Z => by
    rw [show Z * Xs = (Z * U * S) * Vᵀ by rw [hXs]; simp only [Matrix.mul_assoc]]
    exact normal_mul_right U hV _
  have hschur : N d = N (d * V * Ai * Uᵀ * d) := by
    have hX0 : N Xs = 0 := by simpa using hNXs 1
    have h3 : N X = N (d * V * Ai * Uᵀ * d) := by
      set W := V * Ai * Uᵀ with hW
      have e1 : X = X * W * X := by
        calc X = X * V * Ai * Uᵀ * X := eq_mul_inv_mul hrank hA
          _ = X * W * X := by rw [hW]; simp only [Matrix.mul_assoc]
      have e2 : X * W * X = Xs * (W * X) + d * W * Xs + d * W * d := by
        have hXeq : Xs + d = X := by rw [hd]; abel
        calc X * W * X = (Xs + d) * W * (Xs + d) := by rw [hXeq]
          _ = Xs * (W * Xs + W * d) + d * W * Xs + d * W * d := by
              simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
              abel
          _ = _ := by rw [← Matrix.mul_add W, hXeq]
      calc N X = N (X * W * X) := by rw [← e1]
        _ = N (d * W * d) := by
            rw [e2, map_add, map_add, hNXs, hNXs', zero_add, zero_add]
        _ = _ := by rw [hW]; simp only [Matrix.mul_assoc]
    rw [← h3, hd, map_sub, hX0, sub_zero]
  have hξV : ξ * V = d * V := tangentProj_mul_self hV U d
  have hUξ : Uᵀ * ξ = Uᵀ * d := transpose_mul_tangentProj hU V d
  have hb : ξ * V * S⁻¹ * Uᵀ * ξ = d * V * S⁻¹ * Uᵀ * d := by
    calc ξ * V * S⁻¹ * Uᵀ * ξ = (ξ * V) * S⁻¹ * (Uᵀ * ξ) := by simp only [Matrix.mul_assoc]
      _ = (d * V) * S⁻¹ * (Uᵀ * d) := by rw [hξV, hUξ]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hdV : ‖d * V‖ ≤ e := norm_mul_le_of_orthonormal hV d
  have hUd : ‖Uᵀ * d‖ ≤ e := norm_transpose_mul_le hU d
  have hsand : ∀ W : Matrix (Fin k) (Fin k) ℝ, ‖d * V * W * Uᵀ * d‖ ≤ ‖W‖ * e ^ 2 := fun W => by
    calc ‖d * V * W * Uᵀ * d‖ = ‖(d * V) * W * (Uᵀ * d)‖ := by simp only [Matrix.mul_assoc]
      _ ≤ ‖(d * V) * W‖ * ‖Uᵀ * d‖ := Frobenius.norm_mul_le _ _
      _ ≤ ‖d * V‖ * ‖W‖ * ‖Uᵀ * d‖ := by gcongr; exact Frobenius.norm_mul_le _ _
      _ ≤ e * ‖W‖ * e := by gcongr
      _ = _ := by ring
  constructor
  · rw [hschur]
    exact (hNorth.norm_le _).trans ((hsand Ai).trans (by gcongr))
  · rw [hschur, hb, ← map_sub]
    have e3 : d * V * Ai * Uᵀ * d - d * V * S⁻¹ * Uᵀ * d = d * V * (Ai - S⁻¹) * Uᵀ * d := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [e3]
    exact (hNorth.norm_le _).trans ((hsand _).trans (by gcongr))

/-- Value expansion: `f(X) - f(X∗) = ½ H(ξ, ξ) + o(‖d‖²)`, and `‖d‖² ≈ ‖ξ‖²`, in deterministic form
at a fixed `X` of rank `≤ k`.  (arXiv 2306.00897.) -/
theorem local_expansion_value {g X : Matrix m n ℝ} {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    {a c ζ K : ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (h1 : Uᵀ * g = 0) (h2 : g * V = 0)
    (hNle : ‖normal (leftProj U) (rightProj V) (X - U * S * Vᵀ)‖ ≤ K * ‖X - U * S * Vᵀ‖ ^ 2)
    (hNb : ‖normal (leftProj U) (rightProj V) (X - U * S * Vᵀ) -
        normal (leftProj U) (rightProj V)
          (tangentProj U V (X - U * S * Vᵀ) * V * S⁻¹ * Uᵀ * tangentProj U V (X - U * S * Vᵀ))‖ ≤
        ζ * ‖X - U * S * Vᵀ‖ ^ 2)
    (hT : |a - ⟪g, X - U * S * Vᵀ⟫ - ⟪H (X - U * S * Vᵀ), X - U * S * Vᵀ⟫ / 2| ≤
      c * ‖X - U * S * Vᵀ‖ ^ 2) :
    |a - riemHess g H U S V (tangentProj U V (X - U * S * Vᵀ)) / 2| ≤
        (c + ‖g‖ * ζ + ‖H‖ * K * ‖X - U * S * Vᵀ‖) * ‖X - U * S * Vᵀ‖ ^ 2 ∧
      ‖X - U * S * Vᵀ‖ ^ 2 ≤
        ‖tangentProj U V (X - U * S * Vᵀ)‖ ^ 2 + K ^ 2 * ‖X - U * S * Vᵀ‖ ^ 4 := by
  set d := X - U * S * Vᵀ with hd
  set e := ‖d‖ with he
  set N := normal (leftProj U) (rightProj V) with hN
  set ξ := tangentProj U V d with hξ
  set b := N (ξ * V * S⁻¹ * Uᵀ * ξ) with hbdef
  have hTorth : IsOrthProj (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    isOrthProj_tangentProj hU hV
  have hsplit : ξ + N d = d := tangent_apply_add_normal_apply _ _ d
  have he0 : 0 ≤ e := norm_nonneg _
  have hξe : ‖ξ‖ ≤ e := hTorth.norm_le d
  have hgξ : ⟪g, ξ⟫ = 0 := inner_tangentProj_eq_zero hU hV h1 h2 d
  have hgd : ⟪g, d⟫ = ⟪g, N d⟫ := by
    conv_lhs => rw [← hsplit]
    rw [inner_add_right, hgξ, zero_add]
  have hgb : |⟪g, N d⟫ - ⟪g, b⟫| ≤ ‖g‖ * (ζ * e ^ 2) := by
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans (by gcongr)
  have hHd : H d = H ξ + H (N d) := by rw [← map_add, hsplit]
  have hHexp : ⟪H d, d⟫ - ⟪H ξ, ξ⟫ = ⟪H (N d), d⟫ + ⟪H ξ, N d⟫ := by
    have e4 : ⟪H ξ, d⟫ = ⟪H ξ, ξ⟫ + ⟪H ξ, N d⟫ := by
      conv_lhs => rw [← hsplit]
      rw [inner_add_right]
    rw [hHd, inner_add_left, e4]
    ring
  have hHN : ‖H (N d)‖ ≤ ‖H‖ * (K * e ^ 2) := (H.le_opNorm _).trans (by gcongr)
  have hHξ : ‖H ξ‖ ≤ ‖H‖ * e := (H.le_opNorm _).trans (by gcongr)
  have hH1 : |⟪H (N d), d⟫| ≤ ‖H‖ * (K * e ^ 2) * e :=
    (abs_real_inner_le_norm _ _).trans (by gcongr)
  have hH2 : |⟪H ξ, N d⟫| ≤ ‖H‖ * e * (K * e ^ 2) :=
    (abs_real_inner_le_norm _ _).trans (by gcongr)
  have hK0 : 0 ≤ K * e ^ 2 := (norm_nonneg _).trans hNle
  constructor
  · have h3 := abs_expansion_aux hT hgd hgb hHexp hH1 hH2
    have e5 : c * e ^ 2 + ‖g‖ * (ζ * e ^ 2) + (‖H‖ * (K * e ^ 2) * e + ‖H‖ * e * (K * e ^ 2)) / 2 =
        (c + ‖g‖ * ζ + ‖H‖ * K * e) * e ^ 2 := by ring
    rw [e5] at h3
    exact h3
  · have h3 := hTorth.norm_sq_add d
    have h4 : d - ξ = N d := sub_eq_of_eq_add' hsplit.symm
    rw [← hξ, h4] at h3
    have h5 : ‖N d‖ ^ 2 ≤ (K * e ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hNle 2
    have h6 : (K * e ^ 2) ^ 2 = K ^ 2 * e ^ 4 := by ring
    rw [h6] at h5
    rw [he, ← h3]
    linarith

/-- The triangle inequality in `local_expansion_tangent`. -/
lemma abs_tangent_aux {gXτ gτ Hdτ rτ Hxx gn gb t2 t3 E2 E3 E4 E5 : ℝ}
    (hsplit : gXτ = gτ + Hdτ + rτ) (hg : gτ = 2 * gn) (hH : Hdτ = Hxx + t2 + t3)
    (h1 : |gn - gb| ≤ E2) (h2 : |t2| ≤ E3) (h3 : |t3| ≤ E4) (h4 : |rτ| ≤ E5) :
    |gXτ - (Hxx + 2 * gb)| ≤ 2 * E2 + E3 + E4 + E5 := by
  subst hsplit hg hH
  obtain ⟨t11, t12⟩ := abs_le.1 h1
  obtain ⟨t21, t22⟩ := abs_le.1 h2
  obtain ⟨t31, t32⟩ := abs_le.1 h3
  obtain ⟨t41, t42⟩ := abs_le.1 h4
  rw [abs_le]
  constructor <;> linarith

/-- The tangent vector `τ` at `X` used to bound `‖grad f(X)‖` from below: `τ = ξ + 2 N d + O(‖d‖²)`,
where the last term has the form `U Z` and `ξ + 2 N d` is the velocity at `X` of a curve on `M_k`
through `X∗`.  (arXiv 2306.00897.) -/
theorem local_expansion_tangent {g gX X : Matrix m n ℝ} {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    {c ζ K : ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (h1 : Uᵀ * g = 0) (h2 : g * V = 0) (hK2 : ‖S⁻¹‖ ≤ K)
    (hNle : ‖normal (leftProj U) (rightProj V) (X - U * S * Vᵀ)‖ ≤ K * ‖X - U * S * Vᵀ‖ ^ 2)
    (hNb : ‖normal (leftProj U) (rightProj V) (X - U * S * Vᵀ) -
        normal (leftProj U) (rightProj V)
          (tangentProj U V (X - U * S * Vᵀ) * V * S⁻¹ * Uᵀ * tangentProj U V (X - U * S * Vᵀ))‖ ≤
        ζ * ‖X - U * S * Vᵀ‖ ^ 2)
    (hr : ‖gX - g - H (X - U * S * Vᵀ)‖ ≤ c * ‖X - U * S * Vᵀ‖) (hc : 0 ≤ c) :
    ∃ τ ∈ tangentSpaceAt X, ‖τ‖ ≤ ‖X - U * S * Vᵀ‖ + 3 * K * ‖X - U * S * Vᵀ‖ ^ 2 ∧
      |⟪gX, τ⟫ - riemHess g H U S V (tangentProj U V (X - U * S * Vᵀ))| ≤
        (2 * ‖g‖ * ζ + 4 * ‖H‖ * K * ‖X - U * S * Vᵀ‖ +
          c * (1 + 3 * K * ‖X - U * S * Vᵀ‖)) * ‖X - U * S * Vᵀ‖ ^ 2 := by
  classical
  set Xs := U * S * Vᵀ with hXs
  set d := X - Xs with hd
  set e := ‖d‖ with he
  set N := normal (leftProj U) (rightProj V) with hN
  set ξ := tangentProj U V d with hξ
  set b := N (ξ * V * S⁻¹ * Uᵀ * ξ) with hbdef
  set M := Uᵀ * d * V * S⁻¹ with hM
  set E₂ := U * (M * (Uᵀ * d)) with hE₂
  have hTorth : IsOrthProj (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    isOrthProj_tangentProj hU hV
  have hsplit : ξ + N d = d := tangent_apply_add_normal_apply _ _ d
  have he0 : 0 ≤ e := norm_nonneg _
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK2
  have hξe : ‖ξ‖ ≤ e := hTorth.norm_le d
  have hNd : N d = d - ξ := eq_sub_of_add_eq' hsplit
  have hXeq : X = Xs + d := by rw [hd]; abel
  have hmem : ξ + (2 : ℝ) • N d + E₂ ∈ tangentSpaceAt X := by
    refine ⟨(1 - U * Uᵀ) + U * M * Uᵀ, 1 - V * Vᵀ, ?_⟩
    have hUXs : Uᵀ * Xs = S * Vᵀ := by
      calc Uᵀ * Xs = (Uᵀ * U) * S * Vᵀ := by rw [hXs]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.one_mul]
    have hXsV : Xs * V * Vᵀ = Xs := by
      calc Xs * V * Vᵀ = U * S * (Vᵀ * V) * Vᵀ := by rw [hXs]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]
    have hUUXs : U * Uᵀ * Xs = Xs := by
      calc U * Uᵀ * Xs = U * (Uᵀ * U) * S * Vᵀ := by rw [hXs]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.mul_one]
    have hMS : M * S = Uᵀ * d * V := by
      rw [hM, Matrix.mul_assoc _ S⁻¹ S, Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]
    have hMX : U * M * Uᵀ * X = U * Uᵀ * d * V * Vᵀ + E₂ := by
      calc U * M * Uᵀ * X = U * M * (Uᵀ * Xs + Uᵀ * d) := by
            conv_lhs => rw [hXeq]
            rw [Matrix.mul_add]
            simp only [Matrix.mul_assoc, Matrix.mul_add]
        _ = U * (M * S) * Vᵀ + E₂ := by
            rw [hUXs, Matrix.mul_add, hE₂]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hMS]; simp only [Matrix.mul_assoc]
    have hexp : ((1 - U * Uᵀ) + U * M * Uᵀ) * X + X * (1 - V * Vᵀ) =
        (X - U * Uᵀ * X) + U * M * Uᵀ * X + (X - X * V * Vᵀ) := by
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
        Matrix.mul_assoc]
    rw [hexp, hMX, hNd, two_smul, hξ, tangentProj_apply]
    conv_rhs => rw [hXeq]
    simp only [Matrix.add_mul, Matrix.mul_add, hUUXs, hXsV]
    abel
  have hE₂le : ‖E₂‖ ≤ K * e ^ 2 := by
    have hdV : ‖d * V‖ ≤ e := norm_mul_le_of_orthonormal hV d
    have hUd : ‖Uᵀ * d‖ ≤ e := norm_transpose_mul_le hU d
    have hUdV : ‖Uᵀ * d * V‖ ≤ e := by
      rw [Matrix.mul_assoc]
      exact (norm_transpose_mul_le hU _).trans hdV
    rw [hE₂, Frobenius.norm_mul_of_orthonormal hU]
    calc ‖M * (Uᵀ * d)‖ ≤ ‖M‖ * ‖Uᵀ * d‖ := Frobenius.norm_mul_le _ _
      _ ≤ ‖Uᵀ * d * V‖ * ‖S⁻¹‖ * ‖Uᵀ * d‖ := by gcongr; exact Frobenius.norm_mul_le _ _
      _ ≤ e * K * e := by gcongr
      _ = _ := by ring
  have hτle : ‖ξ + (2 : ℝ) • N d + E₂‖ ≤ e + 3 * K * e ^ 2 := by
    calc ‖ξ + (2 : ℝ) • N d + E₂‖ ≤ ‖ξ‖ + ‖(2 : ℝ) • N d‖ + ‖E₂‖ := norm_add₃_le
      _ = ‖ξ‖ + 2 * ‖N d‖ + ‖E₂‖ := by rw [norm_smul]; norm_num
      _ ≤ e + 2 * (K * e ^ 2) + K * e ^ 2 := by gcongr
      _ = _ := by ring
  refine ⟨ξ + (2 : ℝ) • N d + E₂, hmem, hτle, ?_⟩
  set τ := ξ + (2 : ℝ) • N d + E₂ with hτ
  have hgξ : ⟪g, ξ⟫ = 0 := inner_tangentProj_eq_zero hU hV h1 h2 d
  have hgE : ⟪g, E₂⟫ = 0 := by
    rw [hE₂, Frobenius.inner_mul_left', h1, inner_zero_left]
  have hgτ : ⟪g, τ⟫ = 2 * ⟪g, N d⟫ := by
    rw [hτ, inner_add_right, inner_add_right, inner_smul_right, hgξ, hgE]
    ring
  have hHd : H d = H ξ + H (N d) := by rw [← map_add, hsplit]
  have hHτ : ⟪H d, τ⟫ = ⟪H ξ, ξ⟫ + ⟪H (N d), ξ⟫ + ⟪H d, (2 : ℝ) • N d + E₂⟫ := by
    have e1 : τ = ξ + ((2 : ℝ) • N d + E₂) := add_assoc _ _ _
    rw [e1, inner_add_right, hHd, inner_add_left]
  have hsplitX : ⟪gX, τ⟫ = ⟪g, τ⟫ + ⟪H d, τ⟫ + ⟪gX - g - H d, τ⟫ := by
    rw [inner_sub_left, inner_sub_left]
    ring
  have hgb : |⟪g, N d⟫ - ⟪g, b⟫| ≤ ‖g‖ * (ζ * e ^ 2) := by
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans (by gcongr)
  have hHN : ‖H (N d)‖ ≤ ‖H‖ * (K * e ^ 2) := (H.le_opNorm _).trans (by gcongr)
  have hHd' : ‖H d‖ ≤ ‖H‖ * e := H.le_opNorm _
  have h3 : |⟪H (N d), ξ⟫| ≤ ‖H‖ * (K * e ^ 2) * e :=
    (abs_real_inner_le_norm _ _).trans (by gcongr)
  have h4 : |⟪H d, (2 : ℝ) • N d + E₂⟫| ≤ ‖H‖ * e * (3 * K * e ^ 2) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h5 : ‖(2 : ℝ) • N d + E₂‖ ≤ 3 * K * e ^ 2 := by
      calc ‖(2 : ℝ) • N d + E₂‖ ≤ ‖(2 : ℝ) • N d‖ + ‖E₂‖ := norm_add_le _ _
        _ = 2 * ‖N d‖ + ‖E₂‖ := by rw [norm_smul]; norm_num
        _ ≤ 2 * (K * e ^ 2) + K * e ^ 2 := by gcongr
        _ = _ := by ring
    gcongr
  have h5 : |⟪gX - g - H d, τ⟫| ≤ c * e * (e + 3 * K * e ^ 2) :=
    (abs_real_inner_le_norm _ _).trans (by gcongr)
  have h6 := abs_tangent_aux hsplitX hgτ hHτ hgb h3 h4 h5
  have e7 : 2 * (‖g‖ * (ζ * e ^ 2)) + ‖H‖ * (K * e ^ 2) * e + ‖H‖ * e * (3 * K * e ^ 2) +
      c * e * (e + 3 * K * e ^ 2) =
      (2 * ‖g‖ * ζ + 4 * ‖H‖ * K * e + c * (1 + 3 * K * e)) * e ^ 2 := by
    ring
  rw [e7] at h6
  exact h6

/-- `X ↦ (Uᵀ X V)⁻¹` is continuous at `X∗ = U S Vᵀ`, and `Uᵀ X V` is invertible near `X∗`. -/
lemma core_inv_near (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det) :
    (∀ᶠ X in 𝓝 (U * S * Vᵀ), IsUnit (Uᵀ * X * V).det) ∧
      Tendsto (fun X : Matrix m n ℝ => (Uᵀ * X * V)⁻¹) (𝓝 (U * S * Vᵀ)) (𝓝 S⁻¹) := by
  have hΦ : Continuous fun X : Matrix m n ℝ => Uᵀ * X * V :=
    (Frobenius.rightMulCLM V).continuous.comp (Frobenius.leftMulCLM Uᵀ).continuous
  have hval : Uᵀ * (U * S * Vᵀ) * V = S := by
    calc Uᵀ * (U * S * Vᵀ) * V = (Uᵀ * U) * S * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
  have hΦS : Tendsto (fun X : Matrix m n ℝ => Uᵀ * X * V) (𝓝 (U * S * Vᵀ)) (𝓝 S) := by
    have := hΦ.tendsto (U * S * Vᵀ)
    rwa [hval] at this
  constructor
  · have hdet : Continuous fun A : Matrix (Fin k) (Fin k) ℝ => A.det :=
      Continuous.matrix_det continuous_id
    have h1 : ∀ᶠ A in 𝓝 S, A.det ≠ 0 := hdet.continuousAt.eventually_ne hS.ne_zero
    filter_upwards [hΦS.eventually h1] with X hX
    exact isUnit_iff_ne_zero.2 hX
  · obtain ⟨u, hu⟩ := hS
    have hinv : ContinuousAt Ring.inverse S.det := by
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    have h2 : ContinuousAt (fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹) S :=
      continuousAt_matrix_inv S hinv
    exact h2.tendsto.comp hΦS

/-- The arithmetic of the constants in `taylor_on_rank_le`. -/
lemma constants_aux {η B c e gn Hn K : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hB : 1 ≤ B)
    (hc : c = η / (20 * B ^ 2)) (he0 : 0 ≤ e) (he : e ≤ c) (hg' : gn ≤ B)
    (hH' : Hn ≤ B) (hK0 : 0 ≤ K) (hK : K ≤ B) :
    c ≤ 1 ∧ c + gn * c + Hn * K * e ≤ η ∧ (K * e) ^ 2 ≤ η / 2 ∧ 3 * K * e ≤ η ∧
      2 * gn * c + 4 * Hn * K * e + c * (1 + 3 * K * e) ≤ η := by
  have hB0 : 0 < B := by linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcB : c * B ^ 2 = η / 20 := by rw [hc]; field_simp
  have hB2 : B ≤ B ^ 2 := by nlinarith
  have h1B2 : 1 ≤ B ^ 2 := by nlinarith
  have hcle : c ≤ η / 20 := by nlinarith
  have hBc : B * c ≤ η / 20 := by nlinarith
  have hKe : K * e ≤ η / 20 := by
    calc K * e ≤ B * c := by gcongr
      _ ≤ _ := hBc
  have hgc : gn * c ≤ η / 20 := by
    calc gn * c ≤ B * c := by gcongr
      _ ≤ _ := hBc
  have hHKe : Hn * K * e ≤ η / 20 := by
    calc Hn * K * e = Hn * (K * e) := by ring
      _ ≤ B * (B * c) := by gcongr
      _ = c * B ^ 2 := by ring
      _ = _ := hcB
  have hKe0 : 0 ≤ K * e := by positivity
  refine ⟨by linarith, by linarith, ?_, by linarith, ?_⟩
  · have : (K * e) ^ 2 ≤ (η / 20) ^ 2 := pow_le_pow_left₀ hKe0 hKe 2
    nlinarith
  · have h3 : c * (3 * K * e) ≤ 1 * (3 * K * e) := by
      have : 3 * K * e = 3 * (K * e) := by ring
      gcongr
      linarith
    nlinarith

/-- **The Riemannian Hessian is the second-order term of `f` along `M_{≤k}`.**  Let `X∗ = U S Vᵀ`
have rank `k`, with `grad f(X∗) = 0` and `∇f` differentiable at `X∗` with derivative `H`.  For `X`
of rank `≤ k` near `X∗`, with `d = X - X∗` and `ξ = P_{U,V} d`:
`|f(X) - f(X∗) - H(ξ, ξ) / 2| ≤ η ‖d‖²`, `‖d‖² ≤ (1 + η) ‖ξ‖²`, and there is a tangent vector `τ` of
`M_{rank X}` at `X` with `‖τ‖ ≤ (1 + η) ‖d‖` and `|⟪∇f(X), τ⟫ - H(ξ, ξ)| ≤ η ‖d‖²`.
(arXiv 2306.00897.) -/
theorem taylor_on_rank_le {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ}
    (hgrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X) {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hcrit : riemGrad G (U * S * Vᵀ) = 0) (hH : HasFDerivAt G H (U * S * Vᵀ)) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ X in 𝓝 (U * S * Vᵀ), X.rank ≤ k →
      |f X - f (U * S * Vᵀ) -
          riemHess (G (U * S * Vᵀ)) H U S V (tangentProj U V (X - U * S * Vᵀ)) / 2| ≤
        η * ‖X - U * S * Vᵀ‖ ^ 2 ∧
      ‖X - U * S * Vᵀ‖ ^ 2 ≤ (1 + η) * ‖tangentProj U V (X - U * S * Vᵀ)‖ ^ 2 ∧
      ∃ τ ∈ tangentSpaceAt X, ‖τ‖ ≤ (1 + η) * ‖X - U * S * Vᵀ‖ ∧
        |⟪G X, τ⟫ - riemHess (G (U * S * Vᵀ)) H U S V (tangentProj U V (X - U * S * Vᵀ))| ≤
          η * ‖X - U * S * Vᵀ‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := crit_factor hU hV hS hcrit
  set Xs := U * S * Vᵀ with hXs
  set g := G Xs with hg
  set K := ‖S⁻¹‖ + 1 with hK
  set B := ‖g‖ + ‖H‖ + K + 1 with hB
  have hK0 : 0 ≤ K := by positivity
  have hB1 : 1 ≤ B := by rw [hB]; have := norm_nonneg g; have := norm_nonneg H; linarith
  set c := η / (20 * B ^ 2) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨hdet, hinv⟩ := core_inv_near (m := m) (n := n) hU hV hS
  have hball : ∀ᶠ X in 𝓝 Xs, ‖(Uᵀ * X * V)⁻¹ - S⁻¹‖ < c := by
    have := hinv.eventually (Metric.ball_mem_nhds S⁻¹ hc0)
    filter_upwards [this] with X hX
    have h3 : dist (Uᵀ * X * V)⁻¹ S⁻¹ < c := hX
    rwa [dist_eq_norm] at h3
  filter_upwards [hdet, hball, Metric.ball_mem_nhds Xs hc0, taylor_second_order hgrad hH hc0,
    hH.isLittleO.def hc0] with X hA hζ hXball hT hr hrank
  set e := ‖X - Xs‖ with he
  have hec : e < c := by rwa [Metric.mem_ball, dist_eq_norm] at hXball
  have he0 : 0 ≤ e := norm_nonneg _
  have hgn := norm_nonneg g
  have hHn := norm_nonneg H
  obtain ⟨hc1, hC1, hC2, hC3, hC4⟩ := constants_aux (gn := ‖g‖) (Hn := ‖H‖) hη hη1 hB1 hc he0
    hec.le (by linarith only [hB, hHn, hK0]) (by linarith only [hB, hgn, hK0])
    hK0 (by linarith only [hB, hgn, hHn])
  have hK1 : ‖(Uᵀ * X * V)⁻¹‖ ≤ K := by
    have := norm_sub_norm_le (Uᵀ * X * V)⁻¹ S⁻¹
    rw [hK]
    linarith
  have hK2 : ‖S⁻¹‖ ≤ K := by rw [hK]; linarith
  obtain ⟨hNle, hNb⟩ := normal_sub_bounds hU hV hrank hA hζ.le hK1
  obtain ⟨hv1, hv2⟩ := local_expansion_value (a := f X - f Xs) (H := H) (c := c) hU hV h1 h2 hNle
    hNb hT
  obtain ⟨τ, hτ, hτ1, hτ2⟩ := local_expansion_tangent (gX := G X) (H := H) (c := c) hU hV hS h1 h2
    hK2 hNle hNb hr hc0.le
  rw [← hXs, ← he] at hv1 hv2 hτ1 hτ2
  have he2 : 0 ≤ e ^ 2 := sq_nonneg e
  refine ⟨hv1.trans (mul_le_mul_of_nonneg_right hC1 he2), ?_, τ, hτ, ?_,
    hτ2.trans (mul_le_mul_of_nonneg_right hC4 he2)⟩
  · set y := ‖tangentProj U V (X - Xs)‖ ^ 2 with hy
    have h5 : K ^ 2 * e ^ 4 = (K * e) ^ 2 * e ^ 2 := by ring
    rw [h5] at hv2
    have h6 : (K * e) ^ 2 * e ^ 2 ≤ η / 2 * e ^ 2 := by gcongr
    have h7 : e ^ 2 * (1 - η / 2) ≤ y := by linarith only [hv2, h6]
    have h8 : 0 ≤ η * (1 - η) / 2 * e ^ 2 :=
      mul_nonneg (div_nonneg (mul_nonneg hη.le (sub_nonneg.2 hη1)) zero_le_two) he2
    calc e ^ 2 ≤ (1 + η) * (e ^ 2 * (1 - η / 2)) := by linarith only [h8]
      _ ≤ (1 + η) * y := by gcongr
  · have h5 : e + 3 * K * e ^ 2 = e * (1 + 3 * K * e) := by ring
    rw [h5] at hτ1
    refine hτ1.trans ?_
    rw [mul_comm e]
    gcongr

/-- The real-number core of Lemma 3.6. -/
lemma pl_aux {a Qv y e t g₀ τn η μ ε θ : ℝ} (hμ : 0 < μ) (hε : 0 ≤ ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (hθdef : θ = η * (1 + η) / μ) (hθ : θ ≤ 1 / 4)
    (hφ : (1 / 2 + θ) * (1 + η) ^ 3 ≤ (1 / 2 + μ * ε) * (1 - θ) ^ 2) (hg₀ : 0 ≤ g₀)
    (hQ : μ * y ^ 2 ≤ Qv) (he : e ^ 2 ≤ (1 + η) * y ^ 2)
    (ha : |a - Qv / 2| ≤ η * e ^ 2) (hτ : τn ≤ (1 + η) * e) (ht : |t - Qv| ≤ η * e ^ 2)
    (htg : t ≤ g₀ * τn) : a ≤ (1 / (2 * μ) + ε) * g₀ ^ 2 ∧ e ^ 2 ≤ 8 / μ * a := by
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hQ0 : 0 ≤ Qv := (mul_nonneg hμ.le (sq_nonneg y)).trans hQ
  have hy : y ^ 2 ≤ Qv / μ := by rwa [le_div_iff₀' hμ]
  have he2 : e ^ 2 ≤ (1 + η) * (Qv / μ) := he.trans (by gcongr)
  have hηe : η * e ^ 2 ≤ θ * Qv := by
    calc η * e ^ 2 ≤ η * ((1 + η) * (Qv / μ)) := by gcongr
      _ = θ * Qv := by rw [hθdef]; ring
  obtain ⟨a1, a2⟩ := abs_le.1 (ha.trans hηe)
  obtain ⟨t1, -⟩ := abs_le.1 (ht.trans hηe)
  have ha1 : a ≤ (1 / 2 + θ) * Qv := by linarith
  have ha2 : Qv / 4 ≤ a := by nlinarith
  refine ⟨?_, ?_⟩
  · have hp : 0 < 1 - θ := by linarith
    have ht2 : (1 - θ) * Qv ≤ g₀ * ((1 + η) * e) := by
      have : g₀ * τn ≤ g₀ * ((1 + η) * e) := by gcongr
      linarith
    have hsq : ((1 - θ) * Qv) ^ 2 ≤ (g₀ * ((1 + η) * e)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ht2 2
    have hsq2 : (g₀ * ((1 + η) * e)) ^ 2 ≤ g₀ ^ 2 * (1 + η) ^ 3 * (Qv / μ) := by
      calc (g₀ * ((1 + η) * e)) ^ 2 = g₀ ^ 2 * (1 + η) ^ 2 * e ^ 2 := by ring
        _ ≤ g₀ ^ 2 * (1 + η) ^ 2 * ((1 + η) * (Qv / μ)) := by gcongr
        _ = _ := by ring
    rcases hQ0.eq_or_lt with h0 | hpos
    · have : a ≤ 0 := by rw [← h0] at ha1; linarith
      have h2 : 0 ≤ (1 / (2 * μ) + ε) * g₀ ^ 2 := by positivity
      linarith
    · have h3 : (1 - θ) ^ 2 * Qv ≤ g₀ ^ 2 * (1 + η) ^ 3 / μ := by
        have h4 : (1 - θ) ^ 2 * Qv * Qv ≤ g₀ ^ 2 * (1 + η) ^ 3 / μ * Qv := by
          calc (1 - θ) ^ 2 * Qv * Qv = ((1 - θ) * Qv) ^ 2 := by ring
            _ ≤ g₀ ^ 2 * (1 + η) ^ 3 * (Qv / μ) := hsq.trans hsq2
            _ = _ := by ring
        exact le_of_mul_le_mul_right h4 hpos
      have h5 : (1 - θ) ^ 2 * a ≤ (1 - θ) ^ 2 * ((1 / (2 * μ) + ε) * g₀ ^ 2) := by
        calc (1 - θ) ^ 2 * a ≤ (1 - θ) ^ 2 * ((1 / 2 + θ) * Qv) := by gcongr
          _ = (1 / 2 + θ) * ((1 - θ) ^ 2 * Qv) := by ring
          _ ≤ (1 / 2 + θ) * (g₀ ^ 2 * (1 + η) ^ 3 / μ) := by gcongr
          _ = ((1 / 2 + θ) * (1 + η) ^ 3) * (g₀ ^ 2 / μ) := by ring
          _ ≤ ((1 / 2 + μ * ε) * (1 - θ) ^ 2) * (g₀ ^ 2 / μ) := by gcongr
          _ = (1 - θ) ^ 2 * ((1 / (2 * μ) + ε) * g₀ ^ 2) := by field_simp
      exact le_of_mul_le_mul_left h5 (by positivity)
  · have hη2 : 1 + η ≤ 2 := by linarith
    calc e ^ 2 ≤ (1 + η) * (Qv / μ) := he2
      _ ≤ 2 * (Qv / μ) := by gcongr
      _ ≤ 2 * ((4 * a) / μ) := by
          have : Qv ≤ 4 * a := by linarith
          gcongr
      _ = _ := by ring

/-- The choice of the accuracy `η` in Lemma 3.6. -/
lemma exists_eta {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η * (1 + η) / μ ≤ 1 / 4 ∧
      (1 / 2 + η * (1 + η) / μ) * (1 + η) ^ 3 ≤
        (1 / 2 + μ * ε) * (1 - η * (1 + η) / μ) ^ 2 := by
  have hc1 : Continuous fun η : ℝ => (1 / 2 + η * (1 + η) / μ) * (1 + η) ^ 3 -
      (1 / 2 + μ * ε) * (1 - η * (1 + η) / μ) ^ 2 := by fun_prop
  have hc2 : Continuous fun η : ℝ => η * (1 + η) / μ := by fun_prop
  have hv : (1 / 2 + (0 : ℝ) * (1 + 0) / μ) * (1 + 0) ^ 3 -
      (1 / 2 + μ * ε) * (1 - 0 * (1 + 0) / μ) ^ 2 < 0 := by
    have : 0 < μ * ε := mul_pos hμ hε
    norm_num
    linarith
  have ev1 := hc1.continuousAt.eventually (gt_mem_nhds hv)
  have ev2 := hc2.continuousAt.eventually (gt_mem_nhds (show (0 : ℝ) * (1 + 0) / μ < 1 / 4 by
    norm_num))
  have ev3 := ((ev1.and ev2).filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and
    (Ioo_mem_nhdsGT (zero_lt_one' ℝ))
  obtain ⟨η, ⟨h1, h2⟩, h3, h4⟩ := ev3.exists
  exact ⟨η, h3, h4.le, h2.le, by linarith⟩

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ}
  {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}

/-- **Lemma 3.6** (arXiv 2306.00897) for `M = M_k`, together with quadratic growth.  At a critical
point `X∗ = U S Vᵀ` of rank `k` at which the Riemannian Hessian satisfies `H(ξ, ξ) ≥ μ ‖ξ‖²`, for
every `ε > 0` and all `X` of rank `≤ k` near `X∗`:
`f(X) - f(X∗) ≤ (1 / (2 μ) + ε) ‖grad f(X)‖²` and `‖X - X∗‖² ≤ 8 / μ (f(X) - f(X∗))`.

Differences from the paper: Mathlib has no embedded Riemannian manifolds, so the lemma is stated for
`M_k`, the only case the paper uses, and the Hessian is `riemHess`; the proof avoids local charts by
using the identity `eq_mul_inv_mul`.  The estimate holds on `M_{≤k}`, which near `X∗` is `M_k`.
Differentiability of `∇f` at `X∗` replaces twice continuous differentiability. -/
theorem riemannian_pl (hgrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hS : IsUnit S.det) (hcrit : riemGrad G (U * S * Vᵀ) = 0)
    (hH : HasFDerivAt G H (U * S * Vᵀ)) {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj U V ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (U * S * Vᵀ)) H U S V ξ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in 𝓝 (U * S * Vᵀ), X.rank ≤ k →
      f X - f (U * S * Vᵀ) ≤ (1 / (2 * μ) + ε) * ‖riemGrad G X‖ ^ 2 ∧
      ‖X - U * S * Vᵀ‖ ^ 2 ≤ 8 / μ * (f X - f (U * S * Vᵀ)) := by
  obtain ⟨η, hη0, hη1, hθ, hφ⟩ := exists_eta hμ hε
  filter_upwards [taylor_on_rank_le hgrad hU hV hS hcrit hH hη0 hη1] with X hX hrank
  obtain ⟨h1, h2, τ, hτ, hτ1, hτ2⟩ := hX hrank
  have hQ := hpd _ ((isOrthProj_tangentProj (m := m) (n := n) hU hV).idem (X - U * S * Vᵀ))
  have htg : ⟪G X, τ⟫ ≤ ‖riemGrad G X‖ * ‖τ‖ := by
    rw [inner_grad_eq_inner_riemGrad G hτ]
    exact real_inner_le_norm _ _
  exact pl_aux hμ hε.le hη0 hη1 rfl hθ hφ (norm_nonneg _) hQ h2 h1 hτ1 hτ2 htg

/-- **`X∗` is an isolated local minimizer of `f|M_k`** (Theorem 3.7), in the stronger form on
`M_{≤k}`.  (arXiv 2306.00897.) -/
theorem isolated_local_min (hgrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hS : IsUnit S.det) (hcrit : riemGrad G (U * S * Vᵀ) = 0)
    (hH : HasFDerivAt G H (U * S * Vᵀ)) {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj U V ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (U * S * Vᵀ)) H U S V ξ) :
    ∀ᶠ X in 𝓝 (U * S * Vᵀ), X.rank ≤ k → X ≠ U * S * Vᵀ → f (U * S * Vᵀ) < f X := by
  filter_upwards [riemannian_pl hgrad hU hV hS hcrit hH hμ hpd one_pos] with X hX hrank hne
  have h1 := (hX hrank).2
  have h2 : 0 < ‖X - U * S * Vᵀ‖ ^ 2 := by
    have := norm_pos_iff.2 (sub_ne_zero.2 hne)
    positivity
  have h3 : 0 < 8 / μ * (f X - f (U * S * Vᵀ)) := h2.trans_le h1
  have h4 : 0 < f X - f (U * S * Vᵀ) := (mul_pos_iff_of_pos_left (by positivity)).1 h3
  linarith

/-- The remark before Theorem 3.8: `λ∗_min ≤ λ`, since `M_k` is a cone.  (arXiv 2306.00897.) -/
theorem le_lam_of_posDef {lam μ : ℝ} (hf : IsSmooth f G lam) (hk : 0 < k) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hS : IsUnit S.det) (hH : HasFDerivAt G H (U * S * Vᵀ))
    (hpd : ∀ ξ, tangentProj U V ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (U * S * Vᵀ)) H U S V ξ) (hlam : 0 ≤ lam) : μ ≤ lam := by
  set Xs := U * S * Vᵀ with hXs
  have hne : Xs ≠ 0 := by
    intro h0
    have h1 : S = Uᵀ * Xs * V := by
      calc S = (Uᵀ * U) * S * (Vᵀ * V) := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by rw [hXs]; simp only [Matrix.mul_assoc]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at h1
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    rw [h1, Matrix.det_zero] at hS
    exact not_isUnit_zero hS
  have hpos : 0 < ‖Xs‖ ^ 2 := by
    have := norm_pos_iff.2 hne
    positivity
  have hHle : ‖H‖ ≤ lam := hH.le_of_lip' hlam
    (Eventually.of_forall fun X => hf.lipschitz X Xs)
  have h1 := hpd Xs (tangentProj_mul_mul_transpose hU V S)
  have h2 : riemHess (G Xs) H U S V Xs = ⟪H Xs, Xs⟫ := by
    have e : Xs * V * S⁻¹ * Uᵀ * Xs = U * (S * Vᵀ * V * S⁻¹ * Uᵀ * Xs) := by
      rw [hXs]; simp only [Matrix.mul_assoc]
    rw [riemHess, e, normal_mul_left hU V, inner_zero_right, mul_zero, add_zero]
  rw [h2] at h1
  have h3 : ⟪H Xs, Xs⟫ ≤ lam * ‖Xs‖ ^ 2 := by
    calc ⟪H Xs, Xs⟫ ≤ ‖H Xs‖ * ‖Xs‖ := real_inner_le_norm _ _
      _ ≤ ‖H‖ * ‖Xs‖ * ‖Xs‖ := by gcongr; exact H.le_opNorm _
      _ ≤ lam * ‖Xs‖ * ‖Xs‖ := by gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_right (h1.trans h3) hpos

end Hessian

/-! ### Local linear convergence -/

/-- The inductive core of the proof of Theorem 3.7, for a Lyapunov sequence `a`: if `a → 0`,
`‖X_ℓ - X∗‖² ≤ c a_ℓ` near `X∗`, `a_{ℓ+1} ≤ q a_ℓ` near `X∗` for large `ℓ`, `X_{ℓ+1} - X_ℓ → 0` and
`X∗` is an accumulation point, then `X_ℓ → X∗` and `a_ℓ = O(q^ℓ)`.  (arXiv 2306.00897.) -/
theorem local_contraction {E : Type*} [NormedAddCommGroup E] {X : ℕ → E} {Xs : E} {a : ℕ → ℝ}
    {c q r : ℝ} (hr : 0 < r) (hc : 0 < c) (hq0 : 0 < q) (ha0 : ∀ ℓ, 0 ≤ a ℓ)
    (ha : Tendsto a atTop (𝓝 0))
    (hgrow : ∀ ℓ, ‖X ℓ - Xs‖ < r → ‖X ℓ - Xs‖ ^ 2 ≤ c * a ℓ)
    (hcontr : ∀ᶠ ℓ in atTop, ‖X ℓ - Xs‖ < r → a (ℓ + 1) ≤ q * a ℓ)
    (hmove : Tendsto (fun ℓ => X (ℓ + 1) - X ℓ) atTop (𝓝 0))
    (hcluster : MapClusterPt Xs atTop X) :
    Tendsto X atTop (𝓝 Xs) ∧ ∃ C, 0 ≤ C ∧ ∀ᶠ ℓ in atTop,
      a ℓ ≤ C * q ^ ℓ ∧ ‖X ℓ - Xs‖ ^ 2 ≤ c * (C * q ^ ℓ) := by
  have hR : 0 < r ^ 2 / (4 * c) := by positivity
  have ev1 : ∀ᶠ ℓ in atTop, ‖X (ℓ + 1) - X ℓ‖ < r / 4 :=
    (tendsto_zero_iff_norm_tendsto_zero.1 hmove).eventually (gt_mem_nhds (by positivity))
  have ev2 : ∀ᶠ ℓ in atTop, a ℓ < r ^ 2 / (4 * c) := ha.eventually (gt_mem_nhds hR)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ev1.and (ev2.and hcontr))
  have hfreq := hcluster.frequently (p := fun y => ‖y - Xs‖ < r)
    (by
      have := Metric.ball_mem_nhds Xs hr
      filter_upwards [this] with y hy
      rwa [Metric.mem_ball, dist_eq_norm] at hy)
  obtain ⟨ℓ₀, hℓ₀, hball⟩ := frequently_atTop.1 hfreq N
  have hin : ∀ i, ‖X (ℓ₀ + i) - Xs‖ < r := by
    intro i
    induction i with
    | zero => exact hball
    | succ i ih =>
      obtain ⟨h1, h2, -⟩ := hN (ℓ₀ + i) (by omega)
      have h3 := hgrow _ ih
      have h4 : ‖X (ℓ₀ + i) - Xs‖ ^ 2 < (r / 2) ^ 2 := by
        calc ‖X (ℓ₀ + i) - Xs‖ ^ 2 ≤ c * a (ℓ₀ + i) := h3
          _ < c * (r ^ 2 / (4 * c)) := by gcongr
          _ = (r / 2) ^ 2 := by field_simp; ring
      have h5 : ‖X (ℓ₀ + i) - Xs‖ < r / 2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h4
      have h6 : X (ℓ₀ + (i + 1)) - Xs = (X (ℓ₀ + i + 1) - X (ℓ₀ + i)) + (X (ℓ₀ + i) - Xs) := by
        rw [← add_assoc]; abel
      rw [h6]
      calc _ ≤ ‖X (ℓ₀ + i + 1) - X (ℓ₀ + i)‖ + ‖X (ℓ₀ + i) - Xs‖ := norm_add_le _ _
        _ < r / 4 + r / 2 := add_lt_add h1 h5
        _ < r := by linarith
  have hdec : ∀ i, a (ℓ₀ + i) ≤ q ^ i * a ℓ₀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      obtain ⟨-, -, h3⟩ := hN (ℓ₀ + i) (by omega)
      have h4 := h3 (hin i)
      calc a (ℓ₀ + (i + 1)) = a (ℓ₀ + i + 1) := by rw [add_assoc]
        _ ≤ q * a (ℓ₀ + i) := h4
        _ ≤ q * (q ^ i * a ℓ₀) := by gcongr
        _ = _ := by ring
  have hC0 : 0 ≤ a ℓ₀ / q ^ ℓ₀ := div_nonneg (ha0 _) (by positivity)
  have hbound : ∀ ℓ ≥ ℓ₀, a ℓ ≤ a ℓ₀ / q ^ ℓ₀ * q ^ ℓ := fun ℓ hℓ => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hℓ
    refine (hdec i).trans (le_of_eq ?_)
    rw [pow_add]
    field_simp
  have hnear : ∀ ℓ ≥ ℓ₀, ‖X ℓ - Xs‖ ^ 2 ≤ c * a ℓ := fun ℓ hℓ => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hℓ
    exact hgrow _ (hin i)
  refine ⟨?_, _, hC0, ?_⟩
  · have hsq : Tendsto (fun ℓ => ‖X ℓ - Xs‖ ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun ℓ => c * a ℓ) atTop (𝓝 0) := by simpa using ha.const_mul c
      refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ h1
      filter_upwards [eventually_ge_atTop ℓ₀] with ℓ hℓ using hnear ℓ hℓ
    exact tendsto_sub_nhds_zero_iff.1 (tendsto_zero_of_sq (u := fun ℓ => X ℓ - Xs) hsq)
  · filter_upwards [eventually_ge_atTop ℓ₀] with ℓ hℓ
    refine ⟨hbound ℓ hℓ, (hnear ℓ hℓ).trans ?_⟩
    gcongr
    exact hbound ℓ hℓ

/-- From geometric bounds at every rate above `r₀` to the bound on the root.  (arXiv 2306.00897.) -/
theorem limsup_root_le_of_forall {u : ℕ → ℝ} {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hu : ∀ ℓ, 0 ≤ u ℓ)
    (h : ∀ q, r₀ < q → q < 1 → ∃ C, 0 ≤ C ∧ ∀ᶠ ℓ in atTop, u ℓ ≤ C * q ^ ℓ) :
    limsup (fun ℓ : ℕ => u ℓ ^ ((ℓ : ℝ)⁻¹)) atTop ≤ r₀ := by
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  obtain ⟨q, hq1, hq2⟩ := exists_between (lt_min ht hr₁)
  have hq0 : 0 < q := hr₀.trans_lt hq1
  have hqt : q < t := hq2.trans_le (min_le_left _ _)
  obtain ⟨C, hC, hb⟩ := h q hq1 (hq2.trans_le (min_le_right _ _))
  set C' := max C 1 with hC'
  have hC'0 : 0 < C' := lt_max_of_lt_right one_pos
  have hlim : Tendsto (fun ℓ : ℕ => C' ^ ((ℓ : ℝ)⁻¹) * q) atTop (𝓝 q) := by
    have h1 : Tendsto (fun ℓ : ℕ => ((ℓ : ℝ)⁻¹)) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
    have h2 := (Real.continuousAt_const_rpow hC'0.ne' (b := 0)).tendsto.comp h1
    have h3 := h2.mul_const q
    simpa using h3
  have hev : ∀ᶠ ℓ : ℕ in atTop, u ℓ ^ ((ℓ : ℝ)⁻¹) ≤ t := by
    filter_upwards [hb, eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds hqt)] with ℓ h1 h2 h3
    have hℓ : ℓ ≠ 0 := by omega
    have h4 : u ℓ ≤ C' * q ^ ℓ := h1.trans (by gcongr; exact le_max_left _ _)
    calc u ℓ ^ ((ℓ : ℝ)⁻¹) ≤ (C' * q ^ ℓ) ^ ((ℓ : ℝ)⁻¹) :=
          Real.rpow_le_rpow (hu ℓ) h4 (by positivity)
      _ = C' ^ ((ℓ : ℝ)⁻¹) * q := by
          rw [Real.mul_rpow hC'0.le (by positivity), Real.pow_rpow_inv_natCast hq0.le hℓ]
      _ ≤ t := h3.le
  have hlow : IsBoundedUnder (· ≥ ·) atTop (fun ℓ : ℕ => u ℓ ^ ((ℓ : ℝ)⁻¹)) :=
    isBoundedUnder_of ⟨0, fun ℓ => Real.rpow_nonneg (hu ℓ) _⟩
  exact limsup_le_of_le hlow.isCoboundedUnder_le hev

section LinearRate

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ} {rule : ℕ → StepRule}
  {h : ℕ → ℝ} {U : ℕ → Matrix m (Fin k) ℝ} {S : ℕ → Matrix (Fin k) (Fin k) ℝ}
  {V : ℕ → Matrix n (Fin k) ℝ} {X : ℕ → Matrix m n ℝ}

/-- The iterates of Algorithm 2 move by at most `h_ℓ ‖P_{U_ℓ,V_ℓ}(∇f(X_ℓ))‖`, (3.22).
(arXiv 2306.00897.) -/
theorem IsRiemRun.norm_sub_le (hlam : 0 < lam) (hrun : IsRiemRun f G lam rule h U S V X) (ℓ : ℕ) :
    ‖X (ℓ + 1) - X ℓ‖ ≤ h ℓ * ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ := by
  obtain ⟨hU, hV⟩ := hrun.orth ℓ
  obtain ⟨-, -, Q, -, hit, hadm, -, hle, -⟩ := (hrun.step ℓ).spec hU hV (hrun.iter ℓ)
  have hpos := StepRule.step_nonneg hlam hadm
  rw [hrun.iter (ℓ + 1), hit, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hpos]
  gcongr

variable {Us : Matrix m (Fin k) ℝ} {Ss : Matrix (Fin k) (Fin k) ℝ} {Vs : Matrix n (Fin k) ℝ}
  {H : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}

/-- The contraction estimate in the proof of Theorem 3.7: given a Polyak-Lojasiewicz inequality with
constant `C₀` near `X∗` and sufficient decrease with constant `c`. -/
lemma contraction_of_pl {a a' g₂ c C₀ : ℝ} (hc : 0 ≤ c) (hC₀ : 0 < C₀) (hpl : a ≤ C₀ * g₂)
    (hdec : c * g₂ ≤ a - a') : a' ≤ (1 - c / C₀) * a := by
  have h1 : c / C₀ * a ≤ c * g₂ := by
    calc c / C₀ * a ≤ c / C₀ * (C₀ * g₂) := by gcongr
      _ = c * g₂ := by field_simp
  rw [sub_mul, one_mul]
  linarith

/-- Local linear convergence with an explicit rate `q`, from the Polyak-Lojasiewicz inequality.
(arXiv 2306.00897.) -/
theorem riemRun_local_rate (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hrun : IsRiemRun f G lam rule h U S V X) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑle : ∀ ℓ, ϑ ≤ (rule ℓ).theta lam) {hmax : ℝ} (hstep : ∀ ℓ, h ℓ ≤ hmax) {Xs : Matrix m n ℝ}
    (hcluster : MapClusterPt Xs atTop X)
    (hanti : Antitone fun ℓ => f (X ℓ)) (hlim : Tendsto (fun ℓ => f (X ℓ)) atTop (𝓝 (f Xs)))
    (hP : Tendsto (fun ℓ => tangentProj (U ℓ) (V ℓ) (G (X ℓ))) atTop (𝓝 0)) {C₀ c₁ r q : ℝ}
    (hC₀ : 0 < C₀) (hc₁ : 0 < c₁) (hr : 0 < r) (hq : q = 1 - ϑ / (2 * lam) / C₀) (hq0 : 0 < q)
    (hpl : ∀ Y : Matrix m n ℝ, ‖Y - Xs‖ < r → Y.rank ≤ k →
      f Y - f Xs ≤ C₀ * ‖riemGrad G Y‖ ^ 2 ∧ ‖Y - Xs‖ ^ 2 ≤ c₁ * (f Y - f Xs)) :
    Tendsto X atTop (𝓝 Xs) ∧ ∃ C, 0 ≤ C ∧ ∀ᶠ ℓ in atTop,
      f (X ℓ) - f Xs ≤ C * q ^ ℓ ∧ ‖X ℓ - Xs‖ ^ 2 ≤ c₁ * (C * q ^ ℓ) := by
  have hrank : ∀ ℓ, (X ℓ).rank ≤ k := fun ℓ => by
    rw [hrun.iter ℓ]; exact rank_mul_mul_transpose_le _ _ _
  have hfl : ∀ ℓ, f Xs ≤ f (X ℓ) := hanti.le_of_tendsto hlim
  have ha : Tendsto (fun ℓ => f (X ℓ) - f Xs) atTop (𝓝 0) := by
    simpa using hlim.sub_const (f Xs)
  have hmove : Tendsto (fun ℓ => X (ℓ + 1) - X ℓ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun ℓ => hmax * ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖) atTop (𝓝 0) := by
      simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hP).const_mul hmax
    refine squeeze_zero_norm (fun ℓ => (hrun.norm_sub_le hlam ℓ).trans ?_) h1
    gcongr
    exact hstep ℓ
  refine local_contraction (a := fun ℓ => f (X ℓ) - f Xs) hr hc₁ hq0
    (fun ℓ => sub_nonneg.2 (hfl ℓ)) ha (fun ℓ hℓ => (hpl _ hℓ (hrank ℓ)).2)
    (Eventually.of_forall fun ℓ hℓ => ?_) hmove hcluster
  have hdec := (riemBlockDescent_decrease hf hlam hrun ℓ)
  have h2 : ϑ / (2 * lam) * ‖riemGrad G (X ℓ)‖ ^ 2 ≤ f (X ℓ) - f (X (ℓ + 1)) := by
    refine le_trans ?_ (hdec.2.1.trans hdec.1)
    have := hϑle ℓ
    gcongr
  have h3 := contraction_of_pl (a := f (X ℓ) - f Xs) (a' := f (X (ℓ + 1)) - f Xs)
    (c := ϑ / (2 * lam)) (g₂ := ‖riemGrad G (X ℓ)‖ ^ 2)
    (by positivity) hC₀ (hpl _ hℓ (hrank ℓ)).1 (by linarith only [h2])
  rw [hq]
  exact h3

/-- **Theorem 3.7** (arXiv 2306.00897).  Let `f` be `λ`-smooth and bounded below, `(X_ℓ)` the
iterates of Algorithm 2 under any combination of the step-size rules, with `ϑ > 0` a lower bound of
the `ϑ_ℓ` (in particular `inf_ℓ ϑ_ℓ`, `theta_iInf_pos`).  Suppose `(X_ℓ)` has an accumulation point
`X∗ = Us Ss Vsᵀ` of rank `k` (every matrix of rank `k` has this form,
`LeanDLRA.SVD.rank_eq_iff_exists_factor`), at which `∇f` is differentiable and the Riemannian
Hessian of `f|M_k` satisfies `H(ξ, ξ) ≥ μ ‖ξ‖²`, `μ > 0` (e.g. `μ = λ∗_min`).  Then `X_ℓ → X∗`, the
point
`X∗` is an isolated local minimizer of `f|M_{≤k}`, `μ ≤ λ`, and the convergence is R-linear:
`limsup ‖X_ℓ - X∗‖^{1/ℓ} ≤ (1 - ϑ μ / λ)^{1/2} < 1`,
`limsup (f(X_ℓ) - f(X∗))^{1/ℓ} ≤ 1 - ϑ μ / λ`.

Differences from the paper.  Only differentiability of `∇f` at `X∗` is assumed, not `C²` near `X∗`.
We assume a bound `h_ℓ ≤ hmax` on the step sizes.  For fixed steps and for backtracking it holds
(`h_ℓ ≤ 2 / λ`, `h_ℓ ≤ h̄`).  For exact line search the paper derives it from the boundedness of
`N₀`, but boundedness of `N₀` only bounds `h_ℓ ‖P_{1/2}‖`, while `‖P_{1/2}‖ → 0`, so that step is
unclear to us and we keep the bound as a hypothesis.  It is only used for `X_{ℓ+1} - X_ℓ → 0`. -/
theorem riemBlockDescent_linear_rate (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hbdd : BddBelow (range f)) (hrun : IsRiemRun f G lam rule h U S V X) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑle : ∀ ℓ, ϑ ≤ (rule ℓ).theta lam) {hmax : ℝ} (hstep : ∀ ℓ, h ℓ ≤ hmax) (hk : 0 < k)
    (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hcluster : MapClusterPt (Us * Ss * Vsᵀ) atTop X) (hH : HasFDerivAt G H (Us * Ss * Vsᵀ))
    {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj Us Vs ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (Us * Ss * Vsᵀ)) H Us Ss Vs ξ) :
    Tendsto X atTop (𝓝 (Us * Ss * Vsᵀ)) ∧
      (∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), Y.rank ≤ k → Y ≠ Us * Ss * Vsᵀ → f (Us * Ss * Vsᵀ) < f Y) ∧
      μ ≤ lam ∧ 1 - ϑ * μ / lam < 1 ∧
      limsup (fun ℓ : ℕ => ‖X ℓ - Us * Ss * Vsᵀ‖ ^ ((ℓ : ℝ)⁻¹)) atTop ≤ √(1 - ϑ * μ / lam) ∧
      limsup (fun ℓ : ℕ => (f (X ℓ) - f (Us * Ss * Vsᵀ)) ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        1 - ϑ * μ / lam := by
  set Xs := Us * Ss * Vsᵀ with hXs
  obtain ⟨hanti, fstar, hlim, -, hP, -, hcl, -, -, -⟩ :=
    riemBlockDescent_convergence hf hlam hbdd hrun hϑ hϑle
  obtain ⟨hfs, hcrit⟩ := hcl Xs hcluster
  subst hfs
  have hμle : μ ≤ lam := le_lam_of_posDef hf hk hUs hVs hSs hH hpd hlam.le
  have hϑhalf : ϑ ≤ 1 / 2 := by
    obtain ⟨hU0, hV0⟩ := hrun.orth 0
    obtain ⟨-, -, Q, -, -, hadm, -, -⟩ := (hrun.step 0).spec hU0 hV0 (hrun.iter 0)
    exact (hϑle 0).trans (StepRule.theta_le_half hadm)
  have hρ1 : 0 < ϑ * μ / lam := by positivity
  have hρ2 : ϑ * μ / lam ≤ 1 / 2 := by
    rw [div_le_iff₀ hlam]
    exact mul_le_mul hϑhalf hμle hμ.le (by norm_num)
  set ρ₀ := 1 - ϑ * μ / lam with hρ₀
  have hρ0 : 0 < ρ₀ := by rw [hρ₀]; linarith
  have hρlt : ρ₀ < 1 := by rw [hρ₀]; linarith
  -- the bound at every rate `q ∈ (ρ₀, 1)`
  have key : ∀ q, ρ₀ < q → q < 1 → Tendsto X atTop (𝓝 Xs) ∧ ∃ C, 0 ≤ C ∧ ∀ᶠ ℓ in atTop,
      f (X ℓ) - f Xs ≤ C * q ^ ℓ ∧ ‖X ℓ - Xs‖ ^ 2 ≤ 8 / μ * (C * q ^ ℓ) := by
    intro q hq hq1
    have h1q : 0 < 1 - q := sub_pos.2 hq1
    set C₀ := ϑ / (2 * lam) / (1 - q) with hC₀
    have hC₀0 : 0 < C₀ := by positivity
    have hε : 0 < C₀ - 1 / (2 * μ) := by
      have h3 : 1 - q < ϑ * μ / lam := by rw [hρ₀] at hq; linarith
      have e1 : C₀ - 1 / (2 * μ) = (ϑ * μ / lam - (1 - q)) / (2 * μ * (1 - q)) := by
        rw [hC₀]; field_simp
      rw [e1]
      exact div_pos (sub_pos.2 h3) (by positivity)
    have hpl := riemannian_pl (f := f) hf.hasGrad hUs hVs hSs hcrit hH hμ hpd hε
    rw [← hXs] at hpl
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hpl
    have hq0 : 0 < q := hρ0.trans hq
    refine riemRun_local_rate (C₀ := C₀) (c₁ := 8 / μ) (r := r) hf hlam hrun hϑ hϑle hstep hcluster
      hanti hlim hP hC₀0 (by positivity) hr ?_ hq0 fun Y hY hrk => ?_
    · rw [hC₀]; field_simp; ring
    · have h4 := hball Y (by rwa [Metric.mem_ball, dist_eq_norm]) hrk
      rwa [add_sub_cancel] at h4
  obtain ⟨q₀, hq01, hq02⟩ := exists_between hρlt
  have hfl : ∀ ℓ, 0 ≤ f (X ℓ) - f Xs := fun ℓ => sub_nonneg.2 (hanti.le_of_tendsto hlim ℓ)
  have hsq1 : √ρ₀ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  refine ⟨(key q₀ hq01 hq02).1, isolated_local_min hf.hasGrad hUs hVs hSs hcrit hH hμ hpd, hμle,
    hρlt, ?_, ?_⟩
  · refine limsup_root_le_of_forall (Real.sqrt_nonneg _) hsq1 (fun ℓ => norm_nonneg _)
      fun q hq hq1 => ?_
    have hq0 : 0 < q := (Real.sqrt_nonneg _).trans_lt hq
    have hq2 : ρ₀ < q ^ 2 := (Real.sqrt_lt' hq0).1 hq
    have hq3 : q ^ 2 < 1 := by nlinarith
    obtain ⟨-, C, hC, hev⟩ := key (q ^ 2) hq2 hq3
    refine ⟨√(8 / μ * C), Real.sqrt_nonneg _, ?_⟩
    filter_upwards [hev] with ℓ hℓ
    calc ‖X ℓ - Xs‖ = √(‖X ℓ - Xs‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(8 / μ * C * (q ^ ℓ) ^ 2) := by
          refine Real.sqrt_le_sqrt (hℓ.2.trans (le_of_eq ?_))
          rw [← pow_mul, ← pow_mul, mul_comm 2 ℓ]
          ring
      _ = √(8 / μ * C) * q ^ ℓ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  · refine limsup_root_le_of_forall hρ0.le hρlt hfl fun q hq hq1 => ?_
    obtain ⟨-, C, hC, hev⟩ := key q hq hq1
    exact ⟨C, hC, hev.mono fun ℓ h => h.1⟩

end LinearRate

/-! ### The refined local rates: restricted smoothness constants -/

section LocalSmooth

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ}
  {H : Matrix m n ℝ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ}

/-- The triangle inequality for four terms. -/
lemma abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ |a + b| + |c| + |d| := by gcongr; exact abs_add_le _ _
    _ ≤ |a| + |b| + |c| + |d| := by gcongr; exact abs_add_le _ _

/-- **Restricted smoothness near `X∗`** (the mean value estimate in the proof of Theorem 3.8, and
(2.7)).  Let `∇f` be differentiable near `X∗` with derivative `H` continuous at `X∗`, and let `Q∗`
be an orthogonal projector with `‖Q∗ H(X∗) Q∗‖ < Λ`.  For `X` near `X∗` and `P` small lying in the
range of a projector `Q` close to `Q∗`, the descent estimate holds along `P` with constant `Λ`, on
any fixed interval `[0, T]`.  (arXiv 2306.00897.) -/
theorem local_descent (hgrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X) {Xs : Matrix m n ℝ}
    (hH : ∀ᶠ X in 𝓝 Xs, HasFDerivAt G (H X) X) (hHc : ContinuousAt H Xs)
    {Qs : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hQs : IsOrthProj Qs) {Λ T : ℝ}
    (hΛ : ‖Qs ∘L H Xs ∘L Qs‖ < Λ) (hT : 0 < T) :
    ∃ δ > 0, ∀ (X P : Matrix m n ℝ) (Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ),
      ‖X - Xs‖ < δ → ‖P‖ < δ → Q P = P → (∀ Z, ‖Q Z - Qs Z‖ ≤ δ * ‖Z‖) →
      ∀ t ∈ Icc 0 T, f (X - t • P) ≤ f X - t * ⟪G X, P⟫ + Λ / 2 * t ^ 2 * ‖P‖ ^ 2 := by
  set H₀ := H Xs with hH₀
  set l := ‖Qs ∘L H₀ ∘L Qs‖ with hl
  obtain ⟨ζ, hζ0, hζ⟩ : ∃ ζ > 0, l + 3 * ζ ≤ Λ := ⟨(Λ - l) / 3, by
    have := sub_pos.2 hΛ
    positivity, by linarith⟩
  have h1 : ∀ᶠ Y in 𝓝 Xs, HasFDerivAt G (H Y) Y ∧ ‖H Y - H₀‖ < ζ := by
    refine hH.and ?_
    have := hHc.eventually (Metric.ball_mem_nhds H₀ hζ0)
    filter_upwards [this] with Y hY
    have h2 : dist (H Y) H₀ < ζ := hY
    rwa [dist_eq_norm] at h2
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 h1
  set δ := min (min (r / 2) (r / (2 * (T + 1)))) (ζ / (2 * (‖H₀‖ + 1))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ r / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ r / (2 * (T + 1)) := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ ζ / (2 * (‖H₀‖ + 1)) := min_le_right _ _
  refine ⟨δ, hδ0, fun X P Q hX hP hQP hQ t ht => ?_⟩
  have hYnear : ∀ s ∈ Icc (0 : ℝ) T, X - s • P ∈ Metric.ball Xs r := fun s hs => by
    rw [Metric.mem_ball, dist_eq_norm]
    have e : X - s • P - Xs = (X - Xs) - s • P := by abel
    have h2 : ‖s • P‖ ≤ T * δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_mul hs.2 hP.le (norm_nonneg _) hT.le
    have h3 : (T + 1) * δ ≤ r / 2 := by
      calc (T + 1) * δ ≤ (T + 1) * (r / (2 * (T + 1))) := by gcongr
        _ = r / 2 := by field_simp
    rw [e]
    calc ‖X - Xs - s • P‖ ≤ ‖X - Xs‖ + ‖s • P‖ := norm_sub_le _ _
      _ < δ + T * δ := by linarith
      _ = (T + 1) * δ := by ring
      _ ≤ r / 2 := h3
      _ < r := by linarith
  have hw : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => ⟪G (X - s • P), P⟫)
      (-⟪H (X - s • P) P, P⟫) s := fun s hs => by
    have h1 : HasDerivAt (fun s : ℝ => X - s • P) (-P) s := by
      simpa using ((hasDerivAt_id s).smul_const P).const_sub X
    have h2 := (hball _ (hYnear s hs)).1.comp_hasDerivAt s h1
    have h3 := h2.inner ℝ (hasDerivAt_const s P)
    simpa [Function.comp_def, map_neg] using h3
  have hbound : ∀ s ∈ Icc (0 : ℝ) T, ‖-⟪H (X - s • P) P, P⟫‖ ≤ Λ * ‖P‖ ^ 2 := fun s hs => by
    set Y := X - s • P with hY
    have hHY : ‖H Y - H₀‖ < ζ := (hball _ (hYnear s hs)).2
    set D := P - Qs P with hD
    have hDn : ‖D‖ ≤ δ * ‖P‖ := by
      have := hQ P
      rwa [hQP] at this
    have hP' : ‖Qs P‖ ≤ ‖P‖ := hQs.norm_le P
    have e1 : ⟪H Y P, P⟫ = ⟪(H Y - H₀) P, P⟫ + ⟪(Qs ∘L H₀ ∘L Qs) P, P⟫ + ⟪H₀ (Qs P), D⟫ +
        ⟪H₀ D, P⟫ := by
      have e2 : ⟪(Qs ∘L H₀ ∘L Qs) P, P⟫ = ⟪H₀ (Qs P), Qs P⟫ := by
        simp only [ContinuousLinearMap.comp_apply]
        exact hQs.symm _ _
      have e3 : H₀ P = H₀ (Qs P) + H₀ D := by rw [← map_add, hD, add_sub_cancel]
      have e4 : ⟪H₀ (Qs P), P⟫ = ⟪H₀ (Qs P), Qs P⟫ + ⟪H₀ (Qs P), D⟫ := by
        rw [← inner_add_right, hD, add_sub_cancel]
      rw [e2, sub_apply, inner_sub_left, e3, inner_add_left, e4]
      ring
    have t1 : |⟪(H Y - H₀) P, P⟫| ≤ ζ * ‖P‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖(H Y - H₀) P‖ * ‖P‖ ≤ ‖H Y - H₀‖ * ‖P‖ * ‖P‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ζ * ‖P‖ * ‖P‖ := by gcongr
        _ = _ := by ring
    have t2 : |⟪(Qs ∘L H₀ ∘L Qs) P, P⟫| ≤ l * ‖P‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖(Qs ∘L H₀ ∘L Qs) P‖ * ‖P‖ ≤ l * ‖P‖ * ‖P‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ = _ := by ring
    have hsmall : ‖H₀‖ * δ ≤ ζ / 2 := by
      have h3 : (‖H₀‖ + 1) * δ ≤ ζ / 2 := by
        calc (‖H₀‖ + 1) * δ ≤ (‖H₀‖ + 1) * (ζ / (2 * (‖H₀‖ + 1))) := by gcongr
          _ = ζ / 2 := by field_simp
      nlinarith
    have t3 : |⟪H₀ (Qs P), D⟫| ≤ ζ / 2 * ‖P‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖H₀ (Qs P)‖ * ‖D‖ ≤ (‖H₀‖ * ‖P‖) * (δ * ‖P‖) := by
            gcongr
            exact (H₀.le_opNorm _).trans (by gcongr)
        _ = (‖H₀‖ * δ) * ‖P‖ ^ 2 := by ring
        _ ≤ _ := by gcongr
    have t4 : |⟪H₀ D, P⟫| ≤ ζ / 2 * ‖P‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖H₀ D‖ * ‖P‖ ≤ (‖H₀‖ * (δ * ‖P‖)) * ‖P‖ := by
            gcongr
            exact (H₀.le_opNorm _).trans (by gcongr)
        _ = (‖H₀‖ * δ) * ‖P‖ ^ 2 := by ring
        _ ≤ _ := by gcongr
    rw [norm_neg, Real.norm_eq_abs, e1]
    calc |⟪(H Y - H₀) P, P⟫ + ⟪(Qs ∘L H₀ ∘L Qs) P, P⟫ + ⟪H₀ (Qs P), D⟫ + ⟪H₀ D, P⟫|
        ≤ |⟪(H Y - H₀) P, P⟫| + |⟪(Qs ∘L H₀ ∘L Qs) P, P⟫| + |⟪H₀ (Qs P), D⟫| + |⟪H₀ D, P⟫| :=
          abs_add_four_le _ _ _ _
      _ ≤ ζ * ‖P‖ ^ 2 + l * ‖P‖ ^ 2 + ζ / 2 * ‖P‖ ^ 2 + ζ / 2 * ‖P‖ ^ 2 := by gcongr
      _ = (l + 2 * ζ) * ‖P‖ ^ 2 := by ring
      _ ≤ Λ * ‖P‖ ^ 2 := by
          gcongr
          linarith
  have hdiff : ∀ s ∈ Icc (0 : ℝ) T, ⟪G X, P⟫ - ⟪G (X - s • P), P⟫ ≤ Λ * s * ‖P‖ ^ 2 := by
    intro s hs
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := s)
      (f := fun s => ⟪G (X - s • P), P⟫) (f' := fun s => -⟪H (X - s • P) P, P⟫)
      (C := Λ * ‖P‖ ^ 2)
      (fun u hu => (hw u ⟨hu.1, hu.2.trans hs.2⟩).hasDerivWithinAt)
      (fun u hu => hbound u ⟨hu.1, hu.2.le.trans hs.2⟩) s (right_mem_Icc.2 hs.1)
    simp only [zero_smul, sub_zero] at h
    rw [Real.norm_eq_abs] at h
    have h2 := (abs_le.1 h).1
    linarith
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (X - s • P)) (-⟪G (X - s • P), P⟫) s := fun s => by
    have h1 := hasDerivAt_loss_line hgrad X (-P) s
    simpa [sub_eq_add_neg, smul_neg, inner_neg_right] using h1
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f X - s * ⟪G X, P⟫ + Λ / 2 * s ^ 2 * ‖P‖ ^ 2)
      (-⟪G X, P⟫ + Λ * s * ‖P‖ ^ 2) s := fun s => by
    have h := (((hasDerivAt_id' s).mul_const ⟪G X, P⟫).const_sub (f X)).add
      (((hasDerivAt_pow 2 s).const_mul (Λ / 2)).mul_const (‖P‖ ^ 2))
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := t)
    (f := fun s : ℝ => f (X - s • P)) (f' := fun s => -⟪G (X - s • P), P⟫)
    (fun s _ => (hφ s).continuousAt.continuousWithinAt)
    (fun s _ => (hφ s).hasDerivWithinAt)
    (B := fun s => f X - s * ⟪G X, P⟫ + Λ / 2 * s ^ 2 * ‖P‖ ^ 2)
    (B' := fun s => -⟪G X, P⟫ + Λ * s * ‖P‖ ^ 2) (by simp)
    (fun s _ => (hB s).continuousAt.continuousWithinAt)
    (fun s _ => (hB s).hasDerivWithinAt)
    (fun s hs => by
      have := hdiff s ⟨hs.1, hs.2.le.trans ht.2⟩
      linarith)
    (right_mem_Icc.2 ht.1)
  exact key

open Curvature in
/-- The projectors onto the column and row spaces depend Lipschitz continuously on the point near
`X∗ = Us Ss Vsᵀ` of rank `k`: for all `Y = U S Vᵀ` with `k` orthonormal columns in `U`, `V`, also
rank-deficient.  (arXiv 2306.00897.) -/
theorem exists_proj_lipschitz {Us : Matrix m (Fin k) ℝ} {Ss : Matrix (Fin k) (Fin k) ℝ}
    {Vs : Matrix n (Fin k) ℝ} (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Matrix m (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
      (V : Matrix n (Fin k) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 →
      ‖Us * Usᵀ - U * Uᵀ‖ ≤ C * ‖Us * Ss * Vsᵀ - U * S * Vᵀ‖ ∧
      ‖Vs * Vsᵀ - V * Vᵀ‖ ≤ C * ‖Us * Ss * Vsᵀ - U * S * Vᵀ‖ := by
  classical
  refine ⟨√2 * specNorm (Vs * Ss⁻¹ * Usᵀ), mul_nonneg (Real.sqrt_nonneg _) (specNorm_nonneg _),
    fun U S V hU hV => ?_⟩
  have hXG : Us * Ss * Vsᵀ * (Vs * Ss⁻¹ * Usᵀ) = Us * Usᵀ := factor_mul_ginv hVs hSs
  have hGX : Vs * Ss⁻¹ * Usᵀ * (Us * Ss * Vsᵀ) = Vs * Vsᵀ := ginv_mul_factor hUs hSs
  have h1 := norm_colProj_sub_le_of_trace (X := Us * Ss * Vsᵀ) (G := Vs * Ss⁻¹ * Usᵀ)
    (Y := U * S * Vᵀ) (P := U * Uᵀ) (factor_ginv_factor hUs hVs hSs)
    (by rw [hXG]; exact (isOrthProjMat_mul_transpose hUs).symm) (isOrthProjMat_mul_transpose hU)
    (colProj_mul_factor hU) (by rw [hXG, trace_mul_transpose hUs, trace_mul_transpose hU])
  have h2 := norm_rowProj_sub_le_of_trace (X := Us * Ss * Vsᵀ) (G := Vs * Ss⁻¹ * Usᵀ)
    (Y := U * S * Vᵀ) (P := V * Vᵀ) (factor_ginv_factor hUs hVs hSs)
    (by rw [hGX]; exact (isOrthProjMat_mul_transpose hVs).symm) (isOrthProjMat_mul_transpose hV)
    (factor_mul_rowProj hV) (by rw [hGX, trace_mul_transpose hVs, trace_mul_transpose hV])
  rw [hXG] at h1
  rw [hGX] at h2
  exact ⟨h1, h2⟩

/-- `Admissible` depends on the smoothness constant only through fixed step sizes. -/
lemma StepRule.Admissible.of_not_fixed {r : StepRule} {Λ Λ' d h : ℝ} {φ : ℝ → ℝ}
    (hr : r.Admissible Λ d φ h) (hnf : ∀ α, r ≠ StepRule.fixed α) : r.Admissible Λ' d φ h := by
  cases r with
  | fixed α => exact absurd rfl (hnf α)
  | exact => exact hr
  | armijo hbar β γ => exact hr

/-- Restricted smoothness along the two blocks at a point `Y = U S Vᵀ` near `X∗ = Us Ss Vsᵀ`.
(arXiv 2306.00897.) -/
theorem local_descent_blocks (hgrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X)
    {Us : Matrix m (Fin k) ℝ} {Ss : Matrix (Fin k) (Fin k) ℝ} {Vs : Matrix n (Fin k) ℝ}
    (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hH : ∀ᶠ X in 𝓝 (Us * Ss * Vsᵀ), HasFDerivAt G (H X) X)
    (hHc : ContinuousAt H (Us * Ss * Vsᵀ)) {Λ T : ℝ}
    (hΛ₁ : ‖rightProj Vs ∘L H (Us * Ss * Vsᵀ) ∘L rightProj Vs‖ < Λ)
    (hΛ₂ : ‖leftProj Us ∘L H (Us * Ss * Vsᵀ) ∘L leftProj Us‖ < Λ) (hT : 0 < T) :
    ∃ δ > 0, ∀ (U : Matrix m (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ) (V : Matrix n (Fin k) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → ‖U * S * Vᵀ - Us * Ss * Vsᵀ‖ < δ →
      ∀ Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ, (Q = rightProj V ∨ Q = leftProj U) →
      ‖Q (G (U * S * Vᵀ))‖ < δ → ∀ t ∈ Icc 0 T,
        f (U * S * Vᵀ - t • Q (G (U * S * Vᵀ))) ≤
          f (U * S * Vᵀ) - t * ‖Q (G (U * S * Vᵀ))‖ ^ 2 +
            Λ / 2 * t ^ 2 * ‖Q (G (U * S * Vᵀ))‖ ^ 2 := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := local_descent hgrad hH hHc (isOrthProj_rightProj hVs) hΛ₁ hT
  obtain ⟨δ₂, hδ₂, h₂⟩ := local_descent hgrad hH hHc (isOrthProj_leftProj hUs) hΛ₂ hT
  obtain ⟨C, hC, hlip⟩ := exists_proj_lipschitz hUs hVs hSs
  set δ₀ := min δ₁ δ₂ with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min hδ₁ hδ₂
  set δ := min δ₀ (δ₀ / (C + 1)) with hδ
  have hδ0 : 0 < δ := lt_min hδ₀0 (by positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hCδ : C * δ ≤ δ₀ := by
    have h1 : (C + 1) * δ ≤ δ₀ := by
      calc (C + 1) * δ ≤ (C + 1) * (δ₀ / (C + 1)) := by gcongr; exact min_le_right _ _
        _ = δ₀ := by field_simp
    nlinarith
  refine ⟨δ, hδ0, fun U S V hU hV hX Q hQ hP t ht => ?_⟩
  set Y := U * S * Vᵀ with hY
  obtain ⟨hl1, hl2⟩ := hlip U S V hU hV
  have hsmall : C * ‖Us * Ss * Vsᵀ - Y‖ ≤ δ₀ := by
    rw [norm_sub_rev]
    exact (mul_le_mul_of_nonneg_left hX.le hC).trans hCδ
  rcases hQ with rfl | rfl
  · have hclose : ∀ Z : Matrix m n ℝ, ‖rightProj V Z - rightProj Vs Z‖ ≤ δ₁ * ‖Z‖ := fun Z => by
      have e : rightProj V Z - rightProj Vs Z = Z * (V * Vᵀ - Vs * Vsᵀ) := by
        rw [rightProj_apply', rightProj_apply', Matrix.mul_sub]
      have h3 : ‖V * Vᵀ - Vs * Vsᵀ‖ ≤ δ₁ := by
        rw [norm_sub_rev]
        exact hl2.trans (hsmall.trans (min_le_left _ _))
      rw [e]
      calc ‖Z * (V * Vᵀ - Vs * Vsᵀ)‖ ≤ ‖Z‖ * ‖V * Vᵀ - Vs * Vsᵀ‖ :=
            Frobenius.norm_mul_le Z (V * Vᵀ - Vs * Vsᵀ)
        _ ≤ ‖Z‖ * δ₁ := by gcongr
        _ = δ₁ * ‖Z‖ := mul_comm _ _
    have h := h₁ Y _ (rightProj V) (hX.trans_le (hδle.trans (min_le_left _ _)))
      (hP.trans_le (hδle.trans (min_le_left _ _))) ((isOrthProj_rightProj hV).idem _) hclose t ht
    rwa [real_inner_comm, (isOrthProj_rightProj hV).inner_self_apply] at h
  · have hclose : ∀ Z : Matrix m n ℝ, ‖leftProj U Z - leftProj Us Z‖ ≤ δ₂ * ‖Z‖ := fun Z => by
      have e : leftProj U Z - leftProj Us Z = (U * Uᵀ - Us * Usᵀ) * Z := by
        rw [leftProj_apply, leftProj_apply, Matrix.sub_mul]
      have h3 : ‖U * Uᵀ - Us * Usᵀ‖ ≤ δ₂ := by
        rw [norm_sub_rev]
        exact hl1.trans (hsmall.trans (min_le_right _ _))
      rw [e]
      calc ‖(U * Uᵀ - Us * Usᵀ) * Z‖ ≤ ‖U * Uᵀ - Us * Usᵀ‖ * ‖Z‖ :=
            Frobenius.norm_mul_le (U * Uᵀ - Us * Usᵀ) Z
        _ ≤ δ₂ * ‖Z‖ := by gcongr
    have h := h₂ Y _ (leftProj U) (hX.trans_le (hδle.trans (min_le_right _ _)))
      (hP.trans_le (hδle.trans (min_le_right _ _))) ((isOrthProj_leftProj hU).idem _) hclose t ht
    rwa [real_inner_comm, (isOrthProj_leftProj hU).inner_self_apply] at h

end LocalSmooth

/-- The constant `λ∗` of Theorem 3.8: the larger of the operator norms of `P_V H P_V`,
`P_U H P_U`. -/
noncomputable def blockConst (H₀ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (U : Matrix m (Fin k) ℝ)
    (V : Matrix n (Fin k) ℝ) : ℝ :=
  max ‖rightProj V ∘L H₀ ∘L rightProj V‖ ‖leftProj U ∘L H₀ ∘L leftProj U‖

/-- `λ∗ ≤ ‖H₀‖` (so `λ∗ ≤ λ`, Theorem 3.8). -/
lemma blockConst_le {H₀ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {U : Matrix m (Fin k) ℝ}
    {V : Matrix n (Fin k) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) : blockConst H₀ U V ≤ ‖H₀‖ := by
  have key : ∀ {Q : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}, IsOrthProj Q → ‖Q ∘L H₀ ∘L Q‖ ≤ ‖H₀‖ := by
    intro Q hQ
    have h1 := hQ.opNorm_le
    calc ‖Q ∘L H₀ ∘L Q‖ ≤ ‖Q‖ * ‖H₀ ∘L Q‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖H₀‖ * ‖Q‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖H₀‖ * 1) := by gcongr
      _ = _ := by ring
  exact max_le (key (isOrthProj_rightProj hV)) (key (isOrthProj_leftProj hU))

/-- `λ∗_min ≤ λ∗` (Theorem 3.8): the matrix `X∗` lies in `T_{V∗}`, where the Weingarten term of the
Riemannian Hessian vanishes. -/
lemma le_blockConst_of_posDef {g : Matrix m n ℝ} {H₀ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    {U : Matrix m (Fin k) ℝ} {S : Matrix (Fin k) (Fin k) ℝ} {V : Matrix n (Fin k) ℝ} {μ : ℝ}
    (hk : 0 < k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hpd : ∀ ξ, tangentProj U V ξ = ξ → μ * ‖ξ‖ ^ 2 ≤ riemHess g H₀ U S V ξ) :
    μ ≤ blockConst H₀ U V := by
  set Xs := U * S * Vᵀ with hXs
  have hne : Xs ≠ 0 := by
    intro h0
    have h1 : S = Uᵀ * Xs * V := by
      calc S = (Uᵀ * U) * S * (Vᵀ * V) := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by rw [hXs]; simp only [Matrix.mul_assoc]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at h1
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    rw [h1, Matrix.det_zero] at hS
    exact not_isUnit_zero hS
  have hpos : 0 < ‖Xs‖ ^ 2 := by
    have := norm_pos_iff.2 hne
    positivity
  have h1 := hpd Xs (tangentProj_mul_mul_transpose hU V S)
  have h2 : riemHess g H₀ U S V Xs = ⟪H₀ Xs, Xs⟫ := by
    have e : Xs * V * S⁻¹ * Uᵀ * Xs = U * (S * Vᵀ * V * S⁻¹ * Uᵀ * Xs) := by
      rw [hXs]; simp only [Matrix.mul_assoc]
    rw [riemHess, e, normal_mul_left hU V, inner_zero_right, mul_zero, add_zero]
  rw [h2] at h1
  have hR := isOrthProj_rightProj (m := m) hV
  have hfix : rightProj V Xs = Xs := by
    rw [rightProj_apply, hXs]
    calc U * S * Vᵀ * V * Vᵀ = U * S * (Vᵀ * V) * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  have h3 : ⟪H₀ Xs, Xs⟫ ≤ blockConst H₀ U V * ‖Xs‖ ^ 2 := by
    have e : ⟪H₀ Xs, Xs⟫ = ⟪(rightProj V ∘L H₀ ∘L rightProj V) Xs, Xs⟫ := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [hfix, hR.symm, hfix]
    rw [e]
    calc ⟪(rightProj V ∘L H₀ ∘L rightProj V) Xs, Xs⟫
        ≤ ‖(rightProj V ∘L H₀ ∘L rightProj V) Xs‖ * ‖Xs‖ := real_inner_le_norm _ _
      _ ≤ ‖rightProj V ∘L H₀ ∘L rightProj V‖ * ‖Xs‖ * ‖Xs‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ blockConst H₀ U V * ‖Xs‖ * ‖Xs‖ := by
          gcongr
          exact le_max_left _ _
      _ = _ := by ring
  exact le_of_mul_le_mul_right (h1.trans h3) hpos

/-- The two root bounds from geometric bounds at every rate above `ρ₀`.  (arXiv 2306.00897.) -/
theorem limsups_of_rates {E : Type*} [NormedAddCommGroup E] {X : ℕ → E} {Xs : E} {a : ℕ → ℝ}
    {c₁ ρ₀ : ℝ} (hρ0 : 0 ≤ ρ₀) (hρ1 : ρ₀ < 1) (ha : ∀ ℓ, 0 ≤ a ℓ) (hc₁ : 0 < c₁)
    (key : ∀ q, ρ₀ < q → q < 1 → ∃ C, 0 ≤ C ∧ ∀ᶠ ℓ in atTop,
      a ℓ ≤ C * q ^ ℓ ∧ ‖X ℓ - Xs‖ ^ 2 ≤ c₁ * (C * q ^ ℓ)) :
    limsup (fun ℓ : ℕ => ‖X ℓ - Xs‖ ^ ((ℓ : ℝ)⁻¹)) atTop ≤ √ρ₀ ∧
      limsup (fun ℓ : ℕ => a ℓ ^ ((ℓ : ℝ)⁻¹)) atTop ≤ ρ₀ := by
  have hsq1 : √ρ₀ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  constructor
  · refine limsup_root_le_of_forall (Real.sqrt_nonneg _) hsq1 (fun ℓ => norm_nonneg _)
      fun q hq hq1 => ?_
    have hq0 : 0 < q := (Real.sqrt_nonneg _).trans_lt hq
    have hq2 : ρ₀ < q ^ 2 := (Real.sqrt_lt' hq0).1 hq
    have hq3 : q ^ 2 < 1 := by nlinarith
    obtain ⟨C, hC, hev⟩ := key (q ^ 2) hq2 hq3
    refine ⟨√(c₁ * C), Real.sqrt_nonneg _, ?_⟩
    filter_upwards [hev] with ℓ hℓ
    calc ‖X ℓ - Xs‖ = √(‖X ℓ - Xs‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(c₁ * C * (q ^ ℓ) ^ 2) := by
          refine Real.sqrt_le_sqrt (hℓ.2.trans (le_of_eq ?_))
          rw [← pow_mul, ← pow_mul, mul_comm 2 ℓ]
          ring
      _ = √(c₁ * C) * q ^ ℓ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  · refine limsup_root_le_of_forall hρ0 hρ1 ha fun q hq hq1 => ?_
    obtain ⟨C, hC, hev⟩ := key q hq hq1
    exact ⟨C, hC, hev.mono fun ℓ h => h.1⟩

section RefinedRate

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam : ℝ} {rule : ℕ → StepRule}
  {h : ℕ → ℝ} {U : ℕ → Matrix m (Fin k) ℝ} {S : ℕ → Matrix (Fin k) (Fin k) ℝ}
  {V : ℕ → Matrix n (Fin k) ℝ} {X : ℕ → Matrix m n ℝ} {Us : Matrix m (Fin k) ℝ}
  {Ss : Matrix (Fin k) (Fin k) ℝ} {Vs : Matrix n (Fin k) ℝ}
  {H : Matrix m n ℝ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ}

/-- The estimate (3.28): near the limit, with line search rules, the global constant `λ` in (3.15)
may be replaced by any `Λ > λ∗`.  (arXiv 2306.00897.) -/
theorem riem_local_decrease (hf : IsSmooth f G lam) (hrun : IsRiemRun f G lam rule h U S V X)
    (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hHev : ∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), HasFDerivAt G (H Y) Y)
    (hHc : ContinuousAt H (Us * Ss * Vsᵀ)) (hconv : Tendsto X atTop (𝓝 (Us * Ss * Vsᵀ)))
    (hP : Tendsto (fun ℓ => tangentProj (U ℓ) (V ℓ) (G (X ℓ))) atTop (𝓝 0)) {Λ T : ℝ}
    (hΛ : blockConst (H (Us * Ss * Vsᵀ)) Us Vs < Λ) (hΛ0 : 0 < Λ) (hT : 0 < T)
    (hreach : ∀ᶠ ℓ in atTop, (rule ℓ).reach Λ ≤ T)
    (hnf : ∀ᶠ ℓ in atTop, ∀ α, rule ℓ ≠ StepRule.fixed α) :
    ∀ᶠ ℓ in atTop, (rule ℓ).theta Λ / (2 * Λ) * ‖riemGrad G (X ℓ)‖ ^ 2 ≤
      f (X ℓ) - f (X (ℓ + 1)) := by
  obtain ⟨δ, hδ, hloc⟩ := local_descent_blocks hf.hasGrad hUs hVs hSs hHev hHc
    ((le_max_left _ _).trans_lt hΛ) ((le_max_right _ _).trans_lt hΛ) hT
  have ev1 : ∀ᶠ ℓ in atTop, ‖X ℓ - Us * Ss * Vsᵀ‖ < δ :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hconv).eventually (gt_mem_nhds hδ)
  have ev2 : ∀ᶠ ℓ in atTop, ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ < δ :=
    (tendsto_zero_iff_norm_tendsto_zero.1 hP).eventually (gt_mem_nhds hδ)
  filter_upwards [ev1, ev2, hreach, hnf] with ℓ h1 h2 h3 h4
  obtain ⟨hU, hV⟩ := hrun.orth ℓ
  have hXℓ := hrun.iter ℓ
  obtain ⟨-, -, Q, hQ, hit, hadm, hT₂, hle, hcase⟩ := (hrun.step ℓ).spec hU hV hXℓ
  have hsm : ‖Q (G (X ℓ))‖ < δ := hle.trans_lt h2
  have hadm' := hadm.of_not_fixed (Λ' := Λ) h4
  have hdec := StepRule.decrease (r := rule ℓ) (Λ := Λ) (d := ‖Q (G (X ℓ))‖ ^ 2)
    (φ := fun t => f (X ℓ - t • Q (G (X ℓ)))) hΛ0 (sq_nonneg _) (fun t h0 ht => by
      have h5 := hloc (U ℓ) (S ℓ) (V ℓ) hU hV (by rw [← hXℓ]; exact h1) Q hcase
        (by rw [← hXℓ]; exact hsm) t ⟨h0, ht.trans h3⟩
      rw [← hXℓ] at h5
      simpa only [zero_smul, sub_zero] using h5) hadm'
  simp only [zero_smul, sub_zero] at hdec
  rw [← hrun.iter (ℓ + 1)] at hit
  rw [hit]
  have hθ := StepRule.theta_pos hΛ0 hadm'
  have hg : ‖riemGrad G (X ℓ)‖ ≤ ‖tangentProj (U ℓ) (V ℓ) (G (X ℓ))‖ := by
    rw [hXℓ]; exact norm_riemGrad_le_tangentProj G hU hV
  have hg2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  calc (rule ℓ).theta Λ / (2 * Λ) * ‖riemGrad G (X ℓ)‖ ^ 2
      ≤ (rule ℓ).theta Λ / (2 * Λ) * (2 * ‖Q (G (X ℓ))‖ ^ 2) := by
        gcongr
        exact hg2.trans hT₂
    _ = (rule ℓ).theta Λ / Λ * ‖Q (G (X ℓ))‖ ^ 2 := by field_simp
    _ ≤ _ := hdec

/-- The common core of Theorem 3.8: `T₁ Λ` is a lower bound of `ϑ_ℓ` for the smoothness constant
`Λ`, for large `ℓ`.  (arXiv 2306.00897.) -/
theorem riemBlockDescent_refined_core (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hbdd : BddBelow (range f)) (hrun : IsRiemRun f G lam rule h U S V X) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑle : ∀ ℓ, ϑ ≤ (rule ℓ).theta lam) {hmax : ℝ} (hstep : ∀ ℓ, h ℓ ≤ hmax) (hk : 0 < k)
    (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hcluster : MapClusterPt (Us * Ss * Vsᵀ) atTop X)
    (hHev : ∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), HasFDerivAt G (H Y) Y)
    (hHc : ContinuousAt H (Us * Ss * Vsᵀ)) {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj Us Vs ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (Us * Ss * Vsᵀ)) (H (Us * Ss * Vsᵀ)) Us Ss Vs ξ)
    {T₁ : ℝ → ℝ} (hT₁c : ContinuousAt T₁ (blockConst (H (Us * Ss * Vsᵀ)) Us Vs))
    (hT₁pos : 0 < T₁ (blockConst (H (Us * Ss * Vsᵀ)) Us Vs))
    (hT₁half : T₁ (blockConst (H (Us * Ss * Vsᵀ)) Us Vs) ≤ 1 / 2)
    (hT₁le : ∀ Λ > blockConst (H (Us * Ss * Vsᵀ)) Us Vs,
      ∀ᶠ ℓ in atTop, T₁ Λ ≤ (rule ℓ).theta Λ)
    (hreach : ∀ Λ > blockConst (H (Us * Ss * Vsᵀ)) Us Vs,
      ∃ T > 0, ∀ᶠ ℓ in atTop, (rule ℓ).reach Λ ≤ T)
    (hnf : ∀ᶠ ℓ in atTop, ∀ α, rule ℓ ≠ StepRule.fixed α) :
    limsup (fun ℓ : ℕ => ‖X ℓ - Us * Ss * Vsᵀ‖ ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        √(1 - T₁ (blockConst (H (Us * Ss * Vsᵀ)) Us Vs) * μ /
          blockConst (H (Us * Ss * Vsᵀ)) Us Vs) ∧
      limsup (fun ℓ : ℕ => (f (X ℓ) - f (Us * Ss * Vsᵀ)) ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        1 - T₁ (blockConst (H (Us * Ss * Vsᵀ)) Us Vs) * μ /
          blockConst (H (Us * Ss * Vsᵀ)) Us Vs := by
  set Xs := Us * Ss * Vsᵀ with hXs
  set l := blockConst (H Xs) Us Vs with hl
  have hHs : HasFDerivAt G (H Xs) Xs := hHev.self_of_nhds
  obtain ⟨hconv, -⟩ := riemBlockDescent_linear_rate hf hlam hbdd hrun hϑ hϑle hstep hk hUs hVs hSs
    hcluster hHs hμ hpd
  obtain ⟨hanti, fstar, hlim, -, hP, -, hcl, -, -, -⟩ :=
    riemBlockDescent_convergence hf hlam hbdd hrun hϑ hϑle
  obtain ⟨hfs, hcrit⟩ := hcl Xs hcluster
  subst hfs
  have hμl : μ ≤ l := le_blockConst_of_posDef hk hUs hVs hSs hpd
  have hl0 : 0 < l := hμ.trans_le hμl
  have hρ1 : 0 < T₁ l * μ / l := by positivity
  have hρ2 : T₁ l * μ / l ≤ 1 / 2 := by
    rw [div_le_iff₀ hl0]
    exact mul_le_mul hT₁half hμl hμ.le (by norm_num)
  set ρ₀ := 1 - T₁ l * μ / l with hρ₀
  have hρ0 : 0 < ρ₀ := by rw [hρ₀]; linarith
  have hρlt : ρ₀ < 1 := by rw [hρ₀]; linarith
  have hfl : ∀ ℓ, 0 ≤ f (X ℓ) - f Xs := fun ℓ => sub_nonneg.2 (hanti.le_of_tendsto hlim ℓ)
  have ha : Tendsto (fun ℓ => f (X ℓ) - f Xs) atTop (𝓝 0) := by
    simpa using hlim.sub_const (f Xs)
  have hmove : Tendsto (fun ℓ => X (ℓ + 1) - X ℓ) atTop (𝓝 0) := by
    simpa using (hconv.comp (tendsto_add_atTop_nat 1)).sub hconv
  refine limsups_of_rates hρ0.le hρlt hfl (c₁ := 8 / μ) (by positivity) fun q hq hq1 => ?_
  have h1q : 0 < 1 - q := sub_pos.2 hq1
  have hq0 : 0 < q := hρ0.trans hq
  have hcc : ContinuousAt (fun Λ => T₁ Λ / (2 * Λ) * (2 * μ)) l := by
    refine ContinuousAt.mul (ContinuousAt.div hT₁c (by fun_prop) (by positivity)) (by fun_prop)
  have hval : 1 - q < T₁ l / (2 * l) * (2 * μ) := by
    have e : T₁ l / (2 * l) * (2 * μ) = T₁ l * μ / l := by field_simp
    rw [e]
    rw [hρ₀] at hq
    linarith
  have hev := (hcc.eventually (lt_mem_nhds hval)).filter_mono (nhdsWithin_le_nhds (s := Ioi l))
  obtain ⟨Λ, hΛ1, hΛ2⟩ := (hev.and self_mem_nhdsWithin).exists
  have hΛ : l < Λ := hΛ2
  have hΛ0 : 0 < Λ := hl0.trans hΛ
  set c₀ := T₁ Λ / (2 * Λ) with hc₀
  have hc₀0 : 0 < c₀ := by
    have h3 : 0 < c₀ * (2 * μ) := h1q.trans hΛ1
    exact (mul_pos_iff_of_pos_right (by positivity)).1 h3
  set C₀ := c₀ / (1 - q) with hC₀
  have hC₀0 : 0 < C₀ := by positivity
  have hε : 0 < C₀ - 1 / (2 * μ) := by
    have e1 : C₀ - 1 / (2 * μ) = (c₀ * (2 * μ) - (1 - q)) / (2 * μ * (1 - q)) := by
      rw [hC₀]; field_simp
    rw [e1]
    exact div_pos (sub_pos.2 hΛ1) (by positivity)
  have hpl := riemannian_pl (f := f) hf.hasGrad hUs hVs hSs hcrit hHs hμ hpd hε
  rw [← hXs] at hpl
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hpl
  obtain ⟨T, hT, hTle⟩ := hreach Λ hΛ
  have hdec := riem_local_decrease hf hrun hUs hVs hSs hHev hHc hconv hP hΛ hΛ0 hT hTle hnf
  have hrank : ∀ ℓ, (X ℓ).rank ≤ k := fun ℓ => by
    rw [hrun.iter ℓ]; exact rank_mul_mul_transpose_le _ _ _
  have hplY : ∀ ℓ, ‖X ℓ - Xs‖ < r → f (X ℓ) - f Xs ≤ C₀ * ‖riemGrad G (X ℓ)‖ ^ 2 ∧
      ‖X ℓ - Xs‖ ^ 2 ≤ 8 / μ * (f (X ℓ) - f Xs) := fun ℓ hℓ => by
    have h4 := hball (X ℓ) (by rwa [Metric.mem_ball, dist_eq_norm]) (hrank ℓ)
    rwa [add_sub_cancel] at h4
  have hcontr : ∀ᶠ ℓ in atTop, ‖X ℓ - Xs‖ < r →
      f (X (ℓ + 1)) - f Xs ≤ q * (f (X ℓ) - f Xs) := by
    filter_upwards [hdec, hT₁le Λ hΛ] with ℓ h1 h2 hℓ
    have h3 : c₀ * ‖riemGrad G (X ℓ)‖ ^ 2 ≤ f (X ℓ) - f (X (ℓ + 1)) := by
      refine le_trans ?_ h1
      rw [hc₀]
      gcongr
    have h4 := contraction_of_pl (a := f (X ℓ) - f Xs) (a' := f (X (ℓ + 1)) - f Xs)
      (c := c₀) (g₂ := ‖riemGrad G (X ℓ)‖ ^ 2) hc₀0.le hC₀0 (hplY ℓ hℓ).1 (by linarith only [h3])
    have e : 1 - c₀ / C₀ = q := by
      rw [hC₀]; field_simp; ring
    rwa [e] at h4
  exact (local_contraction hr (by positivity) hq0 hfl ha (fun ℓ hℓ => (hplY ℓ hℓ).2) hcontr hmove
    hcluster).2

/-- **Theorem 3.8** (arXiv 2306.00897), mixed rules.  Under the assumptions of
`riemBlockDescent_linear_rate`, let `∇f` be differentiable near `X∗` with derivative `H` continuous
at `X∗`, and let exact line search or backtracking with parameters `h̄, β, γ` be used except for
finitely many steps.  With `λ∗ = max {‖P_{V∗} H(X∗) P_{V∗}‖, ‖P_{U∗} H(X∗) P_{U∗}‖} ≤ λ` and
`ϑ∗ = min {2 β γ (1 - γ), λ∗ γ h̄}`:
`limsup ‖X_ℓ - X∗‖^{1/ℓ} ≤ (1 - ϑ∗ μ / λ∗)^{1/2} < 1`,
`limsup (f(X_ℓ) - f(X∗))^{1/ℓ} ≤ 1 - ϑ∗ μ / λ∗`.
As in `riemBlockDescent_linear_rate` we assume `h_ℓ ≤ hmax`, which is only a restriction for exact
line search. -/
theorem riemBlockDescent_refined_rate (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hbdd : BddBelow (range f)) (hrun : IsRiemRun f G lam rule h U S V X) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑle : ∀ ℓ, ϑ ≤ (rule ℓ).theta lam) {hmax : ℝ} (hstep : ∀ ℓ, h ℓ ≤ hmax) (hk : 0 < k)
    (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hcluster : MapClusterPt (Us * Ss * Vsᵀ) atTop X)
    (hHev : ∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), HasFDerivAt G (H Y) Y)
    (hHc : ContinuousAt H (Us * Ss * Vsᵀ)) {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj Us Vs ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (Us * Ss * Vsᵀ)) (H (Us * Ss * Vsᵀ)) Us Ss Vs ξ)
    {hbar β γ : ℝ} (hb : 0 < hbar) (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hmix : ∀ᶠ ℓ in atTop, rule ℓ = StepRule.exact ∨ rule ℓ = StepRule.armijo hbar β γ) :
    blockConst (H (Us * Ss * Vsᵀ)) Us Vs ≤ lam ∧
      min (2 * β * γ * (1 - γ)) (blockConst (H (Us * Ss * Vsᵀ)) Us Vs * γ * hbar) * μ /
        blockConst (H (Us * Ss * Vsᵀ)) Us Vs > 0 ∧
      limsup (fun ℓ : ℕ => ‖X ℓ - Us * Ss * Vsᵀ‖ ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        √(1 - min (2 * β * γ * (1 - γ)) (blockConst (H (Us * Ss * Vsᵀ)) Us Vs * γ * hbar) * μ /
          blockConst (H (Us * Ss * Vsᵀ)) Us Vs) ∧
      limsup (fun ℓ : ℕ => (f (X ℓ) - f (Us * Ss * Vsᵀ)) ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        1 - min (2 * β * γ * (1 - γ)) (blockConst (H (Us * Ss * Vsᵀ)) Us Vs * γ * hbar) * μ /
          blockConst (H (Us * Ss * Vsᵀ)) Us Vs := by
  set Xs := Us * Ss * Vsᵀ with hXs
  have hHs : HasFDerivAt G (H Xs) Xs := hHev.self_of_nhds
  have hμl : μ ≤ blockConst (H Xs) Us Vs := le_blockConst_of_posDef hk hUs hVs hSs hpd
  have hl0 : 0 < blockConst (H Xs) Us Vs := hμ.trans_le hμl
  have h1g : 0 < 1 - γ := sub_pos.2 hγ1
  have hhalf : 2 * β * γ * (1 - γ) ≤ 1 / 2 := by
    have h1 : γ * (1 - γ) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * γ - 1)]
    have h2 : 0 < γ * (1 - γ) := mul_pos hγ h1g
    nlinarith
  have hT₁c : ContinuousAt (fun Λ : ℝ => min (2 * β * γ * (1 - γ)) (Λ * γ * hbar))
      (blockConst (H Xs) Us Vs) := by fun_prop
  have hpos : 0 < min (2 * β * γ * (1 - γ)) (blockConst (H Xs) Us Vs * γ * hbar) :=
    lt_min (by positivity) (by positivity)
  have hHle : ‖H Xs‖ ≤ lam := hHs.le_of_lip' hlam.le
    (Eventually.of_forall fun Y => hf.lipschitz Y Xs)
  have hnf : ∀ᶠ ℓ in atTop, ∀ α, rule ℓ ≠ StepRule.fixed α := by
    filter_upwards [hmix] with ℓ h1 α h2
    rcases h1 with h1 | h1 <;> rw [h1] at h2 <;> cases h2
  have hres := riemBlockDescent_refined_core (T₁ := fun Λ => min (2 * β * γ * (1 - γ))
    (Λ * γ * hbar)) hf hlam hbdd hrun hϑ hϑle hstep hk hUs hVs hSs hcluster hHev hHc hμ hpd
    hT₁c hpos ((min_le_left _ _).trans hhalf) (fun Λ _ => by
      filter_upwards [hmix] with ℓ h1
      rcases h1 with h1 | h1 <;> rw [h1]
      · exact (min_le_left _ _).trans hhalf
      · exact le_rfl)
    (fun Λ hΛ => by
      have hΛ0 : 0 < Λ := hl0.trans hΛ
      refine ⟨max hbar (1 / Λ), lt_max_of_lt_left hb, ?_⟩
      filter_upwards [hmix] with ℓ h1
      rcases h1 with h1 | h1 <;> rw [h1]
      · exact le_max_right _ _
      · exact le_max_left _ _) hnf
  exact ⟨(blockConst_le hUs hVs).trans hHle, by positivity, hres⟩

/-- **Theorem 3.8** (arXiv 2306.00897), exact line search: if exact line search is used except for
finitely many steps, the estimates hold with `ϑ∗ = 1/2`.  As in `riemBlockDescent_linear_rate` we
assume `h_ℓ ≤ hmax`. -/
theorem riemBlockDescent_refined_rate_exact (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hbdd : BddBelow (range f)) (hrun : IsRiemRun f G lam rule h U S V X) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑle : ∀ ℓ, ϑ ≤ (rule ℓ).theta lam) {hmax : ℝ} (hstep : ∀ ℓ, h ℓ ≤ hmax) (hk : 0 < k)
    (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hcluster : MapClusterPt (Us * Ss * Vsᵀ) atTop X)
    (hHev : ∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), HasFDerivAt G (H Y) Y)
    (hHc : ContinuousAt H (Us * Ss * Vsᵀ)) {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj Us Vs ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (Us * Ss * Vsᵀ)) (H (Us * Ss * Vsᵀ)) Us Ss Vs ξ)
    (hexact : ∀ᶠ ℓ in atTop, rule ℓ = StepRule.exact) :
    limsup (fun ℓ : ℕ => ‖X ℓ - Us * Ss * Vsᵀ‖ ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        √(1 - 1 / 2 * μ / blockConst (H (Us * Ss * Vsᵀ)) Us Vs) ∧
      limsup (fun ℓ : ℕ => (f (X ℓ) - f (Us * Ss * Vsᵀ)) ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        1 - 1 / 2 * μ / blockConst (H (Us * Ss * Vsᵀ)) Us Vs := by
  have hμl := le_blockConst_of_posDef hk hUs hVs hSs hpd
  have hl0 := hμ.trans_le hμl
  have hnf : ∀ᶠ ℓ in atTop, ∀ α, rule ℓ ≠ StepRule.fixed α := by
    filter_upwards [hexact] with ℓ h1 α h2
    rw [h1] at h2
    cases h2
  exact riemBlockDescent_refined_core (T₁ := fun _ => 1 / 2) hf hlam hbdd hrun hϑ hϑle hstep hk hUs
    hVs hSs hcluster hHev hHc hμ hpd continuousAt_const (by norm_num) le_rfl
    (fun Λ _ => by
      filter_upwards [hexact] with ℓ h1
      rw [h1]
      exact le_rfl)
    (fun Λ hΛ => by
      have hΛ0 := hl0.trans hΛ
      refine ⟨1 / Λ, by positivity, ?_⟩
      filter_upwards [hexact] with ℓ h1
      rw [h1]
      exact le_rfl) hnf

end RefinedRate

/-! ### Local linear convergence of ALS -/

/-- Strong convexity with constant `σ`, in the form of Section 3.5. -/
def IsStronglyConvex (f : Matrix m n ℝ → ℝ) (G : Matrix m n ℝ → Matrix m n ℝ) (σ : ℝ) : Prop :=
  ∀ X Y, f X + ⟪G X, Y - X⟫ + σ / 2 * ‖Y - X‖ ^ 2 ≤ f Y

/-- A strongly convex function is bounded below. -/
lemma IsStronglyConvex.bddBelow {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {σ : ℝ}
    (hsc : IsStronglyConvex f G σ) (hσ : 0 < σ) : BddBelow (range f) := by
  refine ⟨f 0 - ‖G 0‖ ^ 2 / (2 * σ), ?_⟩
  rintro _ ⟨Y, rfl⟩
  have h1 := hsc 0 Y
  rw [sub_zero] at h1
  have h2 : -(‖G 0‖ * ‖Y‖) ≤ ⟪G 0, Y⟫ := by
    have := abs_real_inner_le_norm (G 0) Y
    linarith [neg_abs_le ⟪G 0, Y⟫]
  have h3 : ‖G 0‖ ^ 2 / (2 * σ) + σ / 2 * ‖Y‖ ^ 2 - ‖G 0‖ * ‖Y‖ =
      (‖G 0‖ - σ * ‖Y‖) ^ 2 / (2 * σ) := by
    field_simp
    ring
  have h4 : 0 ≤ (‖G 0‖ - σ * ‖Y‖) ^ 2 / (2 * σ) := by positivity
  linarith

/-- The half-step sequence `X̃` of Section 3.5: `X̃_{2ℓ} = X_ℓ` and `X̃_{2ℓ+1} = X_{ℓ+1/2}`. -/
def alsHalf (U : ℕ → Matrix m (Fin k) ℝ) (V Vq : ℕ → Matrix n (Fin k) ℝ)
    (Uh : ℕ → Matrix m (Fin k) ℝ) (i : ℕ) : Matrix m n ℝ :=
  if Even i then U (i / 2) * (V (i / 2))ᵀ else Uh (i / 2) * (Vq (i / 2))ᵀ

section ALSLocal

variable {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {lam σ : ℝ}
  {U : ℕ → Matrix m (Fin k) ℝ} {V Vq : ℕ → Matrix n (Fin k) ℝ} {Uh : ℕ → Matrix m (Fin k) ℝ}
  {Us : Matrix m (Fin k) ℝ} {Ss : Matrix (Fin k) (Fin k) ℝ} {Vs : Matrix n (Fin k) ℝ}
  {H : Matrix m n ℝ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ}

omit [Fintype m] [Fintype n] in
/-- `X̃_{2c} = X_c`. -/
lemma alsHalf_even (c : ℕ) : alsHalf U V Vq Uh (2 * c) = U c * (V c)ᵀ := by
  simp [alsHalf]

omit [Fintype m] [Fintype n] in
/-- `X̃_{2c+1} = X_{c+1/2}`. -/
lemma alsHalf_odd (c : ℕ) : alsHalf U V Vq Uh (2 * c + 1) = Uh c * (Vq c)ᵀ := by
  have h1 : (2 * c + 1) / 2 = c := by omega
  have h2 : ¬ Even (2 * c + 1) := by simp
  simp [alsHalf, h1, h2]

/-- The minimizers of the half-steps are stationary on their subspaces.  (arXiv 2306.00897.) -/
theorem als_stationary (hf : IsSmooth f G lam) (hlam : 0 < lam) (hrun : IsALSRun f U V Vq Uh)
    (ℓ : ℕ) : G (Uh ℓ * (Vq ℓ)ᵀ) * Vq ℓ = 0 ∧
      (U (ℓ + 1))ᵀ * G (U (ℓ + 1) * (V (ℓ + 1))ᵀ) = 0 := by
  obtain ⟨hQU, -⟩ := hrun.qr_U ℓ
  obtain ⟨hQV, -⟩ := hrun.qr_V ℓ
  have hc : 0 < 1 / (2 * lam) := by positivity
  have key : ∀ {x : ℝ}, 1 / (2 * lam) * x ^ 2 ≤ 0 → 0 ≤ x → x = 0 := fun {x} h h0 => by
    have h1 : x ^ 2 ≤ 0 := by
      by_contra hne
      have := mul_pos hc (not_le.1 hne)
      linarith
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _))
  have h0 := decrease_of_min_right hf hlam hQV (X := Uh ℓ * (Vq ℓ)ᵀ) rfl (hrun.argmin_U ℓ)
  have h0' := decrease_of_min_left hf hlam hQU (X := U (ℓ + 1) * (V (ℓ + 1))ᵀ) rfl
    (hrun.argmin_V ℓ)
  rw [sub_self, norm_rightProj_eq hQV] at h0
  rw [sub_self, ← norm_transpose_mul_eq hQU] at h0'
  exact ⟨norm_eq_zero.1 (key h0 (norm_nonneg _)), norm_eq_zero.1 (key h0' (norm_nonneg _))⟩

/-- `f(X̃_ℓ) - f(X̃_{ℓ+1}) ≥ σ / 2 ‖X̃_ℓ - X̃_{ℓ+1}‖²`, from the proof of Theorem 3.10.
(arXiv 2306.00897.) -/
theorem als_move (hf : IsSmooth f G lam) (hlam : 0 < lam) (hsc : IsStronglyConvex f G σ)
    (hrun : IsALSRun f U V Vq Uh) (i : ℕ) :
    σ / 2 * ‖alsHalf U V Vq Uh (i + 1) - alsHalf U V Vq Uh i‖ ^ 2 ≤
      f (alsHalf U V Vq Uh i) - f (alsHalf U V Vq Uh (i + 1)) := by
  obtain ⟨c, hc | hc⟩ := Nat.even_or_odd' i
  · subst hc
    rw [alsHalf_even, alsHalf_odd]
    obtain ⟨h1, -⟩ := als_stationary hf hlam hrun c
    obtain ⟨-, T, hT⟩ := hrun.qr_V c
    have hX : U c * (V c)ᵀ - Uh c * (Vq c)ᵀ = (U c * Tᵀ - Uh c) * (Vq c)ᵀ := by
      rw [hT, Matrix.transpose_mul, Matrix.sub_mul, Matrix.mul_assoc]
    have h2 := hsc (Uh c * (Vq c)ᵀ) (U c * (V c)ᵀ)
    rw [hX, Frobenius.inner_mul_right', Matrix.transpose_transpose, h1, inner_zero_left, add_zero,
      ← hX, norm_sub_rev] at h2
    linarith
  · subst hc
    rw [show 2 * c + 1 + 1 = 2 * (c + 1) by ring, alsHalf_even, alsHalf_odd]
    obtain ⟨-, h1⟩ := als_stationary hf hlam hrun c
    obtain ⟨-, T, hT⟩ := hrun.qr_U c
    have hX : Uh c * (Vq c)ᵀ - U (c + 1) * (V (c + 1))ᵀ =
        U (c + 1) * (T * (Vq c)ᵀ - (V (c + 1))ᵀ) := by
      rw [hT, Matrix.mul_sub, Matrix.mul_assoc]
    have h2 := hsc (U (c + 1) * (V (c + 1))ᵀ) (Uh c * (Vq c)ᵀ)
    rw [hX, Frobenius.inner_mul_left', h1, inner_zero_left, add_zero, ← hX, norm_sub_rev] at h2
    linarith

/-- (3.29) for the sequence `X̃`, at all half-steps but the first.  (arXiv 2306.00897.) -/
theorem als_half_decrease (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hrun : IsALSRun f U V Vq Uh) {i : ℕ} (hi : 1 ≤ i) :
    1 / (2 * lam) * ‖riemGrad G (alsHalf U V Vq Uh i)‖ ^ 2 ≤
      f (alsHalf U V Vq Uh i) - f (alsHalf U V Vq Uh (i + 1)) := by
  obtain ⟨c, hc | hc⟩ := Nat.even_or_odd' i
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    subst hc
    rw [show 2 * (c + 1) + 1 = 2 * (c + 1) + 1 from rfl, alsHalf_even, alsHalf_odd]
    have h := als_half_step_decrease hf hlam hrun c
    exact h.2.2.1.trans h.2.2.2
  · subst hc
    rw [show 2 * c + 1 + 1 = 2 * (c + 1) by ring, alsHalf_even, alsHalf_odd]
    have h := als_half_step_decrease hf hlam hrun c
    exact h.1.trans h.2.1

/-- The half-step estimate with the restricted smoothness constant, near the limit: (3.28) for ALS,
without the factor `1/2` because one of the two blocks vanishes.  (arXiv 2306.00897.) -/
theorem als_local_decrease (hf : IsSmooth f G lam) (hlam : 0 < lam)
    (hrun : IsALSRun f U V Vq Uh) (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hHev : ∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), HasFDerivAt G (H Y) Y)
    (hHc : ContinuousAt H (Us * Ss * Vsᵀ))
    (hconv : Tendsto (alsHalf U V Vq Uh) atTop (𝓝 (Us * Ss * Vsᵀ)))
    (hP : Tendsto (fun ℓ => tangentProj (U ℓ) (Vq ℓ) (G (U ℓ * (V ℓ)ᵀ))) atTop (𝓝 0))
    (hPh : Tendsto (fun ℓ => tangentProj (U (ℓ + 1)) (Vq ℓ) (G (Uh ℓ * (Vq ℓ)ᵀ))) atTop (𝓝 0))
    {Λ : ℝ} (hΛ : blockConst (H (Us * Ss * Vsᵀ)) Us Vs < Λ) (hΛ0 : 0 < Λ) :
    ∀ᶠ i in atTop, 1 / (2 * Λ) * ‖riemGrad G (alsHalf U V Vq Uh i)‖ ^ 2 ≤
      f (alsHalf U V Vq Uh i) - f (alsHalf U V Vq Uh (i + 1)) := by
  obtain ⟨δ, hδ, hloc⟩ := local_descent_blocks hf.hasGrad hUs hVs hSs hHev hHc
    ((le_max_left _ _).trans_lt hΛ) ((le_max_right _ _).trans_lt hΛ) (T := 1 / Λ) (by positivity)
  have ev1 := (tendsto_iff_norm_sub_tendsto_zero.1 hconv).eventually (gt_mem_nhds hδ)
  have ev2 := (tendsto_zero_iff_norm_tendsto_zero.1 hP).eventually (gt_mem_nhds hδ)
  have ev3 := (tendsto_zero_iff_norm_tendsto_zero.1 hPh).eventually (gt_mem_nhds hδ)
  have hdiv : Tendsto (fun i : ℕ => i / 2) atTop atTop := Nat.tendsto_div_const_atTop two_ne_zero
  have ht : (1 / Λ : ℝ) ∈ Icc 0 (1 / Λ) := ⟨by positivity, le_rfl⟩
  have hc : 0 < 1 / (2 * Λ) := by positivity
  have hcalc : ∀ d : ℝ, 1 / (2 * Λ) * d = 1 / Λ * d - Λ / 2 * (1 / Λ) ^ 2 * d := fun d => by
    field_simp
    ring
  filter_upwards [ev1, hdiv.eventually (ev2.and ev3), eventually_ge_atTop 1] with i h1 h2 hi
  obtain ⟨c, hc' | hc'⟩ := Nat.even_or_odd' i
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    subst hc'
    rw [show 2 * (c + 1) / 2 = c + 1 by omega] at h2
    rw [alsHalf_even] at h1 ⊢
    rw [alsHalf_odd]
    obtain ⟨hQU, -⟩ := hrun.qr_U c
    obtain ⟨hQV, T, hT⟩ := hrun.qr_V (c + 1)
    obtain ⟨-, hD⟩ := als_stationary hf hlam hrun c
    have hfac : U (c + 1) * (V (c + 1))ᵀ = U (c + 1) * Tᵀ * (Vq (c + 1))ᵀ := by
      rw [hT, Matrix.transpose_mul, Matrix.mul_assoc]
    set X := U (c + 1) * (V (c + 1))ᵀ with hXdef
    have hsm : ‖rightProj (Vq (c + 1)) (G X)‖ < δ :=
      (norm_rightProj_le_tangentProj hQV _).trans_lt h2.1
    have h3 := hloc (U (c + 1)) Tᵀ (Vq (c + 1)) hQU hQV (by rw [← hfac]; exact h1)
      (rightProj (Vq (c + 1))) (Or.inl rfl) (by rw [← hfac]; exact hsm) _ ht
    rw [← hfac] at h3
    have h4 : f (Uh (c + 1) * (Vq (c + 1))ᵀ) ≤ f (X - (1 / Λ) • rightProj (Vq (c + 1)) (G X)) := by
      have e : X - (1 / Λ) • rightProj (Vq (c + 1)) (G X) =
          (U (c + 1) * Tᵀ - (1 / Λ) • (G X * Vq (c + 1))) * (Vq (c + 1))ᵀ := by
        rw [Matrix.sub_mul, Matrix.smul_mul, rightProj_apply, ← hfac]
      rw [e]
      exact hrun.argmin_U (c + 1) _
    have h5 : ‖riemGrad G X‖ ^ 2 ≤ ‖rightProj (Vq (c + 1)) (G X)‖ ^ 2 := by
      have h6 : ‖riemGrad G X‖ ≤ ‖tangentProj (U (c + 1)) (Vq (c + 1)) (G X)‖ := by
        rw [hfac]; exact norm_riemGrad_le_tangentProj G hQU hQV
      have h7 := norm_tangentProj_sq_le (U (c + 1)) hQV (G X)
      have h8 : leftProj (U (c + 1)) (G X) = 0 := by
        rw [leftProj_apply, Matrix.mul_assoc, hD, Matrix.mul_zero]
      rw [h8, norm_zero, zero_pow two_ne_zero, add_zero] at h7
      exact (pow_le_pow_left₀ (norm_nonneg _) h6 2).trans h7
    calc 1 / (2 * Λ) * ‖riemGrad G X‖ ^ 2
        ≤ 1 / (2 * Λ) * ‖rightProj (Vq (c + 1)) (G X)‖ ^ 2 := by gcongr
      _ = _ := hcalc _
      _ ≤ _ := by linarith only [h3, h4]
  · subst hc'
    rw [show (2 * c + 1) / 2 = c by omega] at h2
    rw [alsHalf_odd] at h1 ⊢
    rw [show 2 * c + 1 + 1 = 2 * (c + 1) by ring, alsHalf_even]
    obtain ⟨hQU, T, hT⟩ := hrun.qr_U c
    obtain ⟨hQV, -⟩ := hrun.qr_V c
    obtain ⟨hC, -⟩ := als_stationary hf hlam hrun c
    have hfac : Uh c * (Vq c)ᵀ = U (c + 1) * T * (Vq c)ᵀ := by rw [hT]
    set X := Uh c * (Vq c)ᵀ with hXdef
    have hsm : ‖leftProj (U (c + 1)) (G X)‖ < δ :=
      (norm_leftProj_le_tangentProj hQU _).trans_lt h2.2
    have h3 := hloc (U (c + 1)) T (Vq c) hQU hQV (by rw [← hfac]; exact h1)
      (leftProj (U (c + 1))) (Or.inr rfl) (by rw [← hfac]; exact hsm) _ ht
    rw [← hfac] at h3
    have h4 : f (U (c + 1) * (V (c + 1))ᵀ) ≤ f (X - (1 / Λ) • leftProj (U (c + 1)) (G X)) := by
      have e : X - (1 / Λ) • leftProj (U (c + 1)) (G X) =
          U (c + 1) * (Vq c * Tᵀ - (1 / Λ) • ((G X)ᵀ * U (c + 1)))ᵀ := by
        rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.mul_sub, Matrix.mul_smul,
          Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.transpose_transpose, leftProj_apply, hfac, Matrix.mul_assoc, Matrix.mul_assoc]
      rw [e]
      exact hrun.argmin_V c _
    have h5 : ‖riemGrad G X‖ ^ 2 ≤ ‖leftProj (U (c + 1)) (G X)‖ ^ 2 := by
      have h6 : ‖riemGrad G X‖ ≤ ‖tangentProj (U (c + 1)) (Vq c) (G X)‖ := by
        rw [hfac]; exact norm_riemGrad_le_tangentProj G hQU hQV
      have h7 := norm_tangentProj_sq_le (U (c + 1)) hQV (G X)
      have h8 : rightProj (Vq c) (G X) = 0 := by
        rw [rightProj_apply, hC, Matrix.zero_mul]
      rw [h8, norm_zero, zero_pow two_ne_zero, zero_add] at h7
      exact (pow_le_pow_left₀ (norm_nonneg _) h6 2).trans h7
    calc 1 / (2 * Λ) * ‖riemGrad G X‖ ^ 2
        ≤ 1 / (2 * Λ) * ‖leftProj (U (c + 1)) (G X)‖ ^ 2 := by gcongr
      _ = _ := hcalc _
      _ ≤ _ := by linarith only [h3, h4]

/-- From the Polyak-Lojasiewicz inequality and sufficient decrease `c₀ ‖grad f(Z_i)‖²` to the rate
`q > 1 - 2 μ c₀`, for a sequence in `M_{≤k}` accumulating at `X∗`.  (arXiv 2306.00897.) -/
theorem rate_of_decrease {Z : ℕ → Matrix m n ℝ} (hgrad : ∀ X, HasFDerivAt f (innerSL ℝ (G X)) X)
    {H₀ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1)
    (hSs : IsUnit Ss.det) (hcrit : riemGrad G (Us * Ss * Vsᵀ) = 0)
    (hHs : HasFDerivAt G H₀ (Us * Ss * Vsᵀ)) {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj Us Vs ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (Us * Ss * Vsᵀ)) H₀ Us Ss Vs ξ)
    (hrank : ∀ i, (Z i).rank ≤ k) (hfl : ∀ i, f (Us * Ss * Vsᵀ) ≤ f (Z i))
    (ha : Tendsto (fun i => f (Z i) - f (Us * Ss * Vsᵀ)) atTop (𝓝 0))
    (hmove : Tendsto (fun i => Z (i + 1) - Z i) atTop (𝓝 0))
    (hcluster : MapClusterPt (Us * Ss * Vsᵀ) atTop Z) {c₀ q : ℝ} (hc₀ : 0 < c₀) (hq0 : 0 < q)
    (hq1 : q < 1) (hq : 1 - 2 * μ * c₀ < q)
    (hdec : ∀ᶠ i in atTop, c₀ * ‖riemGrad G (Z i)‖ ^ 2 ≤ f (Z i) - f (Z (i + 1))) :
    Tendsto Z atTop (𝓝 (Us * Ss * Vsᵀ)) ∧ ∃ C, 0 ≤ C ∧ ∀ᶠ i in atTop,
      f (Z i) - f (Us * Ss * Vsᵀ) ≤ C * q ^ i ∧
        ‖Z i - Us * Ss * Vsᵀ‖ ^ 2 ≤ 8 / μ * (C * q ^ i) := by
  set Xs := Us * Ss * Vsᵀ with hXs
  have h1q : 0 < 1 - q := sub_pos.2 hq1
  set C₀ := c₀ / (1 - q) with hC₀
  have hC₀0 : 0 < C₀ := by positivity
  have hε : 0 < C₀ - 1 / (2 * μ) := by
    have e1 : C₀ - 1 / (2 * μ) = (2 * μ * c₀ - (1 - q)) / (2 * μ * (1 - q)) := by
      rw [hC₀]; field_simp
    rw [e1]
    exact div_pos (by linarith) (by positivity)
  have hpl := riemannian_pl (f := f) hgrad hUs hVs hSs hcrit hHs hμ hpd hε
  rw [← hXs] at hpl
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hpl
  have hplY : ∀ i, ‖Z i - Xs‖ < r → f (Z i) - f Xs ≤ C₀ * ‖riemGrad G (Z i)‖ ^ 2 ∧
      ‖Z i - Xs‖ ^ 2 ≤ 8 / μ * (f (Z i) - f Xs) := fun i hi => by
    have h4 := hball (Z i) (by rwa [Metric.mem_ball, dist_eq_norm]) (hrank i)
    rwa [add_sub_cancel] at h4
  refine local_contraction hr (by positivity) hq0 (fun i => sub_nonneg.2 (hfl i)) ha
    (fun i hi => (hplY i hi).2) ?_ hmove hcluster
  filter_upwards [hdec] with i h1 hi
  have h4 := contraction_of_pl (a := f (Z i) - f Xs) (a' := f (Z (i + 1)) - f Xs)
    (c := c₀) (g₂ := ‖riemGrad G (Z i)‖ ^ 2) hc₀.le hC₀0 (hplY i hi).1 (by linarith only [h1])
  have e : 1 - c₀ / C₀ = q := by
    rw [hC₀]; field_simp; ring
  rwa [e] at h4

/-- The sequence `X̃` of half-steps under strong convexity: its function values decrease to the
limit of the `f(X_ℓ)`, and consecutive half-steps approach each other.  (arXiv 2306.00897.) -/
theorem als_half_basics (hf : IsSmooth f G lam) (hlam : 0 < lam) (hσ : 0 < σ)
    (hsc : IsStronglyConvex f G σ) (hrun : IsALSRun f U V Vq Uh) {fs : ℝ}
    (hlim : Tendsto (fun ℓ => f (U ℓ * (V ℓ)ᵀ)) atTop (𝓝 fs)) :
    (∀ i, fs ≤ f (alsHalf U V Vq Uh i)) ∧
      Tendsto (fun i => f (alsHalf U V Vq Uh i) - fs) atTop (𝓝 0) ∧
      Tendsto (fun i => f (alsHalf U V Vq Uh i) - f (alsHalf U V Vq Uh (i + 1))) atTop (𝓝 0) ∧
      Tendsto (fun i => alsHalf U V Vq Uh (i + 1) - alsHalf U V Vq Uh i) atTop (𝓝 0) := by
  set Z := alsHalf U V Vq Uh with hZ
  have hstep := fun i => als_move hf hlam hsc hrun i
  have hanti : Antitone fun i => f (Z i) := antitone_nat_of_succ_le fun i => by
    have h0 : 0 ≤ σ / 2 * ‖Z (i + 1) - Z i‖ ^ 2 := by positivity
    linarith [hstep i]
  have h2 : Tendsto (fun c : ℕ => 2 * c) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have hsub : Tendsto ((fun i => f (Z i)) ∘ fun c : ℕ => 2 * c) atTop (𝓝 fs) := by
    refine hlim.congr fun c => ?_
    simp only [Function.comp_apply]
    rw [hZ, alsHalf_even]
  have hfl : ∀ i, fs ≤ f (Z i) := fun i => by
    refine le_of_tendsto hsub ?_
    filter_upwards [eventually_ge_atTop i] with c hc
    exact hanti (show i ≤ 2 * c by omega)
  have hbdd : BddBelow (range fun i => f (Z i)) := ⟨fs, by rintro _ ⟨i, rfl⟩; exact hfl i⟩
  have hL := tendsto_atTop_ciInf hanti hbdd
  have hLeq : (⨅ i, f (Z i)) = fs := tendsto_nhds_unique (hL.comp h2) hsub
  rw [hLeq] at hL
  have hdiff : Tendsto (fun i => f (Z i) - f (Z (i + 1))) atTop (𝓝 0) := by
    simpa using hL.sub (hL.comp (tendsto_add_atTop_nat 1))
  refine ⟨hfl, by simpa using hL.sub_const fs, hdiff, ?_⟩
  refine tendsto_zero_of_sq (u := fun i => Z (i + 1) - Z i) ?_
  have h3 : Tendsto (fun i => 2 / σ * (f (Z i) - f (Z (i + 1)))) atTop (𝓝 0) := by
    simpa using hdiff.const_mul (2 / σ)
  refine squeeze_zero (fun i => sq_nonneg _) (fun i => ?_) h3
  have h4 := hstep i
  have e : 2 / σ * (f (Z i) - f (Z (i + 1))) ≥ 2 / σ * (σ / 2 * ‖Z (i + 1) - Z i‖ ^ 2) := by
    gcongr
  have e2 : 2 / σ * (σ / 2 * ‖Z (i + 1) - Z i‖ ^ 2) = ‖Z (i + 1) - Z i‖ ^ 2 := by
    field_simp
  linarith

/-- **Theorem 3.10** (arXiv 2306.00897).  Let `f` be `λ`-smooth and strongly convex, and let
`X_ℓ = U_ℓ V_ℓᵀ` be the iterates of Algorithm 3.  Suppose `(X_ℓ)` has an accumulation point
`X∗ = Us Ss Vsᵀ` of rank `k`, near which `∇f` is differentiable with derivative `H` continuous at
`X∗`, with `H(ξ, ξ) ≥ μ ‖ξ‖²` for the Riemannian Hessian, `μ > 0`.  With `λ∗ = max {‖P_{V∗} H(X∗)
P_{V∗}‖, ‖P_{U∗} H(X∗) P_{U∗}‖} ≤ λ`: `X_ℓ → X∗`, the point `X∗` is an isolated local minimizer of
`f|M_{≤k}`, and `limsup ‖X_ℓ - X∗‖^{1/ℓ} ≤ 1 - μ / λ∗ < 1`,
`limsup (f(X_ℓ) - f(X∗))^{1/ℓ} ≤ (1 - μ / λ∗)²`. -/
theorem als_linear_rate (hf : IsSmooth f G lam) (hlam : 0 < lam) (hσ : 0 < σ)
    (hsc : IsStronglyConvex f G σ) (hrun : IsALSRun f U V Vq Uh) (hk : 0 < k)
    (hUs : Usᵀ * Us = 1) (hVs : Vsᵀ * Vs = 1) (hSs : IsUnit Ss.det)
    (hcluster : MapClusterPt (Us * Ss * Vsᵀ) atTop fun ℓ => U ℓ * (V ℓ)ᵀ)
    (hHev : ∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), HasFDerivAt G (H Y) Y)
    (hHc : ContinuousAt H (Us * Ss * Vsᵀ)) {μ : ℝ} (hμ : 0 < μ)
    (hpd : ∀ ξ, tangentProj Us Vs ξ = ξ →
      μ * ‖ξ‖ ^ 2 ≤ riemHess (G (Us * Ss * Vsᵀ)) (H (Us * Ss * Vsᵀ)) Us Ss Vs ξ) :
    Tendsto (fun ℓ => U ℓ * (V ℓ)ᵀ) atTop (𝓝 (Us * Ss * Vsᵀ)) ∧
      (∀ᶠ Y in 𝓝 (Us * Ss * Vsᵀ), Y.rank ≤ k → Y ≠ Us * Ss * Vsᵀ → f (Us * Ss * Vsᵀ) < f Y) ∧
      blockConst (H (Us * Ss * Vsᵀ)) Us Vs ≤ lam ∧
      1 - μ / blockConst (H (Us * Ss * Vsᵀ)) Us Vs < 1 ∧
      limsup (fun ℓ : ℕ => ‖U ℓ * (V ℓ)ᵀ - Us * Ss * Vsᵀ‖ ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        1 - μ / blockConst (H (Us * Ss * Vsᵀ)) Us Vs ∧
      limsup (fun ℓ : ℕ => (f (U ℓ * (V ℓ)ᵀ) - f (Us * Ss * Vsᵀ)) ^ ((ℓ : ℝ)⁻¹)) atTop ≤
        (1 - μ / blockConst (H (Us * Ss * Vsᵀ)) Us Vs) ^ 2 := by
  set Xs := Us * Ss * Vsᵀ with hXs
  set l := blockConst (H Xs) Us Vs with hl
  have hHs : HasFDerivAt G (H Xs) Xs := hHev.self_of_nhds
  have hbdd := hsc.bddBelow hσ
  obtain ⟨hanti, fstar, hlim, -, hP, hg, hcl, -, -⟩ := als_convergence hf hlam hbdd hrun
  obtain ⟨hfs, hcrit⟩ := hcl Xs hcluster
  subst hfs
  set Z := alsHalf U V Vq Uh with hZ
  have hμl : μ ≤ l := le_blockConst_of_posDef hk hUs hVs hSs hpd
  have hl0 : 0 < l := hμ.trans_le hμl
  have hHle : ‖H Xs‖ ≤ lam := hHs.le_of_lip' hlam.le
    (Eventually.of_forall fun Y => hf.lipschitz Y Xs)
  have hllam : l ≤ lam := (blockConst_le hUs hVs).trans hHle
  have hμlam : μ ≤ lam := hμl.trans hllam
  obtain ⟨hfl, ha, hdiff, hmove⟩ := als_half_basics hf hlam hσ hsc hrun hlim
  have h2 : Tendsto (fun c : ℕ => 2 * c) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have hZ2 : ∀ c, Z (2 * c) = U c * (V c)ᵀ := fun c => alsHalf_even c
  have hZ3 : ∀ c, Z (2 * c + 1) = Uh c * (Vq c)ᵀ := fun c => alsHalf_odd c
  have hcomp : (Z ∘ fun c : ℕ => 2 * c) = fun ℓ => U ℓ * (V ℓ)ᵀ := funext fun c => hZ2 c
  have hclusterZ : MapClusterPt Xs atTop Z :=
    MapClusterPt.of_comp h2 (by rw [hcomp]; exact hcluster)
  have hrank : ∀ i, (Z i).rank ≤ k := fun i => by
    obtain ⟨c, hc | hc⟩ := Nat.even_or_odd' i <;> subst hc
    · rw [hZ2]
      exact (Matrix.rank_mul_le_left _ _).trans (by simpa using (U c).rank_le_card_width)
    · rw [hZ3]
      exact (Matrix.rank_mul_le_left _ _).trans (by simpa using (Uh c).rank_le_card_width)
  have hhalf : 0 < μ / (2 * lam) := by positivity
  have hhalf2 : μ / (2 * lam) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨hZconv, -⟩ := rate_of_decrease hf.hasGrad hUs hVs hSs hcrit hHs hμ hpd hrank hfl ha hmove
    hclusterZ (c₀ := 1 / (2 * lam)) (q := 1 - μ / (2 * lam)) (by positivity) (by linarith)
    (by linarith) (by
      have e : 2 * μ * (1 / (2 * lam)) = 2 * (μ / (2 * lam)) := by ring
      rw [e]
      linarith)
    (by
      filter_upwards [eventually_ge_atTop 1] with i hi
      exact als_half_decrease hf hlam hrun hi)
  have hXconv : Tendsto (fun ℓ => U ℓ * (V ℓ)ᵀ) atTop (𝓝 Xs) := by
    rw [← hcomp]; exact hZconv.comp h2
  have hPh : Tendsto (fun ℓ => tangentProj (U (ℓ + 1)) (Vq ℓ) (G (Uh ℓ * (Vq ℓ)ᵀ))) atTop
      (𝓝 0) := by
    refine tendsto_zero_of_sq ?_
    have h3 : Tendsto (fun c : ℕ => 2 * c + 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
    have h4 := (hdiff.comp h3).const_mul (2 * lam)
    rw [mul_zero] at h4
    refine squeeze_zero (fun ℓ => sq_nonneg _) (fun ℓ => ?_) h4
    have h5 := (als_half_step_decrease hf hlam hrun ℓ).2.1
    simp only [Function.comp_apply]
    rw [alsHalf_odd, show 2 * ℓ + 1 + 1 = 2 * (ℓ + 1) by ring, alsHalf_even]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h5
    linarith
  have hr0 : 0 ≤ 1 - μ / l := by
    have : μ / l ≤ 1 := (div_le_one hl0).2 hμl
    linarith
  have hr1 : 1 - μ / l < 1 := by
    have : 0 < μ / l := by positivity
    linarith
  have key : ∀ q, 1 - μ / l < q → q < 1 → ∃ C, 0 ≤ C ∧ ∀ᶠ i in atTop,
      f (Z i) - f Xs ≤ C * q ^ i ∧ ‖Z i - Xs‖ ^ 2 ≤ 8 / μ * (C * q ^ i) := by
    intro q hq hq1
    have h1q : 0 < 1 - q := sub_pos.2 hq1
    have hq0 : 0 < q := hr0.trans_lt hq
    have h3 : l * (1 - q) < μ := by
      have : 1 - q < μ / l := by linarith
      rwa [lt_div_iff₀' hl0] at this
    set Λ := (l + μ / (1 - q)) / 2 with hΛdef
    have h4 : l < μ / (1 - q) := by rwa [lt_div_iff₀ h1q]
    have hΛ1 : l < Λ := by rw [hΛdef]; linarith
    have hΛ2 : Λ < μ / (1 - q) := by rw [hΛdef]; linarith
    have hΛ0 : 0 < Λ := hl0.trans hΛ1
    have h5 : (1 - q) * Λ < μ := by rwa [lt_div_iff₀' h1q] at hΛ2
    have h6 : 1 - 2 * μ * (1 / (2 * Λ)) < q := by
      have e : 2 * μ * (1 / (2 * Λ)) = μ / Λ := by field_simp
      have h7 : 1 - q < μ / Λ := by rwa [lt_div_iff₀ hΛ0]
      rw [e]
      linarith
    exact (rate_of_decrease hf.hasGrad hUs hVs hSs hcrit hHs hμ hpd hrank hfl ha hmove hclusterZ
      (c₀ := 1 / (2 * Λ)) (by positivity) hq0 hq1 h6
      (als_local_decrease hf hlam hrun hUs hVs hSs hHev hHc hZconv hP hPh hΛ1 hΛ0)).2
  refine ⟨hXconv, isolated_local_min hf.hasGrad hUs hVs hSs hcrit hHs hμ hpd, hllam, hr1, ?_, ?_⟩
  · refine limsup_root_le_of_forall hr0 hr1 (fun ℓ => norm_nonneg _) fun q hq hq1 => ?_
    have hq0 : 0 < q := hr0.trans_lt hq
    obtain ⟨C, hC, hev⟩ := key q hq hq1
    refine ⟨√(8 / μ * C), Real.sqrt_nonneg _, ?_⟩
    filter_upwards [h2.eventually hev] with ℓ hℓ
    rw [hZ2] at hℓ
    calc ‖U ℓ * (V ℓ)ᵀ - Xs‖ = √(‖U ℓ * (V ℓ)ᵀ - Xs‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(8 / μ * C * (q ^ ℓ) ^ 2) := by
          refine Real.sqrt_le_sqrt (hℓ.2.trans (le_of_eq ?_))
          rw [← pow_mul, mul_comm ℓ 2]
          ring
      _ = √(8 / μ * C) * q ^ ℓ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  · have hsq : (1 - μ / l) ^ 2 < 1 := by nlinarith
    refine limsup_root_le_of_forall (sq_nonneg _) hsq
      (fun ℓ => sub_nonneg.2 (hanti.le_of_tendsto hlim ℓ)) fun q hq hq1 => ?_
    have hq0 : 0 < q := (sq_nonneg _).trans_lt hq
    have hrq : 1 - μ / l < √q := Real.lt_sqrt_of_sq_lt hq
    have hq2 : √q < 1 := by
      rw [Real.sqrt_lt' one_pos]
      simpa using hq1
    obtain ⟨C, hC, hev⟩ := key (√q) hrq hq2
    refine ⟨C, hC, ?_⟩
    filter_upwards [h2.eventually hev] with ℓ hℓ
    rw [hZ2] at hℓ
    refine hℓ.1.trans (le_of_eq ?_)
    rw [pow_mul, Real.sq_sqrt hq0.le]

end ALSLocal

/-! ### Instances: the hypotheses can hold -/

section Instances

/-- For fixed steps and for backtracking, step sizes are bounded (`h ≤ 2 / Λ`, `h ≤ h̄`), as used
in Theorem 3.7.  (arXiv 2306.00897.) -/
theorem StepRule.step_le {r : StepRule} {Λ d h : ℝ} {φ : ℝ → ℝ}
    (hr : r.Admissible Λ d φ h) (hne : r ≠ StepRule.exact) : h ≤ r.reach Λ := by
  cases r with
  | fixed α => exact hr.2.2.le
  | exact => exact absurd rfl hne
  | armijo hbar β γ =>
    obtain ⟨hb, hβ, hβ1, -, -, i, rfl, -⟩ := hr
    have : β ^ i ≤ 1 := pow_le_one₀ hβ.le hβ1.le
    change hbar * β ^ i ≤ hbar
    nlinarith

/-- **Algorithm 1 is well defined** for fixed step sizes when `k ≤ min (m, n)`.
(arXiv 2306.00897.) -/
theorem exists_balancedRun {f : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {Λ : ℝ}
    (hkm : k ≤ Fintype.card m) (hkn : k ≤ Fintype.card n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {L₀ : Matrix m (Fin k) ℝ} {R₀ : Matrix n (Fin k) ℝ} (hb : IsBalanced L₀ R₀) :
    ∃ (h : ℕ → ℝ) (L : ℕ → Matrix m (Fin k) ℝ) (R : ℕ → Matrix n (Fin k) ℝ),
      IsBalancedRun f G Λ (fun _ => StepRule.fixed α) h L R ∧ L 0 = L₀ ∧ R 0 = R₀ := by
  set h₀ := 2 * α / Λ with hh₀
  have hadm : ∀ (d : ℝ) (φ : ℝ → ℝ), (StepRule.fixed α).Admissible Λ d φ h₀ :=
    fun _ _ => ⟨hα0, hα1, rfl⟩
  have hrk : ∀ (A : Matrix m (Fin k) ℝ) (B : Matrix n (Fin k) ℝ), (A * Bᵀ).rank ≤ k := fun A _ =>
    (Matrix.rank_mul_le_left _ _).trans (by simpa using A.rank_le_card_width)
  let State := {p : Matrix m (Fin k) ℝ × Matrix n (Fin k) ℝ // IsBalanced p.1 p.2}
  have hstep : ∀ s : State, ∃ s' : State,
      BalancedStep f G Λ (StepRule.fixed α) h₀ s.1.1 s.1.2 s'.1.1 s'.1.2 := by
    rintro ⟨⟨L, R⟩, -⟩
    rcases le_or_gt ‖(G (L * Rᵀ))ᵀ * L‖ ‖G (L * Rᵀ) * R‖ with hsel | hsel
    · obtain ⟨L', R', hB, hP⟩ := exists_isBalanced _ (hrk (L - h₀ • (G (L * Rᵀ) * R)) R) hkm hkn
      exact ⟨⟨(L', R'), hB⟩, hB, Or.inl ⟨hsel, hP, hadm _ _⟩⟩
    · obtain ⟨L', R', hB, hP⟩ := exists_isBalanced _ (hrk L (R - h₀ • ((G (L * Rᵀ))ᵀ * L))) hkm hkn
      exact ⟨⟨(L', R'), hB⟩, hB, Or.inr ⟨hsel, hP, hadm _ _⟩⟩
  choose nxt hnxt using hstep
  let seq : ℕ → State := fun ℓ => Nat.rec ⟨(L₀, R₀), hb⟩ (fun _ s => nxt s) ℓ
  exact ⟨fun _ => h₀, fun ℓ => (seq ℓ).1.1, fun ℓ => (seq ℓ).1.2,
    ⟨hb, fun ℓ => hnxt (seq ℓ)⟩, rfl, rfl⟩

/-- **The assumptions of Theorems 3.7, 3.8 and 3.10 can hold.**  For `f(X) = ‖X - Y‖² / 2` with
`Y = U S Vᵀ` of rank `k`: `f` is `1`-smooth and strongly convex, `Y` is a critical point, its
Riemannian Hessian is `‖ξ‖²`, so `μ = 1`, and `λ∗ ≤ 1`.  (arXiv 2306.00897.) -/
theorem quadratic_instance {U : Matrix m (Fin k) ℝ} {S : Matrix (Fin k) (Fin k) ℝ}
    {V : Matrix n (Fin k) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsSmooth (fun X => ‖X - U * S * Vᵀ‖ ^ 2 / 2) (fun X => X - U * S * Vᵀ) 1 ∧
      IsStronglyConvex (fun X => ‖X - U * S * Vᵀ‖ ^ 2 / 2) (fun X => X - U * S * Vᵀ) 1 ∧
      riemGrad (fun X => X - U * S * Vᵀ) (U * S * Vᵀ) = 0 ∧
      (∀ ξ, riemHess (U * S * Vᵀ - U * S * Vᵀ) 1 U S V ξ = ‖ξ‖ ^ 2) ∧
      blockConst 1 U V ≤ 1 := by
  set Y := U * S * Vᵀ with hY
  refine ⟨⟨fun X => ?_, fun X Z => ?_⟩, fun X Z => ?_, ?_, fun ξ => ?_, ?_⟩
  · have h1 := (((hasFDerivAt_id X).sub_const Y).norm_sq).const_mul (1 / 2 : ℝ)
    have h2 : (fun X : Matrix m n ℝ => ‖X - Y‖ ^ 2 / 2) =
        fun X => (1 / 2 : ℝ) * ‖id X - Y‖ ^ 2 := by
      funext Z
      simp only [id]
      ring
    rw [h2]
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.id_apply, id, smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  · simp only [sub_sub_sub_cancel_right, one_mul, le_refl]
  · have e : (X - Y) + (Z - X) = Z - Y := by abel
    have h1 := norm_add_sq_real (X - Y) (Z - X)
    rw [e] at h1
    change ‖X - Y‖ ^ 2 / 2 + ⟪X - Y, Z - X⟫ + 1 / 2 * ‖Z - X‖ ^ 2 ≤ ‖Z - Y‖ ^ 2 / 2
    rw [h1]
    linarith
  · have h0 : Y - Y = 0 := sub_self Y
    rw [riemGrad, h0, map_zero]
  · simp [riemHess]
  · exact (blockConst_le hU hV).trans IsOrthProj.one.opNorm_le

end Instances

end LeanDLRA.Literature.P2306_00897
