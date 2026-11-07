import Mathlib
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2610.06885: DLR-NE, low-rank certificates (part a)

Formalized here, each with its label from the paper in the docstring:

* **Prop. 3** (`condition_number_le_exp`): for sorted positive singular values
  `σ 0 ≥ … ≥ σ (r-1) > 0` of a core, `κ = σ 0 / σ (r-1) ≤ exp (R / (√2 σ_r²))` with
  `R = specR r σ`. The paper's `R(S)` is `‖SᵀS − α_S² I‖_F`; here it is written through
  the singular values `σ i`, which are the square roots of the eigenvalues of `SᵀS`, so the
  statement is about the sorted real vector `σ`.
* **Thm. 1** (`truncated_network_error`): for the one-hidden-layer network `w ↦ ⟪w, ϕ(W x)⟫`
  with elementwise `Lϕ`-Lipschitz `ϕ`, the rank-`r` truncation `W_r = A V_r V_rᵀ` of the full
  weight satisfies `|V* − V_r| ≤ ε_NN + Lϕ ‖w‖ R_X ε_EYM(r)` on `X`, where
  `ε_EYM(r) = (∑_{r ≤ i < n} σ_i(W)²)^{1/2}`. The Eckart–Young–Mirsky step is
  `LeanDLRA.EckartYoung.norm_sub_truncation`, not a hypothesis. Assumption 3 enters as the
  hypothesis `hNN`. The sup norm over `X` is written as a pointwise bound on `X`.
* **Thm. 2, recursion core** (`error_propagation`): the unrolling of the error recursion
  `e_{k+1} ≤ γ e_k + ε_total` that the paper uses to conclude Thm. 2 (39). The one-step bound is
  taken as the hypothesis `hstep`. It is not derived here: Lemma 3 (single-step error, 38) and
  the contraction Prop. 1 are not formalized in this file. The proof uses the library's
  `discrete_gronwall_const_le`.

Left out: Prop. 1 (the max-min Bellman contraction, which needs the continuous game and mixed
strategies), Lemma 3 and Thm. 2 in full (they depend on Lemma 2, the covering argument, and on
Prop. 1), and Algorithm 1 (an algorithm description; its cost claim, Thm. 3, is not a
statement about a mathematical object that this file formalizes).

Core definitions used: `LeanDLRA.EckartYoung.truncation`, `norm_sub_truncation`,
`rank_truncation_le`, `sq_norm_toEuclideanLin`, `LeanDLRA.Frobenius` norms, and the
library's `discrete_gronwall_const_le`. Local additions: `alphaSq`, `specR`, the elementwise
activation `elemAct`, and small matrix–vector norm lemmas.
-/

open scoped RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2610_06885

open Finset Matrix

/-! ### Proposition 3: condition number of the core -/

/-- `α_S² = (1/r) ∑ σ_i²`, which equals `(1/r) ‖S‖_F²` when `σ_i` are the singular
values of `S`. -/
noncomputable def alphaSq (r : ℕ) (σ : ℕ → ℝ) : ℝ := (∑ i ∈ range r, σ i ^ 2) / r

/-- `R = √(∑_i (σ_i² − α_S²)²)`, which is `‖SᵀS − α_S² I‖_F` when the `σ_i` are the singular
values of `S` (the eigenvalues of `SᵀS` are `σ_i²`). -/
noncomputable def specR (r : ℕ) (σ : ℕ → ℝ) : ℝ :=
  √(∑ i ∈ range r, (σ i ^ 2 - alphaSq r σ) ^ 2)

/-- **Prop. 3 (condition-number bound)**, arXiv 2610.06885, Proposition 3. For sorted positive
singular values `σ 0 ≥ … ≥ σ (r-1) > 0` of a core `S ∈ ℝ^{r×r}`,
`κ(S) = σ_1/σ_r ≤ exp (R(S) / (√2 σ_r²))`, with `R(S) = specR r σ`. The index `i` of
`σ i` runs over `0, …, r-1`, so `σ 0 = σ_1` and `σ (r-1) = σ_r`. -/
theorem condition_number_le_exp (r : ℕ) (hr : 0 < r) (σ : ℕ → ℝ)
    (hsort : ∀ i j, i ≤ j → j < r → σ j ≤ σ i) (hpos : ∀ i < r, 0 < σ i) :
    σ 0 / σ (r - 1) ≤ Real.exp (specR r σ / (√2 * σ (r - 1) ^ 2)) := by
  have hlast : r - 1 < r := Nat.sub_lt hr one_pos
  have hb0 : 0 < σ (r - 1) := hpos _ hlast
  have hab : σ (r - 1) ≤ σ 0 := hsort 0 (r - 1) (Nat.zero_le _) hlast
  have ha0 : 0 < σ 0 := lt_of_lt_of_le hb0 hab
  -- The key inequality: σ_1² − σ_r² ≤ √2 R(S).
  have hkey : σ 0 ^ 2 - σ (r - 1) ^ 2 ≤ √2 * specR r σ := by
    by_cases h1 : r = 1
    · have hEq : σ 0 = σ (r - 1) := by simp [h1]
      have hR : 0 ≤ specR r σ := Real.sqrt_nonneg _
      have hz : σ 0 ^ 2 - σ (r - 1) ^ 2 = 0 := by rw [hEq]; simp
      rw [hz]
      positivity
    · have hr2 : 2 ≤ r := by omega
      have hne : 0 ≠ r - 1 := by omega
      have hsub : ({0, r - 1} : Finset ℕ) ⊆ range r := by
        intro i hi
        simp only [mem_insert, mem_singleton] at hi
        simp only [mem_range]
        omega
      have hpair : (σ 0 ^ 2 - alphaSq r σ) ^ 2 + (σ (r - 1) ^ 2 - alphaSq r σ) ^ 2 ≤
          ∑ i ∈ range r, (σ i ^ 2 - alphaSq r σ) ^ 2 := by
        have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (f := fun i => (σ i ^ 2 - alphaSq r σ) ^ 2) (fun i _ _ => sq_nonneg _)
        rw [Finset.sum_pair hne] at hs
        exact hs
      have h2 : (σ 0 ^ 2 - σ (r - 1) ^ 2) ^ 2 ≤
          2 * ∑ i ∈ range r, (σ i ^ 2 - alphaSq r σ) ^ 2 := by
        nlinarith [sq_nonneg ((σ 0 ^ 2 - alphaSq r σ) + (σ (r - 1) ^ 2 - alphaSq r σ))]
      have h3 := Real.abs_le_sqrt h2
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h3
      unfold specR
      exact (le_abs_self _).trans h3
  set a := σ 0 with ha
  set b := σ (r - 1) with hb
  set t := a / b with ht
  have ht1 : 1 ≤ t := (one_le_div hb0).mpr hab
  have hlog : Real.log t ≤ (t ^ 2 - 1) / 2 := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
    nlinarith [sq_nonneg (t - 1)]
  have hsq : (t ^ 2 - 1) / 2 = (a ^ 2 - b ^ 2) / (2 * b ^ 2) := by
    rw [ht, div_pow]
    field_simp
  have hfin : (t ^ 2 - 1) / 2 ≤ specR r σ / (√2 * b ^ 2) := by
    rw [hsq]
    have hs2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsp : (0 : ℝ) < √2 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ √2 * b ^ 2)
    have he : √2 * specR r σ * (√2 * b ^ 2) = specR r σ * (2 * b ^ 2) := by
      linear_combination (specR r σ * b ^ 2) * hs2
    linarith
  calc a / b = Real.exp (Real.log t) := by rw [Real.exp_log (by linarith)]
    _ ≤ Real.exp (specR r σ / (√2 * b ^ 2)) := Real.exp_le_exp.mpr (hlog.trans hfin)

/-! ### Theorem 1: rank-`r` truncation of the network weight -/

/-- The elementwise activation `ϕ` applied to a vector in `ℝ^m`. -/
noncomputable def elemAct {m : Type*} [Fintype m] (ϕ : ℝ → ℝ) (z : EuclideanSpace ℝ m) :
    EuclideanSpace ℝ m :=
  WithLp.toLp 2 (fun i => ϕ (z i))

/-- The elementwise activation is `Lϕ`-Lipschitz for the Euclidean norm. -/
lemma norm_elemAct_sub_le {m : Type*} [Fintype m] (ϕ : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hϕ : ∀ s t, |ϕ s - ϕ t| ≤ L * |s - t|) (a b : EuclideanSpace ℝ m) :
    ‖elemAct ϕ a - elemAct ϕ b‖ ≤ L * ‖a - b‖ := by
  have key : ‖elemAct ϕ a - elemAct ϕ b‖ ^ 2 ≤ (L * ‖a - b‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsq : |ϕ (a i) - ϕ (b i)| ^ 2 ≤ (L * |a i - b i|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hϕ (a i) (b i)) 2
    simpa [elemAct, Real.norm_eq_abs, sq_abs, mul_pow, PiLp.sub_apply] using hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _)) two_ne_zero).mp key

/-- Frobenius bound on a matrix–vector product: `‖M x‖₂ ≤ ‖M‖_F ‖x‖₂`. -/
lemma norm_toEuclideanLin_le_frob {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin M x‖ ≤ ‖x‖ * ‖M‖ := by
  have h : ‖Matrix.toEuclideanLin M x‖ ^ 2 ≤ (‖x‖ * ‖M‖) ^ 2 := by
    rw [LeanDLRA.EckartYoung.sq_norm_toEuclideanLin, mul_pow, LeanDLRA.Frobenius.norm_sq_eq_sum,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc : |⟪x, (WithLp.toLp 2 (M i) : EuclideanSpace ℝ n)⟫| ≤
        ‖x‖ * ‖(WithLp.toLp 2 (M i) : EuclideanSpace ℝ n)‖ :=
      abs_real_inner_le_norm _ _
    have hrow := LeanDLRA.EckartYoung.sq_norm_row M i
    calc ⟪x, (WithLp.toLp 2 (M i) : EuclideanSpace ℝ n)⟫ ^ 2
        = |⟪x, (WithLp.toLp 2 (M i) : EuclideanSpace ℝ n)⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (‖x‖ * ‖(WithLp.toLp 2 (M i) : EuclideanSpace ℝ n)‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hc 2
      _ = ‖x‖ ^ 2 * ∑ j, M i j ^ 2 := by rw [mul_pow, hrow]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- **Theorem 1 (global low-rank approximation error bound)**, arXiv 2610.06885, Theorem 1.
Network `V(x; w, W) = ⟪w, ϕ(W x)⟫` with elementwise `Lϕ`-Lipschitz activation `ϕ`. Let `W`
be the full-rank weight and `W_r = A V_r V_rᵀ` its rank-`r` truncation
(`LeanDLRA.EckartYoung.truncation`).
Assumption 3 is `hNN`: `|V* − V_full| ≤ ε_NN` on `X`, with `‖x‖ ≤ R_X` on `X` (`hRX`).
Conclusion: `rank W_r ≤ r`, and `|V* − V_r| ≤ ε_NN + Lϕ ‖w‖ R_X ε_EYM(r)` on `X`, where
`ε_EYM(r) = (∑_{r ≤ i < n} σ_i(W)²)^{1/2}` is the Frobenius truncation error of `W`.
The sup norm over `X` is written as a pointwise bound. The Eckart–Young–Mirsky step is
`LeanDLRA.EckartYoung.norm_sub_truncation`, not a hypothesis. -/
theorem truncated_network_error {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (ϕ : ℝ → ℝ) (Lϕ : ℝ) (hLϕ : 0 ≤ Lϕ)
    (hϕ : ∀ s t, |ϕ s - ϕ t| ≤ Lϕ * |s - t|)
    (W : Matrix m n ℝ) (w : EuclideanSpace ℝ m) (r : ℕ)
    (Vstar : EuclideanSpace ℝ n → ℝ) (X : Set (EuclideanSpace ℝ n)) (RX εNN : ℝ)
    (hRX : ∀ x ∈ X, ‖x‖ ≤ RX)
    (hNN : ∀ x ∈ X, |Vstar x - ⟪w, elemAct ϕ (Matrix.toEuclideanLin W x)⟫| ≤ εNN) :
    (LeanDLRA.EckartYoung.truncation W r).rank ≤ r ∧
      ∀ x ∈ X, |Vstar x - ⟪w, elemAct ϕ (Matrix.toEuclideanLin
          (LeanDLRA.EckartYoung.truncation W r) x)⟫| ≤
        εNN + Lϕ * ‖w‖ * RX *
          √(∑ i ∈ Ico r (Fintype.card n),
            (Matrix.toEuclideanLin W).singularValues i ^ 2) := by
  refine ⟨LeanDLRA.EckartYoung.rank_truncation_le W r, fun x hx => ?_⟩
  have hE : ‖W - LeanDLRA.EckartYoung.truncation W r‖ =
      √(∑ i ∈ Ico r (Fintype.card n), (Matrix.toEuclideanLin W).singularValues i ^ 2) :=
    LeanDLRA.EckartYoung.norm_sub_truncation W r
  have hdiff : Matrix.toEuclideanLin W x - Matrix.toEuclideanLin
      (LeanDLRA.EckartYoung.truncation W r) x =
      Matrix.toEuclideanLin (W - LeanDLRA.EckartYoung.truncation W r) x := by
    rw [map_sub, LinearMap.sub_apply]
  have hu : ‖elemAct ϕ (Matrix.toEuclideanLin W x) -
      elemAct ϕ (Matrix.toEuclideanLin (LeanDLRA.EckartYoung.truncation W r) x)‖ ≤
      Lϕ * ‖Matrix.toEuclideanLin (W - LeanDLRA.EckartYoung.truncation W r) x‖ := by
    rw [← hdiff]
    exact norm_elemAct_sub_le ϕ Lϕ hLϕ hϕ _ _
  have hv : ‖Matrix.toEuclideanLin (W - LeanDLRA.EckartYoung.truncation W r) x‖ ≤
      √(∑ i ∈ Ico r (Fintype.card n), (Matrix.toEuclideanLin W).singularValues i ^ 2) *
        RX := by
    rw [← hE]
    calc ‖Matrix.toEuclideanLin (W - LeanDLRA.EckartYoung.truncation W r) x‖
        ≤ ‖x‖ * ‖W - LeanDLRA.EckartYoung.truncation W r‖ :=
          norm_toEuclideanLin_le_frob (W - LeanDLRA.EckartYoung.truncation W r) x
      _ ≤ RX * ‖W - LeanDLRA.EckartYoung.truncation W r‖ :=
          mul_le_mul_of_nonneg_right (hRX x hx) (norm_nonneg _)
      _ = ‖W - LeanDLRA.EckartYoung.truncation W r‖ * RX := mul_comm _ _
  have hD2 : ‖elemAct ϕ (Matrix.toEuclideanLin W x) -
      elemAct ϕ (Matrix.toEuclideanLin (LeanDLRA.EckartYoung.truncation W r) x)‖ ≤
      Lϕ * (√(∑ i ∈ Ico r (Fintype.card n), (Matrix.toEuclideanLin W).singularValues i ^ 2)
        * RX) :=
    hu.trans (mul_le_mul_of_nonneg_left hv hLϕ)
  have hinner : |⟪w, elemAct ϕ (Matrix.toEuclideanLin W x)⟫ -
      ⟪w, elemAct ϕ (Matrix.toEuclideanLin (LeanDLRA.EckartYoung.truncation W r) x)⟫| ≤
      ‖w‖ * (Lϕ * (√(∑ i ∈ Ico r (Fintype.card n),
        (Matrix.toEuclideanLin W).singularValues i ^ 2) * RX)) := by
    rw [← inner_sub_right]
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_left hD2 (norm_nonneg _)
  have hring : ‖w‖ * (Lϕ * (√(∑ i ∈ Ico r (Fintype.card n),
        (Matrix.toEuclideanLin W).singularValues i ^ 2) * RX)) =
      Lϕ * ‖w‖ * RX * √(∑ i ∈ Ico r (Fintype.card n),
        (Matrix.toEuclideanLin W).singularValues i ^ 2) := by ring
  have htri := abs_sub_le (Vstar x) ⟪w, elemAct ϕ (Matrix.toEuclideanLin W x)⟫
    ⟪w, elemAct ϕ (Matrix.toEuclideanLin (LeanDLRA.EckartYoung.truncation W r) x)⟫
  have h1 := hNN x hx
  linarith

/-- **Theorem 2, error-propagation core** (arXiv 2610.06885, Theorem 2, display (39)). If the
one-step error satisfies `‖V_{k+1} − V*‖ ≤ γ ‖V_k − V*‖ + ε_total` with `γ ∈ [0, 1)`
and `ε_total ≥ 0`, then `‖V_k − V*‖ ≤ γᵏ ‖V_0 − V*‖ + ε_total/(1 − γ)`. The one-step
inequality is the hypothesis `hstep`. It is NOT derived here: the paper obtains it from the
contraction Prop. 1 and the single-step bound Lemma 3, which are not formalized in this file. -/
theorem error_propagation {E : Type*} [NormedAddCommGroup E] (V : ℕ → E) (Vstar : E)
    (γ ε : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
    (hstep : ∀ k, ‖V (k + 1) - Vstar‖ ≤ γ * ‖V k - Vstar‖ + ε) (k : ℕ) :
    ‖V k - Vstar‖ ≤ γ ^ k * ‖V 0 - Vstar‖ + ε / (1 - γ) := by
  have hg := discrete_gronwall_const_le (e := fun j => ‖V j - Vstar‖) (a := γ) (b := ε)
    (N := k) hγ0 (fun n _ => hstep n) k le_rfl
  have hgeom : ∑ j ∈ Finset.range k, γ ^ j ≤ 1 / (1 - γ) := by
    have h := geom_sum_Ico_le_of_lt_one hγ0 hγ1 (m := 0) (n := k)
    rw [pow_zero, ← Finset.range_eq_Ico] at h
    exact h
  have hεgeom : ε * ∑ j ∈ Finset.range k, γ ^ j ≤ ε / (1 - γ) := by
    rw [show ε / (1 - γ) = ε * (1 / (1 - γ)) by ring]
    exact mul_le_mul_of_nonneg_left hgeom hε
  have hg' : ‖V k - Vstar‖ ≤ γ ^ k * ‖V 0 - Vstar‖ +
      ε * ∑ j ∈ Finset.range k, γ ^ j := hg
  linarith

end LeanDLRA.Literature.P2610_06885
