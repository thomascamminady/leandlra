import Mathlib
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2610.06885: DLR-NE, low-rank certificates (part a)

Tian, Zhang, Chen, Wang, Liu, *Dynamical low-rank equilibrium computation for stochastic games
between advanced persistent threats and moving target defense* (arXiv 2610.06885v2). This module
formalizes the value-function side of the paper: the condition-number bound of the core (Prop. 3),
the truncation bound for the network weight (Thm. 1), the contraction of the max-min Bellman
operator (Prop. 1), the bridge from empirical to uniform error (Lemma 2), the single-step error of
one DLR-NE iteration (Lemma 3) and the convergence of DLR-NE (Thm. 2), derived from Prop. 1 and
Lemma 3 rather than assumed.

* **Prop. 3** (`condition_number_le_exp_matrix`): for a square core `S` with `σ_r(S) > 0`,
  `κ(S) = σ_1/σ_r ≤ exp (R(S) / (√2 σ_r²))` with `R(S) = ‖SᵀS − α_S² I‖_F`,
  `α_S² = ‖S‖_F²/r`, as printed. `condition_number_le_exp` is the same bound for a sorted
  positive vector `σ`, and `sq_norm_transpose_mul_self_sub_smul` (`‖SᵀS − cI‖_F² =
  ∑ (σ_i² − c)²`) connects the two. The printed proof (Appendix A) has a wrong Cauchy–Schwarz
  step (`prop3_printed_step_fails`); the proposition itself is true, by a two-term argument.
* **Thm. 1** (`truncated_network_error`): truncating the full-rank weight to rank `r`
  (`LeanDLRA.EckartYoung.truncation`) costs at most `Lϕ ‖w‖ R_X ε_EYM(r)` on `X`.
* **Prop. 1** (`bellman_contraction`): the operator `bellmanOp` of eq. (6), the max over the
  defender's mixed strategies (probability measures on `D`) of the min over the attacker's of the
  expected reward plus `γ` times the expected next value, satisfies
  `|T V₁ x − T V₂ x| ≤ γ c` whenever `|V₁ − V₂| ≤ c`. The state, attack and defense spaces are
  arbitrary measurable spaces and the transition law is a Markov kernel `P x : (a, d) ↦ P(·|x,a,d)`.
  `bellman_fixedPoint_unique` adds the uniqueness half of (7).
* **Lemma 2** (`bridge_uniform_error`, with `empirical_risk_le`) and **Lemma 3**
  (`single_step_error`): one outer iteration of Algorithm 1, recorded as `DLRNEStep`
  (augmented factors `Û, Ŝ, V̂`, truncated-SVD retraction, computed targets, Assumptions 1(h),
  4(a)–(c)), returns a rank-`≤ r` network within `ε_total` of eq. (38) of the Bellman target.
  `L_fun = Lϕ W_max S_max` is derived from Assumption 4(a), not assumed.
* **Thm. 2** (`dlrne_convergence`, `dlrne_limsup_le`): the DLR-NE iterates satisfy (39),
  `|V⁽ᵏ⁾ − V*| ≤ γᵏ c₀ + ε_total/(1 − γ)` on `X`, and the lim sup bound. The one-step
  recursion (`dlrne_one_step`) is derived from Prop. 1 and Lemma 3; `error_propagation` is the
  abstract unrolling of that recursion.

Settings and narrowings. Sup norms are written as uniform pointwise bounds (`∀ x, |f x| ≤ c`),
which is the same as `‖f‖_∞ ≤ c`. Value functions on the state space are assumed measurable and
bounded (true for `C(X)` with `X` compact); the networks are shown to be continuous and bounded.
The reward is bounded and measurable in the actions (Assumption 1(c)). `V*` enters through the
fixed-point property (7); its identification with the game value (5) (Shapley,
Mertens–Neyman) is not formalized. In Lemma 3 the Lipschitz constant `L_T` of the computed
target and the inner-loop accuracy (Assumption 4(b), read for the unregularized empirical risk,
as in the paper's proof) are hypotheses, as in the paper. The Frobenius norm replaces the
spectral norm in the retraction step, which gives the same constant.

Left out: Algorithm 1's cost (Thm. 3), Corollary 1 (needs Assumption 5 and the implicit-function
argument of Appendix D), and the derivation of `L_T` in Section 2.2 from the dynamics (2).

Core definitions used: `LeanDLRA.EckartYoung.truncation`, `norm_sub_truncation`,
`rank_truncation_le`, `rightSingularVectors`, `sq_norm_eq_sum_sq_singularValues`, the Frobenius
norm and its orthonormal invariance (`LeanDLRA.Frobenius.norm_mul_of_orthonormal`), and
`discrete_gronwall_const_le`. Local definitions: `alphaSq`, `specR` (the paper's `α_S²`, `R(S)`
written through singular values; `condition_number_le_exp_matrix` relates them to the matrix),
`elemAct`, `net` (the network (8)), `bellmanPayoff`, `bellmanOp` (eq. (6); the library has no
game or Bellman operator) and `DLRNEStep`.
-/

open scoped RealInnerProductSpace LeanDLRA.Frobenius

open MeasureTheory ProbabilityTheory

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

/-- **Prop. 3 (condition-number bound)**, arXiv 2610.06885, Proposition 3, for the singular
values. For sorted positive values `σ 0 ≥ … ≥ σ (r-1) > 0` (the singular values of a core
`S ∈ ℝ^{r×r}`), `κ = σ_1/σ_r ≤ exp (R / (√2 σ_r²))`, with `R = specR r σ`. The index `i` of
`σ i` runs over `0, …, r-1`, so `σ 0 = σ_1` and `σ (r-1) = σ_r`. The matrix statement is
`condition_number_le_exp_matrix`. The proof uses `σ_1² − σ_r² ≤ √2 R` (two extreme terms of `R²`),
not the printed chain (see `prop3_printed_step_fails`). -/
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

open LeanDLRA.EckartYoung in
/-- `‖Sᵀ S − c I‖_F² = ∑_i (σ_i(S)² − c)²`: the right singular vectors of `S` are an orthonormal
eigenbasis of `Sᵀ S − c I` with eigenvalues `σ_i² − c`. For `c = α_S²` this is the paper's
`R(S)² = ∑_i (σ_i² − α_S²)²` (Appendix A, first display). -/
theorem sq_norm_transpose_mul_self_sub_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (c : ℝ) :
    ‖Sᵀ * S - c • (1 : Matrix ι ι ℝ)‖ ^ 2 =
      ∑ i ∈ range (Fintype.card ι), ((toEuclideanLin S).singularValues i ^ 2 - c) ^ 2 := by
  rw [sq_norm_eq_sum_sq_norm_toEuclideanLin _ (rightSingularVectors S)]
  have he : ∀ k, ‖toEuclideanLin (Sᵀ * S - c • (1 : Matrix ι ι ℝ)) (rightSingularVectors S k)‖ ^ 2
      = ((toEuclideanLin S).singularValues k ^ 2 - c) ^ 2 := by
    intro k
    have h1 : toEuclideanLin (Sᵀ * S - c • (1 : Matrix ι ι ℝ)) (rightSingularVectors S k) =
        ((toEuclideanLin S).singularValues k ^ 2 - c) • rightSingularVectors S k := by
      rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        toEuclideanLin_transpose_mul_self, LinearMap.comp_apply,
        adjoint_toEuclideanLin_rightSingularVectors, sub_smul]
      congr 1
      simp [Matrix.toLpLin_one]
    rw [h1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, (rightSingularVectors S).orthonormal.1 k,
      one_pow, mul_one]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ ((toEuclideanLin S).singularValues i ^ 2 - c) ^ 2),
    finrank_euclideanSpace]

/-- **Prop. 3 (condition-number bound)**, arXiv 2610.06885, Proposition 3, for a matrix. Let
`S ∈ ℝ^{r×r}` (index type `ι`, `r = |ι|`) with `σ_r(S) > 0`, written `σ_{r-1}` here because the
library's singular values `σ_i(S) = (toEuclideanLin S).singularValues i` are zero-indexed and
sorted decreasingly. Then `κ(S) = σ_1(S)/σ_r(S) ≤ exp (R(S) / (√2 σ_r(S)²))` with
`R(S) = ‖SᵀS − α_S² I‖_F` and `α_S² = ‖S‖_F²/r` (eq. (42)), exactly as printed. -/
theorem condition_number_le_exp_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hpos : 0 < (toEuclideanLin S).singularValues (Fintype.card ι - 1)) :
    (toEuclideanLin S).singularValues 0 / (toEuclideanLin S).singularValues (Fintype.card ι - 1)
      ≤ Real.exp (‖Sᵀ * S - (‖S‖ ^ 2 / Fintype.card ι) • (1 : Matrix ι ι ℝ)‖ /
        (√2 * (toEuclideanLin S).singularValues (Fintype.card ι - 1) ^ 2)) := by
  have hr : 0 < Fintype.card ι := by
    by_contra h
    have h0 : (toEuclideanLin S).singularValues (Fintype.card ι - 1) = 0 :=
      LinearMap.singularValues_of_finrank_le _ (by rw [finrank_euclideanSpace]; omega)
    linarith
  have key := condition_number_le_exp (Fintype.card ι) hr
    (fun i => (toEuclideanLin S).singularValues i)
    (fun i j hij _ => (toEuclideanLin S).singularValues_antitone hij)
    (fun i hi => lt_of_lt_of_le hpos ((toEuclideanLin S).singularValues_antitone (by omega)))
  have hα : alphaSq (Fintype.card ι) (fun i => (toEuclideanLin S).singularValues i) =
      ‖S‖ ^ 2 / Fintype.card ι := by
    rw [alphaSq, LeanDLRA.EckartYoung.sq_norm_eq_sum_sq_singularValues]
  have hR : specR (Fintype.card ι) (fun i => (toEuclideanLin S).singularValues i) =
      ‖Sᵀ * S - (‖S‖ ^ 2 / Fintype.card ι) • (1 : Matrix ι ι ℝ)‖ := by
    rw [specR, hα, ← sq_norm_transpose_mul_self_sub_smul, Real.sqrt_sq (norm_nonneg _)]
  rw [hR] at key
  exact key

/-- **The printed proof of Prop. 3 has a false step** (arXiv 2610.06885, Appendix A, p. 22). The
chain there uses `∑_i |σ_i² − α_S²| ≤ √r (1/r ∑_i (σ_i² − α_S²)²)^{1/2}` ("Cauchy–Schwarz"); the
right-hand side equals `R(S)`, and an `ℓ¹` norm is not bounded by the `ℓ²` norm. Counterexample:
`r = 3`, `σ² = (3, 2, 1)`, where the left side is `2` and the right side `√2`. Cauchy–Schwarz gives
`√r R(S)` instead, so the printed chain only yields `log κ ≤ √r R(S)/(2σ_r²)`, which is weaker
than the claim for `r ≥ 3`. Proposition 3 itself is true (`condition_number_le_exp`, using
`σ_1² − σ_r² ≤ √2 R(S)` from the two extreme terms). -/
theorem prop3_printed_step_fails :
    ∃ σ : ℕ → ℝ, (∀ i j, i ≤ j → j < 3 → σ j ≤ σ i) ∧ (∀ i < 3, 0 < σ i) ∧
      √3 * √((1 / 3) * ∑ i ∈ range 3, (σ i ^ 2 - alphaSq 3 σ) ^ 2) <
        ∑ i ∈ range 3, |σ i ^ 2 - alphaSq 3 σ| := by
  refine ⟨fun i => √(3 - i), ?_, ?_, ?_⟩
  · intro i j hij _
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact Real.sqrt_le_sqrt (by linarith)
  · intro i hi
    have : (i : ℝ) < 3 := by exact_mod_cast hi
    exact Real.sqrt_pos.mpr (by linarith)
  · have h0 : √(3 - (0 : ℝ)) ^ 2 = 3 := by rw [Real.sq_sqrt] <;> norm_num
    have h1 : √(3 - (1 : ℝ)) ^ 2 = 2 := by rw [Real.sq_sqrt] <;> norm_num
    have h2 : √(3 - (2 : ℝ)) ^ 2 = 1 := by rw [Real.sq_sqrt] <;> norm_num
    have hα : alphaSq 3 (fun i : ℕ => √(3 - (i : ℝ))) = 2 := by
      simp only [alphaSq, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
        Nat.cast_one, Nat.cast_ofNat, h0, h1, h2]
      norm_num
    simp only [hα, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, h0, h1, h2]
    have e : √3 * √(1 / 3 * (0 + (3 - 2) ^ 2 + (2 - 2) ^ 2 + (1 - 2) ^ 2 : ℝ)) = √2 := by
      rw [← Real.sqrt_mul (by norm_num)]
      norm_num
    rw [e]
    norm_num

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

/-! ### The network (8) -/

/-- The single-hidden-layer network `V(x; w, W) = ⟪w, ϕ(W x)⟫` of eq. (8) of arXiv 2610.06885,
with output weights `w`, hidden weight `W` and the elementwise activation `ϕ`. In the factored
form (9), `W = U S Vᵀ`. -/
noncomputable def net {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (ϕ : ℝ → ℝ)
    (w : EuclideanSpace ℝ m) (W : Matrix m n ℝ) (x : EuclideanSpace ℝ n) : ℝ :=
  ⟪w, elemAct ϕ (Matrix.toEuclideanLin W x)⟫

section Network

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (ϕ : ℝ → ℝ) {L : ℝ}
  (hL : 0 ≤ L) (hϕ : ∀ s t, |ϕ s - ϕ t| ≤ L * |s - t|) (w : EuclideanSpace ℝ m)
include hL hϕ

/-- Two networks with the same output weights differ by at most `‖w‖ L ‖W x − W' x'‖`. -/
lemma abs_net_sub_le (W W' : Matrix m n ℝ) (x x' : EuclideanSpace ℝ n) :
    |net ϕ w W x - net ϕ w W' x'| ≤
      ‖w‖ * (L * ‖toEuclideanLin W x - toEuclideanLin W' x'‖) := by
  unfold net
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_elemAct_sub_le ϕ L hL hϕ _ _) (norm_nonneg _))

/-- The network is `‖w‖ L ‖W‖_F`-Lipschitz in the input. -/
lemma abs_net_sub_net_le (W : Matrix m n ℝ) (x y : EuclideanSpace ℝ n) :
    |net ϕ w W x - net ϕ w W y| ≤ ‖w‖ * L * ‖W‖ * ‖x - y‖ := by
  have h := abs_net_sub_le ϕ hL hϕ w W W x y
  rw [← map_sub] at h
  have h2 := norm_toEuclideanLin_le_frob W (x - y)
  calc _ ≤ _ := h
    _ ≤ ‖w‖ * (L * (‖x - y‖ * ‖W‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hL) (norm_nonneg _)
    _ = _ := by ring

/-- Changing the hidden weight changes the network by at most `‖w‖ L ‖W − W'‖_F ‖x‖`. -/
lemma abs_net_sub_net_weight_le (W W' : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    |net ϕ w W x - net ϕ w W' x| ≤ ‖w‖ * L * ‖W - W'‖ * ‖x‖ := by
  have h := abs_net_sub_le ϕ hL hϕ w W W' x x
  have hd : toEuclideanLin W x - toEuclideanLin W' x = toEuclideanLin (W - W') x := by
    rw [map_sub, LinearMap.sub_apply]
  rw [hd] at h
  have h2 := norm_toEuclideanLin_le_frob (W - W') x
  calc _ ≤ _ := h
    _ ≤ ‖w‖ * (L * (‖x‖ * ‖W - W'‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hL) (norm_nonneg _)
    _ = _ := by ring

/-- A bound on the network value. -/
lemma abs_net_le (W : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    |net ϕ w W x| ≤ ‖w‖ * (‖elemAct ϕ (0 : EuclideanSpace ℝ m)‖ + L * ‖W‖ * ‖x‖) := by
  unfold net
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have h1 := norm_elemAct_sub_le ϕ L hL hϕ (toEuclideanLin W x) 0
  have h2 := norm_toEuclideanLin_le_frob W x
  rw [sub_zero] at h1
  calc ‖elemAct ϕ (toEuclideanLin W x)‖
      = ‖(elemAct ϕ (toEuclideanLin W x) - elemAct ϕ 0) + elemAct ϕ 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖elemAct ϕ (toEuclideanLin W x) - elemAct ϕ 0‖ + ‖elemAct ϕ 0‖ := norm_add_le _ _
    _ ≤ L * (‖x‖ * ‖W‖) + ‖elemAct ϕ 0‖ := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hL)
    _ = _ := by ring

/-- The network is continuous in the input. -/
lemma continuous_net (W : Matrix m n ℝ) : Continuous (net ϕ w W) := by
  have hK : 0 ≤ ‖w‖ * L * ‖W‖ := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := ⟨‖w‖ * L * ‖W‖, hK⟩) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact abs_net_sub_net_le ϕ hL hϕ w W x y

end Network

/-! ### Proposition 1: contraction of the max-min Bellman operator -/

/-- The max-min value `⨆ i, ⨅ j, Φ i j` of a bounded payoff is monotone up to a constant:
`Φ ≤ Ψ + c` pointwise gives `maxmin Φ ≤ maxmin Ψ + c`. -/
theorem iSup_iInf_le_add {I J : Type*} [Nonempty I] [Nonempty J] {Φ Ψ : I → J → ℝ} {M c : ℝ}
    (hΦ : ∀ i j, |Φ i j| ≤ M) (hΨ : ∀ i j, |Ψ i j| ≤ M) (h : ∀ i j, Φ i j ≤ Ψ i j + c) :
    (⨆ i, ⨅ j, Φ i j) ≤ (⨆ i, ⨅ j, Ψ i j) + c := by
  have hbΦ : ∀ i, BddBelow (Set.range (Φ i)) := fun i =>
    ⟨-M, by rintro _ ⟨j, rfl⟩; exact (abs_le.mp (hΦ i j)).1⟩
  have hbΨ : ∀ i, BddBelow (Set.range (Ψ i)) := fun i =>
    ⟨-M, by rintro _ ⟨j, rfl⟩; exact (abs_le.mp (hΨ i j)).1⟩
  have hinf : ∀ i, ⨅ j, Φ i j ≤ (⨅ j, Ψ i j) + c := by
    intro i
    have : (⨅ j, Φ i j) - c ≤ ⨅ j, Ψ i j :=
      le_ciInf fun j => by linarith [ciInf_le (hbΦ i) j, h i j]
    linarith
  have hbsup : BddAbove (Set.range fun i => ⨅ j, Ψ i j) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    obtain ⟨j⟩ := ‹Nonempty J›
    exact (ciInf_le (hbΨ i) j).trans (abs_le.mp (hΨ i j)).2
  exact ciSup_le fun i => (hinf i).trans (by linarith [le_ciSup hbsup i])

/-- **The max-min operator is 1-Lipschitz in the sup norm** (the second step of the proof of
Prop. 1 of arXiv 2610.06885): for bounded payoffs with `|Φ − Ψ| ≤ c`,
`|⨆ i, ⨅ j, Φ i j − ⨆ i, ⨅ j, Ψ i j| ≤ c`. -/
theorem abs_iSup_iInf_sub_le {I J : Type*} [Nonempty I] [Nonempty J] {Φ Ψ : I → J → ℝ}
    {M c : ℝ} (hΦ : ∀ i j, |Φ i j| ≤ M) (hΨ : ∀ i j, |Ψ i j| ≤ M)
    (h : ∀ i j, |Φ i j - Ψ i j| ≤ c) :
    |(⨆ i, ⨅ j, Φ i j) - ⨆ i, ⨅ j, Ψ i j| ≤ c := by
  rw [abs_sub_le_iff]
  constructor
  · have := iSup_iInf_le_add hΦ hΨ fun i j => by linarith [(abs_le.mp (h i j)).2]
    linarith
  · have := iSup_iInf_le_add hΨ hΦ fun i j => by linarith [(abs_le.mp (h i j)).1]
    linarith

section Bellman

variable {S A D : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace D]

/-- The pure-strategy Bellman payoff `r(x, a, d) + γ ∫ V(x') P(dx' | x, a, d)` of eq. (6) of
arXiv 2610.06885. The transition law at the state `x` is the kernel `P x : A × D → Measure S`. -/
noncomputable def bellmanPayoff (P : S → Kernel (A × D) S) (rew : S → A × D → ℝ) (γ : ℝ)
    (V : S → ℝ) (x : S) (ad : A × D) : ℝ :=
  rew x ad + γ * ∫ y, V y ∂(P x ad)

/-- **The Bellman operator** (6) of arXiv 2610.06885:
`(T V)(x) = max_{p_D ∈ Δ(D)} min_{p_A ∈ Δ(A)} ∫_{A×D} [r(x,a,d) + γ ∫ V(x') P(dx'|x,a,d)]
p_A(da) p_D(dd)`, with mixed strategies the probability measures on the action spaces and the
max and min written as `⨆` and `⨅` (the paper assumes they are attained). -/
noncomputable def bellmanOp (P : S → Kernel (A × D) S) (rew : S → A × D → ℝ) (γ : ℝ)
    (V : S → ℝ) (x : S) : ℝ :=
  ⨆ pD : ProbabilityMeasure D, ⨅ pA : ProbabilityMeasure A,
    ∫ ad, bellmanPayoff P rew γ V x ad ∂((pA : Measure A).prod (pD : Measure D))

omit [MeasurableSpace A] [MeasurableSpace D] in
/-- The integral of a function bounded by `B` against a probability measure is bounded by `B`. -/
lemma abs_integral_le_of_abs_le {μ : Measure S} [IsProbabilityMeasure μ] {f : S → ℝ} {B : ℝ}
    (h : ∀ y, |f y| ≤ B) : |∫ y, f y ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using h y)
  simpa [Real.norm_eq_abs] using this

omit [MeasurableSpace A] [MeasurableSpace D] in
/-- A bounded measurable function is integrable for a finite measure. -/
lemma integrable_of_abs_le {μ : Measure S} [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (h : ∀ y, |f y| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using h y)

/-- The pure-strategy payoff is measurable in the actions (the kernel integral is measurable). -/
lemma stronglyMeasurable_bellmanPayoff (P : S → Kernel (A × D) S) (rew : S → A × D → ℝ)
    (hrew : ∀ x, Measurable (rew x)) (γ : ℝ) {V : S → ℝ} (hV : Measurable V) (x : S) :
    StronglyMeasurable (bellmanPayoff P rew γ V x) := by
  unfold bellmanPayoff
  exact (hrew x).stronglyMeasurable.add
    ((hV.stronglyMeasurable.integral_kernel (κ := P x)).const_mul γ)

/-- The pure-strategy payoff is bounded by `R_max + γ B` when `|V| ≤ B`. -/
lemma abs_bellmanPayoff_le (P : S → Kernel (A × D) S) [∀ x, IsMarkovKernel (P x)]
    (rew : S → A × D → ℝ) {Rmax : ℝ} (hrew : ∀ x ad, |rew x ad| ≤ Rmax) {γ : ℝ} (hγ : 0 ≤ γ)
    {V : S → ℝ} {B : ℝ} (hB : ∀ y, |V y| ≤ B) (x : S) (ad : A × D) :
    |bellmanPayoff P rew γ V x ad| ≤ Rmax + γ * B := by
  unfold bellmanPayoff
  have h1 := abs_integral_le_of_abs_le (μ := P x ad) hB
  calc |rew x ad + γ * ∫ y, V y ∂(P x ad)| ≤ |rew x ad| + |γ * ∫ y, V y ∂(P x ad)| :=
        abs_add_le _ _
    _ ≤ Rmax + γ * B := by
        rw [abs_mul, abs_of_nonneg hγ]
        exact add_le_add (hrew x ad) (mul_le_mul_of_nonneg_left h1 hγ)

/-- The expectation step of Prop. 1: `|Q_{V₁} − Q_{V₂}| ≤ γ c` for the pure-strategy payoffs. -/
lemma abs_bellmanPayoff_sub_le (P : S → Kernel (A × D) S) [∀ x, IsMarkovKernel (P x)]
    (rew : S → A × D → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) {V₁ V₂ : S → ℝ} (hV₁ : Measurable V₁)
    (hV₂ : Measurable V₂) {B₁ B₂ : ℝ} (hB₁ : ∀ y, |V₁ y| ≤ B₁) (hB₂ : ∀ y, |V₂ y| ≤ B₂)
    {c : ℝ} (hc : ∀ y, |V₁ y - V₂ y| ≤ c) (x : S) (ad : A × D) :
    |bellmanPayoff P rew γ V₁ x ad - bellmanPayoff P rew γ V₂ x ad| ≤ γ * c := by
  unfold bellmanPayoff
  have hi₁ : Integrable V₁ (P x ad) := integrable_of_abs_le hV₁ hB₁
  have hi₂ : Integrable V₂ (P x ad) := integrable_of_abs_le hV₂ hB₂
  have hsub : (∫ y, V₁ y ∂(P x ad)) - ∫ y, V₂ y ∂(P x ad) = ∫ y, (V₁ y - V₂ y) ∂(P x ad) :=
    (integral_sub hi₁ hi₂).symm
  have h1 := abs_integral_le_of_abs_le (μ := P x ad) hc
  have he : rew x ad + γ * ∫ y, V₁ y ∂(P x ad) - (rew x ad + γ * ∫ y, V₂ y ∂(P x ad)) =
      γ * ∫ y, (V₁ y - V₂ y) ∂(P x ad) := by rw [← hsub]; ring
  rw [he, abs_mul, abs_of_nonneg hγ]
  exact mul_le_mul_of_nonneg_left h1 hγ

/-- **Prop. 1 (contraction)**, arXiv 2610.06885, Proposition 1: `‖T V₁ − T V₂‖_∞ ≤ γ ‖V₁ − V₂‖_∞`,
written as `|V₁ − V₂| ≤ c ⇒ |T V₁ x − T V₂ x| ≤ γ c` for every state `x`. Setting: arbitrary
measurable state and action spaces (nonempty action spaces, as `[0,1]^{r_a}`, `[0,1]^{r_d}`),
mixed strategies = all probability measures, a Markov transition kernel at each state, a reward
bounded by `R_max` (Assumption 1(c)) and measurable in the actions, and value functions that are
measurable and bounded (as the elements of `C(X)`, `X` compact). Only `γ ≥ 0` is used. The proof
is the paper's: the expectation is non-expansive and the max-min is 1-Lipschitz
(`abs_iSup_iInf_sub_le`). -/
theorem bellman_contraction [Nonempty A] [Nonempty D] (P : S → Kernel (A × D) S)
    [∀ x, IsMarkovKernel (P x)] (rew : S → A × D → ℝ) (hrew_meas : ∀ x, Measurable (rew x))
    {Rmax : ℝ} (hrew : ∀ x ad, |rew x ad| ≤ Rmax) {γ : ℝ} (hγ : 0 ≤ γ) {V₁ V₂ : S → ℝ}
    (hV₁ : Measurable V₁) (hV₂ : Measurable V₂) (hb₁ : ∃ B, ∀ y, |V₁ y| ≤ B)
    (hb₂ : ∃ B, ∀ y, |V₂ y| ≤ B) {c : ℝ} (hc : ∀ y, |V₁ y - V₂ y| ≤ c) (x : S) :
    |bellmanOp P rew γ V₁ x - bellmanOp P rew γ V₂ x| ≤ γ * c := by
  obtain ⟨B₁, hB₁⟩ := hb₁
  obtain ⟨B₂, hB₂⟩ := hb₂
  have : Nonempty (ProbabilityMeasure A) :=
    ⟨⟨Measure.dirac (Classical.arbitrary A), inferInstance⟩⟩
  have : Nonempty (ProbabilityMeasure D) :=
    ⟨⟨Measure.dirac (Classical.arbitrary D), inferInstance⟩⟩
  have hB₁' : ∀ y, |V₁ y| ≤ |B₁| + |B₂| := fun y =>
    (hB₁ y).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
  have hB₂' : ∀ y, |V₂ y| ≤ |B₁| + |B₂| := fun y =>
    (hB₂ y).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
  have hint : ∀ {V : S → ℝ}, Measurable V → (∀ y, |V y| ≤ |B₁| + |B₂|) →
      ∀ (pA : ProbabilityMeasure A) (pD : ProbabilityMeasure D),
      Integrable (bellmanPayoff P rew γ V x) ((pA : Measure A).prod (pD : Measure D)) := by
    intro V hV hB pA pD
    exact Integrable.of_bound
      (stronglyMeasurable_bellmanPayoff P rew hrew_meas γ hV x).aestronglyMeasurable
      (Rmax + γ * (|B₁| + |B₂|))
      (Filter.Eventually.of_forall fun ad => by
        simpa [Real.norm_eq_abs] using abs_bellmanPayoff_le P rew hrew hγ hB x ad)
  have hbound : ∀ {V : S → ℝ}, (∀ y, |V y| ≤ |B₁| + |B₂|) →
      ∀ (pD : ProbabilityMeasure D) (pA : ProbabilityMeasure A),
      |∫ ad, bellmanPayoff P rew γ V x ad ∂((pA : Measure A).prod (pD : Measure D))| ≤
        Rmax + γ * (|B₁| + |B₂|) :=
    fun hB pD pA => abs_integral_le_of_abs_le fun ad => abs_bellmanPayoff_le P rew hrew hγ hB x ad
  unfold bellmanOp
  refine abs_iSup_iInf_sub_le (hbound hB₁') (hbound hB₂') fun pD pA => ?_
  rw [← integral_sub (hint hV₁ hB₁' pA pD) (hint hV₂ hB₂' pA pD)]
  exact abs_integral_le_of_abs_le fun ad =>
    abs_bellmanPayoff_sub_le P rew hγ hV₁ hV₂ hB₁ hB₂ hc x ad

/-- **Uniqueness of the fixed point** (the uniqueness half of the Banach argument after Prop. 1
of arXiv 2610.06885, eq. (7)): for `0 ≤ γ < 1` the Bellman operator has at most one bounded
measurable fixed point. Existence (and the identification with the game value (5)) is not
formalized. -/
theorem bellman_fixedPoint_unique [Nonempty A] [Nonempty D] (P : S → Kernel (A × D) S)
    [∀ x, IsMarkovKernel (P x)] (rew : S → A × D → ℝ) (hrew_meas : ∀ x, Measurable (rew x))
    {Rmax : ℝ} (hrew : ∀ x ad, |rew x ad| ≤ Rmax) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {V₁ V₂ : S → ℝ} (hV₁ : Measurable V₁) (hV₂ : Measurable V₂) (hb₁ : ∃ B, ∀ y, |V₁ y| ≤ B)
    (hb₂ : ∃ B, ∀ y, |V₂ y| ≤ B) (h₁ : ∀ x, bellmanOp P rew γ V₁ x = V₁ x)
    (h₂ : ∀ x, bellmanOp P rew γ V₂ x = V₂ x) : V₁ = V₂ := by
  obtain ⟨B₁, hB₁⟩ := hb₁
  obtain ⟨B₂, hB₂⟩ := hb₂
  have hk : ∀ k : ℕ, ∀ y, |V₁ y - V₂ y| ≤ γ ^ k * (B₁ + B₂) := by
    intro k
    induction k with
    | zero =>
      intro y
      have := abs_le.mp (hB₁ y)
      have := abs_le.mp (hB₂ y)
      rw [pow_zero, one_mul, abs_le]
      constructor <;> linarith
    | succ k ih =>
      intro y
      have := bellman_contraction P rew hrew_meas hrew hγ0 hV₁ hV₂ ⟨B₁, hB₁⟩ ⟨B₂, hB₂⟩ ih y
      rw [h₁, h₂] at this
      calc _ ≤ γ * (γ ^ k * (B₁ + B₂)) := this
        _ = _ := by ring
  funext y
  have ht : Filter.Tendsto (fun k : ℕ => γ ^ k * (B₁ + B₂)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (B₁ + B₂)
  have h0 : |V₁ y - V₂ y| ≤ 0 := ge_of_tendsto' ht fun k => hk k y
  have := abs_nonpos_iff.mp h0
  linarith

end Bellman

/-! ### Lemmas 2 and 3: from the inner loop to a uniform single-step error -/

/-- `√(a + b) ≤ √a + √b` for `a ≥ 0` (for `b < 0` the right side is `√a`). -/
lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) : √(a + b) ≤ √a + √b := by
  rcases le_total 0 b with hb | hb
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  · rw [Real.sqrt_eq_zero'.mpr hb, add_zero]
    exact Real.sqrt_le_sqrt (by linarith)

/-- **Empirical risk of the inner-loop output** (first display of the proof of Lemma 2 of
arXiv 2610.06885): if `f̂` is within `ε_inner` of the empirical risk of a candidate `f*` that is
`ϵ_app`-close to the target on the sample points `x_j` (Assumptions 4(b), 4(c)), then
`(1/N) ∑_j (f̂(x_j) − g(x_j))² ≤ ϵ_app² + ε_inner`. -/
theorem empirical_risk_le {M : Type*} {N : ℕ} (c : Fin N → M) {fhat fstar g : M → ℝ}
    {ϵapp εinner : ℝ} (happ : ∀ j, |fstar (c j) - g (c j)| ≤ ϵapp)
    (hinner : (∑ j, (fhat (c j) - g (c j)) ^ 2) / N ≤
      (∑ j, (fstar (c j) - g (c j)) ^ 2) / N + εinner) :
    (∑ j, (fhat (c j) - g (c j)) ^ 2) / N ≤ ϵapp ^ 2 + εinner := by
  suffices hs : (∑ j, (fstar (c j) - g (c j)) ^ 2) / N ≤ ϵapp ^ 2 by linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, div_zero]
    positivity
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [div_le_iff₀ hNpos]
    calc ∑ j, (fstar (c j) - g (c j)) ^ 2 ≤ ∑ _j : Fin N, ϵapp ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (happ j) 2
      _ = ϵapp ^ 2 * N := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- **Lemma 2 (bridge: empirical `L²` to uniform `L^∞`)**, arXiv 2610.06885, Lemma 2, eq. (37).
Let `{x_j}_{j<N}` be a `δ`-covering of the state space `M` (`N = N_δ ≥ 1`), `f̂` and `g`
`L_fun`- and `L_T`-Lipschitz, and `(1/N) ∑_j (f̂(x_j) − g(x_j))² ≤ ϵ_app² + ε_inner`. Then
`|f̂(x) − g(x)| ≤ √N ϵ_app + √(N ε_inner) + (L_fun + L_T) δ` for every `x`. Hypothesis (i) of the
paper (the candidate `f*`) only serves to give the risk bound; see `empirical_risk_le`. The state
space is any pseudometric space (in the paper `X ⊂ ℝⁿ` with the Euclidean distance). -/
theorem bridge_uniform_error {M : Type*} [PseudoMetricSpace M] {N : ℕ} (hN : 0 < N)
    (c : Fin N → M) {δ : ℝ} (hcov : ∀ x, ∃ j, dist x (c j) ≤ δ) {fhat g : M → ℝ}
    {Lfun LT : ℝ} (hLfun : 0 ≤ Lfun) (hLT : 0 ≤ LT)
    (hf : ∀ x y, |fhat x - fhat y| ≤ Lfun * dist x y) (hg : ∀ x y, |g x - g y| ≤ LT * dist x y)
    {ϵapp εinner : ℝ} (happ : 0 ≤ ϵapp)
    (hrisk : (∑ j, (fhat (c j) - g (c j)) ^ 2) / N ≤ ϵapp ^ 2 + εinner) (x : M) :
    |fhat x - g x| ≤ √N * ϵapp + √(N * εinner) + (Lfun + LT) * δ := by
  obtain ⟨j, hj⟩ := hcov x
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsum : ∑ i, (fhat (c i) - g (c i)) ^ 2 ≤ N * ϵapp ^ 2 + N * εinner := by
    rw [div_le_iff₀ hNpos] at hrisk
    linarith
  have hcj : |fhat (c j) - g (c j)| ≤ √N * ϵapp + √(N * εinner) := by
    have h1 : (fhat (c j) - g (c j)) ^ 2 ≤ ∑ i, (fhat (c i) - g (c i)) ^ 2 :=
      Finset.single_le_sum (f := fun i => (fhat (c i) - g (c i)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : |fhat (c j) - g (c j)| ≤ √(N * ϵapp ^ 2 + N * εinner) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (h1.trans hsum)
    have ha : √(N * ϵapp ^ 2) = √N * ϵapp := by
      rw [Real.sqrt_mul hNpos.le, Real.sqrt_sq happ]
    rw [← ha]
    exact h2.trans (sqrt_add_le_sqrt_add_sqrt (by positivity))
  have h1 := hf x (c j)
  have h2 := hg (c j) x
  rw [dist_comm] at h2
  have h1' : Lfun * dist x (c j) ≤ Lfun * δ := mul_le_mul_of_nonneg_left hj hLfun
  have h2' : LT * dist x (c j) ≤ LT * δ := mul_le_mul_of_nonneg_left hj hLT
  have t1 := abs_sub_le (fhat x) (fhat (c j)) (g x)
  have t2 := abs_sub_le (fhat (c j)) (g (c j)) (g x)
  linarith

/-- The retraction error: for `Û`, `V̂` with orthonormal columns,
`‖Û Π_r(Ŝ) V̂ᵀ − Û Ŝ V̂ᵀ‖_F = (∑_{i ≥ r} σ_i(Ŝ)²)^{1/2}` (proof of Lemma 3 of arXiv 2610.06885,
Term 2, with the Frobenius norm; `Π_r = LeanDLRA.EckartYoung.truncation`). -/
lemma norm_retract_sub {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ] [DecidableEq κ]
    {U : Matrix m κ ℝ} {V : Matrix n κ ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix κ κ ℝ) (r : ℕ) :
    ‖U * LeanDLRA.EckartYoung.truncation S r * Vᵀ - U * S * Vᵀ‖ =
      √(∑ i ∈ Ico r (Fintype.card κ), (toEuclideanLin S).singularValues i ^ 2) := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hV,
    LeanDLRA.Frobenius.norm_mul_of_orthonormal hU, norm_sub_rev,
    LeanDLRA.EckartYoung.norm_sub_truncation]

/-- **One outer iteration of Algorithm 1 (DLR-NE)** of arXiv 2610.06885, with the data and
hypotheses used in Lemma 3. The iteration starts from a network whose Bellman target is
`g = T V⁽ᵏ⁾ : X → ℝ` and returns the network `x ↦ ⟪w, ϕ(W x)⟫`:
* `U`, `V` are the augmented bases `Û ∈ ℝ^{m×2r}`, `V̂ ∈ ℝ^{n×2r}` with orthonormal columns
  (line 4), `S` is the trained augmented core `Ŝ_{s*}` (line 6), `w` the trained output weights;
* `retract`: `W = Û Π_r(Ŝ) V̂ᵀ` (truncated-SVD retraction, lines 7–8);
* `weight_le`, `core_le`: `‖w‖ ≤ W_max` and `‖Ŝ‖_F ≤ S_max` (Assumption 4(a));
* `tail_le`: `(∑_{r ≤ i < 2r} σ_i(Ŝ)²)^{1/2} ≤ ϵ_retr` (the definition of `ϵ_retr`);
* `ghat` are the computed targets (line 2) with `|ĝ − g| ≤ ϵ_mm` (Assumption 1(h)), and `ĝ` is
  `L_T`-Lipschitz on `X` (the paper's `L_T`, Section 2.2);
* `fstar` is the candidate of Assumption 4(c) on the sample points, and `inner` is the
  inner-loop accuracy (Assumption 4(b)) for the empirical risk on the `δ`-covering `c`.
The paper fits against `ĝ` in the sketch of Lemma 3 and against `g` in Appendix B; taking
`ghat = g` gives the latter. -/
structure DLRNEStep {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (ϕ : ℝ → ℝ)
    {X : Set (EuclideanSpace ℝ n)} {N : ℕ} (c : Fin N → X) (r : ℕ)
    (ϵapp εinner ϵretr ϵmm Wmax Smax LT : ℝ) (g : X → ℝ) (w : EuclideanSpace ℝ m)
    (W : Matrix m n ℝ) where
  /-- The augmented left basis `Û`. -/
  U : Matrix m (Fin (2 * r)) ℝ
  /-- The trained augmented core `Ŝ_{s*}`. -/
  S : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ
  /-- The augmented right basis `V̂`. -/
  V : Matrix n (Fin (2 * r)) ℝ
  /-- The computed Bellman targets `ĝ`. -/
  ghat : X → ℝ
  /-- The candidate `f*` of Assumption 4(c). -/
  fstar : X → ℝ
  /-- `Û` has orthonormal columns. -/
  orthU : Uᵀ * U = 1
  /-- `V̂` has orthonormal columns. -/
  orthV : Vᵀ * V = 1
  /-- Truncated-SVD retraction. -/
  retract : W = U * LeanDLRA.EckartYoung.truncation S r * Vᵀ
  /-- Output-weight bound. -/
  weight_le : ‖w‖ ≤ Wmax
  /-- Core bound (Assumption 4(a)). -/
  core_le : ‖S‖ ≤ Smax
  /-- Retraction tail. -/
  tail_le : √(∑ i ∈ Ico r (2 * r), (toEuclideanLin S).singularValues i ^ 2) ≤ ϵretr
  /-- Min-max accuracy (Assumption 1(h)). -/
  minmax : ∀ x, |ghat x - g x| ≤ ϵmm
  /-- The computed target is `L_T`-Lipschitz. -/
  target_lip : ∀ x y, |ghat x - ghat y| ≤ LT * dist x y
  /-- Basis-augmented representability on the samples (Assumption 4(c)). -/
  approx : ∀ j, |fstar (c j) - ghat (c j)| ≤ ϵapp
  /-- Inner-loop accuracy (Assumption 4(b)). -/
  inner : (∑ j, (net ϕ w (U * S * Vᵀ) (c j) - ghat (c j)) ^ 2) / N ≤
    (∑ j, (fstar (c j) - ghat (c j)) ^ 2) / N + εinner

/-- The retracted iterate has rank `≤ r` (`A : F_r → F_r` in Lemma 3 of arXiv 2610.06885). -/
theorem DLRNEStep.rank_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {ϕ : ℝ → ℝ}
    {X : Set (EuclideanSpace ℝ n)} {N : ℕ} {c : Fin N → X} {r : ℕ}
    {ϵapp εinner ϵretr ϵmm Wmax Smax LT : ℝ} {g : X → ℝ} {w : EuclideanSpace ℝ m}
    {W : Matrix m n ℝ} (h : DLRNEStep ϕ c r ϵapp εinner ϵretr ϵmm Wmax Smax LT g w W) :
    W.rank ≤ r := by
  rw [h.retract]
  calc (h.U * LeanDLRA.EckartYoung.truncation h.S r * h.Vᵀ).rank
      ≤ (h.U * LeanDLRA.EckartYoung.truncation h.S r).rank := rank_mul_le_left _ _
    _ ≤ (LeanDLRA.EckartYoung.truncation h.S r).rank := rank_mul_le_right _ _
    _ ≤ r := LeanDLRA.EckartYoung.rank_truncation_le _ _

/-- **Lemma 3 (uniform single-step fitting error)**, arXiv 2610.06885, Lemma 3, eq. (38). For one
outer iteration `h : DLRNEStep …` of Algorithm 1 with Bellman target `g = T V⁽ᵏ⁾` on a state
space `X ⊂ ℝⁿ` with `‖x‖ ≤ R_X`, a `δ`-covering `{x_j}_{j<N}` (`N ≥ 1`), and an `Lϕ`-Lipschitz
activation, the retracted network `f(x) = ⟪w, ϕ(W x)⟫` has rank `≤ r` and
`|f(x) − g(x)| ≤ ε_total := √N ϵ_app + √(N ε_inner) + (L_fun + L_T) δ + Lϕ W_max R_X ϵ_retr
+ ϵ_mm` on `X`, with `L_fun = Lϕ W_max S_max` (the Lipschitz constant of the fitted network
`f̂(x) = ⟪w, ϕ(Û Ŝ V̂ᵀ x)⟫`, derived from Assumption 4(a)). The proof is the paper's
decomposition `‖f − g‖ ≤ ‖f − f̂‖ + ‖f̂ − ĝ‖ + ‖ĝ − g‖` with Lemma 2 for the middle term. -/
theorem single_step_error {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (ϕ : ℝ → ℝ)
    {Lϕ : ℝ} (hLϕ : 0 ≤ Lϕ) (hϕ : ∀ s t, |ϕ s - ϕ t| ≤ Lϕ * |s - t|)
    {X : Set (EuclideanSpace ℝ n)} {RX : ℝ} (hRX : ∀ x : X, ‖(x : EuclideanSpace ℝ n)‖ ≤ RX)
    {N : ℕ} (hN : 0 < N) (c : Fin N → X) {δ : ℝ} (hcov : ∀ x, ∃ j, dist x (c j) ≤ δ)
    {r : ℕ} {ϵapp εinner ϵretr ϵmm Wmax Smax LT : ℝ} (hLT : 0 ≤ LT) {g : X → ℝ}
    {w : EuclideanSpace ℝ m} {W : Matrix m n ℝ}
    (h : DLRNEStep ϕ c r ϵapp εinner ϵretr ϵmm Wmax Smax LT g w W) :
    W.rank ≤ r ∧ ∀ x : X, |net ϕ w W x - g x| ≤ √N * ϵapp + √(N * εinner) +
      (Lϕ * Wmax * Smax + LT) * δ + Lϕ * Wmax * RX * ϵretr + ϵmm := by
  refine ⟨h.rank_le, fun x => ?_⟩
  have hWmax : 0 ≤ Wmax := (norm_nonneg _).trans h.weight_le
  have hSmax : 0 ≤ Smax := (norm_nonneg _).trans h.core_le
  have happ0 : 0 ≤ ϵapp := (abs_nonneg _).trans (h.approx ⟨0, hN⟩)
  -- (iv) the retraction term
  have hretr : |net ϕ w W x - net ϕ w (h.U * h.S * h.Vᵀ) x| ≤ Lϕ * Wmax * RX * ϵretr := by
    have h1 := abs_net_sub_net_weight_le ϕ hLϕ hϕ w W (h.U * h.S * h.Vᵀ) x
    have h2 : ‖W - h.U * h.S * h.Vᵀ‖ ≤ ϵretr := by
      have e : W - h.U * h.S * h.Vᵀ =
          h.U * LeanDLRA.EckartYoung.truncation h.S r * h.Vᵀ - h.U * h.S * h.Vᵀ :=
        congrArg (· - h.U * h.S * h.Vᵀ) h.retract
      rw [e, norm_retract_sub h.orthU h.orthV, Fintype.card_fin]
      exact h.tail_le
    have hx := hRX x
    have hr0 : 0 ≤ ϵretr := (norm_nonneg _).trans h2
    have a1 : ‖w‖ * Lϕ ≤ Wmax * Lϕ := mul_le_mul_of_nonneg_right h.weight_le hLϕ
    have a2 : ‖w‖ * Lϕ * ‖W - h.U * h.S * h.Vᵀ‖ ≤ Wmax * Lϕ * ϵretr :=
      mul_le_mul a1 h2 (norm_nonneg _) (mul_nonneg hWmax hLϕ)
    have a3 := mul_le_mul a2 hx (norm_nonneg _) (mul_nonneg (mul_nonneg hWmax hLϕ) hr0)
    calc _ ≤ ‖w‖ * Lϕ * ‖W - h.U * h.S * h.Vᵀ‖ * ‖(x : EuclideanSpace ℝ n)‖ := h1
      _ ≤ Wmax * Lϕ * ϵretr * RX := a3
      _ = _ := by ring
  -- (i)–(iii) the bridge term
  have hW : ‖h.U * h.S * h.Vᵀ‖ = ‖h.S‖ := by
    rw [LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal h.orthV,
      LeanDLRA.Frobenius.norm_mul_of_orthonormal h.orthU]
  have hLfun : ∀ y z : X, |net ϕ w (h.U * h.S * h.Vᵀ) y - net ϕ w (h.U * h.S * h.Vᵀ) z| ≤
      (Lϕ * Wmax * Smax) * dist y z := by
    intro y z
    have h1 := abs_net_sub_net_le ϕ hLϕ hϕ w (h.U * h.S * h.Vᵀ) y z
    rw [Subtype.dist_eq, dist_eq_norm]
    calc _ ≤ ‖w‖ * Lϕ * ‖h.U * h.S * h.Vᵀ‖ * ‖(y : EuclideanSpace ℝ n) - z‖ := h1
      _ ≤ Wmax * Lϕ * Smax * ‖(y : EuclideanSpace ℝ n) - z‖ := by
          rw [hW]
          gcongr
          · exact h.weight_le
          · exact h.core_le
      _ = _ := by ring
  have hrisk := empirical_risk_le c (fhat := fun y : X => net ϕ w (h.U * h.S * h.Vᵀ) y)
    h.approx h.inner
  have hbridge := bridge_uniform_error hN c hcov
    (fhat := fun y : X => net ϕ w (h.U * h.S * h.Vᵀ) y) (by positivity) hLT hLfun h.target_lip
    happ0 hrisk x
  have hmm := h.minmax x
  have t1 := abs_sub_le (net ϕ w W x) (net ϕ w (h.U * h.S * h.Vᵀ) x) (g x)
  have t2 := abs_sub_le (net ϕ w (h.U * h.S * h.Vᵀ) x) (h.ghat x) (g x)
  linarith

/-! ### Theorem 2: convergence of DLR-NE -/

/-- **Theorem 2, error-propagation core** (arXiv 2610.06885, Theorem 2, display (39)), in an
abstract normed group. If the one-step error satisfies `‖V_{k+1} − V*‖ ≤ γ ‖V_k − V*‖ + ε_total`
with `γ ∈ [0, 1)` and `ε_total ≥ 0`, then `‖V_k − V*‖ ≤ γᵏ ‖V_0 − V*‖ + ε_total/(1 − γ)`. Here the
one-step inequality is the hypothesis `hstep` (conditional form). For the DLR-NE iterates it is
derived from Prop. 1 and Lemma 3 in `dlrne_one_step`, and Theorem 2 itself is
`dlrne_convergence`. -/
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

/-- **Theorem 2, one-step recursion** (arXiv 2610.06885, proof of Theorem 2, first display): if
the current iterate `V⁽ᵏ⁾(x) = ⟪w, ϕ(W x)⟫` satisfies `|V⁽ᵏ⁾ − V*| ≤ e` on `X` and one DLR-NE
iteration `h` (Lemma 3's data, with Bellman target `T V⁽ᵏ⁾`) produces `V⁽ᵏ⁺¹⁾(x) = ⟪w', ϕ(W' x)⟫`,
then `|V⁽ᵏ⁺¹⁾ − V*| ≤ γ e + ε_total` on `X`. Derived from Prop. 1 (`bellman_contraction`),
Lemma 3 (`single_step_error`) and `T V* = V*` (eq. (7)); this is the hypothesis `hstep` of
`error_propagation`. The game is as in `bellman_contraction` with state space `X`; `V*` is a
bounded measurable fixed point of `T`. -/
theorem dlrne_one_step {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A D : Type*} [MeasurableSpace A] [MeasurableSpace D] [Nonempty A] [Nonempty D]
    {X : Set (EuclideanSpace ℝ n)} (P : X → Kernel (A × D) X) [∀ x, IsMarkovKernel (P x)]
    (rew : X → A × D → ℝ) (hrew_meas : ∀ x, Measurable (rew x)) {Rmax : ℝ}
    (hrew : ∀ x ad, |rew x ad| ≤ Rmax) {γ : ℝ} (hγ : 0 ≤ γ)
    {Vstar : X → ℝ} (hVs : Measurable Vstar) (hVsb : ∃ B, ∀ x, |Vstar x| ≤ B)
    (hfix : ∀ x, bellmanOp P rew γ Vstar x = Vstar x)
    (ϕ : ℝ → ℝ) {Lϕ : ℝ} (hLϕ : 0 ≤ Lϕ) (hϕ : ∀ s t, |ϕ s - ϕ t| ≤ Lϕ * |s - t|)
    {RX : ℝ} (hRX : ∀ x : X, ‖(x : EuclideanSpace ℝ n)‖ ≤ RX)
    {N : ℕ} (hN : 0 < N) (c : Fin N → X) {δ : ℝ} (hcov : ∀ x, ∃ j, dist x (c j) ≤ δ)
    {r : ℕ} {ϵapp εinner ϵretr ϵmm Wmax Smax LT : ℝ} (hLT : 0 ≤ LT)
    {w w' : EuclideanSpace ℝ m} {W W' : Matrix m n ℝ}
    (h : DLRNEStep ϕ c r ϵapp εinner ϵretr ϵmm Wmax Smax LT
      (bellmanOp P rew γ fun x => net ϕ w W x) w' W')
    {e : ℝ} (he : ∀ x : X, |net ϕ w W x - Vstar x| ≤ e) (x : X) :
    |net ϕ w' W' x - Vstar x| ≤ γ * e + (√N * ϵapp + √(N * εinner) +
      (Lϕ * Wmax * Smax + LT) * δ + Lϕ * Wmax * RX * ϵretr + ϵmm) := by
  have h3 := (single_step_error ϕ hLϕ hϕ hRX hN c hcov hLT h).2 x
  have hmeas : Measurable fun x : X => net ϕ w W x :=
    ((continuous_net ϕ hLϕ hϕ w W).comp continuous_subtype_val).measurable
  have hbdd : ∃ B, ∀ x : X, |net ϕ w W x| ≤ B :=
    ⟨‖w‖ * (‖elemAct ϕ (0 : EuclideanSpace ℝ m)‖ + Lϕ * ‖W‖ * RX), fun x =>
      (abs_net_le ϕ hLϕ hϕ w W x).trans (by gcongr; exact hRX x)⟩
  have hP := bellman_contraction P rew hrew_meas hrew hγ hmeas hVs hbdd hVsb he x
  rw [hfix] at hP
  have t := abs_sub_le (net ϕ w' W' x) (bellmanOp P rew γ (fun x => net ϕ w W x) x) (Vstar x)
  linarith

/-- **Theorem 2 (convergence of DLR-NE)**, arXiv 2610.06885, Theorem 2, eq. (39), without the
one-step hypothesis of `error_propagation`. Let `V⁽ᵏ⁾(x) = ⟪w_k, ϕ(W_k x)⟫` be the DLR-NE iterates
on the state space `X ⊂ ℝⁿ`, where every outer iteration `k → k+1` is a `DLRNEStep` for the Bellman
target `T V⁽ᵏ⁾` (Algorithm 1 under Assumptions 1, 2 and 4, recorded as in Lemma 3). Let `V*` be a
bounded measurable fixed point of the Bellman operator (eq. (7)), `0 ≤ γ < 1`, and
`|V⁽⁰⁾ − V*| ≤ c₀` on `X` (e.g. `c₀ = ‖V⁽⁰⁾ − V*‖_∞`). Then for all `k`,
`|V⁽ᵏ⁾ − V*| ≤ γᵏ c₀ + ε_total/(1 − γ)` on `X`, with `ε_total` of eq. (38) and
`L_fun = Lϕ W_max S_max`. The one-step bound is `dlrne_one_step` (Prop. 1 and Lemma 3). -/
theorem dlrne_convergence {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A D : Type*} [MeasurableSpace A] [MeasurableSpace D] [Nonempty A] [Nonempty D]
    {X : Set (EuclideanSpace ℝ n)} (P : X → Kernel (A × D) X) [∀ x, IsMarkovKernel (P x)]
    (rew : X → A × D → ℝ) (hrew_meas : ∀ x, Measurable (rew x)) {Rmax : ℝ}
    (hrew : ∀ x ad, |rew x ad| ≤ Rmax) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {Vstar : X → ℝ} (hVs : Measurable Vstar) (hVsb : ∃ B, ∀ x, |Vstar x| ≤ B)
    (hfix : ∀ x, bellmanOp P rew γ Vstar x = Vstar x)
    (ϕ : ℝ → ℝ) {Lϕ : ℝ} (hLϕ : 0 ≤ Lϕ) (hϕ : ∀ s t, |ϕ s - ϕ t| ≤ Lϕ * |s - t|)
    {RX : ℝ} (hRX : ∀ x : X, ‖(x : EuclideanSpace ℝ n)‖ ≤ RX)
    {N : ℕ} (hN : 0 < N) (c : Fin N → X) {δ : ℝ} (hcov : ∀ x, ∃ j, dist x (c j) ≤ δ)
    {r : ℕ} {ϵapp εinner ϵretr ϵmm Wmax Smax LT : ℝ} (hLT : 0 ≤ LT)
    (w : ℕ → EuclideanSpace ℝ m) (W : ℕ → Matrix m n ℝ)
    (step : ∀ k, DLRNEStep ϕ c r ϵapp εinner ϵretr ϵmm Wmax Smax LT
      (bellmanOp P rew γ fun x => net ϕ (w k) (W k) x) (w (k + 1)) (W (k + 1)))
    {c₀ : ℝ} (hc₀ : ∀ x : X, |net ϕ (w 0) (W 0) x - Vstar x| ≤ c₀) (k : ℕ) (x : X) :
    |net ϕ (w k) (W k) x - Vstar x| ≤ γ ^ k * c₀ + (√N * ϵapp + √(N * εinner) +
      (Lϕ * Wmax * Smax + LT) * δ + Lϕ * Wmax * RX * ϵretr + ϵmm) / (1 - γ) := by
  have hstep : ∀ k e, (∀ x : X, |net ϕ (w k) (W k) x - Vstar x| ≤ e) → ∀ x : X,
      |net ϕ (w (k + 1)) (W (k + 1)) x - Vstar x| ≤ γ * e + (√N * ϵapp + √(N * εinner) +
        (Lϕ * Wmax * Smax + LT) * δ + Lϕ * Wmax * RX * ϵretr + ϵmm) := fun k e he x =>
    dlrne_one_step P rew hrew_meas hrew hγ0 hVs hVsb hfix ϕ hLϕ hϕ hRX hN c hcov hLT (step k) he x
  have hε0 : 0 ≤ √N * ϵapp + √(N * εinner) + (Lϕ * Wmax * Smax + LT) * δ +
      Lϕ * Wmax * RX * ϵretr + ϵmm :=
    (abs_nonneg _).trans ((single_step_error ϕ hLϕ hϕ hRX hN c hcov hLT (step 0)).2 x)
  generalize √N * ϵapp + √(N * εinner) + (Lϕ * Wmax * Smax + LT) * δ +
      Lϕ * Wmax * RX * ϵretr + ϵmm = ε at hstep hε0 ⊢
  have hk : ∀ k, ∀ x : X, |net ϕ (w k) (W k) x - Vstar x| ≤
      γ ^ k * c₀ + ε * ∑ j ∈ range k, γ ^ j := by
    intro k
    induction k with
    | zero => intro x; simpa using hc₀ x
    | succ k ih =>
      intro x
      refine (hstep k _ ih x).trans (le_of_eq ?_)
      rw [geom_sum_succ, pow_succ']
      ring
  have hgeom : ∑ j ∈ range k, γ ^ j ≤ 1 / (1 - γ) := by
    have h := geom_sum_Ico_le_of_lt_one hγ0 hγ1 (m := 0) (n := k)
    rw [pow_zero, ← Finset.range_eq_Ico] at h
    exact h
  have hεgeom : ε * ∑ j ∈ range k, γ ^ j ≤ ε / (1 - γ) := by
    rw [show ε / (1 - γ) = ε * (1 / (1 - γ)) by ring]
    exact mul_le_mul_of_nonneg_left hgeom hε0
  linarith [hk k x]

/-- **Theorem 2, steady state** (arXiv 2610.06885, Theorem 2:
`lim sup_k ‖V⁽ᵏ⁾ − V*‖_∞ ≤ ε_total/(1 − γ)`), in the form: for every `η > 0`, eventually
`|V⁽ᵏ⁾ − V*| ≤ ε_total/(1 − γ) + η` on all of `X`. Same hypotheses as `dlrne_convergence`. -/
theorem dlrne_limsup_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A D : Type*} [MeasurableSpace A] [MeasurableSpace D] [Nonempty A] [Nonempty D]
    {X : Set (EuclideanSpace ℝ n)} (P : X → Kernel (A × D) X) [∀ x, IsMarkovKernel (P x)]
    (rew : X → A × D → ℝ) (hrew_meas : ∀ x, Measurable (rew x)) {Rmax : ℝ}
    (hrew : ∀ x ad, |rew x ad| ≤ Rmax) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {Vstar : X → ℝ} (hVs : Measurable Vstar) (hVsb : ∃ B, ∀ x, |Vstar x| ≤ B)
    (hfix : ∀ x, bellmanOp P rew γ Vstar x = Vstar x)
    (ϕ : ℝ → ℝ) {Lϕ : ℝ} (hLϕ : 0 ≤ Lϕ) (hϕ : ∀ s t, |ϕ s - ϕ t| ≤ Lϕ * |s - t|)
    {RX : ℝ} (hRX : ∀ x : X, ‖(x : EuclideanSpace ℝ n)‖ ≤ RX)
    {N : ℕ} (hN : 0 < N) (c : Fin N → X) {δ : ℝ} (hcov : ∀ x, ∃ j, dist x (c j) ≤ δ)
    {r : ℕ} {ϵapp εinner ϵretr ϵmm Wmax Smax LT : ℝ} (hLT : 0 ≤ LT)
    (w : ℕ → EuclideanSpace ℝ m) (W : ℕ → Matrix m n ℝ)
    (step : ∀ k, DLRNEStep ϕ c r ϵapp εinner ϵretr ϵmm Wmax Smax LT
      (bellmanOp P rew γ fun x => net ϕ (w k) (W k) x) (w (k + 1)) (W (k + 1)))
    {c₀ : ℝ} (hc₀ : ∀ x : X, |net ϕ (w 0) (W 0) x - Vstar x| ≤ c₀) {η : ℝ} (hη : 0 < η) :
    ∃ K, ∀ k ≥ K, ∀ x : X, |net ϕ (w k) (W k) x - Vstar x| ≤ (√N * ϵapp + √(N * εinner) +
      (Lϕ * Wmax * Smax + LT) * δ + Lϕ * Wmax * RX * ϵretr + ϵmm) / (1 - γ) + η := by
  have ht : Filter.Tendsto (fun k : ℕ => γ ^ k * c₀) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const c₀
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hη))
  refine ⟨K, fun k hk x => ?_⟩
  have h1 := dlrne_convergence P rew hrew_meas hrew hγ0 hγ1 hVs hVsb hfix ϕ hLϕ hϕ hRX hN c hcov
    hLT w W step hc₀ k x
  have h2 := hK k hk
  linarith

/-! ### Non-vacuity -/

/-- The hypotheses of `dlrne_convergence` can all be met: the one-point state space
`X = {0} ⊂ ℝ¹`, one action per player, zero reward, `γ = 1/2`, the zero network, `V* = 0`,
rank `r = 0` and all error budgets `0`. -/
example : ∀ (k : ℕ) (x : ({0} : Set (EuclideanSpace ℝ (Fin 1)))),
    |net id (0 : EuclideanSpace ℝ (Fin 1)) (0 : Matrix (Fin 1) (Fin 1) ℝ) x - 0| ≤
      (1 / 2 : ℝ) ^ k * 0 + (√((1 : ℕ) : ℝ) * 0 + √(((1 : ℕ) : ℝ) * 0) + (1 * 0 * 0 + 0) * 0 +
        1 * 0 * 0 * 0 + 0) / (1 - 1 / 2) := by
  let X : Set (EuclideanSpace ℝ (Fin 1)) := {0}
  let P : X → Kernel (Unit × Unit) X := fun x => Kernel.const _ (Measure.dirac x)
  let rew : X → Unit × Unit → ℝ := fun _ _ => 0
  have hnet : ∀ (W : Matrix (Fin 1) (Fin 1) ℝ) (y : EuclideanSpace ℝ (Fin 1)),
      net id (0 : EuclideanSpace ℝ (Fin 1)) W y = 0 := fun W y => by simp [net]
  have hT0 : ∀ x, bellmanOp P rew (1 / 2) (fun _ => 0) x = 0 := fun x => by
    simp [bellmanOp, bellmanPayoff, rew]
  have hT : ∀ x, bellmanOp P rew (1 / 2)
      (fun y : X => net id (0 : EuclideanSpace ℝ (Fin 1)) (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (y : EuclideanSpace ℝ (Fin 1))) x = 0 := fun x => by
    simp only [hnet]; exact hT0 x
  let c : Fin 1 → X := fun _ => ⟨0, Set.mem_singleton 0⟩
  have hsub : ∀ y z : X, y = z := fun y z =>
    Subtype.ext ((Set.mem_singleton_iff.mp y.2).trans (Set.mem_singleton_iff.mp z.2).symm)
  let step : ℕ → DLRNEStep id c 0 0 0 0 0 0 0 0
      (bellmanOp P rew (1 / 2) fun x =>
        net id (0 : EuclideanSpace ℝ (Fin 1)) (0 : Matrix (Fin 1) (Fin 1) ℝ) x)
      (0 : EuclideanSpace ℝ (Fin 1)) (0 : Matrix (Fin 1) (Fin 1) ℝ) := fun _ =>
    { U := 0, S := 0, V := 0, ghat := fun _ => 0, fstar := fun _ => 0
      orthU := by ext i; exact absurd i.2 (by norm_num)
      orthV := by ext i; exact absurd i.2 (by norm_num)
      retract := by simp
      weight_le := by simp
      core_le := by simp
      tail_le := by simp
      minmax := fun x => by rw [hT x]; simp
      target_lip := fun x y => by simp
      approx := fun j => by simp
      inner := by simp [hnet] }
  intro k x
  exact dlrne_convergence P rew (fun _ => measurable_const) (Rmax := 0) (fun _ _ => by simp [rew])
    (by norm_num) (by norm_num) measurable_const ⟨0, fun _ => by simp⟩ hT0 id zero_le_one
    (fun s t => by simp) (RX := 0) (fun y => by simp [Set.mem_singleton_iff.mp y.2]) Nat.one_pos c
    (δ := 0)
    (fun y => ⟨0, by rw [hsub y (c 0)]; simp⟩) le_rfl (fun _ => 0) (fun _ => 0) step
    (fun y => by simp [hnet]) k x

end LeanDLRA.Literature.P2610_06885
