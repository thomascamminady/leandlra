import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Training.FactorizedDynamics

/-!
# Singular-value dynamics and implicit bias in factorized training with weight decay

Open problem OP-TR-43 of `docs/catalogue/survey/open-problems.json` (arXiv 2209.13569, Sec. 3.3 and
4.2):
with L2 decay `λ (‖U‖² + ‖V‖²) / 2` on the factors of `W = U Vᵀ`, singular values are claimed to
evolve "rich get richer, poor get poorer", with `σ̇ᵢ = -2σᵢ ⟨∇L, uᵢvᵢᵀ⟩ - 2λσᵢ`, and the
effective rank `‖W‖_* / ‖W‖_op` to drop; "Frobenius decay" `λ ‖U Vᵀ‖² / 2` is reported to keep
it higher.

This module proves exact statements about the two flows, for an **arbitrary gradient curve**
`G(t)` (hence every loss) and arbitrary, not necessarily balanced, factors, without differentiating
singular values.  The quadratic form `F_Q(t) = ‖U(t) Q‖² + ‖V(t) Q‖²` (`Q` any test matrix:
`Q = 1` gives `‖U‖² + ‖V‖²`, a column gives the Rayleigh quotient of `UᵀU + VᵀV`) is the object.

* `hasDerivAt_product`: along `U̇ = -G V - λ U`, `V̇ = -Gᵀ U - λ V` the product satisfies
  `Ẇ = -(G V Vᵀ + U Uᵀ G) - 2λ W`.  The decay enters only as the uniform rescaling `-2λW`.
* `exp_smul_solves_undecayed`: `(e^{λt} U, e^{λt} V)` solves the decay-free flow for the same
  gradient curve.  So every scale-invariant functional of `W` (effective rank, normalized singular
  value profile) is the same with and without decay once the gradient curve is fixed.
* `hasDerivAt_gramForm`: `Ḟ_Q = -4 ⟪U Q, G V Q⟫ - 2λ F_Q`.
* `gramForm_le_exp`, `exp_le_gramForm` (**envelope theorem**): if `‖G(t)‖_op ≤ g`, then
  `e^{-2(g+λ)t} F_Q(0) ≤ F_Q(t) ≤ e^{2(g-λ)t} F_Q(0)` for `t ≥ 0` and every `Q`.  In Loewner
  order: `e^{-2(g+λ)t} N(0) ≤ N(t) ≤ e^{2(g-λ)t} N(0)` for `N = UᵀU + VᵀV`
  (`posSemidef_exp_smul_sub_gram`, `posSemidef_gram_sub_exp_smul`), hence the same for every
  sorted eigenvalue of `N` (Loewner monotonicity, `LeanDLRA.Classical.CourantFischer`).  For
  balanced factors `N = 2 UᵀU`, whose eigenvalues are the singular values of `W` (a standard
  fact not re-proved here).
* `gramForm_ratio_le`: ratios `F_{Q₁}(t) / F_{Q₂}(t)` move by at most `e^{4gt}`, independently of
  `λ`.  Weight decay cannot by itself change the effective rank; the claimed mechanism "growth
  rates scale with `σᵢ`" is exactly the scale-free part of the dynamics.
* `kernel_invariant`: `U(t) q = 0 ∧ V(t) q = 0 ↔ U(0) q = 0 ∧ V(0) q = 0`; the common kernel,
  hence `rank` of balanced factors, is conserved for all finite times (zero singular values never
  activate, nonzero ones never vanish in finite time).
* `norm_product_le_exp`, `tendsto_product_zero`: if `g < λ`, `‖W(t)‖ ≤ e^{-2(λ-g)t} F_1(0) / 2`
  and `W(t) → 0`: the collapse threshold is `‖∇L‖_op < λ`.  (Remark: `W = 0` is a fixed point
  of the factor flow, but of the full-matrix flow `Ẇ = -∇L - λW` only if `∇L(0) = 0`.)
* `scalar_attains_envelope`: the envelope is attained (`U = V = e^{(g-λ)t} u₀`, `G = -g`).

The Frobenius-decay flow `U̇ = -(G + λ W) V`, `V̇ = -(G + λ W)ᵀ U` is the decay-free flow for the
gradient curve `G + λ W`, so it conserves `UᵀU - VᵀV` exactly (`balance_const_frobeniusDecay`);
for balanced factors the decay term in `d/dt ‖U q‖²` is `-2λ ‖UᵀU q‖²`, quadratic rather than
linear in the Gram matrix (`hasDerivAt_rayleigh_frobeniusDecay`), which gives the a priori cap
`‖U(t) q‖² ≤ max (‖U(0) q‖², g / λ)` for unit `q` (`rayleigh_le_max_frobeniusDecay`), whereas
under L2 decay the same quantity can grow like `e^{2(g-λ)t}`.  Under the pure Frobenius-decay term
the effective rank `‖U‖⁴ / ‖UᵀU‖² = (tr M)² / tr(M²)` of `M = UᵀU` (equal to `(Σσᵢ)² / Σσᵢ²`
for balanced factors) is nondecreasing (`effectiveRank_monotone_frobeniusDecay`), and the factor
never dies in finite time (`exp_mul_le_normSq_pureFrobeniusDecay`); under the pure L2 term the
effective rank is constant (`effectiveRank_const_l2Decay`).

Related prior work: Arora–Cohen–Hu–Luo 2019 (singular value dynamics of
balanced deep factorizations without decay), Srebro–Shraibman 2005 (nuclear norm as the balanced
factor penalty), and `LeanDLRA.FactorizedDynamics.balance_eq_exp`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpTR43

open LeanDLRA

variable {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p]

/-! ### Scalar comparison lemmas -/

/-- If `F' ≤ c F` on `[0, ∞)`, then `F t ≤ e^{c t} F 0` for `t ≥ 0`. -/
theorem le_exp_mul_of_deriv_le {F F' : ℝ → ℝ} {c : ℝ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (h : ∀ t, 0 ≤ t → F' t ≤ c * F t) {t : ℝ} (ht : 0 ≤ t) :
    F t ≤ Real.exp (c * t) * F 0 := by
  have hφ : ∀ s, HasDerivAt (fun s => Real.exp (-c * s) * F s)
      (Real.exp (-c * s) * (F' s - c * F s)) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-c * s)) (Real.exp (-c * s) * (-c)) s := by
      simpa using ((hasDerivAt_id' s).const_mul (-c)).exp
    convert he.mul (hF s) using 1
    ring
  have hanti : AntitoneOn (fun s => Real.exp (-c * s) * F s) (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun s _ => (hφ s).continuousAt.continuousWithinAt)
      (fun s _ => (hφ s).differentiableAt.differentiableWithinAt) (fun s hs => by
      rw [interior_Ici] at hs
      rw [(hφ s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [h s hs.le]))
  have h0 := hanti (Set.mem_Ici.2 le_rfl) ht ht
  simp only [mul_zero, Real.exp_zero, one_mul] at h0
  calc F t = Real.exp (c * t) * (Real.exp (-c * t) * F t) := by
        rw [← mul_assoc, ← Real.exp_add, show c * t + -c * t = 0 by ring, Real.exp_zero,
          one_mul]
    _ ≤ Real.exp (c * t) * F 0 := by gcongr

/-- If `c F ≤ F'` on `[0, ∞)`, then `e^{c t} F 0 ≤ F t` for `t ≥ 0`. -/
theorem exp_mul_le_of_le_deriv {F F' : ℝ → ℝ} {c : ℝ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (h : ∀ t, 0 ≤ t → c * F t ≤ F' t) {t : ℝ} (ht : 0 ≤ t) : Real.exp (c * t) * F 0 ≤ F t := by
  have := le_exp_mul_of_deriv_le (F := fun s => -F s) (F' := fun s => -F' s) (c := c)
    (fun s => (hF s).neg) (fun s hs => by linarith [h s hs]) ht
  linarith

/-- **Barrier lemma**: if `F' ≤ 2 F (g - λ F)` on `[0, ∞)` with `λ > 0`, `g ≥ 0`, then
`F t ≤ max (F 0) (g / λ)` for `t ≥ 0`. -/
theorem le_max_of_deriv_le_logistic {F F' : ℝ → ℝ} {g lam : ℝ} (hg : 0 ≤ g) (hlam : 0 < lam)
    (hF : ∀ t, HasDerivAt F (F' t) t) (h : ∀ t, 0 ≤ t → F' t ≤ 2 * F t * (g - lam * F t))
    {t : ℝ} (ht : 0 ≤ t) : F t ≤ max (F 0) (g / lam) := by
  set c := max (F 0) (g / lam) with hc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hgc : g / lam ≤ c := le_max_right _ _
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := F) (f' := F') (a := 0) (b := t)
    (B := fun _ => c + ε) (B' := fun _ => 0)
    (fun s _ => (hF s).continuousAt.continuousWithinAt)
    (fun s _ => (hF s).hasDerivWithinAt) (by linarith [le_max_left (F 0) (g / lam)])
    continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _) (fun s hs hsB => by
      have h1 := h s hs.1
      have hFs : g / lam < F s := by rw [hsB]; linarith
      have hpos : 0 < F s := by linarith [div_nonneg hg hlam.le]
      have hneg : g - lam * F s < 0 := by
        rw [div_lt_iff₀ hlam] at hFs; linarith
      change F' s < 0
      nlinarith)
  exact key ⟨ht, le_rfl⟩

/-! ### Operator-norm bounds in Frobenius form -/

/-- Column-wise operator-norm bound: if `‖A y‖² ≤ g² ‖y‖²` for all vectors `y`, then
`‖A Y‖ ≤ g ‖Y‖` in the Frobenius norm. -/
theorem norm_mul_le_of_mulVec_le {A : Matrix m n ℝ} {g : ℝ} (hg : 0 ≤ g)
    (hA : ∀ y : n → ℝ, (A *ᵥ y) ⬝ᵥ (A *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) (Y : Matrix n p ℝ) :
    ‖A * Y‖ ≤ g * ‖Y‖ := by
  have L : ‖A * Y‖ ^ 2 = ∑ j, ∑ i, (A * Y) i j ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Finset.sum_comm]
  have R : ‖Y‖ ^ 2 = ∑ j, ∑ i, Y i j ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Finset.sum_comm]
  have hsq : ‖A * Y‖ ^ 2 ≤ (g * ‖Y‖) ^ 2 := by
    rw [mul_pow, L, R, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := hA (fun i => Y i j)
    have hcol : ∀ i, (A *ᵥ fun i => Y i j) i = (A * Y) i j := fun i => by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    simpa only [dotProduct, hcol, sq] using h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- `|⟪X, A Y⟫| ≤ g ‖X‖ ‖Y‖` when `‖A‖_op ≤ g`. -/
theorem abs_inner_mul_le_of_mulVec_le {A : Matrix m n ℝ} {g : ℝ} (hg : 0 ≤ g)
    (hA : ∀ y : n → ℝ, (A *ᵥ y) ⬝ᵥ (A *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) (X : Matrix m p ℝ)
    (Y : Matrix n p ℝ) : |⟪X, A * Y⟫| ≤ g * ‖X‖ * ‖Y‖ :=
  calc |⟪X, A * Y⟫| ≤ ‖X‖ * ‖A * Y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖X‖ * (g * ‖Y‖) := by gcongr; exact norm_mul_le_of_mulVec_le hg hA Y
    _ = g * ‖X‖ * ‖Y‖ := by ring

/-! ### The L2-decayed factor flow -/

section L2

variable {U : ℝ → Matrix m k ℝ} {V : ℝ → Matrix n k ℝ} {G : ℝ → Matrix m n ℝ} {lam : ℝ}

/-- **Product dynamics under L2 decay**: along `U̇ = -G V - λ U`, `V̇ = -Gᵀ U - λ V`,
`Ẇ = -(G V Vᵀ + U Uᵀ G) - 2λ W` for `W = U Vᵀ`.  The decay acts on `W` as a uniform rescaling. -/
theorem hasDerivAt_product {t : ℝ} (hU : HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) :
    HasDerivAt (fun t => U t * (V t)ᵀ)
      (-(G t * V t * (V t)ᵀ + U t * (U t)ᵀ * G t) - (2 * lam) • (U t * (V t)ᵀ)) t := by
  convert Frobenius.hasDerivAt_mul hU (Frobenius.hasDerivAt_transpose hV) using 1
  simp only [Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  module

/-- **Weight decay is a change of variables**: if `(U, V)` solves the L2-decayed flow for the
gradient curve `G`, then `(e^{λt} U, e^{λt} V)` solves the decay-free flow `U̇ = -G V`,
`V̇ = -Gᵀ U` for the same curve.  Scale-invariant functionals of `W` therefore coincide. -/
theorem exp_smul_solves_undecayed (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (t : ℝ) :
    HasDerivAt (fun t => Real.exp (lam * t) • U t)
        (-(G t * (Real.exp (lam * t) • V t))) t ∧
      HasDerivAt (fun t => Real.exp (lam * t) • V t)
        (-((G t)ᵀ * (Real.exp (lam * t) • U t))) t := by
  have he : HasDerivAt (fun t => Real.exp (lam * t)) (Real.exp (lam * t) * lam) t := by
    simpa using ((hasDerivAt_id' t).const_mul lam).exp
  constructor
  · convert he.smul (hU t) using 1
    simp only [Matrix.mul_smul, smul_sub, smul_smul]
    module
  · convert he.smul (hV t) using 1
    simp only [Matrix.mul_smul, smul_sub, smul_smul]
    module

/-- Derivative of the quadratic form `F_Q = ‖U Q‖² + ‖V Q‖²` along the L2-decayed flow:
`Ḟ_Q = -4 ⟪U Q, G (V Q)⟫ - 2λ F_Q`. -/
theorem hasDerivAt_gramForm {t : ℝ} (hU : HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (Q : Matrix k p ℝ) :
    HasDerivAt (fun t => ‖U t * Q‖ ^ 2 + ‖V t * Q‖ ^ 2)
      (-4 * ⟪U t * Q, G t * (V t * Q)⟫ - 2 * lam * (‖U t * Q‖ ^ 2 + ‖V t * Q‖ ^ 2)) t := by
  have h1 := (Frobenius.hasDerivAt_mul_const Q hU).norm_sq
  have h2 := (Frobenius.hasDerivAt_mul_const Q hV).norm_sq
  convert h1.add h2 using 1
  simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, inner_sub_right, inner_neg_right,
    inner_smul_right, Matrix.mul_assoc]
  have e : ⟪V t * Q, (G t)ᵀ * (U t * Q)⟫ = ⟪G t * (V t * Q), U t * Q⟫ := by
    rw [Frobenius.inner_mul_left', Matrix.transpose_transpose]
  rw [e, real_inner_comm (G t * (V t * Q)), real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  ring

variable {g : ℝ}

/-- The first-order bound `|4 ⟪U Q, G V Q⟫| ≤ 2 g F_Q` from `‖G‖_op ≤ g`. -/
theorem abs_four_mul_inner_le (hg : 0 ≤ g)
    (hG : ∀ y : n → ℝ, (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) (Q : Matrix k p ℝ) :
    |4 * ⟪U t * Q, G t * (V t * Q)⟫| ≤ 2 * g * (‖U t * Q‖ ^ 2 + ‖V t * Q‖ ^ 2) := by
  have h := abs_inner_mul_le_of_mulVec_le hg hG (U t * Q) (V t * Q)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  nlinarith [sq_nonneg (‖U t * Q‖ - ‖V t * Q‖), hg]

/-- **Envelope theorem, upper half**: if `‖G(t)‖_op ≤ g` for all `t`, then
`F_Q(t) ≤ e^{2(g-λ)t} F_Q(0)` for `t ≥ 0` and every test matrix `Q`. -/
theorem gramForm_le_exp (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) (Q : Matrix k p ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖U t * Q‖ ^ 2 + ‖V t * Q‖ ^ 2 ≤
      Real.exp (2 * (g - lam) * t) * (‖U 0 * Q‖ ^ 2 + ‖V 0 * Q‖ ^ 2) :=
  le_exp_mul_of_deriv_le (fun s => hasDerivAt_gramForm (hU s) (hV s) Q) (fun s _ => by
    have := abs_four_mul_inner_le (U := U) (V := V) (t := s) hg (hG s) Q
    linarith [(abs_le.1 this).1]) ht

/-- **Envelope theorem, lower half**: `e^{-2(g+λ)t} F_Q(0) ≤ F_Q(t)` for `t ≥ 0`. -/
theorem exp_le_gramForm (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) (Q : Matrix k p ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-2 * (g + lam) * t) * (‖U 0 * Q‖ ^ 2 + ‖V 0 * Q‖ ^ 2) ≤
      ‖U t * Q‖ ^ 2 + ‖V t * Q‖ ^ 2 :=
  exp_mul_le_of_le_deriv (fun s => hasDerivAt_gramForm (hU s) (hV s) Q) (fun s _ => by
    have := abs_four_mul_inner_le (U := U) (V := V) (t := s) hg (hG s) Q
    linarith [(abs_le.1 this).2]) ht

/-- **Ratios are `λ`-independent**: for two test matrices,
`F_{Q₁}(t) F_{Q₂}(0) ≤ e^{4 g t} F_{Q₁}(0) F_{Q₂}(t)`.  The weight-decay rate `λ` cancels: decay
alone cannot change the effective rank, condition number, or any ratio of singular values. -/
theorem gramForm_ratio_le (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y))
    (Q₁ Q₂ : Matrix k p ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (‖U t * Q₁‖ ^ 2 + ‖V t * Q₁‖ ^ 2) * (‖U 0 * Q₂‖ ^ 2 + ‖V 0 * Q₂‖ ^ 2) ≤
      Real.exp (4 * g * t) * (‖U 0 * Q₁‖ ^ 2 + ‖V 0 * Q₁‖ ^ 2) *
        (‖U t * Q₂‖ ^ 2 + ‖V t * Q₂‖ ^ 2) := by
  have h1 := gramForm_le_exp hU hV hg hG Q₁ ht
  have h2 := exp_le_gramForm hU hV hg hG Q₂ ht
  have e : Real.exp (4 * g * t) =
      Real.exp (2 * (g - lam) * t) * (Real.exp (-2 * (g + lam) * t))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (-2 * (g + lam) * t)
  have hA : 0 ≤ ‖U 0 * Q₂‖ ^ 2 + ‖V 0 * Q₂‖ ^ 2 := by positivity
  have hB : 0 ≤ ‖U 0 * Q₁‖ ^ 2 + ‖V 0 * Q₁‖ ^ 2 := by positivity
  have hC : 0 ≤ ‖U t * Q₂‖ ^ 2 + ‖V t * Q₂‖ ^ 2 := by positivity
  rw [e]
  calc (‖U t * Q₁‖ ^ 2 + ‖V t * Q₁‖ ^ 2) * (‖U 0 * Q₂‖ ^ 2 + ‖V 0 * Q₂‖ ^ 2)
      ≤ (Real.exp (2 * (g - lam) * t) * (‖U 0 * Q₁‖ ^ 2 + ‖V 0 * Q₁‖ ^ 2)) *
          ((Real.exp (-2 * (g + lam) * t))⁻¹ * (‖U t * Q₂‖ ^ 2 + ‖V t * Q₂‖ ^ 2)) := by
        apply mul_le_mul h1 _ hA (by positivity)
        rw [le_inv_mul_iff₀ hpos]
        exact h2
    _ = _ := by ring

/-! ### Loewner form, kernel invariance, collapse, sharpness -/

/-- `‖A col q‖² = ⟨A q, A q⟩`. -/
theorem norm_sq_mul_replicateCol (A : Matrix m k ℝ) (q : k → ℝ) :
    ‖A * Matrix.replicateCol Unit q‖ ^ 2 = (A *ᵥ q) ⬝ᵥ (A *ᵥ q) := by
  rw [← Matrix.replicateCol_mulVec, Frobenius.norm_sq_eq_sum]
  simp [Matrix.replicateCol_apply, dotProduct, sq]

/-- `⟨q, Aᵀ A q⟩ = ⟨A q, A q⟩`. -/
theorem dotProduct_transpose_mul_self_mulVec (A : Matrix m k ℝ) (q : k → ℝ) :
    q ⬝ᵥ ((Aᵀ * A) *ᵥ q) = (A *ᵥ q) ⬝ᵥ (A *ᵥ q) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

omit [Fintype k] in
/-- A real matrix equal to its transpose is Hermitian. -/
theorem isHermitian_of_transpose_eq {A : Matrix k k ℝ} (h : Aᵀ = A) : A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, h]

/-- **Loewner envelope, upper half**: `e^{2(g-λ)t} N(0) - N(t)` is positive semidefinite for
`N = UᵀU + VᵀV` and `t ≥ 0`.  With `LeanDLRA.Classical.CourantFischer`
(`eigenvalues₀_le_of_posSemidef_sub`) every sorted eigenvalue of `N(t)` is at most the
corresponding one of `e^{2(g-λ)t} N(0)`. -/
theorem posSemidef_exp_smul_sub_gram (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (2 * (g - lam) * t) • ((U 0)ᵀ * U 0 + (V 0)ᵀ * V 0) -
      ((U t)ᵀ * U t + (V t)ᵀ * V t)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_transpose_eq ?_) fun q => ?_
  · simp [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul]
  · have h := gramForm_le_exp hU hV hg hG (Matrix.replicateCol Unit q) ht
    simp only [norm_sq_mul_replicateCol] at h
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
      dotProduct_sub, dotProduct_smul, dotProduct_add, dotProduct_transpose_mul_self_mulVec,
      smul_eq_mul]
    linarith

/-- **Loewner envelope, lower half**: `N(t) - e^{-2(g+λ)t} N(0)` is positive semidefinite. -/
theorem posSemidef_gram_sub_exp_smul (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) {t : ℝ} (ht : 0 ≤ t) :
    (((U t)ᵀ * U t + (V t)ᵀ * V t) -
      Real.exp (-2 * (g + lam) * t) • ((U 0)ᵀ * U 0 + (V 0)ᵀ * V 0)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_transpose_eq ?_) fun q => ?_
  · simp [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul]
  · have h := exp_le_gramForm hU hV hg hG (Matrix.replicateCol Unit q) ht
    simp only [norm_sq_mul_replicateCol] at h
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
      dotProduct_sub, dotProduct_smul, dotProduct_add, dotProduct_transpose_mul_self_mulVec,
      smul_eq_mul]
    linarith

/-- **Kernel invariance**: the common kernel of `U(t)` and `V(t)` is the same for all `t ≥ 0`
(for balanced factors this is the kernel of `UᵀU`, so the rank of `W = U Vᵀ` is conserved): a
vanishing singular direction never activates and a nonvanishing one never dies in finite time. -/
theorem kernel_invariant (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) {t : ℝ} (ht : 0 ≤ t)
    (q : k → ℝ) : (U t *ᵥ q = 0 ∧ V t *ᵥ q = 0) ↔ (U 0 *ᵥ q = 0 ∧ V 0 *ᵥ q = 0) := by
  have h1 := gramForm_le_exp hU hV hg hG (Matrix.replicateCol Unit q) ht
  have h2 := exp_le_gramForm hU hV hg hG (Matrix.replicateCol Unit q) ht
  simp only [norm_sq_mul_replicateCol] at h1 h2
  have e1 := Real.exp_pos (2 * (g - lam) * t)
  have e2 := Real.exp_pos (-2 * (g + lam) * t)
  have a1 := dotProduct_self_star_nonneg (U t *ᵥ q)
  have a2 := dotProduct_self_star_nonneg (V t *ᵥ q)
  have a3 := dotProduct_self_star_nonneg (U 0 *ᵥ q)
  have a4 := dotProduct_self_star_nonneg (V 0 *ᵥ q)
  simp only [star_trivial] at a1 a2 a3 a4
  simp only [← dotProduct_self_eq_zero (R := ℝ)]
  constructor
  · rintro ⟨hu, hv⟩
    rw [hu, hv] at h2
    constructor <;> nlinarith
  · rintro ⟨hu, hv⟩
    rw [hu, hv] at h1
    constructor <;> nlinarith

/-- **Collapse below the threshold**: `‖U(t) V(t)ᵀ‖ ≤ e^{2(g-λ)t} (‖U(0)‖² + ‖V(0)‖²) / 2`. -/
theorem norm_product_le_exp (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) {t : ℝ} (ht : 0 ≤ t) :
    ‖U t * (V t)ᵀ‖ ≤ Real.exp (2 * (g - lam) * t) * (‖U 0‖ ^ 2 + ‖V 0‖ ^ 2) / 2 := by
  classical
  have h := gramForm_le_exp hU hV hg hG (1 : Matrix k k ℝ) ht
  simp only [Matrix.mul_one] at h
  have h1 : ‖U t * (V t)ᵀ‖ ≤ ‖U t‖ * ‖V t‖ := by
    rw [← Frobenius.norm_transpose (V t)]; exact Frobenius.norm_mul_le _ _
  nlinarith [sq_nonneg (‖U t‖ - ‖V t‖)]

/-- **Dead-layer attractor**: if `‖∇L‖_op ≤ g < λ` along the trajectory, then `W(t) → 0`.  For
the full-matrix flow `Ẇ = -∇L - λW` the origin is not even a fixed point unless `∇L(0) = 0`. -/
theorem tendsto_product_zero (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (hg : 0 ≤ g)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) (hlt : g < lam) :
    Tendsto (fun t => U t * (V t)ᵀ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _)
    ((eventually_ge_atTop 0).mono fun t ht => norm_product_le_exp hU hV hg hG ht) ?_
  have h1 : Tendsto (fun t : ℝ => Real.exp (2 * (g - lam) * t)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => 2 * (lam - g) * t) atTop atTop :=
      Tendsto.const_mul_atTop (by linarith) tendsto_id
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp this
    refine h.congr fun t => ?_
    simp only [Function.comp]; ring_nf
  simpa using (h1.mul_const ((‖U 0‖ ^ 2 + ‖V 0‖ ^ 2))).div_const 2

/-- **The envelope is attained**: for `U = V = e^{(g-λ)t} U₀` (`1 × k` factors) and the constant
gradient `G = -g`, the L2-decayed flow equations hold, `‖G‖_op = g`, and
`F_Q(t) = e^{2(g-λ)t} F_Q(0)` exactly. -/
theorem scalar_attains_envelope (U₀ : Matrix Unit k ℝ) :
    (∀ t, HasDerivAt (fun t => Real.exp ((g - lam) * t) • U₀)
        (-((-g) • (1 : Matrix Unit Unit ℝ) * (Real.exp ((g - lam) * t) • U₀)) -
          lam • (Real.exp ((g - lam) * t) • U₀)) t) ∧
      (∀ (y : Unit → ℝ), (((-g) • (1 : Matrix Unit Unit ℝ)) *ᵥ y) ⬝ᵥ
          (((-g) • (1 : Matrix Unit Unit ℝ)) *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) ∧
      ∀ (Q : Matrix k p ℝ) t, ‖Real.exp ((g - lam) * t) • U₀ * Q‖ ^ 2 +
          ‖Real.exp ((g - lam) * t) • U₀ * Q‖ ^ 2 =
        Real.exp (2 * (g - lam) * t) * (‖Real.exp ((g - lam) * 0) • U₀ * Q‖ ^ 2 +
          ‖Real.exp ((g - lam) * 0) • U₀ * Q‖ ^ 2) := by
  refine ⟨fun t => ?_, fun y => ?_, fun Q t => ?_⟩
  · have he : HasDerivAt (fun t => Real.exp ((g - lam) * t))
        (Real.exp ((g - lam) * t) * (g - lam)) t := by
      simpa using ((hasDerivAt_id' t).const_mul (g - lam)).exp
    convert he.smul_const U₀ using 1
    simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
    module
  · simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    nlinarith [dotProduct_self_star_nonneg y]
  · simp only [mul_zero, Real.exp_zero, one_smul, Matrix.smul_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    ring_nf

end L2

/-! ### The Frobenius-decay flow -/

section FrobeniusDecay

variable {U : ℝ → Matrix m k ℝ} {V : ℝ → Matrix n k ℝ} {G : ℝ → Matrix m n ℝ} {lam g : ℝ}

/-- **Frobenius decay conserves balancedness exactly** (contrast `balance_eq_exp`): the flow
`U̇ = -(G + λ W) V`, `V̇ = -(G + λ W)ᵀ U` with `W = U Vᵀ` is the decay-free flow for the gradient
curve `G + λ W`, so `UᵀU - VᵀV` is constant. -/
theorem balance_const_frobeniusDecay
    (hU : ∀ t, HasDerivAt U (-((G t + lam • (U t * (V t)ᵀ)) * V t)) t)
    (hV : ∀ t, HasDerivAt V (-((G t + lam • (U t * (V t)ᵀ))ᵀ * U t)) t) (t : ℝ) :
    (U t)ᵀ * U t - (V t)ᵀ * V t = (U 0)ᵀ * U 0 - (V 0)ᵀ * V 0 :=
  FactorizedDynamics.balance_eq_const (G := fun t => G t + lam • (U t * (V t)ᵀ)) hU hV t

/-- Derivative of `‖U Q‖²` along the Frobenius-decay flow for balanced factors
(`UᵀU = VᵀV = M`): `d/dt ‖U Q‖² = -2 ⟪U Q, G V Q⟫ - 2λ ‖M Q‖²`.  The decay term is quadratic in
the Gram matrix, against `-2λ ‖U Q‖²` (linear) under L2 decay. -/
theorem hasDerivAt_rayleigh_frobeniusDecay {t : ℝ}
    (hU : HasDerivAt U (-((G t + lam • (U t * (V t)ᵀ)) * V t)) t)
    (hbal : (U t)ᵀ * U t = (V t)ᵀ * V t) (Q : Matrix k p ℝ) :
    HasDerivAt (fun t => ‖U t * Q‖ ^ 2)
      (-2 * ⟪U t * Q, G t * (V t * Q)⟫ - 2 * lam * ‖(U t)ᵀ * U t * Q‖ ^ 2) t := by
  have h1 := (Frobenius.hasDerivAt_mul_const Q hU).norm_sq
  convert h1 using 1
  simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.smul_mul, inner_add_right, inner_neg_right,
    inner_smul_right, Matrix.mul_assoc]
  have e : ⟪U t * Q, U t * ((V t)ᵀ * (V t * Q))⟫ = ‖(U t)ᵀ * (U t * Q)‖ ^ 2 := by
    rw [Frobenius.inner_mul_left', show (V t)ᵀ * (V t * Q) = (U t)ᵀ * (U t * Q) by
      rw [← Matrix.mul_assoc, ← hbal, Matrix.mul_assoc], real_inner_self_eq_norm_sq]
  rw [e]
  ring

/-- For balanced factors, `‖V Q‖ = ‖U Q‖`. -/
theorem norm_mul_eq_of_balanced {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (hbal : Uᵀ * U = Vᵀ * V) (Q : Matrix k p ℝ) : ‖V * Q‖ = ‖U * Q‖ := by
  have h : ‖V * Q‖ ^ 2 = ‖U * Q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left,
      Frobenius.inner_mul_left, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hbal]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `‖U Q‖² = ⟪Q, UᵀU Q⟫ ≤ ‖Q‖ ‖UᵀU Q‖`. -/
theorem norm_sq_mul_le_norm_mul_norm (U : Matrix m k ℝ) (Q : Matrix k p ℝ) :
    ‖U * Q‖ ^ 2 ≤ ‖Q‖ * ‖Uᵀ * U * Q‖ := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, Matrix.mul_assoc]
  exact real_inner_le_norm _ _

/-- **A priori cap under Frobenius decay**: for balanced factors, `‖∇L‖_op ≤ g`, `λ > 0` and a
unit test matrix (`‖Q‖ = 1`, e.g. a unit column), `‖U(t) Q‖² ≤ max (‖U(0) Q‖²) (g / λ)` for all
`t ≥ 0`.  So every Rayleigh quotient of `UᵀU`, in particular the top singular value of `W`, is
bounded by `g / λ` once it is; under L2 decay the same quantity can grow like `e^{2(g-λ)t}`
(`scalar_attains_envelope`). -/
theorem rayleigh_le_max_frobeniusDecay
    (hU : ∀ t, HasDerivAt U (-((G t + lam • (U t * (V t)ᵀ)) * V t)) t)
    (hV : ∀ t, HasDerivAt V (-((G t + lam • (U t * (V t)ᵀ))ᵀ * U t)) t)
    (hbal : (U 0)ᵀ * U 0 = (V 0)ᵀ * V 0) (hg : 0 ≤ g) (hlam : 0 < lam)
    (hG : ∀ t (y : n → ℝ), (G t *ᵥ y) ⬝ᵥ (G t *ᵥ y) ≤ g ^ 2 * (y ⬝ᵥ y)) {Q : Matrix k p ℝ}
    (hQ : ‖Q‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖U t * Q‖ ^ 2 ≤ max (‖U 0 * Q‖ ^ 2) (g / lam) := by
  have hb : ∀ s, (U s)ᵀ * U s = (V s)ᵀ * V s := fun s => by
    have := balance_const_frobeniusDecay hU hV s
    rw [hbal, sub_self, sub_eq_zero] at this
    exact this
  refine le_max_of_deriv_le_logistic hg hlam
    (fun s => hasDerivAt_rayleigh_frobeniusDecay (hU s) (hb s) Q) (fun s _ => ?_) ht
  have h1 := abs_inner_mul_le_of_mulVec_le hg (hG s) (U s * Q) (V s * Q)
  rw [norm_mul_eq_of_balanced (hb s)] at h1
  have h2 := norm_sq_mul_le_norm_mul_norm (U s) Q
  rw [hQ, one_mul] at h2
  have h3 : (‖U s * Q‖ ^ 2) ^ 2 ≤ ‖(U s)ᵀ * U s * Q‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [(abs_le.1 h1).1, (abs_le.1 h1).2]

end FrobeniusDecay

/-! ### Effective rank under the pure decay terms -/

section PureDecay

variable {U : ℝ → Matrix m k ℝ} {V : ℝ → Matrix n k ℝ} {lam : ℝ}

/-- Under pure L2 decay `U̇ = -λU`, `V̇ = -λV`, `U(t) = e^{-λt} U(0)`. -/
theorem eq_exp_smul_l2Decay (hU : ∀ t, HasDerivAt U (-(lam • U t)) t) (t : ℝ) :
    U t = Real.exp (-lam * t) • U 0 := by
  have he : ∀ s, HasDerivAt (fun s => Real.exp (lam * s) • U s) 0 s := by
    intro s
    have h : HasDerivAt (fun s => Real.exp (lam * s)) (Real.exp (lam * s) * lam) s := by
      simpa using ((hasDerivAt_id' s).const_mul lam).exp
    convert h.smul (hU s) using 1
    simp only [smul_neg, smul_smul]
    module
  have hc := is_const_of_deriv_eq_zero (fun s => (he s).differentiableAt)
    (fun s => (he s).deriv) t 0
  simp only [mul_zero, Real.exp_zero, one_smul] at hc
  rw [← hc, smul_smul, ← Real.exp_add, show -lam * t + lam * t = 0 by ring, Real.exp_zero,
    one_smul]

/-- **Pure L2 decay leaves the effective rank unchanged**: `‖U‖⁴ / ‖UᵀU‖²` (for balanced factors
`‖W‖_*² / ‖W‖_F²`) is constant along `U̇ = -λU`. -/
theorem effectiveRank_const_l2Decay (hU : ∀ t, HasDerivAt U (-(lam • U t)) t) (t : ℝ) :
    (‖U t‖ ^ 2) ^ 2 / ‖(U t)ᵀ * U t‖ ^ 2 = (‖U 0‖ ^ 2) ^ 2 / ‖(U 0)ᵀ * U 0‖ ^ 2 := by
  rw [eq_exp_smul_l2Decay hU t]
  have hpos := Real.exp_pos (-lam * t)
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hpos, abs_of_pos (mul_pos hpos hpos), mul_pow]
  rcases eq_or_ne ‖(U 0)ᵀ * U 0‖ 0 with h | h
  · simp [h]
  · field_simp

variable (hU : ∀ t, HasDerivAt U (-(lam • (U t * ((V t)ᵀ * V t)))) t)
  (hV : ∀ t, HasDerivAt V (-(lam • (V t * ((U t)ᵀ * U t)))) t)
include hU hV

/-- Pure Frobenius decay `U̇ = -λ U VᵀV`, `V̇ = -λ V UᵀU` conserves `UᵀU - VᵀV`. -/
theorem balance_const_pureFrobeniusDecay (t : ℝ) :
    (U t)ᵀ * U t - (V t)ᵀ * V t = (U 0)ᵀ * U 0 - (V 0)ᵀ * V 0 :=
  FactorizedDynamics.balance_eq_const (G := fun t => lam • (U t * (V t)ᵀ))
    (fun t => by simpa [Matrix.smul_mul, Matrix.mul_assoc] using hU t)
    (fun t => by simpa [Matrix.smul_mul, Matrix.mul_assoc, Matrix.transpose_mul] using hV t) t

variable (hbal : (U 0)ᵀ * U 0 = (V 0)ᵀ * V 0)
include hbal

/-- Balance propagates. -/
theorem balanced_pureFrobeniusDecay (t : ℝ) : (U t)ᵀ * U t = (V t)ᵀ * V t := by
  have := balance_const_pureFrobeniusDecay hU hV t
  rwa [hbal, sub_self, sub_eq_zero] at this

/-- `d/dt ‖U‖² = -2λ ‖UᵀU‖²` under pure Frobenius decay (balanced). -/
theorem hasDerivAt_normSq_pureFrobeniusDecay (t : ℝ) :
    HasDerivAt (fun t => ‖U t‖ ^ 2) (-2 * lam * ‖(U t)ᵀ * U t‖ ^ 2) t := by
  have h := (hU t).norm_sq
  convert h using 1
  rw [← balanced_pureFrobeniusDecay hU hV hbal t, inner_neg_right, inner_smul_right,
    Frobenius.inner_mul_left', real_inner_self_eq_norm_sq]
  ring

/-- `Ṁ = -2λ M²` for `M = UᵀU` under pure Frobenius decay (balanced). -/
theorem hasDerivAt_gram_pureFrobeniusDecay (t : ℝ) :
    HasDerivAt (fun t => (U t)ᵀ * U t) ((-2 * lam) • ((U t)ᵀ * U t * ((U t)ᵀ * U t))) t := by
  have h := Frobenius.hasDerivAt_mul (Frobenius.hasDerivAt_transpose (hU t)) (hU t)
  convert h using 1
  rw [← balanced_pureFrobeniusDecay hU hV hbal t]
  simp only [Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module

/-- `d/dt ‖UᵀU‖² = -4λ ‖U UᵀU‖²` under pure Frobenius decay (balanced). -/
theorem hasDerivAt_gramNormSq_pureFrobeniusDecay (t : ℝ) :
    HasDerivAt (fun t => ‖(U t)ᵀ * U t‖ ^ 2)
      (-4 * lam * ‖U t * ((U t)ᵀ * U t)‖ ^ 2) t := by
  have h := (hasDerivAt_gram_pureFrobeniusDecay hU hV hbal t).norm_sq
  convert h using 1
  rw [inner_smul_right, ← real_inner_self_eq_norm_sq (U t * ((U t)ᵀ * U t)),
    Frobenius.inner_mul_left, ← Matrix.mul_assoc]
  ring

omit hU hV hbal in
/-- Cauchy–Schwarz: `‖UᵀU‖⁴ ≤ ‖U‖² ‖U UᵀU‖²`. -/
theorem gramNormSq_sq_le (U : Matrix m k ℝ) :
    (‖Uᵀ * U‖ ^ 2) ^ 2 ≤ ‖U‖ ^ 2 * ‖U * (Uᵀ * U)‖ ^ 2 := by
  have h : ‖Uᵀ * U‖ ^ 2 ≤ ‖U‖ * ‖U * (Uᵀ * U)‖ := by
    rw [← real_inner_self_eq_norm_sq, ← Frobenius.inner_mul_left']
    exact real_inner_le_norm _ _
  have := pow_le_pow_left₀ (by positivity) h 2
  linarith [mul_pow ‖U‖ ‖U * (Uᵀ * U)‖ 2]

omit hU hV hbal in
/-- `‖UᵀU‖² ≤ (‖U‖²)²`. -/
theorem gramNormSq_le_sq (U : Matrix m k ℝ) : ‖Uᵀ * U‖ ^ 2 ≤ (‖U‖ ^ 2) ^ 2 := by
  have h : ‖Uᵀ * U‖ ≤ ‖U‖ * ‖U‖ := by
    rw [← Frobenius.norm_transpose U]
    nth_rw 2 [Frobenius.norm_transpose U]
    exact Frobenius.norm_mul_le _ _
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith [mul_pow ‖U‖ ‖U‖ 2]

/-- `‖U(t)‖² ≤ ‖U(0)‖²` for `t ≥ 0` (`λ ≥ 0`). -/
theorem normSq_le_pureFrobeniusDecay (hlam : 0 ≤ lam) {t : ℝ} (ht : 0 ≤ t) :
    ‖U t‖ ^ 2 ≤ ‖U 0‖ ^ 2 := by
  have := le_exp_mul_of_deriv_le (c := 0)
    (fun s => hasDerivAt_normSq_pureFrobeniusDecay hU hV hbal s)
    (fun s _ => by nlinarith [sq_nonneg ‖(U s)ᵀ * U s‖]) ht
  simpa using this

/-- `‖U(t)‖² ≥ e^{-2λ ‖U(0)‖² t} ‖U(0)‖²` for `t ≥ 0`: the factor never dies in finite time. -/
theorem exp_mul_le_normSq_pureFrobeniusDecay (hlam : 0 ≤ lam) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-2 * lam * ‖U 0‖ ^ 2 * t) * ‖U 0‖ ^ 2 ≤ ‖U t‖ ^ 2 :=
  exp_mul_le_of_le_deriv (fun s => hasDerivAt_normSq_pureFrobeniusDecay hU hV hbal s)
    (fun s hs => by
      have h1 := gramNormSq_le_sq (U s)
      have h2 := normSq_le_pureFrobeniusDecay hU hV hbal hlam hs
      have h3 : 0 ≤ ‖U s‖ ^ 2 := by positivity
      nlinarith [mul_nonneg hlam h3]) ht

omit hU hV hbal in
/-- `U ≠ 0 → UᵀU ≠ 0` (Frobenius: `‖U‖² = tr (UᵀU)`). -/
theorem gramNormSq_pos_of_normSq_pos {U : Matrix m k ℝ} (h : 0 < ‖U‖ ^ 2) :
    0 < ‖Uᵀ * U‖ ^ 2 := by
  rcases (sq_nonneg ‖Uᵀ * U‖).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have hM : Uᵀ * U = 0 := by
      have := h'.symm
      rwa [sq_eq_zero_iff, norm_eq_zero] at this
    have : ‖U‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hM, Matrix.trace_zero]
    linarith

/-- **Pure Frobenius decay raises the effective rank**: for balanced factors with `U(0) ≠ 0` and
`λ ≥ 0`, `ρ(t) = ‖U(t)‖⁴ / ‖U(t)ᵀU(t)‖²` (`= ‖W‖_*² / ‖W‖_F²` for balanced factors, `= (Σσᵢ)² /
Σσᵢ²`) is nondecreasing on `[0, ∞)`.  Proof: `ρ' = 4λ a (a c - b²) / b²` with `a = ‖U‖²`,
`b = ‖UᵀU‖²`, `c = ‖U UᵀU‖²` and `b² ≤ a c` by Cauchy–Schwarz.  Under pure L2 decay `ρ` is
constant (`effectiveRank_const_l2Decay`): the decay term of Frobenius decay, `-2λσᵢ²`, is
disproportionately strong on large singular values, that of L2 decay, `-2λσᵢ`, is scale-free. -/
theorem effectiveRank_monotone_frobeniusDecay (hlam : 0 ≤ lam) (h0 : 0 < ‖U 0‖ ^ 2) :
    MonotoneOn (fun t => (‖U t‖ ^ 2) ^ 2 / ‖(U t)ᵀ * U t‖ ^ 2) (Ici 0) := by
  have ha : ∀ s, 0 ≤ s → 0 < ‖U s‖ ^ 2 := fun s hs =>
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) h0)
      (exp_mul_le_normSq_pureFrobeniusDecay hU hV hbal hlam hs)
  have hb : ∀ s, 0 ≤ s → 0 < ‖(U s)ᵀ * U s‖ ^ 2 := fun s hs =>
    gramNormSq_pos_of_normSq_pos (ha s hs)
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun t => (‖U t‖ ^ 2) ^ 2 / ‖(U t)ᵀ * U t‖ ^ 2)
      ((((-2 * lam * ‖(U s)ᵀ * U s‖ ^ 2) * ‖U s‖ ^ 2 + ‖U s‖ ^ 2 *
          (-2 * lam * ‖(U s)ᵀ * U s‖ ^ 2)) * ‖(U s)ᵀ * U s‖ ^ 2 -
        ‖U s‖ ^ 2 * ‖U s‖ ^ 2 * (-4 * lam * ‖U s * ((U s)ᵀ * U s)‖ ^ 2)) /
          (‖(U s)ᵀ * U s‖ ^ 2) ^ 2) s := fun s hs => by
    have h1 := hasDerivAt_normSq_pureFrobeniusDecay hU hV hbal s
    have h2 := hasDerivAt_gramNormSq_pureFrobeniusDecay hU hV hbal s
    have h3 := (h1.mul h1).div h2 (hb s hs).ne'
    convert h3 using 1
    funext t
    simp only [Pi.div_apply, Pi.mul_apply]
    ring
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => ?_)
  rw [interior_Ici] at hs
  rw [(hd s hs.le).deriv]
  apply div_nonneg _ (by positivity)
  have hcs := gramNormSq_sq_le (U s)
  have := ha s hs.le
  have e : ((-2 * lam * ‖(U s)ᵀ * U s‖ ^ 2) * ‖U s‖ ^ 2 + ‖U s‖ ^ 2 *
          (-2 * lam * ‖(U s)ᵀ * U s‖ ^ 2)) * ‖(U s)ᵀ * U s‖ ^ 2 -
        ‖U s‖ ^ 2 * ‖U s‖ ^ 2 * (-4 * lam * ‖U s * ((U s)ᵀ * U s)‖ ^ 2) =
      4 * lam * ‖U s‖ ^ 2 * (‖U s‖ ^ 2 * ‖U s * ((U s)ᵀ * U s)‖ ^ 2 -
        (‖(U s)ᵀ * U s‖ ^ 2) ^ 2) := by ring
  rw [e]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlam) this.le) (sub_nonneg.2 hcs)

end PureDecay

end LeanDLRA.Novel.OpTR43
