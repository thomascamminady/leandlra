import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.SVD
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.InexactSubsteps
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Projectors

/-!
# Tight bound of rank thresholding and its consequences

Consequences of the golden-ratio quasi-optimality of low-rank projection
(`LeanDLRA.norm_sub_le_goldenRatio_mul`). With `φ = (1 + √5)/2`, the module proves the following.

* **The abstract argument** (`norm_sub_le_add_gold_mul`).  For any model set `𝓢` in a real inner
  product space, a best approximation `T` of `X`, an orthogonal projector `Q` with `Q T = T`,
  `Q X ∈ 𝓢`, and `B` stable under `Q + t⁻¹ (1 - Q)`, `t ≥ 1`: `‖T - A‖ ≤ ‖A - B‖ + φ ‖X - A‖` for
  **every** `A`.  The library theorem is the case `A = B`, of which this is an independent proof.
* **Truncation for an arbitrary target** (`norm_sub_le_distLR_add_gold`):
  `‖T - A‖ ≤ dist(A, M_{≤ r}) + φ ‖X - A‖`, improving the `2` of `LeanDLRA.norm_bestTrunc_sub_le`
  for all `A`, with both coefficients optimal (`one_le_and_goldenRatio_le`), and the one-parameter
  family it comes from (`sq_norm_sub_le_family_of_rank`).
* **DLRA** (`norm_trunc_flow_le_gold`, `fixedRank_trunc_local_error_le_gold`,
  `fixedRank_global_error_le_gold`): the fixed-rank truncated augmented BUG integrator, local and
  global error, with `φ` in place of `1 + κ = 2`.
* **SVP / matrix IHT** (`norm_svpStep_sub_le`, `norm_svpStep_sub_le_of_rip`,
  `norm_svp_iterate_sub_le`, `tendsto_svp`): the one-step bound `φ (ρ(λ) ‖E‖ + λ √L ‖e‖)`, RIP order
  `3 r`, general step size, measurement noise, every tie-breaking.
* **Sharpness** (`exists_svpStep_eq`, `exists_stall`, `exists_stall_of_rip`,
  `exists_stall_of_condition`): `φ δ` is attained for every `δ ∈ (0, 1)`, and from `δ = 1/φ` on SVP
  has fixed points that are not solutions, so `δ_{3r} < 1/φ` cannot be relaxed.
* **The step-size window** (`gold_rate_lt_one_iff`, `window_nonempty_iff`, `rate_eq_of_le`,
  `two_mul_loss_le_norm_proj_grad`).  The "iff" of Corollary G is **false** as stated
  (`phi_window_not_iff`); the true statement is that the window is two-sided,
  `(1 - 1/φ)/μ < λ < φ/L`, for the *bound*, and that its lower end is necessary in the worst case
  over `L` (`exists_stall`).
* **Block sparsity** (`norm_sub_le_add_gold_mul_blockSparse`, `norm_sub_le_gold_mul_blockSparse`,
  `norm_blockIHT_sub_le`, `norm_sub_le_add_gold_mul_rowSparse`): `k`-sparse vectors (the Shen–Li
  bound with `ρ = 1`), block-sparse vectors, row-sparse matrices, with the sharpness examples
  `exists_eq_gold_sparse`, `exists_eq_gold_rowSparse`.

The Galerkin space is taken one-sided here (`P` acts on columns only): it has
dimension `≤ 3 r` once it also contains the current iterate, which is what brings the RIP order from
`4 r` down to `3 r`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.GoldenThresholding

local notation "φ" => Real.goldenRatio

/-! ### Golden-ratio arithmetic -/

section Arithmetic

lemma gold_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq

lemma gold_gt : 1 < φ := Real.one_lt_goldenRatio

lemma gold_lt : φ < 2 := Real.goldenRatio_lt_two

lemma gold_inv : φ⁻¹ = φ - 1 :=
  inv_eq_of_mul_eq_one_right (by nlinarith [gold_sq])

/-- The homogeneous quadratic core of the golden-ratio argument.  `D2 = ‖T - A‖²`, `e2 = ‖X - A‖²`,
`g = ‖X - T‖`, `c = ⟪T - A, X - T⟫`, `R = ‖q (T - A) + p (X - T)‖`, `d = ‖A - B‖`. -/
private lemma golden_aux {p q D2 e2 g d R c : ℝ} (hq : 0 < q) (hpq : q < p)
    (hN : 0 < q ^ 2 + p * q - p ^ 2) (hg : 0 ≤ g)
    (he : e2 = D2 + 2 * c + g ^ 2) (hR : R ^ 2 = q ^ 2 * D2 + 2 * p * q * c + p ^ 2 * g ^ 2)
    (hgR : q * g ≤ R + q * d) :
    (p - q) * (q ^ 2 + p * q - p ^ 2) * D2 ≤
      p * (q ^ 2 + p * q - p ^ 2) * e2 + p * (p - q) * q * d ^ 2 := by
  set N := q ^ 2 + p * q - p ^ 2 with hNdef
  have hp : 0 < p := hq.trans hpq
  have hw : 0 < p * (p - q) := mul_pos hp (sub_pos.2 hpq)
  have hRexp : R ^ 2 = (q ^ 2 - p * q) * D2 + p * q * e2 + (p ^ 2 - p * q) * g ^ 2 := by
    rw [hR, he]; ring
  have key : q * ((p - q) * N * D2) ≤ q * (p * N * e2 + p * (p - q) * q * d ^ 2) := by
    rcases le_or_gt g d with hgd | hgd
    · have h1 : 0 ≤ N * R ^ 2 := mul_nonneg hN.le (sq_nonneg R)
      rw [hRexp] at h1
      have h2 : g ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hg hgd 2
      have h3 : N * g ^ 2 ≤ q ^ 2 * d ^ 2 := by
        have h4 : N ≤ q ^ 2 := by rw [hNdef]; nlinarith
        calc N * g ^ 2 ≤ q ^ 2 * g ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg g)
          _ ≤ q ^ 2 * d ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg q)
      have h5 := mul_le_mul_of_nonneg_left h3 hw.le
      nlinarith
    · have h1 : (q * (g - d)) ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hq.le (by linarith)) (by linarith) 2
      have h2 := mul_le_mul_of_nonneg_left h1 hN.le
      rw [hRexp] at h2
      have h3 : N = q ^ 2 - p * (p - q) := by rw [hNdef]; ring
      have h4 := sq_nonneg (q ^ 2 * d - N * g)
      have h5 : N * (p * (p - q) * g ^ 2 - (q * (g - d)) ^ 2) ≤ p * (p - q) * q ^ 2 * d ^ 2 := by
        rw [h3] at h4 ⊢
        nlinarith
      nlinarith
  exact le_of_mul_le_mul_left key hq

end Arithmetic

/-! ### The abstract argument -/

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `shrink Q t = Q + t⁻¹ (1 - Q)`: keep the range of `Q`, shrink its complement by `t`.  For
`t = φ` this is the contraction `M` of Theorem E. -/
noncomputable def shrink (Q : V →L[ℝ] V) (t : ℝ) (Z : V) : V := Q Z + t⁻¹ • (Z - Q Z)

lemma norm_shrink_le {Q : V →L[ℝ] V} (hQ : IsOrthProj Q) {t : ℝ} (ht : 1 ≤ t) (Z : V) :
    ‖shrink Q t Z‖ ≤ ‖Z‖ := by
  have h0 : ⟪Q Z, Z - Q Z⟫ = 0 := hQ.inner_sub_self Z Z
  have hsplit := hQ.norm_sq_add Z
  have h1 : ‖shrink Q t Z‖ ^ 2 = ‖Q Z‖ ^ 2 + (t⁻¹) ^ 2 * ‖Z - Q Z‖ ^ 2 := by
    rw [shrink, norm_add_sq_real, inner_smul_right, h0, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have h2 : (t⁻¹) ^ 2 ≤ 1 := by
    have : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
    have h3 : 0 ≤ t⁻¹ := by positivity
    nlinarith
  have h3 : ‖shrink Q t Z‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
    nlinarith [sq_nonneg ‖Z - Q Z‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

variable {𝓢 : Set V} {Q : V →L[ℝ] V} {X T A B : V}

/-- First-order condition: a best approximation `T` in `𝓢` with `Q T = T` and `Q X ∈ 𝓢` is `Q X`. -/
lemma apply_eq_of_best (hQ : IsOrthProj Q) (hT : ∀ Z ∈ 𝓢, ‖X - T‖ ≤ ‖X - Z‖) (hQT : Q T = T)
    (hQX : Q X ∈ 𝓢) : Q X = T := by
  have h1 := hQ.norm_sq_add (X - T)
  have e1 : Q (X - T) = Q X - T := by rw [map_sub, hQT]
  have e2 : (X - T) - (Q X - T) = X - Q X := by abel
  rw [e1, e2] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hT _ hQX) 2
  have h3 : ‖Q X - T‖ = 0 := by nlinarith [norm_nonneg (Q X - T)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- The variational inequality behind everything: `‖X - T‖ ≤ ‖T - A + t (X - T)‖ + ‖A - B‖`. -/
lemma norm_sub_le_of_shrink (hQ : IsOrthProj Q) (hT : ∀ Z ∈ 𝓢, ‖X - T‖ ≤ ‖X - Z‖) (hQT : Q T = T)
    (hQX : Q X ∈ 𝓢) (hB : ∀ t : ℝ, 1 ≤ t → shrink Q t B ∈ 𝓢) {t : ℝ} (ht : 1 ≤ t) (A : V) :
    ‖X - T‖ ≤ ‖T - A + t • (X - T)‖ + ‖A - B‖ := by
  have hE : Q (X - T) = 0 := by rw [map_sub, apply_eq_of_best hQ hT hQT hQX, hQT, sub_self]
  have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
  have e : X - shrink Q t B = shrink Q t (T + t • (X - T) - B) := by
    simp only [shrink, map_sub, map_add, map_smul, hE, hQT, smul_zero, add_zero]
    have : t⁻¹ • (T + t • (X - T) - B - (T - Q B)) = (X - T) - t⁻¹ • (B - Q B) := by
      rw [show T + t • (X - T) - B - (T - Q B) = t • (X - T) - (B - Q B) by abel, smul_sub,
        smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [this]
    abel
  calc ‖X - T‖ ≤ ‖X - shrink Q t B‖ := hT _ (hB t ht)
    _ = ‖shrink Q t (T + t • (X - T) - B)‖ := by rw [e]
    _ ≤ ‖T + t • (X - T) - B‖ := norm_shrink_le hQ ht _
    _ = ‖(T - A + t • (X - T)) + (A - B)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

/-- Abstract form of the family of `sq_norm_sub_le_family_of_rank`. -/
theorem sq_norm_sub_le_family (hQ : IsOrthProj Q) (hT : ∀ Z ∈ 𝓢, ‖X - T‖ ≤ ‖X - Z‖) (hQT : Q T = T)
    (hQX : Q X ∈ 𝓢) (hB : ∀ t : ℝ, 1 ≤ t → shrink Q t B ∈ 𝓢) {t : ℝ} (ht : 1 < t)
    (hs : 0 < 1 + t - t ^ 2) (A : V) :
    ‖T - A‖ ^ 2 ≤ t / (t - 1) * ‖X - A‖ ^ 2 + t / (1 + t - t ^ 2) * ‖A - B‖ ^ 2 := by
  set E := X - T with hE
  have he : ‖X - A‖ ^ 2 = ‖T - A‖ ^ 2 + 2 * ⟪T - A, E⟫ + ‖E‖ ^ 2 := by
    rw [show X - A = (T - A) + E by rw [hE]; abel, norm_add_sq_real]
  have hR : ‖T - A + t • E‖ ^ 2 =
      1 ^ 2 * ‖T - A‖ ^ 2 + 2 * t * 1 * ⟪T - A, E⟫ + t ^ 2 * ‖E‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hk := golden_aux (p := t) (q := 1) (d := ‖A - B‖) one_pos ht
    (by linarith) (norm_nonneg _) he hR
    (by simpa using norm_sub_le_of_shrink hQ hT hQT hQX hB ht.le A)
  have ht1 : 0 < t - 1 := by linarith
  have hs' : 0 < 1 ^ 2 + t * 1 - t ^ 2 := by linarith
  have h1 : t / (t - 1) * ‖X - A‖ ^ 2 + t / (1 + t - t ^ 2) * ‖A - B‖ ^ 2 =
      (t * (1 ^ 2 + t * 1 - t ^ 2) * ‖X - A‖ ^ 2 + t * (t - 1) * 1 * ‖A - B‖ ^ 2) /
        ((t - 1) * (1 ^ 2 + t * 1 - t ^ 2)) := by
    have : (1 : ℝ) ^ 2 + t * 1 - t ^ 2 = 1 + t - t ^ 2 := by ring
    rw [this]
    field_simp
  rw [h1, le_div_iff₀ (mul_pos ht1 hs')]
  linarith

/-- **Abstract golden inequality with a defect.**  Let `T` be a best approximation of `X` in `𝓢`,
`Q` an orthogonal projector with `Q T = T`, `Q X ∈ 𝓢`, and let the point `B` stay in `𝓢` under
all `Q + t⁻¹ (1 - Q)`, `t ≥ 1`.  Then for **every** `A`, `‖T - A‖ ≤ ‖A - B‖ + φ ‖X - A‖`.

This is what makes every quasi-projection argument work with `φ` instead of `2`.  For `A = B` it is
`LeanDLRA.norm_sub_le_goldenRatio_mul` and, for sparse vectors, the bound of Shen–Li (JMLR 2018)
with `ρ = 1`; the proof takes `t = (‖A - B‖ + φ ‖X - A‖) / (‖A - B‖ + ‖X - A‖)` in the argument of
Theorem E (which is `t = φ`).  Tucker and tensor-train sets are not covered: in general
`Q X ∈ 𝓢` fails for a single-mode projector, and `Q + t⁻¹ (1 - Q)` does not preserve them for the
all-mode one.  That is a limit of this proof; no counterexample to `φ` for those sets is given. -/
theorem norm_sub_le_add_gold_mul (hQ : IsOrthProj Q) (hT : ∀ Z ∈ 𝓢, ‖X - T‖ ≤ ‖X - Z‖)
    (hQT : Q T = T) (hQX : Q X ∈ 𝓢) (hB : ∀ t : ℝ, 1 ≤ t → shrink Q t B ∈ 𝓢) (A : V) :
    ‖T - A‖ ≤ ‖A - B‖ + φ * ‖X - A‖ := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ1 := gold_gt
  have hφ2 := gold_lt
  have hφ3 := gold_sq
  set E := X - T with hE
  set d := ‖A - B‖ with hd
  set e := ‖X - A‖ with hee
  have hd0 : 0 ≤ d := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  have he : e ^ 2 = ‖T - A‖ ^ 2 + 2 * ⟪T - A, E⟫ + ‖E‖ ^ 2 := by
    rw [hee, show X - A = (T - A) + E by rw [hE]; abel, norm_add_sq_real]
  rcases he0.eq_or_lt with he1 | he1
  · -- `X = A`: the best-approximation property alone
    have hXA : X = A := by
      have : ‖X - A‖ = 0 := by rw [← hee, ← he1]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    have h1 := hT B (by simpa [shrink] using hB 1 le_rfl)
    rw [← he1, mul_zero, add_zero, hd, ← hXA, norm_sub_rev T]
    exact h1
  rcases hd0.eq_or_lt with hd1 | hd1
  · -- `d = 0`: the case `t = φ`, Theorem E
    have h1 := norm_sub_le_of_shrink hQ hT hQT hQX hB hφ1.le A
    rw [← hd, ← hd1, add_zero] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hR : ‖T - A + φ • E‖ ^ 2 = ‖T - A‖ ^ 2 + 2 * φ * ⟪T - A, E⟫ + φ ^ 2 * ‖E‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [hR] at h2
    rw [← hd1, zero_add]
    have h3 : ‖T - A‖ ^ 2 ≤ (φ * e) ^ 2 := by
      have h4 : (φ - 1) * ‖T - A‖ ^ 2 ≤ φ * e ^ 2 := by nlinarith
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  -- general case: `t = (d + φ e) / (d + e)`
  set q := d + e with hq
  set p := d + φ * e with hp
  have hq0 : 0 < q := by positivity
  have hpq : q < p := by rw [hq, hp]; nlinarith
  have hN : q ^ 2 + p * q - p ^ 2 = d * (d + (3 - φ) * e) := by
    rw [hq, hp]; linear_combination (-e ^ 2) * hφ3
  have hN0 : 0 < q ^ 2 + p * q - p ^ 2 := by
    rw [hN]; exact mul_pos hd1 (by nlinarith)
  set t := p / q with ht
  have ht1 : 1 ≤ t := by rw [ht, one_le_div hq0]; exact hpq.le
  have h1 := norm_sub_le_of_shrink hQ hT hQT hQX hB ht1 A
  rw [← hd] at h1
  have hscale : ‖(q : ℝ) • (T - A) + p • E‖ = q * ‖T - A + t • E‖ := by
    rw [← Real.norm_of_nonneg hq0.le, ← norm_smul, smul_add, smul_smul, ht,
      mul_div_cancel₀ _ hq0.ne', Real.norm_of_nonneg hq0.le]
  have hR : ‖(q : ℝ) • (T - A) + p • E‖ ^ 2 =
      q ^ 2 * ‖T - A‖ ^ 2 + 2 * p * q * ⟪T - A, E⟫ + p ^ 2 * ‖E‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_left, inner_smul_right, norm_smul, norm_smul, mul_pow, mul_pow,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    simp only [conj_trivial]
    ring
  have hgR : q * ‖E‖ ≤ ‖(q : ℝ) • (T - A) + p • E‖ + q * d := by
    rw [hscale]; nlinarith
  have hk := golden_aux hq0 hpq hN0 (norm_nonneg _) he hR hgR
  have hpe : p - q = (φ - 1) * e := by rw [hq, hp]; ring
  have hmain : ‖T - A‖ ^ 2 ≤ p ^ 2 := by
    have hpos : 0 < (p - q) * (q ^ 2 + p * q - p ^ 2) := mul_pos (sub_pos.2 hpq) hN0
    refine le_of_mul_le_mul_left (hk.trans ?_) hpos
    rw [hN, hpe]
    have hp0 : 0 < p := hq0.trans hpq
    have : 0 ≤ p * d * e * ((φ - 1) * (2 - φ) * d * e) := by
      have : 0 ≤ (φ - 1) * (2 - φ) := mul_nonneg (by linarith) (by linarith)
      positivity
    have h1 : (φ - 1) * p - e = (φ - 1) * d := by rw [hp]; linear_combination e * hφ3
    have e1 : (φ - 1) * e * (d * (d + (3 - φ) * e)) * p ^ 2 - (p * (d * (d + (3 - φ) * e)) * e ^ 2 +
        p * ((φ - 1) * e) * q * d ^ 2) = p * d * e * ((φ - 1) * (2 - φ) * d * e) := by
      linear_combination (p * d * (d + (3 - φ) * e) * e) * h1 - (p * (φ - 1) * e * d ^ 2) * hq
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hq0.trans hpq).le two_ne_zero).mp hmain


/-- **Pythagoras across a projector.**  If `T` is a best approximation of `X` in `𝓢`, `P` an
orthogonal projector fixing `T` and mapping `𝓢` into itself, then `T` is also a best approximation
of `P X`. -/
lemma best_of_proj {P : V →L[ℝ] V} (hP : IsOrthProj P) (hPT : P T = T)
    (hS : ∀ Z ∈ 𝓢, P Z ∈ 𝓢) (hT : ∀ Z ∈ 𝓢, ‖X - T‖ ≤ ‖X - Z‖) :
    ∀ Z ∈ 𝓢, ‖P X - T‖ ≤ ‖P X - Z‖ := by
  intro Z hZ
  have split : ∀ W : V, P W = W → ‖X - W‖ ^ 2 = ‖P X - W‖ ^ 2 + ‖X - P X‖ ^ 2 := by
    intro W hW
    have h1 := hP.norm_sq_add (X - W)
    have e1 : P (X - W) = P X - W := by rw [map_sub, hW]
    have e2 : (X - W) - (P X - W) = X - P X := by abel
    rw [e1, e2] at h1
    exact h1.symm
  have h1 := split T hPT
  have h2 := split (P Z) (hP.idem Z)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) (hT _ (hS Z hZ)) 2
  have h4 : ‖P X - T‖ ≤ ‖P X - P Z‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    linarith
  refine h4.trans ?_
  have h5 : P X - P Z = P (P X - Z) := by rw [map_sub, hP.idem]
  rw [h5]
  exact hP.norm_le _

/-- **Projected golden inequality.**  If in addition `P` fixes `A ∈ 𝓢`, then the error of `T` is
controlled by the part of `X - A` that `P` sees: `‖T - A‖ ≤ φ ‖P (X - A)‖`.  This is the step that
lets a restricted isometry act on `X - A`, which need not be low rank: it combines Theorem E with
the identity `T_r(Y) = T_r(P_S Y)` of Corollary F. -/
theorem norm_sub_le_gold_mul_proj {P : V →L[ℝ] V} (hP : IsOrthProj P) (hPT : P T = T)
    (hPA : P A = A) (hS : ∀ Z ∈ 𝓢, P Z ∈ 𝓢) (hT : ∀ Z ∈ 𝓢, ‖X - T‖ ≤ ‖X - Z‖) (hQ : IsOrthProj Q)
    (hQT : Q T = T) (hQX : Q (P X) ∈ 𝓢) (hA : ∀ t : ℝ, 1 ≤ t → shrink Q t A ∈ 𝓢) :
    ‖T - A‖ ≤ φ * ‖P (X - A)‖ := by
  have h := norm_sub_le_add_gold_mul hQ (best_of_proj hP hPT hS hT) hQT hQX hA A
  rwa [sub_self, norm_zero, zero_add, ← hPA, ← map_sub, hPA] at h

end Abstract

/-! ### A symmetric operator with restricted spectrum, on the range of a projector -/

section Spectrum

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F]
  {𝒜 : V →ₗ[ℝ] F} {P : V →L[ℝ] V} {μ L lam : ℝ}

/-- The contraction factor `ρ(λ) = max(|1 - λ μ|, |1 - λ L|)` of a gradient step for a quadratic
with spectrum in `[μ, L]`. -/
noncomputable def rate (μ L lam : ℝ) : ℝ := max |1 - lam * μ| |1 - lam * L|

lemma rate_nonneg (μ L lam : ℝ) : 0 ≤ rate μ L lam := le_max_of_le_left (abs_nonneg _)

/-- Restricted spectrum implies that `I - λ 𝒜*𝒜` has norm `≤ ρ(λ)` on the range of `P`: for
`P E = E`, `‖P (E - λ 𝒜*𝒜 E)‖ ≤ ρ(λ) ‖E‖`.  This is the polarisation lemma of RIP theory. -/
theorem norm_proj_gradStep_le (hP : IsOrthProj P)
    (hspec : ∀ Z, P Z = Z → μ * ‖Z‖ ^ 2 ≤ ‖𝒜 Z‖ ^ 2 ∧ ‖𝒜 Z‖ ^ 2 ≤ L * ‖Z‖ ^ 2) (hlam : 0 ≤ lam)
    {E : V} (hE : P E = E) :
    ‖P (E - lam • LinearMap.adjoint 𝒜 (𝒜 E))‖ ≤ rate μ L lam * ‖E‖ := by
  set ρ := rate μ L lam with hρ
  have hρ0 : 0 ≤ ρ := rate_nonneg _ _ _
  set w := E - lam • LinearMap.adjoint 𝒜 (𝒜 E) with hw
  set Z := P w with hZdef
  have hZ : P Z = Z := hP.idem w
  set b : V → V → ℝ := fun U W => ⟪U, W⟫ - lam * ⟪𝒜 U, 𝒜 W⟫ with hb
  have hZb : ‖Z‖ ^ 2 = b Z E := by
    have h1 : ⟪Z, Z⟫ = ⟪Z, w⟫ := by
      conv_lhs => rw [hZdef]
      rw [← hZdef, show ⟪P w, Z⟫ = ⟪w, P Z⟫ from hP.symm w Z, hZ, real_inner_comm]
    rw [← real_inner_self_eq_norm_sq, h1, hw, inner_sub_right, inner_smul_right,
      LinearMap.adjoint_inner_right]
  have hray : ∀ U, P U = U → |b U U| ≤ ρ * ‖U‖ ^ 2 := by
    intro U hU
    obtain ⟨h1, h2⟩ := hspec U hU
    have e : b U U = ‖U‖ ^ 2 - lam * ‖𝒜 U‖ ^ 2 := by
      simp only [hb, real_inner_self_eq_norm_sq]
    have h3 := mul_le_mul_of_nonneg_left h1 hlam
    have h4 := mul_le_mul_of_nonneg_left h2 hlam
    have h5 : 1 - lam * μ ≤ ρ := (le_abs_self _).trans (le_max_left _ _)
    have h6 : -(1 - lam * L) ≤ ρ := (neg_le_abs _).trans (le_max_right _ _)
    have hU0 := sq_nonneg ‖U‖
    rw [e, abs_le]
    constructor
    · nlinarith
    · nlinarith
  have hadd : P (‖E‖ • Z + ‖Z‖ • E) = ‖E‖ • Z + ‖Z‖ • E := by
    rw [map_add, map_smul, map_smul, hZ, hE]
  have hsub : P (‖E‖ • Z - ‖Z‖ • E) = ‖E‖ • Z - ‖Z‖ • E := by
    rw [map_sub, map_smul, map_smul, hZ, hE]
  have hpol : 4 * ‖E‖ * ‖Z‖ * b Z E ≤ 4 * ρ * ‖E‖ ^ 2 * ‖Z‖ ^ 2 := by
    have h1 := (le_abs_self _).trans (hray _ hadd)
    have h2 := (neg_le_abs _).trans (hray _ hsub)
    have e1 : b (‖E‖ • Z + ‖Z‖ • E) (‖E‖ • Z + ‖Z‖ • E) =
        ‖E‖ ^ 2 * b Z Z + 2 * ‖E‖ * ‖Z‖ * b Z E + ‖Z‖ ^ 2 * b E E := by
      simp only [hb, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, conj_trivial, real_inner_comm (𝒜 Z) (𝒜 E), real_inner_comm Z E]
      ring
    have e2 : b (‖E‖ • Z - ‖Z‖ • E) (‖E‖ • Z - ‖Z‖ • E) =
        ‖E‖ ^ 2 * b Z Z - 2 * ‖E‖ * ‖Z‖ * b Z E + ‖Z‖ ^ 2 * b E E := by
      simp only [hb, map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
        inner_smul_right, conj_trivial, real_inner_comm (𝒜 Z) (𝒜 E), real_inner_comm Z E]
      ring
    have e3 : ‖‖E‖ • Z + ‖Z‖ • E‖ ^ 2 + ‖‖E‖ • Z - ‖Z‖ • E‖ ^ 2 =
        4 * ‖E‖ ^ 2 * ‖Z‖ ^ 2 := by
      have := parallelogram_law_with_norm ℝ (‖E‖ • Z) (‖Z‖ • E)
      simp only [norm_smul, norm_norm] at this
      nlinarith
    rw [e1] at h1
    rw [e2] at h2
    nlinarith
  rcases (norm_nonneg Z).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  rcases (norm_nonneg E).eq_or_lt with h1 | h1
  · have hE0 : E = 0 := norm_eq_zero.mp h1.symm
    have : Z = 0 := by simp [hZdef, hw, hE0]
    simp [this] at h0
  rw [← hZb] at hpol
  have h2 : 0 < ‖E‖ * ‖Z‖ * ‖Z‖ := by positivity
  have h3 : (‖E‖ * ‖Z‖ * ‖Z‖) * ‖Z‖ ≤ (‖E‖ * ‖Z‖ * ‖Z‖) * (ρ * ‖E‖) := by nlinarith
  exact le_of_mul_le_mul_left h3 h2

/-- The noise is seen through `√L`: `‖P 𝒜* e‖ ≤ √L ‖e‖`. -/
theorem norm_proj_adjoint_le (hP : IsOrthProj P) (hL : 0 ≤ L)
    (hspec : ∀ Z, P Z = Z → ‖𝒜 Z‖ ^ 2 ≤ L * ‖Z‖ ^ 2) (e : F) :
    ‖P (LinearMap.adjoint 𝒜 e)‖ ≤ √L * ‖e‖ := by
  set w := LinearMap.adjoint 𝒜 e with hw
  set Z := P w with hZdef
  have hZ : P Z = Z := hP.idem w
  have h1 : ‖Z‖ ^ 2 = ⟪𝒜 Z, e⟫ := by
    have h0 : ⟪Z, Z⟫ = ⟪Z, w⟫ :=
      calc ⟪Z, Z⟫ = ⟪P w, Z⟫ := rfl
        _ = ⟪w, P Z⟫ := hP.symm w Z
        _ = ⟪Z, w⟫ := by rw [hZ, real_inner_comm]
    rw [← real_inner_self_eq_norm_sq, h0, hw, LinearMap.adjoint_inner_right]
  have h2 : ‖𝒜 Z‖ ≤ √L * ‖Z‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (𝒜 Z)), ← Real.sqrt_sq (norm_nonneg Z), ← Real.sqrt_mul hL]
    exact Real.sqrt_le_sqrt (hspec Z hZ)
  have h3 : ‖Z‖ ^ 2 ≤ ‖𝒜 Z‖ * ‖e‖ := by
    rw [h1]; exact real_inner_le_norm _ _
  rcases (norm_nonneg Z).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  have h4 : ‖Z‖ * ‖Z‖ ≤ ‖Z‖ * (√L * ‖e‖) := by nlinarith [norm_nonneg e]
  exact le_of_mul_le_mul_left h4 h0

/-- **Abstract IHT step.**  `𝓢` any model set, `T` a best approximation in `𝓢` of the gradient
step `X - λ 𝒜*(𝒜 X - b)`, `P` an orthogonal projector mapping `𝓢` to itself and fixing `X`, `Xs`
and `T`, with `𝒜` of spectrum in `[μ, L]` on the range of `P`.  Then
`‖T - Xs‖ ≤ φ (ρ(λ) ‖X - Xs‖ + λ √L ‖b - 𝒜 Xs‖)`. -/
theorem norm_step_sub_le {𝓢 : Set V} {Q : V →L[ℝ] V} {X Xs T : V} {b : F} (hP : IsOrthProj P)
    (hPX : P X = X) (hPXs : P Xs = Xs) (hPT : P T = T) (hS : ∀ Z ∈ 𝓢, P Z ∈ 𝓢)
    (hspec : ∀ Z, P Z = Z → μ * ‖Z‖ ^ 2 ≤ ‖𝒜 Z‖ ^ 2 ∧ ‖𝒜 Z‖ ^ 2 ≤ L * ‖Z‖ ^ 2) (hlam : 0 ≤ lam)
    (hL : 0 ≤ L)
    (hT : ∀ Z ∈ 𝓢, ‖(X - lam • LinearMap.adjoint 𝒜 (𝒜 X - b)) - T‖ ≤
      ‖(X - lam • LinearMap.adjoint 𝒜 (𝒜 X - b)) - Z‖)
    (hQ : IsOrthProj Q) (hQT : Q T = T)
    (hQX : Q (P (X - lam • LinearMap.adjoint 𝒜 (𝒜 X - b))) ∈ 𝓢)
    (hA : ∀ t : ℝ, 1 ≤ t → shrink Q t Xs ∈ 𝓢) :
    ‖T - Xs‖ ≤ φ * (rate μ L lam * ‖X - Xs‖ + lam * √L * ‖b - 𝒜 Xs‖) := by
  have hφ0 : 0 ≤ φ := Real.goldenRatio_pos.le
  refine (norm_sub_le_gold_mul_proj hP hPT hPXs hS hT hQ hQT hQX hA).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hφ0
  set E := X - Xs with hE
  have hPE : P E = E := by rw [hE, map_sub, hPX, hPXs]
  have e : (X - lam • LinearMap.adjoint 𝒜 (𝒜 X - b)) - Xs =
      (E - lam • LinearMap.adjoint 𝒜 (𝒜 E)) + lam • LinearMap.adjoint 𝒜 (b - 𝒜 Xs) := by
    have h1 : 𝒜 X - b = 𝒜 E - (b - 𝒜 Xs) := by rw [hE, map_sub]; abel
    rw [h1, map_sub, smul_sub, hE]
    abel
  rw [e, map_add, map_smul]
  refine (norm_add_le _ _).trans (add_le_add (norm_proj_gradStep_le hP hspec hlam hPE) ?_)
  rw [norm_smul, Real.norm_of_nonneg hlam, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (norm_proj_adjoint_le hP hL (fun Z hZ => (hspec Z hZ).2) _) hlam

/-- **The bridge to PL.**  If `P` fixes `E` and `μ ‖E‖² ≤ ‖𝒜 E‖²`, the projected gradient of
`½ ‖𝒜 Z‖²` at `E` dominates the loss: `μ ‖𝒜 E‖² ≤ ‖P 𝒜*𝒜 E‖²`.  This is the PL inequality with the
same `μ`, for any Galerkin space containing the error. -/
theorem mul_norm_sq_le_norm_proj_grad (hP : IsOrthProj P) {E : V} (hE : P E = E)
    (hμ : μ * ‖E‖ ^ 2 ≤ ‖𝒜 E‖ ^ 2) :
    μ * ‖𝒜 E‖ ^ 2 ≤ ‖P (LinearMap.adjoint 𝒜 (𝒜 E))‖ ^ 2 := by
  set G := LinearMap.adjoint 𝒜 (𝒜 E) with hG
  have h1 : ‖𝒜 E‖ ^ 2 = ⟪E, P G⟫ := by
    rw [← hP.symm, hE, hG, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have h2 : ‖𝒜 E‖ ^ 2 ≤ ‖E‖ * ‖P G‖ := by
    rw [h1]; exact real_inner_le_norm _ _
  rcases (norm_nonneg E).eq_or_lt with h0 | h0
  · have hE0 : E = 0 := norm_eq_zero.mp h0.symm
    simp [hE0]
  have h3 : ‖E‖ ^ 2 * (μ * ‖𝒜 E‖ ^ 2) ≤ ‖E‖ ^ 2 * ‖P G‖ ^ 2 := by
    have h4 : 0 ≤ ‖𝒜 E‖ ^ 2 := sq_nonneg _
    have h5 := mul_le_mul_of_nonneg_right hμ h4
    have h6 := pow_le_pow_left₀ h4 h2 2
    nlinarith
  exact le_of_mul_le_mul_left h3 (by positivity)

end Spectrum

/-! ### Low-rank matrices: left multiplication -/

section LeftMul

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

/-- Left multiplication by an orthogonal projector matrix is an orthogonal projector for the
Frobenius inner product. -/
lemma isOrthProj_left {P : Matrix m m ℝ} (hP : Curvature.IsOrthProjMat P) :
    IsOrthProj (Frobenius.leftMulCLM P : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) where
  idem X := by simp only [Frobenius.leftMulCLM_apply]; rw [← Matrix.mul_assoc, hP.idem]
  symm X Y := by simp only [Frobenius.leftMulCLM_apply]; rw [Frobenius.inner_mul_left, hP.symm]

lemma shrink_left [DecidableEq m] (P : Matrix m m ℝ) (t : ℝ) (Z : Matrix m n ℝ) :
    shrink (Frobenius.leftMulCLM P) t Z = (P + t⁻¹ • (1 - P)) * Z := by
  simp only [shrink, Frobenius.leftMulCLM_apply, Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.one_mul]

omit [Fintype m] in
/-- `rank [A B] ≤ rank A + rank B`. -/
lemma rank_fromCols_le (A : Matrix m k ℝ) (B : Matrix m l ℝ) :
    (Matrix.fromCols A B).rank ≤ A.rank + B.rank := by
  classical
  have e : Matrix.fromCols A B = A * Matrix.fromCols (1 : Matrix k k ℝ) (0 : Matrix k l ℝ) +
      B * Matrix.fromCols (0 : Matrix l k ℝ) (1 : Matrix l l ℝ) := by
    rw [Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero,
      Matrix.mul_zero, Matrix.mul_one]
    ext i (j | j) <;> simp
  rw [e]
  exact (EckartYoung.rank_add_le _ _).trans
    (add_le_add (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_left _ _))

/-- An orthogonal projector onto a space containing the columns of `B`, of rank at most
`rank B`. -/
lemma exists_orthProj (B : Matrix m k ℝ) :
    ∃ P : Matrix m m ℝ, Curvature.IsOrthProjMat P ∧ P.rank ≤ B.rank ∧ P * B = B := by
  classical
  obtain ⟨U, S, V, hU, -, -, hB⟩ := (SVD.rank_eq_iff_exists_factor (r := B.rank) B).1 rfl
  refine ⟨U * Uᵀ, Curvature.isOrthProjMat_mul_transpose hU, ?_, ?_⟩
  · refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
    simp
  · have h : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
      rw [Matrix.mul_assoc U Uᵀ, ← Matrix.mul_assoc Uᵀ, ← Matrix.mul_assoc Uᵀ, hU,
        Matrix.one_mul, Matrix.mul_assoc U S]
    rwa [← hB] at h

/-- An orthogonal projector of rank `≤ rank A₁ + rank A₂ + rank A₃` fixing the three matrices. -/
lemma exists_orthProj_three (A₁ A₂ A₃ : Matrix m n ℝ) :
    ∃ P : Matrix m m ℝ, Curvature.IsOrthProjMat P ∧ P.rank ≤ A₁.rank + A₂.rank + A₃.rank ∧
      P * A₁ = A₁ ∧ P * A₂ = A₂ ∧ P * A₃ = A₃ := by
  obtain ⟨P, hP, hr, hB⟩ := exists_orthProj (Matrix.fromCols (Matrix.fromCols A₁ A₂) A₃)
  rw [Matrix.mul_fromCols, Matrix.mul_fromCols] at hB
  have hB' := Matrix.fromCols_inj hB
  have hB'' := Matrix.fromCols_inj hB'.1
  exact ⟨P, hP, hr.trans ((rank_fromCols_le _ _).trans
    (Nat.add_le_add_right (rank_fromCols_le _ _) _)), hB''.1, hB''.2, hB'.2⟩

end LeftMul

section LowRank

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {X T : Matrix m n ℝ}

lemma best_of_distLR (hT : ‖X - T‖ ≤ distLR r X) :
    ∀ Z ∈ lowRankSet m n r, ‖X - T‖ ≤ ‖X - Z‖ :=
  fun _ hZ => hT.trans (distLR_le_norm_sub hZ)

/-- The data of the abstract argument for best rank-`r` approximation: `Q` is the column projector
of `T`. -/
private lemma exists_rank_data (hTr : T.rank ≤ r) :
    ∃ Q : Matrix m m ℝ, Curvature.IsOrthProjMat Q ∧ Q.rank ≤ r ∧ Q * T = T := by
  obtain ⟨Q, hQ, hr, hQT⟩ := exists_orthProj T
  exact ⟨Q, hQ, hr.trans hTr, hQT⟩

private lemma mem_of_rank_le {Q : Matrix m m ℝ} (hr : Q.rank ≤ r) (Z : Matrix m n ℝ) :
    Frobenius.leftMulCLM Q Z ∈ lowRankSet m n r :=
  (Matrix.rank_mul_le_left _ _).trans hr

private lemma shrink_mem (Q : Matrix m m ℝ) {B : Matrix m n ℝ}
    (hB : B ∈ lowRankSet m n r) (t : ℝ) :
    shrink (Frobenius.leftMulCLM Q) t B ∈ lowRankSet m n r := by
  classical
  rw [shrink_left]
  exact (Matrix.rank_mul_le_right _ _).trans hB

/-- **Golden truncation inequality, no low-rank assumption on the target.**  If `T` is a best
rank-`r` approximation of `X`, then for every `A`

    ‖T - A‖ ≤ dist(A, M_{≤ r}) + φ ‖X - A‖.

This replaces the constant `2` of `LeanDLRA.norm_bestTrunc_sub_le` (arXiv 2608.27749, Remark 2) by
`φ`, for every target, and reduces to `norm_sub_le_goldenRatio_mul` when `rank A ≤ r`.  Neither
coefficient can be lowered (`one_le_and_goldenRatio_le`).  Corollary G only asks for
the case `rank A ≤ r`. -/
theorem norm_sub_le_distLR_add_gold (hT : ‖X - T‖ ≤ distLR r X) (hTr : T.rank ≤ r)
    (A : Matrix m n ℝ) : ‖T - A‖ ≤ distLR r A + φ * ‖X - A‖ := by
  classical
  obtain ⟨Q, hQ, hr, hQT⟩ := exists_rank_data hTr
  obtain ⟨B, hB, hAB⟩ := exists_best_approx r A
  have h := norm_sub_le_add_gold_mul (isOrthProj_left hQ) (best_of_distLR hT) hQT
    (mem_of_rank_le hr X) (fun t _ => shrink_mem Q hB t) A
  rwa [hAB] at h

/-- **The family behind `norm_sub_le_distLR_add_gold`.**  For every `t > 1` with
`1 + t - t² > 0` (that is `1 < t < φ`),

    ‖T - A‖² ≤ t/(t-1) ‖X - A‖² + t/(1+t-t²) dist(A, M_{≤ r})².

It quantifies the trade-off between the two terms: for `‖X - A‖ ≪ dist(A, M_{≤ r})`, the choice
`t - 1 ≈ ‖X - A‖ / (√2 dist(A, M_{≤ r}))` gives a first-order cost `√2 ‖X - A‖` (this expansion is
not formalised here).3 for the related gap-dependent question. -/
theorem sq_norm_sub_le_family_of_rank (hT : ‖X - T‖ ≤ distLR r X) (hTr : T.rank ≤ r)
    {t : ℝ} (ht : 1 < t) (hs : 0 < 1 + t - t ^ 2) (A : Matrix m n ℝ) :
    ‖T - A‖ ^ 2 ≤ t / (t - 1) * ‖X - A‖ ^ 2 + t / (1 + t - t ^ 2) * distLR r A ^ 2 := by
  classical
  obtain ⟨Q, hQ, hr, hQT⟩ := exists_rank_data hTr
  obtain ⟨B, hB, hAB⟩ := exists_best_approx r A
  have h := sq_norm_sub_le_family (isOrthProj_left hQ) (best_of_distLR hT) hQT
    (mem_of_rank_le hr X) (fun t _ => shrink_mem Q hB t) ht hs A
  rwa [hAB] at h

/-- **Truncating a distance-contractive step.**  If an untruncated step `X ↦ Ŷ` satisfies
`‖Ŷ - Xs‖ ≤ q ‖X - Xs‖` with `rank Xs ≤ r`, its truncation satisfies `‖T - Xs‖ ≤ φ q ‖X - Xs‖`.
This is the true content of the formula `φ (1 - μ λ)` of Corollary G: `q` has to be
a contraction factor for the *distance*, which a PL inequality does not provide
(`phi_window_not_iff`); for a quadratic with restricted spectrum, `q = 1 - λ μ` by
`rate_eq_of_le`. -/
theorem norm_sub_le_gold_mul_of_contraction {Yh Y Xs : Matrix m n ℝ} {q : ℝ}
    (hT : ‖Yh - T‖ ≤ distLR r Yh) (hTr : T.rank ≤ r) (hXs : Xs.rank ≤ r)
    (hq : ‖Yh - Xs‖ ≤ q * ‖Y - Xs‖) : ‖T - Xs‖ ≤ φ * q * ‖Y - Xs‖ := by
  have h := norm_sub_le_distLR_add_gold hT hTr Xs
  rw [distLR_eq_zero_of_rank_le hXs, zero_add] at h
  rw [mul_assoc]
  exact h.trans (mul_le_mul_of_nonneg_left hq Real.goldenRatio_pos.le)

/-- Pythagoras across a Galerkin space, for matrices (`T_r(Y) = T_r(P_S Y)`, one-sided
form): if `P` is an orthogonal projector with `P T = T`, then a best rank-`r` approximation `T` of
`X` is one of `P X`. -/
theorem le_distLR_of_orthProj {P : Matrix m m ℝ} (hP : Curvature.IsOrthProjMat P) (hPT : P * T = T)
    (hT : ‖X - T‖ ≤ distLR r X) : ‖P * X - T‖ ≤ distLR r (P * X) := by
  refine le_distLR_iff.2 fun Z hZ => ?_
  exact best_of_proj (isOrthProj_left hP) hPT
    (fun Z hZ => (Matrix.rank_mul_le_right _ _).trans hZ) (best_of_distLR hT) Z hZ

end LowRank

/-! ### DLRA: the truncation term with `φ` instead of `2` -/

section DLRA

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε h t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Robust truncation bound with `φ`** (Corollary G).  Same setting as
`LeanDLRA.norm_trunc_flow_le` for a best truncation (`κ = 1`): the coefficient `1 + κ = 2` of
`‖Ŷ - A(t₁)‖` becomes `φ`, without assuming that `A(t₁)` has low rank.  This improves the constant
in the bound `h ε_r + 2 ‖Ŷ - A(t₁)‖` of arXiv 2402.08607, Remark 4 and arXiv 2608.27749, Remark 2,
which is how a truncated higher-order step inherits the error of the untruncated one. -/
theorem norm_trunc_flow_le_gold (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) (hε0 : 0 ≤ ε)
    (hε : NearNormalBound F r ε t₀ t₁ (A t₀) (B * h)) {Yh T : Matrix m n ℝ}
    (hT : ‖Yh - T‖ ≤ distLR r Yh) (hTr : T.rank ≤ r) :
    ‖T - A t₁‖ ≤ 2 * (h * (4 * L * B * h + ε)) + φ * ‖Yh - A t₁‖ := by
  have h1 := norm_sub_le_distLR_add_gold hT hTr (A t₁)
  have h2 := distLR_flow_le hF hL hB hc ht₁ hh hA hrank hε0 hε
  linarith

/-- The variant of `norm_trunc_flow_le_gold` without the `h²` term, as in
`LeanDLRA.norm_trunc_flow_le_exp`: `‖T - A(t₁)‖ ≤ h ε e^{L h} + φ ‖Ŷ - A(t₁)‖`, under the global
factored normal-component bound and without continuity of `F` in time. -/
theorem norm_trunc_flow_le_exp_gold (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε0 : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hrank : (A t₀).rank ≤ r) {Yh T : Matrix m n ℝ}
    (hT : ‖Yh - T‖ ≤ distLR r Yh) (hTr : T.rank ≤ r) :
    ‖T - A t₁‖ ≤ h * ε * Real.exp (L * h) + φ * ‖Yh - A t₁‖ := by
  have h1 := norm_sub_le_distLR_add_gold hT hTr (A t₁)
  have h2 := distLR_flow_le_exp hF hL hB hε0 hε ht₁ hh hA hrank
  linarith

/-- **The augmented BUG step truncated back to rank `r`, with `φ`** (the actual step of
`LeanDLRA.fixedRank_trunc_local_error_le`, `κ = 1`):
`‖T - A(t₁)‖ ≤ 2 h (4 L B h + ε) + φ h (c₁ ε + c₂ h)`, where the library has `2 h (c₁ ε + c₂ h)`. -/
theorem fixedRank_trunc_local_error_le_gold {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k]
    [DecidableEq k'] {ϑ : ℝ} {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ}
    {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ}
    {Y₁ : Matrix m n ℝ} (hs : MatrixBUG.IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : MatrixBUG.FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) {T : Matrix m n ℝ}
    (hT : ‖Ua * Sa t₁ * Vaᵀ - T‖ ≤ distLR r (Ua * Sa t₁ * Vaᵀ)) (hTr : T.rank ≤ r) :
    ‖T - A t₁‖ ≤ 2 * (h * (4 * L * B * h + ε)) + φ * (h * (bugC₁ L H * ε + bugC₂ L B H * h)) := by
  have hs' : MatrixBUG.IsRankAdaptiveStep F 0 t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa
      (Ua * Sa t₁ * Vaᵀ) := { hs with trunc := by simp }
  have hloc := hs'.local_error_le hε hF hL hB ht₁ hh hhH hA hA₀
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε t₀ U₀ V₀ S₀ hs.orthU₀ hs.orthV₀)
  have hrank : (A t₀).rank ≤ r := hA₀ ▸ rank_mul_mul_transpose_le U₀ S₀ V₀
  have h1 := norm_trunc_flow_le_gold hF hL hB hc ht₁ hh hA hrank hε0
    (nearNormalBound_of_factored hε _ _ _ _) hT hTr
  have h2 := mul_le_mul_of_nonneg_left (by simpa using hloc) Real.goldenRatio_pos.le
  linarith

/-- **Global error of the fixed-rank truncated augmented BUG integrator, with `φ`.**  The setting
of `LeanDLRA.fixedRank_global_error_le'` with `κ = 1`: each step is an augmented BUG step, truncated
back to rank `r` by a best approximation.  Then for `j ≤ N`, `j h ≤ T`,

    ‖Yⱼ - A(tⱼ)‖ ≤ e^{L T} (δ + T (ε e^{L H} + φ (c₁ ε + c₂ h))),

where the library has `2` in place of `φ`.  The truncated local error is what enters the Lady
Windermere fan, so the improvement survives to the global bound.  It concerns the fixed-rank
truncation only: a tolerance truncation `‖Y₁ - Ŷ‖ ≤ ϑ` costs `‖Ŷ - A‖ + ϑ` and has no factor to
improve. -/
theorem fixedRank_global_error_le_gold (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε₀ : 0 ≤ ε)
    (hε : MatrixBUG.FactoredNormalBound F r ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H)
    {N : ℕ} (hA : ODESolution F A t₀ (t₀ + N * h)) {ka kb : ℕ → ℕ}
    {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {Ua : (j : ℕ) → Matrix m (Fin (ka j)) ℝ}
    {Va : (j : ℕ) → Matrix n (Fin (kb j)) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {Sa : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ} {θ : ℝ}
    (hstep : ∀ j < N, MatrixBUG.IsRankAdaptiveStep F θ (t₀ + j * h) (t₀ + (j + 1) * h) (U j)
      (Sm j) (V j) (Ua j) (Va j) (K j) (Lf j) (Sa j) (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ))
    (htrunc : ∀ j < N, ‖Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ
        - U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ‖
      ≤ distLR r (Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * (δ
        + T * (ε * Real.exp (L * H) + φ * (bugC₁ L H * ε + bugC₂ L B H * h))) := by
  have hφ0 : 0 ≤ φ := Real.goldenRatio_pos.le
  have hc₁ := bugC₁_nonneg hL (hh.trans hhH)
  have hc₂ := bugC₂_nonneg hL hB.nonneg (hh.trans hhH)
  have hexpH : Real.exp (L * h) ≤ Real.exp (L * H) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have hg : 0 ≤ ε * Real.exp (L * H) + φ * (bugC₁ L H * ε + bugC₂ L B H * h) := by
    positivity
  have hloc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ - Φ j (t₀ + (j + 1) * h)‖ ≤
      h * (ε * Real.exp (L * H) + φ * (bugC₁ L H * ε + bugC₂ L B H * h)) + 0 := by
    intro j hj
    have hs := hstep j hj
    have hs0 : MatrixBUG.IsRankAdaptiveStep F 0 (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j)
        (V j) (Ua j) (Va j) (K j) (Lf j) (Sa j) (Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ) :=
      { hs with trunc := by simp }
    have ht : t₀ + (j + 1) * h = t₀ + j * h + h := by ring
    have hloc0 := hs0.local_error_le hε hF hL hB ht hh hhH (hΦ j hj) (hΦ₀ j hj)
    rw [add_zero] at hloc0
    have hrank : (Φ j (t₀ + j * h)).rank ≤ r := by
      rw [hΦ₀ j hj]; exact rank_mul_mul_transpose_le _ _ _
    have h1 := norm_trunc_flow_le_exp_gold hF hL hB hε₀ hε ht hh (hΦ j hj) hrank (htrunc j hj)
      (rank_mul_mul_transpose_le _ _ _)
    have h2 := mul_le_mul_of_nonneg_left hloc0 hφ0
    have h3 : h * ε * Real.exp (L * h) ≤ h * ε * Real.exp (L * H) :=
      mul_le_mul_of_nonneg_left hexpH (by positivity)
    calc _ ≤ h * ε * Real.exp (L * h) + φ *
          ‖Ua j * Sa j (t₀ + (j + 1) * h) * (Va j)ᵀ - Φ j (t₀ + (j + 1) * h)‖ := h1
      _ ≤ _ := by nlinarith
  intro j hj hjT
  have h := InexactSubsteps.lady_windermere_defect (Y := fun j => U j * Sm j * (V j)ᵀ) hF hL hh hA
    hΦ hΦ₀ hg le_rfl hloc hδ j hj hjT
  simpa using h

end DLRA

/-! ### Singular value projection / matrix iterative hard thresholding -/

section SVP

variable {m n : Type*} [Fintype m] [Fintype n] {G : Type*} [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] {𝒜 : Matrix m n ℝ →ₗ[ℝ] G} {r s : ℕ}
  {μ L lam : ℝ} {b : G} {X Xs T : Matrix m n ℝ}

/-- `𝒜` has spectrum in `[μ, L]` on matrices of rank `≤ s`: restricted strong convexity and
smoothness of `Z ↦ ½ ‖𝒜 Z - b‖²`. -/
def RestrictedSpectrum (𝒜 : Matrix m n ℝ →ₗ[ℝ] G) (s : ℕ) (μ L : ℝ) : Prop :=
  ∀ Z : Matrix m n ℝ, Z.rank ≤ s → μ * ‖Z‖ ^ 2 ≤ ‖𝒜 Z‖ ^ 2 ∧ ‖𝒜 Z‖ ^ 2 ≤ L * ‖Z‖ ^ 2

/-- The rank restricted isometry property with constant `δ` at order `s`. -/
def HasRIP (𝒜 : Matrix m n ℝ →ₗ[ℝ] G) (s : ℕ) (δ : ℝ) : Prop :=
  RestrictedSpectrum 𝒜 s (1 - δ) (1 + δ)

omit [FiniteDimensional ℝ G] in
lemma RestrictedSpectrum.mono {s' : ℕ} (h : RestrictedSpectrum 𝒜 s μ L) (hs : s' ≤ s) :
    RestrictedSpectrum 𝒜 s' μ L := fun Z hZ => h Z (hZ.trans hs)

/-- The gradient step `X - λ 𝒜*(𝒜 X - b)` for `Z ↦ ½ ‖𝒜 Z - b‖²`. -/
noncomputable def gradStep (𝒜 : Matrix m n ℝ →ₗ[ℝ] G) (b : G) (lam : ℝ) (X : Matrix m n ℝ) :
    Matrix m n ℝ := X - lam • LinearMap.adjoint 𝒜 (𝒜 X - b)

/-- One step of SVP / matrix IHT with step size `λ`: `T` is **a** best rank-`r` approximation of
the gradient step (ties broken arbitrarily). -/
structure IsSVPStep (𝒜 : Matrix m n ℝ →ₗ[ℝ] G) (b : G) (r : ℕ) (lam : ℝ) (X T : Matrix m n ℝ) :
    Prop where
  rank_le : T.rank ≤ r
  best : ‖gradStep 𝒜 b lam X - T‖ ≤ distLR r (gradStep 𝒜 b lam X)

/-- SVP steps exist. -/
theorem exists_isSVPStep (𝒜 : Matrix m n ℝ →ₗ[ℝ] G) (b : G) (r : ℕ) (lam : ℝ)
    (X : Matrix m n ℝ) : ∃ T, IsSVPStep 𝒜 b r lam X T := by
  obtain ⟨T, hT, h⟩ := exists_best_approx r (gradStep 𝒜 b lam X)
  exact ⟨T, hT, h.le⟩

/-- **Contraction of SVP / matrix IHT with the golden ratio** (Corollary F, sharper
in the RIP order and with a general step size and noise).  If `𝒜` has spectrum in `[μ, L]` on rank
`≤ 3 r`, `X`, `Xs` have rank `≤ r` and `T` is an SVP step of step size `λ ≥ 0`, then

    ‖T - Xs‖ ≤ φ (ρ(λ) ‖X - Xs‖ + λ √L ‖b - 𝒜 Xs‖),   ρ(λ) = max(|1 - λ μ|, |1 - λ L|).

The Galerkin space needs only one side: `P` is the projector onto the column spaces of `X`, `Xs`
and `T`, of dimension `≤ 3 r`, and every matrix in its range has rank `≤ 3 r`.  This gives order
`3 r` (in place of `4 r`).  With the constant `2` of the classical quasi-projection argument
the factor would be `2 ρ(λ)`. -/
theorem norm_svpStep_sub_le (h : RestrictedSpectrum 𝒜 (3 * r) μ L) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hX : X.rank ≤ r) (hXs : Xs.rank ≤ r) (hstep : IsSVPStep 𝒜 b r lam X T) :
    ‖T - Xs‖ ≤ φ * (rate μ L lam * ‖X - Xs‖ + lam * √L * ‖b - 𝒜 Xs‖) := by
  classical
  obtain ⟨p, hp, hpr, hpX, hpXs, hpT⟩ := exists_orthProj_three X Xs T
  have hpr' : p.rank ≤ 3 * r := by
    have := hstep.rank_le
    omega
  obtain ⟨Q, hQ, hr, hQT⟩ := exists_rank_data hstep.rank_le
  refine norm_step_sub_le (P := Frobenius.leftMulCLM p) (Q := Frobenius.leftMulCLM Q)
    (𝓢 := lowRankSet m n r) (isOrthProj_left hp) hpX hpXs hpT
    (fun Z hZ => (Matrix.rank_mul_le_right _ _).trans hZ) (fun Z hZ => h Z ?_) hlam hL
    (best_of_distLR hstep.best) (isOrthProj_left hQ) hQT (mem_of_rank_le hr _)
    (fun t _ => shrink_mem Q hXs t)
  rw [← hZ]
  exact (Matrix.rank_mul_le_left _ _).trans hpr'

/-- The noiseless case: `‖T - Xs‖ ≤ φ ρ(λ) ‖X - Xs‖`. -/
theorem norm_svpStep_sub_le_of_exact (h : RestrictedSpectrum 𝒜 (3 * r) μ L) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam) (hX : X.rank ≤ r) (hXs : Xs.rank ≤ r)
    (hstep : IsSVPStep 𝒜 (𝒜 Xs) r lam X T) :
    ‖T - Xs‖ ≤ φ * rate μ L lam * ‖X - Xs‖ := by
  have := norm_svpStep_sub_le h hL hlam hX hXs hstep
  simpa [mul_assoc] using this

/-- `ρ(1) = δ` for the RIP normalisation `μ = 1 - δ`, `L = 1 + δ`. -/
lemma rate_rip {δ : ℝ} (hδ : 0 ≤ δ) : rate (1 - δ) (1 + δ) 1 = δ := by
  have h1 : (1 : ℝ) - 1 * (1 - δ) = δ := by ring
  have h2 : (1 : ℝ) - 1 * (1 + δ) = -δ := by ring
  rw [rate, h1, h2, abs_neg, max_self, abs_of_nonneg hδ]

/-- **The RIP form.**  Under `δ_{3r}`, unit-step SVP satisfies
`‖X_{k+1} - X*‖ ≤ φ δ_{3r} ‖X_k - X*‖`, a contraction when `δ_{3r} < 1/φ ≈ 0.618`; the threshold is
exact (`exists_stall_of_rip`).  The quasi-projection argument with the constant `2` needs
`δ_{3r} < 1/2`.  Jain–Meka–Dhillon's loss-based analysis needs `δ_{2r} < 1/3`, a condition at
another order, so the two are not directly comparable. -/
theorem norm_svpStep_sub_le_of_rip {δ : ℝ} (hδ : 0 ≤ δ) (h : HasRIP 𝒜 (3 * r) δ)
    (hX : X.rank ≤ r) (hXs : Xs.rank ≤ r) (hstep : IsSVPStep 𝒜 (𝒜 Xs) r 1 X T) :
    ‖T - Xs‖ ≤ φ * δ * ‖X - Xs‖ := by
  have := norm_svpStep_sub_le_of_exact h (by linarith) zero_le_one hX hXs hstep
  rwa [rate_rip hδ] at this

/-- Corollary F with RIP at order `4 r`. -/
theorem norm_svpStep_sub_le_of_rip_four {δ : ℝ} (hδ : 0 ≤ δ) (h : HasRIP 𝒜 (4 * r) δ)
    (hX : X.rank ≤ r) (hXs : Xs.rank ≤ r) (hstep : IsSVPStep 𝒜 (𝒜 Xs) r 1 X T) :
    ‖T - Xs‖ ≤ φ * δ * ‖X - Xs‖ :=
  norm_svpStep_sub_le_of_rip hδ (RestrictedSpectrum.mono h (by omega)) hX hXs hstep

/-- **Linear convergence of SVP, with noise.**  Along any SVP trajectory from rank `≤ r` and with
`q = φ ρ(λ)`, `‖X_k - Xs‖ ≤ qᵏ ‖X₀ - Xs‖ + (∑_{i<k} qⁱ) φ λ √L ‖b - 𝒜 Xs‖`. -/
theorem norm_svp_iterate_sub_le (h : RestrictedSpectrum 𝒜 (3 * r) μ L) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam) {Y : ℕ → Matrix m n ℝ} (hY0 : (Y 0).rank ≤ r) (hXs : Xs.rank ≤ r)
    (hY : ∀ k, IsSVPStep 𝒜 b r lam (Y k) (Y (k + 1))) (k : ℕ) :
    ‖Y k - Xs‖ ≤ (φ * rate μ L lam) ^ k * ‖Y 0 - Xs‖ +
      (∑ i ∈ Finset.range k, (φ * rate μ L lam) ^ i) * (φ * (lam * √L * ‖b - 𝒜 Xs‖)) := by
  have hrank : ∀ k, (Y k).rank ≤ r := fun k => by
    cases k with
    | zero => exact hY0
    | succ k => exact (hY k).rank_le
  set q := φ * rate μ L lam with hq
  have hq0 : 0 ≤ q := mul_nonneg Real.goldenRatio_pos.le (rate_nonneg _ _ _)
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := norm_svpStep_sub_le h hL hlam (hrank k) hXs (hY k)
    have h2 := mul_le_mul_of_nonneg_left ih hq0
    rw [geom_sum_succ]
    calc ‖Y (k + 1) - Xs‖ ≤ q * ‖Y k - Xs‖ + φ * (lam * √L * ‖b - 𝒜 Xs‖) := by
          rw [hq, mul_assoc, ← mul_add]
          exact h1
      _ ≤ _ := by
          have e : q ^ (k + 1) = q * q ^ k := pow_succ' q k
          rw [e]
          nlinarith

/-- For `φ ρ(λ) < 1` and exact data the iterates converge to `Xs`, whatever the tie-breaking. -/
theorem tendsto_svp (h : RestrictedSpectrum 𝒜 (3 * r) μ L) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hq : φ * rate μ L lam < 1) {Y : ℕ → Matrix m n ℝ} (hY0 : (Y 0).rank ≤ r)
    (hXs : Xs.rank ≤ r) (hY : ∀ k, IsSVPStep 𝒜 (𝒜 Xs) r lam (Y k) (Y (k + 1))) :
    Tendsto Y atTop (𝓝 Xs) := by
  have hq0 : 0 ≤ φ * rate μ L lam := mul_nonneg Real.goldenRatio_pos.le (rate_nonneg _ _ _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const ‖Y 0 - Xs‖ |>.trans (by simp))
  simpa using norm_svp_iterate_sub_le h hL hlam hY0 hXs hY k

/-- The hypothesis of the window implies a PL inequality for `ℓ(Z) = ½ ‖𝒜 Z - 𝒜 Xs‖²`, with the
same `μ`, for the gradient projected on any Galerkin space containing `X` and `Xs`:
`2 μ (ℓ(X) - 0) ≤ ‖p ∇ℓ(X)‖²`.  It is not the tangent-space (Riemannian) PL inequality, since
`X - Xs` need not be tangent to `M_r` at `X`. -/
theorem two_mul_loss_le_norm_proj_grad (h : RestrictedSpectrum 𝒜 (2 * r) μ L) (hX : X.rank ≤ r)
    (hXs : Xs.rank ≤ r) {p : Matrix m m ℝ} (hp : Curvature.IsOrthProjMat p) (hpX : p * X = X)
    (hpXs : p * Xs = Xs) :
    2 * μ * (‖𝒜 X - 𝒜 Xs‖ ^ 2 / 2) ≤ ‖p * LinearMap.adjoint 𝒜 (𝒜 X - 𝒜 Xs)‖ ^ 2 := by
  classical
  have hr : (X - Xs).rank ≤ 2 * r := by
    have e : X - Xs = X + (-1 : Matrix m m ℝ) * Xs := by
      rw [Matrix.neg_mul, Matrix.one_mul, sub_eq_add_neg]
    rw [e]
    refine (EckartYoung.rank_add_le _ _).trans ?_
    have := Matrix.rank_mul_le_right (-1 : Matrix m m ℝ) Xs
    omega
  have hE : Frobenius.leftMulCLM p (X - Xs) = X - Xs := by
    simp only [Frobenius.leftMulCLM_apply, Matrix.mul_sub, hpX, hpXs]
  have := mul_norm_sq_le_norm_proj_grad (𝒜 := 𝒜) (isOrthProj_left hp) hE (h _ hr).1
  rw [map_sub 𝒜, Frobenius.leftMulCLM_apply] at this
  linarith

end SVP

/-! ### The step-size window -/

section Window

variable {μ L lam : ℝ}

/-- In the classical range `λ ≤ 2/(μ + L)` the factor `ρ(λ)` is `1 - λ μ`, the expression of
Corollary G. -/
lemma rate_eq_of_le (hμL : μ ≤ L) (hlam : 0 ≤ lam) (h : lam * (μ + L) ≤ 2) :
    rate μ L lam = 1 - lam * μ := by
  have h1 : lam * μ ≤ lam * L := mul_le_mul_of_nonneg_left hμL hlam
  have h2 : lam * μ ≤ 1 := by nlinarith
  have h3 : |1 - lam * μ| = 1 - lam * μ := abs_of_nonneg (by linarith)
  rw [rate, h3]
  refine max_eq_left (abs_le.2 ⟨?_, by linarith⟩)
  nlinarith

/-- **The step-size window for the bound.**  For `0 < μ ≤ L`, the bound of `norm_svpStep_sub_le` is
a contraction exactly for `(1 - 1/φ)/μ < λ < φ/L`, with `1 - 1/φ ≈ 0.382`.  This is an equivalence
for the *bound*, not for the iteration: see `phi_window_not_iff`. -/
theorem gold_rate_lt_one_iff (hμ : 0 < μ) (hμL : μ ≤ L) :
    φ * rate μ L lam < 1 ↔ (1 - φ⁻¹) / μ < lam ∧ lam < φ / L := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ1 := gold_gt
  have hφ2 := gold_lt
  have hinv := gold_inv
  have hL : 0 < L := hμ.trans_le hμL
  have hc : φ * rate μ L lam < 1 ↔ rate μ L lam < φ⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hφ0, mul_comm]
  rw [hc, rate, max_lt_iff, abs_lt, abs_lt, div_lt_iff₀ hμ, lt_div_iff₀ hL, hinv]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hlam : 0 < lam := by
      by_contra hneg
      have : lam * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hμ.le
      linarith
    have h3 : lam * μ ≤ lam * L := mul_le_mul_of_nonneg_left hμL hlam.le
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The comparison: with the constant `2` the window is `1/(2 μ) < λ < 3/(2 L)`. -/
theorem two_rate_lt_one_iff (hμ : 0 < μ) (hμL : μ ≤ L) :
    2 * rate μ L lam < 1 ↔ 1 / (2 * μ) < lam ∧ lam < 3 / (2 * L) := by
  have hL : 0 < L := hμ.trans_le hμL
  have hc : 2 * rate μ L lam < 1 ↔ rate μ L lam < 1 / 2 := by
    rw [lt_div_iff₀ two_pos, mul_comm]
  have e1 : 1 / (2 * μ) < lam ↔ 1 < lam * (2 * μ) := div_lt_iff₀ (by positivity)
  have e2 : lam < 3 / (2 * L) ↔ lam * (2 * L) < 3 := lt_div_iff₀ (by positivity)
  rw [e1, e2, hc, rate, max_lt_iff, abs_lt, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hlam : 0 < lam := by
      by_contra hneg
      have : lam * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hμ.le
      linarith
    have h3 : lam * μ ≤ lam * L := mul_le_mul_of_nonneg_left hμL hlam.le
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **The window is non-empty iff `L/μ < φ³ ≈ 4.236`**, against `L/μ < 3` for the constant `2`:
`δ < 1/φ` in the RIP normalisation is `(1 + δ)/(1 - δ) < φ³`.  The upper end
of the window is what makes the condition on `L/μ` appear. -/
theorem window_nonempty_iff (hμ : 0 < μ) (hμL : μ ≤ L) :
    (∃ lam, (1 - φ⁻¹) / μ < lam ∧ lam < φ / L) ↔ L < φ ^ 3 * μ := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ2 := gold_sq
  have hL : 0 < L := hμ.trans_le hμL
  have h3 : φ ^ 3 = 2 * φ + 1 := by linear_combination (φ + 1) * hφ2
  have h4 : (2 - φ) * φ ^ 3 = φ := by rw [h3]; linear_combination (-2) * hφ2
  have hiff : (1 - φ⁻¹) / μ < φ / L ↔ L < φ ^ 3 * μ := by
    rw [gold_inv, div_lt_div_iff₀ hμ hL, show 1 - (φ - 1) = 2 - φ by ring]
    have h5 : 0 < φ ^ 3 := by positivity
    constructor
    · intro h
      have := mul_lt_mul_of_pos_left h h5
      have h6 : φ ^ 3 * ((2 - φ) * L) = φ * L :=
        calc φ ^ 3 * ((2 - φ) * L) = ((2 - φ) * φ ^ 3) * L := by ring
          _ = φ * L := by rw [h4]
      rw [h6] at this
      have h7 : φ * L < φ * (φ ^ 3 * μ) := by nlinarith
      exact lt_of_mul_lt_mul_left h7 hφ0.le
    · intro h
      have h6 : 0 < 2 - φ := by linarith [gold_lt]
      have := mul_lt_mul_of_pos_left h h6
      calc (2 - φ) * L < (2 - φ) * (φ ^ 3 * μ) := this
        _ = φ * μ := by rw [← mul_assoc, h4]
  rw [← hiff]
  constructor
  · rintro ⟨lam, h1, h2⟩
    exact h1.trans h2
  · exact fun h => exists_between h

lemma three_lt_gold_cube : 3 < φ ^ 3 := by
  have h3 : φ ^ 3 = 2 * φ + 1 := by linear_combination (φ + 1) * gold_sq
  rw [h3]
  linarith [gold_gt]

end Window

/-! ### Corollary G's "iff" is false; the true statement -/

section NotIff

variable {m n : Type*} [Fintype m] [Fintype n] {r s : ℕ} {lam : ℝ} {X T : Matrix m n ℝ}

/-- For `ℓ(X) = ½ ‖X‖²` the truncated gradient iteration from rank `≤ r` is
`X ↦ (1 - λ) X`: truncation does nothing, whatever `r`. -/
theorem svpStep_id_eq (hX : X.rank ≤ r)
    (h : IsSVPStep (LinearMap.id : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) 0 r lam X T) :
    T = (1 - lam) • X := by
  classical
  have e : gradStep (LinearMap.id : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) 0 lam X = (1 - lam) • X := by
    simp [gradStep, sub_smul]
  have hb := h.best
  rw [e] at hb
  have hr : ((1 - lam) • X).rank ≤ r := by
    have e2 : (1 - lam) • X = ((1 - lam) • (1 : Matrix m m ℝ)) * X := by
      rw [Matrix.smul_mul, Matrix.one_mul]
    rw [e2]
    exact (Matrix.rank_mul_le_right _ _).trans hX
  rw [distLR_eq_zero_of_rank_le hr] at hb
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp hb)).symm

/-- `𝒜 = id` has spectrum exactly `{1}` at every rank. -/
lemma restrictedSpectrum_id (s : ℕ) :
    RestrictedSpectrum (LinearMap.id : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) s 1 1 :=
  fun Z _ => by simp

/-- `ℓ(X) = ½ ‖X‖²` satisfies the Riemannian PL inequality with `μ = 1`, with equality, on the
whole manifold of matrices `U S Vᵀ`: its gradient `X` is tangent at `X`. -/
theorem riemannianPL_half_sq {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k]
    {U : Matrix m k ℝ} {S : Matrix k k' ℝ} (V : Matrix n k' ℝ) (hU : Uᵀ * U = 1) :
    2 * 1 * (1 / 2 * ‖U * S * Vᵀ‖ ^ 2) = ‖tangentProj U V (U * S * Vᵀ)‖ ^ 2 := by
  rw [tangentProj_mul_mul_transpose hU V S]
  ring

/-- **The "iff" in Corollary G is false, in both directions.**  Take
`ℓ(X) = ½ ‖X‖²`, with `ℓ⋆ = 0`: the Riemannian PL inequality
`2 μ (ℓ(X) - ℓ⋆) ≤ ‖P_X ∇ℓ(X)‖²` holds with `μ = 1` (`riemannianPL_half_sq`), and with `𝒜 = id` the
truncated iteration is the SVP iteration.

* `λ = 1/10`: `φ (1 - μ λ) > 1`, yet the iteration contracts with the factor `9/10`;
* `λ = 3`: `φ (1 - μ λ) < 1`, yet the iteration doubles the error.

The formula `φ (1 - μ λ)` is a bound, valid only under a smoothness restriction on `λ`
(`rate_eq_of_le`), and only in the worst case over `L`: see `exists_stall`. -/
theorem phi_window_not_iff (hX : X.rank ≤ r) :
    (1 < φ * (1 - 1 / 10 * 1) ∧
      ∀ T, IsSVPStep (LinearMap.id : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) 0 r (1 / 10) X T →
        ‖T‖ = 9 / 10 * ‖X‖) ∧
    (φ * (1 - 3 * 1) < 1 ∧
      ∀ T, IsSVPStep (LinearMap.id : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) 0 r 3 X T →
        ‖T‖ = 2 * ‖X‖) := by
  have hφ1 := gold_gt
  have hφ2 := gold_sq
  have h2 : (1.6 : ℝ) < φ := by nlinarith
  refine ⟨⟨by nlinarith, fun T hT => ?_⟩, ⟨by nlinarith, fun T hT => ?_⟩⟩
  · rw [svpStep_id_eq hX hT, norm_smul]
    norm_num
  · rw [svpStep_id_eq hX hT, norm_smul]
    norm_num

end NotIff

/-! ### Realising a prescribed gradient step by a rank-one perturbation of the identity -/

section Realization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `Z ↦ α Z + (β - α) ⟪u, Z⟫ u`: multiplication by `β` on the unit vector `u`, by `α` on `u^⊥`. -/
noncomputable def rankOneOp (u : V) (α β : ℝ) : V →ₗ[ℝ] V where
  toFun Z := α • Z + ((β - α) * ⟪u, Z⟫) • u
  map_add' Z W := by
    simp only [smul_add, inner_add_right, mul_add, add_smul]
    abel
  map_smul' c Z := by
    simp only [RingHom.id_apply, smul_add, inner_smul_right, smul_smul]
    congr 2 <;> ring

lemma rankOneOp_apply (u : V) (α β : ℝ) (Z : V) :
    rankOneOp u α β Z = α • Z + ((β - α) * ⟪u, Z⟫) • u := rfl

lemma rankOneOp_symm (u : V) (α β : ℝ) (Z W : V) :
    ⟪rankOneOp u α β Z, W⟫ = ⟪Z, rankOneOp u α β W⟫ := by
  simp only [rankOneOp_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    conj_trivial, real_inner_comm Z u]
  ring

lemma norm_sq_rankOneOp {u : V} (hu : ‖u‖ = 1) (α β : ℝ) (Z : V) :
    ‖rankOneOp u α β Z‖ ^ 2 = α ^ 2 * ‖Z‖ ^ 2 + (β ^ 2 - α ^ 2) * ⟪u, Z⟫ ^ 2 := by
  rw [rankOneOp_apply, norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, inner_smul_left,
    inner_smul_right, hu, Real.norm_eq_abs, sq_abs, Real.norm_eq_abs, sq_abs, real_inner_comm Z u]
  simp only [conj_trivial]
  ring

lemma rankOneOp_rankOneOp {u : V} (hu : ‖u‖ = 1) (α β : ℝ) (Z : V) :
    rankOneOp u α β (rankOneOp u α β Z) = α ^ 2 • Z + ((β ^ 2 - α ^ 2) * ⟪u, Z⟫) • u := by
  have hu2 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  simp only [rankOneOp_apply, inner_add_right, inner_smul_right, hu2, smul_add, smul_smul]
  rw [add_assoc, ← add_smul]
  congr 2
  · ring
  · ring

/-- **Realisation.**  Let `s = 1 - λ μ`.  If `‖W‖ ≤ s ‖E‖` and `⟪W, E⟫ < s ‖E‖²`, then there is an
operator `𝒜` with spectrum in `[μ, L]`, `λ (μ + L) ≤ 2`, whose gradient step sends `E` to `W`:
`E - λ 𝒜*𝒜 E = W`.  The operator is `√μ` on the orthogonal complement of the line of
`s E - W` and `√L` on it.  If `λ (μ + L) = 2`, then `I - λ 𝒜*𝒜` is `s` times the Householder
reflection taking `E` to `W/s`. -/
theorem exists_realization [FiniteDimensional ℝ V] {E W : V} {μ lam : ℝ} (hμ : 0 ≤ μ)
    (hlam : 0 < lam) (hW : ‖W‖ ≤ (1 - lam * μ) * ‖E‖)
    (hpos : ⟪W, E⟫ < (1 - lam * μ) * ‖E‖ ^ 2) :
    ∃ (L : ℝ) (𝒜 : V →ₗ[ℝ] V), μ ≤ L ∧ lam * (μ + L) ≤ 2 ∧
      (∀ Z, μ * ‖Z‖ ^ 2 ≤ ‖𝒜 Z‖ ^ 2 ∧ ‖𝒜 Z‖ ^ 2 ≤ L * ‖Z‖ ^ 2) ∧
      E - lam • LinearMap.adjoint 𝒜 (𝒜 E) = W := by
  set s := 1 - lam * μ with hs
  set u₀ := s • E - W with hu₀
  have hE : 0 < ‖E‖ := by
    rcases (norm_nonneg E).eq_or_lt with h | h
    · have hE0 : E = 0 := norm_eq_zero.mp h.symm
      simp [hE0] at hpos
    · exact h
  have hs0 : 0 ≤ s := by
    by_contra hneg
    have : s * ‖E‖ < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hE
    linarith [norm_nonneg W]
  have hin : ⟪u₀, E⟫ = s * ‖E‖ ^ 2 - ⟪W, E⟫ := by
    rw [hu₀, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  have hin0 : 0 < ⟪u₀, E⟫ := by rw [hin]; linarith
  have hn : ‖u₀‖ ^ 2 = s ^ 2 * ‖E‖ ^ 2 - 2 * s * ⟪W, E⟫ + ‖W‖ ^ 2 := by
    rw [hu₀, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_left,
      real_inner_comm E W]
    simp only [conj_trivial]
    ring
  have hu0 : 0 < ‖u₀‖ := by
    refine norm_pos_iff.2 fun h => ?_
    rw [h, inner_zero_left] at hin0
    exact lt_irrefl _ hin0
  set n := ‖u₀‖ with hndef
  set γ := n ^ 2 / ⟪u₀, E⟫ with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hγ1 : γ * ⟪u₀, E⟫ = n ^ 2 := div_mul_cancel₀ _ hin0.ne'
  have hγ2 : γ ≤ 2 * s := by
    rw [hγ, div_le_iff₀ hin0, hn, hin]
    have h1 : ‖W‖ ^ 2 ≤ (s * ‖E‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
    nlinarith
  set L := μ + γ / lam with hL
  have hμL : μ ≤ L := by
    have : 0 ≤ γ / lam := by positivity
    linarith
  have hL0 : 0 ≤ L := hμ.trans hμL
  set û := n⁻¹ • u₀ with hû
  have hû1 : ‖û‖ = 1 := by
    rw [hû, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hu0, inv_mul_cancel₀ hu0.ne']
  set 𝒜 := rankOneOp û √μ √L with h𝒜
  have hadj : LinearMap.adjoint 𝒜 = 𝒜 :=
    ((LinearMap.eq_adjoint_iff 𝒜 𝒜).2 (rankOneOp_symm û √μ √L)).symm
  have hsμ : √μ ^ 2 = μ := Real.sq_sqrt hμ
  have hsL : √L ^ 2 = L := Real.sq_sqrt hL0
  refine ⟨L, 𝒜, hμL, ?_, fun Z => ?_, ?_⟩
  · have : lam * (γ / lam) = γ := mul_div_cancel₀ _ hlam.ne'
    rw [hL, mul_add, mul_add, this]
    nlinarith
  · have hnorm := norm_sq_rankOneOp hû1 √μ √L Z
    rw [hsμ, hsL] at hnorm
    have h1 : ⟪û, Z⟫ ^ 2 ≤ ‖Z‖ ^ 2 := by
      have := abs_real_inner_le_norm û Z
      rw [hû1, one_mul] at this
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h2 := sq_nonneg ⟪û, Z⟫
    have h3 : 0 ≤ L - μ := by linarith
    rw [show 𝒜 Z = rankOneOp û √μ √L Z from rfl, hnorm]
    constructor <;> nlinarith
  · rw [hadj, show 𝒜 (𝒜 E) = rankOneOp û √μ √L (rankOneOp û √μ √L E) from rfl,
      rankOneOp_rankOneOp hû1, hsμ, hsL]
    have e1 : lam * (L - μ) = γ := by
      rw [hL, add_sub_cancel_left]
      exact mul_div_cancel₀ _ hlam.ne'
    have e2 : ⟪û, E⟫ = n⁻¹ * ⟪u₀, E⟫ := by rw [hû, inner_smul_left]; simp
    have e3 : (lam * ((L - μ) * ⟪û, E⟫)) • û = u₀ := by
      rw [← mul_assoc, e1, e2, hû, smul_smul]
      have : γ * (n⁻¹ * ⟪u₀, E⟫) * n⁻¹ = 1 := by
        have h0 : γ * ⟪u₀, E⟫ * (n⁻¹ * n⁻¹) = 1 := by
          rw [hγ1]; field_simp
        linarith
      rw [this, one_smul]
    rw [smul_add, smul_smul, smul_smul, e3, hu₀, hs, sub_smul, one_smul]
    abel

end Realization

/-! ### Explicit `2 × 2` matrices -/

section Diagonal

/-- `diag(a, b)`. -/
def dg (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![a, b]

lemma norm_sq_dg (a b : ℝ) : ‖dg a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp [dg, Fin.sum_univ_two]

lemma inner_dg (a b c e : ℝ) : ⟪dg a b, dg c e⟫ = a * c + b * e := by
  rw [Frobenius.inner_def]
  simp [dg, Fin.sum_univ_two]

lemma dg_sub (a b c e : ℝ) : dg a b - dg c e = dg (a - c) (b - e) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

lemma dg_add (a b c e : ℝ) : dg a b + dg c e = dg (a + c) (b + e) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

lemma rank_dg_left (a : ℝ) : (dg a 0).rank ≤ 1 := by
  have e : dg a 0 = Matrix.vecMulVec ![a, 0] ![1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, Matrix.vecMulVec_apply]
  rw [e]
  exact Matrix.rank_vecMulVec_le _ _

lemma rank_dg_right (b : ℝ) : (dg 0 b).rank ≤ 1 := by
  have e : dg 0 b = Matrix.vecMulVec ![0, b] ![0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, Matrix.vecMulVec_apply]
  rw [e]
  exact Matrix.rank_vecMulVec_le _ _

/-- `diag(1, 0)` is a best rank-one approximation of `diag(1, c)` for `0 ≤ c ≤ 1`. -/
lemma dg_best {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : ‖dg 1 c - dg 1 0‖ ≤ distLR 1 (dg 1 c) := by
  have hn : ‖dg 1 c - dg 1 0‖ = c := by
    rw [dg_sub, sub_self, sub_zero]
    refine (pow_left_inj₀ (norm_nonneg _) h0 two_ne_zero).mp ?_
    rw [norm_sq_dg]
    ring
  rw [hn]
  refine le_distLR_diagonal h0 (fun i => ?_) (by simp)
  fin_cases i
  · simpa using h1.trans (le_abs_self 1)
  · simpa using le_abs_self c

/-- For `0 ≤ c < 1` the best rank-one approximation of `diag(1, c)` is unique. -/
lemma dg_best_unique {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hr : T.rank ≤ 1) (hT : ‖dg 1 c - T‖ ≤ distLR 1 (dg 1 c)) : T = dg 1 0 := by
  have hc : distLR 1 (dg 1 c) ≤ c := by
    refine (distLR_le_norm_sub (rank_dg_left 1)).trans (le_of_eq ?_)
    rw [dg_sub, sub_self, sub_zero]
    refine (pow_left_inj₀ (norm_nonneg _) h0 two_ne_zero).mp ?_
    rw [norm_sq_dg]
    ring
  have hle : ‖dg 1 c - T‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hT.trans hc) 2
  have hdet : T.det = 0 := by
    by_contra hne
    have hu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hne)
    have h2 : T.rank = 2 := by rw [Matrix.rank_of_isUnit T hu, Fintype.card_fin]
    omega
  rw [Matrix.det_fin_two] at hdet
  rw [Frobenius.norm_sq_eq_sum] at hle
  simp only [Fin.sum_univ_two, Matrix.sub_apply, dg, Matrix.diagonal_apply_eq] at hle
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.diagonal_apply_ne,
    ne_eq, Fin.isValue, zero_ne_one, not_false_eq_true, one_ne_zero, zero_sub,
    even_two, Even.neg_pow] at hle
  set a := T 0 0
  set e := T 0 1
  set g := T 1 0
  set f := T 1 1
  have hf : f = 0 := by
    rcases lt_trichotomy f 0 with h | h | h
    · have h2 : 0 < -f * (1 + c) := mul_pos (by linarith) (by linarith)
      nlinarith [sq_nonneg (1 - a + f), sq_nonneg (e - g), sq_nonneg (e + g)]
    · exact h
    · have h2 : 0 < f * (1 - c) := mul_pos h (by linarith)
      nlinarith [sq_nonneg (1 - a - f), sq_nonneg (e - g), sq_nonneg (e + g)]
  rw [hf] at hle hdet
  have ha : (1 - a) ^ 2 + e ^ 2 + g ^ 2 ≤ 0 := by nlinarith
  have ha1 : a = 1 := by nlinarith [sq_nonneg (1 - a), sq_nonneg e, sq_nonneg g]
  have he : e = 0 := by nlinarith [sq_nonneg (1 - a), sq_nonneg e, sq_nonneg g]
  have hg : g = 0 := by nlinarith [sq_nonneg (1 - a), sq_nonneg e, sq_nonneg g]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [dg] using ha1
  · simpa [dg] using he
  · simpa [dg] using hg
  · simpa [dg] using hf

end Diagonal

/-! ### Sharpness -/

section Sharpness

/-- The extremal configuration of Theorem E: `X = I₂`, `A = diag(0, φ)`, `T = diag(1, 0)`. -/
lemma dg_extremal : ‖dg 1 0 - dg 0 φ‖ = φ * ‖dg 1 1 - dg 0 φ‖ := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ3 := gold_sq
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [dg_sub, dg_sub, mul_pow, norm_sq_dg, norm_sq_dg, hφ3]
  nlinarith

/-- **The two coefficients of `norm_sub_le_distLR_add_gold` are optimal, separately.**  If
`‖T - A‖ ≤ a dist(A, M_{≤ 1}) + b ‖X - A‖` holds for all `2 × 2` data, then `a ≥ 1` and `b ≥ φ`, so
the pair `(1, φ)` cannot be improved in either coordinate.  This does not say that the sum is the
exact envelope in `(dist, ‖X - A‖)` jointly: `sq_norm_sub_le_family_of_rank` is smaller. -/
theorem one_le_and_goldenRatio_le {a b : ℝ}
    (h : ∀ X A T : Matrix (Fin 2) (Fin 2) ℝ, ‖X - T‖ ≤ distLR 1 X → T.rank ≤ 1 →
      ‖T - A‖ ≤ a * distLR 1 A + b * ‖X - A‖) : 1 ≤ a ∧ φ ≤ b := by
  constructor
  · have hb := dg_best (c := 1) zero_le_one le_rfl
    have hn : ‖dg 1 1 - dg 1 0‖ = 1 := by
      refine (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp ?_
      rw [dg_sub, norm_sq_dg]
      ring
    have h1 := h (dg 1 1) (dg 1 1) (dg 1 0) hb (rank_dg_left 1)
    rw [sub_self, norm_zero, mul_zero, add_zero, norm_sub_rev, hn] at h1
    have h2 : distLR 1 (dg 1 1) ≤ 1 := (distLR_le_norm_sub (rank_dg_left 1)).trans hn.le
    have h3 : (1 : ℝ) ≤ distLR 1 (dg 1 1) := hn.ge.trans hb
    have : distLR 1 (dg 1 1) = 1 := le_antisymm h2 h3
    rw [this, mul_one] at h1
    exact h1
  · have h1 := h (dg 1 1) (dg 0 φ) (dg 1 0) (dg_best zero_le_one le_rfl) (rank_dg_left 1)
    rw [distLR_eq_zero_of_rank_le (rank_dg_right φ), mul_zero, zero_add, dg_extremal] at h1
    have h2 : 0 < ‖dg 1 1 - dg 0 φ‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have := congrFun (congrFun (sub_eq_zero.mp h0) 0) 0
      simp [dg] at this
    exact le_of_mul_le_mul_right h1 h2

variable {μ lam : ℝ}

/-- **Spurious fixed points for every step size below the window** (the correct form of the
necessity in Corollary G).  If `φ (1 - λ μ) ≥ 1`, there are `L ≥ μ` with
`λ (μ + L) ≤ 2` (so `ρ(λ) = 1 - λ μ`) and a sensing operator on `ℝ^{2 × 2}` with spectrum in
`[μ, L]` on **all** matrices (so the solution of `𝒜 Z = b` is unique), a rank-one solution `Xs`,
and a rank-one `X ≠ Xs` which is a fixed point of SVP with rank `r = 1` and step `λ`.  If moreover
`φ (1 - λ μ) > 1`, the fixed point does not depend on tie-breaking: `X` is the only SVP step
from `X`. -/
theorem exists_stall (hμ : 0 < μ) (hlam : 0 < lam) (hgold : 1 ≤ φ * (1 - lam * μ)) :
    ∃ (L : ℝ) (𝒜 : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      (X Xs : Matrix (Fin 2) (Fin 2) ℝ), μ ≤ L ∧ lam * (μ + L) ≤ 2 ∧ X.rank ≤ 1 ∧ Xs.rank ≤ 1 ∧
      X ≠ Xs ∧ (∀ s, RestrictedSpectrum 𝒜 s μ L) ∧ IsSVPStep 𝒜 (𝒜 Xs) 1 lam X X ∧
      (1 < φ * (1 - lam * μ) → ∀ T, IsSVPStep 𝒜 (𝒜 Xs) 1 lam X T → T = X) := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ1 := gold_gt
  have hφ2 := gold_lt
  have hφ3 := gold_sq
  set s := 1 - lam * μ with hs
  have hs1 : s < 1 := by have := mul_pos hlam hμ; linarith
  have hs0 : φ - 1 ≤ s := by
    have h1 : 1 ≤ φ * s := hgold
    nlinarith
  have hs2 : 2 - φ ≤ s ^ 2 := by nlinarith
  have hrad : 0 ≤ s ^ 2 * (φ + 2) - 1 := by nlinarith
  set y := √(s ^ 2 * (φ + 2) - 1) with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = s ^ 2 * (φ + 2) - 1 := Real.sq_sqrt hrad
  have hyφ : y < φ := by
    have : y ^ 2 < φ ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hφ0.le this
  have hyl : φ - 1 ≤ y := by
    have : (φ - 1) ^ 2 ≤ y ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by linarith) hy0).1 this
  have hE2 : ‖dg 1 (-φ)‖ ^ 2 = φ + 2 := by rw [norm_sq_dg]; nlinarith
  have hW2 : ‖dg 1 (-y)‖ ^ 2 = (s * ‖dg 1 (-φ)‖) ^ 2 := by
    rw [norm_sq_dg, mul_pow, hE2]; nlinarith
  have hs3 : 0 ≤ s := by linarith
  have hW : ‖dg 1 (-y)‖ ≤ s * ‖dg 1 (-φ)‖ :=
    ((pow_left_inj₀ (norm_nonneg _) (mul_nonneg hs3 (norm_nonneg _)) two_ne_zero).mp hW2).le
  have hin : ⟪dg 1 (-y), dg 1 (-φ)⟫ = 1 + φ * y := by rw [inner_dg]; ring
  have hpos : ⟪dg 1 (-y), dg 1 (-φ)⟫ < s * ‖dg 1 (-φ)‖ ^ 2 := by
    rw [hin, hE2]
    have h1 : (s * (φ + 2)) ^ 2 - (1 + φ * y) ^ 2 = (φ - y) ^ 2 := by
      have e : (s * (φ + 2)) ^ 2 = (1 + y ^ 2) * (1 + φ ^ 2) := by
        rw [hy2, hφ3]; ring
      rw [e]
      ring
    have h2 : 0 < (φ - y) ^ 2 := by
      have : 0 < φ - y := by linarith
      positivity
    have h3 : (1 + φ * y) ^ 2 < (s * (φ + 2)) ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
  obtain ⟨L, 𝒜, hμL, hLam, hspec, hreal⟩ := exists_realization hμ.le hlam hW hpos
  have hX : dg 1 0 - dg 0 φ = dg 1 (-φ) := by rw [dg_sub]; simp
  have hgrad : gradStep 𝒜 (𝒜 (dg 0 φ)) lam (dg 1 0) = dg 1 (φ - y) := by
    have e1 : 𝒜 (dg 1 0) - 𝒜 (dg 0 φ) = 𝒜 (dg 1 (-φ)) := by rw [← map_sub, hX]
    have e2 : dg 1 0 = dg 1 (-φ) + dg 0 φ := by rw [← hX]; abel
    have e3 : dg 1 (φ - y) = dg 1 (-y) + dg 0 φ := by rw [dg_add]; simp [neg_add_eq_sub]
    rw [gradStep, e1, ← hreal] at *
    rw [e3]
    conv_lhs => rw [e2]
    abel
  have hc0 : 0 ≤ φ - y := by linarith
  have hc1 : φ - y ≤ 1 := by linarith
  refine ⟨L, 𝒜, dg 1 0, dg 0 φ, hμL, hLam, rank_dg_left 1, rank_dg_right φ, ?_,
    fun _ Z _ => hspec Z, ⟨rank_dg_left 1, ?_⟩, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [dg] at this
  · rw [hgrad]
    exact dg_best hc0 hc1
  · intro hgt T hT
    have hs4 : φ - 1 < s := by nlinarith
    have hc2 : φ - y < 1 := by
      have h1 : (φ - 1) ^ 2 < y ^ 2 := by nlinarith
      have h2 : φ - 1 < y := lt_of_pow_lt_pow_left₀ 2 hy0 h1
      linarith
    have h3 := hT.best
    rw [hgrad] at h3
    exact dg_best_unique hc0 hc2 hT.rank_le h3

/-- **`1/φ` is exactly the RIP threshold of unit-step SVP.**  By `tendsto_svp`, every SVP trajectory
converges under `δ_{3r} < 1/φ`.  Conversely, for every `δ ∈ [1/φ, 1)` there is an operator with
RIP constant `δ` on *all* of `ℝ^{2 × 2}`, a rank-one solution `Xs` and a rank-one `X ≠ Xs` that is
a fixed point of SVP with `r = 1`; for `δ > 1/φ` this does not depend on tie-breaking. The example
is not compressive (`𝒜` is invertible); `r = 1` is the only rank covered. -/
theorem exists_stall_of_rip {δ : ℝ} (h1 : φ⁻¹ ≤ δ) (h2 : δ < 1) :
    ∃ (𝒜 : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      (X Xs : Matrix (Fin 2) (Fin 2) ℝ), X.rank ≤ 1 ∧ Xs.rank ≤ 1 ∧ X ≠ Xs ∧
      (∀ s, HasRIP 𝒜 s δ) ∧ IsSVPStep 𝒜 (𝒜 Xs) 1 1 X X ∧
      (φ⁻¹ < δ → ∀ T, IsSVPStep 𝒜 (𝒜 Xs) 1 1 X T → T = X) := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hin : (1 : ℝ) ≤ φ * δ := by
    have := mul_le_mul_of_nonneg_left h1 hφ0.le
    rwa [mul_inv_cancel₀ hφ0.ne'] at this
  have e : φ * (1 - 1 * (1 - δ)) = φ * δ := by ring_nf
  obtain ⟨L, 𝒜, X, Xs, -, hL, hX, hXs, hne, hspec, hstep, huniq⟩ :=
    exists_stall (μ := 1 - δ) (lam := 1) (by linarith) one_pos (by rw [e]; exact hin)
  have hL' : L ≤ 1 + δ := by linarith
  refine ⟨𝒜, X, Xs, hX, hXs, hne, fun s Z hZ => ⟨(hspec s Z hZ).1, ?_⟩, hstep, fun hgt => ?_⟩
  · exact (hspec s Z hZ).2.trans (mul_le_mul_of_nonneg_right hL' (sq_nonneg _))
  · refine huniq ?_
    rw [e]
    have := mul_lt_mul_of_pos_left hgt hφ0
    rwa [mul_inv_cancel₀ hφ0.ne'] at this

/-- **The factor `φ δ` is attained in one step, for every `δ ∈ (0, 1)`.**  So the constant in
`norm_svpStep_sub_le_of_rip` cannot be lowered at any value of the RIP constant, which is stronger
than the sharpness of Theorem E it is built on: the extremal configuration of that
theorem is reached by an actual gradient step of an operator with RIP constant `δ`. -/
theorem exists_svpStep_eq {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    ∃ (𝒜 : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      (X Xs T : Matrix (Fin 2) (Fin 2) ℝ), X.rank ≤ 1 ∧ Xs.rank ≤ 1 ∧ X ≠ Xs ∧
      (∀ s, HasRIP 𝒜 s δ) ∧ IsSVPStep 𝒜 (𝒜 Xs) 1 1 X T ∧ ‖T - Xs‖ = φ * δ * ‖X - Xs‖ := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ1 := gold_gt
  have hφ2 := gold_lt
  have hφ3 := gold_sq
  set w := √(3 - φ) with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 (by linarith)
  have hw2 : w ^ 2 = 3 - φ := Real.sq_sqrt (by linarith)
  set R := w / δ with hR
  have hR0 : 0 < R := by positivity
  have hδR : δ * R = w := mul_div_cancel₀ _ h0.ne'
  have hEn : ‖dg 0 R‖ = R := by
    refine (pow_left_inj₀ (norm_nonneg _) hR0.le two_ne_zero).mp ?_
    rw [norm_sq_dg]
    ring
  have hWn : ‖dg 1 (1 - φ)‖ = w := by
    refine (pow_left_inj₀ (norm_nonneg _) hw0.le two_ne_zero).mp ?_
    rw [norm_sq_dg, hw2]
    nlinarith
  have es : (1 : ℝ) - 1 * (1 - δ) = δ := by ring
  have hW : ‖dg 1 (1 - φ)‖ ≤ (1 - 1 * (1 - δ)) * ‖dg 0 R‖ := by
    rw [es, hEn, hWn, hδR]
  have hpos : ⟪dg 1 (1 - φ), dg 0 R⟫ < (1 - 1 * (1 - δ)) * ‖dg 0 R‖ ^ 2 := by
    rw [es, inner_dg, hEn]
    have h2 : (1 - φ) * R < 0 := mul_neg_of_neg_of_pos (by linarith) hR0
    have h3 : 0 < δ * R ^ 2 := by positivity
    linarith
  obtain ⟨L, 𝒜, -, hL, hspec, hreal⟩ := exists_realization (μ := 1 - δ) (lam := 1)
    (by linarith) one_pos hW hpos
  have hX : dg 0 (φ + R) - dg 0 φ = dg 0 R := by rw [dg_sub]; simp
  have hgrad : gradStep 𝒜 (𝒜 (dg 0 φ)) 1 (dg 0 (φ + R)) = dg 1 1 := by
    have e1 : 𝒜 (dg 0 (φ + R)) - 𝒜 (dg 0 φ) = 𝒜 (dg 0 R) := by rw [← map_sub, hX]
    have e2 : dg 0 (φ + R) = dg 0 R + dg 0 φ := by rw [dg_add]; simp [add_comm]
    have e3 : dg 1 1 = dg 1 (1 - φ) + dg 0 φ := by rw [dg_add]; simp
    rw [gradStep, e1, e3, ← hreal]
    conv_lhs => rw [e2]
    abel
  have hL' : L ≤ 1 + δ := by linarith
  refine ⟨𝒜, dg 0 (φ + R), dg 0 φ, dg 1 0, rank_dg_right _, rank_dg_right _, ?_,
    fun s Z _ => ⟨(hspec Z).1, (hspec Z).2.trans (mul_le_mul_of_nonneg_right hL' (sq_nonneg _))⟩,
    ⟨rank_dg_left 1, ?_⟩, ?_⟩
  · intro h
    have := congrFun (congrFun h 1) 1
    simp only [dg, Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    linarith
  · rw [hgrad]
    exact dg_best zero_le_one le_rfl
  · rw [hX, hEn, mul_assoc, hδR]
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [dg_sub, norm_sq_dg, mul_pow, hw2, hφ3]
    nlinarith

/-- **The condition number `φ³` cannot be relaxed at the best constant step.**  If `L ≥ φ³ μ`, some
sensing operator with spectrum in `[μ, L]` has a non-solution fixed point of SVP with the step
`λ = 2/(μ + L)`, the step minimising `ρ(λ)`.  With `norm_svpStep_sub_le`: at this step, contraction
holds for all operators with spectrum in `[μ, L]` if and only if `L < φ³ μ`. -/
theorem exists_stall_of_condition {L : ℝ} (hμ : 0 < μ) (h : φ ^ 3 * μ ≤ L) :
    ∃ (𝒜 : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      (X Xs : Matrix (Fin 2) (Fin 2) ℝ), X.rank ≤ 1 ∧ Xs.rank ≤ 1 ∧ X ≠ Xs ∧
      (∀ s, RestrictedSpectrum 𝒜 s μ L) ∧ IsSVPStep 𝒜 (𝒜 Xs) 1 (2 / (μ + L)) X X := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ1 := gold_gt
  have hφ3 := gold_sq
  have hcube : φ ^ 3 = 2 * φ + 1 := by linear_combination (φ + 1) * hφ3
  have hL : 0 < L := by
    have : 0 < φ ^ 3 * μ := by positivity
    linarith
  have hsum : 0 < μ + L := by linarith
  have hlam : 0 < 2 / (μ + L) := by positivity
  have hgold : 1 ≤ φ * (1 - 2 / (μ + L) * μ) := by
    have e : 1 - 2 / (μ + L) * μ = (L - μ) / (μ + L) := by
      field_simp
      ring
    rw [e, ← mul_div_assoc, one_le_div hsum]
    have h1 : (φ - 1) * (φ ^ 3 * μ) = (φ + 1) * μ := by
      rw [hcube]
      linear_combination (2 * μ) * hφ3
    have h2 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ φ - 1)
    nlinarith
  obtain ⟨L', 𝒜, X, Xs, -, hL', hX, hXs, hne, hspec, hstep, -⟩ := exists_stall hμ hlam hgold
  have hLL : L' ≤ L := by
    have h1 : μ + L' ≤ 2 / (2 / (μ + L)) := by
      rw [le_div_iff₀ hlam, mul_comm]
      exact hL'
    have h2 : 2 / (2 / (μ + L)) = μ + L := by
      field_simp
    linarith
  exact ⟨𝒜, X, Xs, hX, hXs, hne, fun s Z hZ => ⟨(hspec s Z hZ).1,
    (hspec s Z hZ).2.trans (mul_le_mul_of_nonneg_right hLL (sq_nonneg _))⟩, hstep⟩

end Sharpness

/-! ### Block sparsity: vectors, blocks, rows -/

section Block

variable {β : Type*} [Fintype β] {H : β → Type*} [∀ b, NormedAddCommGroup (H b)]
  [∀ b, InnerProductSpace ℝ (H b)]

open Classical in
/-- The blocks on which `x ∈ ⨁₂ H b` does not vanish. -/
noncomputable def blockSupport (x : PiLp 2 H) : Finset β := Finset.univ.filter fun b => x b ≠ 0

variable (H) in
/-- Vectors with at most `k` nonzero blocks.  For `H b = ℝ` these are the `k`-sparse vectors, for
`H b = EuclideanSpace ℝ (block b)` the block-sparse vectors; see `rowSparse` for rows. -/
def blockSparse (k : ℕ) : Set (PiLp 2 H) := {x | (blockSupport x).card ≤ k}

omit [∀ b, InnerProductSpace ℝ (H b)] in
lemma mem_blockSupport {x : PiLp 2 H} {b : β} : b ∈ blockSupport x ↔ x b ≠ 0 := by
  simp [blockSupport]

open Classical in
/-- The coordinate projector on the blocks in `S`, as a linear map. -/
noncomputable def maskₗ (S : Finset β) : PiLp 2 H →ₗ[ℝ] PiLp 2 H where
  toFun x := WithLp.toLp 2 fun b => if b ∈ S then x b else 0
  map_add' x y := by
    ext b
    by_cases h : b ∈ S <;> simp [h]
  map_smul' c x := by
    ext b
    by_cases h : b ∈ S <;> simp [h]

omit [Fintype β] in
open Classical in
lemma maskₗ_apply (S : Finset β) (x : PiLp 2 H) (b : β) :
    maskₗ S x b = if b ∈ S then x b else 0 := rfl

open Classical in
lemma norm_sq_maskₗ_le (S : Finset β) (x : PiLp 2 H) : ‖maskₗ S x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [maskₗ_apply]
  by_cases h : b ∈ S <;> simp [h]

/-- The coordinate projector on the blocks in `S`. -/
noncomputable def mask (S : Finset β) : PiLp 2 H →L[ℝ] PiLp 2 H :=
  (maskₗ S).mkContinuous 1 fun x => by
    rw [one_mul]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (norm_sq_maskₗ_le S x)

open Classical in
lemma mask_apply (S : Finset β) (x : PiLp 2 H) (b : β) :
    mask S x b = if b ∈ S then x b else 0 := rfl

lemma isOrthProj_mask (S : Finset β) : IsOrthProj (mask S : PiLp 2 H →L[ℝ] PiLp 2 H) where
  idem x := by
    ext b
    by_cases h : b ∈ S <;> simp [mask_apply, h]
  symm x y := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : b ∈ S <;> simp [mask_apply, h]

lemma mask_eq_self {S : Finset β} {x : PiLp 2 H} (h : blockSupport x ⊆ S) : mask S x = x := by
  ext b
  by_cases hb : b ∈ S
  · simp [mask_apply, hb]
  · have : x b = 0 := by
      by_contra hne
      exact hb (h (mem_blockSupport.2 hne))
    simp [mask_apply, hb, this]

lemma blockSupport_mask_subset_left (S : Finset β) (x : PiLp 2 H) :
    blockSupport (mask S x) ⊆ S := by
  intro b hb
  have h := mem_blockSupport.1 hb
  rw [mask_apply] at h
  by_contra hS
  simp [hS] at h

lemma blockSupport_mask_subset_right (S : Finset β) (x : PiLp 2 H) :
    blockSupport (mask S x) ⊆ blockSupport x := by
  intro b hb
  have h := mem_blockSupport.1 hb
  rw [mask_apply] at h
  refine mem_blockSupport.2 fun h0 => h ?_
  simp [h0]

lemma blockSupport_shrink_subset (S : Finset β) (t : ℝ) (x : PiLp 2 H) :
    blockSupport (shrink (mask S) t x) ⊆ blockSupport x := by
  intro b hb
  refine mem_blockSupport.2 fun h0 => mem_blockSupport.1 hb ?_
  simp only [shrink, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, mask_apply, h0]
  simp

variable {k : ℕ} {X T : PiLp 2 H}

/-- **Golden inequality for block-sparse vectors** (`ρ = 1` in Shen–Li, JMLR 2018, for `H b = ℝ`).
If `T` is a best `k`-block approximation of `X`, then for every `A` and every `k`-block-sparse `B`,
`‖T - A‖ ≤ ‖A - B‖ + φ ‖X - A‖`. -/
theorem norm_sub_le_add_gold_mul_blockSparse (hT : ∀ Z ∈ blockSparse H k, ‖X - T‖ ≤ ‖X - Z‖)
    (hTk : T ∈ blockSparse H k) (A : PiLp 2 H) {B : PiLp 2 H} (hB : B ∈ blockSparse H k) :
    ‖T - A‖ ≤ ‖A - B‖ + φ * ‖X - A‖ := by
  refine norm_sub_le_add_gold_mul (𝓢 := blockSparse H k) (Q := mask (blockSupport T))
    (isOrthProj_mask _) hT (mask_eq_self subset_rfl) ?_ (fun t _ => ?_) A
  · exact (Finset.card_le_card (blockSupport_mask_subset_left _ X)).trans hTk
  · exact (Finset.card_le_card (blockSupport_shrink_subset _ t B)).trans hB

/-- The Shen–Li bound `‖T - A‖ ≤ φ ‖X - A‖` for `k`-block-sparse `A`. -/
theorem norm_sub_le_gold_mul_blockSparse (hT : ∀ Z ∈ blockSparse H k, ‖X - T‖ ≤ ‖X - Z‖)
    (hTk : T ∈ blockSparse H k) {A : PiLp 2 H} (hA : A ∈ blockSparse H k) :
    ‖T - A‖ ≤ φ * ‖X - A‖ := by
  simpa using norm_sub_le_add_gold_mul_blockSparse hT hTk A hA

/-- Hard thresholding: best `k`-block approximations exist. -/
theorem exists_best_blockSparse (X : PiLp 2 H) (k : ℕ) :
    ∃ T ∈ blockSparse H k, ∀ Z ∈ blockSparse H k, ‖X - T‖ ≤ ‖X - Z‖ := by
  classical
  set a : β → ℝ := fun b => ‖X b‖ ^ 2 with ha
  have ha0 : ∀ b, 0 ≤ a b := fun b => sq_nonneg _
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset.filter fun S : Finset β => S.card ≤ k) (fun S => ∑ b ∈ S, a b)
    ⟨∅, by simp⟩
  have hSk : S.card ≤ k := (Finset.mem_filter.1 hS).2
  have hdist : ∀ (S' : Finset β) (Z : PiLp 2 H), blockSupport Z ⊆ S' →
      ∑ b ∈ Finset.univ \ S', a b ≤ ‖X - Z‖ ^ 2 := by
    intro S' Z hZ
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ b ∈ Finset.univ \ S', a b ≤ ∑ b ∈ Finset.univ \ S', ‖(X - Z) b‖ ^ 2 := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hbS : b ∉ S' := (Finset.mem_sdiff.1 hb).2
          have h0 : Z b = 0 := by
            by_contra hne
            exact hbS (hZ (mem_blockSupport.2 hne))
          simp [ha, h0]
      _ ≤ ∑ b, ‖(X - Z) b‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
  have hT : ‖X - mask S X‖ ^ 2 = ∑ b ∈ Finset.univ \ S, a b := by
    rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_sdiff (Finset.subset_univ S)]
    have h1 : ∑ b ∈ S, ‖(X - mask S X) b‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      simp [mask_apply, hb]
    rw [h1, add_zero]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbS : b ∉ S := (Finset.mem_sdiff.1 hb).2
    simp [mask_apply, hbS, ha]
  refine ⟨mask S X, ?_, fun Z hZ => ?_⟩
  · exact (Finset.card_le_card (blockSupport_mask_subset_left _ X)).trans hSk
  · have h1 := hdist (blockSupport Z) Z subset_rfl
    have h2 := hmax (blockSupport Z) (Finset.mem_filter.2 ⟨by simp, hZ⟩)
    have h3 := Finset.sum_sdiff (Finset.subset_univ S) (f := a)
    have h4 := Finset.sum_sdiff (Finset.subset_univ (blockSupport Z)) (f := a)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [hT]
    linarith

end Block

/-- The constant in `norm_sub_le_gold_mul_blockSparse` is attained by `1`-sparse vectors in `ℝ²`:
`X = (1, 1)`, `A = (0, φ)`, `T = (1, 0)`. -/
theorem exists_eq_gold_sparse :
    ∃ X A T : PiLp 2 (fun _ : Fin 2 => ℝ),
      (∀ Z ∈ blockSparse (fun _ : Fin 2 => ℝ) 1, ‖X - T‖ ≤ ‖X - Z‖) ∧
      T ∈ blockSparse (fun _ : Fin 2 => ℝ) 1 ∧ A ∈ blockSparse (fun _ : Fin 2 => ℝ) 1 ∧ X ≠ A ∧
      ‖T - A‖ = φ * ‖X - A‖ := by
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  have hφ1 := gold_gt
  have hφ3 := gold_sq
  have hsq : ∀ x : PiLp 2 (fun _ : Fin 2 => ℝ), ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    intro x
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  refine ⟨WithLp.toLp 2 ![1, 1], WithLp.toLp 2 ![0, φ], WithLp.toLp 2 ![1, 0], ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ
    have hcard : ¬ (Z 0 ≠ 0 ∧ Z 1 ≠ 0) := by
      rintro ⟨h0, h1⟩
      have hsub : ({0, 1} : Finset (Fin 2)) ⊆ blockSupport Z := by
        intro b hb
        fin_cases b
        · exact mem_blockSupport.2 h0
        · exact mem_blockSupport.2 h1
      have := Finset.card_le_card hsub
      have h3 : (blockSupport Z).card ≤ 1 := hZ
      simp at this
      omega
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [hsq, hsq]
    simp only [PiLp.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self]
    by_cases h0 : Z 0 = 0
    · rw [h0]; nlinarith [sq_nonneg (1 - Z 1)]
    · have h1 : Z 1 = 0 := by
        by_contra h1
        exact hcard ⟨h0, h1⟩
      rw [h1]; nlinarith [sq_nonneg (1 - Z 0)]
  · have : blockSupport (WithLp.toLp 2 ![1, 0] : PiLp 2 (fun _ : Fin 2 => ℝ)) ⊆ {0} := by
      intro b hb
      have := mem_blockSupport.1 hb
      fin_cases b
      · simp
      · simp at this
    exact (Finset.card_le_card this).trans (by simp)
  · have : blockSupport (WithLp.toLp 2 ![0, φ] : PiLp 2 (fun _ : Fin 2 => ℝ)) ⊆ {1} := by
      intro b hb
      have := mem_blockSupport.1 hb
      fin_cases b
      · simp at this
      · simp
    exact (Finset.card_le_card this).trans (by simp)
  · intro h
    have := congrArg (fun x : PiLp 2 (fun _ : Fin 2 => ℝ) => x 0) h
    simp at this
  · refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, hsq, hsq]
    simp only [PiLp.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    have h3 : (1 - φ) ^ 2 = 2 - φ := by nlinarith
    rw [h3, hφ3]
    nlinarith

/-! ### Iterative hard thresholding for block-sparse vectors -/

section BlockIHT

variable {β : Type*} [Fintype β] {H : β → Type*} [∀ b, NormedAddCommGroup (H b)]
  [∀ b, InnerProductSpace ℝ (H b)] [∀ b, FiniteDimensional ℝ (H b)] {G : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {𝒜 : PiLp 2 H →ₗ[ℝ] G} {k : ℕ} {μ L lam : ℝ} {b : G} {X Xs T : PiLp 2 H}

/-- **Block IHT with the golden ratio.**  If `𝒜` has spectrum in `[μ, L]` on `3 k`-block-sparse
vectors, `X`, `Xs` are `k`-block-sparse and `T` is a best `k`-block approximation of
`X - λ 𝒜*(𝒜 X - b)`, then `‖T - Xs‖ ≤ φ (ρ(λ) ‖X - Xs‖ + λ √L ‖b - 𝒜 Xs‖)`.  For `H b = ℝ` and
`λ = 1` this is the vector IHT condition `δ_{3k} < 1/φ`. -/
theorem norm_blockIHT_sub_le
    (h : ∀ Z ∈ blockSparse H (3 * k), μ * ‖Z‖ ^ 2 ≤ ‖𝒜 Z‖ ^ 2 ∧ ‖𝒜 Z‖ ^ 2 ≤ L * ‖Z‖ ^ 2)
    (hL : 0 ≤ L) (hlam : 0 ≤ lam) (hX : X ∈ blockSparse H k) (hXs : Xs ∈ blockSparse H k)
    (hTk : T ∈ blockSparse H k)
    (hT : ∀ Z ∈ blockSparse H k, ‖(X - lam • LinearMap.adjoint 𝒜 (𝒜 X - b)) - T‖ ≤
      ‖(X - lam • LinearMap.adjoint 𝒜 (𝒜 X - b)) - Z‖) :
    ‖T - Xs‖ ≤ φ * (rate μ L lam * ‖X - Xs‖ + lam * √L * ‖b - 𝒜 Xs‖) := by
  classical
  set S := blockSupport X ∪ blockSupport Xs ∪ blockSupport T with hS
  have hX' : (blockSupport X).card ≤ k := hX
  have hXs' : (blockSupport Xs).card ≤ k := hXs
  have hT' : (blockSupport T).card ≤ k := hTk
  have hSc : S.card ≤ 3 * k := by
    have h1 : S.card ≤ (blockSupport X ∪ blockSupport Xs).card + (blockSupport T).card :=
      Finset.card_union_le _ _
    have h2 := Finset.card_union_le (blockSupport X) (blockSupport Xs)
    omega
  have hsub1 : blockSupport X ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hsub2 : blockSupport Xs ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hsub3 : blockSupport T ⊆ S := Finset.subset_union_right
  refine norm_step_sub_le (P := mask S) (Q := mask (blockSupport T)) (𝓢 := blockSparse H k)
    (isOrthProj_mask _) (mask_eq_self hsub1) (mask_eq_self hsub2) (mask_eq_self hsub3)
    (fun Z hZ => ?_) (fun Z hZ => h Z ?_) hlam hL hT (isOrthProj_mask _) (mask_eq_self subset_rfl)
    ?_ (fun t _ => ?_)
  · exact (Finset.card_le_card (blockSupport_mask_subset_right _ Z)).trans hZ
  · change (blockSupport Z).card ≤ 3 * k
    rw [← hZ]
    exact (Finset.card_le_card (blockSupport_mask_subset_left _ Z)).trans hSc
  · exact (Finset.card_le_card (blockSupport_mask_subset_left _ _)).trans hT'
  · exact (Finset.card_le_card (blockSupport_shrink_subset _ t Xs)).trans hXs

end BlockIHT

/-! ### Row-sparse matrices -/

section Rows

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A matrix as the family of its rows: an isometry onto `⨁₂_{i : m} ℝⁿ`. -/
noncomputable def toRows (Z : Matrix m n ℝ) : PiLp 2 (fun _ : m => EuclideanSpace ℝ n) :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 (Z i)

lemma norm_toRows (Z : Matrix m n ℝ) : ‖toRows Z‖ = ‖Z‖ := rfl

omit [Fintype m] [Fintype n] in
lemma toRows_sub (Y Z : Matrix m n ℝ) : toRows (Y - Z) = toRows Y - toRows Z := rfl

omit [Fintype m] [Fintype n] in
lemma toRows_surjective : Function.Surjective (toRows (m := m) (n := n)) :=
  fun x => ⟨Matrix.of fun i j => x i j, rfl⟩

variable (m n) in
/-- Matrices with at most `k` nonzero rows. -/
def rowSparse (k : ℕ) : Set (Matrix m n ℝ) :=
  {Z | toRows Z ∈ blockSparse (fun _ : m => EuclideanSpace ℝ n) k}

/-- **Golden inequality for row-sparse matrices**: if `T` is a best approximation of
`X` with at most `k` nonzero rows, then `‖T - A‖ ≤ ‖A - B‖ + φ ‖X - A‖` for every `A` and every `B`
with at most `k` nonzero rows; in particular `‖T - A‖ ≤ φ ‖X - A‖` for row-sparse `A`. -/
theorem norm_sub_le_add_gold_mul_rowSparse {k : ℕ} {X T : Matrix m n ℝ}
    (hT : ∀ Z ∈ rowSparse m n k, ‖X - T‖ ≤ ‖X - Z‖) (hTk : T ∈ rowSparse m n k)
    (A : Matrix m n ℝ) {B : Matrix m n ℝ} (hB : B ∈ rowSparse m n k) :
    ‖T - A‖ ≤ ‖A - B‖ + φ * ‖X - A‖ := by
  have hT' : ∀ Z' ∈ blockSparse (fun _ : m => EuclideanSpace ℝ n) k,
      ‖toRows X - toRows T‖ ≤ ‖toRows X - Z'‖ := by
    intro Z' hZ'
    obtain ⟨Z, rfl⟩ := toRows_surjective Z'
    rw [← toRows_sub, ← toRows_sub, norm_toRows, norm_toRows]
    exact hT Z hZ'
  have h := norm_sub_le_add_gold_mul_blockSparse hT' hTk (toRows A) hB
  rwa [← toRows_sub, ← toRows_sub, ← toRows_sub, norm_toRows, norm_toRows, norm_toRows] at h

/-- The constant for row-sparse matrices is attained: `A = diag(0, φ)` and `T = diag(1, 0)` have one
nonzero row, and `T` is a best approximation of `X = I₂` among such matrices. -/
theorem exists_eq_gold_rowSparse :
    ∃ X A T : Matrix (Fin 2) (Fin 2) ℝ, (∀ Z ∈ rowSparse (Fin 2) (Fin 2) 1, ‖X - T‖ ≤ ‖X - Z‖) ∧
      T ∈ rowSparse (Fin 2) (Fin 2) 1 ∧ A ∈ rowSparse (Fin 2) (Fin 2) 1 ∧ X ≠ A ∧
      ‖T - A‖ = φ * ‖X - A‖ := by
  have hzero : ∀ (Z : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2), Z i = 0 →
      blockSupport (toRows Z) ⊆ {1 - i} := by
    intro Z i hi b hb
    have h := mem_blockSupport.1 hb
    have hbi : b ≠ i := by
      rintro rfl
      apply h
      ext j
      exact congrFun hi j
    fin_cases b <;> fin_cases i <;> simp_all
  have hrow : ∀ (Z : Matrix (Fin 2) (Fin 2) ℝ), Z ∈ rowSparse (Fin 2) (Fin 2) 1 →
      Z 0 = 0 ∨ Z 1 = 0 := by
    intro Z hZ
    by_contra hne
    rw [not_or] at hne
    have hsub : ({0, 1} : Finset (Fin 2)) ⊆ blockSupport (toRows Z) := by
      intro b hb
      have hnz : ∀ i, Z i ≠ 0 → toRows Z i ≠ 0 := by
        intro i hi h0
        apply hi
        funext j
        exact congrFun (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => (v : Fin 2 → ℝ)) h0) j
      fin_cases b
      · exact mem_blockSupport.2 (hnz 0 hne.1)
      · exact mem_blockSupport.2 (hnz 1 hne.2)
    have h1 := Finset.card_le_card hsub
    have h2 : (blockSupport (toRows Z)).card ≤ 1 := hZ
    simp at h1
    omega
  have hmem : ∀ (Z : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2), Z i = 0 →
      Z ∈ rowSparse (Fin 2) (Fin 2) 1 := fun Z i hi =>
    (Finset.card_le_card (hzero Z i hi)).trans (by simp)
  refine ⟨dg 1 1, dg 0 φ, dg 1 0, fun Z hZ => ?_, hmem _ 1 ?_, hmem _ 0 ?_, ?_, dg_extremal⟩
  · have hn : ‖dg 1 1 - dg 1 0‖ ^ 2 = 1 := by
      rw [dg_sub, norm_sq_dg]
      ring
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [hn, Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two, Matrix.sub_apply, dg, Matrix.diagonal_apply_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.diagonal_apply_ne, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_sub]
    rcases hrow Z hZ with h0 | h0
    · have h1 : Z 0 0 = 0 := congrFun h0 0
      have h2 : Z 0 1 = 0 := congrFun h0 1
      rw [h1, h2]
      nlinarith [sq_nonneg (Z 1 0), sq_nonneg (1 - Z 1 1)]
    · have h1 : Z 1 0 = 0 := congrFun h0 0
      have h2 : Z 1 1 = 0 := congrFun h0 1
      rw [h1, h2]
      nlinarith [sq_nonneg (Z 0 1), sq_nonneg (1 - Z 0 0)]
  · funext j
    fin_cases j <;> simp [dg]
  · funext j
    fin_cases j <;> simp [dg]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [dg] at this

end Rows

end LeanDLRA.Novel.GoldenThresholding
