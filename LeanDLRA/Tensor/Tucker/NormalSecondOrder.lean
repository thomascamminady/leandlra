import LeanDLRA.Tensor.Tucker.ProjectorLipschitz
import LeanDLRA.Tensor.Tucker.BUGStep
import LeanDLRA.DLRA.QuasiOptimalityDefect

/-!
# The normal component of a nearby Tucker tensor, with a constant independent of the order

Let `Y = C' ×ₖ U'ₖ` be a Tucker tensor with `d` modes and tangent projector `P(Y)`
(`tuckerTangentProj` with the core projector `1`), let `ρ` be a lower bound of the smallest
nonzero singular values of the `d` matricizations of `Y`, and let `X = C ×ₖ Uₖ` be a Tucker tensor
of the same format with `e = ‖X - Y‖ < ρ`. This file shows

  `ρ (ρ - 2 e) ‖X - P(Y) X‖² ≤ e⁴ / 2`,   i.e.   `‖X - P(Y) X‖ ≤ e² / √(2 ρ (ρ - 2 e))`,

so the normal component of `X` at `Y` is of second order in `e` with a constant that does not
depend on the number of modes; to first order the constant is `1/√2`. The bound of
[BachmayrEisenmannUschmajew2025, Prop. 4.9] is `√d e²/ρ` (for all `e`, with `ρ` at the other
point).

## Main results

* `LeanDLRA.sub_mul_sum_sq_le_of_chain`: the inequality for real numbers behind the theorem.
* `LeanDLRA.modePrefix_succ_of_lt` and four lemmas on the prefix products of mode operators.
* `LeanDLRA.sub_mul_norm_sq_sub_modeTangentProj_apply_le`: the abstract form. For the tangent
  projector `P = modeTangentProj P₀ Q₀`, a vector `y` fixed by all `P₀ i`, `Q₀ i` and a vector `z`
  such that in every mode `σ ‖(1 - P₀ i) (1 - Q₀ i) zᵢ‖ ≤ ‖(1 - P₀ i) zᵢ‖ ‖(1 - Q₀ i) zᵢ‖` for
  `zᵢ = P₀ 0 ⋯ P₀ (i - 1) z`: `(σ² - ‖z - y‖²) ‖z - P z‖² ≤ ‖z - y‖⁴ / 2`.
* `LeanDLRA.norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul`: for a matrix `M` of rank at most
  `q` with `0 < ρ ≤ σ_{q-1}(M)`: `‖A M B‖ ≤ ρ⁻¹ ‖A M‖ ‖M B‖`.
* `LeanDLRA.Tensor.mul_norm_one_sub_modeProj_sub_coRange_le`: the same for a tensor and the
  mode-`k` normal projector `(1 - P_U) (1 - Q_W)`.
* `LeanDLRA.Tensor.mul_norm_sq_sub_tuckerTangentProj_tucker_le`,
  `LeanDLRA.Tensor.norm_sub_tuckerTangentProj_tucker_le`: the two forms of the bound above.

## Implementation notes

The normal component is the orthogonal sum of the `d` parts
`tᵢ = (1 - P₀ i) (1 - Q₀ i) zᵢ`, `zᵢ = P₀ 0 ⋯ P₀ (i - 1) z`
(`norm_sq_sub_modeTangentProj_apply_eq`). The matricization `M` of `zᵢ` has rank at most `rᵢ` and
`σ_{rᵢ}(M) ≥ ρ - e`, and `tᵢ = (1 - Q) M (1 - P) = ((1 - Q) M) M⁺ (M (1 - P))` in the
matricization, so `(ρ - e) ‖tᵢ‖ ≤ aᵢ bᵢ` with `aᵢ = ‖(1 - P₀ i) zᵢ‖` and
`bᵢ = ‖(1 - Q₀ i) zᵢ‖`. The numbers `aᵢ²` are the terms of the telescoping sum
`‖z - y‖² = ∑ᵢ aᵢ² + ‖P₀ 0 ⋯ P₀ (d - 1) (z - y)‖²`, and
`bᵢ² ≤ ‖tᵢ‖² + ‖P₀ 0 ⋯ P₀ i (z - y)‖²`: the part of `z - y` that enters `bᵢ` has not been used
by `a₀, …, aᵢ`. With `cₖ = ‖P₀ 0 ⋯ P₀ (k - 1) (z - y)‖²` this gives
`∑ᵢ aᵢ² bᵢ² ≤ e² ∑ᵢ ‖tᵢ‖² + ∑ᵢ (cᵢ - cᵢ₊₁) cᵢ₊₁` and `(cᵢ - cᵢ₊₁) cᵢ₊₁ ≤ (cᵢ² - cᵢ₊₁²)/2`.
Bounding every `bᵢ` by `e` and every `aᵢ` by `e` gives the factor `√d` instead.

## References

* [BachmayrEisenmannUschmajew2025, Prop. 4.9]
-/

open Matrix Finset
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### The inequality for real numbers -/

/-- **The chain inequality.** Let `c 0 ≥ c 1 ≥ ⋯ ≥ 0` with `c k ≤ e²`, and for `i < d` let
`aᵢ² = c i - c (i + 1)`, `bᵢ² ≤ tᵢ² + c (i + 1)` and `σ tᵢ ≤ aᵢ bᵢ`. Then
`(σ² - e²) ∑ᵢ tᵢ² ≤ e⁴ / 2`. -/
theorem sub_mul_sum_sq_le_of_chain {d : ℕ} {a b t : Fin d → ℝ} {c : ℕ → ℝ} {e σ : ℝ}
    (hσ : 0 ≤ σ) (ht : ∀ i, 0 ≤ t i) (hc0 : ∀ k, 0 ≤ c k) (hce : ∀ k, c k ≤ e ^ 2)
    (ha : ∀ i : Fin d, a i ^ 2 = c i - c (i + 1))
    (hb : ∀ i : Fin d, b i ^ 2 ≤ t i ^ 2 + c (i + 1))
    (hm : ∀ i, σ * t i ≤ a i * b i) :
    (σ ^ 2 - e ^ 2) * ∑ i, t i ^ 2 ≤ e ^ 4 / 2 := by
  have key : ∀ i : Fin d,
      (σ ^ 2 - e ^ 2) * t i ^ 2 ≤ (c i ^ 2 - c (i + 1) ^ 2) / 2 := fun i => by
    have h1 : (σ * t i) ^ 2 ≤ (a i * b i) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hσ (ht i)) (hm i) 2
    have hd0 : 0 ≤ c i - c (i + 1) := by rw [← ha i]; exact sq_nonneg _
    have h2 : (a i * b i) ^ 2 ≤ (c i - c (i + 1)) * (t i ^ 2 + c (i + 1)) := by
      rw [mul_pow, ha i]
      exact mul_le_mul_of_nonneg_left (hb i) hd0
    have h3 : (c i - c (i + 1)) * t i ^ 2 ≤ e ^ 2 * t i ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hc0 (i + 1), hce i]) (sq_nonneg _)
    nlinarith [sq_nonneg (c i - c (i + 1))]
  have hsum : ∑ i : Fin d, (c i ^ 2 - c (i + 1) ^ 2) = c 0 ^ 2 - c d ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => c i ^ 2 - c (i + 1) ^ 2) d,
      Finset.sum_range_sub']
  have h0 : c 0 ^ 2 ≤ e ^ 4 := by nlinarith [hc0 0, hce 0]
  calc (σ ^ 2 - e ^ 2) * ∑ i, t i ^ 2
      = ∑ i, (σ ^ 2 - e ^ 2) * t i ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin d, (c i ^ 2 - c (i + 1) ^ 2) / 2 := Finset.sum_le_sum fun i _ => key i
    _ = (c 0 ^ 2 - c d ^ 2) / 2 := by rw [← Finset.sum_div, hsum]
    _ ≤ e ^ 4 / 2 := by linarith [sq_nonneg (c d)]

/-- Non-vacuity of `sub_mul_sum_sq_le_of_chain`: one mode, `c = (1, 0, 0, …)`,
`a = b = t = σ = e = 1`; all hypotheses hold and no number is zero. -/
example : ((1 : ℝ) ^ 2 - 1 ^ 2) * ∑ i : Fin 1, (fun _ => (1 : ℝ)) i ^ 2 ≤ 1 ^ 4 / 2 :=
  sub_mul_sum_sq_le_of_chain (a := fun _ => 1) (b := fun _ => 1) (t := fun _ => 1)
    (c := fun k => if k = 0 then 1 else 0) zero_le_one (fun _ => zero_le_one)
    (fun k => by split_ifs <;> norm_num) (fun k => by split_ifs <;> norm_num)
    (fun i => by fin_cases i; simp) (fun i => by fin_cases i; simp) (fun i => by simp)

/-! ### Prefix products of mode operators -/

section Prefix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

/-- The prefix product of the first `k + 1` mode operators is the prefix product of the first
`k` ones times the operator of mode `k`. -/
theorem modePrefix_succ_of_lt (P : Fin d → E →L[ℝ] E) {k : ℕ} (hk : k < d) :
    modePrefix P (k + 1) = modePrefix P k * P ⟨k, hk⟩ := by
  unfold modePrefix
  rw [List.take_add_one, List.prod_append]
  simp [hk]

/-- Beyond the last mode the prefix products do not change. -/
private lemma modePrefix_succ_of_le (P : Fin d → E →L[ℝ] E) {k : ℕ} (hk : d ≤ k) :
    modePrefix P (k + 1) = modePrefix P k := by
  rw [modePrefix_of_le P hk, modePrefix_of_le P (Nat.le_succ_of_le hk)]

/-- A map that commutes with the first `k` mode operators commutes with their product. -/
theorem apply_modePrefix_apply_comm {P : Fin d → E →L[ℝ] E} (S : E →L[ℝ] E) (k : ℕ)
    (h : ∀ j : Fin d, (j : ℕ) < k → ∀ x, S (P j x) = P j (S x)) (x : E) :
    S (modePrefix P k x) = modePrefix P k (S x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have ih' := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    by_cases hk : k < d
    · rw [modePrefix_succ_of_lt P hk]
      change S (modePrefix P k (P ⟨k, hk⟩ x)) = modePrefix P k (P ⟨k, hk⟩ (S x))
      rw [ih', h ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · rw [modePrefix_succ_of_le P (not_lt.1 hk)]
      exact ih' x

/-- A vector fixed by the first `k` mode operators is fixed by their product. -/
theorem modePrefix_apply_eq_self {P : Fin d → E →L[ℝ] E} (k : ℕ) {x : E}
    (h : ∀ j : Fin d, (j : ℕ) < k → P j x = x) : modePrefix P k x = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    by_cases hk : k < d
    · rw [modePrefix_succ_of_lt P hk]
      change modePrefix P k (P ⟨k, hk⟩ x) = x
      rw [h ⟨k, hk⟩ (Nat.lt_succ_self k), ih']
    · rw [modePrefix_succ_of_le P (not_lt.1 hk)]
      exact ih'

/-- A map that absorbs each of the first `k` mode operators absorbs their product. -/
theorem apply_modePrefix_apply_eq {P : Fin d → E →L[ℝ] E} (Q : E →L[ℝ] E) (k : ℕ)
    (h : ∀ j : Fin d, (j : ℕ) < k → ∀ x, Q (P j x) = Q x) (x : E) :
    Q (modePrefix P k x) = Q x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have ih' := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    by_cases hk : k < d
    · rw [modePrefix_succ_of_lt P hk]
      change Q (modePrefix P k (P ⟨k, hk⟩ x)) = Q x
      rw [ih', h ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · rw [modePrefix_succ_of_le P (not_lt.1 hk)]
      exact ih' x

/-- A prefix product of orthogonal projectors does not increase the norm. -/
theorem norm_modePrefix_apply_le_norm {P : Fin d → E →L[ℝ] E} (hP : ∀ i, IsOrthProj (P i))
    (k : ℕ) (x : E) : ‖modePrefix P k x‖ ≤ ‖x‖ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < d
    · rw [modePrefix_succ_of_lt P hk]
      exact (ih _).trans ((hP ⟨k, hk⟩).norm_le x)
    · rw [modePrefix_succ_of_le P (not_lt.1 hk)]
      exact ih x

end Prefix

/-! ### The abstract form -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
  {P₀ Q₀ : Fin d → E →L[ℝ] E}

/-- **The normal component of a nearby vector, abstract form.** Let `P = modeTangentProj P₀ Q₀`
be the tangent projector of mode projectors `P₀ i` and co-range projectors `Q₀ i` (hypotheses of
`modeTangentProj_isOrthProj`), let `y` be fixed by all `P₀ i` and all `Q₀ i`, and let `z` satisfy

  `σ ‖(1 - P₀ i) (zᵢ - Q₀ i zᵢ)‖ ≤ ‖zᵢ - P₀ i zᵢ‖ ‖zᵢ - Q₀ i zᵢ‖`,   `zᵢ = P₀ 0 ⋯ P₀ (i - 1) z`,

for every mode `i`, with a number `σ ≥ 0`. Then `(σ² - ‖z - y‖²) ‖z - P z‖² ≤ ‖z - y‖⁴ / 2`,
for every number `d` of modes. -/
theorem sub_mul_norm_sq_sub_modeTangentProj_apply_le (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) {y z : E}
    (hPy : ∀ i, P₀ i y = y) (hQy : ∀ i, Q₀ i y = y) {σ : ℝ} (hσ : 0 ≤ σ)
    (hm : ∀ i : Fin d, σ * ‖(1 - P₀ i) (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z))‖ ≤
      ‖modePrefix P₀ i z - P₀ i (modePrefix P₀ i z)‖ *
        ‖modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z)‖) :
    (σ ^ 2 - ‖z - y‖ ^ 2) * ‖z - modeTangentProj P₀ Q₀ z‖ ^ 2 ≤ ‖z - y‖ ^ 4 / 2 := by
  have hQP : ∀ i j, j ≠ i → ∀ x, Q₀ i (P₀ j x) = Q₀ i x := fun i j hj x => by
    refine ext_inner_right ℝ fun w => ?_
    rw [(hQ₀ i).symm, (hP₀ j).symm, hQsub i j hj, (hQ₀ i).symm]
  have hne : ∀ {i j : Fin d}, (j : ℕ) < (i : ℕ) → j ≠ i := fun h h' => by
    rw [h'] at h
    exact lt_irrefl _ h
  have hRy : ∀ k, modePrefix P₀ k y = y := fun k =>
    modePrefix_apply_eq_self k fun j _ => hPy j
  have hRP : ∀ (i : Fin d) (k : ℕ) x, P₀ i (modePrefix P₀ k x) = modePrefix P₀ k (P₀ i x) :=
    fun i k x => apply_modePrefix_apply_comm (P₀ i) k (fun j _ x => hc₀₀ i j x) x
  have hRQ : ∀ (i : Fin d) x, modePrefix P₀ i (Q₀ i x) = Q₀ i x := fun i x =>
    modePrefix_apply_eq_self i fun j hj => hQsub i j (hne hj) x
  have hQR : ∀ (i : Fin d) x, Q₀ i (modePrefix P₀ i x) = Q₀ i x := fun i x =>
    apply_modePrefix_apply_eq (Q₀ i) i (fun j hj x => hQP i j (hne hj) x) x
  have hsucc : ∀ (i : Fin d) x, modePrefix P₀ ((i : ℕ) + 1) x = P₀ i (modePrefix P₀ i x) :=
    fun i x => by
      rw [modePrefix_succ_of_lt P₀ i.2, hRP]
      rfl
  -- Pythagoras for one projector
  have hpyth : ∀ {T : E →L[ℝ] E}, IsOrthProj T → ∀ w, ‖w‖ ^ 2 = ‖w - T w‖ ^ 2 + ‖T w‖ ^ 2 :=
    fun hT w => by
      have h := hT.norm_sub_apply_sq w 0
      simpa only [map_zero, sub_zero] using h
  -- the three families of numbers
  have ht : ∀ i : Fin d, modePrefix P₀ i ((1 - P₀ i) (z - Q₀ i z)) =
      (1 - P₀ i) (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z)) := fun i => by
    simp only [sub_apply, one_apply_eq_self, map_sub]
    rw [hRQ i z, hQR i z, ← hRP i i z, ← hRP i i (Q₀ i z), hRQ i z]
  have ha : ∀ i : Fin d, modePrefix P₀ i z - P₀ i (modePrefix P₀ i z) =
      modePrefix P₀ i (z - y) - modePrefix P₀ ((i : ℕ) + 1) (z - y) := fun i => by
    rw [hsucc, map_sub, map_sub, hRy, hPy]
    abel
  have hb : ∀ i : Fin d, P₀ i (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z)) =
      modePrefix P₀ ((i : ℕ) + 1) (z - y) - Q₀ i (modePrefix P₀ ((i : ℕ) + 1) (z - y)) :=
    fun i => by
      rw [hsucc, map_sub, map_sub, map_sub, map_sub, hRy, hPy, hQy, ← hcQ₀]
      abel
  have h := sub_mul_sum_sq_le_of_chain (e := ‖z - y‖) (σ := σ)
    (a := fun i : Fin d => ‖modePrefix P₀ i z - P₀ i (modePrefix P₀ i z)‖)
    (b := fun i : Fin d => ‖modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z)‖)
    (t := fun i : Fin d => ‖(1 - P₀ i) (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z))‖)
    (c := fun k => ‖modePrefix P₀ k (z - y)‖ ^ 2) hσ (fun _ => norm_nonneg _)
    (fun _ => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_modePrefix_apply_le_norm hP₀ k _) 2)
    (fun i => by
      have h1 := hpyth (hP₀ i) (modePrefix P₀ i (z - y))
      rw [← hsucc] at h1
      rw [ha i]
      linarith)
    (fun i => by
      have h1 := hpyth (hP₀ i) (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z))
      have h2 : ‖P₀ i (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z))‖ ^ 2 ≤
          ‖modePrefix P₀ ((i : ℕ) + 1) (z - y)‖ ^ 2 := by
        rw [hb i]
        have h3 := hpyth (hQ₀ i) (modePrefix P₀ ((i : ℕ) + 1) (z - y))
        nlinarith [sq_nonneg ‖Q₀ i (modePrefix P₀ ((i : ℕ) + 1) (z - y))‖]
      have e : (1 - P₀ i) (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z)) =
          modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z) -
            P₀ i (modePrefix P₀ i z - Q₀ i (modePrefix P₀ i z)) := by
        simp only [sub_apply, one_apply_eq_self]
      rw [e]
      linarith)
    hm
  rw [norm_sq_sub_modeTangentProj_apply_eq hP₀ hc₀₀ hQsub z]
  simpa only [ht] using h

/-- Non-vacuity of `sub_mul_norm_sq_sub_modeTangentProj_apply_le`: one mode on the real line with
`P₀ = Q₀ = 1`, `y = 1`, `z = 2`, `σ = 2`; all hypotheses hold (the normal component is zero,
since the tangent space is the whole line). -/
example : ((2 : ℝ) ^ 2 - ‖(2 : ℝ) - 1‖ ^ 2) *
    ‖(2 : ℝ) - modeTangentProj (fun _ : Fin 1 => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) 2‖ ^ 2 ≤
      ‖(2 : ℝ) - 1‖ ^ 4 / 2 :=
  sub_mul_norm_sq_sub_modeTangentProj_apply_le (fun _ => IsOrthProj.one)
    (fun _ => IsOrthProj.one) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) zero_le_two (fun i => by simp)

end Abstract

/-! ### Matrices and matricizations -/

section MatrixSecondOrder

open Curvature EckartYoung

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l] [DecidableEq n]

/-- **A product through a matrix of rank at most `q`.** If `M` has rank at most `q` and
`0 < ρ ≤ σ_{q-1}(M)`, then `‖A M B‖ ≤ ρ⁻¹ ‖A M‖ ‖M B‖` in Frobenius norms: `M = M M⁺ M` and
`‖M⁺‖₂ ≤ ρ⁻¹`. -/
theorem norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul {q : ℕ} {M : Matrix m n ℝ}
    (hM : M.rank ≤ q) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin M).singularValues (q - 1)) (A : Matrix k m ℝ)
    (B : Matrix n l ℝ) : ‖A * M * B‖ ≤ ρ⁻¹ * ‖A * M‖ * ‖M * B‖ := by
  classical
  have hrank : M.rank = q := by
    refine le_antisymm hM ?_
    by_contra hlt
    have h0 := (singularValues_le_specNorm_sub M M (r := q - 1) (by omega)).trans
      (specNorm_le_frob _)
    rw [sub_self, norm_zero] at h0
    linarith
  have hp := specNorm_pinv_le hrank hρ hσ
  have e : A * M * B = A * M * (M.pinv * (M * B)) := by
    conv_lhs => rw [← M.mul_pinv_mul_self]
    simp only [Matrix.mul_assoc]
  rw [e]
  calc ‖A * M * (M.pinv * (M * B))‖ ≤ ‖A * M‖ * ‖M.pinv * (M * B)‖ :=
        Matrix.frobenius_norm_mul _ _
    _ ≤ ‖A * M‖ * (ρ⁻¹ * ‖M * B‖) :=
        mul_le_mul_of_nonneg_left ((frob_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right hp (norm_nonneg _))) (norm_nonneg _)
    _ = ρ⁻¹ * ‖A * M‖ * ‖M * B‖ := by ring

/-- Non-vacuity of `norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul`: the `1 × 1` identity matrix,
`q = 1` and `ρ` its singular value. -/
example : ∃ ρ : ℝ, 0 < ρ ∧ ∀ A B : Matrix (Fin 1) (Fin 1) ℝ,
    ‖A * (1 : Matrix (Fin 1) (Fin 1) ℝ) * B‖ ≤ ρ⁻¹ * ‖A * (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ *
      ‖(1 : Matrix (Fin 1) (Fin 1) ℝ) * B‖ :=
  ⟨_, SVD.singularValues_pred_rank_pos (X := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (by simp)
      zero_lt_one,
    fun A B => norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul (by simp)
      (SVD.singularValues_pred_rank_pos (X := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (by simp)
        zero_lt_one) le_rfl A B⟩

end MatrixSecondOrder

namespace Tensor

section ModeSecondOrder

variable {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- **The mode-`k` normal component of a tensor of mode rank at most `q`.** Let the unfolding
`Mat_{≠k}(T)` have rank at most `q` and `0 < ρ ≤ σ_{q-1}(Mat_{≠k}(T))`. For every matrix `U`
acting on mode `k` and every `W` acting on the other modes, with `P = modeProj k U` and
`Q = actOn (· ≠ k) (W Wᵀ)`: `ρ ‖(1 - P) (T - Q T)‖ ≤ ‖T - P T‖ ‖T - Q T‖`. -/
theorem mul_norm_one_sub_modeProj_sub_coRange_le {k : Fin d} {r s : Type*} [Fintype r]
    [Fintype s] (U : Matrix (ι k) r ℝ) (W : Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) s ℝ)
    {q : ℕ} {T : Tensor ι} (hT : (unfold (· ≠ k) T).rank ≤ q) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin (unfold (· ≠ k) T)).singularValues (q - 1)) :
    ρ * ‖(1 - modeProj k U) (T - actOn (· ≠ k) (W * Wᵀ) T)‖ ≤
      ‖T - modeProj k U T‖ * ‖T - actOn (· ≠ k) (W * Wᵀ) T‖ := by
  have e1 : unfold (· ≠ k) (T - actOn (· ≠ k) (W * Wᵀ) T) =
      (1 - W * Wᵀ) * unfold (· ≠ k) T := by
    rw [unfold_sub, unfold_actOn, Matrix.sub_mul, Matrix.one_mul]
  have e2 : unfold (· ≠ k) (T - modeProj k U T) = unfold (· ≠ k) T *
      (1 - (U * Uᵀ)ᵀ.submatrix (compEquiv k) (compEquiv k)) := by
    rw [unfold_sub, modeProj, unfold_ne_modeAct, Matrix.mul_sub, Matrix.mul_one]
  have e3 : unfold (· ≠ k) ((1 - modeProj k U) (T - actOn (· ≠ k) (W * Wᵀ) T)) =
      (1 - W * Wᵀ) * unfold (· ≠ k) T *
        (1 - (U * Uᵀ)ᵀ.submatrix (compEquiv k) (compEquiv k)) := by
    simp only [sub_apply, one_apply_eq_self]
    rw [unfold_sub, modeProj, unfold_ne_modeAct, e1, Matrix.mul_sub, Matrix.mul_one]
  have h := norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul hT hρ hσ (1 - W * Wᵀ)
    (1 - (U * Uᵀ)ᵀ.submatrix (compEquiv k) (compEquiv k))
  rw [← e3, ← e1, ← e2, norm_unfold, norm_unfold, norm_unfold] at h
  calc ρ * ‖(1 - modeProj k U) (T - actOn (· ≠ k) (W * Wᵀ) T)‖
      ≤ ρ * (ρ⁻¹ * ‖T - actOn (· ≠ k) (W * Wᵀ) T‖ * ‖T - modeProj k U T‖) :=
        mul_le_mul_of_nonneg_left h hρ.le
    _ = ‖T - modeProj k U T‖ * ‖T - actOn (· ≠ k) (W * Wᵀ) T‖ := by
        field_simp

end ModeSecondOrder

/-! ### Tucker tensors -/

section TuckerSecondOrder

variable {d : ℕ} {ι r : Fin d → Type*} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]
  [∀ k, Fintype (r k)] [∀ k, DecidableEq (r k)] {U U' : ∀ k, Matrix (ι k) (r k) ℝ}
  {C C' : Tensor r} {s' : Fin d → Type*} [∀ k, Fintype (s' k)]
  {W' : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s' k) ℝ}

/-- **The normal component of a nearby Tucker tensor, with a constant independent of the number
of modes.** Let `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` be Tucker tensors with `d` modes, orthonormal
`Uₖ`, `U'ₖ` with `|r k|` columns, and co-range bases `W'` of `Y` as in
`tuckerTangentProj_eq_starProjection`. Let `ρ` be a lower bound of the singular values
`σ_{|r k|}` of all unfoldings of `Y`, and `e = ‖X - Y‖ < ρ`. Then the normal component of `X`
at `Y` satisfies `ρ (ρ - 2 e) ‖X - P(Y) X‖² ≤ e⁴ / 2`. -/
theorem mul_norm_sq_sub_tuckerTangentProj_tucker_le (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B) {ρ : ℝ}
    (hσ' : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C' U'))).singularValues
      (Fintype.card (r k) - 1))
    (he : ‖tucker C U - tucker C' U'‖ < ρ) :
    ρ * (ρ - 2 * ‖tucker C U - tucker C' U'‖) *
        ‖tucker C U - tuckerTangentProj U' 1 W' (tucker C U)‖ ^ 2 ≤
      ‖tucker C U - tucker C' U'‖ ^ 4 / 2 := by
  have b1 : ∀ k, IsOrthProj (modeProj k (U' k) : Tensor ι →L[ℝ] Tensor ι) := fun k =>
    isOrthProj_modeProj k (hU' k)
  have b2 : ∀ k, IsOrthProj (actOn (· ≠ k) (W' k * (W' k)ᵀ) : Tensor ι →L[ℝ] Tensor ι) :=
    fun k => isOrthProj_coRangeProj_of_capture (hWX' k) (hWB' k)
  have hpos : 0 < ρ - ‖tucker C U - tucker C' U'‖ := sub_pos.2 he
  have h := sub_mul_norm_sq_sub_modeTangentProj_apply_le
    (P₀ := fun k => modeProj k (U' k)) (Q₀ := fun k => actOn (· ≠ k) (W' k * (W' k)ᵀ))
    (y := tucker C' U') (z := tucker C U) (σ := ρ - ‖tucker C U - tucker C' U'‖) b1 b2
    (modeProj_comm_family U')
    (fun i x => (modeProj_comm_coRangeProj i (U' i) (W' i) x).symm)
    (fun i j hji x => modeProj_coRangeProj_of_ne hji (hU' j) (hWB' i) x)
    (fun i => modeProj_tucker i (hU' i) C') hWX' hpos.le (fun i => ?_)
  · rw [tuckerTangentProj_one_eq]
    have e : (ρ - ‖tucker C U - tucker C' U'‖) ^ 2 - ‖tucker C U - tucker C' U'‖ ^ 2 =
        ρ * (ρ - 2 * ‖tucker C U - tucker C' U'‖) := by ring
    rwa [e] at h
  · -- the mode `i`: the unfolding of the prefix projection of `X`
    have hfix : modeProj i (U i) (modePrefix (fun k => modeProj k (U' k)) i (tucker C U)) =
        modePrefix (fun k => modeProj k (U' k)) i (tucker C U) := by
      rw [apply_modePrefix_apply_comm (modeProj i (U i)) i
        (fun j hj x => modeProj_comm (fun hij => by rw [hij] at hj; exact lt_irrefl _ hj) _ _ x),
        modeProj_tucker i (hU i) C]
    have hrk : (unfold (· ≠ i)
        (modePrefix (fun k => modeProj k (U' k)) i (tucker C U))).rank ≤
        Fintype.card (r i) := by
      rw [rank_unfold_ne]
      exact rank_unfold_le_of_modeProj_eq_self i hfix
    have hn : ‖unfold (· ≠ i) (modePrefix (fun k => modeProj k (U' k)) i (tucker C U)) -
        unfold (· ≠ i) (tucker C' U')‖ ≤ ‖tucker C U - tucker C' U'‖ := by
      rw [← unfold_sub, norm_unfold]
      have hy : modePrefix (fun k => modeProj k (U' k)) i (tucker C' U') = tucker C' U' :=
        modePrefix_apply_eq_self i fun j _ => modeProj_tucker j (hU' j) C'
      nth_rw 1 [← hy]
      rw [← map_sub]
      exact norm_modePrefix_apply_le_norm b1 i _
    have hw := (abs_le.1 (WeylSingular.abs_singularValues_sub_le_frobenius
      (unfold (· ≠ i) (modePrefix (fun k => modeProj k (U' k)) i (tucker C U)))
      (unfold (· ≠ i) (tucker C' U')) (Fintype.card (r i) - 1))).1
    exact mul_norm_one_sub_modeProj_sub_coRange_le (U' i) (W' i) hrk hpos
      (by linarith [hσ' i])

/-- **The normal component of a nearby Tucker tensor, explicit form.** Under the hypotheses of
`mul_norm_sq_sub_tuckerTangentProj_tucker_le`, if `2 ‖X - Y‖ < ρ` then
`‖X - P(Y) X‖ ≤ ‖X - Y‖² / √(2 ρ (ρ - 2 ‖X - Y‖))`. -/
theorem norm_sub_tuckerTangentProj_tucker_le (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hU' : ∀ k, (U' k)ᵀ * U' k = 1)
    (hWX' : ∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U')
    (hWB' : ∀ k, ∃ B : Matrix _ (s' k) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B) {ρ : ℝ}
    (hσ' : ∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C' U'))).singularValues
      (Fintype.card (r k) - 1))
    (he : 2 * ‖tucker C U - tucker C' U'‖ < ρ) :
    ‖tucker C U - tuckerTangentProj U' 1 W' (tucker C U)‖ ≤
      ‖tucker C U - tucker C' U'‖ ^ 2 /
        √(2 * ρ * (ρ - 2 * ‖tucker C U - tucker C' U'‖)) := by
  have he0 := norm_nonneg (tucker C U - tucker C' U')
  have h := mul_norm_sq_sub_tuckerTangentProj_tucker_le hU hU' hWX' hWB' hσ'
    (by linarith)
  have hD : 0 < 2 * ρ * (ρ - 2 * ‖tucker C U - tucker C' U'‖) :=
    mul_pos (by linarith) (by linarith)
  have hsq : ‖tucker C U - tuckerTangentProj U' 1 W' (tucker C U)‖ ^ 2 ≤
      (‖tucker C U - tucker C' U'‖ ^ 2 /
        √(2 * ρ * (ρ - 2 * ‖tucker C U - tucker C' U'‖))) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hD.le, le_div_iff₀ hD]
    nlinarith
  exact (abs_le_of_sq_le_sq' hsq (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))).2

end TuckerSecondOrder

/-! ### Example -/

namespace TuckerNormalSecondOrderExamples

/-- The Tucker tensor with one mode of dimension one, the core entry `c` and the basis `1`. -/
theorem tucker_const (c : ℝ) :
    tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => c)
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) = WithLp.toLp 2 fun _ => c :=
  tucker_one _

/-- The co-range basis with the entry one fixes the constant tensor. -/
theorem actOn_const (k : Fin 1) (c : ℝ) :
    actOn (ι := fun _ : Fin 1 => Fin 1) (· ≠ k)
      ((Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ) *
        (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ)ᵀ)
      (WithLp.toLp 2 fun _ => c) = WithLp.toLp 2 fun _ => c := by
  ext x
  simp [actOn_apply, Matrix.mul_apply]

/-- The co-range basis with the entry one lies in the column space of the unfolding of the
constant tensor `c ≠ 0`. -/
theorem coRange_const (k : Fin 1) {c : ℝ} (hc : c ≠ 0) :
    ∃ B : Matrix ({j : Fin 1 // ¬ j ≠ k} → Fin 1) (Fin 1) ℝ,
      (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ) =
        unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k) (WithLp.toLp 2 fun _ => c) * B := by
  refine ⟨Matrix.of fun _ _ => c⁻¹, ?_⟩
  ext z i
  rw [Matrix.mul_apply]
  simp [hc]

/-- The unfolding of the constant tensor `c ≠ 0` has rank one. -/
theorem rank_unfold_const (k : Fin 1) {c : ℝ} (hc : c ≠ 0) :
    (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k) (WithLp.toLp 2 fun _ => c)).rank =
      Fintype.card (Fin 1) := by
  obtain ⟨B, hB⟩ := coRange_const k hc
  have hW : (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ)ᵀ *
      (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ) = 1 := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j]
  refine le_antisymm ((rank_le_card_width _).trans (by simp)) ?_
  calc Fintype.card (Fin 1) = (1 : Matrix (Fin 1) (Fin 1) ℝ).rank := rank_one.symm
    _ ≤ (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ k) (WithLp.toLp 2 fun _ => c) * B).rank := by
        rw [← hW]
        nth_rw 2 [hB]
        exact rank_mul_le_right _ _
    _ ≤ _ := rank_mul_le_left _ _

/-- The singular value of the unfolding of the constant tensor `3`. -/
theorem singularValues_unfold_const_pos :
    0 < (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
      (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) :=
  SVD.singularValues_pred_rank_pos (rank_unfold_const 0 three_ne_zero) (by simp)

/-- The distance of two constant tensors. -/
theorem norm_const_sub_const (c c' : ℝ) :
    ‖(WithLp.toLp 2 fun _ => c : Tensor fun _ : Fin 1 => Fin 1) - WithLp.toLp 2 fun _ => c'‖ =
      |c - c'| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- Non-vacuity of `norm_sub_tuckerTangentProj_tucker_le` with `X ≠ Y`: one mode of dimension
one, `Y` the tensor with the entry `3`, `ρ` the singular value of its unfolding, `X` the tensor
with the entry `3 + ρ/4`, the basis `1` for both and the co-range basis with the entry one. All
hypotheses hold. (With one mode the tangent space is the whole space, so the left-hand side is
zero here.) -/
example : ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, c ≠ 3 ∧
    ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => c)
          (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
        tuckerTangentProj (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1
          (fun k => (Matrix.of fun _ _ => 1 : Matrix ({j : Fin 1 // j ≠ k} → Fin 1) (Fin 1) ℝ))
          (tucker (WithLp.toLp 2 fun _ => c) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)))‖ ≤
      ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => c)
            (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
          tucker (WithLp.toLp 2 fun _ => (3 : ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ^ 2 /
        √(2 * ρ * (ρ - 2 *
          ‖tucker (ι := fun _ : Fin 1 => Fin 1) (WithLp.toLp 2 fun _ => c)
              (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) -
            tucker (WithLp.toLp 2 fun _ => (3 : ℝ))
              (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))‖)) := by
  have hρ := singularValues_unfold_const_pos
  refine ⟨_, hρ, 3 + (toEuclideanLin (unfold (ι := fun _ : Fin 1 => Fin 1) (· ≠ (0 : Fin 1))
      (WithLp.toLp 2 fun _ => (3 : ℝ)))).singularValues (Fintype.card (Fin 1) - 1) / 4,
    by linarith, ?_⟩
  refine norm_sub_tuckerTangentProj_tucker_le (fun _ => by simp) (fun _ => by simp)
    (fun k => by rw [tucker_const]; exact actOn_const k 3)
    (fun k => by rw [tucker_const]; exact coRange_const k three_ne_zero)
    (fun k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [tucker_const]) ?_
  rw [tucker_const, tucker_const, norm_const_sub_const, add_sub_cancel_left,
    abs_of_pos (by linarith)]
  linarith

end TuckerNormalSecondOrderExamples

end Tensor

end LeanDLRA
