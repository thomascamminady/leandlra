import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Tensor.Defs

/-!
# Pythagorean telescoping for orthogonal mode projectors: `√d` instead of `d`

Let `P 0, …, P (d - 1)` be orthogonal projectors on a real inner product space `E` and let
`Π = P 0 ∘ P 1 ∘ ⋯ ∘ P (d - 1)` be their ordered product (`LeanDLRA.modeProd`).  The linear
telescoping bound `‖x - Π x‖ ≤ ∑ᵢ ‖x - P i x‖` (`LeanDLRA.norm_sub_modeProd_apply_le`, the proof
of Lemma 6 of Ceruti–Lubich, arXiv 2010.02022) only uses that each `P i` is a contraction.  For
*orthogonal* projectors the error components are orthogonal, and the bound improves to a
Pythagorean one:

  `‖x - Π x‖² ≤ ∑ᵢ ‖x - P i x‖²`,

so `‖x - P i x‖ ≤ δᵢ` for all `i` gives `‖x - Π x‖ ≤ √(∑ᵢ δᵢ²) ≤ √d · maxᵢ δᵢ`.  For the Tucker
mode projectors `P i X = X ×ᵢ Uᵢ Uᵢᵀ` and `Uᵢ` the dominant left singular vectors of the
mode-`i` matricization this is the `√d` quasi-optimality of the higher-order SVD (HOSVD).

## Main results

* `LeanDLRA.IsOrthProj.norm_sub_apply_sq`: the Pythagorean step
  `‖x - T y‖² = ‖x - T x‖² + ‖T (x - y)‖²` for an orthogonal projector `T`.
* `LeanDLRA.norm_sq_sub_modeProd_apply_le`: `‖x - Π x‖² ≤ ∑ᵢ ‖x - P i x‖²`.  **No commutativity
  is needed** (the factors may even be arbitrary orthogonal projectors, as for the sequentially
  truncated HOSVD).
* `LeanDLRA.norm_sq_sub_modeProd_apply_eq` (exact Pythagorean telescoping): for *pairwise
  commuting* orthogonal projectors,
  `‖x - Π x‖² = ∑ᵢ ‖(P 0 ⋯ P (i - 1)) (1 - P i) x‖²`, with the prefix products
  `LeanDLRA.modePrefix P i`.  The general form `norm_sq_apply_sub_modeProd_apply_eq` carries an
  additional orthogonal projector `S` commuting with all `P i` in front.
* `LeanDLRA.norm_sub_modeProd_apply_le_sqrt` (`‖x - Π x‖ ≤ √(∑ᵢ δᵢ²)`) and
  `LeanDLRA.norm_sub_modeProd_apply_le_sqrt_mul` (`‖x - Π x‖ ≤ √d ϑ`), together with the
  comparisons `sqrt_sum_sq_le_sum` and `sqrt_natCast_le` showing that they improve the linear
  bound.

## Connection to dynamical low-rank approximation

* `LeanDLRA.tucker_capture'`: the new Tucker bases of one step of the Tucker BUG integrator
  capture the exact solution up to `√d ϑ`, `ϑ = h (4 L B h + ε)`, instead of `d ϑ`
  (`LeanDLRA.tucker_capture`); no commutativity assumption is needed.
* `LeanDLRA.tucker_local_error'`, `LeanDLRA.IsTuckerBUGStep.local_error'`,
  `LeanDLRA.IsTuckerBUGStep.local_error_le'`: the robust local error bound
  `(e^{L h} - 1) (B h + √d ϑ) + √d ϑ ≤ h (c₁ ε + c₂ h)` with the improved constants
  `tuckerSqrtC₁ d L H = √d (1 + L H e^{L H})` and
  `tuckerSqrtC₂ d L B H = L B (4 √d + e^{L H} (1 + 4 √d L H))` (OP-RA-06 / OP-RA-22 in
  `docs/OPEN_PROBLEMS.md`); `IsBUGStep.local_error_sqrt_two` is the matrix case `d = 2`.
* `LeanDLRA.norm_sub_modeProd_apply_le_sqrt_mul_norm_sub`,
  `LeanDLRA.norm_sub_modeProd_apply_le_sqrt_mul_infDist`: **quasi-optimality.**  If each `P i`
  is a best mode-`i` approximation, i.e. `‖x - P i x‖ ≤ dist(x, Mᵢ)` for sets `Mᵢ` containing the
  approximation class `M` (Tucker tensors of multilinear rank `≤ (r₀, …, r_{d-1})` and
  `Mᵢ` the tensors of mode-`i` rank `≤ rᵢ`, by Eckart–Young for the matricizations), then
  `‖x - Π x‖ ≤ √d dist(x, M)`.
* `LeanDLRA.norm_sub_modeProd_apply_le_of_tol` (per-mode tolerance `ϑ / √d` suffices for the
  global tolerance `ϑ`, compared with `ϑ / d` in `LeanDLRA.norm_sub_le_of_chain`) and
  `LeanDLRA.IsAugTuckerBUGStep.local_error_modeTrunc`: the local error of the rank-adaptive
  Tucker BUG integrator (Ceruti–Kusch–Lubich, arXiv 2104.05247) when the augmented result is
  truncated by orthogonal mode projectors with per-mode truncation errors `≤ τ` (HOSVD
  truncation): the truncation contributes `√d τ`.

The prefix products `modePrefix` and the constants `tuckerSqrtC₁`, `tuckerSqrtC₂` are defined in
`LeanDLRA/Tensor/Defs.lean`.

## References

* L. De Lathauwer, B. De Moor, J. Vandewalle, *A multilinear singular value decomposition*,
  SIAM J. Matrix Anal. Appl. 21 (2000), Property 10.
* N. Vannieuwenhoven, R. Vandebril, K. Meerbergen, *A new truncation strategy for the higher-order
  singular value decomposition*, SIAM J. Sci. Comput. 34 (2012), Theorem 5.1.
* L. Grasedyck, *Hierarchical singular value decomposition of tensors*, SIAM J. Matrix Anal.
  Appl. 31 (2010), Lemma 3.2 / Theorem 3.11.
* G. Ceruti, C. Lubich, *An unconventional robust integrator for dynamical low-rank
  approximation*, BIT 62 (2022), arXiv 2010.02022, Lemmas 6 and 7.
* G. Ceruti, J. Kusch, C. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, BIT 62 (2022), arXiv 2104.05247, §4.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

/-! ### Prefix products -/

section Prefix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] lemma modePrefix_zero {d : ℕ} (P : Fin d → E →L[ℝ] E) : modePrefix P 0 = 1 := by
  simp [modePrefix]

lemma modePrefix_succ {d : ℕ} (P : Fin (d + 1) → E →L[ℝ] E) (k : ℕ) :
    modePrefix P (k + 1) = P 0 * modePrefix (fun i => P i.succ) k := by
  simp [modePrefix, List.ofFn_succ, List.take_succ_cons]

lemma modePrefix_of_le {d : ℕ} (P : Fin d → E →L[ℝ] E) {k : ℕ} (hk : d ≤ k) :
    modePrefix P k = modeProd P := by
  simp [modePrefix, modeProd, List.take_of_length_le, hk]

end Prefix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Pythagorean telescoping -/

section Telescoping

/-- **Pythagorean step.**  For an orthogonal projector `T`,
`‖x - T y‖² = ‖x - T x‖² + ‖T (x - y)‖²`: the decomposition
`x - T y = (1 - T) x + T (x - y)` is orthogonal. -/
lemma IsOrthProj.norm_sub_apply_sq {T : E →L[ℝ] E} (hT : IsOrthProj T) (x y : E) :
    ‖x - T y‖ ^ 2 = ‖x - T x‖ ^ 2 + ‖T (x - y)‖ ^ 2 := by
  have hdec : x - T y = (x - T x) + T (x - y) := by rw [map_sub]; abel
  have horth : ⟪x - T x, T (x - y)⟫ = 0 := by rw [real_inner_comm, hT.inner_sub_self]
  rw [hdec, norm_add_sq_real, horth]
  ring

/-- **Pythagorean telescoping bound** (list form): for orthogonal projectors `T₁, …, T_k`,
`‖x - (T₁ ∘ ⋯ ∘ T_k) x‖² ≤ ∑ⱼ ‖x - Tⱼ x‖²`.  No commutativity is needed. -/
lemma norm_sq_sub_listProd_apply_le {l : List (E →L[ℝ] E)} (hl : ∀ T ∈ l, IsOrthProj T)
    (x : E) : ‖x - l.prod x‖ ^ 2 ≤ (l.map fun T => ‖x - T x‖ ^ 2).sum := by
  induction l with
  | nil => simp
  | cons T l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    change ‖x - T (l.prod x)‖ ^ 2 ≤ _
    have hT := hl T List.mem_cons_self
    have h1 : ‖T (x - l.prod x)‖ ^ 2 ≤ ‖x - l.prod x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hT.norm_le _) 2
    have h2 := ih fun T' hT' => hl T' (List.mem_cons_of_mem T hT')
    rw [hT.norm_sub_apply_sq]
    linarith

/-- **Pythagorean telescoping bound for mode projectors** (HOSVD error bound, De Lathauwer–
De Moor–Vandewalle 2000, Property 10): for orthogonal projectors `P 0, …, P (d - 1)`,
`‖x - (P 0 ∘ ⋯ ∘ P (d - 1)) x‖² ≤ ∑ᵢ ‖x - P i x‖²`.  No commutativity is needed. -/
theorem norm_sq_sub_modeProd_apply_le {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) (x : E) :
    ‖x - modeProd P x‖ ^ 2 ≤ ∑ i, ‖x - P i x‖ ^ 2 := by
  have h := norm_sq_sub_listProd_apply_le (l := List.ofFn P) (fun T hT => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact hP i) x
  rw [List.map_ofFn, List.sum_ofFn] at h
  exact h

/-- **Exact Pythagorean telescoping, with a commuting projector in front.**  Let the
`P i` be pairwise commuting orthogonal projectors and `S` an orthogonal projector commuting
with every `P i`.  Then
`‖S (x - Π x)‖² = ∑ᵢ ‖S (P 0 ⋯ P (i - 1)) (x - P i x)‖²`. -/
theorem norm_sq_apply_sub_modeProd_apply_eq {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) (hc : ∀ i j x, P i (P j x) = P j (P i x)) {S : E →L[ℝ] E}
    (hS : IsOrthProj S) (hSc : ∀ i x, S (P i x) = P i (S x)) (x : E) :
    ‖S (x - modeProd P x)‖ ^ 2 = ∑ i : Fin d, ‖S (modePrefix P i (x - P i x))‖ ^ 2 := by
  induction d generalizing S with
  | zero => simp
  | succ d ih =>
    have hS' : IsOrthProj (S * P 0) := hS.mul (hP 0) (hSc 0)
    have hS'c : ∀ (i : Fin d) y, (S * P 0) (P i.succ y) = P i.succ ((S * P 0) y) := by
      intro i y
      change S (P 0 (P i.succ y)) = P i.succ (S (P 0 y))
      rw [hc 0 i.succ, hSc]
    have hih := ih (P := fun i => P i.succ) (fun i => hP i.succ)
      (fun i j y => hc i.succ j.succ y) hS' hS'c
    change ‖S (P 0 (x - modeProd (fun i => P i.succ) x))‖ ^ 2 = _ at hih
    have hmp : modeProd P x = P 0 (modeProd (fun i => P i.succ) x) := by
      rw [modeProd_succ]; rfl
    have hdec : S (x - modeProd P x)
        = S (x - P 0 x) + S (P 0 (x - modeProd (fun i => P i.succ) x)) := by
      rw [hmp]; simp only [map_sub]; abel
    have horth : ⟪S (x - P 0 x), S (P 0 (x - modeProd (fun i => P i.succ) x))⟫ = 0 := by
      rw [hS.inner_comp, ← (hP 0).symm, ← hSc, map_sub, (hP 0).idem, sub_self, map_zero,
        inner_zero_left]
    have hpre : ∀ i : Fin d, S (modePrefix P ((i.succ : Fin (d + 1)) : ℕ) (x - P i.succ x))
        = (S * P 0) (modePrefix (fun i => P i.succ) i (x - P i.succ x)) := by
      intro i
      rw [Fin.val_succ, modePrefix_succ]
      rfl
    rw [Fin.sum_univ_succ, hdec, norm_add_sq_real, horth, Fin.val_zero, modePrefix_zero,
      one_apply_eq_self, hih]
    simp only [hpre]
    ring

/-- **Exact Pythagorean telescoping for commuting orthogonal projectors**: for pairwise
commuting orthogonal projectors `P 0, …, P (d - 1)`,
`‖x - (P 0 ∘ ⋯ ∘ P (d - 1)) x‖² = ∑ᵢ ‖(P 0 ⋯ P (i - 1)) (1 - P i) x‖²`. -/
theorem norm_sq_sub_modeProd_apply_eq {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) (hc : ∀ i j x, P i (P j x) = P j (P i x)) (x : E) :
    ‖x - modeProd P x‖ ^ 2 = ∑ i : Fin d, ‖modePrefix P i (x - P i x)‖ ^ 2 := by
  simpa using norm_sq_apply_sub_modeProd_apply_eq hP hc IsOrthProj.one (fun _ _ => rfl) x

/-- **`√(∑ δᵢ²)` bound.**  If `‖x - P i x‖ ≤ δᵢ` for orthogonal projectors `P i`, then
`‖x - (P 0 ∘ ⋯ ∘ P (d - 1)) x‖ ≤ √(∑ᵢ δᵢ²)`. -/
theorem norm_sub_modeProd_apply_le_sqrt {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) {x : E} {δ : Fin d → ℝ} (hδ : ∀ i, ‖x - P i x‖ ≤ δ i) :
    ‖x - modeProd P x‖ ≤ √(∑ i, δ i ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (x - modeProd P x))]
  refine Real.sqrt_le_sqrt ((norm_sq_sub_modeProd_apply_le hP x).trans ?_)
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hδ i) 2

/-- **`√d` bound.**  If `‖x - P i x‖ ≤ ϑ` for orthogonal projectors `P 0, …, P (d - 1)`, then
`‖x - (P 0 ∘ ⋯ ∘ P (d - 1)) x‖ ≤ √d ϑ`. -/
theorem norm_sub_modeProd_apply_le_sqrt_mul {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) {x : E} {ϑ : ℝ} (hϑ : ∀ i, ‖x - P i x‖ ≤ ϑ) :
    ‖x - modeProd P x‖ ≤ √(d : ℝ) * ϑ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hϑ0 : 0 ≤ ϑ := (norm_nonneg _).trans (hϑ ⟨0, hd⟩)
    refine (norm_sub_modeProd_apply_le_sqrt hP (δ := fun _ => ϑ) hϑ).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hϑ0]

/-- The Pythagorean bound improves the linear one: `√(∑ᵢ δᵢ²) ≤ ∑ᵢ δᵢ` for `δ ≥ 0`. -/
lemma sqrt_sum_sq_le_sum {ι : Type*} (s : Finset ι) {δ : ι → ℝ} (hδ : ∀ i ∈ s, 0 ≤ δ i) :
    √(∑ i ∈ s, δ i ^ 2) ≤ ∑ i ∈ s, δ i := by
  rw [Real.sqrt_le_left (Finset.sum_nonneg hδ)]
  exact Finset.sum_sq_le_sq_sum_of_nonneg hδ

/-- `√d ≤ d` for natural numbers `d`. -/
lemma sqrt_natCast_le (d : ℕ) : √(d : ℝ) ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [Real.sqrt_le_left (Nat.cast_nonneg d)]
    nlinarith

end Telescoping

/-! ### Constants of the improved local error bound -/

section Constants

lemma tuckerSqrtC₁_le (d : ℕ) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) :
    tuckerSqrtC₁ d L H ≤ tuckerC₁ d L H := by
  unfold tuckerSqrtC₁ tuckerC₁
  exact mul_le_mul_of_nonneg_right (sqrt_natCast_le d) (by positivity)

lemma tuckerSqrtC₂_le (d : ℕ) {L B H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    tuckerSqrtC₂ d L B H ≤ tuckerC₂ d L B H := by
  unfold tuckerSqrtC₂ tuckerC₂
  have hs := sqrt_natCast_le d
  have he : 0 ≤ Real.exp (L * H) := (Real.exp_pos _).le
  have hLH : 0 ≤ L * H := mul_nonneg hL hH
  have h1 : 4 * √(d : ℝ) * L * H ≤ 4 * d * L * H := by nlinarith
  have h2 : Real.exp (L * H) * (1 + 4 * √(d : ℝ) * L * H)
      ≤ Real.exp (L * H) * (1 + 4 * d * L * H) := by nlinarith
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hL hB)

/-- The explicit local bound `(e^{L h} - 1) (B h + D ϑ) + D ϑ`, `ϑ = h (4 L B h + ε)`, is bounded
by `h (c₁ ε + c₂ h)` with `D = √d` and the constants `tuckerSqrtC₁`, `tuckerSqrtC₂`, for
`0 ≤ h ≤ H`.  Only `√d ε ≥ 0` is needed. -/
lemma tucker_sqrt_bound_le {d : ℕ} {L B ε h H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hdε : 0 ≤ √(d : ℝ) * ε) (hh : 0 ≤ h) (hhH : h ≤ H) :
    (Real.exp (L * h) - 1) * (B * h + √(d : ℝ) * (h * (4 * L * B * h + ε)))
        + √(d : ℝ) * (h * (4 * L * B * h + ε))
      ≤ h * (tuckerSqrtC₁ d L H * ε + tuckerSqrtC₂ d L B H * h) := by
  set e := Real.exp (L * H) with he
  set D : ℝ := √(d : ℝ) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have hHh : 0 ≤ H - h := by linarith
  have hexp : Real.exp (L * h) ≤ e := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have h1 : Real.exp (L * h) - 1 ≤ L * h * e :=
    (exp_sub_one_le_mul_exp (L * h)).trans (mul_le_mul_of_nonneg_left hexp hLh)
  have hX : 0 ≤ B * h + D * (h * (4 * L * B * h + ε)) := by
    have hrw : B * h + D * (h * (4 * L * B * h + ε))
        = B * h + 4 * D * L * B * h ^ 2 + h * (D * ε) := by ring
    rw [hrw]
    have : 0 ≤ h * (D * ε) := mul_nonneg hh hdε
    positivity
  have h2 : (Real.exp (L * h) - 1) * (B * h + D * (h * (4 * L * B * h + ε)))
      ≤ L * h * e * (B * h + D * (h * (4 * L * B * h + ε))) :=
    mul_le_mul_of_nonneg_right h1 hX
  have hgap1 : 0 ≤ L * e * h * (D * ε) * (H - h) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hL he0) hh) hdε) hHh
  have hgap2 : 0 ≤ 4 * D * L ^ 2 * B * e * h ^ 2 * (H - h) := by positivity
  have hid : h * (tuckerSqrtC₁ d L H * ε + tuckerSqrtC₂ d L B H * h)
      = L * h * e * (B * h + D * (h * (4 * L * B * h + ε))) + D * (h * (4 * L * B * h + ε))
        + (L * e * h * (D * ε) * (H - h) + 4 * D * L ^ 2 * B * e * h ^ 2 * (H - h)) := by
    unfold tuckerSqrtC₁ tuckerSqrtC₂; rw [← he, ← hD]; ring
  rw [hid]
  linarith

end Constants

/-! ### Capture and local error of the Tucker BUG integrator with `√d` -/

section Local

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {d : ℕ}

/-- **Lemma 6 of arXiv 2010.02022 with `√d`.**  Under the hypotheses of `tucker_capture`, the
new Tucker bases capture the exact solution up to

    ‖A t₁ - (P₁ 0 ∘ ⋯ ∘ P₁ (d-1)) A t₁‖ ≤ √d ϑ,    ϑ = h (4 L B h + ε),

instead of `d ϑ`.  The mode projectors need not commute. -/
theorem tucker_capture' {P₁ Q₀ : Fin d → E →L[ℝ] E} {YK : Fin d → ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : ∀ i, IsOrthProj (P₁ i)) (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = A t₀)
    (hKcap : ∀ i, P₁ i (YK i t₁) = YK i t₁)
    (hεK : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε) :
    ‖A t₁ - modeProd P₁ (A t₁)‖ ≤ √(d : ℝ) * (h * (4 * L * B * h + ε)) :=
  norm_sub_modeProd_apply_le_sqrt_mul hP₁ fun i => by
    have := kstep_capture hF hL hB (hP₁ i) (hQ₀ i) ht₁ hh hA (hK i) (hK₀ i) (hKcap i) (hεK i)
    simpa using this

/-- **Robust local error of the Tucker BUG integrator with `√d`** (arXiv 2010.02022, Lemma 7,
improved constant).  Under the hypotheses of `tucker_local_error`, with `ϑ = h (4 L B h + ε)`,

    ‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + √d ϑ) + √d ϑ. -/
theorem tucker_local_error' {P₁ Q₀ : Fin d → E →L[ℝ] E} {Y₀ : E} {YK : Fin d → ℝ → E}
    {YS : ℝ → E} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : ∀ i, IsOrthProj (P₁ i)) (hQ₀ : ∀ i, IsOrthProj (Q₀ i))
    (hc : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = Y₀)
    (hKcap : ∀ i, P₁ i (YK i t₁) = YK i t₁)
    (hεK : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = modeProd P₁ Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + √(d : ℝ) * (h * (4 * L * B * h + ε)))
      + √(d : ℝ) * (h * (4 * L * B * h + ε)) :=
  galerkin_step_error (IsOrthProj.modeProd hP₁ hc) hF hL hB ht₁ hh hA hS (by rw [hS₀, hA₀])
    (tucker_capture' hF hL hB hP₁ hQ₀ ht₁ hh hA hK (fun i => (hK₀ i).trans hA₀.symm) hKcap hεK)

namespace IsTuckerBUGStep

variable {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E} {YK : Fin d → ℝ → E} {YS : ℝ → E}

/-- On a nonempty step, `√d ε ≥ 0`. -/
lemma sqrt_mul_eps_nonneg (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁) :
    0 ≤ √(d : ℝ) * ε := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact mul_nonneg (Real.sqrt_nonneg _)
      ((norm_nonneg _).trans (hs.kNormal ⟨0, hd⟩ t₀ ⟨le_rfl, h01⟩))

/-- Bundled form of `tucker_capture'`. -/
theorem capture' (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - modeProd P₁ (A t₁)‖ ≤ √(d : ℝ) * (h * (4 * L * B * h + ε)) :=
  tucker_capture' hF hL hB hs.projP₁ hs.projQ₀ ht₁ hh hA hs.kSol
    (fun i => (hs.kStart i).trans hA₀.symm) hs.kCap hs.kNormal

/-- Bundled form of `tucker_local_error'`. -/
theorem local_error' (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + √(d : ℝ) * (h * (4 * L * B * h + ε)))
      + √(d : ℝ) * (h * (4 * L * B * h + ε)) :=
  tucker_local_error' hF hL hB hs.projP₁ hs.projQ₀ hs.comm₁ ht₁ hh hA hA₀ hs.kSol hs.kStart
    hs.kCap hs.kNormal hs.sSol hs.sStart

/-- **Robust local error of the Tucker BUG integrator, `O`-form with `√d`**: for `0 ≤ h ≤ H`,
`‖YS t₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = tuckerSqrtC₁ d L H ≤ tuckerC₁ d L H` and
`c₂ = tuckerSqrtC₂ d L B H ≤ tuckerC₂ d L B H`. -/
theorem local_error_le' (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ h * (tuckerSqrtC₁ d L H * ε + tuckerSqrtC₂ d L B H * h) :=
  (hs.local_error' hF hL hB ht₁ hh hA hA₀).trans
    (tucker_sqrt_bound_le hL hB.nonneg (hs.sqrt_mul_eps_nonneg (by linarith)) hh hhH)

end IsTuckerBUGStep

/-- **Matrix case `d = 2`**: the matrix BUG local error bound with `√2` in place of `2`
(compare `IsBUGStep.local_error_of_tucker` and arXiv 2010.02022, Lemma 4). -/
theorem IsBUGStep.local_error_sqrt_two {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + √2 * (h * (4 * L * B * h + ε)))
      + √2 * (h * (4 * L * B * h + ε)) := by
  have h2 := hs.toTucker.local_error' hF hL hB ht₁ hh hA hA₀
  simpa using h2

end Local

/-! ### Quasi-optimality and rank truncation -/

section Truncation

/-- **HOSVD quasi-optimality** (De Lathauwer–De Moor–Vandewalle 2000; abstract form).  If every
mode projector is at least as good as a competitor `y`, `‖x - P i x‖ ≤ ‖x - y‖` (e.g. `P i` the
projector onto the dominant mode-`i` singular vectors and `y` any tensor of mode-`i` rank
`≤ rᵢ`, by Eckart–Young), then `‖x - (P 0 ∘ ⋯ ∘ P (d - 1)) x‖ ≤ √d ‖x - y‖`. -/
theorem norm_sub_modeProd_apply_le_sqrt_mul_norm_sub {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) {x y : E} (hopt : ∀ i, ‖x - P i x‖ ≤ ‖x - y‖) :
    ‖x - modeProd P x‖ ≤ √(d : ℝ) * ‖x - y‖ :=
  norm_sub_modeProd_apply_le_sqrt_mul hP hopt

/-- **HOSVD quasi-optimality, distance form.**  Let `M ⊆ Mᵢ` for all modes `i` (e.g. `M` the
tensors of multilinear rank `≤ (r₀, …, r_{d-1})` and `Mᵢ` those of mode-`i` rank `≤ rᵢ`), `M`
nonempty, and let each orthogonal projector `P i` be a best approximation from `Mᵢ`,
`‖x - P i x‖ ≤ dist(x, Mᵢ)`.  Then `‖x - (P 0 ∘ ⋯ ∘ P (d - 1)) x‖ ≤ √d dist(x, M)`. -/
theorem norm_sub_modeProd_apply_le_sqrt_mul_infDist {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) {x : E} {M : Set E} {Mi : Fin d → Set E} (hM : M.Nonempty)
    (hsub : ∀ i, M ⊆ Mi i) (hopt : ∀ i, ‖x - P i x‖ ≤ Metric.infDist x (Mi i)) :
    ‖x - modeProd P x‖ ≤ √(d : ℝ) * Metric.infDist x M :=
  norm_sub_modeProd_apply_le_sqrt_mul hP fun i =>
    (hopt i).trans (Metric.infDist_le_infDist_of_subset (hsub i) hM)

/-- **Per-mode tolerance `ϑ / √d`.**  If the orthogonal truncation projectors `P i` satisfy
`‖x - P i x‖ ≤ ϑ / √d` (`d ≥ 1`), then `‖x - (P 0 ∘ ⋯ ∘ P (d - 1)) x‖ ≤ ϑ`.  The linear
telescoping (`norm_sub_le_of_chain`) needs the smaller tolerance `ϑ / d`. -/
theorem norm_sub_modeProd_apply_le_of_tol {d : ℕ} (hd : 0 < d) {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) {x : E} {ϑ : ℝ} (htol : ∀ i, ‖x - P i x‖ ≤ ϑ / √(d : ℝ)) :
    ‖x - modeProd P x‖ ≤ ϑ := by
  have hs : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  refine (norm_sub_modeProd_apply_le_sqrt_mul hP htol).trans_eq ?_
  field_simp

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {d : ℕ}

/-- **Local error of the rank-adaptive Tucker BUG integrator with mode-wise truncation**
(arXiv 2104.05247, §4.1, step 3, and §4.2, with HOSVD-type truncation).  If the augmented result
`YS t₁` is truncated by orthogonal mode projectors `R i` with per-mode truncation errors
`‖YS t₁ - R i (YS t₁)‖ ≤ τ`, then the truncated result `Y₁ = (R 0 ∘ ⋯ ∘ R (d - 1)) (YS t₁)`
satisfies, with `ϑ = h (4 L B h + ε)`,

    ‖Y₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + √d ϑ) + √d ϑ + √d τ. -/
theorem IsAugTuckerBUGStep.local_error_modeTrunc {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E}
    {YK : Fin d → ℝ → E} {YS : ℝ → E} (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) {R : Fin d → E →L[ℝ] E}
    (hR : ∀ i, IsOrthProj (R i)) {τ : ℝ} (htr : ∀ i, ‖YS t₁ - R i (YS t₁)‖ ≤ τ) :
    ‖modeProd R (YS t₁) - A t₁‖
      ≤ (Real.exp (L * h) - 1) * (B * h + √(d : ℝ) * (h * (4 * L * B * h + ε)))
        + √(d : ℝ) * (h * (4 * L * B * h + ε)) + √(d : ℝ) * τ := by
  have h1 := hs.local_error' hF hL hB ht₁ hh hA hA₀
  have h2 : ‖modeProd R (YS t₁) - YS t₁‖ ≤ √(d : ℝ) * τ := by
    rw [norm_sub_rev]; exact norm_sub_modeProd_apply_le_sqrt_mul hR htr
  calc ‖modeProd R (YS t₁) - A t₁‖
      ≤ ‖modeProd R (YS t₁) - YS t₁‖ + ‖YS t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

end Truncation

end LeanDLRA
