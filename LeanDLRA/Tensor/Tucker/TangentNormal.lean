import LeanDLRA.Tensor.Tucker.Tangent
import LeanDLRA.Classical.CommutingProjectorTelescoping

/-!
# Normal components with respect to the tangent projector of the Tucker manifold

The tangent projector of the Tucker manifold, `P = modeTangentProj P₀ Q₀ = ∏ᵢ P₀ i +
∑ᵢ (1 - P₀ i) Q₀ i` with the mode projectors `P₀ i` and the co-range projectors `Q₀ i`, is below
each of the `d` projectors `Tᵢ = P₀ i + (1 - P₀ i) Q₀ i`, which are the tangent projectors of the
manifolds of matrices of fixed rank at the matricizations. This file compares the normal component
`z - P z` with the `d` normal components `z - Tᵢ z = (1 - P₀ i) (z - Q₀ i z)`:

  `‖z - P z‖² = ∑ᵢ ‖(P₀ 0 ⋯ P₀ (i - 1)) (1 - P₀ i) (z - Q₀ i z)‖² ≤ ∑ᵢ ‖z - Tᵢ z‖²`,

and `Tᵢ (P z) = P z`. So a bound for the `d` matricizations gives a bound for the Tucker manifold
with the factor `√d`: if the normal components at a second frame of the vectors tangent at the
first one are bounded with a constant `c` in every mode, and conversely, then the two tangent
projectors differ by at most `√d c` in the operator norm.

All statements are for an abstract real inner product space and projectors satisfying the
hypotheses of `modeTangentProj_isOrthProj`.

## Main results

* `LeanDLRA.sub_modeTangentProj_apply_sub_eq`, `LeanDLRA.modeTangentProj_apply_sub_coRange_eq`:
  `(1 - P₀ k) (P z - Q₀ k (P z)) = 0`, a tangent vector is tangent in every mode.
* `LeanDLRA.norm_sq_sub_modeTangentProj_apply_eq`,
  `LeanDLRA.norm_sq_sub_modeTangentProj_apply_le`: the identity and the bound above.
* `LeanDLRA.norm_sub_modeTangentProj_apply_le_sqrt_mul`: `‖z - P z‖ ≤ √d δ` if
  `‖(1 - P₀ i) (z - Q₀ i z)‖ ≤ δ` for all `i`.
* `LeanDLRA.norm_sub_modeTangentProj_apply_le_of_eq_self`,
  `LeanDLRA.norm_modeTangentProj_apply_le_of_eq_zero`,
  `LeanDLRA.norm_modeTangentProj_sub_le`: the bounds with `√d c` for two frames.
-/

open scoped RealInnerProductSpace

namespace LeanDLRA

section ModeTangentNormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A product of orthogonal projectors does not increase the norm. -/
private lemma norm_listProd_apply_le {l : List (E →L[ℝ] E)} (hl : ∀ T ∈ l, IsOrthProj T)
    (x : E) : ‖l.prod x‖ ≤ ‖x‖ := by
  induction l with
  | nil => simp
  | cons T l ih =>
    rw [List.prod_cons]
    exact ((hl T List.mem_cons_self).norm_le _).trans
      (ih fun S hS => hl S (List.mem_cons_of_mem T hS))

/-- A prefix product of orthogonal projectors does not increase the norm. -/
private lemma norm_modePrefix_apply_le {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) (k : ℕ) (x : E) : ‖modePrefix P k x‖ ≤ ‖x‖ :=
  norm_listProd_apply_le (fun T hT => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hT)
    exact hP i) x

variable {d : ℕ} {P₀ Q₀ : Fin d → E →L[ℝ] E}

/-- The tangent projector applied to a vector, in terms of applications. -/
private lemma modeTangentProj_apply (x : E) :
    modeTangentProj P₀ Q₀ x = modeProd P₀ x + ∑ i, (Q₀ i x - P₀ i (Q₀ i x)) := by
  simp [modeTangentProj]

/-- **The mode-`k` complement of a tangent projection.** For the tangent projector
`P = modeTangentProj P₀ Q₀`: `(1 - P₀ k) (P z) = (1 - P₀ k) (Q₀ k z)`. -/
theorem sub_modeTangentProj_apply_eq (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (k : Fin d) (z : E) :
    modeTangentProj P₀ Q₀ z - P₀ k (modeTangentProj P₀ Q₀ z) = Q₀ k z - P₀ k (Q₀ k z) := by
  have hidem : ∀ i x, P₀ i (P₀ i x) = P₀ i x := fun i => (hP₀ i).idem
  rw [modeTangentProj_apply, map_add, map_sum, apply_modeProd_eq_self hidem hc₀₀,
    add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
  · rw [map_sub, hidem, sub_self, sub_zero]
  · intro i _ hik
    rw [map_sub, hc₀₀ k i, hQsub i k (Ne.symm hik), sub_self]
  · simp

/-- **The co-range part of a tangent projection.** For the tangent projector
`P = modeTangentProj P₀ Q₀`: `(1 - P₀ k) (Q₀ k (P z)) = (1 - P₀ k) (Q₀ k z)`. -/
theorem coRange_modeTangentProj_apply_sub_eq (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (k : Fin d) (z : E) :
    Q₀ k (modeTangentProj P₀ Q₀ z) - P₀ k (Q₀ k (modeTangentProj P₀ Q₀ z)) =
      Q₀ k z - P₀ k (Q₀ k z) := by
  have hidem : ∀ i x, P₀ i (P₀ i x) = P₀ i x := fun i => (hP₀ i).idem
  -- `Q₀ k` absorbs the other mode projectors also from the right
  have hQP : ∀ j, j ≠ k → ∀ y, Q₀ k (P₀ j y) = Q₀ k y := fun j hj y => by
    refine ext_inner_right ℝ fun x => ?_
    rw [(hQ₀ k).symm, (hP₀ j).symm, hQsub k j hj, (hQ₀ k).symm]
  have h0 : Q₀ k (modeProd P₀ z) - P₀ k (Q₀ k (modeProd P₀ z)) = 0 := by
    rw [← hcQ₀, apply_modeProd_eq_self hidem hc₀₀, sub_self]
  rw [modeTangentProj_apply, map_add, map_add, map_sum, map_sum, add_sub_add_comm, h0, zero_add,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
  · rw [map_sub, hcQ₀ k (Q₀ k z), (hQ₀ k).idem, map_sub, hidem, sub_self, sub_zero]
  · intro i _ hik
    rw [map_sub, hQP i hik, sub_self, map_zero, sub_zero]
  · simp

/-- **A tangent vector is tangent in every mode.** For `P = modeTangentProj P₀ Q₀` and every
mode `k`, the vector `P z` has no normal component with respect to the tangent projector
`P₀ k + (1 - P₀ k) Q₀ k` of the `k`-th matricization: `(1 - P₀ k) (P z - Q₀ k (P z)) = 0`. -/
theorem modeTangentProj_apply_sub_coRange_eq (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (k : Fin d) (z : E) :
    (1 - P₀ k) (modeTangentProj P₀ Q₀ z - Q₀ k (modeTangentProj P₀ Q₀ z)) = 0 := by
  have h1 := sub_modeTangentProj_apply_eq hP₀ hc₀₀ hQsub k z
  have h2 := coRange_modeTangentProj_apply_sub_eq hP₀ hQ₀ hc₀₀ hcQ₀ hQsub k z
  simp only [sub_apply, one_apply_eq_self, map_sub]
  rw [h1, h2, sub_self]

/-- **The normal component is the orthogonal sum of its mode parts.** For
`P = modeTangentProj P₀ Q₀`:
`‖z - P z‖² = ∑ᵢ ‖(P₀ 0 ⋯ P₀ (i - 1)) (1 - P₀ i) (z - Q₀ i z)‖²`. -/
theorem norm_sq_sub_modeTangentProj_apply_eq (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (z : E) :
    ‖z - modeTangentProj P₀ Q₀ z‖ ^ 2 =
      ∑ i : Fin d, ‖modePrefix P₀ i ((1 - P₀ i) (z - Q₀ i z))‖ ^ 2 := by
  have hidem : ∀ i x, P₀ i (P₀ i x) = P₀ i x := fun i => (hP₀ i).idem
  have hcompl : ∀ j y, modeProd P₀ (y - P₀ j y) = 0 := fun j y => by
    have hproj : modeProd P₀ (P₀ j y) = P₀ j (modeProd P₀ y) :=
      (Commute.clm_apply (commute_modeProd (a := P₀ j) fun i =>
        ContinuousLinearMap.ext (hc₀₀ j i)) y).symm
    rw [map_sub, hproj, apply_modeProd_eq_self hidem hc₀₀, sub_self]
  have hprod : modeProd P₀ (z - modeTangentProj P₀ Q₀ z) = 0 := by
    rw [modeTangentProj_apply, map_sub, map_add, map_sum,
      Finset.sum_eq_zero fun i _ => hcompl i (Q₀ i z), add_zero,
      (IsOrthProj.modeProd hP₀ hc₀₀).idem, sub_self]
  have h := norm_sq_sub_modeProd_apply_eq hP₀ hc₀₀ (z - modeTangentProj P₀ Q₀ z)
  rw [hprod, sub_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := sub_modeTangentProj_apply_eq hP₀ hc₀₀ hQsub i z
  have e : z - modeTangentProj P₀ Q₀ z - P₀ i (z - modeTangentProj P₀ Q₀ z) =
      (1 - P₀ i) (z - Q₀ i z) := by
    simp only [sub_apply, one_apply_eq_self, map_sub]
    calc z - modeTangentProj P₀ Q₀ z - (P₀ i z - P₀ i (modeTangentProj P₀ Q₀ z))
        = (z - P₀ i z) - (modeTangentProj P₀ Q₀ z - P₀ i (modeTangentProj P₀ Q₀ z)) := by abel
      _ = z - P₀ i z - (Q₀ i z - P₀ i (Q₀ i z)) := by rw [h1]
  rw [e]

/-- **The normal component is bounded by the normal components of the modes.** For
`P = modeTangentProj P₀ Q₀`: `‖z - P z‖² ≤ ∑ᵢ ‖(1 - P₀ i) (z - Q₀ i z)‖²`, where
`(1 - P₀ i) (z - Q₀ i z)` is the normal component of `z` with respect to the tangent projector
`P₀ i + (1 - P₀ i) Q₀ i` of the `i`-th matricization. -/
theorem norm_sq_sub_modeTangentProj_apply_le (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (z : E) :
    ‖z - modeTangentProj P₀ Q₀ z‖ ^ 2 ≤ ∑ i : Fin d, ‖(1 - P₀ i) (z - Q₀ i z)‖ ^ 2 := by
  rw [norm_sq_sub_modeTangentProj_apply_eq hP₀ hc₀₀ hQsub]
  exact Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_modePrefix_apply_le hP₀ _ _) 2

/-- **The factor `√d`.** If the normal component of `z` in every mode is at most `δ`, then
`‖z - P z‖ ≤ √d δ` for `P = modeTangentProj P₀ Q₀`. -/
theorem norm_sub_modeTangentProj_apply_le_sqrt_mul (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) {z : E} {δ : ℝ}
    (hδ : ∀ i, ‖(1 - P₀ i) (z - Q₀ i z)‖ ≤ δ) :
    ‖z - modeTangentProj P₀ Q₀ z‖ ≤ √d * δ := by
  have hδ0 : 0 ≤ √(d : ℝ) * δ := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · exact mul_nonneg (Real.sqrt_nonneg _) ((norm_nonneg _).trans (hδ ⟨0, hd⟩))
  refine abs_le_of_sq_le_sq' ?_ hδ0 |>.2
  calc ‖z - modeTangentProj P₀ Q₀ z‖ ^ 2
      ≤ ∑ i : Fin d, ‖(1 - P₀ i) (z - Q₀ i z)‖ ^ 2 :=
        norm_sq_sub_modeTangentProj_apply_le hP₀ hc₀₀ hQsub z
    _ ≤ ∑ _i : Fin d, δ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hδ i) 2
    _ = (√d * δ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow,
          Real.sq_sqrt (Nat.cast_nonneg d)]

/-! ### Two orthogonal projectors -/

/-- **From tangent vectors to normal vectors.** Let `P`, `P'` be orthogonal projectors. If
`‖z - P' z‖ ≤ κ ‖z‖` for all `z` in the range of `P`, then `‖P N‖ ≤ κ ‖N‖` for all `N` in the
kernel of `P'`: the maps `(1 - P') P` and `P (1 - P')` are adjoint to each other. -/
theorem IsOrthProj.norm_apply_le_of_norm_sub_apply_le {P P' : E →L[ℝ] E} (hP : IsOrthProj P)
    (hP' : IsOrthProj P') {κ : ℝ} (hκ : 0 ≤ κ) (h : ∀ z, P z = z → ‖z - P' z‖ ≤ κ * ‖z‖)
    {N : E} (hN : P' N = 0) : ‖P N‖ ≤ κ * ‖N‖ := by
  have e : ‖P N‖ * ‖P N‖ = ⟪P N - P' (P N), N⟫ := by
    rw [inner_sub_left, hP'.symm, hN, inner_zero_right, sub_zero,
      ← real_inner_self_eq_norm_mul_norm, hP.symm, hP.idem]
    exact real_inner_comm _ _
  have h1 : ‖P N‖ * ‖P N‖ ≤ ‖P N‖ * (κ * ‖N‖) := by
    rw [e]
    calc ⟪P N - P' (P N), N⟫ ≤ ‖P N - P' (P N)‖ * ‖N‖ := real_inner_le_norm _ _
      _ ≤ κ * ‖P N‖ * ‖N‖ := mul_le_mul_of_nonneg_right (h _ (hP.idem N)) (norm_nonneg _)
      _ = ‖P N‖ * (κ * ‖N‖) := by ring
  rcases (norm_nonneg (P N)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg hκ (norm_nonneg _)
  · exact le_of_mul_le_mul_left h1 h0

/-- **From normal vectors to tangent vectors.** Let `P`, `P'` be orthogonal projectors. If
`‖P' N‖ ≤ κ ‖N‖` for all `N` in the kernel of `P`, then `‖z - P z‖ ≤ κ ‖z‖` for all `z` in the
range of `P'`. -/
theorem IsOrthProj.norm_sub_apply_le_of_norm_apply_le {P P' : E →L[ℝ] E} (hP : IsOrthProj P)
    (hP' : IsOrthProj P') {κ : ℝ} (hκ : 0 ≤ κ) (h : ∀ N, P N = 0 → ‖P' N‖ ≤ κ * ‖N‖)
    {z : E} (hz : P' z = z) : ‖z - P z‖ ≤ κ * ‖z‖ := by
  have hw : P (z - P z) = 0 := by rw [map_sub, hP.idem, sub_self]
  have e : ‖z - P z‖ * ‖z - P z‖ = ⟪P' (z - P z), z⟫ := by
    rw [hP'.symm, hz, ← real_inner_self_eq_norm_mul_norm, inner_sub_right (z - P z) z (P z),
      ← hP.symm, hw, inner_zero_left, sub_zero]
  have h1 : ‖z - P z‖ * ‖z - P z‖ ≤ ‖z - P z‖ * (κ * ‖z‖) := by
    rw [e]
    calc ⟪P' (z - P z), z⟫ ≤ ‖P' (z - P z)‖ * ‖z‖ := real_inner_le_norm _ _
      _ ≤ κ * ‖z - P z‖ * ‖z‖ := mul_le_mul_of_nonneg_right (h _ hw) (norm_nonneg _)
      _ = ‖z - P z‖ * (κ * ‖z‖) := by ring
  rcases (norm_nonneg (z - P z)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg hκ (norm_nonneg _)
  · exact le_of_mul_le_mul_left h1 h0

/-- **The difference of two orthogonal projectors.** If the normal component with respect to
`P'` of every vector in the range of `P` is at most `κ` times the vector, and conversely, then
`‖P' B - P B‖ ≤ κ ‖B‖` for all `B`: the difference is the orthogonal sum of `P' (B - P B)` and
`-(P B - P' (P B))`, and `‖B‖² = ‖B - P B‖² + ‖P B‖²`. -/
theorem IsOrthProj.norm_sub_apply_le_of_norm_sub_apply_le {P P' : E →L[ℝ] E}
    (hP : IsOrthProj P) (hP' : IsOrthProj P') {κ : ℝ} (hκ : 0 ≤ κ)
    (h : ∀ z, P z = z → ‖z - P' z‖ ≤ κ * ‖z‖) (h' : ∀ z, P' z = z → ‖z - P z‖ ≤ κ * ‖z‖)
    (B : E) : ‖P' B - P B‖ ≤ κ * ‖B‖ := by
  have ha : ‖P' (B - P B)‖ ≤ κ * ‖B - P B‖ :=
    hP'.norm_apply_le_of_norm_sub_apply_le hP hκ h' (by rw [map_sub, hP.idem, sub_self])
  have hb : ‖P B - P' (P B)‖ ≤ κ * ‖P B‖ := h _ (hP.idem B)
  have horth : ⟪P' (B - P B), P B - P' (P B)⟫ = 0 := by
    rw [hP'.symm, map_sub, hP'.idem, sub_self, inner_zero_right]
  have hdec : P' B - P B = P' (B - P B) - (P B - P' (P B)) := by
    rw [map_sub]
    abel
  have hpyth : ‖B‖ ^ 2 = ‖B - P B‖ ^ 2 + ‖P B‖ ^ 2 := by
    have := hP.norm_sub_apply_sq B 0
    simpa using this
  refine abs_le_of_sq_le_sq' ?_ (mul_nonneg hκ (norm_nonneg _)) |>.2
  rw [hdec, norm_sub_sq_real, horth, mul_zero, sub_zero, mul_pow, hpyth, mul_add]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow] at h1 h2
  exact add_le_add h1 h2

/-! ### Two frames -/

variable {P₀' Q₀' : Fin d → E →L[ℝ] E}

/-- **The normal component at a second frame of a tangent vector.** Let `P = modeTangentProj
P₀ Q₀` and `P' = modeTangentProj P₀' Q₀'`. If in every mode `k` the vectors that are tangent with
respect to the first frame, `(1 - P₀ k) (z - Q₀ k z) = 0`, have a normal component with respect
to the second frame of norm at most `c ‖z‖`, then `‖z - P' z‖ ≤ √d c ‖z‖` for all `z` with
`P z = z`. -/
theorem norm_sub_modeTangentProj_apply_le_of_eq_self (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (hP₀' : ∀ i, IsOrthProj (P₀' i))
    (hc₀₀' : ∀ i j x, P₀' i (P₀' j x) = P₀' j (P₀' i x))
    (hQsub' : ∀ i j, j ≠ i → ∀ x, P₀' j (Q₀' i x) = Q₀' i x) {c : ℝ}
    (h : ∀ k z, (1 - P₀ k) (z - Q₀ k z) = 0 → ‖(1 - P₀' k) (z - Q₀' k z)‖ ≤ c * ‖z‖)
    {z : E} (hz : modeTangentProj P₀ Q₀ z = z) :
    ‖z - modeTangentProj P₀' Q₀' z‖ ≤ √d * c * ‖z‖ := by
  rw [mul_assoc]
  refine norm_sub_modeTangentProj_apply_le_sqrt_mul hP₀' hc₀₀' hQsub' fun k => h k z ?_
  have := modeTangentProj_apply_sub_coRange_eq hP₀ hQ₀ hc₀₀ hcQ₀ hQsub k z
  rwa [hz] at this

/-- **The tangent projector on a vector normal at a second frame.** Under the hypotheses of
`norm_sub_modeTangentProj_apply_le_of_eq_self` with `c ≥ 0`: `‖P N‖ ≤ √d c ‖N‖` for all `N` with
`P' N = 0`. -/
theorem norm_modeTangentProj_apply_le_of_eq_zero (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (hP₀' : ∀ i, IsOrthProj (P₀' i))
    (hQ₀' : ∀ i, IsOrthProj (Q₀' i)) (hc₀₀' : ∀ i j x, P₀' i (P₀' j x) = P₀' j (P₀' i x))
    (hcQ₀' : ∀ i x, Q₀' i (P₀' i x) = P₀' i (Q₀' i x))
    (hQsub' : ∀ i j, j ≠ i → ∀ x, P₀' j (Q₀' i x) = Q₀' i x) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k z, (1 - P₀ k) (z - Q₀ k z) = 0 → ‖(1 - P₀' k) (z - Q₀' k z)‖ ≤ c * ‖z‖)
    {N : E} (hN : modeTangentProj P₀' Q₀' N = 0) :
    ‖modeTangentProj P₀ Q₀ N‖ ≤ √d * c * ‖N‖ :=
  (modeTangentProj_isOrthProj hP₀ hQ₀ hc₀₀ hcQ₀ hQsub).norm_apply_le_of_norm_sub_apply_le
    (modeTangentProj_isOrthProj hP₀' hQ₀' hc₀₀' hcQ₀' hQsub')
    (mul_nonneg (Real.sqrt_nonneg _) hc)
    (fun _ hz => norm_sub_modeTangentProj_apply_le_of_eq_self hP₀ hQ₀ hc₀₀ hcQ₀ hQsub hP₀' hc₀₀'
      hQsub' h hz) hN

/-- **Lipschitz bound of the tangent projector of the Tucker manifold from the bounds of the
modes.** Let `P = modeTangentProj P₀ Q₀` and `P' = modeTangentProj P₀' Q₀'`. If in every mode the
vectors tangent with respect to one frame have a normal component with respect to the other
frame of norm at most `c` times their norm, then `‖P' B - P B‖ ≤ √d c ‖B‖` for all `B`. -/
theorem norm_modeTangentProj_sub_le (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (hP₀' : ∀ i, IsOrthProj (P₀' i))
    (hQ₀' : ∀ i, IsOrthProj (Q₀' i)) (hc₀₀' : ∀ i j x, P₀' i (P₀' j x) = P₀' j (P₀' i x))
    (hcQ₀' : ∀ i x, Q₀' i (P₀' i x) = P₀' i (Q₀' i x))
    (hQsub' : ∀ i j, j ≠ i → ∀ x, P₀' j (Q₀' i x) = Q₀' i x) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k z, (1 - P₀ k) (z - Q₀ k z) = 0 → ‖(1 - P₀' k) (z - Q₀' k z)‖ ≤ c * ‖z‖)
    (h' : ∀ k z, (1 - P₀' k) (z - Q₀' k z) = 0 → ‖(1 - P₀ k) (z - Q₀ k z)‖ ≤ c * ‖z‖)
    (B : E) :
    ‖modeTangentProj P₀' Q₀' B - modeTangentProj P₀ Q₀ B‖ ≤ √d * c * ‖B‖ :=
  (modeTangentProj_isOrthProj hP₀ hQ₀ hc₀₀ hcQ₀ hQsub).norm_sub_apply_le_of_norm_sub_apply_le
    (modeTangentProj_isOrthProj hP₀' hQ₀' hc₀₀' hcQ₀' hQsub')
    (mul_nonneg (Real.sqrt_nonneg _) hc)
    (fun _ hz => norm_sub_modeTangentProj_apply_le_of_eq_self hP₀ hQ₀ hc₀₀ hcQ₀ hQsub hP₀' hc₀₀'
      hQsub' h hz)
    (fun _ hz => norm_sub_modeTangentProj_apply_le_of_eq_self hP₀' hQ₀' hc₀₀' hcQ₀' hQsub' hP₀
      hc₀₀ hQsub h' hz) B

/-- Non-vacuity of `norm_modeTangentProj_sub_le` with two different projectors: one mode on `ℝ`,
the frame of the identities (`P = 1`) and the frame of the zero maps (`P' = 0`), `c = 1`. The
bound `‖P' B - P B‖ ≤ √1 · 1 · ‖B‖` holds with equality. -/
example (B : ℝ) :
    ‖modeTangentProj (fun _ : Fin 1 => (0 : ℝ →L[ℝ] ℝ)) (fun _ => 0) B -
      modeTangentProj (fun _ : Fin 1 => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) B‖ ≤
        √(1 : ℕ) * 1 * ‖B‖ := by
  have h0 : IsOrthProj (0 : ℝ →L[ℝ] ℝ) := ⟨fun _ => rfl, fun _ _ => by simp⟩
  refine norm_modeTangentProj_sub_le (fun _ => IsOrthProj.one) (fun _ => IsOrthProj.one)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun i j hji => absurd (Subsingleton.elim j i) hji)
    (fun _ => h0) (fun _ => h0) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun i j hji => absurd (Subsingleton.elim j i) hji) zero_le_one (fun _ z _ => ?_)
    (fun _ z hz => ?_) B
  · simp
  · have hz0 : z = 0 := by simpa using hz
    simp [hz0]

end ModeTangentNormal

end LeanDLRA
