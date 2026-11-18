import LeanDLRA.Tensor.Tucker.NormalSecondOrder

/-!
# Tangent vectors at one Tucker frame are almost tangent at a nearby one: the abstract form

Let `P = modeTangentProj P₀ Q₀` be the tangent projector of the mode projectors `P₀ i` and the
co-range projectors `Q₀ i` of a Tucker tensor `y` with `d` modes, and let `P' i`, `Q' i` be the
mode and co-range projectors of a second Tucker tensor `x`. `LeanDLRA.norm_modeTangentProj_sub_le`
bounds the normal component at `y` of a vector `T` tangent at `x` by `√d c ‖T‖` if it is at most
`c ‖T‖` in every mode. This file has a bound without the factor `√d`:

  `σ ‖T - P T‖ ≤ 2 ‖x - y‖ ‖T‖`,

under two hypotheses in every mode that are instances of `‖A M B‖ ≤ ρ⁻¹ ‖A M‖ ‖M B‖` for the
matricization `M` of `x` and of its prefix projection `P₀ 0 ⋯ P₀ (i - 1) x`. This file does not
carry out the matricization.

## Main results

* `LeanDLRA.sum_norm_modePrefix_sub_sq_le`: `∑ᵢ ‖(1 - P i) (P 0 ⋯ P (i - 1)) w‖² ≤ ‖w‖²` for
  commuting orthogonal projectors.
* `LeanDLRA.sum_norm_sub_apply_sq_le_of_apply_sub_eq`: `∑ᵢ ‖(1 - P' i) T‖² ≤ ‖T‖²` if
  `(1 - P' i) (1 - P' j) T = 0` for `i ≠ j`.
* `LeanDLRA.mul_norm_sub_modeTangentProj_apply_le_two_mul`: the bound above.

## Implementation notes

The normal component at `y` is the orthogonal sum of the parts
`tᵢ = Rᵢ (1 - P₀ i) (1 - Q₀ i) T`, `Rᵢ = P₀ 0 ⋯ P₀ (i - 1)`
(`norm_sq_sub_modeTangentProj_apply_eq`). A vector tangent at `x` is
`T = P' i T + Q' i (1 - P' i) T`, so

  `tᵢ = (1 - P₀ i) P' i (Rᵢ (1 - Q₀ i) T) + Rᵢ (1 - Q₀ i) Q' i ((1 - P₀ i) (1 - P' i) T)`.

The first hypothesis bounds the first summand by `‖(1 - P₀ i) Rᵢ x‖ ‖T‖ / σ`, the second one the
second summand by `‖Rᵢ (1 - Q₀ i) x‖ ‖(1 - P' i) T‖ / σ`. The squares of `‖(1 - P₀ i) Rᵢ x‖ =
‖(1 - P₀ i) Rᵢ (x - y)‖` sum to at most `‖x - y‖²` and the squares of `‖(1 - P' i) T‖` to at most
`‖T‖²`.

## References

* [BachmayrEisenmannUschmajew2025, Props. 4.2 and 4.7]
-/

open Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

/-- **Prefix products of commuting orthogonal projectors split a vector orthogonally.**
`∑ᵢ ‖Rᵢ w - P i (Rᵢ w)‖² ≤ ‖w‖²` for `Rᵢ = P 0 ⋯ P (i - 1)`. -/
theorem sum_norm_modePrefix_sub_sq_le {P : Fin d → E →L[ℝ] E} (hP : ∀ i, IsOrthProj (P i))
    (hc : ∀ i j x, P i (P j x) = P j (P i x)) (w : E) :
    ∑ i : Fin d, ‖modePrefix P i w - P i (modePrefix P i w)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have hterm : ∀ i : Fin d, ‖modePrefix P i w - P i (modePrefix P i w)‖ ^ 2 =
      ‖modePrefix P i w‖ ^ 2 - ‖modePrefix P ((i : ℕ) + 1) w‖ ^ 2 := fun i => by
    have h := (hP i).norm_sub_apply_sq (modePrefix P i w) 0
    simp only [map_zero, sub_zero] at h
    have e : modePrefix P ((i : ℕ) + 1) w = P i (modePrefix P i w) := by
      rw [modePrefix_succ_of_lt P i.2]
      exact (apply_modePrefix_apply_comm (P i) i (fun j _ x => hc i j x) w).symm
    rw [e]
    linarith
  have h0 : modePrefix P 0 w = w :=
    modePrefix_apply_eq_self 0 fun j hj => absurd hj (Nat.not_lt_zero _)
  calc ∑ i : Fin d, ‖modePrefix P i w - P i (modePrefix P i w)‖ ^ 2
      = ∑ i : Fin d, (‖modePrefix P i w‖ ^ 2 - ‖modePrefix P ((i : ℕ) + 1) w‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ k ∈ range d, (‖modePrefix P k w‖ ^ 2 - ‖modePrefix P (k + 1) w‖ ^ 2) :=
        Fin.sum_univ_eq_sum_range
          (fun k => ‖modePrefix P k w‖ ^ 2 - ‖modePrefix P (k + 1) w‖ ^ 2) d
    _ = ‖modePrefix P 0 w‖ ^ 2 - ‖modePrefix P d w‖ ^ 2 :=
        Finset.sum_range_sub' (fun k => ‖modePrefix P k w‖ ^ 2) d
    _ ≤ ‖w‖ ^ 2 := by rw [h0]; linarith [sq_nonneg ‖modePrefix P d w‖]

/-- **The mode parts of a tangent vector.** Let `P' i` be orthogonal projectors and `T` a vector
with `(1 - P' i) (1 - P' j) T = 0` for `i ≠ j` (a tangent vector of the Tucker manifold with
the mode projectors `P' i`). Then `∑ᵢ ‖T - P' i T‖² ≤ ‖T‖²`. -/
theorem sum_norm_sub_apply_sq_le_of_apply_sub_eq {P' : Fin d → E →L[ℝ] E}
    (hP' : ∀ i, IsOrthProj (P' i)) {T : E}
    (hT : ∀ i j, i ≠ j → P' i (T - P' j T) = T - P' j T) :
    ∑ i, ‖T - P' i T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  have hTw : ∀ i, ⟪T, T - P' i T⟫ = ‖T - P' i T‖ ^ 2 := fun i => by
    have h := (hP' i).norm_sub_apply_sq T 0
    simp only [map_zero, sub_zero] at h
    have h2 : ⟪T, P' i T⟫ = ‖P' i T‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, (hP' i).symm, (hP' i).idem]
    rw [inner_sub_right, real_inner_self_eq_norm_sq, h2]
    linarith
  have horth : ∀ i j, i ≠ j → ⟪T - P' i T, T - P' j T⟫ = 0 := fun i j hij => by
    rw [inner_sub_left, (hP' i).symm, hT i j hij, sub_self]
  have hs1 : ‖∑ i, (T - P' i T)‖ ^ 2 = ∑ i, ‖T - P' i T‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i (fun j _ hji => horth i j (Ne.symm hji))
      (fun h => absurd (Finset.mem_univ i) h), real_inner_self_eq_norm_sq]
  have hs2 : ⟪T, ∑ i, (T - P' i T)⟫ = ∑ i, ‖T - P' i T‖ ^ 2 := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ => hTw i
  have hcs := real_inner_le_norm T (∑ i, (T - P' i T))
  rw [hs2, ← hs1] at hcs
  rw [← hs1]
  rcases (norm_nonneg (∑ i, (T - P' i T))).eq_or_lt with h | h
  · rw [← h]
    nlinarith [sq_nonneg ‖T‖]
  · have hle : ‖∑ i, (T - P' i T)‖ ≤ ‖T‖ :=
      le_of_mul_le_mul_right (by rw [← sq]; exact hcs) h
    exact pow_le_pow_left₀ h.le hle 2

variable {P₀ Q₀ P' Q' : Fin d → E →L[ℝ] E}

/-- **The normal component at one Tucker frame of a vector tangent at another frame.** Let
`P = modeTangentProj P₀ Q₀` be the tangent projector of mode projectors `P₀ i` and co-range
projectors `Q₀ i` (hypotheses of `modeTangentProj_isOrthProj`) fixing `y`. Let `P' i` be
orthogonal projectors and `Q' i` maps
(the mode and co-range projectors of a second frame, at `x`) such that
`P' i` commutes with `Q₀ i` and with `P₀ j`, `j ≠ i`, and `Q' i` commutes with `P₀ i`, and let
`T` satisfy `(1 - P' i) T = Q' i (1 - P' i) T` in every mode and `∑ᵢ ‖(1 - P' i) T‖² ≤ ‖T‖²`
(a tangent vector at the second frame). If in every mode `i`, with `Rᵢ = P₀ 0 ⋯ P₀ (i - 1)`,
for all `S` and `V`,

  `σ ‖(1 - P₀ i) (P' i S)‖ ≤ ‖(1 - P₀ i) (Rᵢ x)‖ ‖P' i S‖`,
  `σ ‖Rᵢ (1 - Q₀ i) (Q' i V)‖ ≤ ‖Rᵢ (1 - Q₀ i) x‖ ‖Q' i V‖`,

then `σ ‖T - P T‖ ≤ 2 ‖x - y‖ ‖T‖`, for every number `d` of modes. -/
theorem mul_norm_sub_modeTangentProj_apply_le_two_mul (hP₀ : ∀ i, IsOrthProj (P₀ i))
    (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (hc₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x))
    (hcQ₀ : ∀ i x, Q₀ i (P₀ i x) = P₀ i (Q₀ i x))
    (hQsub : ∀ i j, j ≠ i → ∀ x, P₀ j (Q₀ i x) = Q₀ i x) (hP' : ∀ i, IsOrthProj (P' i))
    (hc' : ∀ i j, j ≠ i → ∀ x, P' i (P₀ j x) = P₀ j (P' i x))
    (hcP'Q : ∀ i x, P' i (Q₀ i x) = Q₀ i (P' i x))
    (hcQ'P : ∀ i x, Q' i (P₀ i x) = P₀ i (Q' i x)) {x y T : E} (hPy : ∀ i, P₀ i y = y)
    (hQy : ∀ i, Q₀ i y = y) (hT : ∀ i, Q' i (T - P' i T) = T - P' i T)
    (hTsum : ∑ i, ‖T - P' i T‖ ^ 2 ≤ ‖T‖ ^ 2) {σ : ℝ} (hσ : 0 ≤ σ)
    (hI : ∀ (i : Fin d) (S : E), σ * ‖P' i S - P₀ i (P' i S)‖ ≤
      ‖modePrefix P₀ i x - P₀ i (modePrefix P₀ i x)‖ * ‖P' i S‖)
    (hII : ∀ (i : Fin d) (V : E), σ * ‖modePrefix P₀ i (Q' i V - Q₀ i (Q' i V))‖ ≤
      ‖modePrefix P₀ i (x - Q₀ i x)‖ * ‖Q' i V‖) :
    σ * ‖T - modeTangentProj P₀ Q₀ T‖ ≤ 2 * ‖x - y‖ * ‖T‖ := by
  have hsub : ∀ {P : E →L[ℝ] E}, IsOrthProj P → ∀ w, ‖w - P w‖ ≤ ‖w‖ := fun {P} hP w => by
    have h := hP.norm_sub_apply_sq w 0
    simp only [map_zero, sub_zero] at h
    exact (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖P w‖]) (norm_nonneg _)).2
  have hstep : ∀ i : Fin d, σ * ‖modePrefix P₀ i ((1 - P₀ i) (T - Q₀ i T))‖ ≤
      ‖modePrefix P₀ i (x - y) - P₀ i (modePrefix P₀ i (x - y))‖ * ‖T‖ +
        ‖x - y‖ * ‖T - P' i T‖ := by
    intro i
    have cRP : ∀ w, P₀ i (modePrefix P₀ i w) = modePrefix P₀ i (P₀ i w) := fun w =>
      apply_modePrefix_apply_comm (P₀ i) i (fun j _ z => hc₀₀ i j z) w
    have cRP' : ∀ w, P' i (modePrefix P₀ i w) = modePrefix P₀ i (P' i w) := fun w =>
      apply_modePrefix_apply_comm (P' i) i
        (fun j hj z => hc' i j (fun hji => by rw [hji] at hj; exact lt_irrefl _ hj) z) w
    obtain ⟨S, hS⟩ : ∃ S, S = modePrefix P₀ i (T - Q₀ i T) := ⟨_, rfl⟩
    obtain ⟨V, hV⟩ : ∃ V, V = (T - P' i T) - P₀ i (T - P' i T) := ⟨_, rfl⟩
    have hQV : Q' i V = V := by rw [hV, map_sub, hcQ'P, hT i]
    have key : (1 - P₀ i) (T - Q₀ i T) =
        (P' i (T - Q₀ i T) - P₀ i (P' i (T - Q₀ i T))) + (V - Q₀ i V) := by
      rw [hV]
      simp only [sub_apply, one_apply_eq_self, map_sub,
        hcP'Q i, hcQ₀ i]
      abel
    have hdec : modePrefix P₀ i ((1 - P₀ i) (T - Q₀ i T)) =
        (P' i S - P₀ i (P' i S)) + modePrefix P₀ i (Q' i V - Q₀ i (Q' i V)) := by
      rw [key, map_add, hQV, hS, cRP', cRP, ← map_sub]
    have hy : modePrefix P₀ i y = y := modePrefix_apply_eq_self i fun j _ => hPy j
    have ha : modePrefix P₀ i x - P₀ i (modePrefix P₀ i x) =
        modePrefix P₀ i (x - y) - P₀ i (modePrefix P₀ i (x - y)) := by
      rw [map_sub, map_sub, hy, hPy]
      abel
    have hb : ‖modePrefix P₀ i (x - Q₀ i x)‖ ≤ ‖x - y‖ := by
      have e : x - Q₀ i x = (x - y) - Q₀ i (x - y) := by
        rw [map_sub, hQy]
        abel
      rw [e]
      exact (norm_modePrefix_apply_le_norm hP₀ i _).trans (hsub (hQ₀ i) _)
    have hS1 : ‖P' i S‖ ≤ ‖T‖ := by
      refine ((hP' i).norm_le S).trans ?_
      rw [hS]
      exact (norm_modePrefix_apply_le_norm hP₀ i _).trans (hsub (hQ₀ i) T)
    have hV1 : ‖Q' i V‖ ≤ ‖T - P' i T‖ := by
      rw [hQV, hV]
      exact hsub (hP₀ i) _
    have h1 := hI i S
    have h2 := hII i V
    rw [hdec]
    calc σ * ‖(P' i S - P₀ i (P' i S)) + modePrefix P₀ i (Q' i V - Q₀ i (Q' i V))‖
        ≤ σ * (‖P' i S - P₀ i (P' i S)‖ + ‖modePrefix P₀ i (Q' i V - Q₀ i (Q' i V))‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hσ
      _ = σ * ‖P' i S - P₀ i (P' i S)‖ +
            σ * ‖modePrefix P₀ i (Q' i V - Q₀ i (Q' i V))‖ := mul_add _ _ _
      _ ≤ ‖modePrefix P₀ i x - P₀ i (modePrefix P₀ i x)‖ * ‖P' i S‖ +
            ‖modePrefix P₀ i (x - Q₀ i x)‖ * ‖Q' i V‖ := add_le_add h1 h2
      _ ≤ ‖modePrefix P₀ i (x - y) - P₀ i (modePrefix P₀ i (x - y))‖ * ‖T‖ +
            ‖x - y‖ * ‖T - P' i T‖ := by
          rw [ha]
          exact add_le_add (mul_le_mul_of_nonneg_left hS1 (norm_nonneg _))
            (mul_le_mul hb hV1 (norm_nonneg _) (norm_nonneg _))
  have ha := sum_norm_modePrefix_sub_sq_le hP₀ hc₀₀ (x - y)
  have hsq : (σ * ‖T - modeTangentProj P₀ Q₀ T‖) ^ 2 ≤ (2 * ‖x - y‖ * ‖T‖) ^ 2 := by
    rw [mul_pow, norm_sq_sub_modeTangentProj_apply_eq hP₀ hc₀₀ hQsub, Finset.mul_sum]
    calc ∑ i : Fin d, σ ^ 2 * ‖modePrefix P₀ i ((1 - P₀ i) (T - Q₀ i T))‖ ^ 2
        ≤ ∑ i : Fin d,
            (2 * ‖T‖ ^ 2 * ‖modePrefix P₀ i (x - y) - P₀ i (modePrefix P₀ i (x - y))‖ ^ 2 +
              2 * ‖x - y‖ ^ 2 * ‖T - P' i T‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => by
            have h1 := hstep i
            have h2 := pow_le_pow_left₀ (mul_nonneg hσ (norm_nonneg _)) h1 2
            nlinarith [sq_nonneg
              (‖modePrefix P₀ i (x - y) - P₀ i (modePrefix P₀ i (x - y))‖ * ‖T‖ -
                ‖x - y‖ * ‖T - P' i T‖)]
      _ = 2 * ‖T‖ ^ 2 *
              ∑ i : Fin d, ‖modePrefix P₀ i (x - y) - P₀ i (modePrefix P₀ i (x - y))‖ ^ 2 +
            2 * ‖x - y‖ ^ 2 * ∑ i : Fin d, ‖T - P' i T‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (2 * ‖x - y‖ * ‖T‖) ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg ‖T‖) (sub_nonneg.2 ha),
            mul_nonneg (sq_nonneg ‖x - y‖) (sub_nonneg.2 hTsum)]
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- Non-vacuity of `mul_norm_sub_modeTangentProj_apply_le_two_mul`,
`sum_norm_modePrefix_sub_sq_le` and `sum_norm_sub_apply_sq_le_of_apply_sub_eq`: on the real line
with one mode and all projectors equal to `1`, `x = 2`, `y = 1`, `T = 1`, `σ = 1`; all
hypotheses hold (the tangent space is the whole line, so the normal component is zero). -/
example : (1 : ℝ) * ‖(1 : ℝ) - modeTangentProj (fun _ : Fin 1 => (1 : ℝ →L[ℝ] ℝ))
    (fun _ => 1) 1‖ ≤ 2 * ‖(2 : ℝ) - 1‖ * ‖(1 : ℝ)‖ :=
  mul_norm_sub_modeTangentProj_apply_le_two_mul (P' := fun _ => 1) (Q' := fun _ => 1)
    (fun _ => IsOrthProj.one) (fun _ => IsOrthProj.one) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ => IsOrthProj.one)
    (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => by simp)
    (sum_norm_sub_apply_sq_le_of_apply_sub_eq (fun _ => IsOrthProj.one) fun _ _ _ => by simp)
    zero_le_one (fun _ _ => by simp) (fun _ _ => by simp)

end Abstract

end LeanDLRA
