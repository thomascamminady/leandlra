import LeanDLRA.Tensor.TT.TangentProjector
import LeanDLRA.Tensor.Tucker.NormalSecondOrder

/-!
# The normal component of a nearby vector for the tensor-train tangent projector

For orthogonal interface projectors `Ql k` (`P_{≤k}`, nested, `Ql 0 = 1`) and `Qr k` (`P_{>k}`),
the tensor-train tangent projector `P = ttTangentSum Ql Qr (n + 1)` has the normal projector

  `1 - P = ∑_{k < n} (Ql k - Ql (k + 1)) (1 - Qr (k + 1))`,

an orthogonal sum over the `n` interfaces. This file shows: if `y` is fixed by all interface
projectors and `z` satisfies at every interface

  `σ ‖(Ql k - Ql (k + 1)) (1 - Qr (k + 1)) z‖ ≤
    ‖(Ql k - Ql (k + 1)) z‖ ‖Ql k (1 - Qr (k + 1)) z‖`,

then `(σ² - ‖z - y‖²) ‖z - P z‖² ≤ ‖z - y‖⁴ / 2` for every number of modes. The hypothesis is
the statement `‖A M B‖ ≤ ρ⁻¹ ‖A M‖ ‖M B‖` of `norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul`
for the `k`-th unfolding `M` of `Ql k z`, whose rank is at most the `k`-th rank of the tensor
train; this file does not carry out the matricization. The bounds of
[BachmayrEisenmannUschmajew2025, Prop. 4.11] for the normal component has the factor
`√(d - 1)`.

## Main results

* `LeanDLRA.Tensor.sub_ttTangentSum_apply_eq_sum`: the normal component as the sum over the
  interfaces.
* `LeanDLRA.Tensor.norm_sq_sub_ttTangentSum_apply_eq`: its squared norm is the sum of the squared
  norms of the interface parts.
* `LeanDLRA.Tensor.sub_mul_norm_sq_sub_ttTangentSum_apply_le`: the bound above.

## References

* [LubichOseledetsVandereycken2015]
* [BachmayrEisenmannUschmajew2025, Prop. 4.11]
-/

open Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.Tensor

section TTNormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ql Qr : ℕ → E →L[ℝ] E}
  {n : ℕ}

/-- **The normal component for the tensor-train tangent projector.** For interface operators
with `Ql 0 = 1` and `Qr (n + 1) = 1`:
`z - P z = ∑_{k < n} (Ql k - Ql (k + 1)) (z - Qr (k + 1) z)`. -/
theorem sub_ttTangentSum_apply_eq_sum (hl0 : Ql 0 = 1) (hrd : Qr (n + 1) = 1) (z : E) :
    z - ttTangentSum Ql Qr (n + 1) z =
      ∑ k ∈ range n, (Ql k (z - Qr (k + 1) z) - Ql (k + 1) (z - Qr (k + 1) z)) := by
  have hP : ttTangentSum Ql Qr (n + 1) z =
      ∑ k ∈ range n, (Ql k (Qr (k + 1) z) - Ql (k + 1) (Qr (k + 1) z)) + Ql n z := by
    simp [ttTangentSum, Finset.sum_range_succ, hrd, Finset.sum_sub_distrib]
    abel
  have htel : ∑ k ∈ range n, (Ql k z - Ql (k + 1) z) + Ql n z = z := by
    rw [Finset.sum_range_sub' (fun k => Ql k z), hl0]
    simp
  have h : z - ttTangentSum Ql Qr (n + 1) z =
      (∑ k ∈ range n, (Ql k z - Ql (k + 1) z) + Ql n z) -
        (∑ k ∈ range n, (Ql k (Qr (k + 1) z) - Ql (k + 1) (Qr (k + 1) z)) + Ql n z) := by
    rw [htel, hP]
  rw [h, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_sub]
  abel

/-- **The interface parts of the normal component are orthogonal.** For orthogonal interface
projectors `Ql k` with nested ranges, `Ql 0 = 1` and `Qr (n + 1) = 1`:
`‖z - P z‖² = ∑_{k < n} ‖(Ql k - Ql (k + 1)) (z - Qr (k + 1) z)‖²`. -/
theorem norm_sq_sub_ttTangentSum_apply_eq (hQl : ∀ k, IsOrthProj (Ql k)) (hl0 : Ql 0 = 1)
    (hrd : Qr (n + 1) = 1) (hlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) (z : E) :
    ‖z - ttTangentSum Ql Qr (n + 1) z‖ ^ 2 =
      ∑ k ∈ range n, ‖Ql k (z - Qr (k + 1) z) - Ql (k + 1) (z - Qr (k + 1) z)‖ ^ 2 := by
  have hlrA : ∀ k x, Ql k (Ql (k + 1) x) = Ql (k + 1) x := fun k x =>
    congrArg (fun T => T x) (hlr k)
  have hlkA : ∀ k x, Ql (k + 1) (Ql k x) = Ql (k + 1) x := fun k x => by
    refine ext_inner_right ℝ fun w => ?_
    rw [(hQl (k + 1)).symm, (hQl k).symm, hlrA, ← (hQl (k + 1)).symm]
  have hdown : ∀ m k, k ≤ m → ∀ x, Ql m (Ql k x) = Ql m x := by
    intro m
    induction m with
    | zero =>
      intro k hk x
      obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact (hQl 0).idem x
    | succ m ih =>
      intro k hk x
      rcases Nat.lt_or_ge k (m + 1) with h | h
      · rw [← hlkA m (Ql k x), ih k (Nat.lt_succ_iff.1 h) x, hlkA]
      · obtain rfl : k = m + 1 := le_antisymm hk h
        exact (hQl (m + 1)).idem x
  rw [sub_ttTangentSum_apply_eq_sum hl0 hrd]
  obtain ⟨v, hv⟩ : ∃ v : ℕ → E, ∀ k,
      v k = Ql k (z - Qr (k + 1) z) - Ql (k + 1) (z - Qr (k + 1) z) := ⟨_, fun _ => rfl⟩
  simp only [← hv]
  have hkill : ∀ m, Ql m (∑ k ∈ range m, v k) = 0 := fun m => by
    rw [map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [hv, map_sub, hdown m k hk'.le, hdown m (k + 1) hk', sub_self]
  have hfix : ∀ m, Ql m (v m) = v m := fun m => by
    rw [hv, map_sub, (hQl m).idem, hlrA]
  have key : ∀ m, ‖∑ k ∈ range m, v k‖ ^ 2 = ∑ k ∈ range m, ‖v k‖ ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h0 : ⟪∑ k ∈ range m, v k, v m⟫ = 0 := by
        rw [← hfix m, ← (hQl m).symm, hkill m, inner_zero_left]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, norm_add_sq_real, ih, h0]
      ring
  exact key n

/-- **The normal component of a nearby vector for the tensor-train tangent projector.** Let
`Ql k`, `Qr k` be orthogonal interface projectors with nested left ranges, `Ql 0 = 1`,
`Qr (n + 1) = 1`, left and right projectors commuting, and `P = ttTangentSum Ql Qr (n + 1)`.
Let `y` be fixed by all interface projectors and let `z` satisfy, with a number `σ ≥ 0`,

  `σ ‖(Ql k - Ql (k + 1)) (z - Qr (k + 1) z)‖ ≤
    ‖(Ql k - Ql (k + 1)) z‖ ‖Ql k (z - Qr (k + 1) z)‖`

at every interface `k < n`. Then `(σ² - ‖z - y‖²) ‖z - P z‖² ≤ ‖z - y‖⁴ / 2`, for every number
`n` of interfaces. -/
theorem sub_mul_norm_sq_sub_ttTangentSum_apply_le (hQl : ∀ k, IsOrthProj (Ql k))
    (hQr : ∀ k, IsOrthProj (Qr k)) (hl0 : Ql 0 = 1) (hrd : Qr (n + 1) = 1)
    (hcomm : ∀ j k, j ≤ k → Ql j * Qr k = Qr k * Ql j)
    (hlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) {y z : E} (hly : ∀ k, Ql k y = y)
    (hry : ∀ k, Qr k y = y) {σ : ℝ} (hσ : 0 ≤ σ)
    (hm : ∀ k < n, σ * ‖Ql k (z - Qr (k + 1) z) - Ql (k + 1) (z - Qr (k + 1) z)‖ ≤
      ‖Ql k z - Ql (k + 1) z‖ * ‖Ql k (z - Qr (k + 1) z)‖) :
    (σ ^ 2 - ‖z - y‖ ^ 2) * ‖z - ttTangentSum Ql Qr (n + 1) z‖ ^ 2 ≤ ‖z - y‖ ^ 4 / 2 := by
  have hlrA : ∀ k x, Ql k (Ql (k + 1) x) = Ql (k + 1) x := fun k x =>
    congrArg (fun T => T x) (hlr k)
  have hlkA : ∀ k x, Ql (k + 1) (Ql k x) = Ql (k + 1) x := fun k x => by
    refine ext_inner_right ℝ fun w => ?_
    rw [(hQl (k + 1)).symm, (hQl k).symm, hlrA, ← (hQl (k + 1)).symm]
  have hpyth : ∀ {T : E →L[ℝ] E}, IsOrthProj T → ∀ w, ‖w‖ ^ 2 = ‖w - T w‖ ^ 2 + ‖T w‖ ^ 2 :=
    fun hT w => by
      have h := hT.norm_sub_apply_sq w 0
      simpa only [map_zero, sub_zero] using h
  have h := sub_mul_sum_sq_le_of_chain (e := ‖z - y‖) (σ := σ)
    (a := fun i : Fin n => ‖Ql i z - Ql ((i : ℕ) + 1) z‖)
    (b := fun i : Fin n => ‖Ql i (z - Qr ((i : ℕ) + 1) z)‖)
    (t := fun i : Fin n => ‖Ql i (z - Qr ((i : ℕ) + 1) z) -
      Ql ((i : ℕ) + 1) (z - Qr ((i : ℕ) + 1) z)‖)
    (c := fun k => ‖Ql k (z - y)‖ ^ 2) hσ (fun _ => norm_nonneg _) (fun _ => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) ((hQl k).norm_le _) 2)
    (fun i => by
      have h1 := hpyth (hQl ((i : ℕ) + 1)) (Ql i (z - y))
      rw [hlkA] at h1
      have e : Ql i z - Ql ((i : ℕ) + 1) z = Ql i (z - y) - Ql ((i : ℕ) + 1) (z - y) := by
        rw [map_sub, map_sub, hly, hly]
        abel
      rw [e]
      linarith)
    (fun i => by
      have h1 := hpyth (hQl ((i : ℕ) + 1)) (Ql i (z - Qr ((i : ℕ) + 1) z))
      rw [hlkA] at h1
      have e : Ql ((i : ℕ) + 1) (z - Qr ((i : ℕ) + 1) z) =
          Ql ((i : ℕ) + 1) (z - y) - Qr ((i : ℕ) + 1) (Ql ((i : ℕ) + 1) (z - y)) := by
        have hc : Ql ((i : ℕ) + 1) (Qr ((i : ℕ) + 1) z) =
            Qr ((i : ℕ) + 1) (Ql ((i : ℕ) + 1) z) :=
          congrArg (fun T => T z) (hcomm ((i : ℕ) + 1) ((i : ℕ) + 1) le_rfl)
        rw [map_sub, map_sub, map_sub, hly, hry, hc]
        abel
      have h2 := hpyth (hQr ((i : ℕ) + 1)) (Ql ((i : ℕ) + 1) (z - y))
      rw [← e] at h2
      nlinarith [sq_nonneg ‖Qr ((i : ℕ) + 1) (Ql ((i : ℕ) + 1) (z - y))‖])
    (fun i => hm i i.2)
  rw [norm_sq_sub_ttTangentSum_apply_eq hQl hl0 hrd hlr,
    ← Fin.sum_univ_eq_sum_range (fun k => ‖Ql k (z - Qr (k + 1) z) -
      Ql (k + 1) (z - Qr (k + 1) z)‖ ^ 2) n]
  exact h

/-- Non-vacuity of `sub_mul_norm_sq_sub_ttTangentSum_apply_le`: on the real line with all
interface projectors equal to `1`, one interface, `y = 1`, `z = 2`, `σ = 2`; all hypotheses hold
(the normal component is zero, since the tangent space is the whole line). -/
example : ((2 : ℝ) ^ 2 - ‖(2 : ℝ) - 1‖ ^ 2) *
    ‖(2 : ℝ) - ttTangentSum (fun _ => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) (1 + 1) 2‖ ^ 2 ≤
      ‖(2 : ℝ) - 1‖ ^ 4 / 2 :=
  sub_mul_norm_sq_sub_ttTangentSum_apply_le (fun _ => IsOrthProj.one) (fun _ => IsOrthProj.one)
    rfl rfl (fun _ _ _ => rfl) (fun _ => by simp) (fun _ => rfl) (fun _ => rfl) zero_le_two
    (fun k _ => by simp)

end TTNormal

end LeanDLRA.Tensor
