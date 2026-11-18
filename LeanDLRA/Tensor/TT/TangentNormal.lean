import LeanDLRA.Tensor.TT.NormalSecondOrderTrain

/-!
# Tangent vectors at one tensor train are almost tangent at a nearby one

Let `X` and `Y` be tensor trains with `d` modes and the same bond dimensions, with tangent
projectors `P(X)`, `P(Y)` (`ttTangentProj`), and let `0 < ρ` be a lower bound of the singular
values `σ_{|β k|}` of the unfoldings `X⟨k⟩`, `0 < k < d`. This file shows, for all tensors `Z`,

  `‖T - P(Y) T‖ ≤ 2 ρ⁻¹ ‖X - Y‖ ‖T‖`   for `T` tangent at `X`,
  `‖Z - P(Y) Z‖ ≤ ‖Z - P(X) Z‖ + 2 ρ⁻¹ ‖X - Y‖ ‖P(X) Z‖`,

and, if `ρ` is also a lower bound at `Y`, `‖P(Y) Z - P(X) Z‖ ≤ 2 ρ⁻¹ ‖X - Y‖ ‖Z‖`. There is no
smallness condition on `‖X - Y‖`, and the constant `2` does not depend on the number of modes.
The bounds of the difference of the projectors in [BachmayrEisenmannUschmajew2025, Prop. 4.11]
and in Budzinskiy–Zamarashkin (arXiv 2110.03975, Lemma 3.1) have the constants `4 d` and
`2 (d - 1)`.

## Main results

* `LeanDLRA.Tensor.sum_norm_sub_sq_le_of_nested`: `∑_{k < n} ‖(Ql k - Ql (k + 1)) z‖² ≤ ‖z‖²`
  for nested orthogonal projectors.
* `LeanDLRA.Tensor.ttTangentSum_apply_sub_apply_eq`: a vector in the range of the alternating
  sum of nested interface projectors is tangent at every interface,
  `(1 - Pl j) (1 - Pr j) (P W) = 0`.
* `LeanDLRA.Tensor.mul_norm_sub_ttTangentSum_apply_le_two_mul`: the abstract form of the first
  bound, for two families of interface projectors.
* `LeanDLRA.Tensor.mul_norm_actOn_actOn_mul_transpose_le`,
  `LeanDLRA.Tensor.mul_norm_actOn_compl_actOn_compl_mul_transpose_le`: for a tensor `X` whose
  `p`-unfolding has the column space of `U` and smallest singular value at least `ρ`,
  `ρ ‖D (U Uᵀ S)‖ ≤ ‖D X‖ ‖U Uᵀ S‖` for `D` acting on the modes in `p`, and the same for the
  row space and maps acting on the other modes.
* `LeanDLRA.Tensor.mul_norm_sub_ttTangentProj_apply_le_two_mul`,
  `LeanDLRA.Tensor.norm_sub_ttTangentProj_apply_le_add`,
  `LeanDLRA.Tensor.norm_ttTangentProj_sub_le`: the three bounds above.

## Implementation notes

The normal component at `Y` is the orthogonal sum over the interfaces of
`t_k = (P_{≤k} - P_{≤k+1}) (1 - P_{>k+1}) T` (projectors of `Y`). With the projectors
`P'_{≤k+1}`, `P'_{>k+1}` of `X` a tangent vector at `X` is
`T = P'_{>k+1} T + P'_{≤k+1} (1 - P'_{>k+1}) T`. In the unfolding with respect to the first
`k + 1` modes, `P'_{>k+1}` is the projector onto the row space of `M = X⟨k+1⟩` and `P'_{≤k+1}`
the projector onto its column space, so both factor through `M`, and
`‖A M B‖ ≤ ρ⁻¹ ‖A M‖ ‖M B‖` gives

  `ρ ‖t_k‖ ≤ ‖(1 - P_{>k+1}) X‖ ‖(P_{≤k} - P_{≤k+1}) T‖ + ‖(P_{≤k} - P_{≤k+1}) X‖ ‖T‖`.

Here `(1 - P_{>k+1}) X = (1 - P_{>k+1}) (X - Y)` and
`(P_{≤k} - P_{≤k+1}) X = (P_{≤k} - P_{≤k+1}) (X - Y)`, and the squares of
`‖(P_{≤k} - P_{≤k+1}) z‖` sum to at most `‖z‖²`: every part of `X - Y` and of `T` is used at one
interface only.

## References

* [LubichOseledetsVandereycken2015]
* [BachmayrEisenmannUschmajew2025, Prop. 4.11]
* S. Budzinskiy, N. Zamarashkin, arXiv 2110.03975, Lemma 3.1
-/

open Matrix Finset
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Tensor

/-! ### Interface projectors in an inner product space -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Nested orthogonal projectors split a vector orthogonally.** For orthogonal projectors
`Ql k` with nested ranges and `Ql 0 = 1`: `∑_{k < n} ‖Ql k z - Ql (k + 1) z‖² ≤ ‖z‖²`. -/
theorem sum_norm_sub_sq_le_of_nested {Ql : ℕ → E →L[ℝ] E} (hQl : ∀ k, IsOrthProj (Ql k))
    (hl0 : Ql 0 = 1) (hlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) (n : ℕ) (z : E) :
    ∑ k ∈ range n, ‖Ql k z - Ql (k + 1) z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have hlrA : ∀ k x, Ql k (Ql (k + 1) x) = Ql (k + 1) x := fun k x =>
    congrArg (fun T => T x) (hlr k)
  have hlkA : ∀ k x, Ql (k + 1) (Ql k x) = Ql (k + 1) x := fun k x => by
    refine ext_inner_right ℝ fun w => ?_
    rw [(hQl (k + 1)).symm, (hQl k).symm, hlrA, ← (hQl (k + 1)).symm]
  have hterm : ∀ k, ‖Ql k z - Ql (k + 1) z‖ ^ 2 = ‖Ql k z‖ ^ 2 - ‖Ql (k + 1) z‖ ^ 2 :=
    fun k => by
      have h := (hQl (k + 1)).norm_sub_apply_sq (Ql k z) 0
      simp only [map_zero, sub_zero] at h
      rw [hlkA] at h
      linarith
  have h0 : ‖Ql 0 z‖ ^ 2 = ‖z‖ ^ 2 := by rw [hl0]; rfl
  calc ∑ k ∈ range n, ‖Ql k z - Ql (k + 1) z‖ ^ 2
      = ∑ k ∈ range n, (‖Ql k z‖ ^ 2 - ‖Ql (k + 1) z‖ ^ 2) :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ = ‖Ql 0 z‖ ^ 2 - ‖Ql n z‖ ^ 2 := Finset.sum_range_sub' (fun k => ‖Ql k z‖ ^ 2) n
    _ ≤ ‖z‖ ^ 2 := by rw [h0]; linarith [sq_nonneg ‖Ql n z‖]

/-- **Tangent vectors are tangent at every interface.** For orthogonal interface projectors with
nested left ranges, nested right ranges and commuting left and right projectors, a vector
`P W` in the range of the alternating sum `P = ttTangentSum Pl Pr (n + 1)` satisfies
`(1 - Pl j) (1 - Pr j) (P W) = 0` for every `j`. -/
theorem ttTangentSum_apply_sub_apply_eq {Pl Pr : ℕ → E →L[ℝ] E} {n : ℕ}
    (hPl : ∀ k, IsOrthProj (Pl k)) (hPr : ∀ k, IsOrthProj (Pr k))
    (hcomm : ∀ j k, j ≤ k → Pl j * Pr k = Pr k * Pl j)
    (hlr : ∀ k, Pl k * Pl (k + 1) = Pl (k + 1)) (hrr : ∀ k, Pr (k + 1) * Pr k = Pr k) (j : ℕ)
    (W : E) :
    Pl j (ttTangentSum Pl Pr (n + 1) W - Pr j (ttTangentSum Pl Pr (n + 1) W)) =
      ttTangentSum Pl Pr (n + 1) W - Pr j (ttTangentSum Pl Pr (n + 1) W) := by
  have hcA : ∀ a b, a ≤ b → ∀ x, Pl a (Pr b x) = Pr b (Pl a x) := fun a b hab x =>
    congrArg (fun T => T x) (hcomm a b hab)
  have hlrA : ∀ k x, Pl k (Pl (k + 1) x) = Pl (k + 1) x := fun k x =>
    congrArg (fun T => T x) (hlr k)
  have hrrA : ∀ k x, Pr (k + 1) (Pr k x) = Pr k x := fun k x =>
    congrArg (fun T => T x) (hrr k)
  have nestL : ∀ k, j ≤ k → ∀ x, Pl j (Pl k x) = Pl k x := fun k hk => by
    induction k, hk using Nat.le_induction with
    | base => exact fun x => (hPl j).idem x
    | succ k hk ih =>
      intro x
      rw [← hlrA k x]
      exact ih _
  have nestR : ∀ m i, m ≤ i → ∀ x, Pr i (Pr m x) = Pr m x := fun m i hi => by
    induction i, hi using Nat.le_induction with
    | base => exact fun x => (hPr m).idem x
    | succ i hi ih =>
      intro x
      rw [← ih x]
      exact hrrA i _
  obtain ⟨G, hG⟩ : ∃ G : E →L[ℝ] E, ∀ u, G u = (u - Pr j u) - Pl j (u - Pr j u) :=
    ⟨(1 - Pl j) * (1 - Pr j), fun u => rfl⟩
  have key : ∀ k m, k ≤ m → (j ≤ k ∨ m ≤ j) → ∀ x, G (Pl k (Pr m x)) = 0 := by
    rintro k m hkm (h | h) x
    · rw [hG, map_sub, hcA j j le_rfl, nestL k h, sub_self]
    · have e : Pr j (Pl k (Pr m x)) = Pl k (Pr m x) := by
        rw [← hcA k j (hkm.trans h), nestR m j h]
      rw [hG, e, sub_self, map_zero, sub_self]
  have hP : ttTangentSum Pl Pr (n + 1) W =
      ∑ k ∈ range (n + 1), Pl k (Pr (k + 1) W) - ∑ k ∈ range n, Pl (k + 1) (Pr (k + 1) W) := by
    simp [ttTangentSum]
  have h0 : G (ttTangentSum Pl Pr (n + 1) W) = 0 := by
    rw [hP, map_sub, map_sum, map_sum,
      Finset.sum_eq_zero fun k _ => key k (k + 1) (Nat.le_succ k) (by omega) W,
      Finset.sum_eq_zero fun k _ => key (k + 1) (k + 1) le_rfl (by omega) W, sub_self]
  rw [hG] at h0
  exact (sub_eq_zero.1 h0).symm

/-- **The normal component at one frame of a vector tangent at another frame, interface
projectors.** Let `Ql`, `Qr` be orthogonal interface projectors as in
`sub_mul_norm_sq_sub_ttTangentSum_apply_le` with `P = ttTangentSum Ql Qr (n + 1)`, fixing `y`.
Let `Pl`, `Pr` be orthogonal projectors (the interface projectors of a second frame, at `x`)
commuting with the projectors of the first frame that act on the other side, and let `T` be
tangent at every interface of the second frame, `(1 - Pl (k + 1)) (1 - Pr (k + 1)) T = 0`. If at
every interface `k < n`, for all `S` and `V`,

  `ρ ‖(Ql k - Ql (k + 1)) (Pl (k + 1) S)‖ ≤ ‖(Ql k - Ql (k + 1)) x‖ ‖Pl (k + 1) S‖`,
  `ρ ‖(1 - Qr (k + 1)) (Pr (k + 1) V)‖ ≤ ‖(1 - Qr (k + 1)) x‖ ‖Pr (k + 1) V‖`,

then `ρ ‖T - P T‖ ≤ 2 ‖x - y‖ ‖T‖`, for every number `n` of interfaces. -/
theorem mul_norm_sub_ttTangentSum_apply_le_two_mul {Ql Qr Pl Pr : ℕ → E →L[ℝ] E} {n : ℕ}
    (hQl : ∀ k, IsOrthProj (Ql k)) (hQr : ∀ k, IsOrthProj (Qr k)) (hl0 : Ql 0 = 1)
    (hrd : Qr (n + 1) = 1) (hcomm : ∀ j k, j ≤ k → Ql j * Qr k = Qr k * Ql j)
    (hlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) (hPl : ∀ k, IsOrthProj (Pl k))
    (hPr : ∀ k, IsOrthProj (Pr k)) (hQlPr : ∀ j k, j ≤ k → Ql j * Pr k = Pr k * Ql j)
    (hPlQr : ∀ k, Pl k * Qr k = Qr k * Pl k) {x y T : E} (hly : ∀ k, Ql k y = y)
    (hry : ∀ k, Qr k y = y)
    (hT : ∀ k < n, Pl (k + 1) (T - Pr (k + 1) T) = T - Pr (k + 1) T) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hI : ∀ k < n, ∀ S, ρ * ‖Ql k (Pl (k + 1) S) - Ql (k + 1) (Pl (k + 1) S)‖ ≤
      ‖Ql k x - Ql (k + 1) x‖ * ‖Pl (k + 1) S‖)
    (hII : ∀ k < n, ∀ V, ρ * ‖Pr (k + 1) V - Qr (k + 1) (Pr (k + 1) V)‖ ≤
      ‖x - Qr (k + 1) x‖ * ‖Pr (k + 1) V‖) :
    ρ * ‖T - ttTangentSum Ql Qr (n + 1) T‖ ≤ 2 * ‖x - y‖ * ‖T‖ := by
  have hsub : ∀ {P : E →L[ℝ] E}, IsOrthProj P → ∀ w, ‖w - P w‖ ≤ ‖w‖ := fun {P} hP w => by
    have h := hP.norm_sub_apply_sq w 0
    simp only [map_zero, sub_zero] at h
    exact (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖P w‖]) (norm_nonneg _)).2
  have hstep : ∀ k < n, ρ * ‖Ql k (T - Qr (k + 1) T) - Ql (k + 1) (T - Qr (k + 1) T)‖ ≤
      ‖x - y‖ * ‖Ql k T - Ql (k + 1) T‖ +
        ‖Ql k (x - y) - Ql (k + 1) (x - y)‖ * ‖T‖ := by
    intro k hk
    have c1 : ∀ w, Ql k (Qr (k + 1) w) = Qr (k + 1) (Ql k w) := fun w =>
      congrArg (fun F : E →L[ℝ] E => F w) (hcomm k (k + 1) (Nat.le_succ k))
    have c2 : ∀ w, Ql (k + 1) (Qr (k + 1) w) = Qr (k + 1) (Ql (k + 1) w) := fun w =>
      congrArg (fun F : E →L[ℝ] E => F w) (hcomm (k + 1) (k + 1) le_rfl)
    have c3 : ∀ w, Ql k (Pr (k + 1) w) = Pr (k + 1) (Ql k w) := fun w =>
      congrArg (fun F : E →L[ℝ] E => F w) (hQlPr k (k + 1) (Nat.le_succ k))
    have c4 : ∀ w, Ql (k + 1) (Pr (k + 1) w) = Pr (k + 1) (Ql (k + 1) w) := fun w =>
      congrArg (fun F : E →L[ℝ] E => F w) (hQlPr (k + 1) (k + 1) le_rfl)
    have c5 : ∀ w, Pl (k + 1) (Qr (k + 1) w) = Qr (k + 1) (Pl (k + 1) w) := fun w =>
      congrArg (fun F : E →L[ℝ] E => F w) (hPlQr (k + 1))
    obtain ⟨S, hS⟩ : ∃ S, S = T - Pr (k + 1) T := ⟨_, rfl⟩
    have hLS : Pl (k + 1) S = S := by rw [hS]; exact hT k hk
    obtain ⟨V, hV⟩ : ∃ V, V = Ql k T - Ql (k + 1) T := ⟨_, rfl⟩
    obtain ⟨S', hS'⟩ : ∃ S', S' = S - Qr (k + 1) S := ⟨_, rfl⟩
    have hS'' : Pl (k + 1) S' = S' := by rw [hS', map_sub, c5, hLS]
    have hdec : Ql k (T - Qr (k + 1) T) - Ql (k + 1) (T - Qr (k + 1) T) =
        (Pr (k + 1) V - Qr (k + 1) (Pr (k + 1) V)) +
          (Ql k (Pl (k + 1) S') - Ql (k + 1) (Pl (k + 1) S')) := by
      rw [hS'', hS', hV, hS]
      simp only [map_sub, c1, c2, c3, c4]
      abel
    have hx1 : ‖x - Qr (k + 1) x‖ ≤ ‖x - y‖ := by
      have e : x - Qr (k + 1) x = (x - y) - Qr (k + 1) (x - y) := by
        rw [map_sub, hry]
        abel
      rw [e]
      exact hsub (hQr (k + 1)) _
    have hx2 : Ql k x - Ql (k + 1) x = Ql k (x - y) - Ql (k + 1) (x - y) := by
      rw [map_sub, map_sub, hly, hly]
      abel
    have h1 := hII k hk V
    have h2 := hI k hk S'
    have hV1 : ‖Pr (k + 1) V‖ ≤ ‖V‖ := (hPr (k + 1)).norm_le V
    have hS1 : ‖Pl (k + 1) S'‖ ≤ ‖T‖ := by
      refine ((hPl (k + 1)).norm_le S').trans ?_
      rw [hS']
      refine (hsub (hQr (k + 1)) S).trans ?_
      rw [hS]
      exact hsub (hPr (k + 1)) T
    rw [hdec, ← hV]
    calc ρ * ‖(Pr (k + 1) V - Qr (k + 1) (Pr (k + 1) V)) +
          (Ql k (Pl (k + 1) S') - Ql (k + 1) (Pl (k + 1) S'))‖
        ≤ ρ * (‖Pr (k + 1) V - Qr (k + 1) (Pr (k + 1) V)‖ +
            ‖Ql k (Pl (k + 1) S') - Ql (k + 1) (Pl (k + 1) S')‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hρ
      _ = ρ * ‖Pr (k + 1) V - Qr (k + 1) (Pr (k + 1) V)‖ +
            ρ * ‖Ql k (Pl (k + 1) S') - Ql (k + 1) (Pl (k + 1) S')‖ := mul_add _ _ _
      _ ≤ ‖x - Qr (k + 1) x‖ * ‖Pr (k + 1) V‖ +
            ‖Ql k x - Ql (k + 1) x‖ * ‖Pl (k + 1) S'‖ := add_le_add h1 h2
      _ ≤ ‖x - y‖ * ‖V‖ + ‖Ql k (x - y) - Ql (k + 1) (x - y)‖ * ‖T‖ := by
          rw [hx2]
          exact add_le_add (mul_le_mul hx1 hV1 (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hS1 (norm_nonneg _))
  have hα := sum_norm_sub_sq_le_of_nested hQl hl0 hlr n T
  have ha := sum_norm_sub_sq_le_of_nested hQl hl0 hlr n (x - y)
  have hsq : (ρ * ‖T - ttTangentSum Ql Qr (n + 1) T‖) ^ 2 ≤ (2 * ‖x - y‖ * ‖T‖) ^ 2 := by
    rw [mul_pow, norm_sq_sub_ttTangentSum_apply_eq hQl hl0 hrd hlr, Finset.mul_sum]
    calc ∑ k ∈ range n,
          ρ ^ 2 * ‖Ql k (T - Qr (k + 1) T) - Ql (k + 1) (T - Qr (k + 1) T)‖ ^ 2
        ≤ ∑ k ∈ range n, (2 * ‖x - y‖ ^ 2 * ‖Ql k T - Ql (k + 1) T‖ ^ 2 +
            2 * ‖T‖ ^ 2 * ‖Ql k (x - y) - Ql (k + 1) (x - y)‖ ^ 2) :=
          Finset.sum_le_sum fun k hk => by
            have h1 := hstep k (Finset.mem_range.1 hk)
            have h2 := pow_le_pow_left₀ (mul_nonneg hρ (norm_nonneg _)) h1 2
            nlinarith [sq_nonneg (‖x - y‖ * ‖Ql k T - Ql (k + 1) T‖ -
              ‖Ql k (x - y) - Ql (k + 1) (x - y)‖ * ‖T‖)]
      _ = 2 * ‖x - y‖ ^ 2 * ∑ k ∈ range n, ‖Ql k T - Ql (k + 1) T‖ ^ 2 +
            2 * ‖T‖ ^ 2 * ∑ k ∈ range n, ‖Ql k (x - y) - Ql (k + 1) (x - y)‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (2 * ‖x - y‖ * ‖T‖) ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg ‖x - y‖) (sub_nonneg.2 hα),
            mul_nonneg (sq_nonneg ‖T‖) (sub_nonneg.2 ha)]
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- **The normal component at a second projector.** For orthogonal projectors `P`, `P'` such
that `‖T - P' T‖ ≤ κ ‖T‖` for all `T` in the range of `P`:
`‖z - P' z‖ ≤ ‖z - P z‖ + κ ‖P z‖` for all `z`. -/
theorem _root_.LeanDLRA.IsOrthProj.norm_sub_apply_le_add_of_norm_sub_apply_le
    {P P' : E →L[ℝ] E} (hP : IsOrthProj P) (hP' : IsOrthProj P') {κ : ℝ}
    (h : ∀ T, P T = T → ‖T - P' T‖ ≤ κ * ‖T‖) (z : E) :
    ‖z - P' z‖ ≤ ‖z - P z‖ + κ * ‖P z‖ := by
  have h1 : ‖(z - P z) - P' (z - P z)‖ ≤ ‖z - P z‖ := by
    have h2 := hP'.norm_sub_apply_sq (z - P z) 0
    simp only [map_zero, sub_zero] at h2
    exact (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖P' (z - P z)‖]) (norm_nonneg _)).2
  have e : z - P' z = ((z - P z) - P' (z - P z)) + (P z - P' (P z)) := by
    rw [map_sub]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h1 (h _ (hP.idem z)))

end Abstract

end LeanDLRA.Tensor

namespace LeanDLRA

/-! ### A matrix with a positive singular value has full rank -/

section Rank

open Curvature EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- A matrix of rank at most `q` whose singular value `σ_{q-1}` is positive has rank `q`. -/
theorem rank_eq_of_pos_of_le_singularValues {q : ℕ} {M : Matrix m n ℝ} (hM : M.rank ≤ q)
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ρ ≤ (toEuclideanLin M).singularValues (q - 1)) :
    M.rank = q := by
  refine le_antisymm hM ?_
  by_contra hlt
  have h0 := (singularValues_le_specNorm_sub M M (r := q - 1) (by omega)).trans
    (specNorm_le_frob _)
  rw [sub_self, norm_zero] at h0
  linarith

end Rank

namespace Tensor

/-! ### Projectors onto the column space and the row space of an unfolding -/

section Unfold

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- A matrix acting on a subset `q` of the modes in `p` is a matrix acting on the modes in
`p`. -/
theorem exists_actOn_eq_actOn_of_imp {p q : κ → Prop} [DecidablePred p] [DecidablePred q]
    (hqp : ∀ k, q k → p k) (M : Matrix (∀ k : Subtype q, ι k) (∀ k : Subtype q, ι k) ℝ) :
    ∃ M' : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ,
      ∀ X : Tensor ι, actOn q M X = actOn p M' X := by
  obtain ⟨M', h⟩ := exists_unfold_actOn_eq_mul_of_imp (p := p) hqp M
  exact ⟨M', fun X => unfold_injective p (by rw [h X, unfold_actOn])⟩

variable [∀ k, DecidableEq (ι k)]

/-- **A map acting on the row modes, after the projector onto the column space of an
unfolding.** Let `U Uᵀ` (acting on the modes in `p`) fix `X`, with `U` having `|r|` columns, and
let `0 < ρ ≤ σ_{|r|}(Mat_p(X))`. For every matrix `D` acting on the modes in `p` and every
tensor `S`: `ρ ‖D (U Uᵀ S)‖ ≤ ‖D X‖ ‖U Uᵀ S‖`. -/
theorem mul_norm_actOn_actOn_mul_transpose_le (p : κ → Prop) [DecidablePred p] {r : Type*}
    [Fintype r] {U : Matrix (∀ k : Subtype p, ι k) r ℝ} {X : Tensor ι}
    (hfix : actOn p (U * Uᵀ) X = X) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin (unfold p X)).singularValues (Fintype.card r - 1))
    (D : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ) (S : Tensor ι) :
    ρ * ‖actOn p D (actOn p (U * Uᵀ) S)‖ ≤ ‖actOn p D X‖ * ‖actOn p (U * Uᵀ) S‖ := by
  have hfixM : U * Uᵀ * unfold p X = unfold p X := by rw [← unfold_actOn, hfix]
  have hrk : (unfold p X).rank ≤ Fintype.card r := by
    rw [← hfixM, Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  have hr := rank_eq_of_pos_of_le_singularValues hrk hρ hσ
  obtain ⟨C, hC⟩ := Matrix.exists_rangeProj_eq_mul (unfold p X)
  rw [rangeProj_eq_mul_transpose_of_rank_eq hfixM hr] at hC
  have e3 : unfold p (actOn p D (actOn p (U * Uᵀ) S)) =
      D * unfold p X * (C * unfold p S) := by
    rw [unfold_actOn, unfold_actOn, hC]
    simp only [Matrix.mul_assoc]
  have e2 : unfold p (actOn p (U * Uᵀ) S) = unfold p X * (C * unfold p S) := by
    rw [unfold_actOn, hC, Matrix.mul_assoc]
  have e1 : unfold p (actOn p D X) = D * unfold p X := unfold_actOn p D X
  have h := norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul hrk hρ hσ D (C * unfold p S)
  rw [← e3, ← e2, ← e1, norm_unfold, norm_unfold, norm_unfold] at h
  calc ρ * ‖actOn p D (actOn p (U * Uᵀ) S)‖
      ≤ ρ * (ρ⁻¹ * ‖actOn p D X‖ * ‖actOn p (U * Uᵀ) S‖) :=
        mul_le_mul_of_nonneg_left h hρ.le
    _ = ‖actOn p D X‖ * ‖actOn p (U * Uᵀ) S‖ := by
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]

/-- **A map acting on the column modes, after the projector onto the row space of an
unfolding.** Let `W Wᵀ` (acting on the modes outside `p`) fix `X`, with `W` having `|r|`
columns, and let `0 < ρ ≤ σ_{|r|}(Mat_p(X))`. For every matrix `N` acting on the modes outside
`p` and every tensor `V`: `ρ ‖N (W Wᵀ V)‖ ≤ ‖N X‖ ‖W Wᵀ V‖`. -/
theorem mul_norm_actOn_compl_actOn_compl_mul_transpose_le (p : κ → Prop) [DecidablePred p]
    {r : Type*} [Fintype r] {W : Matrix (∀ k : {k // ¬ p k}, ι k) r ℝ}
    {X : Tensor ι} (hfix : actOn (fun k => ¬ p k) (W * Wᵀ) X = X) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin (unfold p X)).singularValues (Fintype.card r - 1))
    (N : Matrix (∀ k : {k // ¬ p k}, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ) (V : Tensor ι) :
    ρ * ‖actOn (fun k => ¬ p k) N (actOn (fun k => ¬ p k) (W * Wᵀ) V)‖ ≤
      ‖actOn (fun k => ¬ p k) N X‖ * ‖actOn (fun k => ¬ p k) (W * Wᵀ) V‖ := by
  have hsym : (W * Wᵀ)ᵀ = W * Wᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hfixM : unfold p X * (W * Wᵀ) = unfold p X := by
    have h := congrArg (unfold p) hfix
    rwa [unfold_actOn_compl, hsym] at h
  have hrk : (unfold p X).rank ≤ Fintype.card r := by
    rw [← hfixM, ← Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)
  have hr := rank_eq_of_pos_of_le_singularValues hrk hρ hσ
  have hfixT : W * Wᵀ * (unfold p X)ᵀ = (unfold p X)ᵀ := by
    rw [← hsym, ← Matrix.transpose_mul, hfixM]
  obtain ⟨C, hC⟩ := Matrix.exists_rangeProj_eq_mul (unfold p X)ᵀ
  rw [rangeProj_eq_mul_transpose_of_rank_eq hfixT (by rw [Matrix.rank_transpose, hr])] at hC
  have hC' : W * Wᵀ = Cᵀ * unfold p X := by
    rw [← hsym, hC, Matrix.transpose_mul, Matrix.transpose_transpose]
  have e3 : unfold p (actOn (fun k => ¬ p k) N (actOn (fun k => ¬ p k) (W * Wᵀ) V)) =
      unfold p V * Cᵀ * unfold p X * Nᵀ := by
    rw [unfold_actOn_compl, unfold_actOn_compl, hsym, hC']
    simp only [Matrix.mul_assoc]
  have e2 : unfold p (actOn (fun k => ¬ p k) (W * Wᵀ) V) = unfold p V * Cᵀ * unfold p X := by
    rw [unfold_actOn_compl, hsym, hC', Matrix.mul_assoc]
  have e1 : unfold p (actOn (fun k => ¬ p k) N X) = unfold p X * Nᵀ :=
    unfold_actOn_compl p N X
  have h := norm_mul_mul_le_inv_mul_norm_mul_mul_norm_mul hrk hρ hσ (unfold p V * Cᵀ) Nᵀ
  rw [← e3, ← e2, ← e1, norm_unfold, norm_unfold, norm_unfold] at h
  calc ρ * ‖actOn (fun k => ¬ p k) N (actOn (fun k => ¬ p k) (W * Wᵀ) V)‖
      ≤ ρ * (ρ⁻¹ * ‖actOn (fun k => ¬ p k) (W * Wᵀ) V‖ * ‖actOn (fun k => ¬ p k) N X‖) :=
        mul_le_mul_of_nonneg_left h hρ.le
    _ = ‖actOn (fun k => ¬ p k) N X‖ * ‖actOn (fun k => ¬ p k) (W * Wᵀ) V‖ := by
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul, mul_comm]

end Unfold

/-! ### Tensor trains -/

section Train

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*} [∀ k, Fintype (β k)]

/-- The TT tangent projector is the alternating sum of the interface projectors continued
constantly beyond the last interface. -/
theorem ttTangentProj_eq_ttTangentSum_min (A B : TTCores ι β) :
    ttTangentProj A B = ttTangentSum (fun k => ttLeftProj A (min k d))
      (fun k => ttRightProj B (min k d)) d := by
  rw [ttTangentProj, ttTangentSum, ttTangentSum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk := Finset.mem_range.mp hk
    rw [Nat.min_eq_left hk.le, Nat.min_eq_left (Nat.succ_le_of_lt hk)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk := Finset.mem_range.mp hk
    rw [Nat.min_eq_left (show k + 1 ≤ d by omega)]

variable [∀ k, DecidableEq (β k)]

/-- Nested left interface projectors, continued constantly beyond the last interface. -/
theorem ttLeftProj_min_mul_succ [Subsingleton (β 0)] {A : TTCores ι β}
    (hA : ∀ i, IsLeftOrth A i) (k : ℕ) :
    ttLeftProj A (min k d) * ttLeftProj A (min (k + 1) d) = ttLeftProj A (min (k + 1) d) := by
  rcases Nat.lt_or_ge k d with h | h
  · rw [Nat.min_eq_left h.le, Nat.min_eq_left (Nat.succ_le_of_lt h)]
    exact ttLeftProj_mul_succ fun i _ => hA i
  · rw [Nat.min_eq_right h, Nat.min_eq_right (show d ≤ k + 1 by omega)]
    ext1 W
    exact (isOrthProj_ttLeftProj le_rfl fun i _ => hA i).idem W

/-- Nested right interface projectors, continued constantly beyond the last interface. -/
theorem ttRightProj_min_succ_mul [Subsingleton (β d)] {B : TTCores ι β}
    (hB : ∀ i, IsRightOrth B i) (k : ℕ) :
    ttRightProj B (min (k + 1) d) * ttRightProj B (min k d) = ttRightProj B (min k d) := by
  rcases Nat.lt_or_ge k d with h | h
  · rw [Nat.min_eq_left h.le, Nat.min_eq_left (Nat.succ_le_of_lt h)]
    exact ttRightProj_succ_mul h fun i _ => hB i
  · rw [Nat.min_eq_right h, Nat.min_eq_right (show d ≤ k + 1 by omega)]
    ext1 W
    exact (isOrthProj_ttRightProj le_rfl fun i _ => hB i).idem W

variable [∀ i, DecidableEq (ι i)]

/-- **The normal component at `Y` of a tangent vector at `X`, two tensor trains.** Let
`Y = tt A = tt B` and `X = tt A' = tt B'` with left-orthogonal cores `A`, `A'` and
right-orthogonal cores `B`, `B'`, `d ≥ 1` modes, and let `0 < ρ` be a lower bound of the singular
values `σ_{|β k|}` of the unfoldings `X⟨k⟩`, `0 < k < d`. For every `T` tangent at `X`,
`P(X) T = T`: `ρ ‖T - P(Y) T‖ ≤ 2 ‖X - Y‖ ‖T‖`. -/
theorem mul_norm_sub_ttTangentProj_apply_le_two_mul [Unique (β 0)] [Unique (β d)]
    {A B A' B' : TTCores ι β} (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i)
    (hB : ∀ i, IsRightOrth B i) (hAB : tt B = tt A) (hA' : ∀ i, IsLeftOrth A' i)
    (hB' : ∀ i, IsRightOrth B' i) (hAB' : tt B' = tt A') {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt A'))).singularValues (Fintype.card (β k) - 1))
    {T : Tensor ι} (hT : ttTangentProj A' B' T = T) :
    ρ * ‖T - ttTangentProj A B T‖ ≤ 2 * ‖tt A' - tt A‖ * ‖T‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hQl : ∀ {G : TTCores ι β}, (∀ i, IsLeftOrth G i) → ∀ k,
      IsOrthProj (ttLeftProj G (min k (n + 1))) := fun hG k =>
    isOrthProj_ttLeftProj (min_le_right _ _) fun i _ => hG i
  have hQr : ∀ {G : TTCores ι β}, (∀ i, IsRightOrth G i) → ∀ k,
      IsOrthProj (ttRightProj G (min k (n + 1))) := fun hG k =>
    isOrthProj_ttRightProj (min_le_right _ _) fun i _ => hG i
  have htan : ∀ j, ttLeftProj A' (min j (n + 1)) (T - ttRightProj B' (min j (n + 1)) T) =
      T - ttRightProj B' (min j (n + 1)) T := fun j => by
    have h := ttTangentSum_apply_sub_apply_eq (Pl := fun k => ttLeftProj A' (min k (n + 1)))
      (Pr := fun k => ttRightProj B' (min k (n + 1))) (n := n) (hQl hA') (hQr hB')
      (fun a b hab => ttLeftProj_comm_ttRightProj A' B' (min_le_min_right _ hab))
      (ttLeftProj_min_mul_succ hA') (ttRightProj_min_succ_mul hB') j T
    rw [← ttTangentProj_eq_ttTangentSum_min, hT] at h
    exact h
  rw [ttTangentProj_eq_ttTangentSum_min A B]
  refine mul_norm_sub_ttTangentSum_apply_le_two_mul
    (Pl := fun k => ttLeftProj A' (min k (n + 1)))
    (Pr := fun k => ttRightProj B' (min k (n + 1))) (x := tt A') (y := tt A)
    (hQl hA) (hQr hB) (by simpa using ttLeftProj_zero A) (by simpa using ttRightProj_self B)
    (fun j k hjk => ttLeftProj_comm_ttRightProj A B (min_le_min_right _ hjk))
    (ttLeftProj_min_mul_succ hA) (hQl hA') (hQr hB')
    (fun j k hjk => ttLeftProj_comm_ttRightProj A B' (min_le_min_right _ hjk))
    (fun k => ttLeftProj_comm_ttRightProj A' B le_rfl)
    (fun k => ttLeftProj_tt (min_le_right _ _) fun i _ => hA i)
    (fun k => by
      rw [← hAB]
      exact ttRightProj_tt (min_le_right _ _) fun i _ => hB i)
    (fun k _ => htan (k + 1)) hρ.le (fun k hk S => ?_) (fun k hk V => ?_)
  · simp only [Nat.min_eq_left (show k ≤ n + 1 by omega),
      Nat.min_eq_left (show k + 1 ≤ n + 1 by omega)]
    obtain ⟨M', hM'⟩ := exists_actOn_eq_actOn_of_imp
      (p := fun i : Fin (n + 1) => i.val < k + 1) (q := fun i : Fin (n + 1) => i.val < k)
      (fun i hi => Nat.lt_succ_of_lt hi) (ttLeft A k * (ttLeft A k)ᵀ)
    have e : ∀ Z, ttLeftProj A k Z - ttLeftProj A (k + 1) Z =
        actOn (fun i : Fin (n + 1) => i.val < k + 1)
          (M' - ttLeft A (k + 1) * (ttLeft A (k + 1))ᵀ) Z := fun Z => by
      rw [actOn_sub]
      exact congrArg (· - ttLeftProj A (k + 1) Z) (hM' Z)
    rw [e, e]
    exact mul_norm_actOn_actOn_mul_transpose_le (fun i : Fin (n + 1) => i.val < k + 1)
      (U := ttLeft A' (k + 1)) (ttLeftProj_tt (by omega) fun i _ => hA' i) hρ
      (hσ (k + 1) (Nat.succ_pos k) (by omega)) _ S
  · simp only [Nat.min_eq_left (show k + 1 ≤ n + 1 by omega)]
    have e : ∀ Z, Z - ttRightProj B (k + 1) Z =
        actOn (fun i : Fin (n + 1) => ¬ i.val < k + 1)
          (1 - ttRight B (k + 1) * (ttRight B (k + 1))ᵀ) Z := fun Z => by
      rw [actOn_sub, actOn_one]
      rfl
    have hfix : ttRightProj B' (k + 1) (tt A') = tt A' := by
      rw [← hAB']
      exact ttRightProj_tt (by omega) fun i _ => hB' i
    rw [e, e]
    exact mul_norm_actOn_compl_actOn_compl_mul_transpose_le
      (fun i : Fin (n + 1) => i.val < k + 1) (W := ttRight B' (k + 1)) hfix hρ
      (hσ (k + 1) (Nat.succ_pos k) (by omega)) _ V

/-- **The normal component at `Y` of a tangent vector at `X`, explicit form.** Under the
hypotheses of `mul_norm_sub_ttTangentProj_apply_le_two_mul`:
`‖T - P(Y) T‖ ≤ 2 ρ⁻¹ ‖X - Y‖ ‖T‖`. -/
theorem norm_sub_ttTangentProj_apply_le_of_eq_self [Unique (β 0)] [Unique (β d)]
    {A B A' B' : TTCores ι β} (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i)
    (hB : ∀ i, IsRightOrth B i) (hAB : tt B = tt A) (hA' : ∀ i, IsLeftOrth A' i)
    (hB' : ∀ i, IsRightOrth B' i) (hAB' : tt B' = tt A') {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt A'))).singularValues (Fintype.card (β k) - 1))
    {T : Tensor ι} (hT : ttTangentProj A' B' T = T) :
    ‖T - ttTangentProj A B T‖ ≤ 2 * ρ⁻¹ * ‖tt A' - tt A‖ * ‖T‖ := by
  have h := mul_norm_sub_ttTangentProj_apply_le_two_mul hd hA hB hAB hA' hB' hAB' hρ hσ hT
  rw [show 2 * ρ⁻¹ * ‖tt A' - tt A‖ * ‖T‖ = ρ⁻¹ * (2 * ‖tt A' - tt A‖ * ‖T‖) by ring,
    ← div_eq_inv_mul, le_div_iff₀ hρ, mul_comm]
  exact h

/-- **The normal component at `Y` from the normal and the tangential component at `X`.** Under
the hypotheses of `mul_norm_sub_ttTangentProj_apply_le_two_mul` (singular values at `X` only, no
smallness condition), for every tensor `Z`:
`‖Z - P(Y) Z‖ ≤ ‖Z - P(X) Z‖ + 2 ρ⁻¹ ‖X - Y‖ ‖P(X) Z‖`. -/
theorem norm_sub_ttTangentProj_apply_le_add [Unique (β 0)] [Unique (β d)]
    {A B A' B' : TTCores ι β} (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i)
    (hB : ∀ i, IsRightOrth B i) (hAB : tt B = tt A) (hA' : ∀ i, IsLeftOrth A' i)
    (hB' : ∀ i, IsRightOrth B' i) (hAB' : tt B' = tt A') {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt A'))).singularValues (Fintype.card (β k) - 1))
    (Z : Tensor ι) :
    ‖Z - ttTangentProj A B Z‖ ≤ ‖Z - ttTangentProj A' B' Z‖ +
      2 * ρ⁻¹ * ‖tt A' - tt A‖ * ‖ttTangentProj A' B' Z‖ :=
  (isOrthProj_ttTangentProj hA' hB').norm_sub_apply_le_add_of_norm_sub_apply_le
    (isOrthProj_ttTangentProj hA hB)
    (fun _ hT => norm_sub_ttTangentProj_apply_le_of_eq_self hd hA hB hAB hA' hB' hAB' hρ hσ hT)
    Z

/-- **A Lipschitz bound of the TT tangent projector with a constant independent of the number
of modes.** Let `Y = tt A = tt B` and `X = tt A' = tt B'` be tensor trains with `d ≥ 1` modes,
and let `0 < ρ` be a lower bound of the singular values `σ_{|β k|}` of the unfoldings `X⟨k⟩` and
`Y⟨k⟩`, `0 < k < d`. For every tensor `Z`: `‖P(Y) Z - P(X) Z‖ ≤ 2 ρ⁻¹ ‖X - Y‖ ‖Z‖`. -/
theorem norm_ttTangentProj_sub_le [Unique (β 0)] [Unique (β d)] {A B A' B' : TTCores ι β}
    (hd : 0 < d) (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i) (hAB : tt B = tt A)
    (hA' : ∀ i, IsLeftOrth A' i) (hB' : ∀ i, IsRightOrth B' i) (hAB' : tt B' = tt A') {ρ : ℝ}
    (hρ : 0 < ρ)
    (hσ : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt A))).singularValues (Fintype.card (β k) - 1))
    (hσ' : ∀ k, 0 < k → k < d → ρ ≤ (toEuclideanLin (unfold (fun i : Fin d => i.val < k)
      (tt A'))).singularValues (Fintype.card (β k) - 1))
    (Z : Tensor ι) :
    ‖ttTangentProj A B Z - ttTangentProj A' B' Z‖ ≤ 2 * ρ⁻¹ * ‖tt A' - tt A‖ * ‖Z‖ :=
  (isOrthProj_ttTangentProj hA' hB').norm_sub_apply_le_of_norm_sub_apply_le
    (isOrthProj_ttTangentProj hA hB) (by positivity)
    (fun _ hT => norm_sub_ttTangentProj_apply_le_of_eq_self hd hA hB hAB hA' hB' hAB' hρ hσ' hT)
    (fun _ hT => by
      rw [norm_sub_rev (tt A') (tt A)]
      exact norm_sub_ttTangentProj_apply_le_of_eq_self hd hA' hB' hAB' hA hB hAB hρ hσ hT)
    Z

end Train

/-! ### Examples -/

namespace TTTangentNormalExamples

open TTNormalSecondOrderTrainExamples

/-- Non-vacuity of `rank_eq_of_pos_of_le_singularValues`: the `1 × 1` identity matrix. -/
example : (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = 1 :=
  rank_eq_of_pos_of_le_singularValues (by simp)
    (SVD.singularValues_pred_rank_pos (X := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (by simp)
      zero_lt_one) le_rfl

/-- Non-vacuity of `mul_norm_sub_ttTangentProj_apply_le_two_mul` (and of the statements for
interface projectors and unfoldings it is proved from) with three modes of dimension two:
`Y = e₁ ⊗ e₁ ⊗ e₁`, `X = v ⊗ v ⊗ v` with `v = (40/41, 9/41)`, `ρ = 1`, and the tangent vector
`T = P(X) Z` at `X` for any tensor `Z`. All hypotheses hold and `X ≠ Y`. -/
example (Z : Tensor fun _ : Fin 3 => Fin 2) : tt nearCores ≠ tt baseCores ∧
    (1 : ℝ) * ‖ttTangentProj nearCores nearCores Z -
        ttTangentProj baseCores baseCores (ttTangentProj nearCores nearCores Z)‖ ≤
      2 * ‖tt nearCores - tt baseCores‖ * ‖ttTangentProj nearCores nearCores Z‖ :=
  by
  refine ⟨tt_nearCores_ne_tt_baseCores,
    mul_norm_sub_ttTangentProj_apply_le_two_mul (A := baseCores) (B := baseCores)
      (A' := nearCores) (B' := nearCores) (ρ := 1) (by norm_num) isLeftOrth_baseCores
      isRightOrth_baseCores rfl isLeftOrth_nearCores isRightOrth_nearCores rfl one_pos ?_
      ((isOrthProj_ttTangentProj isLeftOrth_nearCores isRightOrth_nearCores).idem Z)⟩
  exact one_le_singularValues_unfold_tt_nearCores

/-- Non-vacuity of `norm_sub_ttTangentProj_apply_le_add` for the same tensor trains. -/
example (Z : Tensor fun _ : Fin 3 => Fin 2) :
    ‖Z - ttTangentProj baseCores baseCores Z‖ ≤ ‖Z - ttTangentProj nearCores nearCores Z‖ +
      2 * (1 : ℝ)⁻¹ * ‖tt nearCores - tt baseCores‖ * ‖ttTangentProj nearCores nearCores Z‖ :=
  by
  refine norm_sub_ttTangentProj_apply_le_add (A := baseCores) (B := baseCores)
    (A' := nearCores) (B' := nearCores) (ρ := 1) (by norm_num) isLeftOrth_baseCores
    isRightOrth_baseCores rfl isLeftOrth_nearCores isRightOrth_nearCores rfl one_pos ?_ Z
  exact one_le_singularValues_unfold_tt_nearCores

/-- Non-vacuity of `norm_ttTangentProj_sub_le` for the same tensor trains: the singular values
of the unfoldings of both are at least `ρ = 1`. -/
example (Z : Tensor fun _ : Fin 3 => Fin 2) :
    ‖ttTangentProj baseCores baseCores Z - ttTangentProj nearCores nearCores Z‖ ≤
      2 * (1 : ℝ)⁻¹ * ‖tt nearCores - tt baseCores‖ * ‖Z‖ :=
  by
  refine norm_ttTangentProj_sub_le (A := baseCores) (B := baseCores) (A' := nearCores)
    (B' := nearCores) (ρ := 1) (by norm_num) isLeftOrth_baseCores isRightOrth_baseCores rfl
    isLeftOrth_nearCores isRightOrth_nearCores rfl one_pos ?_ ?_ Z
  · exact one_le_singularValues_unfold_tt_baseCores
  · exact one_le_singularValues_unfold_tt_nearCores

end TTTangentNormalExamples

end Tensor

end LeanDLRA
