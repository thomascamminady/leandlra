import LeanDLRA.Tensor.TT.Basic

/-!
# The TT tangent projector and cross interpolation

For a tensor train with left-orthogonal cores `A` and right-orthogonal cores `B`, the TT tangent
projector `P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}` (`ttTangentProj`) is
an orthogonal projector (Lubich–Oseledets–Vandereycken, arXiv 1407.2042, Thm 3.1 and Cor. 3.2;
the TDVP projector of arXiv 2603.13990, Eq. (4.19)). Its summands `P_{≤k-1} P_{>k}` and
`P_{≤k} P_{>k}` are the orthogonal projectors of the substeps of the TT projector-splitting
integrator.

With oblique interface operators `P_{≤k} = Ten_k(P_{≤k} ·)`, `P_{>k}` (any matrices acting on the
first `k`, resp. the last `d - k` modes) that **interpolate** on nested index sets
`I^{≤k} ⊂ I^{≤k-1} × [n_k]`, `I^{>k-1} ⊂ [n_k] × I^{>k}`, the same alternating sum has the **cross
interpolation property** `[P_Y Z](I^{≤j-1}, i_j, I^{>j}) = Z(I^{≤j-1}, i_j, I^{>j})`
(Dektor–Peng–Venturi, arXiv 2402.18721, Lemma 4.1 and Thm 4.1).

## Main results

* `ttTangentSum_idem`: the alternating sum of idempotent interface operators with nested
  left operators is idempotent (arXiv 2402.18721, Prop. 4.1).
* `ttTangentSum_isOrthProj`: for orthogonal interface projectors it is an orthogonal
  projector (arXiv 1407.2042, Thm 3.1).
* `ttTangentSum_isObliqueProj`: for oblique interface operators with the ranges of
  orthogonal ones it is an oblique projector onto the range of the orthogonal alternating
  sum (arXiv 2510.19518, §6).
* `ttTangentSum_two`: for `d = 2` the alternating sum is the matrix tangent projector
  `tangent P_{≤1} P_{>1}`.
* `isOrthProj_ttTangentProj`: `P_Y` is an orthogonal projector.
* `ttTangentProj_tt`: `P_Y Y = Y` for the tensor train `Y` of the cores `A`.
* `isOrthProj_ttLeftProj_mul_ttRightProj`: the substep projectors `P_{≤j} P_{>k}` (`j ≤ k`)
  are orthogonal projectors.
* `actOn_apply_eq_of_row_eq_one`: an operator whose rows at an index set are unit rows
  interpolates there (the interpolatory projectors of arXiv 2402.18721, Eq. (37)).
* `ttTangentSum_actOn_apply_eq_of_interp`: cross interpolation (arXiv 2402.18721, Thm 4.1).

The modes are numbered `0, …, d - 1`; the paper's mode `j` is our mode `j - 1`, its `P_{≤k}`
acts on our modes `< k` and its `P_{>k}` on our modes `≥ k`.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Tensor

/-- For two modes the alternating sum is the matrix tangent projector built from the left and
the right projector: `P_Y = P_{≤1} + P_{>1} - P_{≤1} P_{>1}` (`LeanDLRA.tangent`), the projector
`P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` of Koch–Lubich. -/
theorem ttTangentSum_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Pl Pr : ℕ → E →L[ℝ] E) (h0 : Pl 0 = 1) (h2 : Pr 2 = 1) :
    ttTangentSum Pl Pr 2 = tangent (Pl 1) (Pr 1) := by
  simp only [ttTangentSum, Finset.sum_range_succ, Finset.sum_range_zero, h0, h2, one_mul,
    mul_one, zero_add, tangent, show 2 - 1 = 1 from rfl]
  abel

/-! ### The alternating sum of abstract interface projectors -/

section AlternatingSum

open Finset

section Idempotence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- With `Pr (n + 1) = 1` the alternating sum over `n + 1` modes is
`∑_{k<n} (Pl k - Pl (k + 1)) * Pr (k + 1) + Pl n`. -/
private theorem ttTangentSum_succ {Pl Pr : ℕ → E →L[ℝ] E} {n : ℕ} (hrd : Pr (n + 1) = 1) :
    ttTangentSum Pl Pr (n + 1) = (∑ k ∈ range n, (Pl k - Pl (k + 1)) * Pr (k + 1)) + Pl n := by
  unfold ttTangentSum
  rw [Finset.sum_range_succ, hrd, Nat.add_sub_cancel]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_one]
  abel

/-- **Idempotence of the alternating sum** (arXiv 2402.18721, Prop. 4.1, idempotence paragraph;
arXiv 2510.19518, §6). If the interface operators are idempotent, the left ones are nested in
range and kernel (`P_{≤k} P_{≤k+1} = P_{≤k+1}`, `P_{≤k+1} P_{≤k} = P_{≤k+1}`), the last right one
is the identity and left and right operators on disjoint mode sets commute, then
`ttTangentSum Pl Pr d` is idempotent. The nesting and commutation relations are hypotheses on
abstract operators. -/
theorem ttTangentSum_idem {Pl Pr : ℕ → E →L[ℝ] E} {d : ℕ}
    (hPl : ∀ k, Pl k * Pl k = Pl k) (hPr : ∀ k, Pr k * Pr k = Pr k) (hrd : Pr d = 1)
    (hcomm : ∀ j k, j ≤ k → Pl j * Pr k = Pr k * Pl j)
    (hlr : ∀ k, Pl k * Pl (k + 1) = Pl (k + 1)) (hlk : ∀ k, Pl (k + 1) * Pl k = Pl (k + 1)) :
    ttTangentSum Pl Pr d * ttTangentSum Pl Pr d = ttTangentSum Pl Pr d := by
  cases d with
  | zero => simp [ttTangentSum]
  | succ n =>
    rw [ttTangentSum_succ hrd]
    -- the differences of left projectors are orthogonal idempotents
    have hle : ∀ j k, j ≤ k → Pl j * Pl k = Pl k := by
      intro j k hjk
      induction k, hjk using Nat.le_induction with
      | base => exact hPl j
      | succ k hk ih => rw [← hlr k, ← mul_assoc, ih]
    have hge : ∀ j k, j ≤ k → Pl k * Pl j = Pl k := by
      intro j k hjk
      induction k, hjk using Nat.le_induction with
      | base => exact hPl j
      | succ k hk ih => rw [← hlk k, mul_assoc, ih]
    set c : ℕ → E →L[ℝ] E := fun k => Pl k - Pl (k + 1) with hc
    have hcc : ∀ j k, j < k → c j * c k = 0 := by
      intro j k hjk
      simp only [hc, sub_mul, mul_sub]
      rw [hle j k hjk.le, hle j (k + 1) (by omega), hle (j + 1) k hjk,
        hle (j + 1) (k + 1) (by omega)]
      abel
    have hcc' : ∀ j k, k < j → c j * c k = 0 := by
      intro j k h
      simp only [hc, sub_mul, mul_sub]
      rw [hge k j h.le, hge k (j + 1) (by omega), hge (k + 1) j h, hge (k + 1) (j + 1) (by omega)]
      abel
    have hcc2 : ∀ k, c k * c k = c k := by
      intro k
      simp only [hc, sub_mul, mul_sub]
      rw [hPl k, hlr k, hlk k, hPl (k + 1)]
      abel
    have hcl : ∀ k, k < n → Pl n * c k = 0 := by
      intro k hk
      simp only [hc, mul_sub]
      rw [hge k n hk.le, hge (k + 1) n hk]
      abel
    have hlc : ∀ k, k < n → c k * Pl n = 0 := by
      intro k hk
      simp only [hc, sub_mul]
      rw [hle k n hk.le, hle (k + 1) n hk]
      abel
    have hcb : ∀ k, c k * Pr (k + 1) = Pr (k + 1) * c k := by
      intro k
      simp only [hc, sub_mul, mul_sub]
      rw [hcomm k (k + 1) (by omega), hcomm (k + 1) (k + 1) le_rfl]
    set x : ℕ → E →L[ℝ] E := fun k => c k * Pr (k + 1) with hx
    have hxx : ∀ j k, x j * x k = if j = k then x k else 0 := by
      intro j k
      have : x j * x k = Pr (j + 1) * (c j * c k) * Pr (k + 1) := by
        simp only [hx]
        rw [hcb j]
        simp only [mul_assoc]
      rcases lt_trichotomy j k with h | h | h
      · rw [this, hcc j k h]; simp [h.ne]
      · subst h
        rw [this, hcc2]
        simp only [↓reduceIte]
        change _ = c j * Pr (j + 1)
        rw [mul_assoc, hcb j, ← mul_assoc, hPr]
      · rw [this, hcc' j k h]; simp [h.ne']
    have hxl : ∀ k ∈ range n, x k * Pl n = 0 := by
      intro k hk
      have hk := Finset.mem_range.mp hk
      simp only [hx]
      rw [hcb k, mul_assoc, hlc k hk, mul_zero]
    have hlx : ∀ k ∈ range n, Pl n * x k = 0 := by
      intro k hk
      have hk := Finset.mem_range.mp hk
      simp only [hx]
      rw [← mul_assoc, hcl k hk, zero_mul]
    have hsq : (∑ k ∈ range n, x k) * (∑ k ∈ range n, x k) = ∑ k ∈ range n, x k := by
      rw [Finset.sum_mul_sum]
      simp_rw [hxx]
      simp only [Finset.sum_ite_eq, Finset.mem_range]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp [Finset.mem_range.mp hk]
    change (∑ k ∈ range n, x k + Pl n) * (∑ k ∈ range n, x k + Pl n) = ∑ k ∈ range n, x k + Pl n
    rw [add_mul, mul_add, mul_add, hsq, hPl n, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_eq_zero hxl, Finset.sum_eq_zero hlx]
    simp

/-- Product of two alternating sums over `n + 1` modes: if the left operators `Xl j` fix the
ranges of the `Yl k` with `j ≤ k`, the right operators `Xr a` fix the ranges of the `Yr b` with
`b ≤ a`, and the `Xr j` commute with the `Xl k` and the `Yl k` with `k ≤ j`, then
`ttTangentSum Xl Xr (n + 1) * ttTangentSum Yl Yr (n + 1) = ttTangentSum Yl Yr (n + 1)`. -/
private theorem ttTangentSum_mul_of {Xl Xr Yl Yr : ℕ → E →L[ℝ] E} {n : ℕ}
    (hXrd : Xr (n + 1) = 1) (hYrd : Yr (n + 1) = 1)
    (hXcomm : ∀ j k, j ≤ k → Xl j * Xr k = Xr k * Xl j)
    (r1 : ∀ j k, j ≤ k → Xl j * Yl k = Yl k) (r2 : ∀ a b, b ≤ a → Xr a * Yr b = Yr b)
    (r3 : ∀ k j, k ≤ j → Yl k * Xr j = Xr j * Yl k) :
    ttTangentSum Xl Xr (n + 1) * ttTangentSum Yl Yr (n + 1) = ttTangentSum Yl Yr (n + 1) := by
  rw [ttTangentSum_succ hXrd, ttTangentSum_succ hYrd]
  have hk : ∀ k ∈ range n, ((∑ j ∈ range n, (Xl j - Xl (j + 1)) * Xr (j + 1)) + Xl n) *
      ((Yl k - Yl (k + 1)) * Yr (k + 1)) = (Yl k - Yl (k + 1)) * Yr (k + 1) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    set z := (Yl k - Yl (k + 1)) * Yr (k + 1) with hz
    have hterm : ∀ j, (Xl j - Xl (j + 1)) * Xr (j + 1) * z =
        if k ≤ j then (Xl j - Xl (j + 1)) * z else 0 := by
      intro j
      have hc : (Xl j - Xl (j + 1)) * Xr (j + 1) = Xr (j + 1) * (Xl j - Xl (j + 1)) := by
        simp only [mul_sub, sub_mul]
        rw [hXcomm j (j + 1) (by omega), hXcomm (j + 1) (j + 1) le_rfl]
      split_ifs with h
      · have hc2 : (Yl k - Yl (k + 1)) * Xr (j + 1) = Xr (j + 1) * (Yl k - Yl (k + 1)) := by
          simp only [mul_sub, sub_mul]
          rw [r3 k (j + 1) (by omega), r3 (k + 1) (j + 1) (by omega)]
        calc (Xl j - Xl (j + 1)) * Xr (j + 1) * z
            = (Xl j - Xl (j + 1)) * (Xr (j + 1) * (Yl k - Yl (k + 1))) * Yr (k + 1) := by
              rw [hz]; simp only [mul_assoc]
          _ = (Xl j - Xl (j + 1)) * ((Yl k - Yl (k + 1)) * Xr (j + 1)) * Yr (k + 1) := by
              rw [hc2]
          _ = (Xl j - Xl (j + 1)) * (Yl k - Yl (k + 1)) * (Xr (j + 1) * Yr (k + 1)) := by
              simp only [mul_assoc]
          _ = (Xl j - Xl (j + 1)) * (Yl k - Yl (k + 1)) * Yr (k + 1) := by
              rw [r2 (j + 1) (k + 1) (by omega)]
          _ = (Xl j - Xl (j + 1)) * z := by rw [hz]; simp only [mul_assoc]
      · have h0 : (Xl j - Xl (j + 1)) * (Yl k - Yl (k + 1)) = 0 := by
          simp only [mul_sub, sub_mul]
          rw [r1 j k (by omega), r1 j (k + 1) (by omega), r1 (j + 1) k (by omega),
            r1 (j + 1) (k + 1) (by omega)]
          abel
        have h1 : (Xl j - Xl (j + 1)) * z = 0 := by rw [hz, ← mul_assoc, h0, zero_mul]
        rw [hc, mul_assoc, h1, mul_zero]
    have htele : ∀ m, k ≤ m →
        ∑ j ∈ range m, (if k ≤ j then (Xl j - Xl (j + 1)) * z else 0) = (Xl k - Xl m) * z := by
      intro m hm
      induction m with
      | zero =>
        have : k = 0 := by omega
        subst this
        simp
      | succ m ih =>
        rw [Finset.sum_range_succ]
        rcases Nat.lt_or_ge m k with h | h
        · have hkm : k = m + 1 := by omega
          subst hkm
          have e : ∀ j, j ≤ m →
              (if m + 1 ≤ j then (Xl j - Xl (j + 1)) * z else 0) = 0 := fun j hj =>
            ite_eq_right_iff.mpr fun h' => absurd h' (by omega)
          rw [Finset.sum_eq_zero fun j hj => e j (Finset.mem_range.mp hj).le, e m le_rfl]
          simp
        · rw [ih h]
          simp only [h, ↓reduceIte, sub_mul]
          abel
    rw [add_mul, Finset.sum_mul]
    simp_rw [hterm]
    rw [htele n hk.le, ← add_mul, sub_add_cancel, hz, ← mul_assoc, mul_sub, r1 k k le_rfl,
      r1 k (k + 1) (by omega)]
  have hl : ((∑ j ∈ range n, (Xl j - Xl (j + 1)) * Xr (j + 1)) + Xl n) * Yl n = Yl n := by
    rw [add_mul, Finset.sum_mul, r1 n n le_rfl]
    rw [Finset.sum_eq_zero, zero_add]
    intro j hj
    have hj := Finset.mem_range.mp hj
    have hc : (Xl j - Xl (j + 1)) * Xr (j + 1) = Xr (j + 1) * (Xl j - Xl (j + 1)) := by
      simp only [mul_sub, sub_mul]
      rw [hXcomm j (j + 1) (by omega), hXcomm (j + 1) (j + 1) le_rfl]
    have h0 : (Xl j - Xl (j + 1)) * Yl n = 0 := by
      rw [sub_mul, r1 j n (by omega), r1 (j + 1) n (by omega), sub_self]
    rw [hc, mul_assoc, h0, mul_zero]
  rw [mul_add, Finset.mul_sum, hl, Finset.sum_congr rfl hk]

end Idempotence

section Projector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The alternating sum of orthogonal interface projectors is an orthogonal projector**
(Lubich–Oseledets–Vandereycken, arXiv 1407.2042, Thm 3.1; arXiv 2002.11392, Introduction). If
`Ql k`, `Qr k` are orthogonal projectors, the ranges of the left ones are nested
(`P_{≤k} P_{≤k+1} = P_{≤k+1}`), the last right one is the identity and left and right projectors
on disjoint mode sets commute, then `ttTangentSum Ql Qr d` is idempotent and symmetric. Its
summands `± P_{≤k-1} P_{>k}`, `± P_{≤k} P_{>k}` are the substep projectors of the TT
projector-splitting integrator. -/
theorem ttTangentSum_isOrthProj {Ql Qr : ℕ → E →L[ℝ] E} {d : ℕ}
    (hQl : ∀ k, IsOrthProj (Ql k)) (hQr : ∀ k, IsOrthProj (Qr k)) (hrd : Qr d = 1)
    (hcomm : ∀ j k, j ≤ k → Ql j * Qr k = Qr k * Ql j)
    (hlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) :
    IsOrthProj (ttTangentSum Ql Qr d) := by
  have hlk : ∀ k, Ql (k + 1) * Ql k = Ql (k + 1) := by
    intro k
    ext x
    apply ext_inner_right ℝ
    intro y
    change ⟪Ql (k + 1) (Ql k x), y⟫ = ⟪Ql (k + 1) x, y⟫
    have h : Ql k (Ql (k + 1) y) = Ql (k + 1) y := congrArg (fun T => T y) (hlr k)
    rw [(hQl (k + 1)).symm, (hQl k).symm, h, ← (hQl (k + 1)).symm]
  have hidem := ttTangentSum_idem (fun k => (hQl k).idem') (fun k => (hQr k).idem') hrd hcomm
    hlr hlk
  refine ⟨fun x => congrArg (fun T => T x) hidem, ?_⟩
  have hmulsym : ∀ j k, j ≤ k → ∀ x y, ⟪(Ql j * Qr k) x, y⟫ = ⟪x, (Ql j * Qr k) y⟫ := by
    intro j k hjk x y
    change ⟪Ql j (Qr k x), y⟫ = ⟪x, Ql j (Qr k y)⟫
    have h : Ql j (Qr k y) = Qr k (Ql j y) := congrArg (fun T => T y) (hcomm j k hjk)
    rw [(hQl j).symm, (hQr k).symm, h]
  have hP : ∀ (a : ℕ → ℕ) (b : ℕ → ℕ), (∀ k, a k ≤ b k) → ∀ s : Finset ℕ,
      ∀ x y, ⟪(∑ k ∈ s, Ql (a k) * Qr (b k)) x, y⟫ = ⟪x, (∑ k ∈ s, Ql (a k) * Qr (b k)) y⟫ := by
    intro a b hab s x y
    refine Finset.sum_induction _ (fun T : E →L[ℝ] E => ⟪T x, y⟫ = ⟪x, T y⟫) ?_ ?_ ?_
    · intro T U hT hU
      rw [_root_.add_apply, _root_.add_apply, inner_add_left, inner_add_right, hT, hU]
    · simp
    · intro k _
      exact hmulsym _ _ (hab k) x y
  intro x y
  unfold ttTangentSum
  rw [_root_.sub_apply, _root_.sub_apply, inner_sub_left, inner_sub_right]
  rw [hP (fun k => k) (fun k => k + 1) (fun k => Nat.le_succ k) (range d) x y,
    hP (fun k => k + 1) (fun k => k + 1) (fun k => le_rfl) (range (d - 1)) x y]

/-- **The oblique alternating sum projects onto the range of the orthogonal one**
(arXiv 2510.19518, §6). Let `Ql k`, `Qr k` be orthogonal interface projectors with nested ranges
(`Q_{≤k} Q_{≤k+1} = Q_{≤k+1}`, `Q_{>k+1} Q_{>k} = Q_{>k}`) that commute across disjoint mode sets,
and let `Pl k`, `Pr k` be interface operators with the same ranges (`Pl k * Ql k = Ql k`,
`Ql k * Pl k = Pl k`, likewise on the right) that commute with each other and with the orthogonal
ones across disjoint mode sets; the last right operators `Pr d`, `Qr d` are the identity. Then
`ttTangentSum Pl Pr d` is an oblique projector onto the range of the orthogonal projector
`ttTangentSum Ql Qr d` (`IsObliqueProj`); the generic bound `IsObliqueProj.norm_sub_le_opNorm`
then gives quasi-optimality with the constant `‖P_Y‖`. -/
theorem ttTangentSum_isObliqueProj {Pl Pr Ql Qr : ℕ → E →L[ℝ] E} {d : ℕ}
    (hrd : Pr d = 1) (hcomm : ∀ j k, j ≤ k → Pl j * Pr k = Pr k * Pl j)
    (hQl : ∀ k, IsOrthProj (Ql k)) (hQr : ∀ k, IsOrthProj (Qr k)) (hqrd : Qr d = 1)
    (hqcomm : ∀ j k, j ≤ k → Ql j * Qr k = Qr k * Ql j)
    (hqlr : ∀ k, Ql k * Ql (k + 1) = Ql (k + 1)) (hqrr : ∀ k, Qr (k + 1) * Qr k = Qr k)
    (hPQl : ∀ k, Pl k * Ql k = Ql k) (hQPl : ∀ k, Ql k * Pl k = Pl k)
    (hPQr : ∀ k, Pr k * Qr k = Qr k) (hQPr : ∀ k, Qr k * Pr k = Pr k)
    (hmix : ∀ j k, j ≤ k → Pl j * Qr k = Qr k * Pl j ∧ Ql j * Pr k = Pr k * Ql j) :
    IsObliqueProj (ttTangentSum Pl Pr d) (ttTangentSum Ql Qr d) := by
  have hQo := ttTangentSum_isOrthProj hQl hQr hqrd hqcomm hqlr
  have nl : ∀ j k, j ≤ k → Ql j * Ql k = Ql k := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact (hQl j).idem'
    | succ k hk ih => rw [← hqlr k, ← mul_assoc, ih]
  have nr : ∀ a b, b ≤ a → Qr a * Qr b = Qr b := by
    intro a b hab
    induction a, hab using Nat.le_induction with
    | base => exact (hQr b).idem'
    | succ a ha ih => rw [← ih, ← mul_assoc, hqrr a, ih]
  cases d with
  | zero =>
    refine ⟨hQo, fun x => ?_, fun x => ?_⟩ <;> simp [ttTangentSum]
  | succ n =>
    refine ⟨hQo, fun x => ?_, fun x => ?_⟩
    · refine congrArg (fun T => T x) (ttTangentSum_mul_of hrd hqrd hcomm ?_ ?_ ?_)
      · intro j k hjk
        rw [← nl j k hjk, ← mul_assoc, hPQl, nl j k hjk]
      · intro a b hab
        rw [← nr a b hab, ← mul_assoc, hPQr, nr a b hab]
      · intro k j hkj
        exact (hmix k j hkj).2
    · refine congrArg (fun T => T x) (ttTangentSum_mul_of hqrd hrd hqcomm ?_ ?_ ?_)
      · intro j k hjk
        rw [← hQPl k, ← mul_assoc, nl j k hjk, hQPl]
      · intro a b hab
        rw [← hQPr b, ← mul_assoc, nr a b hab, hQPr]
      · intro k j hkj
        exact (hmix k j hkj).1

end Projector

end AlternatingSum

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*} [∀ k, Fintype (β k)]

/-! ### The orthogonal TT tangent projector -/

section Orthogonal

variable [∀ k, DecidableEq (β k)]

/-- **The TT tangent projector is an orthogonal projector** (arXiv 1407.2042, Thm 3.1 and
Cor. 3.2; arXiv 2603.13990, Eq. (4.19)): for left-orthogonal cores `A` and right-orthogonal cores
`B` of the ordinary TT format (one-element boundary bonds),
`P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}` is idempotent and symmetric.
The proof checks the commutation and nesting relations of the interface projectors
(`ttLeftProj_comm_ttRightProj`, `ttLeftProj_mul_succ`) and applies the abstract
`ttTangentSum_isOrthProj`. -/
theorem isOrthProj_ttTangentProj [Unique (β 0)] [Unique (β d)] {A B : TTCores ι β}
    (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i) :
    IsOrthProj (ttTangentProj A B) := by
  classical
  set Ql : ℕ → Tensor ι →L[ℝ] Tensor ι := fun k => if k ≤ d then ttLeftProj A k else 0
    with hQl
  set Qr : ℕ → Tensor ι →L[ℝ] Tensor ι := fun k => if k ≤ d then ttRightProj B k else 1
    with hQr
  have heq : ttTangentProj A B = ttTangentSum Ql Qr d := by
    rw [ttTangentProj, ttTangentSum, ttTangentSum]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      simp [hQl, hQr, show k ≤ d by omega, show k + 1 ≤ d by omega]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      simp [hQl, hQr, show k + 1 ≤ d by omega]
  rw [heq]
  refine ttTangentSum_isOrthProj (fun k => ?_) (fun k => ?_) ?_ (fun j k hjk => ?_)
    (fun k => ?_)
  · by_cases hk : k ≤ d
    · simpa [hQl, hk] using isOrthProj_ttLeftProj hk fun i _ => hA i
    · simpa [hQl, hk] using (IsOrthProj.zero : IsOrthProj (0 : Tensor ι →L[ℝ] Tensor ι))
  · by_cases hk : k ≤ d
    · simpa [hQr, hk] using isOrthProj_ttRightProj hk fun i _ => hB i
    · simpa [hQr, hk] using (IsOrthProj.one : IsOrthProj (1 : Tensor ι →L[ℝ] Tensor ι))
  · simp [hQr, ttRightProj_self B]
  · by_cases hj : j ≤ d
    · by_cases hk : k ≤ d
      · simp only [hQl, hQr, hj, hk, ite_true]
        exact ttLeftProj_comm_ttRightProj A B hjk
      · simp [hQl, hQr, hj, hk]
    · simp [hQl, hQr, hj]
  · by_cases hk : k + 1 ≤ d
    · simp only [hQl, hk, show k ≤ d by omega, ite_true]
      exact ttLeftProj_mul_succ fun i _ => hA i
    · simp [hQl, hk]

/-- The substep projectors `P_{≤j} P_{>k}` (`j ≤ k`) of the TT projector-splitting integrator are
orthogonal projectors (products of commuting orthogonal projectors). -/
theorem isOrthProj_ttLeftProj_mul_ttRightProj [Subsingleton (β 0)] [Subsingleton (β d)]
    {A B : TTCores ι β} {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ d)
    (hA : ∀ i : Fin d, i.val < j → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k ≤ i.val → IsRightOrth B i) :
    IsOrthProj (ttLeftProj A j * ttRightProj B k) :=
  (isOrthProj_ttLeftProj (hjk.trans hk) hA).mul (isOrthProj_ttRightProj hk hB) fun Z => by
    have := congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T Z) (ttLeftProj_comm_ttRightProj A B hjk)
    simpa using this

/-- **The tensor train lies in the range of its tangent projector**: `P_Y Y = Y` for `Y = tt A`
(`d ≥ 1`, left-orthogonal cores `A`, any right-orthogonal cores `B`). -/
theorem ttTangentProj_tt [Unique (β 0)] [Unique (β d)] {A B : TTCores ι β} (hd : 0 < d)
    (hA : ∀ i, IsLeftOrth A i) : ttTangentProj A B (tt A) = tt A := by
  have hY : ∀ k ≤ d, ttLeftProj A k (tt A) = tt A := fun k hk =>
    ttLeftProj_tt hk fun i _ => hA i
  have hc : ∀ j k, j ≤ k → ∀ Z, ttLeftProj A j (ttRightProj B k Z) =
      ttRightProj B k (ttLeftProj A j Z) := fun j k hjk Z =>
    congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T Z) (ttLeftProj_comm_ttRightProj A B hjk)
  have h1 : ∀ k ∈ Finset.range d, (ttLeftProj A k * ttRightProj B (k + 1)) (tt A) =
      ttRightProj B (k + 1) (tt A) := fun k hk => by
    have hk := Finset.mem_range.mp hk
    change ttLeftProj A k (ttRightProj B (k + 1) (tt A)) = _
    rw [hc k (k + 1) (by omega), hY k hk.le]
  have h2 : ∀ k ∈ Finset.range (d - 1), (ttLeftProj A (k + 1) * ttRightProj B (k + 1)) (tt A) =
      ttRightProj B (k + 1) (tt A) := fun k hk => by
    have hk := Finset.mem_range.mp hk
    change ttLeftProj A (k + 1) (ttRightProj B (k + 1) (tt A)) = _
    rw [hc (k + 1) (k + 1) le_rfl, hY (k + 1) (by omega)]
  have e : ∀ S T : Tensor ι →L[ℝ] Tensor ι, (S - T) (tt A) = S (tt A) - T (tt A) :=
    fun _ _ => rfl
  have es : ∀ (s : Finset ℕ) (f : ℕ → Tensor ι →L[ℝ] Tensor ι),
      (∑ k ∈ s, f k) (tt A) = ∑ k ∈ s, f k (tt A) := fun s f => by simp
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [ttTangentProj, ttTangentSum, e, es, es, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
    Nat.add_sub_cancel, Finset.sum_range_succ, ttRightProj_self B]
  simp

end Orthogonal

/-! ### Cross interpolation -/

section Interpolation

/-- **Interpolating operators.** If the rows of `M` at the index set `I` are unit rows, then
`actOn p M` reproduces every tensor at the multi-indices whose `p`-part lies in `I`. For the
interpolatory projectors `X (Sᵀ X)⁻¹ Sᵀ` of a selection matrix `S` this is the interpolation
property (37) of arXiv 2402.18721. -/
theorem actOn_apply_eq_of_row_eq_one {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*}
    [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] {p : κ → Prop} [DecidablePred p]
    {M : Matrix (∀ k : Subtype p, ι k) (∀ k : Subtype p, ι k) ℝ}
    {I : Set (∀ k : Subtype p, ι k)} (hM : ∀ a ∈ I, ∀ z, M a z = (1 : Matrix _ _ ℝ) a z)
    (Z : Tensor ι) {x : ∀ k, ι k} (hx : Subtype.restrict p x ∈ I) : actOn p M Z x = Z x := by
  simp [actOn_apply, hM _ hx, Matrix.one_apply]

/-- The arithmetic of the proof of arXiv 2402.18721, Thm 4.1: if `aₖ = bₖ` for `k < m`,
`a_m = z` and `aₖ = b_{k-1}` for `m < k < d`, then `∑_{k<d} aₖ - ∑_{k<d-1} bₖ = z`. -/
private lemma sum_sub_sum_eq_of_shift {a b : ℕ → ℝ} {m d : ℕ} {z : ℝ} (hm : m < d)
    (hlt : ∀ k < m, a k = b k) (heq : a m = z) (hgt : ∀ k, m < k → k < d → a k = b (k - 1)) :
    ∑ k ∈ Finset.range d, a k - ∑ k ∈ Finset.range (d - 1), b k = z := by
  obtain ⟨n, rfl⟩ : ∃ n, d = m + 1 + n := ⟨d - (m + 1), by omega⟩
  have e1 : ∑ k ∈ Finset.range (m + 1 + n), a k =
      ∑ k ∈ Finset.range m, b k + z + ∑ j ∈ Finset.range n, b (m + j) := by
    rw [Finset.sum_range_add, Finset.sum_range_succ,
      Finset.sum_congr rfl fun k hk => hlt k (Finset.mem_range.mp hk), heq]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hgt (m + 1 + j) (by omega) (by have := Finset.mem_range.mp hj; omega)]
    congr 1
    omega
  have e2 : ∑ k ∈ Finset.range (m + 1 + n - 1), b k =
      ∑ k ∈ Finset.range m, b k + ∑ j ∈ Finset.range n, b (m + j) := by
    rw [show m + 1 + n - 1 = m + n by omega, Finset.sum_range_add]
  rw [e1, e2]
  ring

/-- **Cross interpolation of the oblique TT tangent projector** (Dektor–Peng–Venturi,
arXiv 2402.18721, Lemma 4.1 and Thm 4.1). Let `Ml k` act on the first `k` modes and `Mr k` on
the modes `≥ k`, and suppose they interpolate on index sets `Il k`, `Ir k`
(`[P_{≤k} Z](x) = Z(x)` whenever `x_{<k} ∈ Il k`, and `[P_{>k} Z](x) = Z(x)` whenever
`x_{≥k} ∈ Ir k`), with nested index sets (arXiv 2402.18721, Eq. (38)):
`y ∈ Il (k + 1) → y_{<k} ∈ Il k` and `y ∈ Ir k → y_{≥k+1} ∈ Ir (k + 1)`. Then for every mode
`m < d` and every multi-index `x` with `x_{<m} ∈ Il m` and `x_{≥m+1} ∈ Ir (m + 1)`,
`[P_Y Z](x) = Z(x)` for the alternating sum `P_Y = ∑ P_{≤k-1} P_{>k} - ∑ P_{≤k} P_{>k}`.

Differences from the paper: the paper takes `P_{≤0} = 1` and `P_{>d} = 1` and interpolation for
`1 ≤ k ≤ d - 1`; here the operators at `k = 0` and `k = d` are arbitrary but must interpolate
too (the identity does, with `Il 0`, `Ir d` the one-element sets of empty multi-indices). The
interpolation property (37) is a hypothesis; for the paper's interpolatory projectors it follows
from `actOn_apply_eq_of_row_eq_one`. -/
theorem ttTangentSum_actOn_apply_eq_of_interp
    (Ml : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // i.val < k}, ι i)
      (∀ i : {i : Fin d // i.val < k}, ι i) ℝ)
    (Mr : ∀ k : ℕ, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i)
      (∀ i : {i : Fin d // ¬ i.val < k}, ι i) ℝ)
    (Il : ∀ k : ℕ, Set (∀ i : {i : Fin d // i.val < k}, ι i))
    (Ir : ∀ k : ℕ, Set (∀ i : {i : Fin d // ¬ i.val < k}, ι i))
    (hl : ∀ k (Z : Tensor ι) (x : ∀ i, ι i), Subtype.restrict (fun i : Fin d => i.val < k) x ∈
      Il k → actOn (fun i : Fin d => i.val < k) (Ml k) Z x = Z x)
    (hr : ∀ k (Z : Tensor ι) (x : ∀ i, ι i), Subtype.restrict (fun i : Fin d => ¬ i.val < k) x ∈
      Ir k → actOn (fun i : Fin d => ¬ i.val < k) (Mr k) Z x = Z x)
    (hnl : ∀ k y, y ∈ Il (k + 1) →
      restrictLE (fun (i : Fin d) (hi : i.val < k) => Nat.lt_succ_of_lt hi) y ∈ Il k)
    (hnr : ∀ k y, y ∈ Ir k →
      restrictLE (fun (i : Fin d) (hi : ¬ i.val < k + 1) hk => hi (Nat.lt_succ_of_lt hk)) y ∈
        Ir (k + 1))
    {m : ℕ} (hm : m < d) {x : ∀ i, ι i}
    (hxl : Subtype.restrict (fun i : Fin d => i.val < m) x ∈ Il m)
    (hxr : Subtype.restrict (fun i : Fin d => ¬ i.val < m + 1) x ∈ Ir (m + 1)) (Z : Tensor ι) :
    ttTangentSum (fun k => actOn (fun i : Fin d => i.val < k) (Ml k))
      (fun k => actOn (fun i : Fin d => ¬ i.val < k) (Mr k)) d Z x = Z x := by
  set Pl : ℕ → Tensor ι →L[ℝ] Tensor ι := fun k => actOn (fun i : Fin d => i.val < k) (Ml k)
  set Pr : ℕ → Tensor ι →L[ℝ] Tensor ι := fun k => actOn (fun i : Fin d => ¬ i.val < k) (Mr k)
  -- the nested index sets contain the parts of `x`
  have hxl' : ∀ k ≤ m, Subtype.restrict (fun i : Fin d => i.val < k) x ∈ Il k := fun k hk =>
    Nat.decreasingInduction
      (motive := fun k _ => Subtype.restrict (fun i : Fin d => i.val < k) x ∈ Il k)
      (fun k _ ih => hnl k _ ih) hxl hk
  have hxr' : ∀ k, m + 1 ≤ k → Subtype.restrict (fun i : Fin d => ¬ i.val < k) x ∈ Ir k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hxr
    | succ k _ ih => exact hnr k _ ih
  have il : ∀ k ≤ m, ∀ W, Pl k W x = W x := fun k hk W => hl k W x (hxl' k hk)
  have ir : ∀ k, m + 1 ≤ k → ∀ W, Pr k W x = W x := fun k hk W => hr k W x (hxr' k hk)
  have comm : ∀ j k, j ≤ k → ∀ W, Pl j (Pr k W) = Pr k (Pl j W) := fun j k hjk W =>
    actOn_comm_of_disjoint _ (fun (i : Fin d) (hi : i.val < j) (hk : ¬ i.val < k) => hk (by omega))
      _ _ W
  have hsum : ttTangentSum Pl Pr d Z x = ∑ k ∈ Finset.range d, Pl k (Pr (k + 1) Z) x -
      ∑ k ∈ Finset.range (d - 1), Pl (k + 1) (Pr (k + 1) Z) x := by
    simp [ttTangentSum]
  rw [hsum]
  refine sum_sub_sum_eq_of_shift hm (fun k hk => ?_) ?_ (fun k hmk hkd => ?_)
  · -- Lemma 4.1, case `j > k`
    rw [il k hk.le, il (k + 1) hk]
  · -- Lemma 4.1, case `j = k`
    rw [il m le_rfl, ir (m + 1) le_rfl]
  · -- Lemma 4.1, case `j < k`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, comm (j + 1) (j + 1 + 1) (Nat.le_succ _), ir (j + 1 + 1) (by omega),
      comm (j + 1) (j + 1) le_rfl, ir (j + 1) (by omega)]

end Interpolation

/-! ### Examples -/

/-- Non-vacuity of `isOrthProj_ttTangentProj`: the rank-one tensor train with cores
`C(α, x, α') = [x = 0]` on two modes of size two (left- and right-orthogonal). -/
example : IsOrthProj (ttTangentProj (d := 2) (ι := fun _ => Fin 2) (β := fun _ => Fin 1)
    (fun _ _ x _ => if x = 0 then (1 : ℝ) else 0) (fun _ _ x _ => if x = 0 then (1 : ℝ) else 0)) :=
  isOrthProj_ttTangentProj
    (fun _ b b' => by
      obtain rfl := Subsingleton.elim b b'
      change ∑ _a : Fin 1, ∑ x : Fin 2, (if x = 0 then (1 : ℝ) else 0) *
        (if x = 0 then 1 else 0) = (1 : Matrix (Fin 1) (Fin 1) ℝ) b b
      simp)
    (fun _ a a' => by
      obtain rfl := Subsingleton.elim a a'
      change ∑ x : Fin 2, ∑ _b : Fin 1, (if x = 0 then (1 : ℝ) else 0) *
        (if x = 0 then 1 else 0) = (1 : Matrix (Fin 1) (Fin 1) ℝ) a a
      simp)

/-- Non-vacuity of `ttTangentSum_actOn_apply_eq_of_interp`: the identity interface operators
interpolate on all index sets. -/
example (Z : Tensor (fun _ : Fin 3 => Fin 2)) (x : Fin 3 → Fin 2) :
    ttTangentSum (fun k => actOn (fun i : Fin 3 => i.val < k) 1)
      (fun k => actOn (fun i : Fin 3 => ¬ i.val < k) 1) 3 Z x = Z x :=
  ttTangentSum_actOn_apply_eq_of_interp (fun _ => 1) (fun _ => 1) (fun _ => Set.univ)
    (fun _ => Set.univ) (fun _ _ _ _ => by simp [Matrix.one_apply])
    (fun _ _ _ _ => by simp [Matrix.one_apply]) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (m := 1) (by norm_num) trivial trivial Z

/-- Non-vacuity of `ttTangentSum_idem` with nonzero data: on `ℝ` the left operators `1, 0, 0, …`
(nested, not all equal) and identity right operators satisfy the hypotheses. -/
example : ttTangentSum (fun k => if k = 0 then (1 : ℝ →L[ℝ] ℝ) else 0) (fun _ => 1) 2 *
    ttTangentSum (fun k => if k = 0 then (1 : ℝ →L[ℝ] ℝ) else 0) (fun _ => 1) 2 =
      ttTangentSum (fun k => if k = 0 then (1 : ℝ →L[ℝ] ℝ) else 0) (fun _ => 1) 2 :=
  ttTangentSum_idem (fun k => by by_cases h : k = 0 <;> simp [h]) (fun _ => mul_one 1) rfl
    (fun _ _ _ => by simp) (fun k => by simp) fun k => by simp

/-- Non-vacuity of `ttTangentSum_isOrthProj` with nonzero data: identity interface operators on
`ℝ` and two modes. -/
example : IsOrthProj (ttTangentSum (fun _ => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) 2) :=
  ttTangentSum_isOrthProj (fun _ => IsOrthProj.one) (fun _ => IsOrthProj.one) rfl
    (fun _ _ _ => rfl) fun _ => mul_one 1

/-- Non-vacuity of `ttTangentSum_isObliqueProj` with nonzero data: identity interface operators on
`ℝ` and two modes. -/
example : IsObliqueProj (ttTangentSum (fun _ => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) 2)
    (ttTangentSum (fun _ => (1 : ℝ →L[ℝ] ℝ)) (fun _ => 1) 2) :=
  ttTangentSum_isObliqueProj rfl (fun _ _ _ => rfl) (fun _ => IsOrthProj.one)
    (fun _ => IsOrthProj.one) rfl (fun _ _ _ => rfl) (fun _ => mul_one 1) (fun _ => mul_one 1)
    (fun _ => mul_one 1) (fun _ => mul_one 1) (fun _ => mul_one 1) (fun _ => mul_one 1)
    fun _ _ _ => ⟨rfl, rfl⟩

end LeanDLRA.Tensor
