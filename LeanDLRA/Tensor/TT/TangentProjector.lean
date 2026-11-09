import LeanDLRA.Tensor.TT.Basic
import LeanDLRA.OpenProblems.TensorNetworks.Part2b

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

* `ttTangentSum_eq_openProblems`: the core alternating sum is the one of
  `OpenProblems/TensorNetworks/Part2Defs.lean` (bridging lemma).
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

/-- Bridging lemma: the core alternating sum `Tensor.ttTangentSum` is the operator
`OpenProblems.TensorNetworks.ttTangentSum` of the earlier abstract development. -/
theorem ttTangentSum_eq_openProblems {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Pl Pr : ℕ → E →L[ℝ] E) (d : ℕ) :
    ttTangentSum Pl Pr d = OpenProblems.TensorNetworks.ttTangentSum Pl Pr d := rfl

/-- For two modes the alternating sum is the matrix tangent projector built from the left and
the right projector: `P_Y = P_{≤1} + P_{>1} - P_{≤1} P_{>1}` (`LeanDLRA.tangent`), the projector
`P(Y) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ` of Koch–Lubich. -/
theorem ttTangentSum_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Pl Pr : ℕ → E →L[ℝ] E) (h0 : Pl 0 = 1) (h2 : Pr 2 = 1) :
    ttTangentSum Pl Pr 2 = tangent (Pl 1) (Pr 1) := by
  simp only [ttTangentSum, Finset.sum_range_succ, Finset.sum_range_zero, h0, h2, one_mul,
    mul_one, zero_add, tangent, show 2 - 1 = 1 from rfl]
  abel

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*} [∀ k, Fintype (β k)]

/-! ### The orthogonal TT tangent projector -/

section Orthogonal

variable [∀ k, DecidableEq (β k)]

/-- **The TT tangent projector is an orthogonal projector** (arXiv 1407.2042, Thm 3.1 and
Cor. 3.2; arXiv 2603.13990, Eq. (4.19)): for left-orthogonal cores `A` and right-orthogonal cores
`B` of the ordinary TT format (one-element boundary bonds),
`P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}` is idempotent and symmetric.
The proof checks the commutation and nesting relations of the interface projectors
(`ttLeftProj_comm_ttRightProj`, `ttLeftProj_mul_succ`, `ttRightProj_succ_mul`) and applies the
abstract `OpenProblems.TensorNetworks.ttTangentSum_isOrthProj`. -/
theorem isOrthProj_ttTangentProj [Unique (β 0)] [Unique (β d)] {A B : TTCores ι β}
    (hA : ∀ i, IsLeftOrth A i) (hB : ∀ i, IsRightOrth B i) :
    IsOrthProj (ttTangentProj A B) := by
  classical
  set Ql : ℕ → Tensor ι →L[ℝ] Tensor ι := fun k => if k ≤ d then ttLeftProj A k else 0
    with hQl
  set Qr : ℕ → Tensor ι →L[ℝ] Tensor ι := fun k => if k ≤ d then ttRightProj B k else 1
    with hQr
  have heq : ttTangentProj A B = OpenProblems.TensorNetworks.ttTangentSum Ql Qr d := by
    rw [← ttTangentSum_eq_openProblems, ttTangentProj, ttTangentSum, ttTangentSum]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      simp [hQl, hQr, show k ≤ d by omega, show k + 1 ≤ d by omega]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      simp [hQl, hQr, show k + 1 ≤ d by omega]
  rw [heq]
  refine OpenProblems.TensorNetworks.ttTangentSum_isOrthProj (fun k => ?_) (fun k => ?_) ?_ ?_
    (fun j k hjk => ?_) (fun k => ?_) (fun k => ?_)
  · by_cases hk : k ≤ d
    · simpa [hQl, hk] using isOrthProj_ttLeftProj hk fun i _ => hA i
    · simpa [hQl, hk] using (IsOrthProj.zero : IsOrthProj (0 : Tensor ι →L[ℝ] Tensor ι))
  · by_cases hk : k ≤ d
    · simpa [hQr, hk] using isOrthProj_ttRightProj hk fun i _ => hB i
    · simpa [hQr, hk] using (IsOrthProj.one : IsOrthProj (1 : Tensor ι →L[ℝ] Tensor ι))
  · simp [hQl, ttLeftProj_zero A]
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
  · by_cases hk : k + 1 ≤ d
    · simp only [hQr, hk, show k ≤ d by omega, ite_true]
      exact ttRightProj_succ_mul (by omega) fun i _ => hB i
    · simp [hQr, hk]

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

end LeanDLRA.Tensor
