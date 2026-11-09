import LeanDLRA.Tensor.Unfolding

/-!
# Tensor trains: interfaces, orthonormality and interface projectors

For tensor-train cores `G` (`Tensor.TTCores`), this file proves the basic structure of the TT
format used by every TT integrator:

* the recursions of the interface matrices `X_{≤k}` (`ttLeft`) and `X_{>k}` (`ttRight`), and
  the factorization of every unfolding `Y⟨k⟩ = X_{≤k} X_{>k}ᵀ` of the tensor train
  (`unfold_tt`), Lubich–Oseledets–Vandereycken (arXiv 1407.2042, §2) and Dektor–Peng–Venturi
  (arXiv 2402.18721, Eq. (16));
* **orthonormality of the interfaces**: if the first `k` cores are left-orthogonal, the columns of
  `X_{≤k}` are orthonormal (`ttLeft_transpose_mul_self`), and if the cores `k + 1, …, d` are
  right-orthogonal, so are the columns of `X_{>k}` (`ttRight_transpose_mul_self`). For matrix
  product states this is Lemma 1 of arXiv 2603.13990 (left and right state vectors are
  orthonormal, Eqs. (4.9)–(4.10)), here for real tensors;
* the interface projectors `P_{≤k}` (`ttLeftProj`) and `P_{>k}` (`ttRightProj`) are orthogonal
  projectors, `P_{≤0} = P_{>d} = 1`, `P_{≤j}` and `P_{>k}` commute for `j ≤ k`, and the ranges are
  nested: `P_{≤k} P_{≤k+1} = P_{≤k+1}`, `P_{>k+1} P_{>k} = P_{>k}` (arXiv 1407.2042, §3; arXiv
  2402.18721, Eq. (25) and the sentence before (21)).

## Main results

* `ttLeft_succ`, `ttRight_of_lt`, `ttRight_of_le`: the interface recursions.
* `sum_prefixSucc`, `sum_suffixSucc`: splitting sums over interface multi-indices.
* `tt_apply_eq_sum`, `unfold_tt`: `Y⟨k⟩ = X_{≤k} X_{>k}ᵀ` for all `k ≤ d`;
  `rank_unfold_tt_le`: the TT ranks are at most the bond dimensions.
* `ttLeft_transpose_mul_self`, `ttRight_transpose_mul_self`: orthonormal interfaces.
* `isOrthProj_ttLeftProj`, `isOrthProj_ttRightProj`, `ttLeftProj_zero`, `ttRightProj_self`,
  `ttLeftProj_comm_ttRightProj`, `ttLeftProj_mul_succ`, `ttRightProj_succ_mul`.
* `ttLeftProj_tt`: the tensor train is fixed by its own left interface projectors.

The boundary bonds `β 0` and `β d` are assumed to have one element (`Unique`), as in the ordinary
TT format; for orthonormality `Subsingleton` suffices.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} {β : ℕ → Type*} [∀ k, Fintype (β k)]

/-! ### Interface recursions -/

section Recursion

variable (G : TTCores ι β)

/-- `X_{≤0} = 1`. -/
@[simp] lemma ttLeft_zero : ttLeft G 0 = fun _ _ => 1 := rfl

/-- The recursion `X_{≤k+1}(y, α') = ∑_α X_{≤k}(y_{<k}, α) C_{k+1}(α, y_k, α')`. -/
lemma ttLeft_succ (k : ℕ) (h : k < d) (y : ∀ i : {i : Fin d // i.val < k + 1}, ι i)
    (b : β (k + 1)) :
    ttLeft G (k + 1) y b = ∑ a, ttLeft G k (restrictLE (fun (i : Fin d) (hi : i.val < k) =>
      Nat.lt_succ_of_lt hi) y) a * G ⟨k, h⟩ a (y ⟨⟨k, h⟩, Nat.lt_succ_self k⟩) b := by
  simp [ttLeft, h]

/-- Past the last core the left interface vanishes. -/
lemma ttLeft_succ_of_le (k : ℕ) (h : d ≤ k) : ttLeft G (k + 1) = 0 := by
  ext y b; simp [ttLeft, not_lt.mpr h]

/-- The recursion `X_{>k}(y, α) = ∑_{α'} C_{k+1}(α, y_k, α') X_{>k+1}(y_{>k}, α')`. -/
lemma ttRight_of_lt (k : ℕ) (h : k < d) (y : ∀ i : {i : Fin d // ¬ i.val < k}, ι i)
    (a : β k) :
    ttRight G k y a = ∑ b, G ⟨k, h⟩ a (y ⟨⟨k, h⟩, lt_irrefl k⟩) b *
      ttRight G (k + 1)
        (restrictLE (fun (i : Fin d) (hi : ¬ i.val < k + 1) hk =>
          hi (Nat.lt_succ_of_lt hk)) y) b := by
  rw [ttRight]
  simp only [h, dite_true]

/-- `X_{>k} = 1` for `k ≥ d`. -/
lemma ttRight_of_le (k : ℕ) (h : d ≤ k) : ttRight G k = fun _ _ => 1 := by
  funext y a
  rw [ttRight]
  simp only [not_lt.mpr h, dite_false]

end Recursion

/-! ### Splitting interface multi-indices -/

section Split

variable (k : ℕ) (h : k < d)

/-- The first `k` entries of an assembled prefix. -/
lemma restrictLE_prefixSuccEquiv_symm
    (yc : (∀ i : {i : Fin d // i.val < k}, ι i) × ι ⟨k, h⟩) :
    restrictLE (fun (i : Fin d) (hi : i.val < k) => Nat.lt_succ_of_lt hi)
      ((prefixSuccEquiv (ι := ι) k h).symm yc) = yc.1 :=
  congrArg Prod.fst ((prefixSuccEquiv (ι := ι) k h).apply_symm_apply yc)

/-- The entry of mode `k` of an assembled prefix. -/
lemma prefixSuccEquiv_symm_apply_self
    (yc : (∀ i : {i : Fin d // i.val < k}, ι i) × ι ⟨k, h⟩) :
    (prefixSuccEquiv (ι := ι) k h).symm yc ⟨⟨k, h⟩, Nat.lt_succ_self k⟩ = yc.2 :=
  congrArg Prod.snd ((prefixSuccEquiv (ι := ι) k h).apply_symm_apply yc)

/-- The entry of mode `k` of an assembled suffix. -/
lemma suffixSuccEquiv_symm_apply_self
    (cy : ι ⟨k, h⟩ × (∀ i : {i : Fin d // ¬ i.val < k + 1}, ι i)) :
    (suffixSuccEquiv (ι := ι) k h).symm cy ⟨⟨k, h⟩, lt_irrefl k⟩ = cy.1 :=
  congrArg Prod.fst ((suffixSuccEquiv (ι := ι) k h).apply_symm_apply cy)

/-- The entries of the modes `> k` of an assembled suffix. -/
lemma restrictLE_suffixSuccEquiv_symm
    (cy : ι ⟨k, h⟩ × (∀ i : {i : Fin d // ¬ i.val < k + 1}, ι i)) :
    restrictLE (fun (i : Fin d) (hi : ¬ i.val < k + 1) hk => hi (Nat.lt_succ_of_lt hk))
      ((suffixSuccEquiv (ι := ι) k h).symm cy) = cy.2 :=
  congrArg Prod.snd ((suffixSuccEquiv (ι := ι) k h).apply_symm_apply cy)

variable [∀ i, Fintype (ι i)]

/-- A sum over multi-indices of the first `k + 1` modes splits into the first `k` modes and
mode `k`. -/
theorem sum_prefixSucc (f : (∀ i : {i : Fin d // i.val < k + 1}, ι i) → ℝ) :
    ∑ y, f y = ∑ y', ∑ c, f ((prefixSuccEquiv (ι := ι) k h).symm (y', c)) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (prefixSuccEquiv (ι := ι) k h) _ _ fun y => by simp

/-- A sum over multi-indices of the modes `k, …, d - 1` splits into mode `k` and the modes
`k + 1, …, d - 1`. -/
theorem sum_suffixSucc (f : (∀ i : {i : Fin d // ¬ i.val < k}, ι i) → ℝ) :
    ∑ y, f y = ∑ c, ∑ y', f ((suffixSuccEquiv (ι := ι) k h).symm (c, y')) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (suffixSuccEquiv (ι := ι) k h) _ _ fun y => by simp

end Split

/-! ### Factorization of the unfoldings -/

section Factor

variable (G : TTCores ι β)

/-- Every unfolding of a tensor train factorizes through its interfaces:
`Y(x) = ∑ₐ X_{≤k}(x_{<k}, a) X_{>k}(x_{≥k}, a)` for `k ≤ d`. -/
theorem tt_apply_eq_sum (k : ℕ) (hk : k ≤ d) (x : ∀ i, ι i) :
    tt G x = ∑ a, ttLeft G k (Subtype.restrict (fun i : Fin d => i.val < k) x) a *
      ttRight G k (Subtype.restrict (fun i : Fin d => ¬ i.val < k) x) a := by
  induction hn : d - k generalizing k with
  | zero =>
    obtain rfl : k = d := by omega
    simp [tt, ttRight_of_le G k le_rfl]
  | succ n ih =>
    have h : k < d := by omega
    rw [ih (k + 1) h (by omega)]
    simp only [ttLeft_succ G k h, ttRight_of_lt G k h, Finset.sum_mul, Finset.mul_sum,
      restrictLE_restrict, Subtype.restrict_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- **TT unfoldings**: `Y⟨k⟩ = X_{≤k} X_{>k}ᵀ` for `k ≤ d` (arXiv 2402.18721, Eq. (16)). -/
theorem unfold_tt (k : ℕ) (hk : k ≤ d) :
    unfold (fun i : Fin d => i.val < k) (tt G) = ttLeft G k * (ttRight G k)ᵀ := by
  ext a b
  simp [tt_apply_eq_sum G k hk, Matrix.mul_apply]

/-- **TT ranks are bounded by the bond dimensions**: the `k`-th unfolding of a tensor train has
rank at most `|β k|`. -/
theorem rank_unfold_tt_le [∀ i, Fintype (ι i)] (k : ℕ) (hk : k ≤ d) :
    (unfold (fun i : Fin d => i.val < k) (tt G)).rank ≤ Fintype.card (β k) := by
  rw [unfold_tt G k hk]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

end Factor

/-! ### Orthonormal interfaces -/

section Orthonormal

variable [∀ i, Fintype (ι i)] [∀ k, DecidableEq (β k)]

/-- **Left-orthogonal cores give orthonormal left interfaces**: if `β 0` has at most one
element and the cores `0, …, k - 1` are left-orthogonal, then `X_{≤k}ᵀ X_{≤k} = 1`
(arXiv 2603.13990, Lemma 1, Eq. (4.9); arXiv 2402.18721, §3.1). -/
theorem ttLeft_transpose_mul_self [Subsingleton (β 0)] {A : TTCores ι β} :
    ∀ k ≤ d, (∀ i : Fin d, i.val < k → IsLeftOrth A i) → (ttLeft A k)ᵀ * ttLeft A k = 1
  | 0, _, _ => by
    have : IsEmpty {i : Fin d // i.val < 0} := ⟨fun i => Nat.not_lt_zero _ i.2⟩
    ext a a'
    change ∑ _y, (1 : ℝ) * 1 = (1 : Matrix (β 0) (β 0) ℝ) a a'
    simp [Matrix.one_apply, Subsingleton.elim a a']
  | k + 1, hk, hA => by
    have h : k < d := hk
    have ih := ttLeft_transpose_mul_self k (by omega) fun i hi => hA i (by omega)
    ext b b'
    rw [Matrix.mul_apply, sum_prefixSucc k h]
    simp only [Matrix.transpose_apply, ttLeft_succ A k h, restrictLE_prefixSuccEquiv_symm,
      prefixSuccEquiv_symm_apply_self]
    rw [Finset.sum_comm]
    simp only [sum_mulVec_mul_mulVec_of_orthonormal ih]
    rw [Finset.sum_comm]
    exact hA ⟨k, h⟩ (Nat.lt_succ_self k) b b'

/-- **Right-orthogonal cores give orthonormal right interfaces**: if `β d` has at most one
element and the cores `k, …, d - 1` are right-orthogonal, then `X_{>k}ᵀ X_{>k} = 1`
(arXiv 2603.13990, Lemma 1, Eq. (4.10)). -/
theorem ttRight_transpose_mul_self [Subsingleton (β d)] {B : TTCores ι β} (k : ℕ) (hk : k ≤ d)
    (hB : ∀ i : Fin d, k ≤ i.val → IsRightOrth B i) : (ttRight B k)ᵀ * ttRight B k = 1 := by
  induction hn : d - k generalizing k with
  | zero =>
    obtain rfl : k = d := by omega
    have : IsEmpty {i : Fin k // ¬ i.val < k} := ⟨fun i => i.2 i.1.2⟩
    ext a a'
    rw [Matrix.mul_apply, ttRight_of_le B k le_rfl]
    change ∑ _y, (1 : ℝ) * 1 = (1 : Matrix (β k) (β k) ℝ) a a'
    simp [Matrix.one_apply, Subsingleton.elim a a']
  | succ n ih =>
    have h : k < d := by omega
    have ih' := ih (k + 1) h (fun i hi => hB i (by omega)) (by omega)
    ext a a'
    rw [Matrix.mul_apply, sum_suffixSucc k h]
    simp only [Matrix.transpose_apply, ttRight_of_lt B k h, restrictLE_suffixSuccEquiv_symm,
      suffixSuccEquiv_symm_apply_self]
    simp only [fun c y' => (Finset.sum_congr rfl fun b _ => mul_comm (B ⟨k, h⟩ a c b) _ :
      ∑ b, B ⟨k, h⟩ a c b * ttRight B (k + 1) y' b = _),
      fun c y' => (Finset.sum_congr rfl fun b _ => mul_comm (B ⟨k, h⟩ a' c b) _ :
      ∑ b, B ⟨k, h⟩ a' c b * ttRight B (k + 1) y' b = _),
      sum_mulVec_mul_mulVec_of_orthonormal ih']
    exact hB ⟨k, h⟩ le_rfl a a'

end Orthonormal

/-! ### Interface projectors -/

section Projectors

variable [∀ i, Fintype (ι i)] [∀ k, DecidableEq (β k)]

/-- The left interface projector `P_{≤k}` is an orthogonal projector when the first `k` cores
are left-orthogonal. -/
theorem isOrthProj_ttLeftProj [Subsingleton (β 0)] {A : TTCores ι β} {k : ℕ} (hk : k ≤ d)
    (hA : ∀ i : Fin d, i.val < k → IsLeftOrth A i) : IsOrthProj (ttLeftProj A k) :=
  isOrthProj_actOn_mul_transpose _ (ttLeft_transpose_mul_self k hk hA)

/-- The right interface projector `P_{>k}` is an orthogonal projector when the cores
`k, …, d - 1` (0-based) are right-orthogonal. -/
theorem isOrthProj_ttRightProj [Subsingleton (β d)] {B : TTCores ι β} {k : ℕ} (hk : k ≤ d)
    (hB : ∀ i : Fin d, k ≤ i.val → IsRightOrth B i) : IsOrthProj (ttRightProj B k) :=
  isOrthProj_actOn_mul_transpose _ (ttRight_transpose_mul_self k hk hB)

omit [∀ k, DecidableEq (β k)] in
/-- `P_{≤0} = 1` in the ordinary TT format (one-element left boundary bond). -/
theorem ttLeftProj_zero [Unique (β 0)] (A : TTCores ι β) : ttLeftProj A 0 = 1 := by
  rw [ttLeftProj, actOn_of_forall_not _ (fun (i : Fin d) (hi : i.val < 0) => Nat.not_lt_zero _ hi) _
    (fun i => (Nat.not_lt_zero _ i.2).elim), Matrix.mul_apply]
  change (∑ _a : β 0, (1 : ℝ) * 1) • (1 : Tensor ι →L[ℝ] Tensor ι) = 1
  simp

omit [∀ k, DecidableEq (β k)] in
/-- `P_{>d} = 1` in the ordinary TT format (one-element right boundary bond). -/
theorem ttRightProj_self [Unique (β d)] (B : TTCores ι β) : ttRightProj B d = 1 := by
  rw [ttRightProj, actOn_of_forall_not _ (fun (i : Fin d) (hi : ¬ i.val < d) => hi i.2) _
    (fun i => (i.2 i.1.2).elim), Matrix.mul_apply, ttRight_of_le B d le_rfl]
  change (∑ _a : β d, (1 : ℝ) * 1) • (1 : Tensor ι →L[ℝ] Tensor ι) = 1
  simp

omit [∀ k, DecidableEq (β k)] in
/-- `P_{≤j}` and `P_{>k}` act on disjoint sets of modes for `j ≤ k`, hence commute
(arXiv 2402.18721, before Eq. (21)). -/
theorem ttLeftProj_comm_ttRightProj (A B : TTCores ι β) {j k : ℕ} (hjk : j ≤ k) :
    ttLeftProj A j * ttRightProj B k = ttRightProj B k * ttLeftProj A j :=
  actOn_mul_comm_of_disjoint _
    (fun (i : Fin d) (hi : i.val < j) (hk : ¬ i.val < k) => hk (by omega)) _ _

omit [∀ i, Fintype (ι i)] [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)] in
/-- Overriding a smaller set of modes first is undone by overriding a larger one. -/
lemma override_override_of_imp {κ : Type*} {ι : κ → Type*} {p q : κ → Prop} [DecidablePred p]
    [DecidablePred q] (hpq : ∀ k, p k → q k) (x : ∀ k, ι k) (z : ∀ k : Subtype p, ι k)
    (w : ∀ k : Subtype q, ι k) : override q (override p x z) w = override q x w := by
  funext k
  by_cases hq : q k
  · simp [override, hq]
  · have hp : ¬ p k := fun h => hq (hpq k h)
    simp [override, hq, hp]

omit [∀ i, Fintype (ι i)] [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)] in
private lemma sum_sum_mul_left {α γ : Type*} [Fintype α] [Fintype γ] (L : α → ℝ)
    (G : α → γ → ℝ) (F : γ → ℝ) :
    ∑ b, (∑ a, L a * G a b) * F b = ∑ a, L a * ∑ b, G a b * F b := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [∀ i, Fintype (ι i)] [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)] in
private lemma sum_sum_mul_right {α γ : Type*} [Fintype α] [Fintype γ] (G : α → γ → ℝ)
    (R : γ → ℝ) (F : α → ℝ) :
    ∑ a, (∑ b, G a b * R b) * F a = ∑ b, R b * ∑ a, G a b * F a := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- **Nested left interfaces**: `P_{≤k} P_{≤k+1} = P_{≤k+1}` when the first `k` cores are
left-orthogonal, because `X_{≤k+1} = (X_{≤k} ⊗ I) C_{k+1}^{<l>}` (arXiv 2402.18721, Eq. (28)). -/
theorem ttLeftProj_mul_succ [Subsingleton (β 0)] {A : TTCores ι β} {k : ℕ}
    (hA : ∀ i : Fin d, i.val < k → IsLeftOrth A i) :
    ttLeftProj A k * ttLeftProj A (k + 1) = ttLeftProj A (k + 1) := by
  by_cases h : k < d
  · ext1 Z
    change ttLeftProj A k (ttLeftProj A (k + 1) Z) = ttLeftProj A (k + 1) Z
    refine actOn_mul_transpose_apply_eq_self_of _ (ttLeft_transpose_mul_self k h.le hA)
      (fun a x => ∑ b, A ⟨k, h⟩ a (x ⟨k, h⟩) b * ∑ w, ttLeft A (k + 1) w b *
        Z (override (fun i : Fin d => i.val < k + 1) x w)) (fun a x z => ?_) (fun x => ?_)
    · have hx : override (fun i : Fin d => i.val < k) x z ⟨k, h⟩ = x ⟨k, h⟩ :=
        override_apply_of_not _ (lt_irrefl k)
      simp only [hx, override_override_of_imp
        (fun (i : Fin d) (hi : i.val < k) => Nat.lt_succ_of_lt hi)]
    · rw [ttLeftProj, actOn_mul_transpose_apply]
      simp only [ttLeft_succ A k h, restrictLE_restrict]
      exact sum_sum_mul_left _ _ _
  · have h0 : ttLeftProj A (k + 1) = 0 := by
      rw [ttLeftProj, ttLeft_succ_of_le A k (not_lt.mp h), Matrix.zero_mul, actOn_zero]
    rw [h0, mul_zero]

/-- **Nested right interfaces**: `P_{>k+1} P_{>k} = P_{>k}` for `k < d` when the cores
`k + 1, …, d - 1` (0-based) are right-orthogonal. -/
theorem ttRightProj_succ_mul [Subsingleton (β d)] {B : TTCores ι β} {k : ℕ} (h : k < d)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i) :
    ttRightProj B (k + 1) * ttRightProj B k = ttRightProj B k := by
  ext1 Z
  change ttRightProj B (k + 1) (ttRightProj B k Z) = ttRightProj B k Z
  refine actOn_mul_transpose_apply_eq_self_of _ (ttRight_transpose_mul_self (k + 1) h hB)
    (fun b x => ∑ a, B ⟨k, h⟩ a (x ⟨k, h⟩) b * ∑ w, ttRight B k w a *
      Z (override (fun i : Fin d => ¬ i.val < k) x w)) (fun b x z => ?_) (fun x => ?_)
  · have hx : override (fun i : Fin d => ¬ i.val < k + 1) x z ⟨k, h⟩ = x ⟨k, h⟩ :=
      override_apply_of_not _ (by simp)
    simp only [hx, override_override_of_imp (p := fun i : Fin d => ¬ i.val < k + 1)
      (q := fun i : Fin d => ¬ i.val < k) (fun i hi hk => hi (Nat.lt_succ_of_lt hk))]
  · rw [ttRightProj, actOn_mul_transpose_apply]
    simp only [ttRight_of_lt B k h, restrictLE_restrict]
    exact sum_sum_mul_right _ _ _

/-- A tensor train is fixed by the left interface projectors of its own (left-orthogonal)
cores: `P_{≤k} Y = Y` for `k ≤ d`. -/
theorem ttLeftProj_tt [Subsingleton (β 0)] {A : TTCores ι β} {k : ℕ}
    (hk : k ≤ d) (hA : ∀ i : Fin d, i.val < k → IsLeftOrth A i) :
    ttLeftProj A k (tt A) = tt A :=
  (actOn_mul_transpose_eq_self_iff _ (ttLeft_transpose_mul_self k hk hA) _).2
    ⟨_, unfold_tt A k hk⟩

end Projectors

/-! ### Example -/

/-- The rank-one tensor train `e₀ ⊗ e₀` on two modes of size two, with the core
`C(α, x, α') = [x = 0]`, used to show that the hypotheses below are satisfiable. -/
example : IsLeftOrth (d := 2) (ι := fun _ => Fin 2) (β := fun _ => Fin 1)
    (fun _ _ x _ => if x = 0 then (1 : ℝ) else 0) 0 := by
  intro b b'
  obtain rfl := Subsingleton.elim b b'
  change ∑ _a : Fin 1, ∑ x : Fin 2, (if x = 0 then (1 : ℝ) else 0) * (if x = 0 then 1 else 0) =
    (1 : Matrix (Fin 1) (Fin 1) ℝ) b b
  simp

example : IsRightOrth (d := 2) (ι := fun _ => Fin 2) (β := fun _ => Fin 1)
    (fun _ _ x _ => if x = 0 then (1 : ℝ) else 0) 1 := by
  intro a a'
  obtain rfl := Subsingleton.elim a a'
  change ∑ x : Fin 2, ∑ _b : Fin 1, (if x = 0 then (1 : ℝ) else 0) * (if x = 0 then 1 else 0) =
    (1 : Matrix (Fin 1) (Fin 1) ℝ) a a
  simp

end LeanDLRA.Tensor
