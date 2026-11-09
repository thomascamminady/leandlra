import LeanDLRA.Tensor.TT.Basic

/-!
# Tensor trains: operations on cores, gauge transformations and the bond-centred form

For tensor-train cores `G` (`Tensor.TTCores`) this file provides the elementary operations on
tensor trains that every TT algorithm uses (Oseledets 2011; Lubich–Oseledets–Vandereycken, arXiv
1407.2042; the list of operations in Wang–Hu, arXiv 2512.14950, §2; the canonical forms of
Petersson–Hodges-Heilmann–Günther, arXiv 2603.13990, §4):

* **locality of the interfaces**: `X_{≤k}` depends only on the cores `< k`, `X_{>k}` only on the
  cores `≥ k`; hence the expansion of a tensor train around one core
  `Y(x) = ∑ X_{≤k}(x_{<k}, α) C_k(α, x_k, α') X_{>k+1}(x_{>k}, α')`;
* **replacing one core** (`Function.update G k C`): the tensor train is linear in each core, so
  scaling one core scales the tensor train and two tensor trains that differ in a single core add
  up to the tensor train with the summed core (arXiv 2512.14950, operations 1 and 3);
* **gauge transformations**: moving a matrix `R` across a bond does not change the tensor train
  (`tt_gauge`). This is the step behind the QR/RQ orthonormalization sweeps (arXiv 2512.14950,
  operations 7–8), moving the orthogonality centre (arXiv 2603.13990, Eqs. (4.11), (4.13)) and
  the gauge invariance `M_k ↦ M_k C⁻¹`, `M_{k+1} ↦ C M_{k+1}`;
* **rank-one tensor trains** (all bonds of size one): entrywise products, inverses and Hadamard
  products with a general tensor train (arXiv 2512.14950, operations 4–5), the sum of all entries
  (operation 6), and the rank bound for sums of tensor trains (operation 2);
* **mixed canonical and bond-centred forms**: the cores `A i` (`i < k`) followed by `B i`
  (`i ≥ k`) (`ttMix`), the bond-centred tensor `Y⟨k⟩ = X_{≤k} S X_{>k}ᵀ` (`ttBond`, arXiv
  2603.13990, Eq. (4.12)), which is a tensor train with `S` merged into core `k`; with orthonormal
  interfaces the rank of the `k`-th unfolding is the rank of the bond matrix `S` (Schmidt rank),
  and the right interface projector fixes a tensor train with right-orthogonal cores.

## Main results

* `ttLeft_congr`, `ttRight_congr`, `tt_apply_eq_sum_core`.
* `tt_update_apply`, `tt_update_add`, `tt_update_smul`, `tt_update_self_smul`.
* `tt_gauge`.
* `tt_mul_rankOne`, `tt_rankOne`, `tt_hadamard_rankOne`, `tt_inv_rankOne`,
  `tt_mul_tt_inv_rankOne`, `sum_tt`, `rank_unfold_tt_add_le`.
* `ttMix`, `ttLeft_ttMix`, `ttRight_ttMix`, `ttBond`, `unfold_ttBond`, `ttBond_eq_tt`,
  `rank_unfold_ttBond`, `ttRightProj_tt`.

Everything is real; complex tensor trains (quantum states) are not covered by these statements.
-/

open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} {β : ℕ → Type*} [∀ k, Fintype (β k)]

/-! ### Locality of the interfaces -/

section Locality

/-- The left interface `X_{≤k}` depends only on the cores `0, …, k - 1`. -/
theorem ttLeft_congr {G G' : TTCores ι β} :
    ∀ k : ℕ, (∀ i : Fin d, i.val < k → G i = G' i) → ttLeft G k = ttLeft G' k
  | 0, _ => rfl
  | k + 1, h => by
    by_cases hk : k < d
    · funext y b
      rw [ttLeft_succ G k hk, ttLeft_succ G' k hk, ttLeft_congr k fun i hi => h i (by omega),
        h ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · rw [ttLeft_succ_of_le G k (not_lt.mp hk), ttLeft_succ_of_le G' k (not_lt.mp hk)]

/-- The right interface `X_{>k}` depends only on the cores `k, …, d - 1` (0-based). -/
theorem ttRight_congr {G G' : TTCores ι β} (k : ℕ) (h : ∀ i : Fin d, k ≤ i.val → G i = G' i) :
    ttRight G k = ttRight G' k := by
  induction hn : d - k generalizing k with
  | zero => rw [ttRight_of_le G k (by omega), ttRight_of_le G' k (by omega)]
  | succ n ih =>
    have hk : k < d := by omega
    funext y a
    rw [ttRight_of_lt G k hk, ttRight_of_lt G' k hk,
      ih (k + 1) (fun i hi => h i (by omega)) (by omega), h ⟨k, hk⟩ le_rfl]

/-- **Expansion of a tensor train around core `k`**:
`Y(x) = ∑_{α, α'} X_{≤k}(x_{<k}, α) C_k(α, x_k, α') X_{>k+1}(x_{>k}, α')`. -/
theorem tt_apply_eq_sum_core (G : TTCores ι β) (k : ℕ) (hk : k < d) (x : ∀ i, ι i) :
    tt G x = ∑ a, ∑ b, ttLeft G k (Subtype.restrict (fun i : Fin d => i.val < k) x) a *
      G ⟨k, hk⟩ a (x ⟨k, hk⟩) b *
      ttRight G (k + 1) (Subtype.restrict (fun i : Fin d => ¬ i.val < k + 1) x) b := by
  rw [tt_apply_eq_sum G k hk.le x]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ttRight_of_lt G k hk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [restrictLE_restrict, Subtype.restrict_apply]
  ring

end Locality

/-! ### Replacing one core -/

section Update

/-- Replacing core `k` does not change the left interfaces `X_{≤j}` for `j ≤ k`. -/
theorem ttLeft_update (G : TTCores ι β) (k : Fin d) (C : β k → ι k → β (k + 1) → ℝ) {j : ℕ}
    (hj : j ≤ k.val) : ttLeft (Function.update G k C) j = ttLeft G j :=
  ttLeft_congr j fun i hi =>
    Function.update_of_ne (fun h => absurd (congrArg Fin.val h) (by omega)) C G

/-- Replacing core `k` does not change the right interfaces `X_{>j}` for `j > k`. -/
theorem ttRight_update (G : TTCores ι β) (k : Fin d) (C : β k → ι k → β (k + 1) → ℝ) {j : ℕ}
    (hj : k.val < j) : ttRight (Function.update G k C) j = ttRight G j :=
  ttRight_congr j fun i hi =>
    Function.update_of_ne (fun h => absurd (congrArg Fin.val h) (by omega)) C G

/-- The tensor train with core `k` replaced by `C`:
`Y(x) = ∑_{α, α'} X_{≤k}(x_{<k}, α) C(α, x_k, α') X_{>k+1}(x_{>k}, α')`. -/
theorem tt_update_apply (G : TTCores ι β) (k : ℕ) (hk : k < d)
    (C : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) (x : ∀ i, ι i) :
    tt (Function.update G ⟨k, hk⟩ C) x = ∑ a, ∑ b,
      ttLeft G k (Subtype.restrict (fun i : Fin d => i.val < k) x) a * C a (x ⟨k, hk⟩) b *
      ttRight G (k + 1) (Subtype.restrict (fun i : Fin d => ¬ i.val < k + 1) x) b := by
  rw [tt_apply_eq_sum_core _ k hk x, ttLeft_update G ⟨k, hk⟩ C le_rfl,
    ttRight_update G ⟨k, hk⟩ C (Nat.lt_succ_self k), Function.update_self]

/-- **Tensor trains with a single varying core** (arXiv 2512.14950, operation 3, Eq. (2.4)): two
tensor trains that differ only in core `k` add up to the tensor train whose core `k` is the sum of
the two cores; the bond dimensions do not grow. -/
theorem tt_update_add (G : TTCores ι β) (k : ℕ) (hk : k < d)
    (C C' : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) :
    tt (Function.update G ⟨k, hk⟩ (C + C')) =
      tt (Function.update G ⟨k, hk⟩ C) + tt (Function.update G ⟨k, hk⟩ C') := by
  ext x
  simp only [PiLp.add_apply, tt_update_apply, Pi.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib]

/-- **Scaling one core** scales the tensor train (arXiv 2512.14950, operation 1, Eq. (2.2)). -/
theorem tt_update_smul (G : TTCores ι β) (k : ℕ) (hk : k < d) (c : ℝ)
    (C : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) :
    tt (Function.update G ⟨k, hk⟩ (c • C)) = c • tt (Function.update G ⟨k, hk⟩ C) := by
  ext x
  simp only [PiLp.smul_apply, tt_update_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Scaling a tensor train** (arXiv 2512.14950, operation 1, Eq. (2.2)): `c Y` is the tensor
train with core `k` replaced by `c C_k`, for any `k`. -/
theorem tt_update_self_smul (G : TTCores ι β) (k : ℕ) (hk : k < d) (c : ℝ) :
    tt (Function.update G ⟨k, hk⟩ (c • G ⟨k, hk⟩)) = c • tt G := by
  rw [tt_update_smul, Function.update_eq_self]

end Update

/-! ### Gauge transformations -/

section Gauge

/-- **Gauge transformation across a bond.** If the cores `G'` agree with `G` except at the cores
`k` and `k + 1`, where `C'_k = C_k ×₃ R` (`C'_k(α, x, γ) = ∑_β C_k(α, x, β) R(β, γ)`) and
`C_{k+1} = R ×₁ C'_{k+1}` (`C_{k+1}(β, x, α') = ∑_γ R(β, γ) C'_{k+1}(γ, x, α')`), then `G` and
`G'` represent the same tensor. With `C_k = Q R` a QR (or `C_{k+1} = R Q` an RQ) factorization
this is one step of the orthonormalization sweeps (arXiv 2512.14950, operations 7–8, Eqs.
(2.8)–(2.14)), with `R = C_j` the shift of the orthogonality centre (arXiv 2603.13990, Eqs.
(4.11) and (4.13)), and with `R C⁻¹ = 1` the gauge invariance noted after Eq. (4.3) of arXiv
2603.13990. -/
theorem tt_gauge {G G' : TTCores ι β} {k : ℕ} (hk : k + 1 < d)
    (R : Matrix (β (k + 1)) (β (k + 1)) ℝ)
    (hl : ∀ (a : β k) (x : ι ⟨k, Nat.lt_of_succ_lt hk⟩) (c : β (k + 1)),
      G' ⟨k, Nat.lt_of_succ_lt hk⟩ a x c = ∑ b, G ⟨k, Nat.lt_of_succ_lt hk⟩ a x b * R b c)
    (hr : ∀ b x b', G ⟨k + 1, hk⟩ b x b' = ∑ c, R b c * G' ⟨k + 1, hk⟩ c x b')
    (hrest : ∀ i : Fin d, i.val ≠ k → i.val ≠ k + 1 → G' i = G i) : tt G' = tt G := by
  have hk' : k < d := by omega
  have hL : ∀ y c, ttLeft G' (k + 1) y c = ∑ b, ttLeft G (k + 1) y b * R b c := by
    intro y c
    have e : ttLeft G' k = ttLeft G k :=
      ttLeft_congr k fun i hi => hrest i (by omega) (by omega)
    rw [ttLeft_succ G' k hk', e]
    simp only [ttLeft_succ G k hk', hl, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring)
  have hR : ∀ z b, ttRight G (k + 1) z b = ∑ c, R b c * ttRight G' (k + 1) z c := by
    intro z b
    have e : ttRight G' (k + 1 + 1) = ttRight G (k + 1 + 1) :=
      ttRight_congr (k + 1 + 1) fun i hi => hrest i (by omega) (by omega)
    rw [ttRight_of_lt G (k + 1) hk]
    simp only [ttRight_of_lt G' (k + 1) hk, e, hr, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b' _ => by ring)
  ext x
  rw [tt_apply_eq_sum G' (k + 1) hk.le x, tt_apply_eq_sum G (k + 1) hk.le x]
  simp only [hL, hR, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring)

end Gauge

/-! ### Rank-one tensor trains, Hadamard products and sums of entries -/

section RankOne

/-- The first `k + 1` modes are the first `k` modes and mode `k`. -/
lemma filter_lt_succ (k : ℕ) (h : k < d) :
    Finset.univ.filter (fun i : Fin d => i.val < k + 1) =
      insert ⟨k, h⟩ (Finset.univ.filter (fun i : Fin d => i.val < k)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

/-- Mode `k` is not among the first `k` modes. -/
lemma not_mem_filter_lt (k : ℕ) (h : k < d) :
    (⟨k, h⟩ : Fin d) ∉ Finset.univ.filter (fun i : Fin d => i.val < k) := by
  simp

/-- Multiplying every core entrywise by a factor `u i (x_i)` multiplies the left interfaces by
the product of the factors of the first `k` modes. -/
theorem ttLeft_mul_rankOne (G : TTCores ι β) (u : ∀ i, ι i → ℝ) (x : ∀ i, ι i) :
    ∀ k ≤ d, ∀ b, ttLeft (fun i a c b' => u i c * G i a c b') k
        (Subtype.restrict (fun i : Fin d => i.val < k) x) b =
      (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), u i (x i)) *
        ttLeft G k (Subtype.restrict (fun i : Fin d => i.val < k) x) b
  | 0, _, b => by simp
  | k + 1, hk, b => by
    have h : k < d := hk
    rw [ttLeft_succ _ k h, ttLeft_succ G k h, filter_lt_succ k h,
      Finset.prod_insert (not_mem_filter_lt k h), Finset.mul_sum]
    simp only [restrictLE_restrict, Subtype.restrict_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ttLeft_mul_rankOne G u x k h.le a]
    ring

/-- **Entrywise product with a rank-one factor**: multiplying every core entrywise by
`u i (x_i)` multiplies the tensor train by `∏ᵢ u i (x_i)`. -/
theorem tt_mul_rankOne (G : TTCores ι β) (u : ∀ i, ι i → ℝ) (x : ∀ i, ι i) :
    tt (fun i a c b => u i c * G i a c b) x = (∏ i, u i (x i)) * tt G x := by
  change ∑ b, ttLeft _ d _ b = (∏ i, u i (x i)) * ∑ b, ttLeft G d _ b
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ttLeft_mul_rankOne G u x d le_rfl b,
    Finset.filter_true_of_mem fun (i : Fin d) _ => i.2]

/-- The left interfaces of a rank-one tensor train (all bonds of size one) are products of core
entries. -/
theorem ttLeft_rankOne [∀ k, Unique (β k)] (G : TTCores ι β) (x : ∀ i, ι i) :
    ∀ k ≤ d, ttLeft G k (Subtype.restrict (fun i : Fin d => i.val < k) x) default =
      ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), G i default (x i) default
  | 0, _ => by simp
  | k + 1, hk => by
    have h : k < d := hk
    rw [ttLeft_succ G k h, filter_lt_succ k h, Finset.prod_insert (not_mem_filter_lt k h),
      Fintype.sum_unique]
    simp only [restrictLE_restrict, Subtype.restrict_apply]
    rw [ttLeft_rankOne G x k h.le]
    ring

/-- **Rank-one tensor trains** (all bonds of size one) are products of their core entries:
`Y(x) = ∏ᵢ C_i(x_i)`. -/
theorem tt_rankOne [∀ k, Unique (β k)] (G : TTCores ι β) (x : ∀ i, ι i) :
    tt G x = ∏ i, G i default (x i) default := by
  change ∑ b, ttLeft G d _ b = _
  rw [Fintype.sum_unique, ttLeft_rankOne G x d le_rfl,
    Finset.filter_true_of_mem fun (i : Fin d) _ => i.2]

/-- **Hadamard product with a rank-one tensor train** (arXiv 2512.14950, operation 5, Eq. (2.6)):
for a rank-one tensor train `A` and any tensor train `B`, `A ⊙ B` is the tensor train with cores
`A_i(x_i) B_i(α, x_i, α')`, with the bond dimensions of `B`. -/
theorem tt_hadamard_rankOne {γ : ℕ → Type*} [∀ k, Fintype (γ k)] [∀ k, Unique (γ k)]
    (A : TTCores ι γ) (G : TTCores ι β) (x : ∀ i, ι i) :
    tt (fun i a c b => A i default c default * G i a c b) x = tt A x * tt G x := by
  rw [tt_mul_rankOne, tt_rankOne A x]

/-- **Entrywise inverse of a rank-one tensor train** (arXiv 2512.14950, operation 4, Eq. (2.5)):
inverting every core entry inverts every entry of the tensor train. -/
theorem tt_inv_rankOne [∀ k, Unique (β k)] (G : TTCores ι β) (x : ∀ i, ι i) :
    tt (fun i a c b => (G i a c b)⁻¹) x = (tt G x)⁻¹ := by
  rw [tt_rankOne, tt_rankOne, Finset.prod_inv_distrib]

/-- The entrywise inverse of a rank-one tensor train with nonzero core entries is a
multiplicative inverse (arXiv 2512.14950, Eq. (2.5), where all entries are assumed nonzero). -/
theorem tt_mul_tt_inv_rankOne [∀ k, Unique (β k)] (G : TTCores ι β)
    (hG : ∀ i a c b, G i a c b ≠ 0) (x : ∀ i, ι i) :
    tt G x * tt (fun i a c b => (G i a c b)⁻¹) x = 1 := by
  rw [tt_inv_rankOne, tt_rankOne]
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hG _ _ _ _)

/-- Summing the left interfaces over the physical indices gives the left interfaces of the
tensor train of the summed cores `∑_x C_i(·, x, ·)` (with one-point physical index sets). -/
theorem sum_ttLeft [∀ i, Fintype (ι i)] (G : TTCores ι β) :
    ∀ k ≤ d, ∀ (u : ∀ _ : {i : Fin d // i.val < k}, Unit) b, ∑ y, ttLeft G k y b =
      ttLeft (ι := fun _ : Fin d => Unit) (fun i a _ b' => ∑ c, G i a c b') k u b
  | 0, _, _, b => by
    have : IsEmpty {i : Fin d // i.val < 0} := ⟨fun i => Nat.not_lt_zero _ i.2⟩
    simp
  | k + 1, hk, u, b => by
    have h : k < d := hk
    have ih : ∀ a, ttLeft (ι := fun _ : Fin d => Unit) (fun i a _ b' => ∑ c, G i a c b') k
        (restrictLE (ι := fun _ : Fin d => Unit)
          (fun (i : Fin d) (hi : i.val < k) => Nat.lt_succ_of_lt hi) u) a =
        ∑ y, ttLeft G k y a := fun a => (sum_ttLeft G k h.le _ a).symm
    rw [sum_prefixSucc k h, ttLeft_succ _ k h]
    simp only [ttLeft_succ G k h, restrictLE_prefixSuccEquiv_symm,
      prefixSuccEquiv_symm_apply_self, ih, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm.trans
      ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm)

/-- **Sum of all entries of a tensor train** (arXiv 2512.14950, operation 6, Eq. (2.7)):
`∑ₓ Y(x)` is the contraction of the summed cores `∑_{x_i} C_i(·, x_i, ·)`, i.e. the tensor train
of the summed cores at the single multi-index of the one-point physical index sets. -/
theorem sum_tt [∀ i, Fintype (ι i)] (G : TTCores ι β) :
    ∑ x, tt G x =
      tt (ι := fun _ : Fin d => Unit) (fun i a _ b => ∑ c, G i a c b) fun _ => () := by
  have : IsEmpty {i : Fin d // ¬ i.val < d} := ⟨fun i => i.2 i.1.2⟩
  change ∑ x, ∑ b, ttLeft G d (Subtype.restrict (fun i : Fin d => i.val < d) x) b =
    ∑ b, ttLeft _ d (Subtype.restrict (fun i : Fin d => i.val < d) fun _ => ()) b
  rw [sum_eq_sum_merge (fun i : Fin d => i.val < d)]
  simp only [restrict_merge, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => sum_ttLeft G d le_rfl _ b)

/-- **Bond dimensions of a sum of tensor trains** (arXiv 2512.14950, operation 2, Eq. (2.3)): the
`k`-th unfolding of the sum of two tensor trains with bond dimensions `|β k|` and `|β' k|` has
rank at most `|β k| + |β' k|`. -/
theorem rank_unfold_tt_add_le [∀ i, Fintype (ι i)] {β' : ℕ → Type*} [∀ k, Fintype (β' k)]
    (A : TTCores ι β) (B : TTCores ι β') (k : ℕ) (hk : k ≤ d) :
    (unfold (fun i : Fin d => i.val < k) (tt A + tt B)).rank ≤
      Fintype.card (β k) + Fintype.card (β' k) :=
  (rank_unfold_add_le _ _ _).trans
    (add_le_add (rank_unfold_tt_le A k hk) (rank_unfold_tt_le B k hk))

end RankOne

/-! ### Mixed canonical and bond-centred forms -/

section Canonical

/-- The cores `A i` for `i < k` followed by the cores `B i` for `i ≥ k` (the mixed canonical form
with left-orthogonal `A` and right-orthogonal `B`, arXiv 2603.13990, Eq. (4.4)). -/
def ttMix (A B : TTCores ι β) (k : ℕ) : TTCores ι β := fun i => if i.val < k then A i else B i

/-- The left interfaces of `ttMix A B k` up to `k` are those of `A`. -/
theorem ttLeft_ttMix (A B : TTCores ι β) {j k : ℕ} (hj : j ≤ k) :
    ttLeft (ttMix A B k) j = ttLeft A j :=
  ttLeft_congr j fun i hi => by simp [ttMix, show i.val < k by omega]

/-- The right interfaces of `ttMix A B k` from `k` on are those of `B`. -/
theorem ttRight_ttMix (A B : TTCores ι β) {j k : ℕ} (hj : k ≤ j) :
    ttRight (ttMix A B k) j = ttRight B j :=
  ttRight_congr j fun i hi => by simp [ttMix, show ¬ i.val < k by omega]

/-- The **bond-centred tensor train** (arXiv 2603.13990, Eq. (4.12); the forms (II) and (IV) of
arXiv 2512.14950, Eq. (3.6)): `Y⟨k⟩ = X_{≤k} S X_{>k}ᵀ` with left interface of `A`, bond matrix
`S` and right interface of `B`. -/
noncomputable def ttBond (A B : TTCores ι β) (k : ℕ) (S : Matrix (β k) (β k) ℝ) : Tensor ι :=
  WithLp.toLp 2 fun x => ∑ a, ∑ a',
    ttLeft A k (Subtype.restrict (fun i : Fin d => i.val < k) x) a * S a a' *
      ttRight B k (Subtype.restrict (fun i : Fin d => ¬ i.val < k) x) a'

/-- The entries of the bond-centred tensor train. -/
theorem ttBond_apply (A B : TTCores ι β) (k : ℕ) (S : Matrix (β k) (β k) ℝ) (x : ∀ i, ι i) :
    ttBond A B k S x = ∑ a, ∑ a',
      ttLeft A k (Subtype.restrict (fun i : Fin d => i.val < k) x) a * S a a' *
        ttRight B k (Subtype.restrict (fun i : Fin d => ¬ i.val < k) x) a' := rfl

/-- The `k`-th unfolding of the bond-centred tensor train is `X_{≤k} S X_{>k}ᵀ`. -/
theorem unfold_ttBond (A B : TTCores ι β) (k : ℕ) (S : Matrix (β k) (β k) ℝ) :
    unfold (fun i : Fin d => i.val < k) (ttBond A B k S) = ttLeft A k * S * (ttRight B k)ᵀ := by
  ext y z
  simp only [unfold_apply, ttBond_apply, restrict_merge, restrict_not_merge, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- **The bond-centred form is a tensor train** (arXiv 2603.13990, Eq. (4.13); arXiv 2512.14950,
Eqs. (3.14), (3.22)): merging the bond matrix into the next core, `M_k = S C_k`, gives the tensor
train with the cores of `A` before `k`, the core `M_k` and the cores of `B` after `k`. -/
theorem ttBond_eq_tt (A B : TTCores ι β) (k : ℕ) (hk : k < d) (S : Matrix (β k) (β k) ℝ) :
    ttBond A B k S = tt (Function.update (ttMix A B k) ⟨k, hk⟩
      fun a c b => ∑ a', S a a' * B ⟨k, hk⟩ a' c b) := by
  ext x
  rw [tt_update_apply, ttBond_apply, ttLeft_ttMix A B le_rfl,
    ttRight_ttMix A B (Nat.le_succ k)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ttRight_of_lt B k hk, restrictLE_restrict, Subtype.restrict_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

/-- **Schmidt rank** (arXiv 2603.13990, after Eq. (4.12)): with orthonormal interfaces
(`X_{≤k}ᵀ X_{≤k} = 1`, `X_{>k}ᵀ X_{>k} = 1`) the rank of the `k`-th unfolding of the bond-centred
tensor train equals the rank of its bond matrix. -/
theorem rank_unfold_ttBond [∀ i, Fintype (ι i)] [∀ k, DecidableEq (β k)] {A B : TTCores ι β}
    {k : ℕ}
    (hA : (ttLeft A k)ᵀ * ttLeft A k = 1) (hB : (ttRight B k)ᵀ * ttRight B k = 1)
    (S : Matrix (β k) (β k) ℝ) :
    (unfold (fun i : Fin d => i.val < k) (ttBond A B k S)).rank = S.rank := by
  rw [unfold_ttBond]
  refine le_antisymm ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)) ?_
  have hS : S = (ttLeft A k)ᵀ * (ttLeft A k * S * (ttRight B k)ᵀ) * ttRight B k := by
    simp only [Matrix.mul_assoc]
    rw [hB, Matrix.mul_one, ← Matrix.mul_assoc, hA, Matrix.one_mul]
  calc S.rank = ((ttLeft A k)ᵀ * (ttLeft A k * S * (ttRight B k)ᵀ) * ttRight B k).rank := by
        rw [← hS]
    _ ≤ _ := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- **A tensor train is fixed by the right interface projectors of its own right-orthogonal
cores**: `P_{>k} Y = Y` if the cores `k, …, d - 1` (0-based) of `Y = tt G` are right-orthogonal
(the right analogue of `ttLeftProj_tt`; arXiv 2603.13990, before Eq. (4.22)). -/
theorem ttRightProj_tt [∀ i, Fintype (ι i)] [Subsingleton (β d)] [∀ k, DecidableEq (β k)]
    {G : TTCores ι β} {k : ℕ} (hk : k ≤ d) (hG : ∀ i : Fin d, k ≤ i.val → IsRightOrth G i) :
    ttRightProj G k (tt G) = tt G :=
  actOn_mul_transpose_apply_eq_self_of _ (ttRight_transpose_mul_self k hk hG)
    (fun a x => ttLeft G k (Subtype.restrict (fun i : Fin d => i.val < k) x) a)
    (fun a x z => by
      rw [restrict_override_of_disjoint (fun (i : Fin d) (hi : ¬ i.val < k) => hi)])
    (fun x => by
      rw [tt_apply_eq_sum G k hk x]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _)

end Canonical

/-! ### Examples -/

/-- Non-vacuity of the rank-one statements: on two modes of size two with one-element bonds, the
cores `C(α, x, α') = 2` give the constant tensor train `4`. -/
example (x : Fin 2 → Fin 2) :
    tt (d := 2) (ι := fun _ => Fin 2) (β := fun _ => Unit) (fun _ _ _ _ => (2 : ℝ)) x = 4 := by
  rw [tt_rankOne]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

end LeanDLRA.Tensor
