import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Tensor.TTN.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Results of arXiv 2501.04157: Automatic partitioning for low-rank stochastic Boolean networks

Three abstract cores of the paper, each stated on matrices, Boolean rules or finite tensors.

* **Sec. 3.1, one-level DLR ansatz** (`normal_leftMul_eq_zero`, `normal_rightMul_eq_zero`).
  The paper writes `P(t, x) ≈ ∑ X⁰_{i₀} S_{i₀ i₁} X¹_{i₁}` and says that reactions depending
  only on the species of one partition are treated exactly. The paper does not state the
  normal-component identity itself; it is the statement of the header, proved here in matrix form.
  Let `Q = rightProj V` and `Y` satisfy `Q Y = Y`, i.e. `Y = C Vᵀ` for some `C`. Then left
  multiplication `Y ↦ M Y` by any matrix `M` acting on the first index has zero normal part
  `(1 - Q)(M Y)`. The mirror statement holds for right multiplication and `leftProj`.
  Non-vacuity: `oneLevel_instance` exhibits `Y = C Vᵀ` with orthonormal `V`.

* **Sec. 4.2, rule-specific information entropy** (`binEntBits`, `ruleProb`, `ruleEntropy`,
  `totalEntropy`, `totalEntropy_mem`). We take the paper's definitions over finite Boolean rules
  `B i : α i → β i → Bool`, with `p_i(x) = |{c : B_i(x, c)}| / |β_i|`, `h̃ = h₂(p)` the binary
  entropy in bits, `h_i` the average of `h̃` over `α_i`, and `H = ∑ᵢ h_i`. The paper's `h₂` is
  `Real.binEntropy / log 2`. Proved: every `h_i` and `H` lies in `[0, d]`, the paper's range claim.
  Examples: a negation-type rule `B x c = !c` has `h = 1` (`ruleEntropy_negation`), and a rule
  depending only on its own species has `h = 0` (`ruleEntropy_absorption`).
  On the state space `Ω = {0,1}^d` itself, `partEntropy p B` is Eqs. (6)–(8) for the partition
  `{k | p k}`, the state split as `x = (xᵢ, xᵢ^∁)` by the core multi-index merge
  `Tensor.merge`, and `partitionEntropy` is Eq. (9) for a partitioning, with `hᵢ` taken for the
  partition containing species `i` (`partitionEntropy_mem`: `H ∈ [0, d]`). The five rules of
  Table 1 are `ruleB0`, …, `ruleB4` (`fiveRules`); Table 2b is `ruleB2_eq`. The three values of
  Sec. 4.2 are proved for every partitioning that cuts the respective pathway: `h₀ = 1`
  (`partEntropy_ruleB0`), `h₂ = 0` (`partEntropy_ruleB2`), `h₃ = 1/2` (`partEntropy_ruleB3`).
  `ruleEntropy_eq_zero_iff` adds that `h = 0` holds exactly for rules that do not depend on the
  complement (the paper's reading "no information is lost", made precise; not stated there).

* **Sec. 3.2, hierarchical tree tensor network**. The paper's recursive decomposition Eq. (4),
  `X^τ_{iτ}(x^τ) = ∑ X^{τ₀}_{iτ₀}(x^{τ₀}) Q^τ_{iτ iτ₀ iτ₁} X^{τ₁}_{iτ₁}(x^{τ₁})`, is the basis
  recursion of the core tree tensor network `TTN` at a binary node (`basis_binary`), with
  `Q^τ = connTensor C` the root matricization `Mat₀(C)` of the core connecting tensor read as an
  `r_τ × r_{τ₀} × r_{τ₁}` array. The rank conditions Eq. (5) follow from full multilinear rank
  (`tucker_full_rank_requires` for any `Q : Fin a → Fin b → Fin c → ℝ`;
  `rank_conditions_binary` for TTN nodes), and the first of the three rank hypotheses holds for
  every orthonormal node (`rank_modeFlat0_of_orthonormal`). The paper's claim is only this
  necessity direction. `tensor_diag_fullRank` shows the hypotheses are satisfiable (a diagonal
  tensor on `Fin 2`).

Not formalized: Algorithm 1 (Kernighan–Lin pool and entropy selection, a graph heuristic) and the
numerical observations of Sec. 5.

Core definitions used: `rightProj`, `leftProj` (Sec. 3.1), `Tensor.merge` (Sec. 4.2), `DimTree`,
`TTN`, `TTN.basis`, `TTN.IsOrthonormal` (Sec. 3.2). Local definitions: the entropy quantities
of Sec. 4.2 (no core counterpart), the flattenings `modeFlat0`–`modeFlat2` of a three-way array
and `connTensor` (bridged to the core TTN by `basis_binary` and `rank_modeFlat0_connTensor`).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2501_04157

/-! ### Sec. 3.1: one-level DLR ansatz -/

section OneLevel

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-- Reactions acting on the first index are left multiplications `Y ↦ M Y`. If `Y = C Vᵀ`
(equivalently `rightProj V Y = Y`) then the normal part of `M Y` with respect to `rightProj V`
vanishes, for every `V` and every `M`. Paper: arXiv 2501.04157, Sec. 3.1. -/
theorem normal_leftMul_eq_zero (V : Matrix n k ℝ) (M : Matrix m m ℝ) (Y : Matrix m n ℝ)
    (hY : rightProj V Y = Y) : (1 - rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (M * Y) = 0 := by
  have hY' : Y * (V * Vᵀ) = Y := by rw [← rightProj_apply', hY]
  have hassoc : M * Y * V * Vᵀ = M * (Y * (V * Vᵀ)) := by simp only [Matrix.mul_assoc]
  simp only [sub_apply, one_apply_eq_self, rightProj_apply,
    sub_eq_zero, hassoc, hY']

/-- Mirror statement: a right multiplication `Y ↦ Y N` has zero normal part with respect to
`leftProj U` whenever `leftProj U Y = Y`. Paper: arXiv 2501.04157, Sec. 3.1. -/
theorem normal_rightMul_eq_zero (U : Matrix m k ℝ) (N : Matrix n n ℝ) (Y : Matrix m n ℝ)
    (hY : leftProj U Y = Y) : (1 - leftProj U : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (Y * N) = 0 := by
  have hY' : (U * Uᵀ) * Y = Y := by rw [← leftProj_apply, hY]
  have hassoc : U * Uᵀ * (Y * N) = (U * Uᵀ * Y) * N := by simp only [Matrix.mul_assoc]
  simp only [sub_apply, one_apply_eq_self, leftProj_apply,
    sub_eq_zero, hassoc, hY']

/-- Non-vacuity: the DLR form `Y = C Vᵀ` with orthonormal `V` satisfies the hypothesis. -/
theorem oneLevel_instance [DecidableEq k] (V : Matrix n k ℝ) (hV : Vᵀ * V = 1) (M : Matrix m m ℝ)
    (C : Matrix m k ℝ) :
    (1 - rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (M * (C * Vᵀ)) = 0 :=
  normal_leftMul_eq_zero V M (C * Vᵀ) (rightProj_mul_transpose hV C)

end OneLevel

/-! ### Sec. 4.2: rule-specific information entropy -/

/-- Binary entropy in bits, `h₂(p) = -p log₂ p - (1 - p) log₂ (1 - p)`. -/
noncomputable def binEntBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- The fraction `p(x)` of configurations `c` of the complement where the rule `B x c` is true. -/
noncomputable def ruleProb {α β : Type*} [Fintype β] (B : α → β → Bool) (x : α) : ℝ :=
  ((univ.filter fun c => B x c = true).card : ℝ) / Fintype.card β

/-- The rule-specific entropy `h_i`: the mean of `h₂(p_i(x))` over the species `x ∈ α`. -/
noncomputable def ruleEntropy {α β : Type*} [Fintype α] [Fintype β] (B : α → β → Bool) : ℝ :=
  (∑ x, binEntBits (ruleProb B x)) / Fintype.card α

/-- The total entropy `H = ∑ᵢ h_i` over `d` rules. -/
noncomputable def totalEntropy {d : ℕ} {α β : Fin d → Type*} [∀ i, Fintype (α i)]
    [∀ i, Fintype (β i)] (B : ∀ i, α i → β i → Bool) : ℝ :=
  ∑ i, ruleEntropy (B i)

/-- The average of `d` numbers in `[0, 1]` lies in `[0, 1]`. -/
private lemma avg_mem_unit {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, f i ∈ Icc (0 : ℝ) 1) :
    (∑ i, f i) / Fintype.card ι ∈ Icc (0 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  · have hpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h
    refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => (hf i).1) hpos.le, ?_⟩
    rw [div_le_one hpos]
    calc ∑ i, f i ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum fun i _ => (hf i).2
      _ = Fintype.card ι := by simp

private lemma binEntBits_mem {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : binEntBits p ∈ Icc (0 : ℝ) 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  exact ⟨div_nonneg (Real.binEntropy_nonneg hp.1 hp.2) hl.le,
    (div_le_one hl).2 Real.binEntropy_le_log_two⟩

private lemma ruleProb_mem {α β : Type*} [Fintype β] (B : α → β → Bool) (x : α) :
    ruleProb B x ∈ Icc (0 : ℝ) 1 := by
  have hcard : ((univ.filter fun c => B x c = true).card : ℝ) ≤ Fintype.card β := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  rcases Nat.eq_zero_or_pos (Fintype.card β) with h | h
  · simp [ruleProb, h]
  · have hpos : (0 : ℝ) < Fintype.card β := by exact_mod_cast h
    exact ⟨div_nonneg (by positivity) hpos.le, (div_le_one hpos).2 hcard⟩

/-- Each rule entropy lies in `[0, 1]`. -/
private lemma ruleEntropy_mem {α β : Type*} [Fintype α] [Fintype β] (B : α → β → Bool) :
    ruleEntropy B ∈ Icc (0 : ℝ) 1 :=
  avg_mem_unit _ fun x => binEntBits_mem (ruleProb_mem B x)

/-- Range of the total entropy: `0 ≤ H ≤ d`. Paper: arXiv 2501.04157, Sec. 4.2. -/
theorem totalEntropy_mem {d : ℕ} {α β : Fin d → Type*} [∀ i, Fintype (α i)]
    [∀ i, Fintype (β i)] (B : ∀ i, α i → β i → Bool) :
    0 ≤ totalEntropy B ∧ totalEntropy B ≤ d := by
  unfold totalEntropy
  constructor
  · exact Finset.sum_nonneg fun i _ => (ruleEntropy_mem (B i)).1
  · calc ∑ i, ruleEntropy (B i) ≤ ∑ _i : Fin d, (1:ℝ) :=
          Finset.sum_le_sum fun i _ => (ruleEntropy_mem (B i)).2
      _ = d := by simp

/-- Negation-type rule `B x c = ¬c`: `p = 1/2` for every species, so `h = 1` (paper's `h₀ = 1`). -/
theorem ruleEntropy_negation : ruleEntropy (fun (_ : Unit) (c : Bool) => !c) = 1 := by
  have hc : (univ.filter fun c : Bool => (!c) = true).card = 1 := by decide
  have hp : ruleProb (fun (_ : Unit) (c : Bool) => !c) () = 2⁻¹ := by
    simp only [ruleProb, hc, Fintype.card_bool]
    norm_num
  have h2 : binEntBits 2⁻¹ = 1 := by
    unfold binEntBits
    rw [Real.binEntropy_two_inv]
    exact div_self (Real.log_pos one_lt_two).ne'
  simp [ruleEntropy, hp, h2]

/-- Absorption-type rule `B x c = x` depending only on its own species: `p ∈ {0, 1}`, so `h = 0`. -/
theorem ruleEntropy_absorption : ruleEntropy (fun (x : Bool) (_ : Bool) => x) = 0 := by
  have hp : ∀ x : Bool, binEntBits (ruleProb (fun (x : Bool) (_ : Bool) => x) x) = 0 := by
    intro x
    cases x <;> simp [ruleProb, binEntBits]
  simp [ruleEntropy, hp]

/-! ### Sec. 4.2: rules on a partition and the five-species example -/

section Partition

/-- Half of the Boolean assignments `b : S → Bool` take a prescribed value at a given
coordinate (the involution flipping coordinate `j` exchanges the two halves). -/
lemma two_mul_card_filter_apply_eq {S : Type*} [Fintype S] [DecidableEq S] (j : S) (v : Bool) :
    2 * (univ.filter fun b : S → Bool => b j = v).card = Fintype.card (S → Bool) := by
  set flip : (S → Bool) ≃ (S → Bool) :=
    { toFun := fun b => Function.update b j (!b j)
      invFun := fun b => Function.update b j (!b j)
      left_inv := fun b => by funext k; by_cases hk : k = j <;> simp [hk]
      right_inv := fun b => by funext k; by_cases hk : k = j <;> simp [hk] }
  have hswap : (univ.filter fun b : S → Bool => b j = v).card =
      (univ.filter fun b : S → Bool => ¬ b j = v).card := by
    refine Finset.card_bij (fun b _ => flip b) (fun b hb => ?_) (fun b _ b' _ h => flip.injective h)
      (fun b hb => ⟨flip b, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp [flip, hb]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      cases h : b j <;> cases v <;> simp_all [flip]
    · exact flip.apply_symm_apply b
  have htot := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (S → Bool))) (fun b : S → Bool => b j = v)
  rw [Finset.card_univ] at htot
  omega

/-- If the rule `B x` is true exactly when coordinate `j` of the complement state has value `v`,
then `p(x) = 1/2`. -/
lemma ruleProb_eq_half {α S : Type*} [Fintype S] [DecidableEq S] (B : α → (S → Bool) → Bool)
    (x : α) (j : S) (v : Bool) (h : ∀ b, B x b = true ↔ b j = v) : ruleProb B x = 2⁻¹ := by
  have hf : (univ.filter fun b => B x b = true) = univ.filter fun b : S → Bool => b j = v :=
    Finset.filter_congr fun b _ => h b
  have hc := two_mul_card_filter_apply_eq j v
  have hpos : (0 : ℝ) < Fintype.card (S → Bool) := by exact_mod_cast Fintype.card_pos
  unfold ruleProb
  rw [hf, div_eq_iff hpos.ne', ← hc]
  push_cast
  ring

/-- If the rule `B x` does not depend on the complement state, then `p(x) ∈ {0, 1}`. -/
lemma ruleProb_eq_zero_or_one {α β : Type*} [Fintype β] (B : α → β → Bool) (x : α)
    (h : ∀ b b', B x b = B x b') : ruleProb B x = 0 ∨ ruleProb B x = 1 := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b₀⟩⟩
  · left; simp [ruleProb]
  · cases hb : B x b₀
    · left
      have : (univ.filter fun c => B x c = true) = ∅ :=
        Finset.filter_false_of_mem fun c _ => by rw [h c b₀, hb]; decide
      simp [ruleProb, this]
    · right
      have : (univ.filter fun c => B x c = true) = Finset.univ := by
        ext c; simp [h c b₀, hb]
      have hpos : (0 : ℝ) < Fintype.card β := by
        have : Nonempty β := ⟨b₀⟩
        exact_mod_cast Fintype.card_pos
      simp [ruleProb, this, hpos.ne']

/-- `h₂(1/2) = 1`. -/
lemma binEntBits_two_inv : binEntBits 2⁻¹ = 1 := by
  unfold binEntBits
  rw [Real.binEntropy_two_inv]
  exact div_self (Real.log_pos one_lt_two).ne'

/-- `h₂(p) = 0` for `p ∈ {0, 1}`. -/
lemma binEntBits_eq_zero_of {p : ℝ} (hp : p = 0 ∨ p = 1) : binEntBits p = 0 := by
  rcases hp with rfl | rfl <;> simp [binEntBits]

/-- **Zero entropy for rules that do not depend on the complement** (arXiv 2501.04157, Sec. 4.2,
the absorption-law discussion of `B₂`): if `B x c` does not depend on `c`, then `h = 0`. -/
theorem ruleEntropy_eq_zero_of_indep {α β : Type*} [Fintype α] [Fintype β] (B : α → β → Bool)
    (h : ∀ x b b', B x b = B x b') : ruleEntropy B = 0 := by
  simp [ruleEntropy, binEntBits_eq_zero_of (ruleProb_eq_zero_or_one B _ (h _))]

/-- **Zero entropy characterizes rules that do not depend on the complement**: `h = 0` if and
only if `B x c` does not depend on `c` for any `x`. The paper reads `h = 0` as "no information
is lost" (Sec. 4.2); this makes the reading precise. The `if` direction is
`ruleEntropy_eq_zero_of_indep`. -/
theorem ruleEntropy_eq_zero_iff {α β : Type*} [Fintype α] [Fintype β] (B : α → β → Bool) :
    ruleEntropy B = 0 ↔ ∀ x b b', B x b = B x b' := by
  refine ⟨fun h0 x b b' => ?_, ruleEntropy_eq_zero_of_indep B⟩
  have hα : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨x⟩
    exact_mod_cast Fintype.card_pos
  have hnn : ∀ y, 0 ≤ binEntBits (ruleProb B y) := fun y =>
    (binEntBits_mem (ruleProb_mem B y)).1
  have hsum : ∑ y, binEntBits (ruleProb B y) = 0 := by
    have := h0; unfold ruleEntropy at this
    rwa [div_eq_zero_iff, or_iff_left hα.ne'] at this
  have hx : binEntBits (ruleProb B x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn y).1 hsum x (Finset.mem_univ x)
  have hβ : (0 : ℝ) < Fintype.card β := by
    have : Nonempty β := ⟨b⟩
    exact_mod_cast Fintype.card_pos
  have hbin : Real.binEntropy (ruleProb B x) = 0 := by
    unfold binEntBits at hx
    rwa [div_eq_zero_iff, or_iff_left (Real.log_pos one_lt_two).ne'] at hx
  rcases Real.binEntropy_eq_zero.1 hbin with hp | hp
  · have hc : (univ.filter fun c => B x c = true).card = 0 := by
      unfold ruleProb at hp
      rw [div_eq_zero_iff, or_iff_left hβ.ne'] at hp
      exact_mod_cast hp
    have hf : ∀ c, B x c = false := fun c => by
      have := Finset.card_eq_zero.1 hc
      by_contra hc'
      have hm : c ∈ univ.filter fun c => B x c = true := by simpa using hc'
      simp [this] at hm
    rw [hf b, hf b']
  · have hc : (univ.filter fun c => B x c = true).card = Fintype.card β := by
      unfold ruleProb at hp
      rw [div_eq_one_iff_eq hβ.ne'] at hp
      exact_mod_cast hp
    have hf : ∀ c, B x c = true := fun c => by
      have := Finset.filter_card_eq (hc.trans Finset.card_univ.symm) c (Finset.mem_univ c)
      simpa using this
    rw [hf b, hf b']

variable {d : ℕ}

/-- The **rule-specific entropy for a partition** (arXiv 2501.04157, Eqs. (6)–(8)): the species
`k` with `p k` form the partition `Pᵢ` that contains the updated species, a state is split as
`x = (xᵢ, xᵢ^∁)` by the core multi-index merge `Tensor.merge`, and `h` is `ruleEntropy` of
`(xᵢ, xᵢ^∁) ↦ B(xᵢ, xᵢ^∁)`. -/
noncomputable def partEntropy (p : Fin d → Prop) [DecidablePred p] (B : (Fin d → Bool) → Bool) :
    ℝ :=
  ruleEntropy fun (a : Subtype p → Bool) (b : {k // ¬ p k} → Bool) =>
    B (Tensor.merge (ι := fun _ => Bool) p a b)

/-- The **total entropy of a partitioning** `(P⁰, P¹)` (Eq. (9)): `H = ∑ᵢ hᵢ`, where `hᵢ` is
taken for the partition `Pᵢ = {k | p k ↔ p i}` containing species `i` and `B i` is the rule
updating species `i`. -/
noncomputable def partitionEntropy (p : Fin d → Prop) [DecidablePred p]
    (B : Fin d → (Fin d → Bool) → Bool) : ℝ :=
  ∑ i, partEntropy (fun k => p k ↔ p i) (B i)

/-- The total entropy of a partitioning is an instance of `totalEntropy`, hence lies in
`[0, d]`, the range stated after Eq. (9). -/
theorem partitionEntropy_mem (p : Fin d → Prop) [DecidablePred p]
    (B : Fin d → (Fin d → Bool) → Bool) :
    0 ≤ partitionEntropy p B ∧ partitionEntropy p B ≤ d :=
  totalEntropy_mem (α := fun i => {k // p k ↔ p i} → Bool)
    (β := fun i => {k // ¬ (p k ↔ p i)} → Bool)
    fun i a b => B i (Tensor.merge (ι := fun _ => Bool) (fun k => p k ↔ p i) a b)

/-- The rule `B₀(x) = ¬x₁` of the five-species example (Table 1). -/
def ruleB0 (x : Fin 5 → Bool) : Bool := !x 1

/-- The rule `B₁(x) = x₂ ∨ x₃` (Table 1). -/
def ruleB1 (x : Fin 5 → Bool) : Bool := x 2 || x 3

/-- The rule `B₂(x) = x₂ ∨ (x₂ ∧ x₄)` (Table 1). -/
def ruleB2 (x : Fin 5 → Bool) : Bool := x 2 || (x 2 && x 4)

/-- The rule `B₃(x) = (¬x₂) ∧ x₃` (Table 1). -/
def ruleB3 (x : Fin 5 → Bool) : Bool := !x 2 && x 3

/-- The rule `B₄(x) = x₁ ∧ (¬x₄)` (Table 1). -/
def ruleB4 (x : Fin 5 → Bool) : Bool := x 1 && !x 4

/-- The five rules of Table 1, `Bᵢ` updating species `Sᵢ`. -/
def fiveRules : Fin 5 → (Fin 5 → Bool) → Bool := ![ruleB0, ruleB1, ruleB2, ruleB3, ruleB4]

/-- **Table 2b**: the absorption law, `B₂(x) = x₂`. -/
theorem ruleB2_eq (x : Fin 5 → Bool) : ruleB2 x = x 2 := by
  unfold ruleB2; cases x 2 <;> cases x 4 <;> rfl

/-- The entries of a merged state at a mode in the partition. -/
lemma merge_apply_of {p : Fin d → Prop} [DecidablePred p] (a : Subtype p → Bool)
    (b : {k // ¬ p k} → Bool) {k : Fin d} (hk : p k) :
    Tensor.merge (ι := fun _ => Bool) p a b k = a ⟨k, hk⟩ := by
  simp [Tensor.merge, hk]

/-- The entries of a merged state at a mode outside the partition. -/
lemma merge_apply_of_not {p : Fin d → Prop} [DecidablePred p] (a : Subtype p → Bool)
    (b : {k // ¬ p k} → Bool) {k : Fin d} (hk : ¬ p k) :
    Tensor.merge (ι := fun _ => Bool) p a b k = b ⟨k, hk⟩ := by
  simp [Tensor.merge, hk]

variable (p : Fin 5 → Prop) [DecidablePred p]

/-- **`h₀ = 1`** (arXiv 2501.04157, Sec. 4.2): for every partitioning that cuts the pathway
`S₁ → S₀` (the partition `P₀` of `S₀` does not contain `S₁`), the rule `B₀ = ¬x₁` loses all
information. Only `S₁ ∉ P₀` is used, so the statement is for every partition without `S₁`. -/
theorem partEntropy_ruleB0 (h1 : ¬ p 1) : partEntropy p ruleB0 = 1 := by
  have hp : ∀ a, ruleProb (fun (a : Subtype p → Bool) (b : {k // ¬ p k} → Bool) =>
      ruleB0 (Tensor.merge (ι := fun _ => Bool) p a b)) a = 2⁻¹ := fun a =>
    ruleProb_eq_half _ a ⟨1, h1⟩ false fun b => by
      simp [ruleB0, merge_apply_of_not a b h1]
  have hα : (Fintype.card (Subtype p → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [partEntropy, ruleEntropy, hp, binEntBits_two_inv, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  exact div_self hα

/-- **`h₂ = 0`** (Sec. 4.2): for every partitioning with `S₂` in the partition, the
absorption-law rule `B₂` loses no information, wherever `S₄` lies. -/
theorem partEntropy_ruleB2 (h2 : p 2) : partEntropy p ruleB2 = 0 :=
  ruleEntropy_eq_zero_of_indep _ fun a b b' => by
    simp only [ruleB2_eq, merge_apply_of a _ h2]

/-- **`h₃ = 1/2`** (Sec. 4.2): for every partitioning that cuts the pathway `S₂ → S₃`, the rule
`B₃ = (¬x₂) ∧ x₃` loses half of the information. -/
theorem partEntropy_ruleB3 (h3 : p 3) (h2 : ¬ p 2) : partEntropy p ruleB3 = 1 / 2 := by
  have hp : ∀ a : Subtype p → Bool, binEntBits (ruleProb
      (fun (a : Subtype p → Bool) (b : {k // ¬ p k} → Bool) =>
        ruleB3 (Tensor.merge (ι := fun _ => Bool) p a b)) a) =
      if a ⟨3, h3⟩ = true then 1 else 0 := fun a => by
    by_cases ha : a ⟨3, h3⟩ = true
    · simp only [ha, ↓reduceIte]
      rw [ruleProb_eq_half _ a ⟨2, h2⟩ false fun b => by
        simp [ruleB3, merge_apply_of_not a b h2, merge_apply_of a b h3, ha]]
      exact binEntBits_two_inv
    · simp only [ha, ↓reduceIte, Bool.false_eq_true]
      refine binEntBits_eq_zero_of (ruleProb_eq_zero_or_one _ a fun b b' => ?_)
      simp [ruleB3, merge_apply_of a _ h3, ha]
  have hc := two_mul_card_filter_apply_eq (S := Subtype p) ⟨3, h3⟩ true
  have hα : (0 : ℝ) < Fintype.card (Subtype p → Bool) := by
    exact_mod_cast Fintype.card_pos
  simp only [partEntropy, ruleEntropy, hp]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    div_eq_iff hα.ne']
  have : ((univ.filter fun a : Subtype p → Bool => a ⟨3, h3⟩ = true).card : ℝ) * 2 =
      Fintype.card (Subtype p → Bool) := by
    rw [mul_comm]; exact_mod_cast hc
  linarith

/-- Non-vacuity: the partitioning `P⁰ = {S₀, S₃}` cuts both pathways `S₁ → S₀` and
`S₂ → S₃`, so `h₀ = 1` and `h₃ = 1/2` there. -/
example : partEntropy (· ∈ ({0, 3} : Finset (Fin 5))) ruleB0 = 1 ∧
    partEntropy (· ∈ ({0, 3} : Finset (Fin 5))) ruleB3 = 1 / 2 :=
  ⟨partEntropy_ruleB0 _ (by decide), partEntropy_ruleB3 _ (by decide) (by decide)⟩

end Partition

/-! ### Sec. 3.2: hierarchical tree tensor network -/

/-- Mode-0 flattening of `Q : Fin a → Fin b → Fin c → ℝ`: rows indexed by the first mode. -/
def modeFlat0 {a b c : ℕ} (Q : Fin a → Fin b → Fin c → ℝ) : Matrix (Fin a) (Fin b × Fin c) ℝ :=
  fun i jk => Q i jk.1 jk.2

/-- Mode-1 flattening of `Q`: rows indexed by the second mode. -/
def modeFlat1 {a b c : ℕ} (Q : Fin a → Fin b → Fin c → ℝ) : Matrix (Fin b) (Fin a × Fin c) ℝ :=
  fun j ik => Q ik.1 j ik.2

/-- Mode-2 flattening of `Q`: rows indexed by the third mode. -/
def modeFlat2 {a b c : ℕ} (Q : Fin a → Fin b → Fin c → ℝ) : Matrix (Fin c) (Fin a × Fin b) ℝ :=
  fun k ij => Q ij.1 ij.2 k

/-- Full multilinear rank `(a, b, c)` of the connection tensor forces `a ≤ b c`, `b ≤ c a`,
`c ≤ a b`: each flattening has at most as many columns as the product of the other two modes.
Paper: arXiv 2501.04157, Sec. 3.2 (rank condition for the Tucker split `Q^τ`). -/
theorem tucker_full_rank_requires {a b c : ℕ} (Q : Fin a → Fin b → Fin c → ℝ)
    (h0 : (modeFlat0 Q).rank = a) (h1 : (modeFlat1 Q).rank = b)
    (h2 : (modeFlat2 Q).rank = c) :
    a ≤ b * c ∧ b ≤ c * a ∧ c ≤ a * b := by
  have r0 := (modeFlat0 Q).rank_le_card_width
  have r1 := (modeFlat1 Q).rank_le_card_width
  have r2 := (modeFlat2 Q).rank_le_card_width
  rw [h0] at r0
  rw [h1] at r1
  rw [h2] at r2
  simp only [Fintype.card_prod, Fintype.card_fin] at r0 r1 r2
  exact ⟨r0, by linarith [mul_comm a c], by linarith [mul_comm a b]⟩

/-- A matrix with a right inverse has rank equal to its number of rows. -/
private lemma rank_eq_card_of_mul_eq_one {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {A : Matrix ι κ ℝ} {N : Matrix κ ι ℝ} (h : A * N = 1) : A.rank = Fintype.card ι := by
  apply le_antisymm A.rank_le_card_height
  calc Fintype.card ι = (1 : Matrix ι ι ℝ).rank := (Matrix.rank_one).symm
    _ = (A * N).rank := by rw [h]
    _ ≤ A.rank := Matrix.rank_mul_le_left _ _

/-- The diagonal connection tensor `Q i j k = [i = j = k]` on `Fin 2` has full multilinear
rank `(2, 2, 2)`, so the hypotheses of `tucker_full_rank_requires` are satisfiable. -/
theorem tensor_diag_fullRank :
    let Qd : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k => if i = j ∧ j = k then 1 else 0
    (modeFlat0 Qd).rank = 2 ∧ (modeFlat1 Qd).rank = 2 ∧ (modeFlat2 Qd).rank = 2 := by
  intro Qd
  refine ⟨rank_eq_card_of_mul_eq_one (N := Matrix.of fun p i' => Qd i' p.1 p.2) ?_,
    rank_eq_card_of_mul_eq_one (N := Matrix.of fun p i' => Qd p.1 i' p.2) ?_,
    rank_eq_card_of_mul_eq_one (N := Matrix.of fun p i' => Qd p.1 p.2 i') ?_⟩ <;>
  · ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [Qd, modeFlat0, modeFlat1, modeFlat2, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two]

/-! ### Sec. 3.2: the hierarchical decomposition is a core tree tensor network -/

section TTN

variable {κ : Type*} [DecidableEq κ] {ι : κ → Type*}

/-- The connection tensor `Q^τ_{iτ iτ₀ iτ₁}` of a binary node of a core tree tensor network: the
root matricization `Mat₀(C)` of the connecting tensor read as an `r_τ × r_{τ₀} × r_{τ₁}`
array. -/
def connTensor {rs : Fin 2 → ℕ} {r : ℕ} (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ) :
    Fin r → Fin (rs 0) → Fin (rs 1) → ℝ :=
  fun a b₀ b₁ => C a ((piFinTwoEquiv _).symm (b₀, b₁))

/-- **Eq. (4), hierarchical partitioning** (arXiv 2501.04157, Sec. 3.2): at a binary node `τ`
with subpartitions `τ₀, τ₁`, the low-rank factors of the core tree tensor network satisfy
`X^τ_{iτ}(x^τ) = ∑_{iτ₀, iτ₁} X^{τ₀}_{iτ₀}(x^{τ₀}) Q^τ_{iτ iτ₀ iτ₁} X^{τ₁}_{iτ₁}(x^{τ₁})` with
`X^τ` the basis matrix `TTN.basis` and `Q^τ = connTensor C`. So the paper's binary hierarchical
decomposition is the core `TTN` on a binary dimension tree (the paper's Eq. (2) is the root
with `r_τ = 1`, `TTN.toTensor`). -/
theorem basis_binary {cs : Fin 2 → DimTree κ} {rs : Fin 2 → ℕ} {r : ℕ}
    (ds : ∀ i, TTN ι (cs i) (rs i)) (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ)
    (x : ∀ k : {k // k ∈ (DimTree.node cs).modes}, ι k) (a : Fin r) :
    (TTN.node ds C).basis x a = ∑ b₀, ∑ b₁,
      (ds 0).basis (fun k => x ⟨k.1, DimTree.mem_modes_node 0 k.2⟩) b₀ * connTensor C a b₀ b₁ *
        (ds 1).basis (fun k => x ⟨k.1, DimTree.mem_modes_node 1 k.2⟩) b₁ := by
  rw [TTN.basis_node, ← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (piFinTwoEquiv _).symm _ _ fun b => ?_).symm
  obtain ⟨b₀, b₁⟩ := b
  simp only [connTensor, Fin.prod_univ_two, piFinTwoEquiv_symm_apply, Fin.cons_zero,
    Fin.cons_one]
  ring

/-- The mode-0 flattening of the connection tensor has the rank of the root matricization
`Mat₀(C)` (the two differ by a reindexing of the columns). -/
theorem rank_modeFlat0_connTensor {rs : Fin 2 → ℕ} {r : ℕ}
    (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ) : (modeFlat0 (connTensor C)).rank = C.rank := by
  have : modeFlat0 (connTensor C) = C.submatrix id (piFinTwoEquiv _).symm := by
    ext a b; rfl
  rw [this]
  exact Matrix.rank_submatrix C (Equiv.refl _) _

/-- **Eq. (5)** for the core tree tensor network: if the connection tensor of a binary node has
full multilinear rank `(r_τ, r_{τ₀}, r_{τ₁})`, then `r_τ ≤ r_{τ₀} r_{τ₁}`,
`r_{τ₀} ≤ r_{τ₁} r_τ` and `r_{τ₁} ≤ r_{τ₀} r_τ`. The first rank condition is the full row
rank of `Mat₀(C)` (`rank_modeFlat0_connTensor`), which holds for orthonormal tree tensor
networks (`Mat₀(C) Mat₀(C)ᵀ = 1`, `rank_modeFlat0_of_orthonormal`). -/
theorem rank_conditions_binary {rs : Fin 2 → ℕ} {r : ℕ} (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ)
    (h0 : (modeFlat0 (connTensor C)).rank = r) (h1 : (modeFlat1 (connTensor C)).rank = rs 0)
    (h2 : (modeFlat2 (connTensor C)).rank = rs 1) :
    r ≤ rs 0 * rs 1 ∧ rs 0 ≤ rs 1 * r ∧ rs 1 ≤ rs 0 * r := by
  obtain ⟨a, b, c⟩ := tucker_full_rank_requires _ h0 h1 h2
  exact ⟨a, b, by linarith [mul_comm r (rs 0)]⟩

/-- For an orthonormal node (`Mat₀(C) Mat₀(C)ᵀ = 1`, `TTN.IsOrthonormal`) the root
matricization has full row rank `r_τ`. -/
theorem rank_modeFlat0_of_orthonormal {rs : Fin 2 → ℕ} {r : ℕ}
    {C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ} (hC : C * Cᵀ = 1) :
    (modeFlat0 (connTensor C)).rank = r := by
  rw [rank_modeFlat0_connTensor, rank_eq_card_of_mul_eq_one hC, Fintype.card_fin]

end TTN

end LeanDLRA.Literature.P2501_04157
