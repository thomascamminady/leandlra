import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
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
  depending only on its own species has `h = 0` (`ruleEntropy_absorption`). The paper's exact
  rules on five species are not formalized, only these two extreme values.

* **Sec. 3.2, hierarchical tree tensor network** (`tucker_full_rank_requires`). For a connection
  tensor `Q : Fin a → Fin b → Fin c → ℝ` with full multilinear rank `(a, b, c)`, meaning every
  flattening (matricisation) has rank equal to its number of rows, the paper's conditions
  `a ≤ b c`, `b ≤ c a`, `c ≤ a b` hold. The paper's claim is only this necessity direction, and the
  binary tree decomposition itself is not formalized. `tensor_diag_fullRank` shows the hypotheses
  are satisfiable (a diagonal tensor on `Fin 2`).
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

end LeanDLRA.Literature.P2501_04157
