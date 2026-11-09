import LeanDLRA.Tensor.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tucker attention: Tucker ranks of MHA, GQA and MLA, and latent RoPE (arXiv 2603.30033)

Klein, Kusch, Sager, Schnake and Schotthöfer, *Tucker Attention: A generalization of approximate
attention mechanisms* (arXiv 2603.30033).  The paper stacks the per-head pre-softmax weights
`W_i = W_i^Q W_i^{K,⊤}` of multi-head attention into a three-way tensor
`𝒲 ∈ ℝ^{n_H × d_model × d_model}` (Eq. (2); the post-softmax tensor `𝒲̃` of Eq. (3) stacks
`W̃_iᵀ = W_i^{O,⊤} W_i^{V,⊤}` in the same way), proposes to parametrize `𝒲` and `𝒲̃` in Tucker
format, and shows that MQA, GQA and MLA are Tucker tensors of specific ranks (Appendix B.1).
It also moves the rotary position embedding into the latent key space (Definition 3.1, Lemma B.5).
The rest of the paper (training, parameter counts, experiments) is empirical.

This module states these results with the core tensor vocabulary of `LeanDLRA.Tensor`: the
attention tensors are elements of `Tensor` with three modes (head, query/output, key/value), and
the Tucker rank is the tuple of ranks of the mode unfoldings `Tensor.unfold (· = k)`.

## Main results

* `headStack A B`: the stacked tensor `𝒲_{ijk} = (A_i B_iᵀ)_{jk}`; the pre-softmax tensor is
  `headStack W^Q W^K`, the post-softmax tensor is `headStack W^{O,⊤} W^V`; `concatHeads A` is the
  column concatenation `W^Q = [W_1^Q, …, W_{n_H}^Q]`.
* Theorem B.2 (`rank_unfold_head_le`, `rank_unfold_query_le`, `rank_unfold_key_le`,
  `tuckerRank_headStack_le`): the Tucker rank of `𝒲` is at most `(n_H, rank W^Q, rank W^K)`.
* Theorem B.3 (`rank_concatHeads_le_of_grouped`, `tuckerRank_gqa_le`): for GQA (and MQA,
  `n_KV = 1`) both attention tensors have Tucker rank at most `(n_H, d_model, n_KV d_H)`.
* Theorem B.4 (`tuckerRank_mla_le`, `tuckerRank_mla_post_le`): for MLA the pre-softmax tensor has
  Tucker rank at most `(n_H, d_c^Q, d_c^K)` and the post-softmax tensor at most
  `(n_H, d_model, d_c^K)`.
* Lemma B.5 (`latentRoPE_eq`, `latentRoPE_eq_of_sub_eq`): latent RoPE (Eq. (12)) has the relative
  position property: if `R(m) R(n)ᵀ = R(m - n)` (Eq. (10)) then the scores
  `Q̂_m ×₃ (K_n R(n) R(m)ᵀ) = Q̂_m ×₃ R(m - n)ᵀ ×₃ K_n` depend on `m, n` only through `m - n`;
  `mla_latentRoPE_eq` is the MLA form (13)–(14).  `rope_isRelativeRotary` shows that the rotary
  embedding of Su et al. (block-diagonal `2 × 2` rotations with arbitrary frequencies) satisfies
  (10), so the hypothesis of Lemma B.5 holds for the real RoPE.

Differences from the paper.  The Tucker rank is stated as the ranks of the three unfoldings
(the paper's "maximal Tucker rank" bounds); the explicit Tucker factorization (8) with a column
permutation `Π` and the KV-cache formula (9) are not formalized, nor is the reformulation (6) of
MHA through the softmax tensors.  `d_model = n_H d_H` is not needed.  The paper's proof of
Theorem B.3 writes `span(W^Q)` where `span(W^K)` is meant; the statement is proved as intended.
No claim of the paper was found to be false.
-/

open Matrix
open scoped Matrix

namespace LeanDLRA.Literature.P2603_30033

open LeanDLRA LeanDLRA.Tensor

variable {nH d dH : ℕ}

/-- The mode sizes `(n_H, d_model, d_model)` of the attention tensors `𝒲, 𝒲̃` (Eqs. (2)–(3)):
mode `0` is the head mode, mode `1` the query (resp. output) mode, mode `2` the key (resp. value)
mode. -/
def attnDims (nH d : ℕ) : Fin 3 → ℕ := ![nH, d, d]

/-- The three-way attention tensors `ℝ^{n_H × d_model × d_model}` (core `Tensor` with three
modes). -/
abbrev AttnTensor (nH d : ℕ) : Type := Tensor fun k : Fin 3 => Fin (attnDims nH d k)

/-- The head index `x₀ ∈ Fin n_H` of a multi-index of an attention tensor. -/
def headIdx (x : ∀ k : Fin 3, Fin (attnDims nH d k)) : Fin nH := x 0

/-- The query (resp. output) index `x₁ ∈ Fin d_model` of a multi-index. -/
def queryIdx (x : ∀ k : Fin 3, Fin (attnDims nH d k)) : Fin d := x 1

/-- The key (resp. value) index `x₂ ∈ Fin d_model` of a multi-index. -/
def keyIdx (x : ∀ k : Fin 3, Fin (attnDims nH d k)) : Fin d := x 2

/-- The **stacked per-head products** `𝒲_{ijk} = (A_i B_iᵀ)_{jk}` (Eq. (2) with `A = W^Q`,
`B = W^K`; Eq. (3) with `A_i = W_i^{O,⊤}`, `B_i = W_i^V`). -/
def headStack (A B : Fin nH → Matrix (Fin d) (Fin dH) ℝ) : AttnTensor nH d :=
  WithLp.toLp 2 fun x => (A (headIdx x) * (B (headIdx x))ᵀ) (queryIdx x) (keyIdx x)

/-- The column concatenation `[A_1, …, A_{n_H}] ∈ ℝ^{d_model × n_H d_H}` of the heads
(`W^Q = [W_1^Q, …, W_{n_H}^Q]`), with the column index `(i, ℓ)`. -/
def concatHeads (A : Fin nH → Matrix (Fin d) (Fin dH) ℝ) : Matrix (Fin d) (Fin nH × Fin dH) ℝ :=
  Matrix.of fun j p => A p.1 j p.2

/-- The **Tucker rank** bound: the ranks of the three mode unfoldings of `X` are at most
`r₀, r₁, r₂`. -/
def TuckerRankLE (X : AttnTensor nH d) (r₀ r₁ r₂ : ℕ) : Prop :=
  (unfold (· = (0 : Fin 3)) X).rank ≤ r₀ ∧ (unfold (· = (1 : Fin 3)) X).rank ≤ r₁ ∧
    (unfold (· = (2 : Fin 3)) X).rank ≤ r₂

/-! ### Theorem B.2: Tucker ranks of the stacked attention tensor -/

/-- The rank of the head-mode unfolding is at most `n_H`. -/
theorem rank_unfold_head_le (X : AttnTensor nH d) : (unfold (· = (0 : Fin 3)) X).rank ≤ nH := by
  refine (rank_le_card_height _).trans_eq ?_
  rw [Fintype.card_congr (modeEquiv (ι := fun k : Fin 3 => Fin (attnDims nH d k)) 0)]
  exact Fintype.card_fin _

/-- The query-mode unfolding factors through `W^Q`: `Mat₂(𝒲) = W^Q N` with rows re-indexed. -/
theorem rank_unfold_query_le (A B : Fin nH → Matrix (Fin d) (Fin dH) ℝ) :
    (unfold (· = (1 : Fin 3)) (headStack A B)).rank ≤ (concatHeads A).rank := by
  classical
  let hd : (∀ k : {k : Fin 3 // ¬ k = 1}, Fin (attnDims nH d k)) → Fin nH :=
    fun b => b ⟨0, by decide⟩
  let kd : (∀ k : {k : Fin 3 // ¬ k = 1}, Fin (attnDims nH d k)) → Fin d :=
    fun b => b ⟨2, by decide⟩
  let rq : (∀ k : {k : Fin 3 // k = 1}, Fin (attnDims nH d k)) → Fin d := fun a => a ⟨1, rfl⟩
  let N : Matrix (Fin nH × Fin dH) (∀ k : {k : Fin 3 // ¬ k = 1}, Fin (attnDims nH d k)) ℝ :=
    Matrix.of fun p b => if p.1 = hd b then B p.1 (kd b) p.2 else 0
  have h : unfold (· = (1 : Fin 3)) (headStack A B) = (concatHeads A * N).submatrix rq id := by
    ext a b
    have e : unfold (· = (1 : Fin 3)) (headStack A B) a b =
        (A (hd b) * (B (hd b))ᵀ) (rq a) (kd b) := rfl
    rw [e, submatrix_apply, id, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single (hd b)]
    · simp [concatHeads, N, transpose_apply]
    · intro i _ hi; simp [N, hi]
    · simp
  rw [h]
  exact (rank_submatrix_le _ _ _).trans (rank_mul_le_left _ _)

/-- The key-mode unfolding factors through `W^K`. -/
theorem rank_unfold_key_le (A B : Fin nH → Matrix (Fin d) (Fin dH) ℝ) :
    (unfold (· = (2 : Fin 3)) (headStack A B)).rank ≤ (concatHeads B).rank := by
  classical
  let hd : (∀ k : {k : Fin 3 // ¬ k = 2}, Fin (attnDims nH d k)) → Fin nH :=
    fun b => b ⟨0, by decide⟩
  let qd : (∀ k : {k : Fin 3 // ¬ k = 2}, Fin (attnDims nH d k)) → Fin d :=
    fun b => b ⟨1, by decide⟩
  let rk : (∀ k : {k : Fin 3 // k = 2}, Fin (attnDims nH d k)) → Fin d := fun a => a ⟨2, rfl⟩
  let N : Matrix (Fin nH × Fin dH) (∀ k : {k : Fin 3 // ¬ k = 2}, Fin (attnDims nH d k)) ℝ :=
    Matrix.of fun p b => if p.1 = hd b then A p.1 (qd b) p.2 else 0
  have h : unfold (· = (2 : Fin 3)) (headStack A B) = (concatHeads B * N).submatrix rk id := by
    ext a b
    have e : unfold (· = (2 : Fin 3)) (headStack A B) a b =
        (A (hd b) * (B (hd b))ᵀ) (qd b) (rk a) := rfl
    rw [e, submatrix_apply, id, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single (hd b)]
    · simp [concatHeads, N, transpose_apply, mul_comm]
    · intro i _ hi; simp [N, hi]
    · simp
  rw [h]
  exact (rank_submatrix_le _ _ _).trans (rank_mul_le_left _ _)

/-- **Theorem B.2** (arXiv 2603.30033): the stacked tensor `𝒲_{ijk} = (W_i^Q W_i^{K,⊤})_{jk}` has
Tucker rank at most `(n_H, rank W^Q, rank W^K)`. -/
theorem tuckerRank_headStack_le (A B : Fin nH → Matrix (Fin d) (Fin dH) ℝ) :
    TuckerRankLE (headStack A B) nH (concatHeads A).rank (concatHeads B).rank :=
  ⟨rank_unfold_head_le _, rank_unfold_query_le A B, rank_unfold_key_le A B⟩

/-- The rank of a concatenation of heads is at most `d_model`. -/
theorem rank_concatHeads_le (A : Fin nH → Matrix (Fin d) (Fin dH) ℝ) :
    (concatHeads A).rank ≤ d :=
  (rank_le_card_height _).trans_eq (Fintype.card_fin d)

/-! ### Theorem B.3: group-query attention -/

/-- In GQA the key heads are shared within groups: `W_h^K = G_{g(h)}` for `n_KV` key heads `G`.
Then `rank W^K ≤ n_KV d_H`. -/
theorem rank_concatHeads_le_of_grouped {nKV : ℕ} (g : Fin nH → Fin nKV)
    (G : Fin nKV → Matrix (Fin d) (Fin dH) ℝ) :
    (concatHeads fun h => G (g h)).rank ≤ nKV * dH := by
  have h : (concatHeads fun h => G (g h)) =
      (concatHeads G).submatrix id fun q => (g q.1, q.2) := rfl
  rw [h]
  refine (rank_submatrix_le _ _ _).trans ((rank_le_card_width _).trans_eq ?_)
  simp

/-- **Theorem B.3** (arXiv 2603.30033): with `n_KV` key heads shared by groups of query heads
(`W_h^K = W_{g(h)}^{K,GQA}`), the pre-softmax tensor has Tucker rank at most
`(n_H, d_model, n_KV d_H)`; the same holds for the post-softmax tensor with shared value heads
(take `A_i = W_i^{O,⊤}`, `G = W^{V,GQA}`).  MQA is the case `n_KV = 1`. -/
theorem tuckerRank_gqa_le {nKV : ℕ} (g : Fin nH → Fin nKV) (A : Fin nH → Matrix (Fin d) (Fin dH) ℝ)
    (G : Fin nKV → Matrix (Fin d) (Fin dH) ℝ) :
    TuckerRankLE (headStack A fun h => G (g h)) nH d (nKV * dH) :=
  ⟨rank_unfold_head_le _, (rank_unfold_query_le _ _).trans (rank_concatHeads_le A),
    (rank_unfold_key_le _ _).trans (rank_concatHeads_le_of_grouped g G)⟩

/-! ### Theorem B.4: multi-head latent attention -/

/-- **Theorem B.4** (arXiv 2603.30033), pre-softmax part: if the query and key matrices are
factored through latent spaces, `W^Q = W^{DQ} W^{UQ}` and `W^K = W^{DKV} W^{UK}` with
`W^{DQ} ∈ ℝ^{d_model × d_c^Q}`, `W^{DKV} ∈ ℝ^{d_model × d_c^K}`, the pre-softmax tensor has Tucker
rank at most `(n_H, d_c^Q, d_c^K)`. -/
theorem tuckerRank_mla_le {dcQ dcK : ℕ} (A B : Fin nH → Matrix (Fin d) (Fin dH) ℝ)
    (DQ : Matrix (Fin d) (Fin dcQ) ℝ) (UQ : Matrix (Fin dcQ) (Fin nH × Fin dH) ℝ)
    (DKV : Matrix (Fin d) (Fin dcK) ℝ) (UK : Matrix (Fin dcK) (Fin nH × Fin dH) ℝ)
    (hQ : concatHeads A = DQ * UQ) (hK : concatHeads B = DKV * UK) :
    TuckerRankLE (headStack A B) nH dcQ dcK :=
  ⟨rank_unfold_head_le _,
    (rank_unfold_query_le A B).trans
      (by rw [hQ]; exact (rank_mul_le_left _ _).trans (rank_le_width _)),
    (rank_unfold_key_le A B).trans
      (by rw [hK]; exact (rank_mul_le_left _ _).trans (rank_le_width _))⟩

/-- **Theorem B.4** (arXiv 2603.30033), post-softmax part: with the value heads factored through
the key latent space, `W^V = W^{DKV} W^{UV}`, and a full output matrix, the post-softmax tensor
(`A_i = W_i^{O,⊤}`, `B = W^V`) has Tucker rank at most `(n_H, d_model, d_c^K)`. -/
theorem tuckerRank_mla_post_le {dcK : ℕ} (O V : Fin nH → Matrix (Fin d) (Fin dH) ℝ)
    (DKV : Matrix (Fin d) (Fin dcK) ℝ) (UV : Matrix (Fin dcK) (Fin nH × Fin dH) ℝ)
    (hV : concatHeads V = DKV * UV) :
    TuckerRankLE (headStack O V) nH d dcK :=
  ⟨rank_unfold_head_le _, (rank_unfold_query_le O V).trans (rank_concatHeads_le O),
    (rank_unfold_key_le O V).trans
      (by rw [hV]; exact (rank_mul_le_left _ _).trans (rank_le_width _))⟩

/-! ### Lemma B.5: latent rotary position embedding -/

/-- The **relative position property** (10) of a rotary embedding `R(ℓ)` acting on a latent space
`L`: `R(m) R(n)ᵀ = R(m - n)`. -/
def IsRelativeRotary {L : Type*} [Fintype L] (R : ℤ → Matrix L L ℝ) : Prop :=
  ∀ m n : ℤ, R m * (R n)ᵀ = R (m - n)

/-- The **latent RoPE score** of Definition 3.1, Eq. (12): `Q̂_m ×₃ (K_n R(n) R(m)ᵀ) ∈ ℝ^{n_H}` for
the head-wise latent queries `Q̂_m` at position `m` and the latent key `K_n` at position `n`. -/
def latentRoPE {L : Type*} [Fintype L] (R : ℤ → Matrix L L ℝ) (Q : Fin nH → L → ℝ) (K : L → ℝ)
    (m n : ℤ) : Fin nH → ℝ :=
  fun h => Q h ⬝ᵥ (K ᵥ* (R n * (R m)ᵀ))

/-- **Lemma B.5** (arXiv 2603.30033): under (10), the latent RoPE score is
`Q̂_m ×₃ R(m - n)ᵀ ×₃ K_n`, i.e. `(Q̂_m)_h · (R(m - n) K_n)`. -/
theorem latentRoPE_eq {L : Type*} [Fintype L] {R : ℤ → Matrix L L ℝ} (hR : IsRelativeRotary R)
    (Q : Fin nH → L → ℝ) (K : L → ℝ) (m n : ℤ) :
    latentRoPE R Q K m n = fun h => Q h ⬝ᵥ (R (m - n) *ᵥ K) := by
  funext h
  simp only [latentRoPE]
  rw [← mulVec_transpose, transpose_mul, transpose_transpose, hR]

/-- The relative position property of latent RoPE: the scores at positions `(m, n)` and
`(m', n')` coincide when `m - n = m' - n'`. -/
theorem latentRoPE_eq_of_sub_eq {L : Type*} [Fintype L] {R : ℤ → Matrix L L ℝ}
    (hR : IsRelativeRotary R) (Q : Fin nH → L → ℝ) (K : L → ℝ) {m n m' n' : ℤ}
    (h : m - n = m' - n') : latentRoPE R Q K m n = latentRoPE R Q K m' n' := by
  rw [latentRoPE_eq hR, latentRoPE_eq hR, h]

/-- **Simplified RoPE for MLA** (Section 3.2.1, Eqs. (13)–(14)): with the fused query map
`W_i^{Q,MLA} ∈ ℝ^{d_model × d_c}` and the shared down-projection `W^{DKV}`, the score
`x_m W_i^{Q,MLA} R(m) R(n)ᵀ W^{DKV,⊤} x_n` equals `x_m W_i^{Q,MLA} R(m - n) W^{DKV,⊤} x_n`. -/
theorem mla_latentRoPE_eq {L : Type*} [Fintype L] {R : ℤ → Matrix L L ℝ} (hR : IsRelativeRotary R)
    (WQ DKV : Matrix (Fin d) L ℝ) (xm xn : Fin d → ℝ) (m n : ℤ) :
    xm ⬝ᵥ ((WQ * R m * (R n)ᵀ * DKVᵀ) *ᵥ xn) = xm ⬝ᵥ ((WQ * R (m - n) * DKVᵀ) *ᵥ xn) := by
  rw [Matrix.mul_assoc WQ, hR]

/-- The `2 × 2` rotation by the angle `θ`. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

lemma rot_mul_transpose (a b : ℝ) : rot a * (rot b)ᵀ = rot (a - b) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [rot, Real.cos_sub, Real.sin_sub] <;> ring

/-- The **rotary position embedding** of Su et al. in a latent space of dimension `2k`: the
block-diagonal matrix of the rotations by `ℓ θ_i`, `i < k`. -/
noncomputable def rope {k : ℕ} (θ : Fin k → ℝ) (ℓ : ℤ) : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℝ :=
  blockDiagonal fun i => rot (ℓ * θ i)

/-- The rotary position embedding satisfies the relative position property (10), so Lemma B.5
applies to it. -/
theorem rope_isRelativeRotary {k : ℕ} (θ : Fin k → ℝ) : IsRelativeRotary (rope θ) := by
  intro m n
  simp only [rope]
  rw [blockDiagonal_transpose, ← blockDiagonal_mul]
  congr 1
  funext i
  rw [rot_mul_transpose]
  congr 1
  push_cast
  ring

end LeanDLRA.Literature.P2603_30033
