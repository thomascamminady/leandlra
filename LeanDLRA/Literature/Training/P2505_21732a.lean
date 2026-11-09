import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.LowRankDistance

/-!
# Results of arXiv 2505.21732: LaX, latent crossing for low-rank training

Zhang, Liu, Wang, Zhang, *LaX: Boosting Low-Rank Training of Foundation Models via Latent Crossing*.
The paper states no theorems (its checklist says it has no theoretical results), so this module
formalizes the architecture of its Section 3: the low-rank layer (Eq. 1), the crossing (Eq. 2), the
stacked form (Eq. 3), the gated form (Eq. 4), the LayerNorm form (Eq. 5) and the gates of Section
3.3, for real matrices of arbitrary finite shape. `laxWeight_eq_mul`, `laxWeight_mulVec`,
`rank_laxWeight_le`, `range_laxWeight_le` and the bundle `lax_layer_structure` give the structure
`LN(B (A x + G A' x')) = LN(B [A, G A'] x̃)` with `rank W ≤ r` and `range W ≤ range B`.
`exists_laxWeight_iff` shows that the identity-gate LaX weights are exactly the matrices of rank at
most `r`, `rank_laxWeight_of_injective` computes the rank as the dimension of the pooled latent
ranges, and `exists_lax_rank_gain` shows that this cap is attained while each pathway alone has
lower rank. `laxOutput_factor` is the exact statement after LayerNorm, which is nonlinear: the
output lies in the affine subspace `β + range (diag γ P B)`, of dimension at most `r`, where `P` is
the centering projector, and `exists_laxOutput_not_mem_range` proves that it can leave `range B`. So
the rank and range facts hold for `W`, and the range fact fails for `LN ∘ W`. The gates are
`identityGate` (0 parameters), `linearGate` (1), `tensorGate` (`r₀ r₀' + r₁ r₁'`, at most `r² + 1`)
and `denseGate` (`r²`), which makes the range from 0 to O(r²) extra parameters precise; these counts
are gate parameters only, and the `2 d` entries of `γ, β` of an elementwise-affine LayerNorm are not
included. Differences from the paper: the two input dimensions and the two latent dimensions may
differ (the paper's case is `n = n'` and `r = r'`); the paper's Section 3.4 says LN is added to
"each LaX pathway" while its Eq. 5 wraps the whole product, and we follow Eq. 5; the paper uses
`G_i` in Eq. 4 and `G_{i-1}` in Eq. 5 with no explanation, and we write one gate `G`; the paper
gives no parameter count for the tensor gate, so that count is derived from its core shapes; the
paper's Intra-Layer LaX has no formula and is not formalized. The LaX architecture is trained with
Adam on the factors, so nothing here is a dynamical low-rank statement; `leftProj_laxWeight` records
the link to the library's projectors.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix Kronecker LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2505_21732

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {d n n' r r' : Type*} [Fintype d] [Fintype n] [Fintype n'] [Fintype r] [Fintype r']

/-! ### The layer -/

/-- arXiv 2505.21732, Eq. (1): the low-rank layer `y = B (A x)`, with down-projection
`A : ℝ^{r × d_in}`, up-projection `B : ℝ^{d_out × r}` and latent `h = A x`. -/
def lowRankLayer (B : Matrix d r ℝ) (A : Matrix r n ℝ) (x : n → ℝ) : d → ℝ :=
  B *ᵥ (A *ᵥ x)

/-- arXiv 2505.21732, Eq. (4): the LaX weight `W = [B A, B G A']` acting on the stacked input
`x̃ = [x; x']`. Here `A, B` belong to layer `i`, `A'` belongs to layer `i - 1`, and the gate `G`
aligns the latent of layer `i - 1` to that of layer `i`. Eq. (3) is the case `G = 1`. -/
def laxWeight (B : Matrix d r ℝ) (A : Matrix r n ℝ) (G : Matrix r r' ℝ) (A' : Matrix r' n' ℝ) :
    Matrix d (n ⊕ n') ℝ :=
  Matrix.fromCols (B * A) (B * (G * A'))

variable (B : Matrix d r ℝ) (A : Matrix r n ℝ) (G : Matrix r r' ℝ) (A' : Matrix r' n' ℝ)

/-- arXiv 2505.21732, Eq. (4): `W = B [A, G A']`, the LaX weight is one block matrix multiplied by
the single up-projection `B`. -/
theorem laxWeight_eq_mul : laxWeight B A G A' = B * Matrix.fromCols A (G * A') := by
  rw [laxWeight, Matrix.mul_fromCols]

/-- arXiv 2505.21732, Eqs. (2)-(4): the stacked form `W x̃` is the latent crossing
`B (A x + G A' x')`. -/
theorem laxWeight_mulVec (x : n → ℝ) (x' : n' → ℝ) :
    laxWeight B A G A' *ᵥ Sum.elim x x' = B *ᵥ (A *ᵥ x + G *ᵥ (A' *ᵥ x')) := by
  rw [laxWeight, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- arXiv 2505.21732, Eqs. (2)-(3), the case with no gate and equal latent dimension:
`B (A x + A' x') = [B A, B A'] x̃`. -/
theorem eq2_eq_eq3 [DecidableEq r] (A'' : Matrix r n' ℝ) (x : n → ℝ) (x' : n' → ℝ) :
    B *ᵥ (A *ᵥ x + A'' *ᵥ x') = Matrix.fromCols (B * A) (B * A'') *ᵥ Sum.elim x x' := by
  have h := laxWeight_mulVec B A (1 : Matrix r r ℝ) A'' x x'
  simpa [laxWeight] using h.symm

/-- arXiv 2505.21732, Eq. (1) against Eq. (4): the zero gate (the linear gate with `β = 0`) gives
back the plain low-rank layer, so LaX extends it. -/
theorem laxWeight_zero_mulVec (x : n → ℝ) (x' : n' → ℝ) :
    laxWeight B A (0 : Matrix r r' ℝ) A' *ᵥ Sum.elim x x' = lowRankLayer B A x := by
  simp [laxWeight_mulVec, lowRankLayer]

/-- arXiv 2505.21732, Eq. (4): a gate does not enlarge the class of weights of one layer, since
`G A'` is one more down-projection, so a gated weight is an identity-gate weight with latent
dimension `r`. -/
theorem laxWeight_gate_absorb [DecidableEq r] :
    laxWeight B A G A' = laxWeight B A (1 : Matrix r r ℝ) (G * A') := by
  simp [laxWeight]

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), rank: `rank [B A, B G A'] ≤ r` for every gate,
also a rectangular one. The paper states no bound; this is the formal content of its stated goal of
improving low-rank layers without increasing the physical rank. -/
theorem rank_laxWeight_le : (laxWeight B A G A').rank ≤ Fintype.card r := by
  rw [laxWeight_eq_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width B)

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), shared column space: `range W ≤ range B`. The
paper does not state it. For the composite with LN it is false, see
`exists_laxOutput_not_mem_range`. -/
theorem range_laxWeight_le :
    LinearMap.range (laxWeight B A G A').mulVecLin ≤ LinearMap.range B.mulVecLin := by
  rw [laxWeight_eq_mul, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- arXiv 2505.21732, Eq. (4): neither pathway loses rank in the crossing. -/
theorem rank_pathway_le :
    (B * A).rank ≤ (laxWeight B A G A').rank ∧
      (B * (G * A')).rank ≤ (laxWeight B A G A').rank := by
  constructor
  · refine Submodule.finrank_mono ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨Sum.elim v 0, by simp [laxWeight]⟩
  · refine Submodule.finrank_mono ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨Sum.elim 0 v, by simp [laxWeight]⟩

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), auxiliary: the range of a block matrix
`[M, M']` is the sum of the ranges. -/
theorem range_fromCols (M : Matrix r n ℝ) (M' : Matrix r n' ℝ) :
    LinearMap.range (Matrix.fromCols M M').mulVecLin =
      LinearMap.range M.mulVecLin ⊔ LinearMap.range M'.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact ⟨Sum.elim v 0, by simp⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨Sum.elim 0 v, by simp⟩

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), the crossing as a sum of latent subspaces, not
stated in the paper: if the up-projection `B` is injective, then
`rank W = dim (range A + range (G A'))`. This is what the crossing does to the operator: it pools
the latent ranges of the two pathways inside the `r` dimensional latent space. -/
theorem rank_laxWeight_of_injective (hB : Function.Injective B.mulVecLin) :
    (laxWeight B A G A').rank =
      Module.finrank ℝ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range (G * A').mulVecLin) := by
  rw [laxWeight_eq_mul, Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp, range_fromCols]
  exact (Submodule.equivMapOfInjective _ hB _).symm.finrank_eq

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), the exact class of identity-gate LaX weights,
not stated in the paper: a matrix on the stacked input is an identity-gate LaX weight with latent
dimension `r` if and only if its rank is at most `r`. So `rank_laxWeight_le` cannot be improved, and
no other constraint holds. Here `A'` is free, that is, not tied to any other layer. -/
theorem exists_laxWeight_iff [DecidableEq r] (W : Matrix d (n ⊕ n') ℝ) :
    (∃ (B : Matrix d r ℝ) (A : Matrix r n ℝ) (A' : Matrix r n' ℝ),
        W = laxWeight B A (1 : Matrix r r ℝ) A') ↔ W.rank ≤ Fintype.card r := by
  classical
  constructor
  · rintro ⟨B, A, A', rfl⟩
    exact rank_laxWeight_le _ _ _ _
  · intro hW
    obtain ⟨U, S, V, -, -, hUSV⟩ :=
      exists_factor_of_rank_le (r := W.rank) le_rfl W.rank_le_card_height W.rank_le_card_width
    have hcard : Fintype.card (Fin W.rank) ≤ Fintype.card r := by simpa using hW
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    let P : Matrix (Fin W.rank) r ℝ := Matrix.of fun a j => if j = e a then 1 else 0
    have hP : P * Pᵀ = 1 := by
      ext a b
      simp [P, Matrix.mul_apply, Matrix.one_apply, e.injective.eq_iff, eq_comm]
    let C : Matrix r (n ⊕ n') ℝ := Pᵀ * (S * Vᵀ)
    refine ⟨U * P, C.toCols₁, C.toCols₂, ?_⟩
    rw [laxWeight_eq_mul, Matrix.one_mul, Matrix.fromCols_toCols]
    calc W = U * S * Vᵀ := hUSV
      _ = U * (P * Pᵀ) * (S * Vᵀ) := by rw [hP]; simp [Matrix.mul_assoc]
      _ = U * P * C := by simp only [C, Matrix.mul_assoc]

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), the cap is attained while each pathway alone
stays below it, not stated in the paper: for every injective `B` and every set `S` of latent
directions there are square down-projections `A, A' : ℝ^{r × r}` (both inputs of dimension `r`)
such that the two pathways have ranks `|S|` and `r - |S|` and the LaX weight has rank `r`. This is
the sense in which LaX raises the rank of the operator up to, and not beyond, the physical rank. -/
theorem exists_lax_rank_gain [DecidableEq r] (hB : Function.Injective B.mulVecLin) (S : Finset r) :
    ∃ A A' : Matrix r r ℝ, (B * A).rank = S.card ∧
      (B * ((1 : Matrix r r ℝ) * A')).rank = Fintype.card r - S.card ∧
      (laxWeight B A (1 : Matrix r r ℝ) A').rank = Fintype.card r := by
  classical
  have hmul : ∀ M : Matrix r r ℝ, (B * M).rank = M.rank := fun M => by
    rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective _ hB _).symm.finrank_eq
  refine ⟨Matrix.diagonal fun i => if i ∈ S then 1 else 0,
    Matrix.diagonal fun i => if i ∈ S then 0 else 1, ?_, ?_, ?_⟩
  · rw [hmul, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext i
    simp
  · rw [Matrix.one_mul, hmul, Matrix.rank_diagonal, Fintype.card_subtype, ← Finset.card_compl]
    congr 1
    ext i
    simp
  · rw [rank_laxWeight_of_injective B _ _ _ hB, Matrix.one_mul]
    have htop : LinearMap.range (Matrix.diagonal fun i => if i ∈ S then (1 : ℝ) else 0).mulVecLin ⊔
        LinearMap.range (Matrix.diagonal fun i => if i ∈ S then (0 : ℝ) else 1).mulVecLin = ⊤ := by
      rw [eq_top_iff]
      intro v _
      have hv : v = (Matrix.diagonal fun i => if i ∈ S then (1 : ℝ) else 0) *ᵥ v +
          (Matrix.diagonal fun i => if i ∈ S then (0 : ℝ) else 1) *ᵥ v := by
        ext i
        by_cases hi : i ∈ S <;> simp [Matrix.mulVec_diagonal, hi]
      rw [hv]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card]

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), link to the library's projectors, not in the
paper: if `B = U S` with `U` orthonormal, then the LaX weight is fixed by the left projector
`U Uᵀ`. -/
theorem leftProj_laxWeight {k : Type*} [Fintype k] [DecidableEq k] (U : Matrix d k ℝ)
    (S : Matrix k r ℝ) (hU : Uᵀ * U = 1) :
    leftProj U (laxWeight (U * S) A G A') = laxWeight (U * S) A G A' := by
  rw [leftProj_apply, laxWeight_eq_mul]
  calc U * Uᵀ * (U * S * Matrix.fromCols A (G * A'))
      = U * (Uᵀ * U) * S * Matrix.fromCols A (G * A') := by simp only [Matrix.mul_assoc]
    _ = U * S * Matrix.fromCols A (G * A') := by rw [hU, Matrix.mul_one]

/-- A strict gain for `r = 2`: both pathways have rank one and the LaX weight has rank two. -/
example : ∃ A A' : Matrix (Fin 2) (Fin 2) ℝ,
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * A).rank = 1 ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) * ((1 : Matrix (Fin 2) (Fin 2) ℝ) * A')).rank = 1 ∧
      (laxWeight (1 : Matrix (Fin 2) (Fin 2) ℝ) A (1 : Matrix (Fin 2) (Fin 2) ℝ) A').rank = 2 := by
  simpa using exists_lax_rank_gain (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (fun _ _ h => by simpa using h) {0}

/-! ### LayerNorm -/

/-- The mean of the coordinates of `y`. -/
noncomputable def coordMean (y : d → ℝ) : ℝ := (∑ i, y i) / Fintype.card d

/-- The (uncorrected) variance of the coordinates of `y`. -/
noncomputable def coordVar (y : d → ℝ) : ℝ := (∑ i, (y i - coordMean y) ^ 2) / Fintype.card d

/-- arXiv 2505.21732, the LN of Sec. 3.4 and Eq. (5). The paper gives no formula; this is the
standard layer normalization `LN(y)_i = γ_i (y_i - mean y) / √(var y + ε) + β_i`, where mean and
variance run over the coordinates of `y`. The non-affine version is `γ = 1, β = 0`. -/
noncomputable def layerNorm (ε : ℝ) (γ β y : d → ℝ) : d → ℝ :=
  fun i => γ i * ((y i - coordMean y) / √(coordVar y + ε)) + β i

/-- The centering projector `P = I - 𝟙𝟙ᵀ / d`, which subtracts the coordinate mean. -/
noncomputable def centering (d : Type*) [Fintype d] [DecidableEq d] : Matrix d d ℝ :=
  1 - (Fintype.card d : ℝ)⁻¹ • Matrix.of fun _ _ => 1

/-- arXiv 2505.21732, Eq. (5), auxiliary: `P` subtracts the coordinate mean. -/
theorem centering_mulVec [DecidableEq d] (y : d → ℝ) :
    centering d *ᵥ y = fun i => y i - coordMean y := by
  rw [centering, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  ext i
  simp [Matrix.mulVec, dotProduct, coordMean, div_eq_inv_mul]

/-- arXiv 2505.21732, Eq. (5), sanity check of `layerNorm`: the non-affine LN output has mean
zero. -/
theorem coordMean_layerNorm (ε : ℝ) (y : d → ℝ) : coordMean (layerNorm ε 1 0 y) = 0 := by
  rcases isEmpty_or_nonempty d with hd | hd
  · simp [coordMean]
  have hN : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : ∑ i, (y i - coordMean y) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, coordMean,
      mul_div_cancel₀ _ hN, sub_self]
  have hmean : ∑ i, (y i - coordMean y) / √(coordVar y + ε) = 0 := by
    rw [← Finset.sum_div, hs, zero_div]
  rw [coordMean]
  simp only [layerNorm, Pi.one_apply, one_mul, Pi.zero_apply, add_zero]
  rw [hmean, zero_div]

/-- arXiv 2505.21732, Eq. (5), sanity check of `layerNorm`: the variance of the non-affine LN output
is `var y / (var y + ε)`. -/
theorem coordVar_layerNorm {ε : ℝ} (hε : 0 ≤ ε) (y : d → ℝ) :
    coordVar (layerNorm ε 1 0 y) = coordVar y / (coordVar y + ε) := by
  have hv : 0 ≤ coordVar y := by
    apply div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
  have hs : √(coordVar y + ε) ^ 2 = coordVar y + ε := Real.sq_sqrt (add_nonneg hv hε)
  rw [coordVar, coordMean_layerNorm]
  simp only [layerNorm, Pi.one_apply, one_mul, Pi.zero_apply, add_zero, sub_zero, div_pow]
  rw [← Finset.sum_div, hs, div_right_comm]
  rfl

/-- arXiv 2505.21732, Eq. (5), sanity check of `layerNorm`: with `ε = 0` and non-constant `y` it
standardizes `y`. -/
theorem coordVar_layerNorm_zero {y : d → ℝ} (hy : coordVar y ≠ 0) :
    coordVar (layerNorm 0 1 0 y) = 1 := by
  rw [coordVar_layerNorm le_rfl, add_zero, div_self hy]

/-- arXiv 2505.21732, Eq. (5), auxiliary: LN is `β` plus `diag γ P` applied to a multiple of `y`,
with a scalar that depends on `y`. -/
theorem layerNorm_eq_factor [DecidableEq d] (ε : ℝ) (γ β y : d → ℝ) :
    layerNorm ε γ β y =
      β + (Matrix.diagonal γ * centering d) *ᵥ ((√(coordVar y + ε))⁻¹ • y) := by
  ext i
  rw [Pi.add_apply, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, centering_mulVec,
    Matrix.mulVec_diagonal]
  simp only [layerNorm, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- arXiv 2505.21732, Eq. (5): the LaX output `ỹ = LN(W x̃)`. -/
noncomputable def laxOutput (ε : ℝ) (γ β : d → ℝ) (B : Matrix d r ℝ) (A : Matrix r n ℝ)
    (G : Matrix r r' ℝ) (A' : Matrix r' n' ℝ) (x : n → ℝ) (x' : n' → ℝ) : d → ℝ :=
  layerNorm ε γ β (laxWeight B A G A' *ᵥ Sum.elim x x')

/-- arXiv 2505.21732, LaX layer structure (Eqs. 2-5), the bundled statement:
`ỹ = LN(B (A x + G A' x')) = LN(B [A, G A'] x̃)`, where `W = B [A, G A']` has rank at most `r` and
range inside `range B`. The rank and range claims are about `W`; for `LN ∘ W` see
`laxOutput_factor` and `exists_laxOutput_not_mem_range`. -/
theorem lax_layer_structure (ε : ℝ) (γ β : d → ℝ) (x : n → ℝ) (x' : n' → ℝ) :
    laxOutput ε γ β B A G A' x x' = layerNorm ε γ β (B *ᵥ (A *ᵥ x + G *ᵥ (A' *ᵥ x'))) ∧
      laxOutput ε γ β B A G A' x x' =
        layerNorm ε γ β ((B * Matrix.fromCols A (G * A')) *ᵥ Sum.elim x x') ∧
      (laxWeight B A G A').rank ≤ Fintype.card r ∧
      LinearMap.range (laxWeight B A G A').mulVecLin ≤ LinearMap.range B.mulVecLin :=
  ⟨by rw [laxOutput, laxWeight_mulVec], by rw [laxOutput, laxWeight_eq_mul],
    rank_laxWeight_le B A G A', range_laxWeight_le B A G A'⟩

/-- arXiv 2505.21732, Eq. (5), the exact form of the output after LN, not stated in the paper:
with `h = A x + G A' x'`, `y = B h`, and the centering projector `P`,
`ỹ = β + (diag γ P B) (√(var y + ε))⁻¹ h`. So the output depends on `x̃` only through the latent
`h`, and it is a rank `r` factorization with one scalar that depends on the input. -/
theorem laxOutput_factor [DecidableEq d] (ε : ℝ) (γ β : d → ℝ) (x : n → ℝ) (x' : n' → ℝ) :
    laxOutput ε γ β B A G A' x x' =
      β + (Matrix.diagonal γ * centering d * B) *ᵥ
        ((√(coordVar (B *ᵥ (A *ᵥ x + G *ᵥ (A' *ᵥ x'))) + ε))⁻¹ •
          (A *ᵥ x + G *ᵥ (A' *ᵥ x'))) := by
  rw [laxOutput, laxWeight_mulVec, layerNorm_eq_factor, ← Matrix.mulVec_smul B,
    Matrix.mulVec_mulVec]

/-- arXiv 2505.21732, Eq. (5), not stated in the paper: the rank fact survives LN in this form. The
output `ỹ` lies in the affine subspace `β + range (diag γ P B)`, whose direction has dimension at
most `r`, for all inputs and all LN parameters. -/
theorem laxOutput_sub_mem [DecidableEq d] (ε : ℝ) (γ β : d → ℝ) (x : n → ℝ) (x' : n' → ℝ) :
    laxOutput ε γ β B A G A' x x' - β ∈
        LinearMap.range (Matrix.diagonal γ * centering d * B).mulVecLin ∧
      (Matrix.diagonal γ * centering d * B).rank ≤ Fintype.card r := by
  refine ⟨?_, (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_width B)⟩
  rw [laxOutput_factor, add_sub_cancel_left]
  exact ⟨_, rfl⟩

/-- arXiv 2505.21732, Eq. (5), counterexample: the shared column space statement is false for the
composite `LN ∘ W`. With `d_out = 2`, `r = 1`, `B = (1, 0)ᵀ` and every `ε ≥ 0`, the LaX output is
not in `range B`. The correct subspace is the centered one of `laxOutput_sub_mem`. -/
theorem exists_laxOutput_not_mem_range {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ (B : Matrix (Fin 2) (Fin 1) ℝ) (A G A' : Matrix (Fin 1) (Fin 1) ℝ) (x x' : Fin 1 → ℝ),
      laxOutput ε 1 0 B A G A' x x' ∉ LinearMap.range B.mulVecLin := by
  refine ⟨!![1; 0], 1, 1, 1, 1, 1, ?_⟩
  rintro ⟨z, hz⟩
  have hy : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ 1 +
      (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ 1)) = ![2, 0] := by
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct]
  have hm : coordMean (![2, 0] : Fin 2 → ℝ) = 1 := by
    simp [coordMean, Fin.sum_univ_two]
  have hv : coordVar (![2, 0] : Fin 2 → ℝ) = 1 := by
    simp [coordVar, hm, Fin.sum_univ_two]
    norm_num
  have hpos : 0 < √(1 + ε) := Real.sqrt_pos.mpr (by linarith)
  have h1 := congrFun hz 1
  rw [laxOutput, laxWeight_mulVec, hy] at h1
  simp [layerNorm, Matrix.mulVec, dotProduct, hm, hv] at h1
  exact div_ne_zero (by norm_num) hpos.ne' h1.symm

/-! ### Gates and their parameter counts -/

/-- arXiv 2505.21732, Sec. 3.3: a gate family with trainable parameters `θ : ι → ℝ`. -/
structure LaxGate (ι r r' : Type*) where
  /-- The gate matrix for the parameters `θ`. -/
  toMatrix : (ι → ℝ) → Matrix r r' ℝ

/-- arXiv 2505.21732, Sec. 3.3: the number of extra trainable parameters of a gate. These are
parameters on top of the factors `B, A, A'`, which the plain low-rank layers already have. -/
def LaxGate.extraParams {ι r r' : Type*} [Fintype ι] (_ : LaxGate ι r r') : ℕ := Fintype.card ι

/-- arXiv 2505.21732, Sec. 3.3, identity gate `G = 1`: no parameters. -/
def identityGate (r : Type*) [DecidableEq r] : LaxGate Empty r r :=
  ⟨fun _ => 1⟩

/-- arXiv 2505.21732, Sec. 3.3, linear gate `G = β`: one trainable scalar. -/
noncomputable def linearGate (r : Type*) [DecidableEq r] : LaxGate Unit r r :=
  ⟨fun θ => θ () • 1⟩

/-- arXiv 2505.21732, Sec. 3.3, dense gate: a full matrix. The paper's gate is square, `r × r`. -/
def denseGate (r r' : Type*) : LaxGate (r × r') r r' :=
  ⟨fun θ => Matrix.of fun i j => θ (i, j)⟩

/-- arXiv 2505.21732, Sec. 3.3, tensor gate: the latent is folded to `R : ℝ^{r₀ × r₁}` and mapped to
`R' = C⁰ R C¹ : ℝ^{r₀' × r₁'}`, with cores `C⁰ : ℝ^{r₀' × r₀}` and `C¹ : ℝ^{r₁ × r₁'}` (the paper's
order-3 cores with their singleton mode dropped). As a matrix on the folded latents, this is the
Kronecker product `C⁰ ⊗ C¹ᵀ`. Here `s₀, s₁` index `r₀, r₁` and `t₀, t₁` index `r₀', r₁'`. -/
def tensorGate (t₀ t₁ s₀ s₁ : Type*) :
    LaxGate ((t₀ × s₀) ⊕ (s₁ × t₁)) (t₀ × t₁) (s₀ × s₁) :=
  ⟨fun θ => (Matrix.of fun a b => θ (Sum.inl (a, b))) ⊗ₖ
    (Matrix.of fun a b => θ (Sum.inr (a, b)))ᵀ⟩

/-- arXiv 2505.21732, Sec. 3.3: the action of the tensor gate is `R ↦ C⁰ R C¹` on folded latents,
as the paper defines it. -/
theorem tensorGate_mulVec {t₀ t₁ s₀ s₁ : Type*} [Fintype s₀] [Fintype s₁]
    (θ : (t₀ × s₀) ⊕ (s₁ × t₁) → ℝ) (R : Matrix s₀ s₁ ℝ) :
    (tensorGate t₀ t₁ s₀ s₁).toMatrix θ *ᵥ (fun p => R p.1 p.2) =
      fun p => ((Matrix.of fun a b => θ (Sum.inl (a, b))) * R *
        (Matrix.of fun a b => θ (Sum.inr (a, b)))) p.1 p.2 := by
  ext ⟨a, b⟩
  simp only [tensorGate, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- arXiv 2505.21732, Sec. 3.3: the identity gate is the identity. -/
theorem identityGate_toMatrix [DecidableEq r] (θ : Empty → ℝ) :
    (identityGate r).toMatrix θ = 1 := rfl

/-- arXiv 2505.21732, Sec. 3.3: the linear gate is injective in its parameter if the latent is
nonzero, so its parameter count is not padded. -/
theorem linearGate_injective [DecidableEq r] [Nonempty r] :
    Function.Injective (linearGate r).toMatrix := by
  intro θ θ' h
  obtain ⟨i⟩ := ‹Nonempty r›
  have hi := congrFun (congrFun h i) i
  have : θ () = θ' () := by simpa [linearGate] using hi
  funext u
  simpa using this

/-- arXiv 2505.21732, Sec. 3.3: the dense gate is a bijection from its parameters onto all matrices,
so its parameter count is not padded. -/
theorem denseGate_bijective : Function.Bijective (denseGate r r').toMatrix := by
  constructor
  · intro θ θ' h
    funext ⟨i, j⟩
    exact congrFun (congrFun h i) j
  · intro M
    exact ⟨fun p => M p.1 p.2, rfl⟩

/-- arXiv 2505.21732, Sec. 3.3: the identity gate has no extra parameters. -/
theorem identityGate_extraParams [DecidableEq r] :
    (identityGate r).extraParams = 0 := by
  simp [LaxGate.extraParams]

/-- arXiv 2505.21732, Sec. 3.3: the linear gate has one extra parameter. -/
theorem linearGate_extraParams [DecidableEq r] : (linearGate r).extraParams = 1 := by
  simp [LaxGate.extraParams]

/-- arXiv 2505.21732, Sec. 3.3: the square dense gate has `r²` extra parameters. -/
theorem denseGate_extraParams : (denseGate r r).extraParams = Fintype.card r ^ 2 := by
  simp [LaxGate.extraParams, sq]

/-- arXiv 2505.21732, Sec. 3.3: the tensor gate has `r₀' r₀ + r₁ r₁'` extra parameters, the sizes of
its two cores. The paper gives only the shapes. -/
theorem tensorGate_extraParams {t₀ t₁ s₀ s₁ : Type*} [Fintype t₀] [Fintype t₁] [Fintype s₀]
    [Fintype s₁] :
    (tensorGate t₀ t₁ s₀ s₁).extraParams =
      Fintype.card t₀ * Fintype.card s₀ + Fintype.card s₁ * Fintype.card t₁ := by
  simp [LaxGate.extraParams]

/-- arXiv 2505.21732, Sec. 3.3, the upper end `O(r²)` of the gate parameter counts for the tensor
gate, derived from the core shapes since the paper gives no count: if both folded latents have the
same rank `R = r₀ r₁ = r₀' r₁' > 0`, then the gate has at most `R² + 1` parameters. The bound is
attained at `r₀ = r₀' = 1`, where the gate is a dense gate times a scalar. -/
theorem tensorGate_extraParams_le {t₀ t₁ s₀ s₁ : Type*} [Fintype t₀] [Fintype t₁] [Fintype s₀]
    [Fintype s₁] {R : ℕ} (hR : 0 < R) (hs : Fintype.card s₀ * Fintype.card s₁ = R)
    (ht : Fintype.card t₀ * Fintype.card t₁ = R) :
    (tensorGate t₀ t₁ s₀ s₁).extraParams ≤ R ^ 2 + 1 := by
  rw [tensorGate_extraParams]
  subst hs
  have hs₀ : 0 < Fintype.card s₀ := Nat.pos_of_ne_zero fun h => by simp [h] at hR
  have hs₁ : 0 < Fintype.card s₁ := Nat.pos_of_ne_zero fun h => by simp [h] at hR
  have ht₀ : 0 < Fintype.card t₀ := Nat.pos_of_ne_zero fun h => by simp [h] at ht; omega
  have ht₁ : 0 < Fintype.card t₁ := Nat.pos_of_ne_zero fun h => by simp [h] at ht; omega
  have hp : 1 ≤ Fintype.card t₀ * Fintype.card s₀ := Nat.mul_pos ht₀ hs₀
  have hq : 1 ≤ Fintype.card s₁ * Fintype.card t₁ := Nat.mul_pos hs₁ ht₁
  have key : (Fintype.card t₀ * Fintype.card s₀) + (Fintype.card s₁ * Fintype.card t₁) ≤
      (Fintype.card t₀ * Fintype.card s₀) * (Fintype.card s₁ * Fintype.card t₁) + 1 := by
    nlinarith [Nat.mul_le_mul (Nat.sub_le_sub_right hp 1) (Nat.sub_le_sub_right hq 1)]
  calc _ ≤ _ := key
    _ = (Fintype.card s₀ * Fintype.card s₁) ^ 2 + 1 := by
      rw [show (Fintype.card t₀ * Fintype.card s₀) * (Fintype.card s₁ * Fintype.card t₁) =
        (Fintype.card t₀ * Fintype.card t₁) * (Fintype.card s₀ * Fintype.card s₁) by ring, ht, sq]

end LeanDLRA.Literature.P2505_21732
