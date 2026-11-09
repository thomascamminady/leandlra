import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Stiff.ImplicitSolvability
import LeanDLRA.Tensor.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# arXiv 2611.04360, Sections 5.1 and 5.3: TT-rank calculus and the energy inequality

The paper (a hybrid TT/QTT discontinuous Galerkin method with fixed-matrix upwinding for
transient multigroup neutron transport) bounds operator ranks in Section 5.1 and propagates the
errors of a step in Section 5.3. This module formalizes the rank calculus of Section 5.1 and the
energy inequality (Lemma 5.2) on which Section 5.3 rests, and connects Lemma 5.2 to the core
θ-method lemma (Lemma 5.3). Lemma 5.4 and Proposition 5.3 are in the companion module (b).

## Section 5.1
* `ttRank` (Definitions 5.1, 5.2) is the rank of the core unfolding `LeanDLRA.Tensor.unfold p X`
  of a core tensor `X : LeanDLRA.Tensor ι` with the modes `p` in the rows (for a tensor train,
  `p = {i | i < k}` is the paper's `k`-th link). `blockUnfolding`, `blockRank` are the same objects
  for a function on two blocks of modes; `unfold_eq_blockUnfolding` is the bridge.
* `ttRank_add_le` (Lemma 5.1 (a)); `ttRank_le_one_of_separable`, `ttRank_eq_one_of_separable`
  (Lemma 5.1 (b), (5.6)–(5.7)); `blockRank_eq_of_kronecker_axis` (Lemma 5.1 (c), (5.8), modes
  grouped into the blocks before, inside and after the cut axis); `blockRank_one_eq_one`
  (Lemma 5.1 (d)); `ttRank_sum_le` (Proposition 5.1 (i), abstract form: `q` terms that are
  separable at the link). Deviation: the equalities of (b) and (c) need the factors to be
  nonzero (a zero factor gives rank `0`); the paper leaves this implicit, the theorems assume it.

## Lemma 5.2 (energy inequality), proved
* The objects as printed: `weightW` (`W = M_h ⊗ M_h ⊗ M_h ⊗ diag(w) ⊗ I_G`), `invSpeed`, `speed`
  (`V⁻¹`, `V`, (4.8)), `energyNormSq` (`‖x‖²_E = xᵀ W V⁻¹ x`), `streaming` (4.7), `removal`,
  `scattering` (4.8, isotropic), `fission` (4.10), `transportOp` (`𝒜 = L + Σ_t - S - F`),
  `collisionMatrix` (`Σ_c`), `symPart`, `lambdaMin` and `growthBound`
  (`γ = max {0, -λ_min(V_G^{1/2} sym(Σ_c) V_G^{1/2})}`).
* Part (i): `upwindC_skew` (`M_h C` skew-symmetric), `upwindD_posSemidef` and `upwindMD_quad`
  (`xᵀ M_h D x = J(u)/2 ≥ 0`), `streaming_energy_nonneg` (`xᵀ W L x ≥ 0`, the Kronecker step).
* Part (ii): `collision_energy_ge` (the mean/fluctuation argument of the proof),
  `energy_inequality_of_streaming` (for any one-dimensional matrices with the properties of (i))
  and `energy_inequality` (for the upwind DG matrices): `xᵀ W 𝒜 x ≥ -γ ‖x‖²_E`.
* Deviation: the paper describes the `2 × 2` blocks of `C` and `D` only in words. `upwindMC`,
  `upwindMD` assemble `M_h C` and `M_h D` from the weak form (4.2) with the upwind flux (4.3),
  the cell basis `1, ξ` (mean and slope, (4.6)) and vacuum boundaries; `upwindC`, `upwindD`
  invert the cell mass matrix `massDG` (`diag(h, h/3)` per cell) into them, as stated after (4.4).
* Hypotheses that Lemma 5.2 leaves to its setting and that its proof uses: `w ≥ 0` with
  `Σ_m w_m = 1` (Section 4.1), speeds `v > 0`, total cross sections `σ ≥ 0`, `M_h` positive
  semidefinite. `growthBound_eq_zero_of_posSemidef`, `growthBound_absorber`: cases with `γ = 0`.

## Lemma 5.3, connected to the core
The core proves Lemma 5.3 on an abstract inner product space, with the energy inequality as
hypothesis as in the paper (`LeanDLRA.thetaMethod_resolvent`, `LeanDLRA.thetaMethod_step_le`).
`EnergySpace G` is `ℝⁿ` with `⟨x, y⟩ = xᵀ G y`; for `G = W V⁻¹`, `energy_inner_ge` turns the matrix
energy inequality into the core hypothesis, and `thetaMethod_matrix_resolvent`,
`thetaMethod_matrix_step_le` are Lemma 5.3 (i), (ii) for matrices.
`transport_thetaMethod_resolvent_of`, `transport_thetaMethod_step_le_of` and their DG instances
`transport_thetaMethod_resolvent`, `transport_thetaMethod_step_le` are Lemma 5.3 for the transport
scheme with the energy inequality supplied by Lemma 5.2, so they are unconditional. They need
positive weights `w > 0`, for `‖·‖_E` to be a norm (the paper's proof: `W` is SPD).

## Not formalized
* Proposition 5.1 (ii), (iii) (ranks inside the digits of an axis; they need the binary-digit
  structure of the shift matrix), Proposition 5.2 (TT-SVD rounding), and Appendix E (anisotropic
  scattering). The matrix theorems above take the energy inequality as a hypothesis, so they
  apply with `γ_Ω` once its inequality is proved.

## Core definitions used, local definitions added
Core: `LeanDLRA.Tensor`, `LeanDLRA.Tensor.unfold`, `LeanDLRA.EckartYoung.rank_add_le`,
`LeanDLRA.thetaMethod_resolvent`, `LeanDLRA.thetaMethod_step_le`. Local: the transport matrices
of the scheme (the core has no DG transport operators), `ttRank` (no core TT-rank; defined from
the core unfolding), `blockUnfolding` (bridged by `unfold_eq_blockUnfolding`), `lambdaMin`,
`symPart`, and `EnergySpace`, the bridge from matrices to the core inner-product-space theorems.
-/

open Finset Matrix
open scoped RealInnerProductSpace Kronecker

namespace LeanDLRA.Literature.P2611_04360

/-! ### Definitions 5.1 and 5.2, Lemma 5.1, Proposition 5.1 (i) -/

section TTRank

/-! #### Unfoldings of functions on two blocks of modes -/

variable {α β : Type*}

/-- The unfolding of a function on two blocks of modes, `X : α × β → ℝ`, with the first block in
the rows: `blockUnfolding X a b = X (a, b)`. The core `LeanDLRA.Tensor.unfold p X` is of this form
after grouping the modes into the `p`-part and the rest (`unfold_eq_blockUnfolding`). -/
def blockUnfolding (X : α × β → ℝ) : Matrix α β ℝ := Matrix.of fun a b => X (a, b)

/-- The rank of `blockUnfolding X`. -/
noncomputable def blockRank [Fintype β] (X : α × β → ℝ) : ℕ := (blockUnfolding X).rank

/-- Rank is unchanged by a left factor with a left inverse and a right factor with a right
inverse: if `X = P A Q` and `A = P' X Q'`, then `rank X = rank A`. -/
lemma rank_eq_of_two_sided {γ δ μ ν : Type*} [Fintype γ] [Fintype δ] [Fintype μ] [Fintype ν]
    {X : Matrix γ δ ℝ} {A : Matrix μ ν ℝ} (P : Matrix γ μ ℝ) (Q : Matrix ν δ ℝ)
    (P' : Matrix μ γ ℝ) (Q' : Matrix δ ν ℝ) (hX : X = P * A * Q) (hA : A = P' * X * Q') :
    X.rank = A.rank := by
  refine le_antisymm ?_ ?_
  · rw [hX]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · rw [hA]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- The unfolding of a product `X(a, b) = f(a) g(b)` is the outer product `f gᵀ`, equation (5.6)
of arXiv 2611.04360. -/
lemma blockUnfolding_mul (f : α → ℝ) (g : β → ℝ) :
    blockUnfolding (fun p : α × β => f p.1 * g p.2) = vecMulVec f g := by
  ext a b
  simp [blockUnfolding, vecMulVec_apply, Matrix.of_apply]

lemma blockRank_mul_le_one [Fintype β] (f : α → ℝ) (g : β → ℝ) :
    blockRank (fun p : α × β => f p.1 * g p.2) ≤ 1 := by
  rw [blockRank, blockUnfolding_mul]
  exact rank_vecMulVec_le f g

lemma blockRank_mul_eq_one [Finite α] [Fintype β] (f : α → ℝ) (g : β → ℝ) (hf : f ≠ 0)
    (hg : g ≠ 0) : blockRank (fun p : α × β => f p.1 * g p.2) = 1 := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.1 hf
  obtain ⟨b₀, hb₀⟩ := Function.ne_iff.1 hg
  have ha : f a₀ ≠ 0 := by simpa using ha₀
  have hb : g b₀ ≠ 0 := by simpa using hb₀
  rw [blockRank]
  have h := rank_eq_of_two_sided (A := (1 : Matrix Unit Unit ℝ))
    (X := blockUnfolding (fun p : α × β => f p.1 * g p.2))
    (Matrix.of fun a _ => f a) (Matrix.of fun _ b => g b)
    (Matrix.of fun _ a => if a = a₀ then (f a₀)⁻¹ else 0)
    (Matrix.of fun b _ => if b = b₀ then (g b₀)⁻¹ else 0) ?_ ?_
  · rw [h, rank_one, Fintype.card_unit]
  · ext a b
    simp [blockUnfolding, Matrix.mul_apply, Matrix.of_apply]
  · ext i j
    simp [blockUnfolding, Matrix.mul_apply, Matrix.of_apply, ite_mul]
    field_simp

/-- **Lemma 5.1 (c)** of arXiv 2611.04360 (equation (5.8)), with the modes grouped into blocks: at
a link `k = (j - 1) d + ℓ` inside the digits of the `j`-th axis, the rows of the unfolding of a
Kronecker product carry the factors on the preceding axes (their product `f`, on `L`) and the
first `ℓ` digits of the `j`-th factor (`M₁`), the columns its remaining digits (`M₂`) and the
factors on the following indices (product `g`, on `R`). Then `r_k(X)` equals the `ℓ`-th quantized
rank `r_ℓ(A^{(j)}) = blockRank a` of the `j`-th factor, viewed as the tensor `a : M₁ × M₂ → ℝ`.
As in (b), the other factors must be nonzero, which the paper leaves implicit. -/
theorem blockRank_eq_of_kronecker_axis {L M₁ M₂ R : Type*} [Finite L] [Finite M₁] [Fintype M₂]
    [Fintype R] (f : L → ℝ) (a : M₁ × M₂ → ℝ) (g : R → ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    blockRank (fun p : (L × M₁) × (M₂ × R) => f p.1.1 * a (p.1.2, p.2.1) * g p.2.2) =
      blockRank a := by
  classical
  have := Fintype.ofFinite L
  have := Fintype.ofFinite M₁
  obtain ⟨l₀, hl₀⟩ := Function.ne_iff.1 hf
  obtain ⟨r₀, hr₀⟩ := Function.ne_iff.1 hg
  have hl : f l₀ ≠ 0 := by simpa using hl₀
  have hr : g r₀ ≠ 0 := by simpa using hr₀
  refine rank_eq_of_two_sided
    (Matrix.of fun (p : L × M₁) (m : M₁) => if p.2 = m then f p.1 else 0)
    (Matrix.of fun (m : M₂) (p : M₂ × R) => if m = p.1 then g p.2 else 0)
    (Matrix.of fun (m : M₁) (p : L × M₁) => if p = (l₀, m) then (f l₀)⁻¹ else 0)
    (Matrix.of fun (p : M₂ × R) (m : M₂) => if p = (m, r₀) then (g r₀)⁻¹ else 0) ?_ ?_
  · ext ⟨l, m₁⟩ ⟨m₂, r⟩
    simp [blockUnfolding, Matrix.mul_apply, Matrix.of_apply, ite_mul]
  · ext m₁ m₂
    simp [blockUnfolding, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      Prod.ext_iff, ite_and]
    field_simp

/-- **Lemma 5.1 (d)** of arXiv 2611.04360: the identity has every quantized rank one. The digits
of an axis are split at the link into the first `ℓ` digits (`α`) and the remaining ones (`β`);
as a tensor whose modes carry the pair of a row and a column digit, the identity matrix on
`α × β` has the entry `δ(a, a') δ(b, b')`, and its unfolding at the link has rank one. -/
theorem blockRank_one_eq_one [Finite α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β] :
    blockRank (fun p : (α × α) × (β × β) =>
      (1 : Matrix (α × β) (α × β) ℝ) (p.1.1, p.2.1) (p.1.2, p.2.2)) = 1 := by
  obtain ⟨a⟩ := ‹Nonempty α›
  obtain ⟨b⟩ := ‹Nonempty β›
  have h := blockRank_mul_eq_one (fun q : α × α => (1 : Matrix α α ℝ) q.1 q.2)
    (fun q : β × β => (1 : Matrix β β ℝ) q.1 q.2)
    (Function.ne_iff.2 ⟨(a, a), by simp⟩) (Function.ne_iff.2 ⟨(b, b), by simp⟩)
  convert h using 3 with p
  rcases p with ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩
  simp only [Matrix.one_apply, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp_all

/-! #### TT-ranks of core tensors -/

variable {κ : Type*} {ι : κ → Type*} [Fintype κ] [DecidableEq κ] [∀ k, Fintype (ι k)]

/-- **Definitions 5.1 and 5.2** of arXiv 2611.04360 on the core tensors `LeanDLRA.Tensor ι`: the
unfolding with the modes `p` in the rows is the core `LeanDLRA.Tensor.unfold p X`, and the TT-rank
at that link is its rank. For a tensor train with modes `Fin d` the `k`-th TT-rank of the paper
is `ttRank (· < k) X` (the core's left interface at cut `k`). -/
noncomputable def ttRank (p : κ → Prop) [DecidablePred p] (X : Tensor ι) : ℕ :=
  (Tensor.unfold p X).rank

omit [Fintype κ] [DecidableEq κ] [∀ k, Fintype (ι k)] in
/-- Bridge to the block form: the core unfolding is the block unfolding of the tensor with its
modes grouped into the `p`-part and the rest. -/
lemma unfold_eq_blockUnfolding (p : κ → Prop) [DecidablePred p] (X : Tensor ι) :
    Tensor.unfold p X = blockUnfolding (fun ab => X (Tensor.merge p ab.1 ab.2)) :=
  rfl

lemma ttRank_eq_blockRank (p : κ → Prop) [DecidablePred p] (X : Tensor ι) :
    ttRank p X = blockRank (fun ab => X (Tensor.merge p ab.1 ab.2)) :=
  rfl

/-- **Lemma 5.1 (a)** of arXiv 2611.04360: TT-ranks are subadditive,
`r_k(X + Y) ≤ r_k(X) + r_k(Y)`. -/
theorem ttRank_add_le (p : κ → Prop) [DecidablePred p] (X Y : Tensor ι) :
    ttRank p (X + Y) ≤ ttRank p X + ttRank p Y := by
  have h : Tensor.unfold p (X + Y) = Tensor.unfold p X + Tensor.unfold p Y := by
    ext a b
    simp [Tensor.unfold, Matrix.of_apply]
  rw [ttRank, h]
  exact LeanDLRA.EckartYoung.rank_add_le _ _

/-- **Lemma 5.1 (b)** of arXiv 2611.04360, upper bound: a Kronecker product whose factors act
either on the modes in `p` or on the rest is separable at that link, `X(x) = f(x_p) g(x_{¬p})`,
its unfolding is the outer product (5.6), and its TT-rank there is at most one. -/
theorem ttRank_le_one_of_separable (p : κ → Prop) [DecidablePred p] (X : Tensor ι)
    (f : (∀ k : Subtype p, ι k) → ℝ) (g : (∀ k : {k // ¬ p k}, ι k) → ℝ)
    (hX : ∀ x, X x = f (Subtype.restrict p x) * g (Subtype.restrict (fun k => ¬ p k) x)) :
    ttRank p X ≤ 1 := by
  have h : (fun ab : (∀ k : Subtype p, ι k) × (∀ k : {k // ¬ p k}, ι k) =>
      X (Tensor.merge p ab.1 ab.2)) = fun ab => f ab.1 * g ab.2 := by
    funext ab
    rw [hX, Tensor.restrict_merge, Tensor.restrict_not_merge]
  rw [ttRank_eq_blockRank, h]
  exact blockRank_mul_le_one f g

/-- **Lemma 5.1 (b)**, equation (5.7) of arXiv 2611.04360: at a link that separates the factors of
a Kronecker product, the TT-rank is exactly one. The paper states `r_k(X) = 1` without a
nonvanishing hypothesis; equality needs both groups of factors to be nonzero (a zero factor gives
`X = 0` of rank `0`), which is assumed here. -/
theorem ttRank_eq_one_of_separable (p : κ → Prop) [DecidablePred p] (X : Tensor ι)
    (f : (∀ k : Subtype p, ι k) → ℝ) (g : (∀ k : {k // ¬ p k}, ι k) → ℝ)
    (hX : ∀ x, X x = f (Subtype.restrict p x) * g (Subtype.restrict (fun k => ¬ p k) x))
    (hf : f ≠ 0) (hg : g ≠ 0) : ttRank p X = 1 := by
  have h : (fun ab : (∀ k : Subtype p, ι k) × (∀ k : {k // ¬ p k}, ι k) =>
      X (Tensor.merge p ab.1 ab.2)) = fun ab => f ab.1 * g ab.2 := by
    funext ab
    rw [hX, Tensor.restrict_merge, Tensor.restrict_not_merge]
  rw [ttRank_eq_blockRank, h]
  exact blockRank_mul_eq_one f g hf hg

/-- **Proposition 5.1 (i)** of arXiv 2611.04360, abstract form: a sum (5.1) of `q` Kronecker
products, each separable at the link `p` (as every term is at the four links `k = d, 2d, 3d,
3d + 1` that separate two different indices), has TT-rank `r_k ≤ q` there. -/
theorem ttRank_sum_le (p : κ → Prop) [DecidablePred p] (X : Tensor ι) (q : ℕ)
    (f : ℕ → (∀ k : Subtype p, ι k) → ℝ) (g : ℕ → (∀ k : {k // ¬ p k}, ι k) → ℝ)
    (hX : ∀ x, X x = ∑ s ∈ range q,
      f s (Subtype.restrict p x) * g s (Subtype.restrict (fun k => ¬ p k) x)) :
    ttRank p X ≤ q := by
  have h : Tensor.unfold p X = ∑ s ∈ range q, vecMulVec (f s) (g s) := by
    ext a b
    simp [Tensor.unfold, Matrix.of_apply, hX, Matrix.sum_apply, vecMulVec_apply]
  rw [ttRank, h]
  clear h hX
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ]
    exact (LeanDLRA.EckartYoung.rank_add_le _ _).trans
      (add_le_add ih (rank_vecMulVec_le _ _))

end TTRank

/-! ### Quadratic forms and the smallest eigenvalue -/

section Quad

variable {ι : Type*} [Fintype ι]

/-- A quadratic form is unchanged by transposing its matrix. -/
lemma dotProduct_transpose_mulVec_self (T : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (Tᵀ *ᵥ x) = x ⬝ᵥ (T *ᵥ x) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

/-- Only the symmetric part of a matrix enters its quadratic form. -/
lemma dotProduct_mulVec_eq_half (T : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (T *ᵥ x) = (1 / 2) * (x ⬝ᵥ ((T + Tᵀ) *ᵥ x)) := by
  rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec_self]
  ring

lemma dotProduct_mulVec_nonneg_of_posSemidef {T : Matrix ι ι ℝ} (hT : T.PosSemidef)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (T *ᵥ x) := by
  simpa using hT.dotProduct_mulVec_nonneg x

/-- A matrix whose symmetric part is positive semidefinite has a nonnegative quadratic form. -/
lemma dotProduct_mulVec_nonneg_of_add_transpose {T : Matrix ι ι ℝ} (hT : (T + Tᵀ).PosSemidef)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (T *ᵥ x) := by
  rw [dotProduct_mulVec_eq_half]
  have := dotProduct_mulVec_nonneg_of_posSemidef hT x
  positivity

/-- A skew-symmetric matrix has a vanishing quadratic form. -/
lemma dotProduct_mulVec_eq_zero_of_add_transpose {T : Matrix ι ι ℝ} (hT : T + Tᵀ = 0)
    (x : ι → ℝ) : x ⬝ᵥ (T *ᵥ x) = 0 := by
  rw [dotProduct_mulVec_eq_half, hT]
  simp

/-- `λ_min(M)`, the smallest eigenvalue of a real symmetric matrix `M`: the infimum of its real
spectrum (for symmetric `M` the spectrum is the finite set of its eigenvalues). -/
noncomputable def lambdaMin [DecidableEq ι] (M : Matrix ι ι ℝ) : ℝ := sInf (spectrum ℝ M)

lemma lambdaMin_le_eigenvalues [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (i : ι) : lambdaMin M ≤ hM.eigenvalues i :=
  csInf_le (Matrix.finite_real_spectrum (A := M)).bddBelow (hM.eigenvalues_mem_spectrum_real i)

/-- The Rayleigh bound `λ_min(M) ‖y‖² ≤ yᵀ M y` for a real symmetric matrix. -/
lemma lambdaMin_mul_dotProduct_le [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (y : ι → ℝ) : lambdaMin M * (y ⬝ᵥ y) ≤ y ⬝ᵥ (M *ᵥ y) := by
  set U : Matrix ι ι ℝ := (hM.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  have hMU : M = U * diagonal hM.eigenvalues * Uᵀ := by
    have h := hM.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using h
  have hUU : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    simpa [star_eq_conjTranspose] using h
  set z := Uᵀ *ᵥ y with hz
  have hMy : M *ᵥ y = U *ᵥ (diagonal hM.eigenvalues *ᵥ z) := by
    rw [hz, mulVec_mulVec, mulVec_mulVec, ← hMU]
  have h1 : y ⬝ᵥ (M *ᵥ y) = z ⬝ᵥ (diagonal hM.eigenvalues *ᵥ z) := by
    rw [hMy, dotProduct_mulVec, ← mulVec_transpose]
  have h2 : y ⬝ᵥ y = z ⬝ᵥ z := by
    rw [hz, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, mulVec_mulVec, hUU,
      one_mulVec]
  rw [h1, h2]
  simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc lambdaMin M * (z i * z i) ≤ hM.eigenvalues i * (z i * z i) :=
        mul_le_mul_of_nonneg_right (lambdaMin_le_eigenvalues hM i) (mul_self_nonneg (z i))
    _ = z i * (hM.eigenvalues i * z i) := by ring

end Quad

/-! ### Lemma 5.2: the energy inequality -/

section Collision

variable {S Dir Grp : Type*}

/-- `sym(Y) = (Y + Yᵀ)/2`, the symmetric part, as in Lemma 5.2 of arXiv 2611.04360. -/
noncomputable def symPart (Y : Matrix Grp Grp ℝ) : Matrix Grp Grp ℝ := (1 / 2 : ℝ) • (Y + Yᵀ)

lemma symPart_transpose (Y : Matrix Grp Grp ℝ) : (symPart Y)ᵀ = symPart Y := by
  ext i j
  simp only [symPart, transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

lemma dotProduct_symPart_mulVec [Fintype Grp] (Y : Matrix Grp Grp ℝ) (ψ : Grp → ℝ) :
    ψ ⬝ᵥ (symPart Y *ᵥ ψ) = ψ ⬝ᵥ (Y *ᵥ ψ) := by
  rw [symPart, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add,
    dotProduct_transpose_mulVec_self, smul_eq_mul]
  ring

/-- `Σ_c = diag(σ¹, …, σ^G) - Σ_s - χ (νσ_f)ᵀ`, the group matrix of the collisions in the proof
of Lemma 5.2 of arXiv 2611.04360 (total cross sections `σ`, scattering matrix `Σ_s` (here `Ss`),
fission spectrum `χ` and production cross sections `νσ_f`). -/
def collisionMatrix [DecidableEq Grp] (σ : Grp → ℝ) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) :
    Matrix Grp Grp ℝ :=
  diagonal σ - Ss - vecMulVec χ νσf

/-- The growth bound of Lemma 5.2 of arXiv 2611.04360, exactly as printed:
`γ = max {0, -λ_min(V_G^{1/2} sym(diag(σ) - Σ_s - χ (νσ_f)ᵀ) V_G^{1/2})}` with
`V_G = diag(v₁, …, v_G)` the group speeds. -/
noncomputable def growthBound [Fintype Grp] [DecidableEq Grp] (v σ : Grp → ℝ)
    (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) : ℝ :=
  max 0 (-lambdaMin (diagonal (fun g => √(v g)) * symPart (collisionMatrix σ Ss χ νσf) *
    diagonal (fun g => √(v g))))

lemma growthBound_nonneg [Fintype Grp] [DecidableEq Grp] (v σ : Grp → ℝ)
    (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) : 0 ≤ growthBound v σ Ss χ νσf :=
  le_max_left _ _

/-- If the weighted symmetric collision matrix `V_G^{1/2} sym(Σ_c) V_G^{1/2}` is positive
semidefinite, then `γ = 0`, so that `ϑ = 1` (remark after Proposition 5.3 of arXiv 2611.04360). -/
lemma growthBound_eq_zero_of_posSemidef [Fintype Grp] [DecidableEq Grp] {v σ : Grp → ℝ}
    {Ss : Matrix Grp Grp ℝ} {χ νσf : Grp → ℝ}
    (h : (diagonal (fun g => √(v g)) * symPart (collisionMatrix σ Ss χ νσf) *
      diagonal (fun g => √(v g))).PosSemidef) :
    growthBound v σ Ss χ νσf = 0 := by
  have hl : 0 ≤ lambdaMin (diagonal (fun g => √(v g)) * symPart (collisionMatrix σ Ss χ νσf) *
      diagonal (fun g => √(v g))) := by
    apply Real.sInf_nonneg
    intro x hx
    rw [h.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact h.eigenvalues_nonneg i
  rw [growthBound]
  exact max_eq_left (by linarith)

/-- A pure absorber (no scattering, no fission production) has `γ = 0`. -/
lemma growthBound_absorber [Fintype Grp] [DecidableEq Grp] {v σ : Grp → ℝ}
    (hσ : ∀ g, 0 ≤ σ g) (χ : Grp → ℝ) : growthBound v σ 0 χ 0 = 0 := by
  apply growthBound_eq_zero_of_posSemidef
  have h : diagonal (fun g => √(v g)) * symPart (collisionMatrix σ 0 χ 0) *
      diagonal (fun g => √(v g)) = diagonal (fun g => √(v g) * σ g * √(v g)) := by
    have hs : symPart (collisionMatrix σ 0 χ 0) = diagonal σ := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [symPart, collisionMatrix]
        ring
      · simp [symPart, collisionMatrix, hij]
    rw [hs, diagonal_mul_diagonal, diagonal_mul_diagonal]
  rw [h]
  exact PosSemidef.diagonal fun g => by
    have := hσ g
    have := Real.sqrt_nonneg (v g)
    positivity

/-- The group step of the proof of Lemma 5.2 (ii) of arXiv 2611.04360: by the definition of `γ`,
`ψᵀ Σ_c ψ ≥ -γ ψᵀ V_G⁻¹ ψ` for every group vector `ψ`. -/
theorem collisionMatrix_quad_ge [Fintype Grp] [DecidableEq Grp] (v σ : Grp → ℝ)
    (hv : ∀ g, 0 < v g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) (ψ : Grp → ℝ) :
    -growthBound v σ Ss χ νσf * (ψ ⬝ᵥ (diagonal (fun g => 1 / v g) *ᵥ ψ)) ≤
      ψ ⬝ᵥ (collisionMatrix σ Ss χ νσf *ᵥ ψ) := by
  have hYh : (diagonal (fun g => √(v g)) * symPart (collisionMatrix σ Ss χ νσf) *
      diagonal (fun g => √(v g))).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_mul,
      diagonal_transpose, symPart_transpose, Matrix.mul_assoc]
  have hsq : ∀ g, √(v g) ≠ 0 := fun g => (Real.sqrt_pos.2 (hv g)).ne'
  have hψ : diagonal (fun g => √(v g)) *ᵥ (fun g => ψ g / √(v g)) = ψ := by
    funext g
    simp [mulVec_diagonal, mul_div_cancel₀ _ (hsq g)]
  have hquad : ψ ⬝ᵥ (collisionMatrix σ Ss χ νσf *ᵥ ψ) =
      (fun g => ψ g / √(v g)) ⬝ᵥ ((diagonal (fun g => √(v g)) *
        symPart (collisionMatrix σ Ss χ νσf) * diagonal (fun g => √(v g))) *ᵥ
          (fun g => ψ g / √(v g))) := by
    rw [← dotProduct_symPart_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec _ (diagonal _), ← mulVec_transpose, diagonal_transpose, hψ]
  have hnorm : (fun g => ψ g / √(v g)) ⬝ᵥ (fun g => ψ g / √(v g)) =
      ψ ⬝ᵥ (diagonal (fun g => 1 / v g) *ᵥ ψ) := by
    simp only [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [div_mul_div_comm, Real.mul_self_sqrt (hv g).le]
    ring
  have hray := lambdaMin_mul_dotProduct_le hYh (fun g => ψ g / √(v g))
  have hγ : -growthBound v σ Ss χ νσf ≤ lambdaMin (diagonal (fun g => √(v g)) *
      symPart (collisionMatrix σ Ss χ νσf) * diagonal (fun g => √(v g))) := by
    rw [growthBound, neg_le]
    exact le_max_right _ _
  have hζ0 : 0 ≤ (fun g => ψ g / √(v g)) ⬝ᵥ (fun g => ψ g / √(v g)) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun g _ => mul_self_nonneg _
  rw [hquad, ← hnorm]
  exact (mul_le_mul_of_nonneg_right hγ hζ0).trans hray

/-- The slice `x_m` of a state at the direction `m`: `x_m(s, g) = x((s, m), g)`. -/
def dirSlice (x : (S × Dir) × Grp → ℝ) (m : Dir) : S × Grp → ℝ := fun p => x ((p.1, m), p.2)

/-- The coefficients `ϕ = (I ⊗ wᵀ ⊗ I) x` of the angular average of a state (proof of
Lemma 5.2 (ii) of arXiv 2611.04360): `ϕ = Σ_m w_m x_m`. -/
noncomputable def angAvg [Fintype Dir] (w : Dir → ℝ) (x : (S × Dir) × Grp → ℝ) :
    S × Grp → ℝ :=
  ∑ m, w m • dirSlice x m

lemma kron_diagonal_mulVec [Fintype S] [Fintype Dir] [Fintype Grp] [DecidableEq Dir]
    (M3 : Matrix S S ℝ) (w : Dir → ℝ) (G : Matrix Grp Grp ℝ) (x : (S × Dir) × Grp → ℝ) (s : S)
    (m : Dir) (g : Grp) :
    ((M3 ⊗ₖ diagonal w ⊗ₖ G) *ᵥ x) ((s, m), g) = w m * ((M3 ⊗ₖ G) *ᵥ dirSlice x m) (s, g) := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, diagonal_apply,
    dirSlice, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_irrel, sum_const_zero, sum_ite_eq,
    mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl fun g' _ => ?_
  ring

lemma kron_vecMulVec_mulVec [Fintype S] [Fintype Dir] [Fintype Grp] (M3 : Matrix S S ℝ)
    (w : Dir → ℝ) (G : Matrix Grp Grp ℝ) (x : (S × Dir) × Grp → ℝ) (s : S) (m : Dir) (g : Grp) :
    ((M3 ⊗ₖ vecMulVec w w ⊗ₖ G) *ᵥ x) ((s, m), g) =
      w m * ((M3 ⊗ₖ G) *ᵥ angAvg w x) (s, g) := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, vecMulVec_apply,
    angAvg, dirSlice, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g' _ => ?_
  refine Finset.sum_congr rfl fun m' _ => ?_
  ring

lemma quad_kron_diagonal [Fintype S] [Fintype Dir] [Fintype Grp] [DecidableEq Dir]
    (M3 : Matrix S S ℝ) (w : Dir → ℝ) (G : Matrix Grp Grp ℝ) (x : (S × Dir) × Grp → ℝ) :
    x ⬝ᵥ ((M3 ⊗ₖ diagonal w ⊗ₖ G) *ᵥ x) =
      ∑ m, w m * (dirSlice x m ⬝ᵥ ((M3 ⊗ₖ G) *ᵥ dirSlice x m)) := by
  conv_lhs => rw [dotProduct]
  simp only [Fintype.sum_prod_type, kron_diagonal_mulVec]
  simp only [dotProduct, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [dirSlice]
  ring

lemma quad_kron_vecMulVec [Fintype S] [Fintype Dir] [Fintype Grp] (M3 : Matrix S S ℝ)
    (w : Dir → ℝ) (G : Matrix Grp Grp ℝ) (x : (S × Dir) × Grp → ℝ) :
    x ⬝ᵥ ((M3 ⊗ₖ vecMulVec w w ⊗ₖ G) *ᵥ x) = angAvg w x ⬝ᵥ ((M3 ⊗ₖ G) *ᵥ angAvg w x) := by
  conv_lhs => rw [dotProduct]
  simp only [Fintype.sum_prod_type, kron_vecMulVec_mulVec]
  conv_rhs => rw [dotProduct]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [angAvg, dirSlice, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Mean and fluctuation (proof of Lemma 5.2 (ii) of arXiv 2611.04360): for weights with
`Σ_m w_m = 1` and any bilinear form, the weighted average of the forms of the slices `y_m` equals
the form of the mean `ϕ = Σ_m w_m y_m` plus the weighted average of the forms of the
fluctuations `y_m - ϕ`. -/
lemma sum_quad_eq_avg_add [Fintype Dir] {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (w : Dir → ℝ) (hw : ∑ m, w m = 1) (y : Dir → ι → ℝ) (φ : ι → ℝ)
    (hφ : φ = ∑ m, w m • y m) :
    ∑ m, w m * (y m ⬝ᵥ (B *ᵥ y m)) =
      φ ⬝ᵥ (B *ᵥ φ) + ∑ m, w m * ((y m - φ) ⬝ᵥ (B *ᵥ (y m - φ))) := by
  have e1 : ∑ m, w m * (y m ⬝ᵥ (B *ᵥ φ)) = φ ⬝ᵥ (B *ᵥ φ) := by
    have h : φ ⬝ᵥ (B *ᵥ φ) = ∑ m, w m * (y m ⬝ᵥ (B *ᵥ φ)) := by
      nth_rewrite 1 [hφ]
      rw [sum_dotProduct]
      simp [smul_dotProduct]
    exact h.symm
  have e2 : ∑ m, w m * (φ ⬝ᵥ (B *ᵥ y m)) = φ ⬝ᵥ (B *ᵥ φ) := by
    have h : B *ᵥ φ = ∑ m, w m • (B *ᵥ y m) := by
      rw [hφ, mulVec_sum]
      simp [mulVec_smul]
    rw [h, dotProduct_sum]
    simp [dotProduct_smul]
  have e3 : ∑ m, w m * (φ ⬝ᵥ (B *ᵥ φ)) = φ ⬝ᵥ (B *ᵥ φ) := by
    rw [← Finset.sum_mul, hw, one_mul]
  have e4 : ∑ m, w m * ((y m - φ) ⬝ᵥ (B *ᵥ (y m - φ))) =
      ∑ m, w m * (y m ⬝ᵥ (B *ᵥ y m)) - ∑ m, w m * (y m ⬝ᵥ (B *ᵥ φ)) -
        ∑ m, w m * (φ ⬝ᵥ (B *ᵥ y m)) + ∑ m, w m * (φ ⬝ᵥ (B *ᵥ φ)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    ring
  rw [e4, e1, e2, e3]
  ring

/-- The fluctuation part is nonnegative: for a positive semidefinite `M₃ ⊗ G`, the form of the
angular average is at most the weighted form `xᵀ (M₃ ⊗ diag(w) ⊗ G) x`. -/
lemma quad_angAvg_le [Fintype S] [Fintype Dir] [Fintype Grp] [DecidableEq Dir]
    (M3 : Matrix S S ℝ) (w : Dir → ℝ) (hw : ∀ m, 0 ≤ w m) (hw1 : ∑ m, w m = 1)
    (G : Matrix Grp Grp ℝ) (hG : (M3 ⊗ₖ G).PosSemidef) (x : (S × Dir) × Grp → ℝ) :
    angAvg w x ⬝ᵥ ((M3 ⊗ₖ G) *ᵥ angAvg w x) ≤ x ⬝ᵥ ((M3 ⊗ₖ diagonal w ⊗ₖ G) *ᵥ x) := by
  rw [quad_kron_diagonal, sum_quad_eq_avg_add _ w hw1 (dirSlice x) (angAvg w x) rfl]
  have : 0 ≤ ∑ m, w m * ((dirSlice x m - angAvg w x) ⬝ᵥ
      ((M3 ⊗ₖ G) *ᵥ (dirSlice x m - angAvg w x))) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (hw m) (dotProduct_mulVec_nonneg_of_posSemidef hG _)
  exact le_add_of_nonneg_right this

/-- **Lemma 5.2 (ii) of arXiv 2611.04360, collision part**, in the Kronecker form of the proof:
with a positive semidefinite space factor `M₃` of the weight `W = M₃ ⊗ diag(w) ⊗ I_G`,
nonnegative angular weights summing to one, positive speeds `v` and nonnegative total cross
sections `σ`, the collision operator `Σ_t - S - F` of isotropic scattering satisfies
`xᵀ W (Σ_t - S - F) x ≥ -γ ‖x‖²_E`. The three products are written after multiplication by
`W`: `W Σ_t = M₃ ⊗ diag(w) ⊗ diag(σ)`, `W S = M₃ ⊗ w wᵀ ⊗ Σ_s`, `W F = M₃ ⊗ w wᵀ ⊗ χ (νσ_f)ᵀ`
(as `diag(w) 1 wᵀ = w wᵀ`), and `W V⁻¹ = M₃ ⊗ diag(w) ⊗ V_G⁻¹`. -/
theorem collision_energy_ge [Fintype S] [Fintype Dir] [Fintype Grp] [DecidableEq Dir]
    [DecidableEq Grp] (M3 : Matrix S S ℝ) (hM3 : M3.PosSemidef) (w : Dir → ℝ)
    (hw : ∀ m, 0 ≤ w m) (hw1 : ∑ m, w m = 1) (v σ : Grp → ℝ) (hv : ∀ g, 0 < v g)
    (hσ : ∀ g, 0 ≤ σ g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) (x : (S × Dir) × Grp → ℝ) :
    -growthBound v σ Ss χ νσf *
        (x ⬝ᵥ ((M3 ⊗ₖ diagonal w ⊗ₖ diagonal (fun g => 1 / v g)) *ᵥ x)) ≤
      x ⬝ᵥ ((M3 ⊗ₖ diagonal w ⊗ₖ diagonal σ) *ᵥ x) -
        x ⬝ᵥ ((M3 ⊗ₖ vecMulVec w w ⊗ₖ Ss) *ᵥ x) -
          x ⬝ᵥ ((M3 ⊗ₖ vecMulVec w w ⊗ₖ vecMulVec χ νσf) *ᵥ x) := by
  have hγ0 := growthBound_nonneg v σ Ss χ νσf
  have h1 := quad_angAvg_le M3 w hw hw1 (diagonal σ) (hM3.kronecker (PosSemidef.diagonal hσ)) x
  have h2 := quad_angAvg_le M3 w hw hw1 (diagonal fun g => 1 / v g)
    (hM3.kronecker (PosSemidef.diagonal fun g => (one_div_pos.2 (hv g)).le)) x
  -- the mean part: `ϕᵀ (M₃ ⊗ (Σ_c + γ V_G⁻¹)) ϕ ≥ 0`
  have hBq : ∀ ψ : Grp → ℝ, 0 ≤ ψ ⬝ᵥ ((collisionMatrix σ Ss χ νσf +
      growthBound v σ Ss χ νσf • diagonal (fun g => 1 / v g)) *ᵥ ψ) := by
    intro ψ
    have := collisionMatrix_quad_ge v σ hv Ss χ νσf ψ
    rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [neg_mul, neg_le_iff_add_nonneg] at this
    exact this
  have hmean := dotProduct_mulVec_nonneg_of_add_transpose (T := M3 ⊗ₖ (collisionMatrix σ Ss χ νσf
      + growthBound v σ Ss χ νσf • diagonal (fun g => 1 / v g))) ?_ (angAvg w x)
  · rw [quad_kron_vecMulVec, quad_kron_vecMulVec]
    have hsplitB : M3 ⊗ₖ (collisionMatrix σ Ss χ νσf +
        growthBound v σ Ss χ νσf • diagonal (fun g => 1 / v g)) =
        M3 ⊗ₖ diagonal σ - M3 ⊗ₖ Ss - M3 ⊗ₖ vecMulVec χ νσf +
          growthBound v σ Ss χ νσf • (M3 ⊗ₖ diagonal (fun g => 1 / v g)) := by
      ext i j
      simp only [collisionMatrix, kroneckerMap_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsplitB, add_mulVec, sub_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at hmean
    nlinarith [mul_le_mul_of_nonneg_left h2 hγ0]
  · rw [← kroneckerMap_transpose, ← conjTranspose_eq_transpose_of_trivial M3,
      hM3.isHermitian.eq, ← kronecker_add]
    refine hM3.kronecker (PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun ψ => ?_)
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_transpose,
        add_comm]
    · rw [star_trivial, add_mulVec, dotProduct_add, dotProduct_transpose_mulVec_self]
      linarith [hBq ψ]

end Collision

/-! ### Lemma 5.2 in the Kronecker form of the scheme -/

section Transport

variable {ι Dir Grp : Type*} [Fintype ι] [DecidableEq ι] [Fintype Dir] [DecidableEq Dir]
  [Fintype Grp] [DecidableEq Grp]

/-- `P + Pᵀ` of a Kronecker product with a symmetric right factor. -/
lemma kron_add_transpose_left {α β : Type*} (P : Matrix α α ℝ) (Q : Matrix β β ℝ)
    (hQ : Qᵀ = Q) : P ⊗ₖ Q + (P ⊗ₖ Q)ᵀ = (P + Pᵀ) ⊗ₖ Q := by
  rw [← kroneckerMap_transpose, hQ, add_kronecker]

/-- `P + Pᵀ` of a Kronecker product with a symmetric left factor. -/
lemma kron_add_transpose_right {α β : Type*} (P : Matrix α α ℝ) (Q : Matrix β β ℝ)
    (hP : Pᵀ = P) : P ⊗ₖ Q + (P ⊗ₖ Q)ᵀ = P ⊗ₖ (Q + Qᵀ) := by
  rw [← kroneckerMap_transpose, hP, kronecker_add]

/-- The weight matrix `W = M_h ⊗ M_h ⊗ M_h ⊗ diag(w) ⊗ I_G` of Section 5.3 of arXiv 2611.04360
(`M_h` the one-dimensional mass matrix, `w` the angular weights), on coefficient vectors indexed
by `(i_x, i_y, i_z, m, g)`. -/
def weightW (Mh : Matrix ι ι ℝ) (w : Dir → ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  Mh ⊗ₖ Mh ⊗ₖ Mh ⊗ₖ diagonal w ⊗ₖ (1 : Matrix Grp Grp ℝ)

/-- `V⁻¹ = I_n ⊗ I_n ⊗ I_n ⊗ I_M ⊗ diag(1/v₁, …, 1/v_G)`, equation (4.8) of arXiv 2611.04360. -/
noncomputable def invSpeed (v : Grp → ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix Dir Dir ℝ) ⊗ₖ
    diagonal (fun g => 1 / v g)

/-- `V = I_n ⊗ I_n ⊗ I_n ⊗ I_M ⊗ diag(v₁, …, v_G)`, the speed matrix of arXiv 2611.04360. -/
def speed (v : Grp → ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix Dir Dir ℝ) ⊗ₖ
    diagonal v

/-- The squared energy norm `‖x‖²_E = xᵀ W V⁻¹ x` of Section 5.3 of arXiv 2611.04360. -/
noncomputable def energyNormSq (Mh : Matrix ι ι ℝ) (w : Dir → ℝ) (v : Grp → ℝ)
    (x : (((ι × ι) × ι) × Dir) × Grp → ℝ) : ℝ :=
  x ⬝ᵥ ((weightW Mh w * invSpeed v) *ᵥ x)

/-- The streaming operator (4.7) of arXiv 2611.04360,
`L = C ⊗ I ⊗ I ⊗ Ω_x ⊗ I_G + D ⊗ I ⊗ I ⊗ |Ω_x| ⊗ I_G + (the same on the y and z axes)`,
with `C`, `D` the sign-changing and the dissipative part of the one-dimensional upwind
derivative (4.4) and `Ω_x = diag(Ω_{1,x}, …, Ω_{M,x})` the direction cosines. -/
def streaming (C D : Matrix ι ι ℝ) (Ωx Ωy Ωz : Dir → ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  C ⊗ₖ 1 ⊗ₖ 1 ⊗ₖ diagonal Ωx ⊗ₖ (1 : Matrix Grp Grp ℝ) +
    D ⊗ₖ 1 ⊗ₖ 1 ⊗ₖ diagonal (fun m => |Ωx m|) ⊗ₖ (1 : Matrix Grp Grp ℝ) +
    1 ⊗ₖ C ⊗ₖ 1 ⊗ₖ diagonal Ωy ⊗ₖ (1 : Matrix Grp Grp ℝ) +
    1 ⊗ₖ D ⊗ₖ 1 ⊗ₖ diagonal (fun m => |Ωy m|) ⊗ₖ (1 : Matrix Grp Grp ℝ) +
    1 ⊗ₖ 1 ⊗ₖ C ⊗ₖ diagonal Ωz ⊗ₖ (1 : Matrix Grp Grp ℝ) +
    1 ⊗ₖ 1 ⊗ₖ D ⊗ₖ diagonal (fun m => |Ωz m|) ⊗ₖ (1 : Matrix Grp Grp ℝ)

/-- The angular average `P₀ = 1 wᵀ` of Section 4.1 of arXiv 2611.04360. -/
def angularAverage (w : Dir → ℝ) : Matrix Dir Dir ℝ := vecMulVec (fun _ => 1) w

/-- The removal `Σ_t = I ⊗ I ⊗ I ⊗ I_M ⊗ diag(σ¹, …, σ^G)`, equation (4.8). -/
def removal (σ : Grp → ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix Dir Dir ℝ) ⊗ₖ
    diagonal σ

/-- The isotropic scattering `S = I ⊗ I ⊗ I ⊗ 1 wᵀ ⊗ Σ_s`, equation (4.8). -/
def scattering (w : Dir → ℝ) (Ss : Matrix Grp Grp ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ angularAverage w ⊗ₖ Ss

/-- The fission gain `F = I ⊗ I ⊗ I ⊗ 1 wᵀ ⊗ χ (νσ_f)ᵀ`, equation (4.10). -/
def fission (w : Dir → ℝ) (χ νσf : Grp → ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ (1 : Matrix ι ι ℝ) ⊗ₖ angularAverage w ⊗ₖ
    vecMulVec χ νσf

/-- The operator `𝒜 = L + Σ_t - S - F` of (4.11) of arXiv 2611.04360, for isotropic
scattering. -/
def transportOp (C D : Matrix ι ι ℝ) (Ωx Ωy Ωz : Dir → ℝ) (w : Dir → ℝ) (σ : Grp → ℝ)
    (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) :
    Matrix ((((ι × ι) × ι) × Dir) × Grp) ((((ι × ι) × ι) × Dir) × Grp) ℝ :=
  streaming C D Ωx Ωy Ωz + removal σ - scattering w Ss - fission w χ νσf

lemma diagonal_mul_angularAverage (w : Dir → ℝ) :
    diagonal w * angularAverage w = vecMulVec w w := by
  ext i j
  simp [angularAverage, diagonal_mul, vecMulVec_apply]

/-- **Lemma 5.2 (i) of arXiv 2611.04360**, Kronecker part: if `M_h` is symmetric positive
semidefinite, `M_h C` is skew-symmetric and `M_h D` has a positive semidefinite symmetric part,
then `xᵀ W L x ≥ 0` for every `x`, for any direction cosines and nonnegative angular weights. The
one-dimensional hypotheses are proved for the upwind DG matrices in `upwindC_skew` and
`upwindD_posSemidef` below. -/
theorem streaming_energy_nonneg (Mh C D : Matrix ι ι ℝ) (hMh : Mh.PosSemidef)
    (hC : Mh * C + (Mh * C)ᵀ = 0) (hD : (Mh * D + (Mh * D)ᵀ).PosSemidef) (Ωx Ωy Ωz : Dir → ℝ)
    (w : Dir → ℝ) (hw : ∀ m, 0 ≤ w m) (x : (((ι × ι) × ι) × Dir) × Grp → ℝ) :
    0 ≤ x ⬝ᵥ ((weightW Mh w * streaming C D Ωx Ωy Ωz) *ᵥ x) := by
  have hMhT : Mhᵀ = Mh := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hMh.isHermitian.eq
  have h1T : (1 : Matrix Grp Grp ℝ)ᵀ = 1 := transpose_one
  have hdT : ∀ d : Dir → ℝ, (diagonal d)ᵀ = diagonal d := fun d => diagonal_transpose d
  have hdP : ∀ d : Dir → ℝ, (∀ m, 0 ≤ d m) → (diagonal d).PosSemidef :=
    fun d hd => PosSemidef.diagonal hd
  have hwa : ∀ Ω : Dir → ℝ, ∀ m, 0 ≤ (w * fun m => |Ω m|) m :=
    fun Ω m => mul_nonneg (hw m) (abs_nonneg _)
  have h1P : (1 : Matrix Grp Grp ℝ).PosSemidef := PosSemidef.one
  simp only [weightW, streaming, Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one,
    diagonal_mul_diagonal, add_mulVec, dotProduct_add]
  have e1 : ∀ Ω : Dir → ℝ, x ⬝ᵥ (((Mh * C) ⊗ₖ Mh ⊗ₖ Mh ⊗ₖ diagonal (fun m => w m * Ω m) ⊗ₖ
      (1 : Matrix Grp Grp ℝ)) *ᵥ x) = 0 := by
    intro Ω
    refine dotProduct_mulVec_eq_zero_of_add_transpose ?_ x
    rw [kron_add_transpose_left _ _ h1T, kron_add_transpose_left _ _ (hdT _),
      kron_add_transpose_left _ _ hMhT, kron_add_transpose_left _ _ hMhT, hC]
    simp
  have e2 : ∀ Ω : Dir → ℝ, x ⬝ᵥ ((Mh ⊗ₖ (Mh * C) ⊗ₖ Mh ⊗ₖ diagonal (fun m => w m * Ω m) ⊗ₖ
      (1 : Matrix Grp Grp ℝ)) *ᵥ x) = 0 := by
    intro Ω
    refine dotProduct_mulVec_eq_zero_of_add_transpose ?_ x
    rw [kron_add_transpose_left _ _ h1T, kron_add_transpose_left _ _ (hdT _),
      kron_add_transpose_left _ _ hMhT, kron_add_transpose_right _ _ hMhT, hC]
    simp
  have e3 : ∀ Ω : Dir → ℝ, x ⬝ᵥ ((Mh ⊗ₖ Mh ⊗ₖ (Mh * C) ⊗ₖ diagonal (fun m => w m * Ω m) ⊗ₖ
      (1 : Matrix Grp Grp ℝ)) *ᵥ x) = 0 := by
    intro Ω
    refine dotProduct_mulVec_eq_zero_of_add_transpose ?_ x
    rw [kron_add_transpose_left _ _ h1T, kron_add_transpose_left _ _ (hdT _),
      kron_add_transpose_right _ _ (by rw [← kroneckerMap_transpose, hMhT]), hC]
    simp
  have f1 : ∀ Ω : Dir → ℝ, 0 ≤ x ⬝ᵥ (((Mh * D) ⊗ₖ Mh ⊗ₖ Mh ⊗ₖ
      diagonal (fun m => w m * |Ω m|) ⊗ₖ (1 : Matrix Grp Grp ℝ)) *ᵥ x) := by
    intro Ω
    refine dotProduct_mulVec_nonneg_of_add_transpose ?_ x
    rw [kron_add_transpose_left _ _ h1T, kron_add_transpose_left _ _ (hdT _),
      kron_add_transpose_left _ _ hMhT, kron_add_transpose_left _ _ hMhT]
    exact (((hD.kronecker hMh).kronecker hMh).kronecker (hdP _ (hwa Ω))).kronecker h1P
  have f2 : ∀ Ω : Dir → ℝ, 0 ≤ x ⬝ᵥ ((Mh ⊗ₖ (Mh * D) ⊗ₖ Mh ⊗ₖ
      diagonal (fun m => w m * |Ω m|) ⊗ₖ (1 : Matrix Grp Grp ℝ)) *ᵥ x) := by
    intro Ω
    refine dotProduct_mulVec_nonneg_of_add_transpose ?_ x
    rw [kron_add_transpose_left _ _ h1T, kron_add_transpose_left _ _ (hdT _),
      kron_add_transpose_left _ _ hMhT, kron_add_transpose_right _ _ hMhT]
    exact (((hMh.kronecker hD).kronecker hMh).kronecker (hdP _ (hwa Ω))).kronecker h1P
  have f3 : ∀ Ω : Dir → ℝ, 0 ≤ x ⬝ᵥ ((Mh ⊗ₖ Mh ⊗ₖ (Mh * D) ⊗ₖ
      diagonal (fun m => w m * |Ω m|) ⊗ₖ (1 : Matrix Grp Grp ℝ)) *ᵥ x) := by
    intro Ω
    refine dotProduct_mulVec_nonneg_of_add_transpose ?_ x
    rw [kron_add_transpose_left _ _ h1T, kron_add_transpose_left _ _ (hdT _),
      kron_add_transpose_right _ _ (by rw [← kroneckerMap_transpose, hMhT])]
    exact (((hMh.kronecker hMh).kronecker hD).kronecker (hdP _ (hwa Ω))).kronecker h1P
  have := e1 Ωx
  have := e2 Ωy
  have := e3 Ωz
  have := f1 Ωx
  have := f2 Ωy
  have := f3 Ωz
  simp only [Pi.mul_apply] at *
  linarith

/-- **Lemma 5.2 (ii) of arXiv 2611.04360** for abstract one-dimensional matrices: if `M_h` is
symmetric positive semidefinite, `M_h C` is skew-symmetric and `M_h D` has a positive
semidefinite symmetric part (the conclusions of Lemma 5.2 (i)), the angular weights are
nonnegative and sum to one, the speeds are positive and the total cross sections nonnegative,
then for isotropic scattering `xᵀ W 𝒜 x ≥ -γ ‖x‖²_E` for every `x`, with `γ` as printed. -/
theorem energy_inequality_of_streaming (Mh C D : Matrix ι ι ℝ) (hMh : Mh.PosSemidef)
    (hC : Mh * C + (Mh * C)ᵀ = 0) (hD : (Mh * D + (Mh * D)ᵀ).PosSemidef) (Ωx Ωy Ωz : Dir → ℝ)
    (w : Dir → ℝ) (hw : ∀ m, 0 ≤ w m) (hw1 : ∑ m, w m = 1) (v σ : Grp → ℝ) (hv : ∀ g, 0 < v g)
    (hσ : ∀ g, 0 ≤ σ g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ)
    (x : (((ι × ι) × ι) × Dir) × Grp → ℝ) :
    -growthBound v σ Ss χ νσf * energyNormSq Mh w v x ≤
      x ⬝ᵥ ((weightW Mh w * transportOp C D Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ x) := by
  have hL := streaming_energy_nonneg Mh C D hMh hC hD Ωx Ωy Ωz w hw x
  have hcol := collision_energy_ge (Mh ⊗ₖ Mh ⊗ₖ Mh) ((hMh.kronecker hMh).kronecker hMh) w hw
    hw1 v σ hv hσ Ss χ νσf x
  have hWV : weightW Mh w * invSpeed v = Mh ⊗ₖ Mh ⊗ₖ Mh ⊗ₖ diagonal w ⊗ₖ
      diagonal (fun g => 1 / v g) := by
    simp only [weightW, invSpeed, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hWR : weightW Mh w * removal σ = Mh ⊗ₖ Mh ⊗ₖ Mh ⊗ₖ diagonal w ⊗ₖ diagonal σ := by
    simp only [weightW, removal, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hWS : weightW Mh w * scattering w Ss = Mh ⊗ₖ Mh ⊗ₖ Mh ⊗ₖ vecMulVec w w ⊗ₖ Ss := by
    simp only [weightW, scattering, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      diagonal_mul_angularAverage]
  have hWF : weightW Mh w * fission w χ νσf =
      Mh ⊗ₖ Mh ⊗ₖ Mh ⊗ₖ vecMulVec w w ⊗ₖ vecMulVec χ νσf := by
    simp only [weightW, fission, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      diagonal_mul_angularAverage]
  rw [energyNormSq, hWV]
  rw [transportOp, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, hWR, hWS, hWF, sub_mulVec,
    sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_sub, dotProduct_add]
  linarith

end Transport

/-! ### The one-dimensional upwind DG matrices (Section 4.2, Lemma 5.2 (i)) -/

section UpwindDG

variable (N : ℕ)

/-- The mean coefficient `c₀` of cell `e` as a vector: coefficients are indexed by the pair
(basis index, cell), the basis index first as in (4.5) of arXiv 2611.04360; the basis on a cell is
`1, ξ` with `ξ ∈ (-1, 1)` the local coordinate, so index `0` is the mean and `1` the slope. -/
def meanCoeff (e : Fin N) : Fin 2 × Fin N → ℝ := fun i => if i = (0, e) then 1 else 0

/-- The slope coefficient `c₁` of cell `e` as a vector. -/
def slopeCoeff (e : Fin N) : Fin 2 × Fin N → ℝ := fun i => if i = (1, e) then 1 else 0

/-- The trace of `c₀ + c₁ ξ` at the right end `ξ = 1` of cell `e`: `r = φ(+1) = (1, 1)`. -/
def rightTrace (e : Fin N) : Fin 2 × Fin N → ℝ := meanCoeff N e + slopeCoeff N e

/-- The trace of `c₀ + c₁ ξ` at the left end `ξ = -1` of cell `e`: `l = φ(-1) = (1, -1)`. -/
def leftTrace (e : Fin N) : Fin 2 × Fin N → ℝ := meanCoeff N e - slopeCoeff N e

/-- The trace `u(x_f⁻)` from the left at the face `x_f`, `f = 0, …, N`: the right trace of cell
`f` (cells numbered from `0`), and the vacuum datum `0` at `x₀ = 0`. -/
def traceMinus : Fin (N + 1) → Fin 2 × Fin N → ℝ := Fin.cases 0 (rightTrace N)

/-- The trace `u(x_f⁺)` from the right at the face `x_f`: the left trace of cell `f`, and the
vacuum datum `0` at `x_N = L`. -/
def tracePlus : Fin (N + 1) → Fin 2 × Fin N → ℝ := Fin.lastCases 0 (leftTrace N)

/-- The jump `[[u]] = u(x_f⁻) - u(x_f⁺)` at the face `x_f`. -/
def faceJump (f : Fin (N + 1)) : Fin 2 × Fin N → ℝ := traceMinus N f - tracePlus N f

/-- The average `{u} = (u(x_f⁻) + u(x_f⁺))/2` at the face `x_f`. -/
noncomputable def faceAvg (f : Fin (N + 1)) : Fin 2 × Fin N → ℝ :=
  (1 / 2 : ℝ) • (traceMinus N f + tracePlus N f)

/-- `M_h C`, the sign-changing part of the mass-weighted upwind derivative (4.4) of
arXiv 2611.04360, assembled from the weak form (4.2) with the upwind flux (4.3),
`µψ̂ = µ {ψ} + |µ|/2 [[ψ]]`, for the basis `1, ξ`: entry `(i, j)` is the form with test function
`φ_i` and trial function `φ_j`, `-∫ φ_j φ_i' dx + Σ_faces {φ_j} [[φ_i]]`, where
`∫_{K_e} u v' dx = 2 c₀(u) c₁(v)` on a cell. The paper describes these blocks only in words. -/
noncomputable def upwindMC : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  ∑ e, (-2 : ℝ) • vecMulVec (slopeCoeff N e) (meanCoeff N e) +
    ∑ f, vecMulVec (faceJump N f) (faceAvg N f)

/-- `M_h D`, the dissipative part of the mass-weighted upwind derivative (4.4) of
arXiv 2611.04360: the jump term `Σ_faces (1/2) [[φ_j]] [[φ_i]]` of the upwind flux. -/
noncomputable def upwindMD : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  (1 / 2 : ℝ) • ∑ f, vecMulVec (faceJump N f) (faceJump N f)

/-- The cell mass of a basis function: `∫_{K_e} 1 dx = h` and `∫_{K_e} ξ² dx = h/3`. -/
noncomputable def cellMass (h : ℝ) (i : Fin 2 × Fin N) : ℝ := if i.1 = 0 then h else h / 3

/-- The one-dimensional mass matrix `M_h` of arXiv 2611.04360 (diagonal in the Legendre basis),
for `N` cells of width `h`. -/
noncomputable def massDG (h : ℝ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  diagonal (cellMass N h)

/-- The matrix `C` of (4.4) of arXiv 2611.04360: the cell mass matrix is inverted into it,
`C = M_h⁻¹ (M_h C)`. -/
noncomputable def upwindC (h : ℝ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  diagonal (fun i => 1 / cellMass N h i) * upwindMC N

/-- The matrix `D` of (4.4) of arXiv 2611.04360, `D = M_h⁻¹ (M_h D)`. -/
noncomputable def upwindD (h : ℝ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  diagonal (fun i => 1 / cellMass N h i) * upwindMD N

lemma cellMass_pos {h : ℝ} (hh : 0 < h) (i : Fin 2 × Fin N) : 0 < cellMass N h i := by
  unfold cellMass
  split_ifs <;> positivity

lemma massDG_posSemidef {h : ℝ} (hh : 0 < h) : (massDG N h).PosSemidef :=
  PosSemidef.diagonal fun i => (cellMass_pos N hh i).le

lemma massDG_mul_inv {h : ℝ} (hh : 0 < h) (A : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) :
    massDG N h * (diagonal (fun i => 1 / cellMass N h i) * A) = A := by
  rw [massDG, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  have : (fun i => cellMass N h i * (1 / cellMass N h i)) = fun _ => (1 : ℝ) := by
    funext i
    field_simp [(cellMass_pos N hh i).ne']
  rw [this, diagonal_one, Matrix.one_mul]

/-- **Lemma 5.2 (i) of arXiv 2611.04360, first claim for `C`**: `M_h C` is skew-symmetric. -/
theorem upwindC_skew {h : ℝ} (hh : 0 < h) :
    massDG N h * upwindC N h + (massDG N h * upwindC N h)ᵀ = 0 := by
  rw [upwindC, massDG_mul_inv N hh]
  have hjump : ∀ f, vecMulVec (faceJump N f) (faceAvg N f) +
      vecMulVec (faceAvg N f) (faceJump N f) =
      vecMulVec (traceMinus N f) (traceMinus N f) - vecMulVec (tracePlus N f) (tracePlus N f) := by
    intro f
    ext i j
    simp only [faceJump, faceAvg, Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm : ∑ f, vecMulVec (traceMinus N f) (traceMinus N f) =
      ∑ e, vecMulVec (rightTrace N e) (rightTrace N e) := by
    rw [Fin.sum_univ_succ]
    simp [traceMinus]
  have hp : ∑ f, vecMulVec (tracePlus N f) (tracePlus N f) =
      ∑ e, vecMulVec (leftTrace N e) (leftTrace N e) := by
    rw [Fin.sum_univ_castSucc]
    simp [tracePlus]
  have hcell : ∀ e, (-2 : ℝ) • (vecMulVec (slopeCoeff N e) (meanCoeff N e) +
      vecMulVec (meanCoeff N e) (slopeCoeff N e)) +
      (vecMulVec (rightTrace N e) (rightTrace N e) - vecMulVec (leftTrace N e) (leftTrace N e))
        = 0 := by
    intro e
    ext i j
    simp only [rightTrace, leftTrace, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      vecMulVec_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Matrix.zero_apply]
    ring
  have key : upwindMC N + (upwindMC N)ᵀ = ∑ e, ((-2 : ℝ) • (vecMulVec (slopeCoeff N e)
      (meanCoeff N e) + vecMulVec (meanCoeff N e) (slopeCoeff N e)) +
      (vecMulVec (rightTrace N e) (rightTrace N e) -
        vecMulVec (leftTrace N e) (leftTrace N e))) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← hm, ← hp, ← Finset.sum_sub_distrib]
    simp only [← hjump]
    rw [upwindMC, transpose_add, transpose_sum, transpose_sum]
    simp only [transpose_smul, transpose_vecMulVec, smul_add, Finset.sum_add_distrib]
    abel
  rw [key]
  exact Finset.sum_eq_zero fun e _ => hcell e

/-- The quadratic form of `M_h D` is half the sum of the squared jumps,
`xᵀ M_h D x = J(u)/2` with `J(u) = Σ_interior [[u]]² + u(0)² + u(L)²` (proof of Lemma 5.2 (i) of
arXiv 2611.04360). -/
theorem upwindMD_quad (x : Fin 2 × Fin N → ℝ) :
    x ⬝ᵥ (upwindMD N *ᵥ x) = (1 / 2) * ∑ f, (faceJump N f ⬝ᵥ x) ^ 2 := by
  have hsq : ∀ a : Fin 2 × Fin N → ℝ, x ⬝ᵥ (vecMulVec a a *ᵥ x) = (a ⬝ᵥ x) ^ 2 := by
    intro a
    simp only [dotProduct, mulVec, vecMulVec_apply]
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [upwindMD, smul_mulVec, dotProduct_smul, sum_mulVec, dotProduct_sum, smul_eq_mul]
  simp only [hsq]

/-- **Lemma 5.2 (i) of arXiv 2611.04360, first claim for `D`**: `M_h D` has a positive
semidefinite symmetric part (here `M_h D` is itself symmetric). -/
theorem upwindD_posSemidef {h : ℝ} (hh : 0 < h) :
    (massDG N h * upwindD N h + (massDG N h * upwindD N h)ᵀ).PosSemidef := by
  rw [upwindD, massDG_mul_inv N hh]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_transpose,
      add_comm]
  · rw [star_trivial, add_mulVec, dotProduct_add, dotProduct_transpose_mulVec_self,
      upwindMD_quad]
    have : 0 ≤ ∑ f, (faceJump N f ⬝ᵥ x) ^ 2 := Finset.sum_nonneg fun f _ => sq_nonneg _
    linarith

end UpwindDG

/-- **Lemma 5.2 of arXiv 2611.04360** (energy inequality), for the upwind DG discretization with
`N` cells of width `h > 0` per axis, degree-one Legendre basis, vacuum boundaries, isotropic
scattering, nonnegative angular weights summing to one, positive speeds and nonnegative total
cross sections: `xᵀ W 𝒜 x ≥ -γ ‖x‖²_E` for every `x`, with `γ` exactly as printed. The matrices
`M_h C`, `M_h D` are assembled from the weak form (4.2)–(4.3) (`upwindMC`, `upwindMD`); part (i)
is `upwindC_skew`, `upwindD_posSemidef`, `streaming_energy_nonneg`. -/
theorem energy_inequality {Dir Grp : Type*} [Fintype Dir] [DecidableEq Dir] [Fintype Grp]
    [DecidableEq Grp] (N : ℕ) {h : ℝ} (hh : 0 < h) (Ωx Ωy Ωz : Dir → ℝ) (w : Dir → ℝ)
    (hw : ∀ m, 0 ≤ w m) (hw1 : ∑ m, w m = 1) (v σ : Grp → ℝ) (hv : ∀ g, 0 < v g)
    (hσ : ∀ g, 0 ≤ σ g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ)
    (x : ((((Fin 2 × Fin N) × (Fin 2 × Fin N)) × (Fin 2 × Fin N)) × Dir) × Grp → ℝ) :
    -growthBound v σ Ss χ νσf * energyNormSq (massDG N h) w v x ≤
      x ⬝ᵥ ((weightW (massDG N h) w *
        transportOp (upwindC N h) (upwindD N h) Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ x) :=
  energy_inequality_of_streaming (massDG N h) (upwindC N h) (upwindD N h)
    (massDG_posSemidef N hh) (upwindC_skew N hh) (upwindD_posSemidef N hh) Ωx Ωy Ωz w hw hw1
    v σ hv hσ Ss χ νσf x

/-! ### The energy inner product: Lemma 5.2 gives the hypothesis of the core Lemma 5.3 -/

section EnergySpace

variable {n : Type*} [Fintype n]

/-- The coefficient space `ℝⁿ` with the inner product `⟨x, y⟩ = xᵀ G y` of a positive definite
matrix `G` (Mathlib's `Matrix.toInnerProductSpace`). For `G = W V⁻¹` this is the energy inner
product `⟨x, y⟩_E = xᵀ W V⁻¹ y` of Section 5.3 of arXiv 2611.04360; the type synonym lets the
abstract inner-product-space results of the core (`LeanDLRA.thetaMethod_resolvent`, ...) be
applied to the matrices of the scheme. -/
def EnergySpace (_G : Matrix n n ℝ) : Type _ := n → ℝ

variable {G : Matrix n n ℝ} [Fact G.PosDef]

noncomputable instance : NormedAddCommGroup (EnergySpace G) := G.toNormedAddCommGroup Fact.out

noncomputable instance : InnerProductSpace ℝ (EnergySpace G) :=
  G.toInnerProductSpace (Fact.out : G.PosDef).posSemidef

instance : FiniteDimensional ℝ (EnergySpace G) := inferInstanceAs (FiniteDimensional ℝ (n → ℝ))

/-- A coefficient vector as an element of the energy space. -/
def EnergySpace.of (G : Matrix n n ℝ) (x : n → ℝ) : EnergySpace G := x

lemma EnergySpace.inner_of (x y : n → ℝ) :
    ⟪EnergySpace.of G x, EnergySpace.of G y⟫ = x ⬝ᵥ (G *ᵥ y) := by
  change (G *ᵥ y) ⬝ᵥ star x = _
  rw [star_trivial, dotProduct_comm]

lemma EnergySpace.norm_of (x : n → ℝ) : ‖EnergySpace.of G x‖ = √(x ⬝ᵥ (G *ᵥ x)) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℝ), RCLike.re_to_real, EnergySpace.inner_of]

/-- A matrix as a linear map of the energy space. -/
noncomputable def EnergySpace.lin (G : Matrix n n ℝ) [Fact G.PosDef] (M : Matrix n n ℝ) :
    EnergySpace G →ₗ[ℝ] EnergySpace G :=
  Matrix.mulVecLin M

lemma EnergySpace.lin_of (M : Matrix n n ℝ) (x : n → ℝ) :
    EnergySpace.lin G M (EnergySpace.of G x) = EnergySpace.of G (M *ᵥ x) :=
  rfl

omit [Fact G.PosDef] in
/-- The energy inequality `xᵀ W A x ≥ -γ ‖x‖²_E` in the energy inner product:
`⟨x, V A x⟩_E ≥ -γ ‖x‖²_E`, since `xᵀ W y = ⟨x, V y⟩_E` (proof of Lemma 5.3 of
arXiv 2611.04360). -/
lemma energy_inner_ge [DecidableEq n] (Wm Vi Vm A : Matrix n n ℝ) [Fact (Wm * Vi).PosDef]
    (hViV : Vi * Vm = 1)
    {γ : ℝ} (hE : ∀ z, -γ * (z ⬝ᵥ ((Wm * Vi) *ᵥ z)) ≤ z ⬝ᵥ ((Wm * A) *ᵥ z)) (z : n → ℝ) :
    -γ * ‖EnergySpace.of (Wm * Vi) z‖ ^ 2 ≤ ⟪EnergySpace.of (Wm * Vi) z,
      EnergySpace.lin (Wm * Vi) Vm (EnergySpace.lin (Wm * Vi) A (EnergySpace.of (Wm * Vi) z))⟫ := by
  rw [← real_inner_self_eq_norm_sq, EnergySpace.lin_of, EnergySpace.lin_of,
    EnergySpace.inner_of, EnergySpace.inner_of, mulVec_mulVec, mulVec_mulVec,
    Matrix.mul_assoc Wm Vi, hViV, Matrix.mul_one]
  exact hE z

omit [Fact G.PosDef]

variable [DecidableEq n]

/-- **Bridge to the core θ-method lemma** (arXiv 2611.04360, proof of Lemma 5.3: "`⟨x, y⟩_E =
xᵀ W V⁻¹ y` is an inner product with norm `‖·‖_E`, and `xᵀ W y = ⟨x, V y⟩_E`"). For matrices `W`,
`V⁻¹`, `V` with `W V⁻¹` positive definite and `V V⁻¹ = V⁻¹ V = I`, the matrix energy inequality
`xᵀ W A x ≥ -γ xᵀ W V⁻¹ x` is the hypothesis of the core `LeanDLRA.thetaMethod_resolvent` in the
energy inner product; hence `K = V⁻¹ + θΔt A` is invertible and
`(1 - θγΔt) ‖z‖_E ≤ ‖V y‖_E` whenever `K z = y` (Lemma 5.3 (i)). -/
theorem thetaMethod_matrix_resolvent (Wm Vi Vm A : Matrix n n ℝ) (hG : (Wm * Vi).PosDef)
    (hVVi : Vm * Vi = 1) (hViV : Vi * Vm = 1) {γ θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt)
    (hs : θ * γ * Δt < 1)
    (hE : ∀ z, -γ * (z ⬝ᵥ ((Wm * Vi) *ᵥ z)) ≤ z ⬝ᵥ ((Wm * A) *ᵥ z)) :
    Function.Bijective (fun z => (Vi + (θ * Δt) • A) *ᵥ z) ∧
      ∀ y z, (Vi + (θ * Δt) • A) *ᵥ z = y →
        (1 - θ * γ * Δt) * √(z ⬝ᵥ ((Wm * Vi) *ᵥ z)) ≤
          √((Vm *ᵥ y) ⬝ᵥ ((Wm * Vi) *ᵥ (Vm *ᵥ y))) := by
  have : Fact (Wm * Vi).PosDef := ⟨hG⟩
  have hVVi' : ∀ z : n → ℝ, EnergySpace.lin (Wm * Vi) Vm (EnergySpace.lin (Wm * Vi) Vi
      (EnergySpace.of (Wm * Vi) z)) = EnergySpace.of (Wm * Vi) z := fun z => by
    rw [EnergySpace.lin_of, EnergySpace.lin_of, mulVec_mulVec, hVVi, one_mulVec]
  obtain ⟨hb, hbd⟩ := LeanDLRA.thetaMethod_resolvent (E := EnergySpace (Wm * Vi)) hVVi' hθ hΔt
    (energy_inner_ge Wm Vi Vm A hViV hE) hs
  have hK : ∀ z : n → ℝ, (EnergySpace.lin (Wm * Vi) Vi + (θ * Δt) • EnergySpace.lin (Wm * Vi) A)
      (EnergySpace.of (Wm * Vi) z) = EnergySpace.of (Wm * Vi) ((Vi + (θ * Δt) • A) *ᵥ z) := by
    intro z
    rw [LinearMap.add_apply, LinearMap.smul_apply, EnergySpace.lin_of, EnergySpace.lin_of,
      add_mulVec, smul_mulVec]
    rfl
  refine ⟨?_, fun y z hz => ?_⟩
  · have hfun : (fun z : n → ℝ => (Vi + (θ * Δt) • A) *ᵥ z) =
        ⇑(EnergySpace.lin (Wm * Vi) Vi + (θ * Δt) • EnergySpace.lin (Wm * Vi) A) := by
      funext z
      exact (hK z).symm
    rw [hfun]
    exact hb
  · have h := hbd (EnergySpace.of (Wm * Vi) y) (EnergySpace.of (Wm * Vi) z) (by rw [hK, hz])
    rwa [EnergySpace.norm_of, EnergySpace.lin_of, EnergySpace.norm_of] at h

/-- **Lemma 5.3 (ii) of arXiv 2611.04360 in matrix form**, through the core
`LeanDLRA.thetaMethod_step_le`: under the hypotheses of `thetaMethod_matrix_resolvent`, with
`1/2 ≤ θ ≤ 1` and `γ ≥ 0`, one exact step `K z = B x` (`B = V⁻¹ - (1 - θ) Δt A`) satisfies
`(1 - θγΔt) ‖z‖_E ≤ (1 + (1 - θ)γΔt) ‖x‖_E`. -/
theorem thetaMethod_matrix_step_le (Wm Vi Vm A : Matrix n n ℝ) (hG : (Wm * Vi).PosDef)
    (hVVi : Vm * Vi = 1) (hViV : Vi * Vm = 1) {γ θ Δt : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ0 : 0 ≤ γ) (hΔt : 0 ≤ Δt) (hs : θ * γ * Δt < 1)
    (hE : ∀ z, -γ * (z ⬝ᵥ ((Wm * Vi) *ᵥ z)) ≤ z ⬝ᵥ ((Wm * A) *ᵥ z)) {x z : n → ℝ}
    (hz : (Vi + (θ * Δt) • A) *ᵥ z = (Vi - ((1 - θ) * Δt) • A) *ᵥ x) :
    (1 - θ * γ * Δt) * √(z ⬝ᵥ ((Wm * Vi) *ᵥ z)) ≤
      (1 + (1 - θ) * γ * Δt) * √(x ⬝ᵥ ((Wm * Vi) *ᵥ x)) := by
  have : Fact (Wm * Vi).PosDef := ⟨hG⟩
  have hVVi' : ∀ z : n → ℝ, EnergySpace.lin (Wm * Vi) Vm (EnergySpace.lin (Wm * Vi) Vi
      (EnergySpace.of (Wm * Vi) z)) = EnergySpace.of (Wm * Vi) z := fun z => by
    rw [EnergySpace.lin_of, EnergySpace.lin_of, mulVec_mulVec, hVVi, one_mulVec]
  have hstep : EnergySpace.lin (Wm * Vi) Vi (EnergySpace.of (Wm * Vi) z) +
      (θ * Δt) • EnergySpace.lin (Wm * Vi) A (EnergySpace.of (Wm * Vi) z) =
      EnergySpace.lin (Wm * Vi) Vi (EnergySpace.of (Wm * Vi) x) -
        ((1 - θ) * Δt) • EnergySpace.lin (Wm * Vi) A (EnergySpace.of (Wm * Vi) x) := by
    rw [EnergySpace.lin_of, EnergySpace.lin_of, EnergySpace.lin_of, EnergySpace.lin_of]
    change EnergySpace.of (Wm * Vi) (Vi *ᵥ z + (θ * Δt) • (A *ᵥ z)) =
      EnergySpace.of (Wm * Vi) (Vi *ᵥ x - ((1 - θ) * Δt) • (A *ᵥ x))
    rw [← smul_mulVec, ← smul_mulVec, ← add_mulVec, ← sub_mulVec, hz]
  have h := LeanDLRA.thetaMethod_step_le (E := EnergySpace (Wm * Vi)) hVVi' hθ hθ1 hγ0 hΔt
    (energy_inner_ge Wm Vi Vm A hViV hE) hs hstep
  rwa [EnergySpace.norm_of, EnergySpace.norm_of] at h

end EnergySpace

section TransportStability

variable {Dir Grp : Type*} [Fintype Dir] [DecidableEq Dir] [Fintype Grp] [DecidableEq Grp]

lemma invSpeed_mul_speed {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Grp → ℝ)
    (hv : ∀ g, v g ≠ 0) :
    (invSpeed v : Matrix ((((ι × ι) × ι) × Dir) × Grp) _ ℝ) * speed v = 1 := by
  simp only [invSpeed, speed, ← mul_kronecker_mul, Matrix.mul_one, diagonal_mul_diagonal]
  have : (fun g => 1 / v g * v g) = fun _ => (1 : ℝ) := by
    funext g
    field_simp [hv g]
  rw [this, diagonal_one]
  simp

lemma speed_mul_invSpeed {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Grp → ℝ)
    (hv : ∀ g, v g ≠ 0) :
    (speed v : Matrix ((((ι × ι) × ι) × Dir) × Grp) _ ℝ) * invSpeed v = 1 := by
  simp only [invSpeed, speed, ← mul_kronecker_mul, Matrix.mul_one, diagonal_mul_diagonal]
  have : (fun g => v g * (1 / v g)) = fun _ => (1 : ℝ) := by
    funext g
    field_simp [hv g]
  rw [this, diagonal_one]
  simp

lemma weightW_mul_invSpeed_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Mh : Matrix ι ι ℝ) (hMh : Mh.PosDef) (w : Dir → ℝ) (hw : ∀ m, 0 < w m) (v : Grp → ℝ)
    (hv : ∀ g, 0 < v g) : (weightW Mh w * invSpeed v).PosDef := by
  simp only [weightW, invSpeed, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  exact (((hMh.kronecker hMh).kronecker hMh).kronecker (PosDef.diagonal hw)).kronecker
    (PosDef.diagonal fun g => one_div_pos.2 (hv g))

/-- **Lemma 5.3 (i) of arXiv 2611.04360 for the transport scheme**, for one-dimensional matrices
with the properties of Lemma 5.2 (i) and a positive definite mass matrix: with positive angular
weights summing to one, positive speeds, nonnegative total cross sections and isotropic
scattering, the step matrix `K = V⁻¹ + θΔt 𝒜` with `θ, Δt ≥ 0` and `θγΔt < 1` (`γ` of
Lemma 5.2) is invertible and `(1 - θγΔt) ‖z‖_E ≤ ‖V y‖_E` whenever `K z = y`. The energy
inequality, which the paper assumes in Lemma 5.3, is supplied by Lemma 5.2. -/
theorem transport_thetaMethod_resolvent_of {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Mh C D : Matrix ι ι ℝ) (hMh : Mh.PosDef) (hC : Mh * C + (Mh * C)ᵀ = 0)
    (hD : (Mh * D + (Mh * D)ᵀ).PosSemidef) (Ωx Ωy Ωz : Dir → ℝ) (w : Dir → ℝ)
    (hw : ∀ m, 0 < w m) (hw1 : ∑ m, w m = 1) (v σ : Grp → ℝ) (hv : ∀ g, 0 < v g)
    (hσ : ∀ g, 0 ≤ σ g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) {θ Δt : ℝ} (hθ : 0 ≤ θ)
    (hΔt : 0 ≤ Δt) (hs : θ * growthBound v σ Ss χ νσf * Δt < 1) :
    Function.Bijective (fun z => (invSpeed v + (θ * Δt) •
        transportOp C D Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ z) ∧
      ∀ y z, (invSpeed v + (θ * Δt) • transportOp C D Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ z = y →
        (1 - θ * growthBound v σ Ss χ νσf * Δt) * √(energyNormSq Mh w v z) ≤
          √(energyNormSq Mh w v (speed v *ᵥ y)) :=
  thetaMethod_matrix_resolvent (weightW Mh w) (invSpeed v) (speed v)
    (transportOp C D Ωx Ωy Ωz w σ Ss χ νσf) (weightW_mul_invSpeed_posDef Mh hMh w hw v hv)
    (speed_mul_invSpeed v fun g => (hv g).ne') (invSpeed_mul_speed v fun g => (hv g).ne') hθ
    hΔt hs fun z => energy_inequality_of_streaming Mh C D hMh.posSemidef hC hD Ωx Ωy Ωz w
      (fun m => (hw m).le) hw1 v σ hv hσ Ss χ νσf z

/-- **Lemma 5.3 (ii) of arXiv 2611.04360 for the transport scheme**: in the setting of
`transport_thetaMethod_resolvent_of`, with `1/2 ≤ θ ≤ 1`, one exact θ-step `K z = B x` satisfies
`(1 - θγΔt) ‖z‖_E ≤ (1 + (1 - θ)γΔt) ‖x‖_E`, i.e. `‖K⁻¹ B‖_E ≤ ϑ`. -/
theorem transport_thetaMethod_step_le_of {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Mh C D : Matrix ι ι ℝ) (hMh : Mh.PosDef) (hC : Mh * C + (Mh * C)ᵀ = 0)
    (hD : (Mh * D + (Mh * D)ᵀ).PosSemidef) (Ωx Ωy Ωz : Dir → ℝ) (w : Dir → ℝ)
    (hw : ∀ m, 0 < w m) (hw1 : ∑ m, w m = 1) (v σ : Grp → ℝ) (hv : ∀ g, 0 < v g)
    (hσ : ∀ g, 0 ≤ σ g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ) {θ Δt : ℝ} (hθ : 1 / 2 ≤ θ)
    (hθ1 : θ ≤ 1) (hΔt : 0 ≤ Δt) (hs : θ * growthBound v σ Ss χ νσf * Δt < 1)
    {x z : (((ι × ι) × ι) × Dir) × Grp → ℝ}
    (hz : (invSpeed v + (θ * Δt) • transportOp C D Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ z =
      (invSpeed v - ((1 - θ) * Δt) • transportOp C D Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ x) :
    (1 - θ * growthBound v σ Ss χ νσf * Δt) * √(energyNormSq Mh w v z) ≤
      (1 + (1 - θ) * growthBound v σ Ss χ νσf * Δt) * √(energyNormSq Mh w v x) :=
  thetaMethod_matrix_step_le (weightW Mh w) (invSpeed v) (speed v)
    (transportOp C D Ωx Ωy Ωz w σ Ss χ νσf) (weightW_mul_invSpeed_posDef Mh hMh w hw v hv)
    (speed_mul_invSpeed v fun g => (hv g).ne') (invSpeed_mul_speed v fun g => (hv g).ne') hθ hθ1
    (growthBound_nonneg v σ Ss χ νσf) hΔt hs
    (fun z => energy_inequality_of_streaming Mh C D hMh.posSemidef hC hD Ωx Ωy Ωz w
      (fun m => (hw m).le) hw1 v σ hv hσ Ss χ νσf z) hz

lemma massDG_posDef (N : ℕ) {h : ℝ} (hh : 0 < h) : (massDG N h).PosDef :=
  PosDef.diagonal fun i => cellMass_pos N hh i

/-- **Lemma 5.3 (i) of arXiv 2611.04360 for the upwind DG transport scheme, unconditional**: the
case of `transport_thetaMethod_resolvent_of` with `N` cells of width `h > 0` per axis, where
Lemma 5.2 (i) is `upwindC_skew` and `upwindD_posSemidef`. -/
theorem transport_thetaMethod_resolvent (N : ℕ) {h : ℝ} (hh : 0 < h) (Ωx Ωy Ωz : Dir → ℝ)
    (w : Dir → ℝ) (hw : ∀ m, 0 < w m) (hw1 : ∑ m, w m = 1) (v σ : Grp → ℝ)
    (hv : ∀ g, 0 < v g) (hσ : ∀ g, 0 ≤ σ g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ)
    {θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt) (hs : θ * growthBound v σ Ss χ νσf * Δt < 1) :
    Function.Bijective (fun z => (invSpeed v + (θ * Δt) •
        transportOp (upwindC N h) (upwindD N h) Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ z) ∧
      ∀ y z, (invSpeed v + (θ * Δt) •
          transportOp (upwindC N h) (upwindD N h) Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ z = y →
        (1 - θ * growthBound v σ Ss χ νσf * Δt) * √(energyNormSq (massDG N h) w v z) ≤
          √(energyNormSq (massDG N h) w v (speed v *ᵥ y)) :=
  transport_thetaMethod_resolvent_of (massDG N h) (upwindC N h) (upwindD N h)
    (massDG_posDef N hh) (upwindC_skew N hh) (upwindD_posSemidef N hh) Ωx Ωy Ωz w hw hw1 v σ hv
    hσ Ss χ νσf hθ hΔt hs

/-- **Lemma 5.3 (ii) of arXiv 2611.04360 for the upwind DG transport scheme, unconditional**:
`‖K⁻¹ B x‖_E ≤ ϑ ‖x‖_E` in the form `(1 - θγΔt) ‖z‖_E ≤ (1 + (1 - θ)γΔt) ‖x‖_E` for
`K z = B x`, `1/2 ≤ θ ≤ 1`. -/
theorem transport_thetaMethod_step_le (N : ℕ) {h : ℝ} (hh : 0 < h) (Ωx Ωy Ωz : Dir → ℝ)
    (w : Dir → ℝ) (hw : ∀ m, 0 < w m) (hw1 : ∑ m, w m = 1) (v σ : Grp → ℝ)
    (hv : ∀ g, 0 < v g) (hσ : ∀ g, 0 ≤ σ g) (Ss : Matrix Grp Grp ℝ) (χ νσf : Grp → ℝ)
    {θ Δt : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hΔt : 0 ≤ Δt)
    (hs : θ * growthBound v σ Ss χ νσf * Δt < 1)
    {x z : ((((Fin 2 × Fin N) × (Fin 2 × Fin N)) × (Fin 2 × Fin N)) × Dir) × Grp → ℝ}
    (hz : (invSpeed v + (θ * Δt) •
        transportOp (upwindC N h) (upwindD N h) Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ z =
      (invSpeed v - ((1 - θ) * Δt) •
        transportOp (upwindC N h) (upwindD N h) Ωx Ωy Ωz w σ Ss χ νσf) *ᵥ x) :
    (1 - θ * growthBound v σ Ss χ νσf * Δt) * √(energyNormSq (massDG N h) w v z) ≤
      (1 + (1 - θ) * growthBound v σ Ss χ νσf * Δt) * √(energyNormSq (massDG N h) w v x) :=
  transport_thetaMethod_step_le_of (massDG N h) (upwindC N h) (upwindD N h) (massDG_posDef N hh)
    (upwindC_skew N hh) (upwindD_posSemidef N hh) Ωx Ωy Ωz w hw hw1 v σ hv hσ Ss χ νσf hθ hθ1
    hΔt hs hz

end TransportStability

/-! ### Non-vacuity -/

/-- Non-vacuity of Lemma 5.1 (b), (c), (d) (arXiv 2611.04360): nonzero factors exist, and the
identity on two binary digits has quantized rank one. -/
example : blockRank (fun _ : Fin 2 × Fin 2 => (1 : ℝ) * 1) = 1 ∧
    blockRank (fun p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (p.1.1, p.2.1) (p.1.2, p.2.2)) = 1 :=
  ⟨blockRank_mul_eq_one (fun _ => 1) (fun _ => 1) (Function.ne_iff.2 ⟨0, by simp⟩)
    (Function.ne_iff.2 ⟨0, by simp⟩), blockRank_one_eq_one⟩

/-- Non-vacuity of Lemma 5.2 and of the transport θ-method theorems (arXiv 2611.04360): one
direction with weight `1`, one group of unit speed, a pure absorber `σ = 1` (so `γ = 0`), and
Crank–Nicolson `θ = 1/2` with any `Δt ≥ 0`; the hypotheses hold and the step matrix is
invertible. -/
example (N : ℕ) (Δt : ℝ) (hΔt : 0 ≤ Δt) :
    Function.Bijective (fun z => (invSpeed (fun _ : Fin 1 => (1 : ℝ)) + ((1 / 2 : ℝ) * Δt) •
      transportOp (upwindC N 1) (upwindD N 1) 0 0 0 (fun _ : Fin 1 => (1 : ℝ))
        (fun _ : Fin 1 => (1 : ℝ)) 0 0 0) *ᵥ z) := by
  have hγ : growthBound (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) 0 0 0 = 0 :=
    growthBound_absorber (fun _ => zero_le_one) 0
  refine (transport_thetaMethod_resolvent N one_pos 0 0 0 (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => one_pos) (by simp) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) (fun _ => one_pos)
    (fun _ => zero_le_one) 0 0 0 (by norm_num) hΔt ?_).1
  rw [hγ]
  norm_num

end LeanDLRA.Literature.P2611_04360
