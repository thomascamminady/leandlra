import LeanDLRA.Matrix.Projectors
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Literature.Stochastic.P2402_03586a

/-!
# Results of arXiv 2407.01404: Petrov-Galerkin DLR approximation and SUPG stabilisation

Nobile and Trigo Trindade, *Petrov-Galerkin Dynamical Low Rank Approximation: SUPG stabilisation
of advection-dominated problems*. This module formalizes the PG-DLR framework (§3) and the
SUPG-DLR stability analysis (§4) in finite dimensions.

## Matrix model of `V_h ⊗ L²_µ̂(Ω̂)` (§2-3)

`V_h ≅ ℝ^m` (an `X`-orthonormal basis) and `L²_µ̂ ≅ ℝ^n` (`f ↦ (√mᵢ f(ωᵢ))ᵢ`), so a random field
is a matrix with the Frobenius product. The stochastic modes form `Ŷ = [Y₀, Y₁, …, Y_R]`
(orthonormal, `Y₀` the mean mode; index type `Option k` in Algorithm 1), `H = H₁ ⊗ I` acts by
left multiplication with `H₁`, and `A_h(u, ·)`, `F(H ·)` are arbitrary linear functionals.

* `doTangent`: the tangent space (25), `{V Ŷᵀ + U Zᵀ : Ŷᵀ Z = 0}`. Bridge to the core:
  `mem_doTangent_iff` (it is `{U B + C Ŷᵀ}`) and `mem_doTangent_iff_tangentProj` (for orthonormal
  `U` it is the fixed-point set of `LeanDLRA.tangentProj U Ŷ`).
* `prop_3_1` (**Proposition 3.1**): (29) on the tangent space ⟺ the mode equations (35)-(36),
  via the identities (37) `inner_tangentVec_vecMulVec_col` and (38)
  `inner_tangentVec_vecMulVec_perp`. The paper proves "⇒"; "⇐" holds as the test functions span
  the tangent space.
* `IsPGDLRStep` (**Algorithm 1**, steps (40), (41), 3-5), `IsPGDLRStep.lemma_3_1`
  (**Lemma 3.1**), `IsPGDLRStep.variational` (**Theorem 3.1**, (43), no invertibility of `W̃`),
  `IsPGDLRStep.lemma_3_2` (**Lemma 3.2**), `IsPGDLRStep.lemma_4_1`, `IsPGDLRStep.lemma_4_2`
  (**Lemmas 4.1, 4.2**, as vector identities).
* `pgdlr_velocity_eq_oblique`: the remark after (29) (PG-DLR obliquely projects the dynamics)
  chained with Lemma 3.1 of arXiv 2402.03586 (`P2402_03586.supg_oblique_opNorm_le`): for
  `H = 1 + K`, `K` skew, `‖H‖ ≤ 2`, the velocity is `P g` and `‖u̇‖ ≤ 3 ‖g‖`.

## Finite model of the SUPG setting (§2.2.1, §4)

`SUPGModel`: `L²(D) ⊗ L²_µ̂` is replaced by functions on finitely many weighted points grouped
into cells; the trial space carries linear maps to values, gradients and pure second derivatives;
`ε`, `b`, `div b`, `c`, `δ_K` are data. The facts that the paper takes from `H¹₀(D)` and the finite
element space are hypotheses here (`IsFE`): integration by parts `(b·∇u, u) = -½(div b u, u)` and
the cellwise inverse inequality `h_K ‖∂ᵢ∂ᵢu‖_K ≤ C_I ‖∂ᵢu‖_K` (the local form of (5) used in the
appendix). Results that use them are conditional on them.

* `SUPGModel.lemma_2_1` (**Lemma 2.1**, weak coercivity (20)) for every `ν` with `µ̃ + ν ≥ 0`;
  `lemma_2_1'` with the paper's `ν` (12). (19) is `IsSUPGParam`, its first bound written
  pointwise (`2 δ_K |c| ≤ 1` on `K`, equivalent and free of `1/0`).
* **Theorem 4.1** (implicit Euler SUPG-DLR, `IsSUPGImplicitRun`): `thm_4_1_i` (case (i) as
  printed, `C₁ = 1/2`, `C₂ = 2/µ₀ + 4δ`), `thm_4_1_ii`, `thm_4_1_iii`; energy forms
  `SUPGModel.thm_4_1_*_of_tested` for any iterates satisfying (49) tested with `uⁿ⁺¹`.
* **Theorem 4.2** (semi-implicit SUPG-DLR, `IsSUPGSemiImplicitRun`, `A¹ₕ = aExpl`,
  `A²ₕ = aImpl`): `thm_4_2_i`, `thm_4_2_ii`, `thm_4_2_iii`; (70)-(72) are `IsSemiParam`; the
  extra terms (83)-(86) are `SUPGModel.aExpl_sub_le`.
* `thm_4_1_hypotheses_satisfiable`, `thm_4_2_hypotheses_satisfiable`: all hypotheses hold in a
  scalar instance (`scalarModel`), which is also a run of Algorithm 1 with `R = 0`.

## Corrections (counterexamples in the finite model, statements checked in the PDF, pp. 21-24)

* Theorem 4.1 (ii) and 4.2 (ii) ("`µ₀ = 0` and `f = 0` ⟹ (56) with `C₂ = 0`") are false when
  `ν > 0`, which `µ₀ = 0` allows: `thm_4_1_ii_as_printed_false`, `thm_4_2_ii_as_printed_false`
  (reaction `c = -1`: the step maps `u⁰ = 1` to `u¹ = 2`). The proofs use `ν = 0`;
  `thm_4_1_ii`, `thm_4_2_ii` assume `ν = 0` instead of `µ₀ = 0`.
* Theorem 4.1 (iii) and 4.2 (iii): the constant `C₃ = e^{(1+2ν)T}` is too small for the implicit
  Grönwall step: `thm_4_1_iii_as_printed_false`, `thm_4_2_iii_as_printed_false`. The corrected
  constant is `(1 + 4δ̄) (1 - Δt(1+2ν))^{-N}` (`gronwall_implicit`, built on the core
  `LeanDLRA.discrete_gronwall_le`), at most `(1 + 4δ̄) e^{(1+2ν)T/(1-Δt(1+2ν))}`
  (`SUPGModel.inv_one_sub_pow_le_exp`); the factor `1 + 4δ̄` is the load term of (69).

## Other differences from the paper

* Finite model instead of `L²(D)`, with the hypotheses of `IsFE`; on the matrix model, `hH` says
  that `H₁` represents the SUPG test operator (17) (`b` deterministic) and `hval` that the
  Frobenius product is `(·,·)_{X, L²_µ̂}`.
* `δ̄` is any upper bound of the `δ_K` (the paper's `δ = max_K δ_K` is one); the load may change
  from step to step (`fⁿ`); `µ₀ = 0`, `f ≠ 0` are not needed in (iii); `δ_K ≥ 0` is explicit.
* Theorem 4.2: the proof gives `A₀' = ‖u⁰‖² + 3Δt/32 (ε̂‖∇u⁰‖² + ‖µ^{1/2}u⁰‖²)` (the `n = 0`
  terms of (83)-(86) times `2Δt`) in place of the printed
  `A₀ = ‖u⁰‖² + ⅛ ε̂‖∇u⁰‖² + ⅛ ‖µ^{1/2}u⁰‖²`; `A₀' ≤ A₀` for `Δt ≤ 4/3` (`SUPGModel.semiA0_le`).
  Whether the printed `A₀` holds for `Δt > 4/3` is left open. (85) needs
  `δ_K |||c⋆|||_K ≤ 1/8`, obtained from (72) and `c̄` being a mean of `c` on the cell
  (`IsSemiParam.c_mean`); `ε̄`, `c̄` may depend on the point.
* Theorem 3.1 and Algorithm 1 hold for any orthonormal `Ŷ` (the mean mode need not be constant).

Not formalized: the skewing conditions (C1)-(C2) and Remarks 1-3 (§3.1), the explicit update
equations (47)-(48), (52)-(53) beyond their variational forms, and the experiments (§5).

Core definitions used: `LeanDLRA.tangentProj` (bridge for `doTangent`), the Frobenius inner
product, `LeanDLRA.discrete_gronwall_le`, and the oblique-projector lemma of arXiv 2402.03586.
Local definitions without a core counterpart: `IsPGDLRStep` (the staggered DO scheme of
Algorithm 1), `SUPGModel` and its forms, `perpProj`, `pgGram`.
-/

open Finset Matrix
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2407_01404

noncomputable section

/-! ### Rank-one calculus in the matrix model -/

section RankOne

variable {m n k k' : Type*}

/-- The Frobenius pairing with a rank-one matrix `a ⊗ y = a yᵀ` is `⟪X, a yᵀ⟫ = (X y) ⬝ a`. -/
theorem inner_vecMulVec [Fintype m] [Fintype n] (X : Matrix m n ℝ) (a : m → ℝ) (y : n → ℝ) :
    ⟪X, vecMulVec a y⟫ = (X *ᵥ y) ⬝ᵥ a := by
  rw [LeanDLRA.Frobenius.inner_def]
  simp only [vecMulVec_apply, dotProduct, mulVec, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `V Yᵀ = ∑ⱼ Vⱼ ⊗ Yⱼ` (sum of the rank-one terms of the columns). -/
theorem mul_transpose_eq_sum [Fintype k] (V : Matrix m k ℝ) (Y : Matrix n k ℝ) :
    V * Yᵀ = ∑ j, vecMulVec (V.col j) (Y.col j) := by
  ext a ω
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

/-- The projection `P⊥ z = z - Ŷ Ŷᵀ z` onto the orthogonal complement of the columns of `Ŷ`. For
`Ŷ = [Y₀, Y₁, …, Y_R]` with `Y₀` the constant mode this is the paper's `P_Y^⊥ z = z⋆ - P_Y z`. -/
def perpProj [Fintype n] [Fintype k'] (Yh : Matrix n k' ℝ) (z : n → ℝ) : n → ℝ :=
  z - Yh *ᵥ (Yhᵀ *ᵥ z)

theorem transpose_mulVec_perpProj [Fintype n] [Fintype k'] [DecidableEq k'] {Yh : Matrix n k' ℝ}
    (hY : Yhᵀ * Yh = 1) (z : n → ℝ) : Yhᵀ *ᵥ perpProj Yh z = 0 := by
  simp only [perpProj, mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc, hY, Matrix.one_mul,
    sub_self]

theorem perpProj_eq_self [Fintype n] [Fintype k'] {Yh : Matrix n k' ℝ} {z : n → ℝ}
    (hz : Yhᵀ *ᵥ z = 0) : perpProj Yh z = z := by
  simp [perpProj, hz]

theorem mulVec_col_eq_zero [Fintype n] {Yh : Matrix n k' ℝ} {Z : Matrix n k ℝ}
    (hZ : Yhᵀ * Z = 0) (j : k) : Yhᵀ *ᵥ Z.col j = 0 := by
  rw [← col_mul_eq_mulVec_col, hZ]
  rfl

/-- `Ŷᵀ Ẏ = 0` gives `Ẏᵀ Ŷ = 0`. -/
theorem transpose_mul_eq_zero [Fintype n] {Yh : Matrix n k' ℝ} {Yd : Matrix n k ℝ}
    (h : Yhᵀ * Yd = 0) : Ydᵀ * Yh = 0 := by
  rw [← transpose_transpose (Ydᵀ * Yh), transpose_mul, transpose_transpose, h, transpose_zero]

end RankOne

/-! ### The tangent space of the mean-tracking DO manifold -/

section Tangent

variable {m n k k' : Type*}

/-- **The tangent space (25)** of the manifold `M_R` of mean-tracking rank-`R` random fields at
`u = U₀ Y₀ + U Yᵀ`, in the matrix model. `Ŷ = [Y₀, Y₁, …, Y_R]` collects all stochastic modes
(orthonormal, `Y₀` the constant mode) and `U = [U₁, …, U_R]` the deterministic modes without the
mean `U₀`. The tangent space consists of `δu = V Ŷᵀ + U Zᵀ` with `V` arbitrary and `Ŷᵀ Z = 0`: the
stochastic variations `δyᵢ` have zero mean and satisfy the Dual DO gauge (24). It does not depend
on `U₀`. -/
def doTangent [Fintype n] [Fintype k] [Fintype k'] (U : Matrix m k ℝ) (Yh : Matrix n k' ℝ) :
    Set (Matrix m n ℝ) :=
  {X | ∃ (V : Matrix m k' ℝ) (Z : Matrix n k ℝ), Yhᵀ * Z = 0 ∧ X = V * Yhᵀ + U * Zᵀ}

/-- A linear functional that vanishes on the generators `vₕ ⊗ Ŷⱼ` and `Uⱼ ⊗ P⊥ z` of the tangent
space vanishes on the whole tangent space. -/
theorem eq_zero_of_mem_doTangent [Fintype n] [Fintype k] [Fintype k']
    (ℓ : Matrix m n ℝ →ₗ[ℝ] ℝ) {U : Matrix m k ℝ} {Yh : Matrix n k' ℝ}
    (h1 : ∀ (vh : m → ℝ) (j : k'), ℓ (vecMulVec vh (Yh.col j)) = 0)
    (h2 : ∀ (z : n → ℝ) (j : k), ℓ (vecMulVec (U.col j) (perpProj Yh z)) = 0)
    {v : Matrix m n ℝ} (hv : v ∈ doTangent U Yh) : ℓ v = 0 := by
  obtain ⟨V, Z, hZ, rfl⟩ := hv
  rw [map_add, mul_transpose_eq_sum, mul_transpose_eq_sum, map_sum, map_sum]
  have h2' : ∀ j, ℓ (vecMulVec (U.col j) (Z.col j)) = 0 := fun j => by
    rw [← perpProj_eq_self (mulVec_col_eq_zero hZ j)]
    exact h2 _ j
  simp [h1, h2']

/-- The test functions `vₕ Yⱼ` of (35) lie in the tangent space. -/
theorem vecMulVec_col_mem_doTangent [Fintype n] [Fintype k] [Fintype k']
    (U : Matrix m k ℝ) (Yh : Matrix n k' ℝ) (vh : m → ℝ) (j : k') :
    vecMulVec vh (Yh.col j) ∈ doTangent U Yh := by
  classical
  refine ⟨vecMulVec vh (Pi.single j 1), 0, by simp, ?_⟩
  rw [vecMulVec_mul, single_one_vecMul, transpose_zero, Matrix.mul_zero, add_zero]
  rfl

/-- The test functions `Uⱼ P⊥ z` of (36) lie in the tangent space. -/
theorem vecMulVec_perp_mem_doTangent [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k']
    {Yh : Matrix n k' ℝ} (hY : Yhᵀ * Yh = 1) (U : Matrix m k ℝ) (z : n → ℝ) (j : k) :
    vecMulVec (U.col j) (perpProj Yh z) ∈ doTangent U Yh := by
  classical
  refine ⟨0, vecMulVec (perpProj Yh z) (Pi.single j 1), ?_, ?_⟩
  · rw [mul_vecMulVec, transpose_mulVec_perpProj hY, zero_vecMulVec]
  · rw [Matrix.zero_mul, zero_add, transpose_vecMulVec, mul_vecMulVec, mulVec_single_one]

/-- **Bridge to the core tangent space.** For orthonormal `Ŷ`, the tangent space (25) consists of
the matrices `U B + C Ŷᵀ`: the tangent space of Koch–Lubich at `U S Ŷᵀ` (left basis `U` of the `R`
non-mean deterministic modes, right basis `Ŷ` of all `R + 1` stochastic modes). -/
theorem mem_doTangent_iff [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k']
    {U : Matrix m k ℝ} {Yh : Matrix n k' ℝ} (hY : Yhᵀ * Yh = 1) (X : Matrix m n ℝ) :
    X ∈ doTangent U Yh ↔ ∃ (B : Matrix k n ℝ) (C : Matrix m k' ℝ), X = U * B + C * Yhᵀ := by
  constructor
  · rintro ⟨V, Z, -, rfl⟩
    exact ⟨Zᵀ, V, add_comm _ _⟩
  · rintro ⟨B, C, rfl⟩
    refine ⟨C + U * B * Yh, Bᵀ - Yh * (Yhᵀ * Bᵀ), ?_, ?_⟩
    · rw [Matrix.mul_sub, ← Matrix.mul_assoc, hY, Matrix.one_mul, sub_self]
    · rw [transpose_sub, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
        Matrix.add_mul, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel

/-- **Bridge to `LeanDLRA.tangentProj`.** If `U` has orthonormal columns, the tangent space (25) is
the fixed-point set of the core tangent-space projector `tangentProj U Ŷ`. -/
theorem mem_doTangent_iff_tangentProj [Fintype m] [Fintype n] [Fintype k] [Fintype k']
    [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ} {Yh : Matrix n k' ℝ} (hU : Uᵀ * U = 1)
    (hY : Yhᵀ * Yh = 1) (X : Matrix m n ℝ) :
    X ∈ doTangent U Yh ↔ LeanDLRA.tangentProj U Yh X = X := by
  rw [mem_doTangent_iff hY, LeanDLRA.tangentProj_eq_self_iff hU hY]

end Tangent

/-! ### Proposition 3.1: the PG-DLR mode equations -/

section Prop31

variable {m n k k' : Type*}

/-- The skewed Gram matrix `W_ij = ⟨Uᵢ, H₁ Uⱼ⟩_X` of Proposition 3.1 and Algorithm 1. -/
def pgGram [Fintype m] (U : Matrix m k ℝ) (H1 : Matrix m m ℝ) : Matrix k k ℝ := Uᵀ * H1 * U

/-- The linear functional `v ↦ c ⟪w, H₁ v⟫ + G v` on the matrix model. -/
def pgFunctional [Fintype m] [Fintype n] (H1 : Matrix m m ℝ) (c : ℝ) (w : Matrix m n ℝ)
    (G : Matrix m n ℝ →ₗ[ℝ] ℝ) : Matrix m n ℝ →ₗ[ℝ] ℝ where
  toFun v := c * ⟪w, H1 * v⟫ + G v
  map_add' v v' := by rw [Matrix.mul_add, inner_add_right, map_add]; ring
  map_smul' a v := by
    rw [Matrix.mul_smul, real_inner_smul_right, map_smul, smul_eq_mul, RingHom.id_apply]; ring

theorem pgFunctional_apply [Fintype m] [Fintype n] (H1 : Matrix m m ℝ) (c : ℝ)
    (w : Matrix m n ℝ) (G : Matrix m n ℝ →ₗ[ℝ] ℝ) (v : Matrix m n ℝ) :
    pgFunctional H1 c w G v = c * ⟪w, H1 * v⟫ + G v := rfl

/-- **Eq. (37)**: testing `δu = U̇ Ŷᵀ + U Ẏᵀ` (with `Ŷᵀ Ẏ = 0`) against
`H(vₕ Yⱼ) = (H₁ vₕ) Yⱼ` gives `⟨U̇ⱼ, H₁ vₕ⟩_X`. -/
theorem inner_tangentVec_vecMulVec_col [Fintype m] [Fintype n] [Fintype k] [Fintype k']
    [DecidableEq k'] {Yh : Matrix n k' ℝ} {Yd : Matrix n k ℝ} (hY : Yhᵀ * Yh = 1)
    (hYd : Yhᵀ * Yd = 0) (Ud : Matrix m k' ℝ) (U : Matrix m k ℝ) (H1 : Matrix m m ℝ)
    (vh : m → ℝ) (j : k') :
    ⟪Ud * Yhᵀ + U * Ydᵀ, H1 * vecMulVec vh (Yh.col j)⟫ = Ud.col j ⬝ᵥ (H1 *ᵥ vh) := by
  have e : (Ud * Yhᵀ + U * Ydᵀ) *ᵥ Yh.col j = Ud.col j := by
    change ((Ud * Yhᵀ + U * Ydᵀ) * Yh).col j = Ud.col j
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hY, transpose_mul_eq_zero hYd,
      Matrix.mul_one, Matrix.mul_zero, add_zero]
  rw [mul_vecMulVec, inner_vecMulVec, e]

/-- **Eq. (38)**: testing `δu = U̇ Ŷᵀ + U Ẏᵀ` (with `Ŷᵀ Ẏ = 0`) against `H(Uⱼ P⊥ z)` gives
`∑ᵢ E[Ẏᵢ z] Wᵢⱼ`. -/
theorem inner_tangentVec_vecMulVec_perp [Fintype m] [Fintype n] [Fintype k] [Fintype k']
    [DecidableEq k'] {Yh : Matrix n k' ℝ} {Yd : Matrix n k ℝ} (hY : Yhᵀ * Yh = 1)
    (hYd : Yhᵀ * Yd = 0) (Ud : Matrix m k' ℝ) (U : Matrix m k ℝ) (H1 : Matrix m m ℝ)
    (z : n → ℝ) (j : k) :
    ⟪Ud * Yhᵀ + U * Ydᵀ, H1 * vecMulVec (U.col j) (perpProj Yh z)⟫ =
      (Ydᵀ *ᵥ z) ⬝ᵥ (pgGram U H1).col j := by
  have e : (Ud * Yhᵀ + U * Ydᵀ) *ᵥ perpProj Yh z = U *ᵥ (Ydᵀ *ᵥ z) := by
    rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, transpose_mulVec_perpProj hY, mulVec_zero,
      zero_add, perpProj, mulVec_sub, mulVec_mulVec (M := Ydᵀ) (N := Yh),
      transpose_mul_eq_zero hYd, zero_mulVec, sub_zero]
  have e' : (pgGram U H1).col j = Uᵀ *ᵥ (H1 *ᵥ U.col j) := by
    rw [mulVec_mulVec]; rfl
  rw [mul_vecMulVec, inner_vecMulVec, e, e', dotProduct_mulVec (Ydᵀ *ᵥ z) Uᵀ, vecMul_transpose]

/-- **Proposition 3.1 of arXiv 2407.01404** (evolution equations for PG-DLR, version 1), with
`H = H₁ ⊗ I`. Write the velocity as `u̇ = U̇ Ŷᵀ + U Ẏᵀ`, where `Ŷ = [Y₀, …, Y_R]` is orthonormal,
`U̇ = [U̇₀, …, U̇_R]` and `Ẏ = [Ẏ₁, …, Ẏ_R]` satisfies `Ŷᵀ Ẏ = 0` (zero mean and the Dual DO gauge).
Let `Ah v = A_h(u, v)` and `FH v = F(H v)` (any linear functionals). Then the PG-DLR problem (29),
tested on the whole tangent space, is equivalent to the mode equations (35) and (36), with
`W = Uᵀ H₁ U` (`pgGram`) and `E_µ̂[Ẏᵢ z] = (Ẏᵀ z)ᵢ`. The paper proves the direction (29) ⇒
(35)-(36); the converse holds because the test functions of (35)-(36) span the tangent space.

Matrix model: `V_h ≅ ℝ^m` with an `X`-orthonormal basis and `L²_µ̂ ≅ ℝ^n` through
`f ↦ (√mᵢ f(ωᵢ))ᵢ`, so both inner products are Euclidean and `V_h ⊗ L²_µ̂` carries the Frobenius
product; `H₁` is the matrix of `vₕ ↦ Π_{V_h} H₁ vₕ`, which is all that enters the left-hand sides
since `u̇ ∈ V_h ⊗ L²_µ̂`. -/
theorem prop_3_1 [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k']
    {Yh : Matrix n k' ℝ} {Yd : Matrix n k ℝ} (hY : Yhᵀ * Yh = 1)
    (hYd : Yhᵀ * Yd = 0) (Ud : Matrix m k' ℝ) (U : Matrix m k ℝ) (H1 : Matrix m m ℝ)
    (Ah FH : Matrix m n ℝ →ₗ[ℝ] ℝ) :
    (∀ v ∈ doTangent U Yh, ⟪Ud * Yhᵀ + U * Ydᵀ, H1 * v⟫ + Ah v = FH v) ↔
      (∀ (vh : m → ℝ) (j : k'), Ud.col j ⬝ᵥ (H1 *ᵥ vh) + Ah (vecMulVec vh (Yh.col j)) =
          FH (vecMulVec vh (Yh.col j))) ∧
      (∀ (z : n → ℝ) (j : k), (Ydᵀ *ᵥ z) ⬝ᵥ (pgGram U H1).col j +
          Ah (vecMulVec (U.col j) (perpProj Yh z)) =
            FH (vecMulVec (U.col j) (perpProj Yh z))) := by
  constructor
  · intro h
    refine ⟨fun vh j => ?_, fun z j => ?_⟩
    · rw [← inner_tangentVec_vecMulVec_col hY hYd Ud U H1 vh j]
      exact h _ (vecMulVec_col_mem_doTangent U Yh vh j)
    · rw [← inner_tangentVec_vecMulVec_perp hY hYd Ud U H1 z j]
      exact h _ (vecMulVec_perp_mem_doTangent hY U z j)
  · rintro ⟨h35, h36⟩ v hv
    have key := eq_zero_of_mem_doTangent (pgFunctional H1 1 (Ud * Yhᵀ + U * Ydᵀ) (Ah - FH))
      (fun vh j => ?_) (fun z j => ?_) hv
    · rw [pgFunctional_apply, LinearMap.sub_apply] at key
      linarith
    · rw [pgFunctional_apply, LinearMap.sub_apply,
        inner_tangentVec_vecMulVec_col hY hYd Ud U H1 vh j]
      linarith [h35 vh j]
    · rw [pgFunctional_apply, LinearMap.sub_apply,
        inner_tangentVec_vecMulVec_perp hY hYd Ud U H1 z j]
      linarith [h36 z j]

end Prop31

/-! ### PG-DLR as an oblique projection (link to arXiv 2402.03586) -/

section Oblique

/-- The tangent space (25) as a submodule of the matrix model. -/
def doTangentSubmodule {m n k k' : Type*} [Fintype n] [Fintype k] [Fintype k']
    (U : Matrix m k ℝ) (Yh : Matrix n k' ℝ) : Submodule ℝ (Matrix m n ℝ) where
  carrier := doTangent U Yh
  add_mem' := by
    rintro _ _ ⟨V, Z, hZ, rfl⟩ ⟨V', Z', hZ', rfl⟩
    refine ⟨V + V', Z + Z', by rw [Matrix.mul_add, hZ, hZ', add_zero], ?_⟩
    rw [transpose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  smul_mem' := by
    rintro a _ ⟨V, Z, hZ, rfl⟩
    refine ⟨a • V, a • Z, by rw [Matrix.mul_smul, hZ, smul_zero], ?_⟩
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **PG-DLR is an oblique projection of the dynamics** (arXiv 2407.01404, remark after (29):
"obliquely projecting the dynamics `-L u + f` onto `T_u M_R`"), combined with **Lemma 3.1 of
arXiv 2402.03586** (`LeanDLRA.Literature.P2402_03586.supg_oblique_opNorm_le`). Let `T` be the
tangent space (e.g. `doTangentSubmodule`), `H = 1 + K` with `K` skew and `‖H‖ ≤ 2` (the setting of
2402.03586: SUPG with `div b = 0` under its step-size condition), and let the right-hand side of
(29) have the Petrov-Galerkin form `v ↦ (g, H v)` for a residual `g` (`g = f - L u`). If `P` is an
oblique projector onto `T` in the sense of eq. (12) of 2402.03586, then every PG-DLR velocity
`u̇ ∈ T` equals `P g`, so `‖u̇‖ ≤ 3 ‖g‖`. The hypotheses `hK`, `hG` are those of the cited lemma. -/
theorem pgdlr_velocity_eq_oblique (T : Submodule ℝ E) (K : E →L[ℝ] E)
    (hK : ∀ x : E, ⟪x, K x⟫ = 0) (hG : ‖(1 : E →L[ℝ] E) + K‖ ≤ 2) (P : E →L[ℝ] E)
    (hPT : ∀ x, P x ∈ T)
    (hP : ∀ x, ∀ w ∈ T, ⟪P x, ((1 : E →L[ℝ] E) + K) w⟫ = ⟪x, ((1 : E →L[ℝ] E) + K) w⟫)
    {g ud : E} (hud : ud ∈ T)
    (h29 : ∀ v ∈ T, ⟪ud, ((1 : E →L[ℝ] E) + K) v⟫ = ⟪g, ((1 : E →L[ℝ] E) + K) v⟫) :
    ud = P g ∧ ‖ud‖ ≤ 3 * ‖g‖ := by
  have hz : P g - ud ∈ T := T.sub_mem (hPT g) hud
  have h0 : ⟪P g - ud, ((1 : E →L[ℝ] E) + K) (P g - ud)⟫ = 0 := by
    rw [inner_sub_left, hP g _ hz, h29 _ hz, sub_self]
  have hcoer : ∀ z : E, ⟪z, ((1 : E →L[ℝ] E) + K) z⟫ = ‖z‖ ^ 2 := by
    intro z
    simp [inner_add_right, hK]
  have heq : ud = P g := by
    rw [hcoer] at h0
    exact (sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))).symm
  refine ⟨heq, ?_⟩
  have hP3 := (LeanDLRA.Literature.P2402_03586.supg_oblique_opNorm_le T K hK hG P hPT hP).1
  rw [heq]
  exact (P.le_opNorm g).trans (mul_le_mul_of_nonneg_right hP3 (norm_nonneg g))

end Oblique

/-! ### Algorithm 1, Lemmas 3.1-3.2 and Theorem 3.1 -/

section Algorithm1

variable {m n k : Type*}

/-- The non-mean columns `[A₁, …, A_R]` of `A = [A₀, A₁, …, A_R]` (index `none` is the mean
mode `0`). -/
def tail (A : Matrix m (Option k) ℝ) : Matrix m k ℝ := A.submatrix id some

/-- **One step of Algorithm 1 of arXiv 2407.01404** (the staggered PG-DLR step), matrix model. The
current iterate is `uⁿ = Û Ŷᵀ` with `Ŷ = [Y₀, Y₁ⁿ, …, Y_Rⁿ]` orthonormal (column `none` is the mean
mode `Y₀`); `A1 u = A¹ₕ(u, ·)`, `A2 u = A²ₕ(u, ·)` and `FH = F(H ·)` are the linear functionals of
(39)-(41), `H = H₁ ⊗ I`.
* `step1` is (40) for `j = 0, …, R` (unknowns `Ũⱼ`);
* `perp` and `step2` are (41): `δỸⱼ ∈ (Yⁿ)^⊥` (zero mean, orthogonal to `Y₁ⁿ, …, Y_Rⁿ`) with
  `W̃ = Ũᵀ H₁ Ũ` (`Ũ = [Ũ₁, …, Ũ_R]`);
* `next` is steps 3-5: `uⁿ⁺¹ = Ũ₀ Y₀ + ∑ᵢ Ũᵢ Ỹᵢ` with `Ỹᵢ = Yᵢⁿ + δỸᵢ`. The orthonormalisation
  of step 4 rewrites this sum in new modes and does not change `uⁿ⁺¹`.
The scheme is implicit through `A2 un1`: the structure states that `(Ũ, δỸ, uⁿ⁺¹)` solve the
equations, as in the paper. -/
structure IsPGDLRStep [Fintype m] [Fintype n] [Fintype k] [DecidableEq k] (H1 : Matrix m m ℝ)
    (A1 A2 : Matrix m n ℝ → Matrix m n ℝ →ₗ[ℝ] ℝ) (FH : Matrix m n ℝ →ₗ[ℝ] ℝ) (Δt : ℝ)
    (un : Matrix m n ℝ) (Uh : Matrix m (Option k) ℝ) (Yh : Matrix n (Option k) ℝ)
    (Ut : Matrix m (Option k) ℝ) (dY : Matrix n k ℝ) (un1 : Matrix m n ℝ) : Prop where
  start : un = Uh * Yhᵀ
  orth : Yhᵀ * Yh = 1
  step1 : ∀ (vh : m → ℝ) (j : Option k),
    Δt⁻¹ * ((Ut - Uh).col j ⬝ᵥ (H1 *ᵥ vh)) + A1 un (vecMulVec vh (Yh.col j)) +
      A2 un1 (vecMulVec vh (Yh.col j)) = FH (vecMulVec vh (Yh.col j))
  perp : Yhᵀ * dY = 0
  step2 : ∀ (z : n → ℝ) (j : k),
    Δt⁻¹ * ((dYᵀ *ᵥ z) ⬝ᵥ (pgGram (tail Ut) H1).col j) +
      A1 un (vecMulVec ((tail Ut).col j) (perpProj Yh z)) +
      A2 un1 (vecMulVec ((tail Ut).col j) (perpProj Yh z)) =
        FH (vecMulVec ((tail Ut).col j) (perpProj Yh z))
  next : un1 = vecMulVec (Ut.col none) (Yh.col none) + tail Ut * (tail Yh + dY)ᵀ

/-- `Û Ŷᵀ = Û₀ Y₀ + ∑ᵢ Ûᵢ Yᵢ`. -/
theorem mul_transpose_option [Fintype k] (A : Matrix m (Option k) ℝ)
    (Y : Matrix n (Option k) ℝ) :
    A * Yᵀ = vecMulVec (A.col none) (Y.col none) + tail A * (tail Y)ᵀ := by
  rw [mul_transpose_eq_sum, mul_transpose_eq_sum, Fintype.sum_option]
  rfl

namespace IsPGDLRStep

variable [Fintype m] [Fintype n] [Fintype k] [DecidableEq k] {H1 : Matrix m m ℝ}
  {A1 A2 : Matrix m n ℝ → Matrix m n ℝ →ₗ[ℝ] ℝ} {FH : Matrix m n ℝ →ₗ[ℝ] ℝ} {Δt : ℝ}
  {un : Matrix m n ℝ} {Uh : Matrix m (Option k) ℝ} {Yh : Matrix n (Option k) ℝ}
  {Ut : Matrix m (Option k) ℝ} {dY : Matrix n k ℝ} {un1 : Matrix m n ℝ}

/-- Steps 3-5 of Algorithm 1 in compact form: `uⁿ⁺¹ = Ũ Ŷᵀ + Ũ_{1:R} δỸᵀ`. -/
theorem next' (h : IsPGDLRStep H1 A1 A2 FH Δt un Uh Yh Ut dY un1) :
    un1 = Ut * Yhᵀ + tail Ut * dYᵀ := by
  rw [h.next, mul_transpose_option, transpose_add, Matrix.mul_add, add_assoc]

/-- **Lemma 3.1 of arXiv 2407.01404.** After one step of Algorithm 1 the new stochastic modes
`Ỹ = Yⁿ + δỸ` (non-mean modes) satisfy `E[(Ỹᵢ - Yᵢⁿ) Yⱼⁿ] = 0` and `E[Ỹᵢ Yⱼⁿ] = δᵢⱼ`. -/
theorem lemma_3_1 (h : IsPGDLRStep H1 A1 A2 FH Δt un Uh Yh Ut dY un1) :
    ((tail Yh + dY) - tail Yh)ᵀ * tail Yh = 0 ∧ (tail Yh + dY)ᵀ * tail Yh = 1 := by
  have h1 : dYᵀ * tail Yh = 0 := by
    ext i j
    have := congrFun (congrFun h.perp (some j)) i
    simpa [Matrix.mul_apply, tail, mul_comm] using this
  have h2 : (tail Yh)ᵀ * tail Yh = 1 := by
    ext i j
    have := congrFun (congrFun h.orth (some i)) (some j)
    simpa [Matrix.mul_apply, Matrix.one_apply, tail] using this
  refine ⟨by rw [add_sub_cancel_left, h1], ?_⟩
  rw [transpose_add, Matrix.add_mul, h1, h2, add_zero]

/-- **Lemma 3.2 of arXiv 2407.01404.** Both `uⁿ` and `uⁿ⁺¹` lie in the tangent space at
`û = ∑ᵢ₌₀^R Ũᵢ Yᵢⁿ`, i.e. in `doTangent Ũ_{1:R} Ŷ`. -/
theorem lemma_3_2 (h : IsPGDLRStep H1 A1 A2 FH Δt un Uh Yh Ut dY un1) :
    un ∈ doTangent (tail Ut) Yh ∧ un1 ∈ doTangent (tail Ut) Yh :=
  ⟨⟨Uh, 0, Matrix.mul_zero _, by rw [h.start, transpose_zero, Matrix.mul_zero, add_zero]⟩,
    ⟨Ut, dY, h.perp, h.next'⟩⟩

theorem sub_eq (h : IsPGDLRStep H1 A1 A2 FH Δt un Uh Yh Ut dY un1) :
    un1 - un = (Ut - Uh) * Yhᵀ + tail Ut * dYᵀ := by
  rw [h.next', h.start, Matrix.sub_mul]
  abel

/-- **Theorem 3.1 of arXiv 2407.01404** (discrete variational formulation (43)). The output of one
step of Algorithm 1 satisfies
`Δt⁻¹ (uⁿ⁺¹ - uⁿ, H v) + A¹ₕ(uⁿ, v) + A²ₕ(uⁿ⁺¹, v) = F(H v)` for every `v` in the tangent space
`T_{Ũ (Yⁿ)ᵀ} M_R`. As in the paper, no invertibility of `W̃` is needed. -/
theorem variational (h : IsPGDLRStep H1 A1 A2 FH Δt un Uh Yh Ut dY un1) {v : Matrix m n ℝ}
    (hv : v ∈ doTangent (tail Ut) Yh) :
    Δt⁻¹ * ⟪un1 - un, H1 * v⟫ + A1 un v + A2 un1 v = FH v := by
  have key := eq_zero_of_mem_doTangent
    (pgFunctional H1 Δt⁻¹ (un1 - un) (A1 un + A2 un1 - FH)) (fun vh j => ?_) (fun z j => ?_) hv
  · rw [pgFunctional_apply, LinearMap.sub_apply, LinearMap.add_apply] at key
    linarith
  · rw [pgFunctional_apply, LinearMap.sub_apply, LinearMap.add_apply, h.sub_eq,
      inner_tangentVec_vecMulVec_col h.orth h.perp (Ut - Uh) (tail Ut) H1 vh j]
    linarith [h.step1 vh j]
  · rw [pgFunctional_apply, LinearMap.sub_apply, LinearMap.add_apply, h.sub_eq,
      inner_tangentVec_vecMulVec_perp h.orth h.perp (Ut - Uh) (tail Ut) H1 z j]
    linarith [h.step2 z j]

/-- **Lemma 4.2 of arXiv 2407.01404.** For a deterministic operator `W` (a matrix acting on the
physical factor), `E[W uⁿ⁺¹ Yⱼⁿ] = W Ũⱼ` for `j = 0, …, R` (stated as an identity of vectors,
which gives (51) after pairing with `vₕ`). -/
theorem lemma_4_2 (h : IsPGDLRStep H1 A1 A2 FH Δt un Uh Yh Ut dY un1) (W : Matrix m m ℝ)
    (j : Option k) : (W * un1) *ᵥ Yh.col j = W *ᵥ Ut.col j := by
  change ((W * un1) * Yh).col j = (W * Ut).col j
  have e : W * un1 * Yh = W * Ut := by
    rw [h.next', Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [h.orth, transpose_mul_eq_zero h.perp]
    simp
  rw [e]

/-- **Lemma 4.1 of arXiv 2407.01404.** For a deterministic operator `W`,
`(W uⁿ⁺¹) P⊥ z = W Ũ (Ỹ - Yⁿ)ᵀ z` with `Ỹ - Yⁿ = δỸ` (stated as an identity of vectors, which
gives (50) after pairing with `v`). -/
theorem lemma_4_1 (h : IsPGDLRStep H1 A1 A2 FH Δt un Uh Yh Ut dY un1) (W : Matrix m m ℝ)
    (z : n → ℝ) : (W * un1) *ᵥ perpProj Yh z = (W * tail Ut * dYᵀ) *ᵥ z := by
  rw [h.next', Matrix.mul_add, add_mulVec, ← Matrix.mul_assoc, ← mulVec_mulVec (M := W * Ut),
    transpose_mulVec_perpProj h.orth, mulVec_zero, zero_add, ← Matrix.mul_assoc,
    ← mulVec_mulVec (M := W * tail Ut), ← mulVec_mulVec (M := W * tail Ut), perpProj,
    mulVec_sub dYᵀ, mulVec_mulVec (M := dYᵀ) (N := Yh), transpose_mul_eq_zero h.perp,
    zero_mulVec, sub_zero]

end IsPGDLRStep

end Algorithm1

/-! ### The SUPG setting (§2.2.1) in a finite model, and Lemma 2.1 -/

section SUPG

/-- **Finite model of the SUPG setting** of §2.2.1 of arXiv 2407.01404. The space
`L²(D) ⊗ L²_µ̂(Ω̂)` is replaced by functions on a finite set `P` of weighted points `(x, ω)`
(`w` = quadrature weight times sample weight `mᵢ`), grouped into the cells `K ∈ T_h` by `cell`.
The discrete trial space is any real vector space `E` with linear maps to point values `u`,
gradients `∇u` and pure second derivatives `∂ᵢ∂ᵢu`; the coefficients `ε`, `b`, `div b`, `c` and
the SUPG parameters `δ_K` are data. All inner products `(·,·)`, `(·,·)_K` are the weighted sums
over the points (over the points of `K`). -/
structure SUPGModel (E : Type*) [AddCommGroup E] [Module ℝ E] (P ι : Type*) (d : ℕ) where
  /-- weights of the points -/
  w : P → ℝ
  /-- the cell `K ∈ T_h` that contains a point -/
  cell : P → ι
  /-- point values `u(x, ω)` -/
  val : E →ₗ[ℝ] P → ℝ
  /-- the gradient `∇u(x, ω)` -/
  grad : E →ₗ[ℝ] P → Fin d → ℝ
  /-- the pure second derivatives `∂ᵢ∂ᵢu(x, ω)` (cellwise) -/
  hess : E →ₗ[ℝ] P → Fin d → ℝ
  /-- the diffusion coefficient `ε` -/
  eps : P → ℝ
  /-- the advection field `b` -/
  b : P → Fin d → ℝ
  /-- the divergence `div b` -/
  divb : P → ℝ
  /-- the reaction coefficient `c` -/
  c : P → ℝ
  /-- the SUPG parameters `δ_K` -/
  δ : ι → ℝ

namespace SUPGModel

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {P ι : Type*} {d : ℕ}
  (S : SUPGModel E P ι d)

/-- `(f, g) = (f, g)_{X, L²_µ̂}`. -/
def ip [Fintype P] (f g : P → ℝ) : ℝ := ∑ p, S.w p * f p * g p

/-- `(f, g)_{K, L²_µ̂}`. -/
def cellIp [Fintype P] [DecidableEq ι] (K : ι) (f g : P → ℝ) : ℝ :=
  ∑ p with S.cell p = K, S.w p * f p * g p

/-- `b · ∇u`. -/
def adv (u : E) (p : P) : ℝ := ∑ i, S.b p i * S.grad u p i

/-- `Δu = ∑ᵢ ∂ᵢ∂ᵢ u`. -/
def lap (u : E) (p : P) : ℝ := ∑ i, S.hess u p i

/-- `|∇u(x, ω)|²`. -/
def gradSqAt (u : E) (p : P) : ℝ := ∑ i, S.grad u p i ^ 2

/-- `‖∇u‖²`. -/
def gradSq [Fintype P] (u : E) : ℝ := ∑ p, S.w p * S.gradSqAt u p

/-- The diffusion form `(ε ∇u, ∇v)`. -/
def diff [Fintype P] (u v : E) : ℝ :=
  ∑ p, S.w p * (S.eps p * ∑ i, S.grad u p i * S.grad v p i)

/-- `∑_K δ_K (f, g)_K`. -/
def stab [Fintype P] [Fintype ι] [DecidableEq ι] (f g : P → ℝ) : ℝ :=
  ∑ K, S.δ K * S.cellIp K f g

/-- **The SUPG bilinear form (15)**:
`(ε∇u, ∇v) + (b·∇u, v) + (cu, v) + ∑_K δ_K (-εΔu + b·∇u + cu, b·∇v)_K`. -/
def aSUPG [Fintype P] [Fintype ι] [DecidableEq ι] (u v : E) : ℝ :=
  S.diff u v + S.ip (S.adv u) (S.val v) + S.ip (fun p => S.c p * S.val u p) (S.val v) +
    S.stab (fun p => -(S.eps p * S.lap u p) + S.adv u p + S.c p * S.val u p) (S.adv v)

/-- `µ̃ = c - |c|/2 - (div b)/2`, eq. (11). -/
def muTilde (p : P) : ℝ := S.c p - |S.c p| / 2 - S.divb p / 2

/-- `ν = -min (inf µ̃, 0)`, eq. (12) (infimum over the points of the model). -/
def nu : ℝ := max (-(⨅ p, S.muTilde p)) 0

/-- `µ₀ = inf µ`, `µ = µ̃ + ν`, eq. (12). -/
def mu0 : ℝ := ⨅ p, (S.muTilde p + S.nu)

/-- `‖u‖² = (u, u)`. -/
def normSq [Fintype P] (u : E) : ℝ := S.ip (S.val u) (S.val u)

/-- **The SUPG norm (21)** (squared), with `µ = µ̃ + ν`:
`ε̂ ‖∇u‖² + ∑_K δ_K ‖b·∇u‖²_K + ‖µ^{1/2} u‖²`. -/
def supgNormSq [Fintype P] [Fintype ι] [DecidableEq ι] (εh ν : ℝ) (u : E) : ℝ :=
  εh * S.gradSq u + S.stab (S.adv u) (S.adv u) +
    S.ip (fun p => (S.muTilde p + ν) * S.val u p) (S.val u)

/-- Standing hypotheses of the finite model: nonnegative weights; the integration-by-parts identity
`(b·∇u, u) = -½ (div b u, u)` (Green's formula with `u = 0` on `∂D`); positive cell diameters
`h_K`; and the cellwise inverse inequality `h_K ‖∂ᵢ∂ᵢu‖_K ≤ C_I ‖∂ᵢu‖_K`, the local form of (5)
applied to `∂ᵢu` in the proof of Lemma 2.1. In the paper these are properties of `H¹₀(D)` and of
the finite element space, not hypotheses. -/
structure IsFE [Fintype P] [DecidableEq ι] (CI : ℝ) (h : ι → ℝ) : Prop where
  w_nonneg : ∀ p, 0 ≤ S.w p
  ibp : ∀ u, S.ip (S.adv u) (S.val u) = -S.ip (fun p => S.divb p * S.val u p) (S.val u) / 2
  h_pos : ∀ K, 0 < h K
  inverse : ∀ u K i, h K ^ 2 * S.cellIp K (fun p => S.hess u p i) (fun p => S.hess u p i) ≤
    CI ^ 2 * S.cellIp K (fun p => S.grad u p i) (fun p => S.grad u p i)

/-- **Condition (19)** on the SUPG parameters:
`0 ≤ δ_K ≤ min (1 / (2 |||c|||_K), h_K² / (2 d C_I² C_E² ε̂))`. The first bound is written
pointwise, `2 δ_K |c(x, ω)| ≤ 1` on `K`, which is equivalent and avoids `1/0` when `c = 0` on
`K`; the second is multiplied out. -/
structure IsSUPGParam (εh CE CI : ℝ) (h : ι → ℝ) : Prop where
  nonneg : ∀ K, 0 ≤ S.δ K
  c_bound : ∀ p, 2 * S.δ (S.cell p) * |S.c p| ≤ 1
  h_bound : ∀ K, 2 * d * CI ^ 2 * CE ^ 2 * εh * S.δ K ≤ h K ^ 2

/-- The stabilisation sum as a sum over points. -/
theorem stab_eq [Fintype P] [Fintype ι] [DecidableEq ι] (f g : P → ℝ) :
    S.stab f g = ∑ p, S.δ (S.cell p) * S.w p * f p * g p := by
  rw [stab, ← Finset.sum_fiberwise Finset.univ S.cell
    (fun p => S.δ (S.cell p) * S.w p * f p * g p)]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [cellIp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.1 hp).2]
  ring

theorem sum_cellIp [Fintype P] [Fintype ι] [DecidableEq ι] (f g : P → ℝ) :
    ∑ K, S.cellIp K f g = S.ip f g :=
  Finset.sum_fiberwise Finset.univ S.cell _

theorem diff_self [Fintype P] (u : E) : S.diff u u = ∑ p, S.w p * (S.eps p * S.gradSqAt u p) := by
  simp only [diff, gradSqAt, sq]

variable {S}

theorem ip_self_nonneg [Fintype P] (hw : ∀ p, 0 ≤ S.w p) (f : P → ℝ) : 0 ≤ S.ip f f :=
  Finset.sum_nonneg fun p _ => by rw [mul_assoc]; exact mul_nonneg (hw p) (mul_self_nonneg _)

theorem cellIp_self_nonneg [Fintype P] [DecidableEq ι] (hw : ∀ p, 0 ≤ S.w p) (K : ι)
    (f : P → ℝ) : 0 ≤ S.cellIp K f f :=
  Finset.sum_nonneg fun p _ => by rw [mul_assoc]; exact mul_nonneg (hw p) (mul_self_nonneg _)

theorem stab_self_nonneg [Fintype P] [Fintype ι] [DecidableEq ι] (hw : ∀ p, 0 ≤ S.w p)
    (hδ : ∀ K, 0 ≤ S.δ K) (f : P → ℝ) : 0 ≤ S.stab f f :=
  Finset.sum_nonneg fun K _ => mul_nonneg (hδ K) (cellIp_self_nonneg hw K f)

theorem gradSq_nonneg [Fintype P] (hw : ∀ p, 0 ≤ S.w p) (u : E) : 0 ≤ S.gradSq u :=
  Finset.sum_nonneg fun p _ =>
    mul_nonneg (hw p) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem weighted_ip_nonneg [Fintype P] (hw : ∀ p, 0 ≤ S.w p) {μ : P → ℝ} (hμ : ∀ p, 0 ≤ μ p)
    (f : P → ℝ) : 0 ≤ S.ip (fun p => μ p * f p) f :=
  Finset.sum_nonneg fun p _ => by
    have : S.w p * (μ p * f p) * f p = S.w p * μ p * (f p * f p) := by ring
    rw [this]
    exact mul_nonneg (mul_nonneg (hw p) (hμ p)) (mul_self_nonneg _)

/-- The three parts of the SUPG norm are nonnegative and bounded by it. -/
theorem supgNormSq_parts [Fintype P] [Fintype ι] [DecidableEq ι] (hw : ∀ p, 0 ≤ S.w p)
    (hδ : ∀ K, 0 ≤ S.δ K) {εh ν : ℝ} (hεh : 0 ≤ εh) (hμ : ∀ p, 0 ≤ S.muTilde p + ν) (u : E) :
    0 ≤ S.stab (S.adv u) (S.adv u) ∧
      0 ≤ S.ip (fun p => (S.muTilde p + ν) * S.val u p) (S.val u) ∧
      S.stab (S.adv u) (S.adv u) + S.ip (fun p => (S.muTilde p + ν) * S.val u p) (S.val u) ≤
        S.supgNormSq εh ν u := by
  refine ⟨stab_self_nonneg hw hδ _, weighted_ip_nonneg hw hμ _, ?_⟩
  have := mul_nonneg hεh (gradSq_nonneg hw u)
  rw [supgNormSq]
  linarith

/-- The cellwise inverse-inequality estimate behind Lemma 2.1 and Theorem 4.2, for a coefficient
`e` with `|e| ≤ C`: if `d C_I² C² δ_K ≤ κ h_K²` on every cell, then
`∑_K δ_K ‖e Δu‖²_K ≤ κ ‖∇u‖²`. It combines `‖Δu‖²_K ≤ d ∑ᵢ ‖∂ᵢ∂ᵢu‖²_K` (Cauchy-Schwarz) with the
cellwise inverse inequality. -/
theorem stab_coefLap_le [Fintype P] [Fintype ι] [DecidableEq ι] {CI C κ : ℝ} {h : ι → ℝ}
    (hS : S.IsFE CI h) {e : P → ℝ} (he : ∀ p, |e p| ≤ C) (hδ : ∀ K, 0 ≤ S.δ K)
    (hκ : ∀ K, d * CI ^ 2 * C ^ 2 * S.δ K ≤ κ * h K ^ 2) (u : E) :
    S.stab (fun p => e p * S.lap u p) (fun p => e p * S.lap u p) ≤ κ * S.gradSq u := by
  have hG : S.gradSq u =
      ∑ K, ∑ i, S.cellIp K (fun p => S.grad u p i) (fun p => S.grad u p i) := by
    rw [Finset.sum_comm]
    simp only [sum_cellIp, ip, gradSq, gradSqAt, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
  rw [stab, hG, Finset.mul_sum]
  refine Finset.sum_le_sum fun K _ => ?_
  set SL := S.cellIp K (fun p => e p * S.lap u p) (fun p => e p * S.lap u p)
  set SH := ∑ i, S.cellIp K (fun p => S.hess u p i) (fun p => S.hess u p i)
  set SG := ∑ i, S.cellIp K (fun p => S.grad u p i) (fun p => S.grad u p i)
  have hA : SL ≤ C ^ 2 * d * SH := by
    have e' : SH = ∑ p with S.cell p = K, S.w p * ∑ i, S.hess u p i ^ 2 := by
      simp only [SH, cellIp, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e', Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have hε2 : e p ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (he p) 2
    have hL2 : S.lap u p ^ 2 ≤ d * ∑ i, S.hess u p i ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => S.hess u p i)
      simpa [lap] using this
    have hw := hS.w_nonneg p
    calc S.w p * (e p * S.lap u p) * (e p * S.lap u p)
        = S.w p * (e p ^ 2 * S.lap u p ^ 2) := by ring
      _ ≤ S.w p * (C ^ 2 * (d * ∑ i, S.hess u p i ^ 2)) := by
          gcongr
      _ = C ^ 2 * d * (S.w p * ∑ i, S.hess u p i ^ 2) := by ring
  have hB : h K ^ 2 * SH ≤ CI ^ 2 * SG := by
    simp only [SH, SG, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hS.inverse u K i
  have hC := hκ K
  have hδK := hδ K
  have hSG : 0 ≤ SG := Finset.sum_nonneg fun _ _ => cellIp_self_nonneg hS.w_nonneg K _
  have hh := hS.h_pos K
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have key : h K ^ 2 * (S.δ K * SL) ≤ h K ^ 2 * (κ * SG) := by
    calc h K ^ 2 * (S.δ K * SL)
        ≤ h K ^ 2 * (S.δ K * (C ^ 2 * d * SH)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hA hδK
      _ = S.δ K * C ^ 2 * d * (h K ^ 2 * SH) := by ring
      _ ≤ S.δ K * C ^ 2 * d * (CI ^ 2 * SG) := by
          apply mul_le_mul_of_nonneg_left hB
          have : 0 ≤ S.δ K * C ^ 2 := mul_nonneg hδK (sq_nonneg _)
          positivity
      _ = (d * CI ^ 2 * C ^ 2 * S.δ K) * SG := by ring
      _ ≤ κ * h K ^ 2 * SG := mul_le_mul_of_nonneg_right hC hSG
      _ = h K ^ 2 * (κ * SG) := by ring
  exact le_of_mul_le_mul_left key (by positivity)

/-- The cellwise inverse-inequality step of the proof of Lemma 2.1 (appendix, second display):
`∑_K δ_K ‖ε Δu‖²_K ≤ ε̂/2 ‖∇u‖²`, from `ε ≤ C_E ε̂` and the second bound of (19). -/
theorem stab_epsLap_le [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI : ℝ} {h : ι → ℝ}
    (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) (u : E) :
    S.stab (fun p => S.eps p * S.lap u p) (fun p => S.eps p * S.lap u p) ≤
      εh / 2 * S.gradSq u := by
  refine stab_coefLap_le hS (C := CE * εh) (fun p => ?_) h19.nonneg (fun K => ?_) u
  · rw [abs_of_nonneg (by linarith [(h10 p).1])]
    exact (h10 p).2
  · have := mul_le_mul_of_nonneg_left (h19.h_bound K) (by positivity : (0 : ℝ) ≤ εh / 2)
    nlinarith [this]

/-- The pointwise inequality behind Lemma 2.1 (Young's inequality twice and the first bound
of (19)). -/
theorem coercivity_pt {w ε εh G δ L g c x dv ν : ℝ} (hw : 0 ≤ w) (hε : εh ≤ ε) (hG : 0 ≤ G)
    (hδ : 0 ≤ δ) (hc : 2 * δ * |c| ≤ 1) (hμ : 0 ≤ c - |c| / 2 - dv / 2 + ν) :
    0 ≤ (w * (ε * G) - w * dv * x * x / 2 + w * (c * x) * x + δ * w * (-L + g + c * x) * g) -
      ((εh * (w * G) + δ * w * g * g + w * ((c - |c| / 2 - dv / 2 + ν) * x) * x) / 2 -
        ν * (w * x * x)) - (εh / 2 * (w * G) - δ * w * L * L) := by
  have key : (w * (ε * G) - w * dv * x * x / 2 + w * (c * x) * x +
      δ * w * (-L + g + c * x) * g) -
      ((εh * (w * G) + δ * w * g * g + w * ((c - |c| / 2 - dv / 2 + ν) * x) * x) / 2 -
        ν * (w * x * x)) - (εh / 2 * (w * G) - δ * w * L * L) =
      w * ((ε - εh) * G + (c - |c| / 2 - dv / 2 + ν) * x ^ 2 / 2 + δ * (L - g / 2) ^ 2 +
        (|c| * x ^ 2 / 2 + δ * g ^ 2 / 4 + δ * c * x * g)) := by ring
  rw [key]
  apply mul_nonneg hw
  have h1 : 0 ≤ |c| * x ^ 2 / 2 + δ * g ^ 2 / 4 + δ * c * x * g := by
    rcases le_or_gt 0 c with hc0 | hc0
    · rw [abs_of_nonneg hc0] at hc ⊢
      nlinarith [mul_nonneg hc0 (sq_nonneg (x + δ * g)),
        mul_nonneg (mul_nonneg hδ (sq_nonneg g)) (by linarith : (0 : ℝ) ≤ 1 - 2 * δ * c)]
    · rw [abs_of_neg hc0] at hc ⊢
      nlinarith [mul_nonneg (neg_nonneg.2 hc0.le) (sq_nonneg (x - δ * g)),
        mul_nonneg (mul_nonneg hδ (sq_nonneg g)) (by linarith : (0 : ℝ) ≤ 1 - 2 * δ * (-c))]
  have h2 : 0 ≤ (ε - εh) * G := mul_nonneg (by linarith) hG
  have h3 : 0 ≤ (c - |c| / 2 - dv / 2 + ν) * x ^ 2 / 2 := by positivity
  have h4 : 0 ≤ δ * (L - g / 2) ^ 2 := mul_nonneg hδ (sq_nonneg _)
  linarith

/-- **Lemma 2.1 of arXiv 2407.01404** (weak coercivity of the SUPG form), in the finite model:
under (10) and (19), `a_SUPG(u, u) ≥ ½ ‖u‖²_SUPG - ν ‖u‖²`.

It holds for every `ν` with `µ = µ̃ + ν ≥ 0`, in particular for the paper's `ν` of (12)
(`lemma_2_1'`). The proof is the paper's (appendix): Young's inequality on the two cross terms,
(19), the cellwise inverse inequality and the identity (80). Differences: the finite model (see
`SUPGModel`); the lemma is **conditional on** integration by parts and the cellwise inverse
inequality (hypotheses of `IsFE`), which the paper takes from `H¹₀(D)` and the finite element
space; and `δ_K ≥ 0`, implicit in the paper, is part of `IsSUPGParam`. -/
theorem lemma_2_1 [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI : ℝ} {h : ι → ℝ}
    (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) {ν : ℝ} (hμ : ∀ p, 0 ≤ S.muTilde p + ν) (u : E) :
    S.supgNormSq εh ν u / 2 - ν * S.normSq u ≤ S.aSUPG u u := by
  have hL := stab_epsLap_le hS hεh h10 h19 u
  obtain ⟨A, hAd⟩ : ∃ A : P → ℝ, A = fun p => S.w p * (S.eps p * S.gradSqAt u p) -
      S.w p * S.divb p * S.val u p * S.val u p / 2 + S.w p * (S.c p * S.val u p) * S.val u p +
      S.δ (S.cell p) * S.w p * (-(S.eps p * S.lap u p) + S.adv u p + S.c p * S.val u p) *
        S.adv u p := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : P → ℝ, T = fun p => (εh * (S.w p * S.gradSqAt u p) +
      S.δ (S.cell p) * S.w p * S.adv u p * S.adv u p +
      S.w p * ((S.muTilde p + ν) * S.val u p) * S.val u p) / 2 -
      ν * (S.w p * S.val u p * S.val u p) := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R : P → ℝ, R = fun p => εh / 2 * (S.w p * S.gradSqAt u p) -
      S.δ (S.cell p) * S.w p * (S.eps p * S.lap u p) * (S.eps p * S.lap u p) := ⟨_, rfl⟩
  have hA : S.aSUPG u u = ∑ p, A p := by
    rw [aSUPG, diff_self, hS.ibp, stab_eq, hAd]
    simp only [ip]
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hT : S.supgNormSq εh ν u / 2 - ν * S.normSq u = ∑ p, T p := by
    rw [supgNormSq, normSq, gradSq, stab_eq, hTd]
    simp only [ip]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_div, ← Finset.sum_sub_distrib]
  have hR : εh / 2 * S.gradSq u -
      S.stab (fun p => S.eps p * S.lap u p) (fun p => S.eps p * S.lap u p) = ∑ p, R p := by
    rw [gradSq, stab_eq, hRd, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hQ : 0 ≤ ∑ p, (A p - T p - R p) := by
    refine Finset.sum_nonneg fun p _ => ?_
    rw [hAd, hTd, hRd]
    exact coercivity_pt (hS.w_nonneg p) (h10 p).1
      (Finset.sum_nonneg fun i _ => sq_nonneg _) (h19.nonneg _) (h19.c_bound p) (hμ p)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← hA, ← hT, ← hR] at hQ
  linarith

/-- `µ = µ̃ + ν ≥ 0` for the paper's `ν`, eq. (12). -/
theorem muTilde_add_nu_nonneg [Finite P] (S : SUPGModel E P ι d) (p : P) :
    0 ≤ S.muTilde p + S.nu := by
  have h1 : (⨅ q, S.muTilde q) ≤ S.muTilde p := ciInf_le (Finite.bddBelow_range _) p
  have h2 : -(⨅ q, S.muTilde q) ≤ S.nu := le_max_left _ _
  linarith

theorem mu0_le [Finite P] (S : SUPGModel E P ι d) (p : P) : S.mu0 ≤ S.muTilde p + S.nu :=
  ciInf_le (Finite.bddBelow_range _) p

theorem nu_nonneg (S : SUPGModel E P ι d) : 0 ≤ S.nu := le_max_right _ _

/-- If `µ₀ > 0` then `ν = 0` (used in case (i) of Theorem 4.1: "note that `ν = 0`"). -/
theorem nu_eq_zero_of_mu0_pos [Finite P] (S : SUPGModel E P ι d) (h : 0 < S.mu0) :
    S.nu = 0 := by
  rcases isEmpty_or_nonempty P with hP | hP
  · simp [nu]
  · obtain ⟨p0, hp0⟩ := Finite.exists_min S.muTilde
    have hinf : (⨅ p, S.muTilde p) = S.muTilde p0 :=
      le_antisymm (ciInf_le (Finite.bddBelow_range _) p0) (le_ciInf hp0)
    have h1 := S.mu0_le p0
    rw [nu, hinf] at h1 ⊢
    rcases le_total (S.muTilde p0) 0 with h2 | h2
    · rw [max_eq_left (by linarith)] at h1
      linarith
    · exact max_eq_right (by linarith)

/-- **Lemma 2.1 of arXiv 2407.01404** with the paper's `ν` of (12). -/
theorem lemma_2_1' [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI : ℝ} {h : ι → ℝ}
    (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) (u : E) :
    S.supgNormSq εh S.nu u / 2 - S.nu * S.normSq u ≤ S.aSUPG u u :=
  lemma_2_1 hS hεh h10 h19 (muTilde_add_nu_nonneg S) u

/-! ### Norm stability of the implicit Euler SUPG-DLR scheme (Theorem 4.1) -/

variable (S) in
/-- `(w, H v)` for the SUPG test operator `H v = v + ∑_K δ_K χ_K b·∇v` of (17). -/
def pgPair [Fintype P] [Fintype ι] [DecidableEq ι] (w v : E) : ℝ :=
  S.ip (S.val w) (S.val v) + S.stab (S.val w) (S.adv v)

variable (S) in
/-- `F(H v) = (f, H v) = (f, v) + ∑_K δ_K (f, b·∇v)_K` for a load `f ∈ L²_µ̂(Ω̂, X)`. -/
def load [Fintype P] [Fintype ι] [DecidableEq ι] (f : P → ℝ) (v : E) : ℝ :=
  S.ip f (S.val v) + S.stab f (S.adv v)

/-- One step of the energy argument of Theorem 4.1, eqs. (58)-(62): if
`Δt⁻¹ (u₁ - u₀, H u₁) + a_SUPG(u₁, u₁) = L` (the variational formulation (49) tested with
`v = u₁`, where `L = F(H u₁)`), then
`‖u₁‖² - ‖u₀‖² + Δt ‖u₁‖²_SUPG - 2Δt ν ‖u₁‖² - Δt/4 ∑_K δ_K ‖b·∇u₁‖²_K ≤ 2Δt L`. -/
theorem energy_step [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI : ℝ} {h : ι → ℝ}
    (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) {ν : ℝ} (hμ : ∀ p, 0 ≤ S.muTilde p + ν) {Δt : ℝ}
    (hΔt : 0 < Δt) (h55 : ∀ K, S.δ K ≤ Δt / 4) {u0 u1 : E} {L : ℝ}
    (hstep : Δt⁻¹ * S.pgPair (u1 - u0) u1 + S.aSUPG u1 u1 = L) :
    S.normSq u1 - S.normSq u0 + Δt * S.supgNormSq εh ν u1 - 2 * Δt * ν * S.normSq u1 -
      Δt / 4 * S.stab (S.adv u1) (S.adv u1) ≤ 2 * Δt * L := by
  have hP : S.pgPair (u1 - u0) u1 = S.ip (S.val u1 - S.val u0) (S.val u1) +
      S.stab (S.val u1 - S.val u0) (S.adv u1) := by rw [pgPair, map_sub]
  have h1 : 2 * S.ip (S.val u1 - S.val u0) (S.val u1) = S.normSq u1 - S.normSq u0 +
      S.ip (S.val u1 - S.val u0) (S.val u1 - S.val u0) := by
    simp only [normSq, ip, Finset.mul_sum, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h2 : -S.ip (S.val u1 - S.val u0) (S.val u1 - S.val u0) -
      Δt / 4 * S.stab (S.adv u1) (S.adv u1) ≤ 2 * S.stab (S.val u1 - S.val u0) (S.adv u1) := by
    rw [stab_eq, stab_eq]
    simp only [ip, Finset.mul_sum, Pi.sub_apply]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    have hw := hS.w_nonneg p
    have hδ := h19.nonneg (S.cell p)
    have hδ' := h55 (S.cell p)
    set D := S.val u1 p - S.val u0 p
    set g := S.adv u1 p
    nlinarith [mul_nonneg hw (sq_nonneg (D + S.δ (S.cell p) * g)),
      mul_nonneg hw (mul_nonneg (mul_nonneg hδ (by linarith : 0 ≤ Δt / 4 - S.δ (S.cell p)))
        (sq_nonneg g))]
  have h3 := lemma_2_1 hS hεh h10 h19 hμ u1
  have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Δt)
  have hstep' : 2 * S.pgPair (u1 - u0) u1 + 2 * Δt * S.aSUPG u1 u1 = 2 * Δt * L := by
    rw [← hstep]
    field_simp
  linarith

/-- The load term of (65): `∑_K δ_K (f, b·∇v)_K ≤ 2 δ̄ ‖f‖² + ⅛ ∑_K δ_K ‖b·∇v‖²_K` for every upper
bound `δ̄` of the `δ_K`. -/
theorem stab_load_le [Fintype P] [Fintype ι] [DecidableEq ι] (hw : ∀ p, 0 ≤ S.w p)
    (hδ : ∀ K, 0 ≤ S.δ K) {δbar : ℝ} (hδbar : ∀ K, S.δ K ≤ δbar) (f : P → ℝ) (v : E) :
    S.stab f (S.adv v) ≤ 2 * δbar * S.ip f f + S.stab (S.adv v) (S.adv v) / 8 := by
  rw [stab_eq, stab_eq, ip, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 := hw p
  have h2 := hδ (S.cell p)
  have h3 := hδbar (S.cell p)
  nlinarith [mul_nonneg (mul_nonneg h1 h2) (sq_nonneg (f p - S.adv v p / 4)),
    mul_nonneg (mul_nonneg h1 (by linarith : 0 ≤ δbar - S.δ (S.cell p))) (sq_nonneg (f p))]

/-- Eq. (63): `(f, v) ≤ ‖f‖² / µ₀ + ¼ ‖µ^{1/2} v‖²` when `µ ≥ µ₀ > 0`. -/
theorem ip_load_le_mu [Fintype P] (hw : ∀ p, 0 ≤ S.w p) {μ0 ν : ℝ} (hμ0 : 0 < μ0)
    (hμ : ∀ p, μ0 ≤ S.muTilde p + ν) (f : P → ℝ) (v : E) :
    S.ip f (S.val v) ≤
      S.ip f f / μ0 + S.ip (fun p => (S.muTilde p + ν) * S.val v p) (S.val v) / 4 := by
  simp only [ip]
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 := hw p
  have h2 := hμ p
  have key : f p * S.val v p ≤ f p * f p / μ0 + μ0 * (S.val v p * S.val v p) / 4 := by
    rw [div_add_div _ _ hμ0.ne' (by norm_num : (4 : ℝ) ≠ 0), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * f p - μ0 * S.val v p)]
  have key2 : μ0 * (S.val v p * S.val v p) ≤ (S.muTilde p + ν) * (S.val v p * S.val v p) :=
    mul_le_mul_of_nonneg_right h2 (mul_self_nonneg _)
  have := mul_le_mul_of_nonneg_left key h1
  have := mul_le_mul_of_nonneg_left key2 h1
  have e1 : S.w p * f p * S.val v p = S.w p * (f p * S.val v p) := by ring
  have e2 : S.w p * f p * f p / μ0 + S.w p * ((S.muTilde p + ν) * S.val v p) * S.val v p / 4 =
      S.w p * (f p * f p / μ0) + S.w p * ((S.muTilde p + ν) * (S.val v p * S.val v p)) / 4 := by
    ring
  rw [e1, e2]
  nlinarith

/-- Eq. (64): `(f, v) ≤ ½ ‖f‖² + ½ ‖v‖²`. -/
theorem ip_load_le_half [Fintype P] (hw : ∀ p, 0 ≤ S.w p) (f : P → ℝ) (v : E) :
    S.ip f (S.val v) ≤ S.ip f f / 2 + S.normSq v / 2 := by
  simp only [normSq, ip]
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  nlinarith [mul_nonneg (hw p) (sq_nonneg (f p - S.val v p))]

theorem load_zero [Fintype P] [Fintype ι] [DecidableEq ι] (v : E) : S.load 0 v = 0 := by
  simp [load, ip, stab, cellIp]

/-- Summation of a telescoping one-step bound. -/
theorem sum_telescope {a s g : ℕ → ℝ} {N : ℕ} (h : ∀ n < N, a (n + 1) - a n + s n ≤ g n) :
    a N + ∑ n ∈ range N, s n ≤ a 0 + ∑ n ∈ range N, g n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := ih fun n hn => h n (by omega)
    have h2 := h N (by omega)
    linarith

/-- **Theorem 4.1 (i) of arXiv 2407.01404**, energy form: if `µ₀ > 0`, (10), (19) and (55) hold,
`δ̄ ≥ max_K δ_K`, and the iterates satisfy (49) tested with `v = uⁿ⁺¹`, then
`‖u^N‖² + Δt/2 ∑ₙ ‖uⁿ⁺¹‖²_SUPG ≤ ‖u⁰‖² + Δt (2/µ₀ + 4δ̄) ∑ₙ ‖fⁿ‖²` (`C₁ = 1/2`,
`C₂ = 2/µ₀ + 4δ`). The load may depend on the step (`fⁿ`). See `thm_4_1_i` for the statement
about Algorithm 1. -/
theorem thm_4_1_i_of_tested [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) (hμ0 : 0 < S.mu0) {δbar : ℝ} (hδbar : ∀ K, S.δ K ≤ δbar)
    {Δt : ℝ} (hΔt : 0 < Δt) (h55 : ∀ K, S.δ K ≤ Δt / 4) {u : ℕ → E} {f : ℕ → P → ℝ} {N : ℕ}
    (hstep : ∀ n < N, Δt⁻¹ * S.pgPair (u (n + 1) - u n) (u (n + 1)) +
      S.aSUPG (u (n + 1)) (u (n + 1)) = S.load (f n) (u (n + 1))) :
    S.normSq (u N) + Δt * (1 / 2) * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) ≤
      S.normSq (u 0) + Δt * (2 / S.mu0 + 4 * δbar) * ∑ n ∈ range N, S.ip (f n) (f n) := by
  have hν := S.nu_eq_zero_of_mu0_pos hμ0
  have hμ := muTilde_add_nu_nonneg S
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_telescope (a := fun n => S.normSq (u n)) fun n hn => ?_
  have e := energy_step hS hεh h10 h19 hμ hΔt h55 (hstep n hn)
  have hl1 := ip_load_le_mu hS.w_nonneg hμ0 (S.mu0_le) (f n) (u (n + 1))
  have hl2 := stab_load_le hS.w_nonneg h19.nonneg hδbar (f n) (u (n + 1))
  obtain ⟨hA, hM, hAM⟩ := supgNormSq_parts hS.w_nonneg h19.nonneg hεh.le hμ (u (n + 1))
  simp only [load] at e
  have h2Δt : (0 : ℝ) ≤ 2 * Δt := by positivity
  have hl1' := mul_le_mul_of_nonneg_left hl1 h2Δt
  have hl2' := mul_le_mul_of_nonneg_left hl2 h2Δt
  have hΔt2 := mul_le_mul_of_nonneg_left hAM hΔt.le
  have hνz : 2 * Δt * S.nu * S.normSq (u (n + 1)) = 0 := by rw [hν]; ring
  have hrhs : Δt * (2 / S.mu0 + 4 * δbar) * S.ip (f n) (f n) =
      2 * Δt * (S.ip (f n) (f n) / S.mu0) + 4 * Δt * δbar * S.ip (f n) (f n) := by ring
  rw [hrhs]
  linarith

/-- **Theorem 4.1 (ii) of arXiv 2407.01404, corrected**, energy form: if `ν = 0` and `f = 0`,
then `‖u^N‖² + ¾ Δt ∑ₙ ‖uⁿ⁺¹‖²_SUPG ≤ ‖u⁰‖²`. The paper assumes `µ₀ = 0` instead of `ν = 0`; its
proof uses `ν = 0`, and with `µ₀ = 0`, `ν > 0` the claim is false
(`thm_4_1_ii_as_printed_false`). Here `µ₀` is arbitrary. -/
theorem thm_4_1_ii_of_tested [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) (hν : S.nu = 0) {Δt : ℝ} (hΔt : 0 < Δt)
    (h55 : ∀ K, S.δ K ≤ Δt / 4) {u : ℕ → E} {N : ℕ}
    (hstep : ∀ n < N, Δt⁻¹ * S.pgPair (u (n + 1) - u n) (u (n + 1)) +
      S.aSUPG (u (n + 1)) (u (n + 1)) = S.load 0 (u (n + 1))) :
    S.normSq (u N) + Δt * (3 / 4) * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) ≤
      S.normSq (u 0) := by
  have hμ := muTilde_add_nu_nonneg S
  rw [Finset.mul_sum]
  have := sum_telescope (a := fun n => S.normSq (u n))
    (s := fun n => Δt * (3 / 4) * S.supgNormSq εh S.nu (u (n + 1))) (g := fun _ => 0)
    (N := N) fun n hn => by
      have e := energy_step hS hεh h10 h19 hμ hΔt h55 (hstep n hn)
      obtain ⟨hA, hM, hAM⟩ := supgNormSq_parts hS.w_nonneg h19.nonneg hεh.le hμ (u (n + 1))
      rw [load_zero] at e
      have hνz : 2 * Δt * S.nu * S.normSq (u (n + 1)) = 0 := by rw [hν]; ring
      have hAs := mul_le_mul_of_nonneg_left (by linarith : S.stab (S.adv (u (n + 1)))
        (S.adv (u (n + 1))) ≤ S.supgNormSq εh S.nu (u (n + 1))) hΔt.le
      linarith
  simpa using this

/-- The implicit discrete Grönwall lemma used for case (iii) of Theorems 4.1 and 4.2: if
`(1 - Δtγ) aₙ₊₁ - aₙ + sₙ₊₁ ≤ C Δt φₙ` with `0 ≤ Δtγ < 1`, `C ≥ 1` and `a₀, s, φ ≥ 0`, then
`a_N + ∑ₙ sₙ₊₁ ≤ C (1 - Δtγ)^{-N} (a₀ + Δt ∑ₙ φₙ)`. The proof applies the core
`LeanDLRA.discrete_gronwall_le` to `eₙ = aₙ + ∑_{k<n} sₖ₊₁`. -/
theorem gronwall_implicit {a s φ : ℕ → ℝ} {N : ℕ} {γ Δt C : ℝ} (hΔt : 0 ≤ Δt)
    (hγ0 : 0 ≤ Δt * γ) (hγ : Δt * γ < 1) (hC : 1 ≤ C) (ha0 : 0 ≤ a 0) (hs : ∀ n, 0 ≤ s n)
    (hφ : ∀ n, 0 ≤ φ n)
    (h : ∀ n < N, (1 - Δt * γ) * a (n + 1) - a n + s (n + 1) ≤ C * Δt * φ n) :
    a N + ∑ n ∈ range N, s (n + 1) ≤
      C * (1 - Δt * γ)⁻¹ ^ N * (a 0 + Δt * ∑ n ∈ range N, φ n) := by
  set q := (1 - Δt * γ)⁻¹ with hq
  have hpos : 0 < 1 - Δt * γ := by linarith
  have hq1 : 1 ≤ q := by
    rw [hq]
    exact one_le_inv₀ hpos |>.2 (by linarith)
  have hq0 : 0 ≤ q := by linarith
  set e : ℕ → ℝ := fun n => a n + ∑ k ∈ range n, s (k + 1) with he
  have hrec : ∀ n < N, e (n + 1) ≤ q * e n + q * (C * Δt * φ n) := by
    intro n hn
    have h1 := h n hn
    have hS0 : 0 ≤ ∑ k ∈ range n, s (k + 1) := Finset.sum_nonneg fun k _ => hs (k + 1)
    have ha : a (n + 1) ≤ q * (a n - s (n + 1) + C * Δt * φ n) := by
      rw [hq, ← div_eq_inv_mul, le_div_iff₀ hpos]
      linarith
    simp only [he, Finset.sum_range_succ]
    have h2 : (1 - q) * s (n + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hs _)
    have h3 : ∑ k ∈ range n, s (k + 1) ≤ q * ∑ k ∈ range n, s (k + 1) :=
      le_mul_of_one_le_left hS0 hq1
    nlinarith
  have hg := LeanDLRA.discrete_gronwall_le hq0 hrec N le_rfl
  have hbound : ∑ k ∈ range N, q ^ (N - 1 - k) * (q * (C * Δt * φ k)) ≤
      q ^ N * (C * Δt * ∑ k ∈ range N, φ k) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hpow : q ^ (N - 1 - k) * q ≤ q ^ N := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hq1 (by omega)
    have hφk : 0 ≤ C * Δt * φ k := mul_nonneg (mul_nonneg (by linarith) hΔt) (hφ k)
    calc q ^ (N - 1 - k) * (q * (C * Δt * φ k)) = q ^ (N - 1 - k) * q * (C * Δt * φ k) := by
          ring
      _ ≤ q ^ N * (C * Δt * φ k) := mul_le_mul_of_nonneg_right hpow hφk
  have he0 : e 0 = a 0 := by simp [he]
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  have hΦ : 0 ≤ ∑ k ∈ range N, φ k := Finset.sum_nonneg fun k _ => hφ k
  have h4 : q ^ N * a 0 ≤ C * q ^ N * a 0 := by nlinarith [mul_nonneg hqN ha0]
  rw [he0] at hg
  have hg' : a N + ∑ k ∈ range N, s (k + 1) ≤
      q ^ N * a 0 + ∑ k ∈ range N, q ^ (N - 1 - k) * (q * (C * Δt * φ k)) := hg
  nlinarith

/-- `(1 - x)^{-N} ≤ exp (N x / (1 - x))` for `0 ≤ x < 1`: with `x = Δt (1 + 2ν)` and `T = N Δt`
this is `exp ((1 + 2ν) T / (1 - Δt (1 + 2ν)))`, the constant that replaces the paper's
`C₃ = e^{(1 + 2ν) T}` in case (iii). -/
theorem inv_one_sub_pow_le_exp {x : ℝ} (hx : x < 1) (N : ℕ) :
    (1 - x)⁻¹ ^ N ≤ Real.exp (N * (x / (1 - x))) := by
  have hpos : 0 < 1 - x := by linarith
  have h1 : (1 - x)⁻¹ = x / (1 - x) + 1 := by field_simp; ring
  rw [Real.exp_nat_mul]
  have h2 : (1 - x)⁻¹ ≤ Real.exp (x / (1 - x)) := by
    rw [h1]
    exact Real.add_one_le_exp _
  exact pow_le_pow_left₀ (inv_nonneg.2 hpos.le) h2 N

/-- **Theorem 4.1 (iii) of arXiv 2407.01404, corrected**, energy form: if `Δt (1 + 2ν) < 1`,
then `‖u^N‖² + Δt/2 ∑ₙ ‖uⁿ⁺¹‖²_SUPG ≤ (1 + 4δ̄) (1 - Δt(1 + 2ν))^{-N} (‖u⁰‖² + Δt ∑ₙ ‖fⁿ‖²)`.
The paper states `C₃ = e^{(1+2ν)T}` in place of `(1 + 4δ̄)(1 - Δt(1+2ν))^{-N}`; that constant
is too small (`thm_4_1_iii_as_printed_false`); by `inv_one_sub_pow_le_exp` the factor here is at
most `(1 + 4δ̄) exp ((1+2ν) T / (1 - Δt(1+2ν)))`. The hypotheses `µ₀ = 0` and `f ≠ 0` of the paper
are not needed. -/
theorem thm_4_1_iii_of_tested [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) {δbar : ℝ} (hδbar : ∀ K, S.δ K ≤ δbar) (hδbar0 : 0 ≤ δbar)
    {Δt : ℝ} (hΔt : 0 < Δt) (h55 : ∀ K, S.δ K ≤ Δt / 4) (hΔtν : Δt * (1 + 2 * S.nu) < 1)
    {u : ℕ → E} {f : ℕ → P → ℝ} {N : ℕ}
    (hstep : ∀ n < N, Δt⁻¹ * S.pgPair (u (n + 1) - u n) (u (n + 1)) +
      S.aSUPG (u (n + 1)) (u (n + 1)) = S.load (f n) (u (n + 1))) :
    S.normSq (u N) + Δt / 2 * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) ≤
      (1 + 4 * δbar) * (1 - Δt * (1 + 2 * S.nu))⁻¹ ^ N *
        (S.normSq (u 0) + Δt * ∑ n ∈ range N, S.ip (f n) (f n)) := by
  have hμ := muTilde_add_nu_nonneg S
  have hν0 := S.nu_nonneg
  rw [show Δt / 2 * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) =
    ∑ n ∈ range N, Δt / 2 * S.supgNormSq εh S.nu (u (n + 1)) from Finset.mul_sum _ _ _]
  refine gronwall_implicit (a := fun n => S.normSq (u n))
    (s := fun n => Δt / 2 * S.supgNormSq εh S.nu (u n)) (φ := fun n => S.ip (f n) (f n))
    hΔt.le (mul_nonneg hΔt.le (by linarith)) hΔtν (by linarith) (ip_self_nonneg hS.w_nonneg _)
    (fun n => ?_) (fun n => ip_self_nonneg hS.w_nonneg _) fun n hn => ?_
  · obtain ⟨hA, hM, hAM⟩ := supgNormSq_parts hS.w_nonneg h19.nonneg hεh.le hμ (u n)
    have := mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg (u n))
    have : 0 ≤ S.supgNormSq εh S.nu (u n) := by rw [supgNormSq]; linarith
    positivity
  · have e := energy_step hS hεh h10 h19 hμ hΔt h55 (hstep n hn)
    have hl1 := ip_load_le_half hS.w_nonneg (f n) (u (n + 1))
    have hl2 := stab_load_le hS.w_nonneg h19.nonneg hδbar (f n) (u (n + 1))
    obtain ⟨hA, hM, hAM⟩ := supgNormSq_parts hS.w_nonneg h19.nonneg hεh.le hμ (u (n + 1))
    simp only [load] at e
    have hΔt2 := mul_le_mul_of_nonneg_left (by linarith : S.stab (S.adv (u (n + 1)))
      (S.adv (u (n + 1))) ≤ S.supgNormSq εh S.nu (u (n + 1))) hΔt.le
    have hl := mul_le_mul_of_nonneg_left (add_le_add hl1 hl2) (by positivity : (0 : ℝ) ≤ 2 * Δt)
    linarith

end SUPGModel

end SUPG


/-! ### Theorem 4.1 for the iterates of Algorithm 1 -/

section Run

namespace SUPGModel

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {P ι : Type*} {d : ℕ}
  (S : SUPGModel E P ι d)

theorem adv_add (u v : E) : S.adv (u + v) = S.adv u + S.adv v := by
  funext p
  simp only [adv, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem adv_smul (a : ℝ) (u : E) : S.adv (a • u) = a • S.adv u := by
  funext p
  simp only [adv, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ip_add_right [Fintype P] (f g g' : P → ℝ) : S.ip f (g + g') = S.ip f g + S.ip f g' := by
  simp only [ip, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_smul_right [Fintype P] (a : ℝ) (f g : P → ℝ) : S.ip f (a • g) = a * S.ip f g := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem stab_add_right [Fintype P] [Fintype ι] [DecidableEq ι] (f g g' : P → ℝ) :
    S.stab f (g + g') = S.stab f g + S.stab f g' := by
  simp only [stab_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem stab_smul_right [Fintype P] [Fintype ι] [DecidableEq ι] (a : ℝ) (f g : P → ℝ) :
    S.stab f (a • g) = a * S.stab f g := by
  simp only [stab_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem diff_add_right [Fintype P] (u v v' : E) : S.diff u (v + v') = S.diff u v + S.diff u v' := by
  simp only [diff, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem diff_smul_right [Fintype P] (a : ℝ) (u v : E) : S.diff u (a • v) = a * S.diff u v := by
  rw [diff, diff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [show ∑ i, S.grad u p i * (a * S.grad v p i) = a * ∑ i, S.grad u p i * S.grad v p i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  ring

theorem aSUPG_add_right [Fintype P] [Fintype ι] [DecidableEq ι] (u v v' : E) :
    S.aSUPG u (v + v') = S.aSUPG u v + S.aSUPG u v' := by
  simp only [aSUPG, diff_add_right, map_add, ip_add_right, adv_add, stab_add_right]
  ring

theorem aSUPG_smul_right [Fintype P] [Fintype ι] [DecidableEq ι] (a : ℝ) (u v : E) :
    S.aSUPG u (a • v) = a * S.aSUPG u v := by
  simp only [aSUPG, diff_smul_right, map_smul, ip_smul_right, adv_smul, stab_smul_right]
  ring

theorem load_add_right [Fintype P] [Fintype ι] [DecidableEq ι] (f : P → ℝ) (v v' : E) :
    S.load f (v + v') = S.load f v + S.load f v' := by
  simp only [load, map_add, ip_add_right, adv_add, stab_add_right]
  ring

theorem load_smul_right [Fintype P] [Fintype ι] [DecidableEq ι] (a : ℝ) (f : P → ℝ) (v : E) :
    S.load f (a • v) = a * S.load f v := by
  simp only [load, map_smul, ip_smul_right, adv_smul, stab_smul_right]
  ring

/-- `a_SUPG(u, ·)` as a linear functional. -/
def aSUPGₗ [Fintype P] [Fintype ι] [DecidableEq ι] (u : E) : E →ₗ[ℝ] ℝ where
  toFun := S.aSUPG u
  map_add' := S.aSUPG_add_right u
  map_smul' a v := by rw [aSUPG_smul_right, smul_eq_mul, RingHom.id_apply]

/-- `v ↦ F(H v) = (f, H v)` as a linear functional. -/
def loadₗ [Fintype P] [Fintype ι] [DecidableEq ι] (f : P → ℝ) : E →ₗ[ℝ] ℝ where
  toFun := S.load f
  map_add' := S.load_add_right f
  map_smul' a v := by rw [load_smul_right, smul_eq_mul, RingHom.id_apply]

@[simp] theorem aSUPGₗ_apply [Fintype P] [Fintype ι] [DecidableEq ι] (u v : E) :
    S.aSUPGₗ u v = S.aSUPG u v := rfl

@[simp] theorem loadₗ_apply [Fintype P] [Fintype ι] [DecidableEq ι] (f : P → ℝ) (v : E) :
    S.loadₗ f v = S.load f v := rfl

end SUPGModel

variable {m n k P ι : Type*} {d : ℕ}

/-- **The implicit Euler SUPG-DLR scheme of §4.0.1 of arXiv 2407.01404**, run for `N` steps:
Algorithm 1 with `A¹ₕ = 0`, `A²ₕ = a_SUPG`, `F(H v) = (fʲ, H v)` and `H = H₁ ⊗ I`; every step
`uʲ ↦ uʲ⁺¹` is an `IsPGDLRStep` for some representation `uʲ = Û Ŷᵀ` with orthonormal stochastic
modes (the output of the orthonormalisation of the previous step). The model `S` lives on the
matrix model `V_h ⊗ L²_µ̂ ≅ ℝ^{m × n}`. -/
def IsSUPGImplicitRun (k : Type*) [Fintype k] [DecidableEq k] [Fintype m] [Fintype n]
    [Fintype P] [Fintype ι] [DecidableEq ι] (S : SUPGModel (Matrix m n ℝ) P ι d)
    (H1 : Matrix m m ℝ) (Δt : ℝ) (f : ℕ → P → ℝ) (u : ℕ → Matrix m n ℝ) (N : ℕ) : Prop :=
  ∀ j < N, ∃ (Uh : Matrix m (Option k) ℝ) (Yh : Matrix n (Option k) ℝ)
    (Ut : Matrix m (Option k) ℝ) (dY : Matrix n k ℝ),
    IsPGDLRStep H1 0 S.aSUPGₗ (S.loadₗ (f j)) Δt (u j) Uh Yh Ut dY (u (j + 1))

variable [Fintype m] [Fintype n] [Fintype k] [DecidableEq k] [Fintype P] [Fintype ι]
  [DecidableEq ι]

/-- **Eq. (49)** tested with `v = uʲ⁺¹`: by Theorem 3.1 and Lemma 3.2 the iterates of the implicit
Euler SUPG-DLR scheme satisfy the tested variational formulation used in the proof of
Theorem 4.1, when `H₁` represents the SUPG test operator (17) (`hH`). -/
theorem IsSUPGImplicitRun.tested {S : SUPGModel (Matrix m n ℝ) P ι d} {H1 : Matrix m m ℝ}
    {Δt : ℝ} {f : ℕ → P → ℝ} {u : ℕ → Matrix m n ℝ} {N : ℕ}
    (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hrun : IsSUPGImplicitRun k S H1 Δt f u N) (j : ℕ) (hj : j < N) :
    Δt⁻¹ * S.pgPair (u (j + 1) - u j) (u (j + 1)) + S.aSUPG (u (j + 1)) (u (j + 1)) =
      S.load (f j) (u (j + 1)) := by
  obtain ⟨Uh, Yh, Ut, dY, hs⟩ := hrun j hj
  have := hs.variational hs.lemma_3_2.2
  rw [hH] at this
  simpa using this

omit [Fintype ι] [DecidableEq ι] in
theorem norm_sq_eq_normSq {S : SUPGModel (Matrix m n ℝ) P ι d}
    (hval : ∀ w v : Matrix m n ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) (v : Matrix m n ℝ) :
    ‖v‖ ^ 2 = S.normSq v := by
  rw [← real_inner_self_eq_norm_sq, hval]
  rfl

/-- **Theorem 4.1 (i) of arXiv 2407.01404** (norm stability of the implicit Euler SUPG-DLR scheme,
`µ₀ > 0`). Assume (10), (19), (55), `δ̄ ≥ max_K δ_K`, and that `H₁` represents the SUPG test
operator (17) on the matrix model whose Frobenius product is `(·,·)_{X, L²_µ̂}` (`hH`, `hval`).
Then the iterates of Algorithm 1 satisfy (56) with `C₁ = 1/2`, `C₂ = 2/µ₀ + 4δ`:
`‖u^N‖² + Δt/2 ∑ⱼ ‖uʲ⁺¹‖²_SUPG ≤ ‖u⁰‖² + Δt (2/µ₀ + 4δ̄) ∑ⱼ ‖fʲ‖²`.
Finite model (`SUPGModel`), conditional on the finite element facts of `IsFE` (as is every
statement below); the load may change from step to step. -/
theorem thm_4_1_i {S : SUPGModel (Matrix m n ℝ) P ι d} {H1 : Matrix m m ℝ} {εh CE CI : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hval : ∀ w v : Matrix m n ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) (hμ0 : 0 < S.mu0)
    {δbar : ℝ} (hδbar : ∀ K, S.δ K ≤ δbar) {Δt : ℝ} (hΔt : 0 < Δt)
    (h55 : ∀ K, S.δ K ≤ Δt / 4) {f : ℕ → P → ℝ} {u : ℕ → Matrix m n ℝ} {N : ℕ}
    (hrun : IsSUPGImplicitRun k S H1 Δt f u N) :
    ‖u N‖ ^ 2 + Δt * (1 / 2) * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
      ‖u 0‖ ^ 2 + Δt * (2 / S.mu0 + 4 * δbar) * ∑ j ∈ range N, S.ip (f j) (f j) := by
  rw [norm_sq_eq_normSq hval, norm_sq_eq_normSq hval]
  exact SUPGModel.thm_4_1_i_of_tested hS hεh h10 h19 hμ0 hδbar hΔt h55 (hrun.tested hH)

/-- **Theorem 4.1 (ii) of arXiv 2407.01404, corrected** (implicit Euler SUPG-DLR, `f = 0`): if
`ν = 0`, the iterates of Algorithm 1 satisfy (56) with `C₁ = 3/4`, `C₂ = 0`. The paper assumes
`µ₀ = 0` instead; its proof needs `ν = 0`, and for `µ₀ = 0 < ν` the printed claim fails
(`thm_4_1_ii_as_printed_false`). -/
theorem thm_4_1_ii {S : SUPGModel (Matrix m n ℝ) P ι d} {H1 : Matrix m m ℝ} {εh CE CI : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hval : ∀ w v : Matrix m n ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) (hν : S.nu = 0)
    {Δt : ℝ} (hΔt : 0 < Δt) (h55 : ∀ K, S.δ K ≤ Δt / 4) {u : ℕ → Matrix m n ℝ} {N : ℕ}
    (hrun : IsSUPGImplicitRun k S H1 Δt (fun _ => 0) u N) :
    ‖u N‖ ^ 2 + Δt * (3 / 4) * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤ ‖u 0‖ ^ 2 := by
  rw [norm_sq_eq_normSq hval, norm_sq_eq_normSq hval]
  exact SUPGModel.thm_4_1_ii_of_tested hS hεh h10 h19 hν hΔt h55 (hrun.tested hH)

/-- **Theorem 4.1 (iii) of arXiv 2407.01404, corrected** (implicit Euler SUPG-DLR): if
`Δt (1 + 2ν) < 1`, the iterates of Algorithm 1 satisfy
`‖u^N‖² + Δt/2 ∑ⱼ ‖uʲ⁺¹‖²_SUPG ≤ (1 + 4δ̄) (1 - Δt(1+2ν))^{-N} (‖u⁰‖² + Δt ∑ⱼ ‖fʲ‖²)`.
The paper's constant `C₃ = e^{(1+2ν)T}` (`T = NΔt`) in (57) is too small
(`thm_4_1_iii_as_printed_false`); the factor here is at most
`(1 + 4δ̄) exp ((1+2ν) T / (1 - Δt(1+2ν)))` (`inv_one_sub_pow_le_exp`). The paper's hypotheses
`µ₀ = 0` and `f ≠ 0` are not needed. -/
theorem thm_4_1_iii {S : SUPGModel (Matrix m n ℝ) P ι d} {H1 : Matrix m m ℝ} {εh CE CI : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    (h19 : S.IsSUPGParam εh CE CI h) (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hval : ∀ w v : Matrix m n ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) {δbar : ℝ}
    (hδbar : ∀ K, S.δ K ≤ δbar) (hδbar0 : 0 ≤ δbar) {Δt : ℝ} (hΔt : 0 < Δt)
    (h55 : ∀ K, S.δ K ≤ Δt / 4) (hΔtν : Δt * (1 + 2 * S.nu) < 1) {f : ℕ → P → ℝ}
    {u : ℕ → Matrix m n ℝ} {N : ℕ} (hrun : IsSUPGImplicitRun k S H1 Δt f u N) :
    ‖u N‖ ^ 2 + Δt / 2 * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
      (1 + 4 * δbar) * (1 - Δt * (1 + 2 * S.nu))⁻¹ ^ N *
        (‖u 0‖ ^ 2 + Δt * ∑ j ∈ range N, S.ip (f j) (f j)) := by
  rw [norm_sq_eq_normSq hval, norm_sq_eq_normSq hval]
  exact SUPGModel.thm_4_1_iii_of_tested hS hεh h10 h19 hδbar hδbar0 hΔt h55 hΔtν
    (hrun.tested hH)

end Run

/-! ### The semi-implicit SUPG-DLR scheme (§4.0.2) and Theorem 4.2 -/

section SemiImplicit

namespace SUPGModel

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {P ι : Type*} {d : ℕ}
  (S : SUPGModel E P ι d)

/-- The diffusion form `(e ∇u, ∇v)` with a coefficient `e`. -/
def dform [Fintype P] (e : P → ℝ) (u v : E) : ℝ :=
  ∑ p, S.w p * (e p * ∑ i, S.grad u p i * S.grad v p i)

/-- **The explicit form `A¹ₕ` of the semi-implicit scheme (§4.0.2)**, with coefficients `e`, `r`
(in the scheme `e = ε⋆ = ε - ε̄`, `r = c⋆ = c - c̄`):
`(e ∇u, ∇v) + (r u, v) + ∑_K δ_K (-e Δu + r u, b·∇v)_K`. -/
def aExpl [Fintype P] [Fintype ι] [DecidableEq ι] (e r : P → ℝ) (u v : E) : ℝ :=
  S.dform e u v + S.ip (fun p => r p * S.val u p) (S.val v) +
    S.stab (fun p => -(e p * S.lap u p) + r p * S.val u p) (S.adv v)

/-- **The implicit form `A²ₕ` of the semi-implicit scheme (§4.0.2)**, with the means `ε̄`, `c̄`:
`(ε̄∇u, ∇v) + (b·∇u, v) + (c̄u, v) + ∑_K δ_K (-ε̄Δu + b·∇u + c̄u, b·∇v)_K`. -/
def aImpl [Fintype P] [Fintype ι] [DecidableEq ι] (eb cb : P → ℝ) (u v : E) : ℝ :=
  S.dform eb u v + S.ip (S.adv u) (S.val v) + S.ip (fun p => cb p * S.val u p) (S.val v) +
    S.stab (fun p => -(eb p * S.lap u p) + S.adv u p + cb p * S.val u p) (S.adv v)

/-- `A¹ₕ + A²ₕ = a_SUPG` when `ε = ε̄ + ε⋆` and `c = c̄ + c⋆`. -/
theorem aExpl_add_aImpl [Fintype P] [Fintype ι] [DecidableEq ι] (eb cb : P → ℝ) (u v : E) :
    S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) u v + S.aImpl eb cb u v =
      S.aSUPG u v := by
  simp only [aExpl, aImpl, aSUPG, dform, diff, ip, stab_eq]
  rw [← sub_eq_zero]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun p _ => by ring

theorem dform_add_right [Fintype P] (e : P → ℝ) (u v v' : E) :
    S.dform e u (v + v') = S.dform e u v + S.dform e u v' := by
  simp only [dform, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dform_smul_right [Fintype P] (a : ℝ) (e : P → ℝ) (u v : E) :
    S.dform e u (a • v) = a * S.dform e u v := by
  rw [dform, dform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [show ∑ i, S.grad u p i * (a * S.grad v p i) = a * ∑ i, S.grad u p i * S.grad v p i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  ring

/-- `A¹ₕ(u, ·)` as a linear functional. -/
def aExplₗ [Fintype P] [Fintype ι] [DecidableEq ι] (e r : P → ℝ) (u : E) : E →ₗ[ℝ] ℝ where
  toFun := S.aExpl e r u
  map_add' v v' := by
    simp only [aExpl, dform_add_right, map_add, ip_add_right, adv_add, stab_add_right]
    ring
  map_smul' a v := by
    simp only [aExpl, dform_smul_right, map_smul, ip_smul_right, adv_smul, stab_smul_right,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- `A²ₕ(u, ·)` as a linear functional. -/
def aImplₗ [Fintype P] [Fintype ι] [DecidableEq ι] (eb cb : P → ℝ) (u : E) : E →ₗ[ℝ] ℝ where
  toFun := S.aImpl eb cb u
  map_add' v v' := by
    simp only [aImpl, dform_add_right, map_add, ip_add_right, adv_add, stab_add_right]
    ring
  map_smul' a v := by
    simp only [aImpl, dform_smul_right, map_smul, ip_smul_right, adv_smul, stab_smul_right,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem aExplₗ_apply [Fintype P] [Fintype ι] [DecidableEq ι] (e r : P → ℝ) (u v : E) :
    S.aExplₗ e r u v = S.aExpl e r u v := rfl

@[simp] theorem aImplₗ_apply [Fintype P] [Fintype ι] [DecidableEq ι] (eb cb : P → ℝ)
    (u v : E) : S.aImplₗ eb cb u v = S.aImpl eb cb u v := rfl

/-- **Hypotheses of Theorem 4.2**: condition (72),
`δ_K ≤ ⅛ min (1/(2|||c|||_K), h_K²/(2 ε̂ C_I² max(C_E², 1) d), 2Δt)` (with `δ_K ≥ 0`, the first
entry written pointwise), the moderate stochasticity (70) `|ε⋆| ≤ ε̂/32` and (71) `|c⋆| ≤ µ/32`
(with `µ = µ̃ + ν`), and `c_mean`: `|c̄|` at a point is bounded by `|c|` at a point of the same
cell (true for the sample mean `c̄(x) = E_µ̂[c(x, ·)]`). The proof of (85) uses the consequence
`δ_K |||c⋆|||_K ≤ 1/8`. -/
structure IsSemiParam [DecidableEq ι] (εh CE CI Δt : ℝ) (h : ι → ℝ) (eb cb : P → ℝ) :
    Prop where
  nonneg : ∀ K, 0 ≤ S.δ K
  c_bound : ∀ p, 16 * S.δ (S.cell p) * |S.c p| ≤ 1
  h_bound : ∀ K, 16 * εh * CI ^ 2 * max (CE ^ 2) 1 * d * S.δ K ≤ h K ^ 2
  dt_bound : ∀ K, S.δ K ≤ Δt / 4
  eps_star : ∀ p, |S.eps p - eb p| ≤ εh / 32
  c_star : ∀ p, |S.c p - cb p| ≤ (S.muTilde p + S.nu) / 32
  c_mean : ∀ p, ∃ q, S.cell q = S.cell p ∧ |cb p| ≤ |S.c q|

variable {S}

/-- (72) implies (19), so Lemma 2.1 applies ("the bounds on `δ_K` in (72) are smaller than
(19)"). -/
theorem IsSemiParam.toSUPGParam [DecidableEq ι] {εh CE CI Δt : ℝ} {h : ι → ℝ}
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb) (hεh : 0 ≤ εh) :
    S.IsSUPGParam εh CE CI h where
  nonneg := hP.nonneg
  c_bound p := by
    have := hP.c_bound p
    have : 0 ≤ S.δ (S.cell p) * |S.c p| := mul_nonneg (hP.nonneg _) (abs_nonneg _)
    nlinarith
  h_bound K := by
    have h1 := hP.h_bound K
    have hm : CE ^ 2 ≤ max (CE ^ 2) 1 := le_max_left _ _
    have hδ := hP.nonneg K
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h2 : 0 ≤ εh * CI ^ 2 * d * S.δ K := by positivity
    have k1 := mul_le_mul_of_nonneg_left hm h2
    have k2 : 0 ≤ εh * CI ^ 2 * d * S.δ K * max (CE ^ 2) 1 :=
      mul_nonneg h2 ((sq_nonneg CE).trans hm)
    linarith

theorem IsSemiParam.delta_cstar [DecidableEq ι] {εh CE CI Δt : ℝ} {h : ι → ℝ}
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb) (p : P) :
    S.δ (S.cell p) * |S.c p - cb p| ≤ 1 / 8 := by
  obtain ⟨q, hq, hcq⟩ := hP.c_mean p
  have h1 := hP.c_bound p
  have h2 := hP.c_bound q
  rw [hq] at h2
  have hδ := hP.nonneg (S.cell p)
  have h3 : |S.c p - cb p| ≤ |S.c p| + |S.c q| := (abs_sub _ _).trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h3 hδ]

theorem IsSemiParam.delta_h [DecidableEq ι] {εh CE CI Δt : ℝ} {h : ι → ℝ}
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb) (hεh : 0 ≤ εh) (K : ι) :
    16 * d * CI ^ 2 * εh * S.δ K ≤ h K ^ 2 := by
  have h1 := hP.h_bound K
  have hm : 1 ≤ max (CE ^ 2) 1 := le_max_right _ _
  have hδ := hP.nonneg K
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 : 0 ≤ 16 * εh * CI ^ 2 * d * S.δ K := by positivity
  have k1 := mul_le_mul_of_nonneg_left hm h2
  linarith

/-- The pointwise inequality behind (83)-(86). -/
theorem semi_pt {w e r μ δ εh G11 G00 G01 x1 x0 L g : ℝ} (hw : 0 ≤ w) (hμ : 0 ≤ μ)
    (hδ : 0 ≤ δ) (he : |e| ≤ εh / 32) (hr : |r| ≤ μ / 32) (hδr : δ * |r| ≤ 1 / 8)
    (hG11 : 0 ≤ G11) (hG01 : |G01| ≤ (G00 + G11) / 2) :
    w * (e * (G11 - G01)) + w * (r * (x1 - x0)) * x1 + δ * w * (-(e * L) + r * (x1 - x0)) * g ≤
      w * (εh / 32 * (3 / 2 * G11 + 1 / 2 * G00)) +
        w * (μ / 32 * (3 / 2 * x1 ^ 2 + 1 / 2 * x0 ^ 2)) + w * (μ / 32 * (x1 ^ 2 + x0 ^ 2)) +
        δ * w * g * g / 8 + 4 * (δ * w * (e * L) * (e * L)) := by
  have hε0 : 0 ≤ εh / 32 := (abs_nonneg e).trans he
  have hD : |G11 - G01| ≤ 3 / 2 * G11 + 1 / 2 * G00 :=
    (abs_sub _ _).trans (by rw [abs_of_nonneg hG11]; linarith)
  have h1 : e * (G11 - G01) ≤ εh / 32 * (3 / 2 * G11 + 1 / 2 * G00) :=
    calc e * (G11 - G01) ≤ |e * (G11 - G01)| := le_abs_self _
      _ = |e| * |G11 - G01| := abs_mul _ _
      _ ≤ εh / 32 * (3 / 2 * G11 + 1 / 2 * G00) :=
          mul_le_mul he hD (abs_nonneg _) hε0
  have hxx : |(x1 - x0) * x1| ≤ 3 / 2 * x1 ^ 2 + 1 / 2 * x0 ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x1 + x0), sq_nonneg (x1 - x0)]
  have h2 : r * (x1 - x0) * x1 ≤ μ / 32 * (3 / 2 * x1 ^ 2 + 1 / 2 * x0 ^ 2) :=
    calc r * (x1 - x0) * x1 = r * ((x1 - x0) * x1) := by ring
      _ ≤ |r * ((x1 - x0) * x1)| := le_abs_self _
      _ = |r| * |(x1 - x0) * x1| := abs_mul _ _
      _ ≤ μ / 32 * (3 / 2 * x1 ^ 2 + 1 / 2 * x0 ^ 2) :=
          mul_le_mul hr hxx (abs_nonneg _) (by positivity)
  have h3 : δ * (-(e * L) * g) ≤ δ * (4 * (e * L) ^ 2 + g ^ 2 / 16) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (2 * (e * L) + g / 4)]) hδ
  have h4 : δ * (r * (x1 - x0) * g) ≤ δ * (4 * (r * (x1 - x0)) ^ 2 + g ^ 2 / 16) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (2 * (r * (x1 - x0)) - g / 4)]) hδ
  have h5 : δ * (4 * (r * (x1 - x0)) ^ 2) ≤ μ / 32 * (x1 ^ 2 + x0 ^ 2) := by
    have hy : (x1 - x0) ^ 2 ≤ 2 * (x1 ^ 2 + x0 ^ 2) := by nlinarith [sq_nonneg (x1 + x0)]
    have e1 : δ * (4 * (r * (x1 - x0)) ^ 2) = 4 * (δ * |r|) * (|r| * (x1 - x0) ^ 2) := by
      rw [mul_pow, ← sq_abs r]; ring
    have h6 : |r| * (x1 - x0) ^ 2 ≤ μ / 32 * (2 * (x1 ^ 2 + x0 ^ 2)) :=
      mul_le_mul hr hy (sq_nonneg _) (by positivity)
    have h7 : 0 ≤ |r| * (x1 - x0) ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 4 * (1 / 8)),
      mul_le_mul_of_nonneg_right hδr h7]
  nlinarith [mul_le_mul_of_nonneg_left h1 hw, mul_le_mul_of_nonneg_left h2 hw,
    mul_le_mul_of_nonneg_left h3 hw, mul_le_mul_of_nonneg_left h4 hw,
    mul_le_mul_of_nonneg_left h5 hw]

theorem lap_sub (u v : E) (p : P) : S.lap (u - v) p = S.lap u p - S.lap v p := by
  simp [lap, map_sub, Finset.sum_sub_distrib]

theorem gradSq_sub_le [Fintype P] (hw : ∀ p, 0 ≤ S.w p) (u v : E) :
    S.gradSq (u - v) ≤ 2 * S.gradSq u + 2 * S.gradSq v := by
  simp only [gradSq, gradSqAt, map_sub, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun i _ => ?_
  nlinarith [mul_nonneg (hw p) (sq_nonneg (S.grad u p i + S.grad v p i))]

/-- **Eqs. (83)-(86)** (the extra terms of the semi-implicit scheme): for `|e| ≤ ε̂/32`,
`|r| ≤ µ/32`, `δ_K |r| ≤ 1/8` and `16 d C_I² ε̂ δ_K ≤ h_K²`,
`A¹(u₁, u₁) - A¹(u₀, u₁) ≤ 5/64 (ε̂‖∇u₁‖² + ‖µ^{1/2}u₁‖²) + 3/64 (ε̂‖∇u₀‖² + ‖µ^{1/2}u₀‖²)
  + ⅛ ∑_K δ_K ‖b·∇u₁‖²_K`. -/
theorem aExpl_sub_le [Fintype P] [Fintype ι] [DecidableEq ι] {εh CI : ℝ} {h : ι → ℝ}
    (hS : S.IsFE CI h) (hεh : 0 < εh) {e r μ : P → ℝ} (hμ : ∀ p, 0 ≤ μ p)
    (he : ∀ p, |e p| ≤ εh / 32) (hr : ∀ p, |r p| ≤ μ p / 32) (hδ : ∀ K, 0 ≤ S.δ K)
    (hδr : ∀ p, S.δ (S.cell p) * |r p| ≤ 1 / 8)
    (hδh : ∀ K, 16 * d * CI ^ 2 * εh * S.δ K ≤ h K ^ 2) (u0 u1 : E) :
    S.aExpl e r u1 u1 - S.aExpl e r u0 u1 ≤
      5 / 64 * (εh * S.gradSq u1 + S.ip (fun p => μ p * S.val u1 p) (S.val u1)) +
        3 / 64 * (εh * S.gradSq u0 + S.ip (fun p => μ p * S.val u0 p) (S.val u0)) +
        S.stab (S.adv u1) (S.adv u1) / 8 := by
  have hL : S.stab (fun p => e p * S.lap (u1 - u0) p) (fun p => e p * S.lap (u1 - u0) p) ≤
      εh / 256 * S.gradSq (u1 - u0) := by
    refine stab_coefLap_le hS he hδ (fun K => ?_) (u1 - u0)
    have h1 := hδh K
    have hδK := hδ K
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : 0 ≤ d * CI ^ 2 * εh * S.δ K := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hεh.le]
  have hG := gradSq_sub_le hS.w_nonneg u1 u0
  have hstabw : S.stab (fun p => e p * S.lap (u1 - u0) p) (fun p => e p * S.lap (u1 - u0) p) =
      ∑ p, S.δ (S.cell p) * S.w p * (e p * (S.lap u1 p - S.lap u0 p)) *
        (e p * (S.lap u1 p - S.lap u0 p)) := by
    rw [stab_eq]
    simp only [lap_sub]
  obtain ⟨X, hXd⟩ : ∃ X : P → ℝ, X = fun p =>
      S.w p * (e p * (∑ i, S.grad u1 p i * S.grad u1 p i -
        ∑ i, S.grad u0 p i * S.grad u1 p i)) +
      S.w p * (r p * (S.val u1 p - S.val u0 p)) * S.val u1 p +
      S.δ (S.cell p) * S.w p * (-(e p * (S.lap u1 p - S.lap u0 p)) +
        r p * (S.val u1 p - S.val u0 p)) * S.adv u1 p := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : P → ℝ, B = fun p =>
      S.w p * (εh / 32 * (3 / 2 * S.gradSqAt u1 p + 1 / 2 * S.gradSqAt u0 p)) +
      S.w p * (μ p / 32 * (3 / 2 * S.val u1 p ^ 2 + 1 / 2 * S.val u0 p ^ 2)) +
      S.w p * (μ p / 32 * (S.val u1 p ^ 2 + S.val u0 p ^ 2)) +
      S.δ (S.cell p) * S.w p * S.adv u1 p * S.adv u1 p / 8 +
      4 * (S.δ (S.cell p) * S.w p * (e p * (S.lap u1 p - S.lap u0 p)) *
        (e p * (S.lap u1 p - S.lap u0 p))) := ⟨_, rfl⟩
  have hX : S.aExpl e r u1 u1 - S.aExpl e r u0 u1 = ∑ p, X p := by
    rw [hXd]
    simp only [aExpl, dform, ip, stab_eq]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_sub_distrib]; ring
  have hB : ∑ p, B p = εh / 32 * (3 / 2 * S.gradSq u1 + 1 / 2 * S.gradSq u0) +
      1 / 32 * (3 / 2 * S.ip (fun p => μ p * S.val u1 p) (S.val u1) +
        1 / 2 * S.ip (fun p => μ p * S.val u0 p) (S.val u0)) +
      1 / 32 * (S.ip (fun p => μ p * S.val u1 p) (S.val u1) +
        S.ip (fun p => μ p * S.val u0 p) (S.val u0)) +
      S.stab (S.adv u1) (S.adv u1) / 8 +
      4 * S.stab (fun p => e p * S.lap (u1 - u0) p) (fun p => e p * S.lap (u1 - u0) p) := by
    rw [hstabw, hBd]
    simp only [gradSq, ip, stab_eq, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hXB : ∑ p, X p ≤ ∑ p, B p := by
    refine Finset.sum_le_sum fun p _ => ?_
    rw [hXd, hBd]
    dsimp only
    have hG01 : |∑ i, S.grad u0 p i * S.grad u1 p i| ≤
        (S.gradSqAt u0 p + ∑ i, S.grad u1 p i * S.grad u1 p i) / 2 := by
      rw [abs_le]
      simp only [gradSqAt, sq]
      constructor
      · rw [neg_le, ← Finset.sum_neg_distrib, add_div, Finset.sum_div, Finset.sum_div,
          ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        nlinarith [sq_nonneg (S.grad u0 p i + S.grad u1 p i)]
      · rw [add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        nlinarith [sq_nonneg (S.grad u0 p i - S.grad u1 p i)]
    have hG11 : 0 ≤ ∑ i, S.grad u1 p i * S.grad u1 p i :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have key := semi_pt (hS.w_nonneg p) (hμ p) (hδ (S.cell p)) (he p) (hr p) (hδr p) hG11 hG01
      (x1 := S.val u1 p) (x0 := S.val u0 p) (L := S.lap u1 p - S.lap u0 p) (g := S.adv u1 p)
    have e1 : S.gradSqAt u1 p = ∑ i, S.grad u1 p i * S.grad u1 p i := by
      simp only [gradSqAt, sq]
    rw [e1]
    exact key
  have hA := stab_self_nonneg hS.w_nonneg hδ (fun p => e p * S.lap (u1 - u0) p)
  have hG0 := gradSq_nonneg hS.w_nonneg u0
  have hG1 := gradSq_nonneg hS.w_nonneg u1
  have hL' := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ εh / 256)
  linarith

/-- One step of the energy argument of Theorem 4.2 (appendix, (82)-(86)): if
`Δt⁻¹ (u₁ - u₀, H u₁) + A¹(u₀, u₁) + A²(u₁, u₁) = L` (the variational formulation (54) tested with
`u₁`), then `‖u₁‖² - ‖u₀‖² + Δt ‖u₁‖²_SUPG - 2Δtν‖u₁‖² - Δt/2 ∑_K δ_K‖b·∇u₁‖²_K
≤ 2Δt L + 5/32 Δt Z₁ + 3/32 Δt Z₀`, with `Z = ε̂‖∇u‖² + ‖µ^{1/2}u‖²`. -/
theorem semi_energy_step [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI Δt : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb) (hΔt : 0 < Δt) {u0 u1 : E}
    {L : ℝ} (hstep : Δt⁻¹ * S.pgPair (u1 - u0) u1 +
      S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) u0 u1 + S.aImpl eb cb u1 u1 = L) :
    S.normSq u1 - S.normSq u0 + Δt * S.supgNormSq εh S.nu u1 - 2 * Δt * S.nu * S.normSq u1 -
      Δt / 2 * S.stab (S.adv u1) (S.adv u1) ≤
      2 * Δt * L + 5 / 32 * Δt * (εh * S.gradSq u1 +
        S.ip (fun p => (S.muTilde p + S.nu) * S.val u1 p) (S.val u1)) +
        3 / 32 * Δt * (εh * S.gradSq u0 +
          S.ip (fun p => (S.muTilde p + S.nu) * S.val u0 p) (S.val u0)) := by
  have hμ := muTilde_add_nu_nonneg S
  have h19 := hP.toSUPGParam hεh.le
  have hsum := S.aExpl_add_aImpl eb cb u1 u1
  have hX := aExpl_sub_le hS hεh hμ hP.eps_star hP.c_star hP.nonneg hP.delta_cstar
    (hP.delta_h hεh.le) u0 u1
  have hstep' : Δt⁻¹ * S.pgPair (u1 - u0) u1 + S.aSUPG u1 u1 =
      L + (S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) u1 u1 -
        S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) u0 u1) := by
    rw [← hsum]
    linear_combination hstep
  have e := energy_step hS hεh h10 h19 hμ hΔt hP.dt_bound hstep'
  have hX' := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 * Δt)
  clear hstep hstep' hsum
  linarith

/-- `A₀' = ‖u⁰‖² + 3Δt/32 (ε̂‖∇u⁰‖² + ‖µ^{1/2}u⁰‖²)`, the initial term that the proof of
Theorem 4.2 produces (the `n = 0` terms of (83)-(86), multiplied by `2Δt`). -/
def semiA0 [Fintype P] [Fintype ι] [DecidableEq ι] (S : SUPGModel E P ι d) (εh Δt : ℝ)
    (u0 : E) : ℝ :=
  S.normSq u0 + 3 / 32 * Δt * (εh * S.gradSq u0 +
    S.ip (fun p => (S.muTilde p + S.nu) * S.val u0 p) (S.val u0))

/-- For `Δt ≤ 4/3`, `A₀'` is at most the paper's
`A₀ = ‖u⁰‖² + ⅛ ε̂‖∇u⁰‖² + ⅛ ‖µ^{1/2}u⁰‖²`. -/
theorem semiA0_le [Fintype P] [Fintype ι] [DecidableEq ι] (hw : ∀ p, 0 ≤ S.w p) {εh Δt : ℝ}
    (hεh : 0 ≤ εh) (hΔt' : Δt ≤ 4 / 3) (u0 : E) :
    S.semiA0 εh Δt u0 ≤ S.normSq u0 + 1 / 8 * εh * S.gradSq u0 +
      1 / 8 * S.ip (fun p => (S.muTilde p + S.nu) * S.val u0 p) (S.val u0) := by
  have h1 := mul_nonneg hεh (gradSq_nonneg hw u0)
  have h2 := weighted_ip_nonneg hw (muTilde_add_nu_nonneg S) (S.val u0)
  have h3 : 3 / 32 * Δt ≤ 1 / 8 := by linarith
  calc S.semiA0 εh Δt u0 = S.normSq u0 + 3 / 32 * Δt * (εh * S.gradSq u0 +
        S.ip (fun p => (S.muTilde p + S.nu) * S.val u0 p) (S.val u0)) := rfl
    _ ≤ S.normSq u0 + 1 / 8 * (εh * S.gradSq u0 +
        S.ip (fun p => (S.muTilde p + S.nu) * S.val u0 p) (S.val u0)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right h3 (add_nonneg h1 h2))
    _ = _ := by ring

/-- **Theorem 4.2 (i) of arXiv 2407.01404**, energy form (semi-implicit scheme, `µ₀ > 0`):
`‖u^N‖² + Δt/4 ∑ₙ ‖uⁿ⁺¹‖²_SUPG ≤ A₀' + Δt (2/µ₀ + 4δ̄) ∑ₙ ‖fⁿ‖²` (`C₁ = 1/4`,
`C₂ = 2/µ₀ + 4δ`). The paper has `A₀` in place of `A₀'`; `A₀' ≤ A₀` for `Δt ≤ 4/3`
(`semiA0_le`); see the module docstring. -/
theorem thm_4_2_i_of_tested [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI Δt : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb) (hμ0 : 0 < S.mu0) {δbar : ℝ}
    (hδbar : ∀ K, S.δ K ≤ δbar) (hΔt : 0 < Δt) {u : ℕ → E} {f : ℕ → P → ℝ} {N : ℕ}
    (hstep : ∀ n < N, Δt⁻¹ * S.pgPair (u (n + 1) - u n) (u (n + 1)) +
      S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) (u n) (u (n + 1)) +
      S.aImpl eb cb (u (n + 1)) (u (n + 1)) = S.load (f n) (u (n + 1))) :
    S.normSq (u N) + Δt * (1 / 4) * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) ≤
      S.semiA0 εh Δt (u 0) + Δt * (2 / S.mu0 + 4 * δbar) * ∑ n ∈ range N, S.ip (f n) (f n) := by
  have hν := S.nu_eq_zero_of_mu0_pos hμ0
  have hμ := muTilde_add_nu_nonneg S
  set Z : ℕ → ℝ := fun n => εh * S.gradSq (u n) +
    S.ip (fun p => (S.muTilde p + S.nu) * S.val (u n) p) (S.val (u n)) with hZ
  have hZ0 : ∀ n, 0 ≤ Z n := fun n =>
    add_nonneg (mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg _))
      (weighted_ip_nonneg hS.w_nonneg hμ _)
  have key := sum_telescope (a := fun n => S.normSq (u n) + 3 / 32 * Δt * Z n)
    (s := fun n => Δt * (1 / 4) * S.supgNormSq εh S.nu (u (n + 1)))
    (g := fun n => Δt * (2 / S.mu0 + 4 * δbar) * S.ip (f n) (f n)) (N := N) fun n hn => by
      have e := semi_energy_step hS hεh h10 hP hΔt (hstep n hn)
      have hl1 := ip_load_le_mu hS.w_nonneg hμ0 (S.mu0_le) (f n) (u (n + 1))
      have hl2 := stab_load_le hS.w_nonneg hP.nonneg hδbar (f n) (u (n + 1))
      have hG1 := mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg (u (n + 1)))
      have hs1 : S.supgNormSq εh S.nu (u (n + 1)) = εh * S.gradSq (u (n + 1)) +
          S.stab (S.adv (u (n + 1))) (S.adv (u (n + 1))) +
          S.ip (fun p => (S.muTilde p + S.nu) * S.val (u (n + 1)) p) (S.val (u (n + 1))) := rfl
      simp only [load] at e
      have h2Δt : (0 : ℝ) ≤ 2 * Δt := by positivity
      have hl1' := mul_le_mul_of_nonneg_left hl1 h2Δt
      have hl2' := mul_le_mul_of_nonneg_left hl2 h2Δt
      have hG1' := mul_nonneg hΔt.le hG1
      have hνz : 2 * Δt * S.nu * S.normSq (u (n + 1)) = 0 := by rw [hν]; ring
      have hrhs : Δt * (2 / S.mu0 + 4 * δbar) * S.ip (f n) (f n) =
          2 * Δt * (S.ip (f n) (f n) / S.mu0) + 4 * Δt * δbar * S.ip (f n) (f n) := by ring
      simp only [hZ]
      rw [hrhs, hs1]
      rw [hs1] at e
      linarith
  have hΔZ : 0 ≤ 3 / 32 * Δt * Z N := mul_nonneg (by positivity) (hZ0 N)
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [hZ] at key hΔZ
  rw [semiA0]
  linarith

/-- **Theorem 4.2 (ii) of arXiv 2407.01404, with `ν = 0`**, energy form (semi-implicit scheme,
`f = 0`): `‖u^N‖² + Δt/2 ∑ₙ ‖uⁿ⁺¹‖²_SUPG ≤ A₀'`. The paper assumes `µ₀ = 0` and states (56)
(with `‖u⁰‖²`); its proof uses `ν = 0` and produces `A₀` on the right. -/
theorem thm_4_2_ii_of_tested [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI Δt : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb) (hν : S.nu = 0) (hΔt : 0 < Δt)
    {u : ℕ → E} {N : ℕ}
    (hstep : ∀ n < N, Δt⁻¹ * S.pgPair (u (n + 1) - u n) (u (n + 1)) +
      S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) (u n) (u (n + 1)) +
      S.aImpl eb cb (u (n + 1)) (u (n + 1)) = S.load 0 (u (n + 1))) :
    S.normSq (u N) + Δt * (1 / 2) * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) ≤
      S.semiA0 εh Δt (u 0) := by
  have hμ := muTilde_add_nu_nonneg S
  set Z : ℕ → ℝ := fun n => εh * S.gradSq (u n) +
    S.ip (fun p => (S.muTilde p + S.nu) * S.val (u n) p) (S.val (u n)) with hZ
  have hZ0 : ∀ n, 0 ≤ Z n := fun n =>
    add_nonneg (mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg _))
      (weighted_ip_nonneg hS.w_nonneg hμ _)
  have key := sum_telescope (a := fun n => S.normSq (u n) + 3 / 32 * Δt * Z n)
    (s := fun n => Δt * (1 / 2) * S.supgNormSq εh S.nu (u (n + 1)))
    (g := fun _ => 0) (N := N) fun n hn => by
      have e := semi_energy_step hS hεh h10 hP hΔt (hstep n hn)
      have hG1 := mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg (u (n + 1)))
      have hM1 := weighted_ip_nonneg hS.w_nonneg hμ (S.val (u (n + 1)))
      have hs1 : S.supgNormSq εh S.nu (u (n + 1)) = εh * S.gradSq (u (n + 1)) +
          S.stab (S.adv (u (n + 1))) (S.adv (u (n + 1))) +
          S.ip (fun p => (S.muTilde p + S.nu) * S.val (u (n + 1)) p) (S.val (u (n + 1))) := rfl
      rw [load_zero] at e
      have hG1' := mul_nonneg hΔt.le hG1
      have hM1' := mul_nonneg hΔt.le hM1
      have hνz : 2 * Δt * S.nu * S.normSq (u (n + 1)) = 0 := by rw [hν]; ring
      simp only [hZ]
      rw [hs1]
      rw [hs1] at e
      linarith
  have hΔZ : 0 ≤ 3 / 32 * Δt * Z N := mul_nonneg (by positivity) (hZ0 N)
  rw [show Δt * (1 / 2) * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) =
    ∑ n ∈ range N, Δt * (1 / 2) * S.supgNormSq εh S.nu (u (n + 1)) from Finset.mul_sum _ _ _]
  simp only [hZ, Finset.sum_const_zero, add_zero] at key hΔZ
  rw [semiA0]
  linarith

/-- **Theorem 4.2 (iii) of arXiv 2407.01404, corrected**, energy form (semi-implicit scheme): if
`Δt (1 + 2ν) < 1`, then
`‖u^N‖² + Δt/4 ∑ₙ ‖uⁿ⁺¹‖²_SUPG ≤ (1 + 4δ̄) (1 - Δt(1+2ν))^{-N} (A₀' + Δt ∑ₙ ‖fⁿ‖²)`.
The paper states `C₃ = e^{(1+2ν)T}` and `A₀`; as in Theorem 4.1 (iii) the implicit Grönwall step
gives `(1 - Δt(1+2ν))^{-N}` (`inv_one_sub_pow_le_exp`). -/
theorem thm_4_2_iii_of_tested [Fintype P] [Fintype ι] [DecidableEq ι] {εh CE CI Δt : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb) {δbar : ℝ}
    (hδbar : ∀ K, S.δ K ≤ δbar) (hδbar0 : 0 ≤ δbar) (hΔt : 0 < Δt)
    (hΔtν : Δt * (1 + 2 * S.nu) < 1) {u : ℕ → E} {f : ℕ → P → ℝ} {N : ℕ}
    (hstep : ∀ n < N, Δt⁻¹ * S.pgPair (u (n + 1) - u n) (u (n + 1)) +
      S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) (u n) (u (n + 1)) +
      S.aImpl eb cb (u (n + 1)) (u (n + 1)) = S.load (f n) (u (n + 1))) :
    S.normSq (u N) + Δt / 4 * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) ≤
      (1 + 4 * δbar) * (1 - Δt * (1 + 2 * S.nu))⁻¹ ^ N *
        (S.semiA0 εh Δt (u 0) + Δt * ∑ n ∈ range N, S.ip (f n) (f n)) := by
  have hμ := muTilde_add_nu_nonneg S
  have hν0 := S.nu_nonneg
  set Z : ℕ → ℝ := fun n => εh * S.gradSq (u n) +
    S.ip (fun p => (S.muTilde p + S.nu) * S.val (u n) p) (S.val (u n)) with hZ
  have hZ0 : ∀ n, 0 ≤ Z n := fun n =>
    add_nonneg (mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg _))
      (weighted_ip_nonneg hS.w_nonneg hμ _)
  have hsnn : ∀ n, 0 ≤ S.supgNormSq εh S.nu (u n) := fun n => by
    obtain ⟨hA, hM, hAM⟩ := supgNormSq_parts hS.w_nonneg hP.nonneg hεh.le hμ (u n)
    have := mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg (u n))
    rw [supgNormSq]
    linarith
  have hγ0 : 0 ≤ Δt * (1 + 2 * S.nu) := mul_nonneg hΔt.le (by linarith)
  have key := gronwall_implicit (a := fun n => S.normSq (u n) + 3 / 32 * Δt * Z n)
    (s := fun n => Δt / 4 * S.supgNormSq εh S.nu (u n)) (φ := fun n => S.ip (f n) (f n))
    (C := 1 + 4 * δbar) (N := N) hΔt.le hγ0 hΔtν (by linarith)
    (add_nonneg (ip_self_nonneg hS.w_nonneg _) (mul_nonneg (by positivity) (hZ0 0)))
    (fun n => mul_nonneg (by positivity) (hsnn n)) (fun n => ip_self_nonneg hS.w_nonneg _)
    fun n hn => by
      have e := semi_energy_step hS hεh h10 hP hΔt (hstep n hn)
      have hl1 := ip_load_le_half hS.w_nonneg (f n) (u (n + 1))
      have hl2 := stab_load_le hS.w_nonneg hP.nonneg hδbar (f n) (u (n + 1))
      have hG1 := mul_nonneg hεh.le (gradSq_nonneg hS.w_nonneg (u (n + 1)))
      have hM1 := weighted_ip_nonneg hS.w_nonneg hμ (S.val (u (n + 1)))
      have hs1 : S.supgNormSq εh S.nu (u (n + 1)) = εh * S.gradSq (u (n + 1)) +
          S.stab (S.adv (u (n + 1))) (S.adv (u (n + 1))) +
          S.ip (fun p => (S.muTilde p + S.nu) * S.val (u (n + 1)) p) (S.val (u (n + 1))) := rfl
      simp only [load] at e
      have h2Δt : (0 : ℝ) ≤ 2 * Δt := by positivity
      have hl' := mul_le_mul_of_nonneg_left (add_le_add hl1 hl2) h2Δt
      have hG1' := mul_nonneg hΔt.le hG1
      have hM1' := mul_nonneg hΔt.le hM1
      have hZ1 : 0 ≤ Δt * (Δt * (1 + 2 * S.nu)) * Z (n + 1) :=
        mul_nonneg (mul_nonneg hΔt.le hγ0) (hZ0 _)
      simp only [hZ] at hZ1 ⊢
      rw [hs1]
      rw [hs1] at e
      linarith
  have hZN := hZ0 N
  have hΔZ : 0 ≤ 3 / 32 * Δt * Z N := mul_nonneg (by positivity) hZN
  rw [show Δt / 4 * ∑ n ∈ range N, S.supgNormSq εh S.nu (u (n + 1)) =
    ∑ n ∈ range N, Δt / 4 * S.supgNormSq εh S.nu (u (n + 1)) from Finset.mul_sum _ _ _]
  simp only [hZ] at key hΔZ
  rw [semiA0]
  linarith

end SUPGModel

end SemiImplicit

/-! ### Theorem 4.2 for the iterates of Algorithm 1 -/

section SemiRun

variable {m n k P ι : Type*} {d : ℕ}

/-- **The semi-implicit SUPG-DLR scheme of §4.0.2 of arXiv 2407.01404**, run for `N` steps:
Algorithm 1 with `A¹ₕ = aExpl ε⋆ c⋆` (explicit in `uⁿ`), `A²ₕ = aImpl ε̄ c̄` (implicit in
`uⁿ⁺¹`), `ε⋆ = ε - ε̄`, `c⋆ = c - c̄`, `F(H v) = (fʲ, H v)` and `H = H₁ ⊗ I`. -/
def IsSUPGSemiImplicitRun (k : Type*) [Fintype k] [DecidableEq k] [Fintype m] [Fintype n]
    [Fintype P] [Fintype ι] [DecidableEq ι] (S : SUPGModel (Matrix m n ℝ) P ι d)
    (eb cb : P → ℝ) (H1 : Matrix m m ℝ) (Δt : ℝ) (f : ℕ → P → ℝ) (u : ℕ → Matrix m n ℝ)
    (N : ℕ) : Prop :=
  ∀ j < N, ∃ (Uh : Matrix m (Option k) ℝ) (Yh : Matrix n (Option k) ℝ)
    (Ut : Matrix m (Option k) ℝ) (dY : Matrix n k ℝ),
    IsPGDLRStep H1 (S.aExplₗ (fun p => S.eps p - eb p) (fun p => S.c p - cb p))
      (S.aImplₗ eb cb) (S.loadₗ (f j)) Δt (u j) Uh Yh Ut dY (u (j + 1))

variable [Fintype m] [Fintype n] [Fintype k] [DecidableEq k] [Fintype P] [Fintype ι]
  [DecidableEq ι]

/-- **Eq. (54)** tested with `v = uʲ⁺¹` (Theorem 3.1 and Lemma 3.2 for the semi-implicit
scheme). -/
theorem IsSUPGSemiImplicitRun.tested {S : SUPGModel (Matrix m n ℝ) P ι d} {eb cb : P → ℝ}
    {H1 : Matrix m m ℝ} {Δt : ℝ} {f : ℕ → P → ℝ} {u : ℕ → Matrix m n ℝ} {N : ℕ}
    (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hrun : IsSUPGSemiImplicitRun k S eb cb H1 Δt f u N) (j : ℕ) (hj : j < N) :
    Δt⁻¹ * S.pgPair (u (j + 1) - u j) (u (j + 1)) +
      S.aExpl (fun p => S.eps p - eb p) (fun p => S.c p - cb p) (u j) (u (j + 1)) +
      S.aImpl eb cb (u (j + 1)) (u (j + 1)) = S.load (f j) (u (j + 1)) := by
  obtain ⟨Uh, Yh, Ut, dY, hs⟩ := hrun j hj
  have := hs.variational hs.lemma_3_2.2
  rw [hH] at this
  simpa using this

/-- **Theorem 4.2 (i) of arXiv 2407.01404** (norm stability of the semi-implicit SUPG-DLR scheme,
`µ₀ > 0`). Under (10), (70), (71), (72) (`IsSemiParam`), the iterates of Algorithm 1 satisfy (73)
with `C₁ = 1/4`, `C₂ = 2/µ₀ + 4δ` and `A₀' = ‖u⁰‖² + 3Δt/32 (ε̂‖∇u⁰‖² + ‖µ^{1/2}u⁰‖²)` in place
of the paper's `A₀ = ‖u⁰‖² + ⅛ ε̂‖∇u⁰‖² + ⅛ ‖µ^{1/2}u⁰‖²`; `A₀' ≤ A₀` when `Δt ≤ 4/3`
(`SUPGModel.semiA0_le`). Finite model; `ε̄`, `c̄` are any functions with the stated bounds. -/
theorem thm_4_2_i {S : SUPGModel (Matrix m n ℝ) P ι d} {H1 : Matrix m m ℝ} {εh CE CI Δt : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb)
    (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hval : ∀ w v : Matrix m n ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) (hμ0 : 0 < S.mu0)
    {δbar : ℝ} (hδbar : ∀ K, S.δ K ≤ δbar) (hΔt : 0 < Δt) {f : ℕ → P → ℝ}
    {u : ℕ → Matrix m n ℝ} {N : ℕ} (hrun : IsSUPGSemiImplicitRun k S eb cb H1 Δt f u N) :
    ‖u N‖ ^ 2 + Δt * (1 / 4) * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
      ‖u 0‖ ^ 2 + 3 / 32 * Δt * (εh * S.gradSq (u 0) +
        S.ip (fun p => (S.muTilde p + S.nu) * S.val (u 0) p) (S.val (u 0))) +
        Δt * (2 / S.mu0 + 4 * δbar) * ∑ j ∈ range N, S.ip (f j) (f j) := by
  rw [norm_sq_eq_normSq hval, norm_sq_eq_normSq hval]
  exact SUPGModel.thm_4_2_i_of_tested hS hεh h10 hP hμ0 hδbar hΔt (hrun.tested hH)

/-- **Theorem 4.2 (ii) of arXiv 2407.01404, with `ν = 0`** (semi-implicit scheme, `f = 0`): the
iterates of Algorithm 1 satisfy `‖u^N‖² + Δt/2 ∑ⱼ ‖uʲ⁺¹‖²_SUPG ≤ A₀'`. The paper assumes `µ₀ = 0`
and states (56) (right-hand side `‖u⁰‖²`); for `µ₀ = 0 < ν` that claim fails
(`thm_4_2_ii_as_printed_false`). -/
theorem thm_4_2_ii {S : SUPGModel (Matrix m n ℝ) P ι d} {H1 : Matrix m m ℝ} {εh CE CI Δt : ℝ}
    {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh) (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh)
    {eb cb : P → ℝ} (hP : S.IsSemiParam εh CE CI Δt h eb cb)
    (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hval : ∀ w v : Matrix m n ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) (hν : S.nu = 0)
    (hΔt : 0 < Δt) {u : ℕ → Matrix m n ℝ} {N : ℕ}
    (hrun : IsSUPGSemiImplicitRun k S eb cb H1 Δt (fun _ => 0) u N) :
    ‖u N‖ ^ 2 + Δt * (1 / 2) * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
      ‖u 0‖ ^ 2 + 3 / 32 * Δt * (εh * S.gradSq (u 0) +
        S.ip (fun p => (S.muTilde p + S.nu) * S.val (u 0) p) (S.val (u 0))) := by
  rw [norm_sq_eq_normSq hval, norm_sq_eq_normSq hval]
  exact SUPGModel.thm_4_2_ii_of_tested hS hεh h10 hP hν hΔt (hrun.tested hH)

/-- **Theorem 4.2 (iii) of arXiv 2407.01404, corrected** (semi-implicit scheme): if
`Δt (1 + 2ν) < 1`, the iterates of Algorithm 1 satisfy
`‖u^N‖² + Δt/4 ∑ⱼ ‖uʲ⁺¹‖²_SUPG ≤ (1 + 4δ̄)(1 - Δt(1+2ν))^{-N} (A₀' + Δt ∑ⱼ ‖fʲ‖²)`. The paper's
`C₃ = e^{(1+2ν)T}` (with `A₀`) is too small (`thm_4_2_iii_as_printed_false`). -/
theorem thm_4_2_iii {S : SUPGModel (Matrix m n ℝ) P ι d} {H1 : Matrix m m ℝ}
    {εh CE CI Δt : ℝ} {h : ι → ℝ} (hS : S.IsFE CI h) (hεh : 0 < εh)
    (h10 : ∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh) {eb cb : P → ℝ}
    (hP : S.IsSemiParam εh CE CI Δt h eb cb)
    (hH : ∀ w v : Matrix m n ℝ, ⟪w, H1 * v⟫ = S.pgPair w v)
    (hval : ∀ w v : Matrix m n ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) {δbar : ℝ}
    (hδbar : ∀ K, S.δ K ≤ δbar) (hδbar0 : 0 ≤ δbar) (hΔt : 0 < Δt)
    (hΔtν : Δt * (1 + 2 * S.nu) < 1) {f : ℕ → P → ℝ} {u : ℕ → Matrix m n ℝ} {N : ℕ}
    (hrun : IsSUPGSemiImplicitRun k S eb cb H1 Δt f u N) :
    ‖u N‖ ^ 2 + Δt / 4 * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
      (1 + 4 * δbar) * (1 - Δt * (1 + 2 * S.nu))⁻¹ ^ N *
        (‖u 0‖ ^ 2 + 3 / 32 * Δt * (εh * S.gradSq (u 0) +
          S.ip (fun p => (S.muTilde p + S.nu) * S.val (u 0) p) (S.val (u 0))) +
          Δt * ∑ j ∈ range N, S.ip (f j) (f j)) := by
  rw [norm_sq_eq_normSq hval, norm_sq_eq_normSq hval]
  exact SUPGModel.thm_4_2_iii_of_tested hS hεh h10 hP hδbar hδbar0 hΔt hΔtν (hrun.tested hH)

end SemiRun

/-! ### A scalar instance: non-vacuity and the counterexamples to Theorem 4.1 (ii), (iii) -/

section Scalar

/-- A one-point model on `1 × 1` matrices (one physical mode, one sample, rank `R = 0`), `d = 1`:
`u ↦ x = u₀₀`, `∇u = β x`, `Δu = 0`, `b = 1`, `div b = -2β` (so that integration by parts holds),
constant `ε` and `c`, weight `1`, one cell, `δ = 0`. Then `a_SUPG(u, v) = (εβ² + β + c) x y`. -/
def scalarModel (β eps c : ℝ) : SUPGModel (Matrix Unit Unit ℝ) Unit Unit 1 where
  w _ := 1
  cell _ := ()
  val := { toFun := fun M _ => M () (), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  grad :=
    { toFun := fun M _ _ => β * M () ()
      map_add' := fun M M' => by funext _ _; simp only [Matrix.add_apply, Pi.add_apply]; ring
      map_smul' := fun a M => by
        funext _ _
        simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  hess := 0
  eps _ := eps
  b _ _ := 1
  divb _ := -2 * β
  c _ := c
  δ _ := 0

variable (β eps c : ℝ)

@[simp] theorem scalar_w (p : Unit) : (scalarModel β eps c).w p = 1 := rfl
@[simp] theorem scalar_val (M : Matrix Unit Unit ℝ) (p : Unit) :
    (scalarModel β eps c).val M p = M () () := rfl
@[simp] theorem scalar_grad (M : Matrix Unit Unit ℝ) (p : Unit) (i : Fin 1) :
    (scalarModel β eps c).grad M p i = β * M () () := rfl
@[simp] theorem scalar_hess : (scalarModel β eps c).hess = 0 := rfl
@[simp] theorem scalar_eps (p : Unit) : (scalarModel β eps c).eps p = eps := rfl
@[simp] theorem scalar_b (p : Unit) (i : Fin 1) : (scalarModel β eps c).b p i = 1 := rfl
@[simp] theorem scalar_divb (p : Unit) : (scalarModel β eps c).divb p = -2 * β := rfl
@[simp] theorem scalar_c (p : Unit) : (scalarModel β eps c).c p = c := rfl
@[simp] theorem scalar_δ (K : Unit) : (scalarModel β eps c).δ K = 0 := rfl

theorem scalar_ip (f g : Unit → ℝ) : (scalarModel β eps c).ip f g = f () * g () := by
  simp [SUPGModel.ip]

theorem scalar_stab (f g : Unit → ℝ) : (scalarModel β eps c).stab f g = 0 := by
  simp [SUPGModel.stab]

theorem scalar_aSUPG (u v : Matrix Unit Unit ℝ) :
    (scalarModel β eps c).aSUPG u v = (eps * β ^ 2 + β + c) * (u () () * v () ()) := by
  simp only [SUPGModel.aSUPG, scalar_stab, scalar_ip, SUPGModel.diff, SUPGModel.adv, scalar_w,
    scalar_val, scalar_grad, scalar_eps, scalar_b, scalar_c, Fintype.sum_unique]
  ring

theorem scalar_pgPair (u v : Matrix Unit Unit ℝ) :
    (scalarModel β eps c).pgPair u v = u () () * v () () := by
  simp only [SUPGModel.pgPair, scalar_stab, scalar_ip, add_zero]
  rfl

theorem scalar_load (f : Unit → ℝ) (v : Matrix Unit Unit ℝ) :
    (scalarModel β eps c).load f v = f () * v () () := by
  simp only [SUPGModel.load, scalar_stab, scalar_ip, add_zero]
  rfl

theorem scalar_hval (u v : Matrix Unit Unit ℝ) :
    ⟪u, v⟫ = (scalarModel β eps c).ip ((scalarModel β eps c).val u)
      ((scalarModel β eps c).val v) := by
  simp [scalar_ip, LeanDLRA.Frobenius.inner_def]

theorem scalar_hH (u v : Matrix Unit Unit ℝ) :
    ⟪u, (1 : Matrix Unit Unit ℝ) * v⟫ = (scalarModel β eps c).pgPair u v := by
  rw [Matrix.one_mul, scalar_pgPair, LeanDLRA.Frobenius.inner_def]
  simp

theorem scalar_normSq (v : Matrix Unit Unit ℝ) : ‖v‖ ^ 2 = v () () * v () () := by
  rw [norm_sq_eq_normSq (scalar_hval 0 0 0), SUPGModel.normSq, scalar_ip]
  rfl

theorem scalar_nu : (scalarModel β eps c).nu = max (-(c - |c| / 2 + β)) 0 := by
  simp only [SUPGModel.nu, SUPGModel.muTilde, scalarModel]
  rw [ciInf_const]
  ring_nf

theorem scalar_mu0 :
    (scalarModel β eps c).mu0 = c - |c| / 2 + β + max (-(c - |c| / 2 + β)) 0 := by
  simp only [SUPGModel.mu0, scalar_nu]
  simp only [SUPGModel.muTilde, scalarModel]
  rw [ciInf_const]
  ring

theorem scalar_isFE : (scalarModel β eps c).IsFE 1 (fun _ => 1) where
  w_nonneg _ := zero_le_one
  ibp u := by
    rw [scalar_ip, scalar_ip]
    simp only [SUPGModel.adv, scalar_val, scalar_grad, scalar_b, scalar_divb, Fin.sum_univ_one]
    ring
  h_pos _ := one_pos
  inverse u K i := by
    have h0 : (scalarModel β eps c).cellIp K (fun p => (scalarModel β eps c).hess u p i)
        (fun p => (scalarModel β eps c).hess u p i) = 0 := by
      simp [SUPGModel.cellIp]
    rw [h0, mul_zero, one_pow, one_mul]
    exact SUPGModel.cellIp_self_nonneg (fun _ => zero_le_one) K _

theorem scalar_param (εh CE : ℝ) : (scalarModel β eps c).IsSUPGParam εh CE 1 (fun _ => 1) where
  nonneg _ := le_rfl
  c_bound _ := by simp
  h_bound _ := by simp

theorem scalar_supgNormSq (εh ν : ℝ) (v : Matrix Unit Unit ℝ) :
    (scalarModel β eps c).supgNormSq εh ν v =
      (εh * β ^ 2 + (c - |c| / 2 + β + ν)) * (v () () * v () ()) := by
  simp only [SUPGModel.supgNormSq, scalar_stab, scalar_ip, SUPGModel.gradSq,
    SUPGModel.gradSqAt, SUPGModel.muTilde, scalar_val, scalar_grad, scalar_w, scalar_c,
    scalar_divb, Fintype.sum_unique]
  ring

/-- The two-point sequence `u⁰ = x₀`, `uʲ = x₁` (`j ≥ 1`) of `1 × 1` matrices. -/
def twoPoint (x0 x1 : ℝ) (j : ℕ) : Matrix Unit Unit ℝ :=
  Matrix.of fun _ _ => if j = 0 then x0 else x1

/-- One implicit Euler step of the scalar model is a run of Algorithm 1 (rank `R = 0`, one sample,
`H₁ = 1`, the mean mode `Y₀ = 1`). -/
theorem scalar_run {Δt x0 x1 f0 : ℝ}
    (hstep : Δt⁻¹ * (x1 - x0) + (eps * β ^ 2 + β + c) * x1 = f0) :
    IsSUPGImplicitRun Empty (scalarModel β eps c) 1 Δt (fun _ _ => f0) (twoPoint x0 x1) 1 := by
  intro j hj
  obtain rfl : j = 0 := by omega
  refine ⟨Matrix.of fun _ _ => x0, Matrix.of fun _ _ => 1, Matrix.of fun _ _ => x1, 0, ?_⟩
  refine
    { start := ?_, orth := ?_, step1 := ?_, perp := ?_, step2 := fun z j => j.elim, next := ?_ }
  · ext a b
    simp [twoPoint, Matrix.mul_apply]
  · ext i i'
    rcases i with _ | ⟨⟨⟩⟩
    rcases i' with _ | ⟨⟨⟩⟩
    simp [Matrix.mul_apply]
  · intro vh i
    rcases i with _ | ⟨⟨⟩⟩
    simp only [scalar_aSUPG, scalar_load, SUPGModel.aSUPGₗ_apply, SUPGModel.loadₗ_apply,
      Pi.zero_apply, LinearMap.zero_apply, add_zero]
    simp [twoPoint, vecMulVec, Matrix.col, dotProduct]
    linear_combination vh () * hstep
  · ext i i'
    exact i'.elim
  · ext a b
    simp [twoPoint, vecMulVec, tail, Matrix.mul_apply]

/-- The hypotheses of `thm_4_1_i`, `thm_4_1_ii` and `thm_4_1_iii` can be satisfied: the scalar
model with `c = 1` (`µ̃ = 1/2`, `ν = 0`, `µ₀ = 1/2`), `Δt = 1/2`, `f = 0`, `u⁰ = 1`, `u¹ = 2/3`. -/
theorem thm_4_1_hypotheses_satisfiable :
    let S := scalarModel 0 1 1
    S.IsFE 1 (fun _ => 1) ∧ (∀ p, (1 : ℝ) ≤ S.eps p ∧ S.eps p ≤ 1 * 1) ∧
      S.IsSUPGParam 1 1 1 (fun _ => 1) ∧
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, (1 : Matrix Unit Unit ℝ) * v⟫ = S.pgPair w v) ∧
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) ∧
      0 < S.mu0 ∧ S.nu = 0 ∧ (1 / 2 : ℝ) * (1 + 2 * S.nu) < 1 ∧
      IsSUPGImplicitRun Empty S 1 (1 / 2) (fun _ _ => 0) (twoPoint 1 (2 / 3)) 1 := by
  intro S
  have hν : S.nu = 0 := by rw [scalar_nu, max_eq_right (by norm_num)]
  refine ⟨scalar_isFE 0 1 1, fun _ => by simp [S], scalar_param 0 1 1 1 1,
    scalar_hH 0 1 1, scalar_hval 0 1 1, ?_, hν, ?_, scalar_run 0 1 1 (by norm_num)⟩
  · rw [scalar_mu0, max_eq_right (by norm_num)]; norm_num
  · rw [hν]; norm_num

/-- **Theorem 4.1 (ii) of arXiv 2407.01404 is false as printed.** The printed statement: under
(10), (19), (55), if `µ₀ = 0` and `f = 0`, then (56) holds with `C₁ = 3/4`, `C₂ = 0`, in
particular `‖u^N‖² ≤ ‖u⁰‖²`. Counterexample: the scalar model with `c = -1`, `b = 0`, `ε = 1`
(`µ̃ = -3/2`, `ν = 3/2`, `µ₀ = 0`), `Δt = 1/2`: the implicit Euler step (a step of Algorithm 1)
maps `u⁰ = 1` to `u¹ = 2`. The proof in the paper uses `ν = 0`, which `µ₀ = 0` does not imply;
`thm_4_1_ii` is the statement with `ν = 0`. -/
theorem thm_4_1_ii_as_printed_false :
    ¬ ∀ (S : SUPGModel (Matrix Unit Unit ℝ) Unit Unit 1) (H1 : Matrix Unit Unit ℝ)
      (εh CE CI Δt : ℝ) (h : Unit → ℝ) (u : ℕ → Matrix Unit Unit ℝ) (N : ℕ),
      S.IsFE CI h → 0 < εh → (∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh) →
      S.IsSUPGParam εh CE CI h → (∀ w v : Matrix Unit Unit ℝ, ⟪w, H1 * v⟫ = S.pgPair w v) →
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) → 0 < Δt →
      (∀ K, S.δ K ≤ Δt / 4) → S.mu0 = 0 →
      IsSUPGImplicitRun Empty S H1 Δt (fun _ => 0) u N →
      ‖u N‖ ^ 2 + Δt * (3 / 4) * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
        ‖u 0‖ ^ 2 := by
  intro H
  have hrun : IsSUPGImplicitRun Empty (scalarModel 0 1 (-1)) 1 (1 / 2) (fun _ _ => 0)
      (twoPoint 1 2) 1 := scalar_run 0 1 (-1) (by norm_num)
  have hν : (scalarModel 0 1 (-1)).nu = 3 / 2 := by
    rw [scalar_nu, max_eq_left (by norm_num)]; norm_num
  have hmu0 : (scalarModel 0 1 (-1)).mu0 = 0 := by
    rw [scalar_mu0, max_eq_left (by norm_num)]; norm_num
  have := H (scalarModel 0 1 (-1)) 1 1 1 1 (1 / 2) (fun _ => 1) (twoPoint 1 2) 1
    (scalar_isFE 0 1 (-1)) one_pos (fun _ => by simp) (scalar_param 0 1 (-1) 1 1)
    (scalar_hH 0 1 (-1)) (scalar_hval 0 1 (-1)) (by norm_num) (fun _ => by norm_num)
    hmu0 hrun
  rw [scalar_normSq, scalar_normSq, Finset.sum_range_one, scalar_supgNormSq, hν] at this
  norm_num [twoPoint] at this

/-- **Theorem 4.1 (iii) of arXiv 2407.01404 is false as printed.** The printed statement: under
(10), (19), (55), if `µ₀ = 0`, `f ≠ 0` and `Δt < (1 + 2ν)⁻¹`, then (57) holds with
`C₃ = e^{(1+2ν)T}`, `T = NΔt`. Counterexample: the scalar model with `β = -50`
(`b·∇u = -50u`, `div b = 100`), `ε = ε̂ = 1/2500`, `c = 0` (`µ̃ = -50`, `ν = 50`, `µ₀ = 0`),
`Δt = 1/110 < 1/101`, `f = 1/100`, `u⁰ = 1`: the step gives `u¹ = 11001/6100`, and
`‖u¹‖² ≈ 3.25 > e^{101/110} (1 + Δt f²) ≈ 2.50`. The cause is the implicit Grönwall step:
`(1 - Δt(1+2ν))^{-N}` exceeds `e^{(1+2ν)T}`; `thm_4_1_iii` has the correct constant. -/
theorem thm_4_1_iii_as_printed_false :
    ¬ ∀ (S : SUPGModel (Matrix Unit Unit ℝ) Unit Unit 1) (H1 : Matrix Unit Unit ℝ)
      (εh CE CI Δt : ℝ) (h : Unit → ℝ) (u : ℕ → Matrix Unit Unit ℝ) (f : ℕ → Unit → ℝ) (N : ℕ),
      S.IsFE CI h → 0 < εh → (∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh) →
      S.IsSUPGParam εh CE CI h → (∀ w v : Matrix Unit Unit ℝ, ⟪w, H1 * v⟫ = S.pgPair w v) →
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) → 0 < Δt →
      (∀ K, S.δ K ≤ Δt / 4) → S.mu0 = 0 → (∀ j, f j ≠ 0) → Δt < (1 + 2 * S.nu)⁻¹ →
      IsSUPGImplicitRun Empty S H1 Δt f u N →
      ‖u N‖ ^ 2 + Δt / 2 * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
        Real.exp ((1 + 2 * S.nu) * (N * Δt)) *
          (‖u 0‖ ^ 2 + Δt * ∑ j ∈ range N, S.ip (f j) (f j)) := by
  intro H
  have hrun : IsSUPGImplicitRun Empty (scalarModel (-50) (1 / 2500) 0) 1 (1 / 110)
      (fun _ _ => 1 / 100) (twoPoint 1 (11001 / 6100)) 1 :=
    scalar_run (-50) (1 / 2500) 0 (by norm_num)
  have hν : (scalarModel (-50) (1 / 2500) 0).nu = 50 := by
    rw [scalar_nu, max_eq_left (by norm_num)]; norm_num
  have hmu0 : (scalarModel (-50) (1 / 2500) 0).mu0 = 0 := by
    rw [scalar_mu0, max_eq_left (by norm_num)]; norm_num
  have hf : ∀ j : ℕ, (fun _ : Unit => (1 / 100 : ℝ)) ≠ 0 := fun _ h => by
    have := congrFun h (); norm_num at this
  have := H (scalarModel (-50) (1 / 2500) 0) 1 (1 / 2500) 1 1 (1 / 110) (fun _ => 1)
    (twoPoint 1 (11001 / 6100)) (fun _ _ => 1 / 100) 1
    (scalar_isFE (-50) (1 / 2500) 0) (by norm_num) (fun _ => by norm_num)
    (scalar_param (-50) (1 / 2500) 0 _ _) (scalar_hH _ _ _) (scalar_hval _ _ _) (by norm_num)
    (fun _ => by norm_num) hmu0 hf (by rw [hν]; norm_num) hrun
  rw [scalar_normSq, scalar_normSq, Finset.sum_range_one, Finset.sum_range_one,
    scalar_supgNormSq, scalar_ip, hν] at this
  have hexp : Real.exp (101 / 110) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
  have he : Real.exp 1 < 272 / 100 := Real.exp_one_lt_d9.trans (by norm_num)
  norm_num [twoPoint] at this
  linarith


/-! #### The scalar instance for the semi-implicit scheme (`ε̄ = ε`, `c̄ = c`) -/

theorem scalar_aExpl_zero (u v : Matrix Unit Unit ℝ) :
    (scalarModel β eps c).aExpl (fun p => (scalarModel β eps c).eps p - eps)
      (fun p => (scalarModel β eps c).c p - c) u v = 0 := by
  simp [SUPGModel.aExpl, SUPGModel.dform, scalar_ip, scalar_stab]

theorem scalar_aImpl (u v : Matrix Unit Unit ℝ) :
    (scalarModel β eps c).aImpl (fun _ => eps) (fun _ => c) u v =
      (eps * β ^ 2 + β + c) * (u () () * v () ()) := by
  have := (scalarModel β eps c).aExpl_add_aImpl (fun _ => eps) (fun _ => c) u v
  rw [scalar_aExpl_zero, zero_add, scalar_aSUPG] at this
  exact this

theorem scalar_gradSq (v : Matrix Unit Unit ℝ) :
    (scalarModel β eps c).gradSq v = β ^ 2 * (v () () * v () ()) := by
  simp only [SUPGModel.gradSq, SUPGModel.gradSqAt, scalar_w, scalar_grad, Fintype.sum_unique]
  ring

theorem scalar_semiParam {εh CE Δt : ℝ} (hεh : 0 ≤ εh) (hΔt : 0 ≤ Δt) :
    (scalarModel β eps c).IsSemiParam εh CE 1 Δt (fun _ => 1) (fun _ => eps) (fun _ => c) where
  nonneg _ := le_rfl
  c_bound _ := by simp
  h_bound _ := by simp
  dt_bound _ := by
    simp only [scalar_δ]
    exact div_nonneg hΔt (by norm_num)
  eps_star _ := by
    simp only [scalar_eps, sub_self, abs_zero]
    exact div_nonneg hεh (by norm_num)
  c_star p := by
    simp only [scalar_c, sub_self, abs_zero]
    exact div_nonneg (SUPGModel.muTilde_add_nu_nonneg _ p) (by norm_num)
  c_mean p := ⟨p, rfl, le_rfl⟩

/-- One semi-implicit step of the scalar model with `ε̄ = ε`, `c̄ = c` (so `A¹ₕ = 0`) is a run of
Algorithm 1. -/
theorem scalar_semi_run {Δt x0 x1 f0 : ℝ}
    (hstep : Δt⁻¹ * (x1 - x0) + (eps * β ^ 2 + β + c) * x1 = f0) :
    IsSUPGSemiImplicitRun Empty (scalarModel β eps c) (fun _ => eps) (fun _ => c) 1 Δt
      (fun _ _ => f0) (twoPoint x0 x1) 1 := by
  intro j hj
  obtain rfl : j = 0 := by omega
  refine ⟨Matrix.of fun _ _ => x0, Matrix.of fun _ _ => 1, Matrix.of fun _ _ => x1, 0, ?_⟩
  refine
    { start := ?_, orth := ?_, step1 := ?_, perp := ?_, step2 := fun z j => j.elim, next := ?_ }
  · ext a b
    simp [twoPoint, Matrix.mul_apply]
  · ext i i'
    rcases i with _ | ⟨⟨⟩⟩
    rcases i' with _ | ⟨⟨⟩⟩
    simp [Matrix.mul_apply]
  · intro vh i
    rcases i with _ | ⟨⟨⟩⟩
    simp only [SUPGModel.aExplₗ_apply, SUPGModel.aImplₗ_apply, SUPGModel.loadₗ_apply,
      scalar_aExpl_zero, scalar_aImpl, scalar_load, add_zero]
    simp [twoPoint, vecMulVec, Matrix.col, dotProduct]
    linear_combination vh () * hstep
  · ext i i'
    exact i'.elim
  · ext a b
    simp [twoPoint, vecMulVec, tail, Matrix.mul_apply]

/-- The hypotheses of `thm_4_2_i`, `thm_4_2_ii` and `thm_4_2_iii` can be satisfied: the scalar
model with `c = 1`, `ε̄ = ε`, `c̄ = c`, `Δt = 1/2`, `f = 0`, `u⁰ = 1`, `u¹ = 2/3`. -/
theorem thm_4_2_hypotheses_satisfiable :
    let S := scalarModel 0 1 1
    S.IsFE 1 (fun _ => 1) ∧ (∀ p, (1 : ℝ) ≤ S.eps p ∧ S.eps p ≤ 1 * 1) ∧
      S.IsSemiParam 1 1 1 (1 / 2) (fun _ => 1) (fun _ => 1) (fun _ => 1) ∧
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, (1 : Matrix Unit Unit ℝ) * v⟫ = S.pgPair w v) ∧
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) ∧
      0 < S.mu0 ∧ S.nu = 0 ∧ (1 / 2 : ℝ) * (1 + 2 * S.nu) < 1 ∧
      IsSUPGSemiImplicitRun Empty S (fun _ => 1) (fun _ => 1) 1 (1 / 2) (fun _ _ => 0)
        (twoPoint 1 (2 / 3)) 1 := by
  intro S
  have hν : S.nu = 0 := by rw [scalar_nu, max_eq_right (by norm_num)]
  refine ⟨scalar_isFE 0 1 1, fun _ => by simp [S], scalar_semiParam 0 1 1 zero_le_one
    (by norm_num), scalar_hH 0 1 1, scalar_hval 0 1 1, ?_, hν, ?_,
    scalar_semi_run 0 1 1 (by norm_num)⟩
  · rw [scalar_mu0, max_eq_right (by norm_num)]; norm_num
  · rw [hν]; norm_num

/-- **Theorem 4.2 (ii) of arXiv 2407.01404 is false as printed** ("if `µ₀ = 0` and `f = 0`, then
(56) holds with `C₁ = 1/2`, `C₂ = 0`"): the counterexample of `thm_4_1_ii_as_printed_false`
(`ε̄ = ε`, `c̄ = c`, so the semi-implicit step is the implicit Euler step) satisfies (70)-(72)
and maps `u⁰ = 1` to `u¹ = 2`. `thm_4_2_ii` is the statement with `ν = 0`. -/
theorem thm_4_2_ii_as_printed_false :
    ¬ ∀ (S : SUPGModel (Matrix Unit Unit ℝ) Unit Unit 1) (H1 : Matrix Unit Unit ℝ)
      (εh CE CI Δt : ℝ) (h : Unit → ℝ) (eb cb : Unit → ℝ) (u : ℕ → Matrix Unit Unit ℝ) (N : ℕ),
      S.IsFE CI h → 0 < εh → (∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh) →
      S.IsSemiParam εh CE CI Δt h eb cb →
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, H1 * v⟫ = S.pgPair w v) →
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) → 0 < Δt →
      S.mu0 = 0 → IsSUPGSemiImplicitRun Empty S eb cb H1 Δt (fun _ => 0) u N →
      ‖u N‖ ^ 2 + Δt * (1 / 2) * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
        ‖u 0‖ ^ 2 := by
  intro H
  have hrun : IsSUPGSemiImplicitRun Empty (scalarModel 0 1 (-1)) (fun _ => 1) (fun _ => -1) 1
      (1 / 2) (fun _ _ => 0) (twoPoint 1 2) 1 := scalar_semi_run 0 1 (-1) (by norm_num)
  have hν : (scalarModel 0 1 (-1)).nu = 3 / 2 := by
    rw [scalar_nu, max_eq_left (by norm_num)]; norm_num
  have hmu0 : (scalarModel 0 1 (-1)).mu0 = 0 := by
    rw [scalar_mu0, max_eq_left (by norm_num)]; norm_num
  have := H (scalarModel 0 1 (-1)) 1 1 1 1 (1 / 2) (fun _ => 1) (fun _ => 1) (fun _ => -1)
    (twoPoint 1 2) 1 (scalar_isFE 0 1 (-1)) one_pos (fun _ => by simp)
    (scalar_semiParam 0 1 (-1) zero_le_one (by norm_num)) (scalar_hH 0 1 (-1))
    (scalar_hval 0 1 (-1)) (by norm_num) hmu0 hrun
  rw [scalar_normSq, scalar_normSq, Finset.sum_range_one, scalar_supgNormSq, hν] at this
  norm_num [twoPoint] at this

/-- **Theorem 4.2 (iii) of arXiv 2407.01404 is false as printed** ((74) with
`C₃ = e^{(1+2ν)T}` and `A₀ = ‖u⁰‖² + ⅛ ε̂‖∇u⁰‖² + ⅛ ‖µ^{1/2}u⁰‖²`): the counterexample of
`thm_4_1_iii_as_printed_false` with `ε̄ = ε`, `c̄ = c` satisfies (70)-(72); there `A₀ = 9/8` and
`‖u¹‖² ≈ 3.25 > e^{101/110} (9/8 + Δt f²) ≈ 2.82`. `thm_4_2_iii` has the correct constant. -/
theorem thm_4_2_iii_as_printed_false :
    ¬ ∀ (S : SUPGModel (Matrix Unit Unit ℝ) Unit Unit 1) (H1 : Matrix Unit Unit ℝ)
      (εh CE CI Δt : ℝ) (h : Unit → ℝ) (eb cb : Unit → ℝ) (u : ℕ → Matrix Unit Unit ℝ)
      (f : ℕ → Unit → ℝ) (N : ℕ),
      S.IsFE CI h → 0 < εh → (∀ p, εh ≤ S.eps p ∧ S.eps p ≤ CE * εh) →
      S.IsSemiParam εh CE CI Δt h eb cb →
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, H1 * v⟫ = S.pgPair w v) →
      (∀ w v : Matrix Unit Unit ℝ, ⟪w, v⟫ = S.ip (S.val w) (S.val v)) → 0 < Δt →
      S.mu0 = 0 → (∀ j, f j ≠ 0) → Δt < (1 + 2 * S.nu)⁻¹ →
      IsSUPGSemiImplicitRun Empty S eb cb H1 Δt f u N →
      ‖u N‖ ^ 2 + Δt / 4 * ∑ j ∈ range N, S.supgNormSq εh S.nu (u (j + 1)) ≤
        Real.exp ((1 + 2 * S.nu) * (N * Δt)) *
          (‖u 0‖ ^ 2 + 1 / 8 * εh * S.gradSq (u 0) +
            1 / 8 * S.ip (fun p => (S.muTilde p + S.nu) * S.val (u 0) p) (S.val (u 0)) +
            Δt * ∑ j ∈ range N, S.ip (f j) (f j)) := by
  intro H
  have hrun : IsSUPGSemiImplicitRun Empty (scalarModel (-50) (1 / 2500) 0) (fun _ => 1 / 2500)
      (fun _ => 0) 1 (1 / 110) (fun _ _ => 1 / 100) (twoPoint 1 (11001 / 6100)) 1 :=
    scalar_semi_run (-50) (1 / 2500) 0 (by norm_num)
  have hν : (scalarModel (-50) (1 / 2500) 0).nu = 50 := by
    rw [scalar_nu, max_eq_left (by norm_num)]; norm_num
  have hmu0 : (scalarModel (-50) (1 / 2500) 0).mu0 = 0 := by
    rw [scalar_mu0, max_eq_left (by norm_num)]; norm_num
  have hf : ∀ j : ℕ, (fun _ : Unit => (1 / 100 : ℝ)) ≠ 0 := fun _ h => by
    have := congrFun h (); norm_num at this
  have := H (scalarModel (-50) (1 / 2500) 0) 1 (1 / 2500) 1 1 (1 / 110) (fun _ => 1)
    (fun _ => 1 / 2500) (fun _ => 0) (twoPoint 1 (11001 / 6100)) (fun _ _ => 1 / 100) 1
    (scalar_isFE (-50) (1 / 2500) 0) (by norm_num) (fun _ => by norm_num)
    (scalar_semiParam (-50) (1 / 2500) 0 (by norm_num) (by norm_num)) (scalar_hH _ _ _)
    (scalar_hval _ _ _) (by norm_num) hmu0 hf (by rw [hν]; norm_num) hrun
  rw [scalar_normSq, scalar_normSq, Finset.sum_range_one, Finset.sum_range_one,
    scalar_supgNormSq, scalar_gradSq, scalar_ip, scalar_ip, hν] at this
  have hexp : Real.exp (101 / 110) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
  have he : Real.exp 1 < 272 / 100 := Real.exp_one_lt_d9.trans (by norm_num)
  norm_num [twoPoint, SUPGModel.muTilde] at this
  linarith

end Scalar

end

end LeanDLRA.Literature.P2407_01404
