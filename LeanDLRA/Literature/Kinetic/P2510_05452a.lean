import LeanDLRA.Foundations.ODE
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Literature.Kinetic.P1912_07522a

/-!
# Rotational invariance of the data-driven filtered `P_N` equations (arXiv 2510.05452)

B. Plumridge, C. Hauck, S. Schotthöfer, *Data-Driven Filtering of the Spherical Harmonics
Method*, arXiv 2510.05452 (v1).  The paper's mathematical statements are Lemma 1, Propositions 1
and 2, Theorem 1 (Sec. 3.3), the definition (15) of a filter function with the exponential filter
(16), and the remarks on the filter matrix (18) and on isotropic features (Sec. 4).  All of them are
formalized here; Sec. 3.1-3.2 (training by PDE-constrained optimisation, chain rule (30)-(32),
Remark 1) and the appendices (recursions (72)-(78), slab and planar reductions, the finite volume
and Heun schemes (84)-(93)) contain definitions and algorithms but no claims, and Sec. 4 is
numerical.

## Main results

* Moments are indexed by `Mode N` (degree `ℓ ≤ N`, order `m`), with `n = (N + 1)²`
  (`card_mode`).  `G = diag(1 - g_ℓ)` (`scatterMatrix`) and `F` of (18) (`filterMatrix`) are
  multiples of the identity on each degree block (`blockScalar`), `Z_O` is block diagonal.
* **Lemma 1**: `lemma1_mul_transpose` (Eq. (37): `r(Ω) = Z r(OΩ)` and orthonormality give
  `Z Zᵀ = I`), `blocks_mul_transpose_of_blockDiagonal'`, `IsLemma1Data.blocks_orthogonal`,
  `blockDiagonal'_transpose_mul_self`, and (36), (38): `moment_comp`, `moment_rotKin`.
* **Proposition 1**, RTE part: `stream_rotKin` (39), `scatter_rotKin` (40), `prop1_rte` (iff).
  `P_N` part: `blockDiagonal'_mul_blockScalar` (42), `advPN_rotMom` (41), `prop1_pn`,
  `prop1_pn_pde`.
* **Theorem 1**: `features_rotMom` (46), `rotMom_fpnRHS` ((44)-(47)), `theorem1`, `theorem1_pde`,
  `theorem1_const` (constant filter strength, remark before Theorem 1), and the semi-discrete
  version in the library's `ODESolution` (`theorem1_ode`).
* **Proposition 2**: `pOp_blockDiagonal'_mulVec` (`P Z_O u = P u`), `prop2`, and with Theorem 1
  `theorem1_nnAnsatz`: the ansatz `𝒩(P ξ, P s)` makes the data-driven `FP_N` equations rotation
  invariant for every network `𝒩`.
* Filters: `IsFilterFunction` (15), `isFilterFunction_expFilter` (`exp(-s⁴)` has order four),
  `filterMatrix_expFilter`, `filterMatrix_mode00` and `fpnRHS_mode00` (`F_{(0,0),(0,0)} = 0`: the
  filter does not change the concentration equation), `filterMatrix_diag_nonneg`.
* Isotropic scattering: `pOp_features_two_isotropic` (only the `ℓ = 0` entry of `σₛ P(G - I)v` is
  nonzero, Sec. 4), `scatterMatrix_isoCoeff` (`G = I - κ e eᵀ`).
* Connection to the library: `pnRHS_eq_pnData_field` identifies the `P_N` right-hand side with
  `PNData.field` of `LeanDLRA.Literature.P1912_07522` (the semi-discrete `P_N` system of arXiv
  1912.07522), and `theorem1_ode` is stated with `ODESolution`.  `isLemma1Data_dirac` shows that
  the hypotheses of Lemma 1 can be met.

## Setting and differences from the paper

* Directions and positions lie in a real inner product space `E` (the paper: `ℝ³`), rotations are
  linear isometries `O : E ≃ₗᵢ[ℝ] E`, and the angular measure is any `O`-invariant measure `μ`
  (the paper: the surface measure of `𝕊²`, which every orthogonal `O` preserves).  The space
  domain is all of `E`, so the inflow condition (1c) is absent; time derivatives are classical,
  pointwise in `x`, for `t` in a set `T`.
* The streaming term `Ω·∇ₓ` is the directional derivative `fderiv ℝ (ψ(·, Ω)) x Ω` (`stream`).
  The `P_N` advection is `A·∇ₓ v = ⟨r Ω·∇ₓ(rᵀ v)⟩` (`advPN`), the first expression in (41), which
  equals (13) for differentiable `v`.  `σₜ = σₐ + σₛ` in the features (20).  The ansatz `Σ_f` and
  the network `𝒩` are arbitrary functions (the weights `w` are fixed).
* **Conditional statements.**  `theorem1`, `prop1_pn`, `theorem1_const` and `theorem1_ode` are
  stated for an abstract domain and advection and assume what the paper's proof takes from
  Proposition 1: `Z G = G Z`, `Z F = F Z` and the commutation (41) of `W_O` with the advection.
  `theorem1_pde`, `prop1_pn_pde` and `theorem1_nnAnsatz` discharge these for the paper's operators.
  They assume only Lemma 1's input `r(Ω) = Z_O r(OΩ)` with orthonormal `r` (`IsLemma1Data`): the
  invariance of the span of the degree-`ℓ` spherical harmonics under rotations, which the paper
  cites ([11, Thm. 1.1.7]) and which needs harmonic analysis on `𝕊²` that Mathlib lacks.  Their
  integrability hypothesis `hreg` is the paper's "sufficiently smooth".  `theorem1_ode` (grids) is
  not a statement of the paper, which states Theorem 1 for the PDE only.
* Not formalised: the eigenvalue property (6) of the spherical harmonics and the formula (7) for
  `g_ℓ` (`isoCoeff` takes `g_0 = 1`, `g_ℓ = 0` for `ℓ ≥ 1` as the isotropic case), the recursion
  relations of Appendix A, and the convergence results of [13] quoted in Sec. 2.3.

## Finding

Eq. (15) as printed requires `f^(ℓ)(0) = 0` for all `ℓ ≤ α - 1`, which for `ℓ = 0` contradicts
`f(0) = 1` (`printed_15_inconsistent`); the intended range is `1 ≤ ℓ ≤ α - 1`.  This is a typo
and affects nothing else.  No other claim was found to be false.

## Definitions

Core and library definitions used: `ODESolution` (`Foundations/ODE`), the Frobenius norm
(`Matrix/Frobenius`), `PNData` (`Literature/Kinetic/P1912_07522a`).  The library has no
spherical-harmonic moment structure, no rotations of kinetic functions and no filtered `P_N`
system, so this file adds them (`Mode`, `blockScalar`, `scatterMatrix`, `filterMatrix`, `pOp`,
`moment`, `rotKin`, `rotMom`, `stream`, `scatter`, `advPN`, `pnRHS`, `features`, `fpnRHS`, ...);
`pnRHS` is bridged to `PNData.field` by `pnRHS_eq_pnData_field`.
-/

open Matrix MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Literature.P2510_05452

open LeanDLRA

/-! ### Moment index set, block-scalar matrices and the operator `P` -/

/-- The index set of the real spherical harmonics `r_ℓ^m` up to degree `N` (arXiv 2510.05452,
Eq. (9)): the degree `ℓ ∈ {0, …, N}` and one of the `2ℓ + 1` orders `m ∈ {-ℓ, …, ℓ}`, ordered by
degree as in `r = [r_0ᵀ, …, r_Nᵀ]ᵀ`. -/
abbrev Mode (N : ℕ) := Σ ℓ : Fin (N + 1), Fin (2 * (ℓ : ℕ) + 1)

/-- arXiv 2510.05452, Sec. 2.2: the number of moments is `n = (N + 1)²`. -/
theorem card_mode (N : ℕ) : Fintype.card (Mode N) = (N + 1) ^ 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun ℓ => 2 * ℓ + 1)]
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

variable {N : ℕ}

/-- A diagonal matrix on the moments that is a multiple `c ℓ` of the identity on each degree block.
The scattering matrix `G` (Sec. 2.2, `G_{(ℓ,m),(ℓ,m)} = 1 - g_ℓ`) and the filter matrix `F`
(Eq. (18)) have this form. -/
def blockScalar (c : Fin (N + 1) → ℝ) : Matrix (Mode N) (Mode N) ℝ :=
  diagonal fun i => c i.1

/-- The scattering matrix `G = ⟨r Q rᵀ⟩` of the `P_N` equations (12): diagonal with entries
`1 - g_ℓ` (arXiv 2510.05452, below (13)). -/
def scatterMatrix (g : Fin (N + 1) → ℝ) : Matrix (Mode N) (Mode N) ℝ :=
  blockScalar fun ℓ => 1 - g ℓ

/-- The filter matrix `F` of the `FP_N` equations, Eq. (18):
`F_{(ℓ,m),(ℓ,m)} = -log f(ℓ / (N + 1))`. -/
noncomputable def filterMatrix (N : ℕ) (f : ℝ → ℝ) : Matrix (Mode N) (Mode N) ℝ :=
  blockScalar fun ℓ => -Real.log (f ((ℓ : ℝ) / (N + 1)))

/-- A block-diagonal matrix commutes with every block-scalar matrix.  This is the step "`Z_O` and
`G` have the same block structure and each block of `G` is a multiple of the identity, so `Z_O`
and `G` commute" in the proof of Proposition 1, and the same step for `F` in Theorem 1. -/
theorem blockDiagonal'_mul_blockScalar
    (Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ)
    (c : Fin (N + 1) → ℝ) :
    blockDiagonal' Zb * blockScalar c = blockScalar c * blockDiagonal' Zb := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [blockScalar, mul_diagonal, diagonal_mul]
  by_cases h : i = j
  · subst h; simp [mul_comm]
  · simp [blockDiagonal'_apply_ne _ _ _ h]

/-- The Euclidean norm `|u_ℓ| = √(u_ℓᵀ u_ℓ)` of the degree-`ℓ` block of a moment vector. -/
noncomputable def blockNorm (u : Mode N → ℝ) (ℓ : Fin (N + 1)) : ℝ :=
  Real.sqrt (∑ m : Fin (2 * (ℓ : ℕ) + 1), u ⟨ℓ, m⟩ ^ 2)

/-- The operator `P : ℝⁿ → ℝ^{N+1}` of Eq. (48), `P u = [|u_0|, …, |u_N|]ᵀ`. -/
noncomputable def pOp (u : Mode N → ℝ) : Fin (N + 1) → ℝ := blockNorm u

/-- A block-diagonal matrix acts on each degree block separately. -/
theorem blockDiagonal'_mulVec_apply
    (Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ)
    (u : Mode N → ℝ) (ℓ : Fin (N + 1)) (m : Fin (2 * (ℓ : ℕ) + 1)) :
    (blockDiagonal' Zb *ᵥ u) ⟨ℓ, m⟩ = (Zb ℓ *ᵥ fun b => u ⟨ℓ, b⟩) m := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single ℓ]
  · simp
  · intro j _ hj
    exact Finset.sum_eq_zero fun b _ => by rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hj), zero_mul]
  · simp

lemma sum_sq_eq_dotProduct {k : Type*} [Fintype k] (v : k → ℝ) : ∑ i, v i ^ 2 = v ⬝ᵥ v := by
  simp [dotProduct, sq]

/-- An orthogonal matrix preserves the sum of squares. -/
lemma dotProduct_mulVec_self {k : Type*} [Fintype k] [DecidableEq k] {Q : Matrix k k ℝ}
    (hQ : Qᵀ * Q = 1) (v : k → ℝ) : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hQ, one_mulVec, dotProduct_comm]

/-- arXiv 2510.05452, proof of Proposition 2: `P u = P Z_O u` for every block-diagonal `Z_O`
with orthogonal blocks. -/
theorem pOp_blockDiagonal'_mulVec
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (hZ : ∀ ℓ, (Zb ℓ)ᵀ * Zb ℓ = 1) (u : Mode N → ℝ) :
    pOp (blockDiagonal' Zb *ᵥ u) = pOp u := by
  funext ℓ
  simp only [pOp, blockNorm, blockDiagonal'_mulVec_apply]
  rw [sum_sq_eq_dotProduct, sum_sq_eq_dotProduct, dotProduct_mulVec_self (hZ ℓ)]

/-- arXiv 2510.05452, Lemma 1 ("hence so is `Z_O`"): a block-diagonal matrix with orthogonal
blocks is orthogonal. -/
theorem blockDiagonal'_transpose_mul_self
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (hZ : ∀ ℓ, (Zb ℓ)ᵀ * Zb ℓ = 1) : (blockDiagonal' Zb)ᵀ * blockDiagonal' Zb = 1 := by
  rw [blockDiagonal'_transpose, ← blockDiagonal'_mul]
  simp only [hZ]
  exact blockDiagonal'_one

/-- Conversely, if the block-diagonal `Z_O` satisfies `Z_O Z_Oᵀ = I`, then so does every block
`Z_O^ℓ`; this is the form in which Lemma 1 states orthogonality. -/
theorem blocks_mul_transpose_of_blockDiagonal'
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (hZ : blockDiagonal' Zb * (blockDiagonal' Zb)ᵀ = 1) (ℓ : Fin (N + 1)) :
    Zb ℓ * (Zb ℓ)ᵀ = 1 := by
  have h : blockDiagonal' (fun k => Zb k * (Zb k)ᵀ) =
      blockDiagonal' (1 : ∀ k : Fin (N + 1), Matrix (Fin (2 * (k : ℕ) + 1))
        (Fin (2 * (k : ℕ) + 1)) ℝ) := by
    rw [blockDiagonal'_mul, ← blockDiagonal'_transpose, hZ, blockDiagonal'_one]
  exact congrFun (blockDiagonal'_injective h) ℓ

/-! ### Rotations of kinetic functions and of moments: Definition 1 and Lemma 1 -/

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {ι : Type*} [Fintype ι]

/-- The moments `⟨r f⟩ = ∫ r(Ω) f(Ω) dΩ` of a function of the direction, componentwise, for a
measure `μ` on directions (in the paper the surface measure of `𝕊²`). -/
noncomputable def moment (μ : Measure E) (r : E → ι → ℝ) (f : E → ℝ) : ι → ℝ :=
  fun i => ∫ Ω, r Ω i * f Ω ∂μ

/-- The operator `R_O` of Definition 1, Eq. (33): `(R_O f)(x, Ω) = f(Ox, OΩ)`. -/
def rotKin (O : E ≃ₗᵢ[ℝ] E) (f : E → E → ℝ) : E → E → ℝ := fun x Ω => f (O x) (O Ω)

/-- The operator `W_O` on moment fields in the form (36), `(W_O v)(x) = Z_O v(Ox)`.  It is
defined for any map `O` of the spatial domain, so that it also covers grids. -/
def rotMom {X : Type*} (O : X → X) (Z : Matrix ι ι ℝ) (v : X → ι → ℝ) : X → ι → ℝ :=
  fun x => Z *ᵥ v (O x)

/-- arXiv 2510.05452, Lemma 1, the orthogonality step (37).  If `r(Ω) = Z r(OΩ)` for a linear
isometry `O` that preserves the measure `μ` of the directions, and the components of `r` are
orthonormal in `L²(μ)`, then `Z Zᵀ = I`.  The existence of `Z` (the invariance of the span of the
degree-`ℓ` harmonics under rotations, [11, Thm. 1.1.7] in the paper) is the hypothesis `hr`. -/
theorem lemma1_mul_transpose {μ : Measure E} {O : E ≃ₗᵢ[ℝ] E} (hμ : MeasurePreserving O μ μ)
    [DecidableEq ι] {r : E → ι → ℝ} {Z : Matrix ι ι ℝ} (hr : ∀ Ω, r Ω = Z *ᵥ r (O Ω))
    (hint : ∀ i j, Integrable (fun Ω => r Ω i * r Ω j) μ)
    (hgram : ∀ i j, ∫ Ω, r Ω i * r Ω j ∂μ = (1 : Matrix ι ι ℝ) i j) :
    Z * Zᵀ = 1 := by
  have hemb : MeasurableEmbedding O := O.toHomeomorph.measurableEmbedding
  ext i j
  have key : ∀ Ω, r Ω i * r Ω j = ∑ a, ∑ b, Z i a * Z j b * (r (O Ω) a * r (O Ω) b) := by
    intro Ω
    rw [hr Ω]
    simp only [mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hcomp : ∀ a b, ∫ Ω, r (O Ω) a * r (O Ω) b ∂μ = (1 : Matrix ι ι ℝ) a b := fun a b => by
    rw [← hgram a b]
    exact hμ.integral_comp hemb (fun Ω => r Ω a * r Ω b)
  have hint' : ∀ a b, Integrable (fun Ω => r (O Ω) a * r (O Ω) b) μ := fun a b =>
    (hμ.integrable_comp_emb hemb).2 (hint a b)
  rw [← hgram i j]
  simp_rw [key]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (hint' a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (hint' _ b).const_mul _, integral_const_mul, hcomp]
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- arXiv 2510.05452, Lemma 1, Eq. (38): `⟨r f(O ·)⟩ = Z ⟨r f⟩`. -/
theorem moment_comp {μ : Measure E} {O : E ≃ₗᵢ[ℝ] E} (hμ : MeasurePreserving O μ μ)
    {r : E → ι → ℝ} {Z : Matrix ι ι ℝ} (hr : ∀ Ω, r Ω = Z *ᵥ r (O Ω)) {f : E → ℝ}
    (hf : ∀ i, Integrable (fun Ω => r Ω i * f Ω) μ) :
    moment μ r (fun Ω => f (O Ω)) = Z *ᵥ moment μ r f := by
  have hemb : MeasurableEmbedding O := O.toHomeomorph.measurableEmbedding
  funext i
  have key : ∀ Ω, r Ω i * f (O Ω) = ∑ a, Z i a * (r (O Ω) a * f (O Ω)) := by
    intro Ω
    rw [hr Ω]
    simp only [mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [moment, mulVec, dotProduct]
  simp_rw [key]
  rw [integral_finsetSum (f := fun a Ω => Z i a * (r (O Ω) a * f (O Ω))) _
    fun a _ => ((hμ.integrable_comp_emb hemb).2 (hf a)).const_mul (Z i a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul]
  congr 1
  exact hμ.integral_comp hemb (fun Ω => r Ω a * f Ω)

/-- arXiv 2510.05452, Lemma 1, Eq. (36): the moments of `R_O f` are `W_O` of the moments of
`f`, `⟨r (R_O f)(x, ·)⟩ = Z_O ⟨r f(Ox, ·)⟩`.  In particular `W_O`, defined in (34) through `f`,
depends only on the moments `v = ⟨r f⟩`. -/
theorem moment_rotKin {μ : Measure E} {O : E ≃ₗᵢ[ℝ] E} (hμ : MeasurePreserving O μ μ)
    {r : E → ι → ℝ} {Z : Matrix ι ι ℝ} (hr : ∀ Ω, r Ω = Z *ᵥ r (O Ω)) (f : E → E → ℝ)
    (hf : ∀ x i, Integrable (fun Ω => r Ω i * f x Ω) μ) :
    (fun x => moment μ r (rotKin O f x)) = rotMom O Z (fun x => moment μ r (f x)) := by
  funext x
  exact moment_comp hμ hr (hf (O x))

/-! ### Proposition 1 for the radiation transport equation -/

/-- The streaming term `Ω · ∇ₓ f(x, Ω)` of (1a), written as the derivative of `f(·, Ω)` at `x` in
the direction `Ω`. -/
noncomputable def stream (f : E → E → ℝ) (x Ω : E) : ℝ := fderiv ℝ (fun y => f y Ω) x Ω

omit [MeasurableSpace E] [BorelSpace E] in
/-- arXiv 2510.05452, Eq. (39): `R_O (Ω · ∇ₓ f) = Ω · ∇ₓ (R_O f)`.  No smoothness is needed:
both sides vanish where `f` is not differentiable. -/
theorem stream_rotKin (O : E ≃ₗᵢ[ℝ] E) (f : E → E → ℝ) (x Ω : E) :
    stream (rotKin O f) x Ω = stream f (O x) (O Ω) := by
  have h := O.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ) (f := fun y => f y (O Ω))
    (x := x)
  have h2 := congrArg (fun L => L Ω) h
  simpa [stream, rotKin, Function.comp_def] using h2

/-- The scattering operator `Q` of Eq. (2): `Q f(x, Ω) = f(x, Ω) - ∫ g(Ω · Ω') f(x, Ω') dΩ'`. -/
noncomputable def scatter (μ : Measure E) (g : ℝ → ℝ) (f : E → E → ℝ) (x Ω : E) : ℝ :=
  f x Ω - ∫ Ω', g ⟪Ω, Ω'⟫ * f x Ω' ∂μ

/-- arXiv 2510.05452, Eq. (40): `R_O (Q f) = Q (R_O f)` for every kernel `g`, when `O` preserves
the measure of the directions. -/
theorem scatter_rotKin {μ : Measure E} {O : E ≃ₗᵢ[ℝ] E} (hμ : MeasurePreserving O μ μ)
    (g : ℝ → ℝ) (f : E → E → ℝ) (x Ω : E) :
    scatter μ g (rotKin O f) x Ω = scatter μ g f (O x) (O Ω) := by
  have h := hμ.integral_comp O.toHomeomorph.measurableEmbedding
    (fun Ω' => g ⟪O Ω, Ω'⟫ * f (O x) Ω')
  simp only [LinearIsometryEquiv.inner_map_map] at h
  simp only [scatter, rotKin, h]

/-- `ψ` solves the radiation transport equation (1a), `∂ₜψ + Ω·∇ₓψ + σₐψ + σₛ Qψ = S`, at all
times `t ∈ T`, with the space variable in all of `E`. -/
def IsRTESolution (μ : Measure E) (g : ℝ → ℝ) (σa σs : E → ℝ) (S : ℝ → E → E → ℝ) (T : Set ℝ)
    (ψ : ℝ → E → E → ℝ) : Prop :=
  ∀ t ∈ T, ∀ x Ω, HasDerivAt (fun τ => ψ τ x Ω)
    (S t x Ω - stream (ψ t) x Ω - σa x * ψ t x Ω - σs x * scatter μ g (ψ t) x Ω) t

/-- arXiv 2510.05452, Proposition 1, first part: the RTE (1a) is rotationally invariant.  `ψ`
solves it with source `S` and cross-sections `σₐ, σₛ` if and only if, for every linear isometry
`O` preserving the measure of the directions, `R_O ψ` solves it with source `R_O S` and
cross-sections `R_O σₐ, R_O σₛ`.  Differences from the paper: the space domain is all of `E`
(a rotation invariant domain), so the inflow condition (1c) is absent; `E` is any real inner
product space and `μ` any `O`-invariant measure (the paper: `ℝ³` and the surface measure of
`𝕊²`). -/
theorem prop1_rte (μ : Measure E) (g : ℝ → ℝ) (σa σs : E → ℝ) (S : ℝ → E → E → ℝ) (T : Set ℝ)
    (ψ : ℝ → E → E → ℝ) :
    IsRTESolution μ g σa σs S T ψ ↔ ∀ O : E ≃ₗᵢ[ℝ] E, MeasurePreserving O μ μ →
      IsRTESolution μ g (σa ∘ O) (σs ∘ O) (fun t => rotKin O (S t)) T
        (fun t => rotKin O (ψ t)) := by
  constructor
  · intro h O hμ t ht x Ω
    have := h t ht (O x) (O Ω)
    simp only [rotKin, Function.comp_apply]
    rw [stream_rotKin, scatter_rotKin hμ]
    exact this
  · intro h
    exact h (LinearIsometryEquiv.refl ℝ E) (MeasurePreserving.id μ)

end Rotation

/-! ### The `P_N` and `FP_N` equations on moment fields: Theorem 1 -/

section MomentEquations

variable {X ι : Type*} [Fintype ι]

/-- The right-hand side `s - T v` of the `P_N` equations (12), (14a),
`T v = A·∇ₓ v + σₐ v + σₛ G v`, with the advection `A·∇ₓ` an operator `adv` on moment fields
`X → ℝⁿ`. -/
def pnRHS (adv : (X → ι → ℝ) → X → ι → ℝ) (σa σs : X → ℝ) (G : Matrix ι ι ℝ)
    (s v : X → ι → ℝ) : X → ι → ℝ :=
  fun x => s x - adv v x - σa x • v x - σs x • (G *ᵥ v x)

/-- The feature matrix `ξ(v)(x) = [A·∇ₓ v, σₜ v, σₛ (G - I) v] ∈ ℝ^{n×3}` of Eq. (20), with the
total cross-section `σₜ = σₐ + σₛ`. -/
def features (adv : (X → ι → ℝ) → X → ι → ℝ) (σa σs : X → ℝ) (G : Matrix ι ι ℝ) [DecidableEq ι]
    (v : X → ι → ℝ) (x : X) : Matrix ι (Fin 3) ℝ :=
  Matrix.of fun i c => (![adv v x, (σa x + σs x) • v x, σs x • ((G - 1) *ᵥ v x)] c) i

/-- The filter strength `σ_f(x) = Σ_f(ξ(v)(x), s(x))` of Eq. (19), for an ansatz
`Σ_f : ℝ^{n×3} × ℝⁿ → ℝ` (the parameters `w` are fixed). -/
def filterStrength (adv : (X → ι → ℝ) → X → ι → ℝ) (σa σs : X → ℝ) (G : Matrix ι ι ℝ)
    [DecidableEq ι] (Sf : Matrix ι (Fin 3) ℝ → (ι → ℝ) → ℝ) (s v : X → ι → ℝ) (x : X) : ℝ :=
  Sf (features adv σa σs G v x) (s x)

/-- The right-hand side of the `FP_N` equations (17a) with the data-driven filter strength (19),
i.e. of (21a): `s - T v - σ_f F v`. -/
def fpnRHS (adv : (X → ι → ℝ) → X → ι → ℝ) (σa σs : X → ℝ) (G F : Matrix ι ι ℝ) [DecidableEq ι]
    (Sf : Matrix ι (Fin 3) ℝ → (ι → ℝ) → ℝ) (s v : X → ι → ℝ) : X → ι → ℝ :=
  fun x => pnRHS adv σa σs G s v x - filterStrength adv σa σs G Sf s v x • (F *ᵥ v x)

/-- `u` solves the `P_N` equations (12a) at all times `t ∈ T`. -/
def IsPNSolution (adv : (X → ι → ℝ) → X → ι → ℝ) (σa σs : X → ℝ) (G : Matrix ι ι ℝ)
    (s : ℝ → X → ι → ℝ) (T : Set ℝ) (u : ℝ → X → ι → ℝ) : Prop :=
  ∀ t ∈ T, ∀ x, HasDerivAt (fun τ => u τ x) (pnRHS adv σa σs G (s t) (u t) x) t

/-- `u` solves the `FP_N` equations (17a) with filter strength (19), at all times `t ∈ T`. -/
def IsFPNSolution (adv : (X → ι → ℝ) → X → ι → ℝ) (σa σs : X → ℝ) (G F : Matrix ι ι ℝ)
    [DecidableEq ι] (Sf : Matrix ι (Fin 3) ℝ → (ι → ℝ) → ℝ) (s : ℝ → X → ι → ℝ) (T : Set ℝ)
    (u : ℝ → X → ι → ℝ) : Prop :=
  ∀ t ∈ T, ∀ x, HasDerivAt (fun τ => u τ x) (fpnRHS adv σa σs G F Sf (s t) (u t) x) t

variable [DecidableEq ι] {adv : (X → ι → ℝ) → X → ι → ℝ} {σa σs : X → ℝ} {G F : Matrix ι ι ℝ}
  {Sf : Matrix ι (Fin 3) ℝ → (ι → ℝ) → ℝ} {O : X → X} {Z : Matrix ι ι ℝ}

/-- The `P_N` equations are the `FP_N` equations with zero filter strength. -/
theorem fpnRHS_zero (adv : (X → ι → ℝ) → X → ι → ℝ) (σa σs : X → ℝ) (G F : Matrix ι ι ℝ)
    (s v : X → ι → ℝ) : fpnRHS adv σa σs G F (fun _ _ => 0) s v = pnRHS adv σa σs G s v := by
  funext x
  simp [fpnRHS, filterStrength]

/-- Eq. (46): if `W_O` commutes with the advection (41) and `Z_O` with `G` (42), then
`Z_O ξ(v)(Ox)` is the feature matrix of `W_O v` for the rotated cross-sections. -/
theorem features_rotMom (v : X → ι → ℝ) (h41 : adv (rotMom O Z v) = rotMom O Z (adv v))
    (hG : Z * G = G * Z) (x : X) :
    features adv (σa ∘ O) (σs ∘ O) G (rotMom O Z v) x = Z * features adv σa σs G v (O x) := by
  have hG1 : Z * (G - 1) = (G - 1) * Z := by rw [Matrix.mul_sub, Matrix.sub_mul, hG]; simp
  have hcol : ∀ (ξ : ι → Fin 3 → ℝ) i c,
      (Z * Matrix.of ξ) i c = (Z *ᵥ fun k => ξ k c) i := fun ξ i c => by
    simp [Matrix.mul_apply, mulVec, dotProduct]
  ext i c
  rw [features, features, hcol]
  fin_cases c
  · simp [h41, rotMom]
  · simp [rotMom, mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  · have key : (G - 1) *ᵥ (Z *ᵥ v (O x)) = Z *ᵥ ((G - 1) *ᵥ v (O x)) := by
      rw [mulVec_mulVec, mulVec_mulVec, hG1]
    change σs (O x) * ((G - 1) *ᵥ (Z *ᵥ v (O x))) i =
      (Z *ᵥ fun k => σs (O x) * ((G - 1) *ᵥ v (O x)) k) i
    rw [key]
    simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

/-- The equivariance of the `FP_N` right-hand side, the content of (44)-(47) in the proof of
Theorem 1: `W_O (s - T v - σ_f F v)` is the right-hand side for `W_O s`, `W_O v` and the rotated
cross-sections. -/
theorem rotMom_fpnRHS (s v : X → ι → ℝ) (h41 : adv (rotMom O Z v) = rotMom O Z (adv v))
    (hG : Z * G = G * Z) (hF : Z * F = F * Z)
    (h43 : ∀ x s', Sf (features adv σa σs G v x) s' = Sf (Z * features adv σa σs G v x) (Z *ᵥ s')) :
    rotMom O Z (fpnRHS adv σa σs G F Sf s v) =
      fpnRHS adv (σa ∘ O) (σs ∘ O) G F Sf (rotMom O Z s) (rotMom O Z v) := by
  funext x
  have hσ : filterStrength adv (σa ∘ O) (σs ∘ O) G Sf (rotMom O Z s) (rotMom O Z v) x =
      filterStrength adv σa σs G Sf s v (O x) := by
    simp only [filterStrength]
    rw [features_rotMom v h41 hG x]
    exact (h43 (O x) (s (O x))).symm
  have hadv : adv (rotMom O Z v) x = Z *ᵥ adv v (O x) := congrFun h41 x
  simp only [fpnRHS, hσ, pnRHS, hadv]
  simp only [rotMom, Function.comp_apply]
  simp only [fpnRHS, pnRHS, mulVec_sub, mulVec_smul, mulVec_mulVec, hG, hF]

/-- arXiv 2510.05452, **Theorem 1**: if the filter ansatz satisfies (43),
`Σ_f(ξ(v), s) = Σ_f(Z_O ξ(v), Z_O s)`, then the `FP_N` equations are rotationally invariant: when
`u` solves (17a) with source `s` and cross-sections `σₐ, σₛ`, then `W_O u` solves (17a) with
source `W_O s` and cross-sections `R_O σₐ, R_O σₛ` (the converse is the case `O = I`).

This version is for an abstract spatial domain `X`, rotation `O : X → X`, advection operator
`adv` and matrices `Z, G, F`.  It is **conditional** on the two commutation properties that the
paper's proof takes from Proposition 1: `Z G = G Z`, `Z F = F Z` (Eq. (42), (44)) and the
commutation (41) of `W_O` with the advection along the solution.  For the paper's operators these
are proved below (`blockDiagonal'_mul_blockScalar`, `advPN_rotMom`), and `theorem1_pde` is the
unconditional statement. -/
theorem theorem1 {s : ℝ → X → ι → ℝ} {T : Set ℝ} {u : ℝ → X → ι → ℝ} (hG : Z * G = G * Z)
    (hF : Z * F = F * Z) (h41 : ∀ t ∈ T, adv (rotMom O Z (u t)) = rotMom O Z (adv (u t)))
    (h43 : ∀ v x s', Sf (features adv σa σs G v x) s' =
      Sf (Z * features adv σa σs G v x) (Z *ᵥ s'))
    (hu : IsFPNSolution adv σa σs G F Sf s T u) :
    IsFPNSolution adv (σa ∘ O) (σs ∘ O) G F Sf (fun t => rotMom O Z (s t)) T
      (fun t => rotMom O Z (u t)) := by
  intro t ht x
  have hd := (Matrix.mulVecLin Z).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hu t ht (O x))
  have heq := congrFun (rotMom_fpnRHS (s t) (u t) (h41 t ht) hG hF (h43 (u t))) x
  rw [← heq]
  exact hd

/-- The `P_N` equations are the `FP_N` equations with zero filter strength. -/
theorem isPNSolution_iff {s : ℝ → X → ι → ℝ} {T : Set ℝ} {u : ℝ → X → ι → ℝ} :
    IsPNSolution adv σa σs G s T u ↔ IsFPNSolution adv σa σs G F (fun _ _ => 0) s T u := by
  simp only [IsPNSolution, IsFPNSolution, fpnRHS_zero]

omit [DecidableEq ι] in
/-- arXiv 2510.05452, Proposition 1, second part: the `P_N` equations (12) are rotationally
invariant, `W_O u` solves (12) with source `W_O s` and cross-sections `R_O σₐ, R_O σₛ`.  Abstract
form, conditional on (41) and (42) as in `theorem1`; `prop1_pn_pde` is the unconditional form. -/
theorem prop1_pn {s : ℝ → X → ι → ℝ} {T : Set ℝ} {u : ℝ → X → ι → ℝ} (hG : Z * G = G * Z)
    (h41 : ∀ t ∈ T, adv (rotMom O Z (u t)) = rotMom O Z (adv (u t)))
    (hu : IsPNSolution adv σa σs G s T u) :
    IsPNSolution adv (σa ∘ O) (σs ∘ O) G (fun t => rotMom O Z (s t)) T
      (fun t => rotMom O Z (u t)) := by
  classical
  rw [isPNSolution_iff (F := 0)] at hu ⊢
  exact theorem1 hG (by simp) h41 (fun _ _ _ => rfl) hu

/-- arXiv 2510.05452, remark before Theorem 1: with a constant filter strength the `FP_N`
solution inherits the rotational invariance (no condition on the ansatz is needed). -/
theorem theorem1_const (c : ℝ) {s : ℝ → X → ι → ℝ} {T : Set ℝ} {u : ℝ → X → ι → ℝ}
    (hG : Z * G = G * Z) (hF : Z * F = F * Z)
    (h41 : ∀ t ∈ T, adv (rotMom O Z (u t)) = rotMom O Z (adv (u t)))
    (hu : IsFPNSolution adv σa σs G F (fun _ _ => c) s T u) :
    IsFPNSolution adv (σa ∘ O) (σs ∘ O) G F (fun _ _ => c) (fun t => rotMom O Z (s t)) T
      (fun t => rotMom O Z (u t)) :=
  theorem1 hG hF h41 (fun _ _ _ => rfl) hu

end MomentEquations

/-! ### Proposition 2: the rotation invariant ansatz -/

/-- The ansatz (49), `Σ_f(ξ, s) = 𝒩(P ξ, P s)`, for any network `𝒩` (with fixed parameters),
where `P` acts on each column of `ξ` as in (51). -/
noncomputable def nnAnsatz (NN : (Fin 3 → Fin (N + 1) → ℝ) → (Fin (N + 1) → ℝ) → ℝ)
    (ξ : Matrix (Mode N) (Fin 3) ℝ) (s : Mode N → ℝ) : ℝ :=
  NN (fun c => pOp fun i => ξ i c) (pOp s)

/-- arXiv 2510.05452, **Proposition 2**: the ansatz `𝒩(P ξ, P s)` satisfies (43) for every
block-diagonal `Z_O` with orthogonal blocks. -/
theorem prop2
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (hZ : ∀ ℓ, (Zb ℓ)ᵀ * Zb ℓ = 1) (NN : (Fin 3 → Fin (N + 1) → ℝ) → (Fin (N + 1) → ℝ) → ℝ)
    (ξ : Matrix (Mode N) (Fin 3) ℝ) (s : Mode N → ℝ) :
    nnAnsatz NN ξ s = nnAnsatz NN (blockDiagonal' Zb * ξ) (blockDiagonal' Zb *ᵥ s) := by
  have hcol : ∀ c, (fun i => (blockDiagonal' Zb * ξ) i c) =
      blockDiagonal' Zb *ᵥ fun i => ξ i c := fun c => by
    funext i
    simp [Matrix.mul_apply, mulVec, dotProduct]
  simp only [nnAnsatz, hcol, pOp_blockDiagonal'_mulVec hZ]

/-! ### The `P_N` advection and the unconditional Theorem 1 -/

section Advection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {ι : Type*} [Fintype ι]

/-- The advection operator of the `P_N` equations in the form used in (41),
`(A·∇ₓ v)(x) = ⟨r rᵀ Ω·∇ₓ v⟩ = ⟨r(Ω) (Ω·∇ₓ)(r(Ω)ᵀ v)(x)⟩`.  For differentiable `v` this is
`∑_m A^(m) ∂_m v` with `A^(m) = ⟨Ω^(m) r rᵀ⟩`, Eq. (13). -/
noncomputable def advPN (μ : Measure E) (r : E → ι → ℝ) (v : E → ι → ℝ) (x : E) : ι → ℝ :=
  moment μ r (fun Ω => fderiv ℝ (fun y => r Ω ⬝ᵥ v y) x Ω)

/-- arXiv 2510.05452, Eq. (41): `W_O (A·∇ₓ v) = A·∇ₓ (W_O v)`, from Lemma 1 (`r(Ω) = Z r(OΩ)`
with `Z` orthogonal), the chain rule (39) and the invariance of the measure.  The integrability
hypothesis is the regularity of `v` ("sufficiently smooth" in the paper). -/
theorem advPN_rotMom {μ : Measure E} {O : E ≃ₗᵢ[ℝ] E} (hμ : MeasurePreserving O μ μ)
    {r : E → ι → ℝ} {Z : Matrix ι ι ℝ} (hr : ∀ Ω, r Ω = Z *ᵥ r (O Ω)) [DecidableEq ι]
    (hZ : Zᵀ * Z = 1) (v : E → ι → ℝ)
    (hint : ∀ x i, Integrable (fun Ω => r Ω i * fderiv ℝ (fun y => r Ω ⬝ᵥ v y) x Ω) μ) :
    advPN μ r (rotMom O Z v) = rotMom O Z (advPN μ r v) := by
  funext x
  have hrot : ∀ Ω, Zᵀ *ᵥ r Ω = r (O Ω) := fun Ω => by
    rw [hr Ω, mulVec_mulVec, hZ, one_mulVec]
  have hdot : ∀ Ω y, r Ω ⬝ᵥ (Z *ᵥ v (O y)) = r (O Ω) ⬝ᵥ v (O y) := fun Ω y => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hrot]
  have hcomp : ∀ Ω, fderiv ℝ (fun y => r Ω ⬝ᵥ (Z *ᵥ v (O y))) x Ω =
      fderiv ℝ (fun z => r (O Ω) ⬝ᵥ v z) (O x) (O Ω) := by
    intro Ω
    simp_rw [hdot Ω]
    have h := O.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ)
      (f := fun z => r (O Ω) ⬝ᵥ v z) (x := x)
    have h2 := congrArg (fun L => L Ω) h
    simpa [Function.comp_def] using h2
  simp only [advPN, rotMom]
  simp_rw [hcomp]
  exact moment_comp hμ hr (f := fun Ω' => fderiv ℝ (fun z => r Ω' ⬝ᵥ v z) (O x) Ω') (hint (O x))

variable {N : ℕ}

/-- The hypotheses of Lemma 1 for the angular basis `r` and a measure preserving rotation `O`:
`r(Ω) = Z_O r(OΩ)` with `Z_O = diag(Z_O^0, …, Z_O^N)` (Eq. (35)), and orthonormality of the
components of `r`.  The first is the invariance of the spherical harmonics of degree `ℓ` under
rotations ([11, Thm. 1.1.7] in the paper), which is not proved here. -/
structure IsLemma1Data (μ : Measure E) (r : E → Mode N → ℝ) (O : E ≃ₗᵢ[ℝ] E)
    (Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ) :
    Prop where
  /-- `O` preserves the measure of the directions. -/
  measurePreserving : MeasurePreserving O μ μ
  /-- Eq. (35): `r(Ω) = Z_O r(OΩ)`. -/
  rot : ∀ Ω, r Ω = blockDiagonal' Zb *ᵥ r (O Ω)
  /-- The products of components of `r` are integrable. -/
  integrable : ∀ i j, Integrable (fun Ω => r Ω i * r Ω j) μ
  /-- The components of `r` are orthonormal. -/
  gram : ∀ i j, ∫ Ω, r Ω i * r Ω j ∂μ = (1 : Matrix (Mode N) (Mode N) ℝ) i j

/-- arXiv 2510.05452, **Lemma 1**: under `IsLemma1Data`, every block `Z_O^ℓ` is orthogonal. -/
theorem IsLemma1Data.blocks_orthogonal {μ : Measure E} {r : E → Mode N → ℝ} {O : E ≃ₗᵢ[ℝ] E}
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (h : IsLemma1Data μ r O Zb) (ℓ : Fin (N + 1)) :
    Zb ℓ * (Zb ℓ)ᵀ = 1 ∧ (Zb ℓ)ᵀ * Zb ℓ = 1 := by
  have h1 := blocks_mul_transpose_of_blockDiagonal'
    (lemma1_mul_transpose h.measurePreserving h.rot h.integrable h.gram) ℓ
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

/-- `Z_O` is orthogonal under `IsLemma1Data`. -/
theorem IsLemma1Data.transpose_mul_self {μ : Measure E} {r : E → Mode N → ℝ}
    {O : E ≃ₗᵢ[ℝ] E}
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (h : IsLemma1Data μ r O Zb) : (blockDiagonal' Zb)ᵀ * blockDiagonal' Zb = 1 :=
  blockDiagonal'_transpose_mul_self fun ℓ => (h.blocks_orthogonal ℓ).2

/-- arXiv 2510.05452, **Theorem 1**, unconditional form for the paper's operators: the advection
`A·∇ₓ = advPN` on all of `E`, the scattering matrix `G` (`scatterMatrix`), the filter matrix `F`
of (18) (`filterMatrix`), and `Z_O` from Lemma 1.  If the ansatz satisfies (43), then `W_O u`
solves the `FP_N` equations (17a) with source `W_O s` and cross-sections `R_O σₐ, R_O σₛ`
whenever `u` solves them.  The integrability hypothesis `hreg` is the smoothness of `u`. -/
theorem theorem1_pde {μ : Measure E} {r : E → Mode N → ℝ} {O : E ≃ₗᵢ[ℝ] E}
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (hL : IsLemma1Data μ r O Zb) {g : Fin (N + 1) → ℝ} {f : ℝ → ℝ} {σa σs : E → ℝ}
    {Sf : Matrix (Mode N) (Fin 3) ℝ → (Mode N → ℝ) → ℝ}
    (h43 : ∀ v x s', Sf (features (advPN μ r) σa σs (scatterMatrix g) v x) s' =
      Sf (blockDiagonal' Zb * features (advPN μ r) σa σs (scatterMatrix g) v x)
        (blockDiagonal' Zb *ᵥ s'))
    {s : ℝ → E → Mode N → ℝ} {T : Set ℝ} {u : ℝ → E → Mode N → ℝ}
    (hreg : ∀ t ∈ T, ∀ x i, Integrable (fun Ω => r Ω i * fderiv ℝ (fun y => r Ω ⬝ᵥ u t y) x Ω) μ)
    (hu : IsFPNSolution (advPN μ r) σa σs (scatterMatrix g) (filterMatrix N f) Sf s T u) :
    IsFPNSolution (advPN μ r) (σa ∘ O) (σs ∘ O) (scatterMatrix g) (filterMatrix N f) Sf
      (fun t => rotMom O (blockDiagonal' Zb) (s t)) T
      (fun t => rotMom O (blockDiagonal' Zb) (u t)) :=
  theorem1 (blockDiagonal'_mul_blockScalar Zb _) (blockDiagonal'_mul_blockScalar Zb _)
    (fun t ht => advPN_rotMom hL.measurePreserving hL.rot hL.transpose_mul_self (u t)
      (hreg t ht)) h43 hu

/-- arXiv 2510.05452, **Proposition 1**, second part, unconditional form: the `P_N` equations
(12) with the paper's advection and scattering matrix are rotationally invariant. -/
theorem prop1_pn_pde {μ : Measure E} {r : E → Mode N → ℝ} {O : E ≃ₗᵢ[ℝ] E}
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (hL : IsLemma1Data μ r O Zb) {g : Fin (N + 1) → ℝ} {σa σs : E → ℝ}
    {s : ℝ → E → Mode N → ℝ} {T : Set ℝ} {u : ℝ → E → Mode N → ℝ}
    (hreg : ∀ t ∈ T, ∀ x i, Integrable (fun Ω => r Ω i * fderiv ℝ (fun y => r Ω ⬝ᵥ u t y) x Ω) μ)
    (hu : IsPNSolution (advPN μ r) σa σs (scatterMatrix g) s T u) :
    IsPNSolution (advPN μ r) (σa ∘ O) (σs ∘ O) (scatterMatrix g)
      (fun t => rotMom O (blockDiagonal' Zb) (s t)) T
      (fun t => rotMom O (blockDiagonal' Zb) (u t)) :=
  prop1_pn (blockDiagonal'_mul_blockScalar Zb _)
    (fun t ht => advPN_rotMom hL.measurePreserving hL.rot hL.transpose_mul_self (u t)
      (hreg t ht)) hu

/-- arXiv 2510.05452, Theorem 1 with Proposition 2: the data-driven `FP_N` equations with the
ansatz `Σ_f = 𝒩(P ξ, P s)` of (49) are rotationally invariant, for every network `𝒩`. -/
theorem theorem1_nnAnsatz {μ : Measure E} {r : E → Mode N → ℝ} {O : E ≃ₗᵢ[ℝ] E}
    {Zb : ∀ ℓ : Fin (N + 1), Matrix (Fin (2 * (ℓ : ℕ) + 1)) (Fin (2 * (ℓ : ℕ) + 1)) ℝ}
    (hL : IsLemma1Data μ r O Zb) {g : Fin (N + 1) → ℝ} {f : ℝ → ℝ} {σa σs : E → ℝ}
    (NN : (Fin 3 → Fin (N + 1) → ℝ) → (Fin (N + 1) → ℝ) → ℝ)
    {s : ℝ → E → Mode N → ℝ} {T : Set ℝ} {u : ℝ → E → Mode N → ℝ}
    (hreg : ∀ t ∈ T, ∀ x i, Integrable (fun Ω => r Ω i * fderiv ℝ (fun y => r Ω ⬝ᵥ u t y) x Ω) μ)
    (hu : IsFPNSolution (advPN μ r) σa σs (scatterMatrix g) (filterMatrix N f) (nnAnsatz NN)
      s T u) :
    IsFPNSolution (advPN μ r) (σa ∘ O) (σs ∘ O) (scatterMatrix g) (filterMatrix N f)
      (nnAnsatz NN) (fun t => rotMom O (blockDiagonal' Zb) (s t)) T
      (fun t => rotMom O (blockDiagonal' Zb) (u t)) :=
  theorem1_pde hL (fun _ _ _ => prop2 (fun ℓ => (hL.blocks_orthogonal ℓ).2) NN _ _) hreg hu

end Advection

/-! ### Filter functions, the filter matrix and isotropic scattering -/

section Filter

variable {N : ℕ}

/-- A filter function of order `α`, Eq. (15): non-negative, monotonically decreasing and of class
`C^α` on `[0, 1]`, with (i) `f(0) = 1`, (ii) `f^(ℓ)(0) = 0` for `1 ≤ ℓ ≤ α - 1` and
(iii) `f^(α)(0) ≠ 0`, derivatives taken within `[0, 1]`.  The paper prints (ii) for all
`ℓ ≤ α - 1`; for `ℓ = 0` that contradicts (i) (`printed_15_inconsistent`), so `ℓ ≥ 1` is
meant. -/
structure IsFilterFunction (f : ℝ → ℝ) (α : ℕ) : Prop where
  /-- `f ∈ C^α([0, 1])`. -/
  contDiffOn : ContDiffOn ℝ α f (Icc 0 1)
  /-- `f` is non-negative on `[0, 1]`. -/
  nonneg : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f s
  /-- `f` is monotonically decreasing on `[0, 1]`. -/
  antitoneOn : AntitoneOn f (Icc 0 1)
  /-- (i) `f(0) = 1`. -/
  map_zero : f 0 = 1
  /-- (ii) `f^(ℓ)(0) = 0` for `1 ≤ ℓ ≤ α - 1`. -/
  iteratedDeriv_eq_zero : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ α - 1 → iteratedDerivWithin ℓ f (Icc 0 1) 0 = 0
  /-- (iii) `f^(α)(0) ≠ 0`. -/
  iteratedDeriv_ne_zero : iteratedDerivWithin α f (Icc 0 1) 0 ≠ 0

/-- arXiv 2510.05452, Eq. (15) as printed: no function satisfies (i) `f(0) = 1` together with
(ii) `f^(ℓ)(0) = 0` for all `ℓ ≤ α - 1`, because `ℓ = 0` is included.  A typo: the intended
range is `1 ≤ ℓ ≤ α - 1`, as in `IsFilterFunction`. -/
theorem printed_15_inconsistent (f : ℝ → ℝ) (α : ℕ) :
    ¬ (f 0 = 1 ∧ ∀ ℓ ≤ α - 1, iteratedDerivWithin ℓ f (Icc 0 1) 0 = 0) := by
  rintro ⟨h1, h2⟩
  have := h2 0 (Nat.zero_le _)
  rw [iteratedDerivWithin_zero, h1] at this
  exact one_ne_zero this

/-- The exponential filter of Eq. (16), `f(s) = exp(-s^α)` with `α = 4`. -/
noncomputable def expFilter (s : ℝ) : ℝ := Real.exp (-s ^ 4)

lemma hasDerivAt_poly_mul_expFilter {p p' : ℝ → ℝ} (hp : ∀ s, HasDerivAt p (p' s) s) (s : ℝ) :
    HasDerivAt (fun s => p s * expFilter s) ((p' s - 4 * s ^ 3 * p s) * expFilter s) s := by
  have h1 : HasDerivAt expFilter (Real.exp (-s ^ 4) * -(↑4 * s ^ 3)) s := by
    unfold expFilter
    simpa using ((hasDerivAt_pow 4 s).neg).exp
  convert (hp s).mul h1 using 1
  simp only [expFilter]
  ring

lemma deriv_poly_mul_expFilter {p p' : ℝ → ℝ} (hp : ∀ s, HasDerivAt p (p' s) s) :
    deriv (fun s => p s * expFilter s) = fun s => (p' s - 4 * s ^ 3 * p s) * expFilter s :=
  funext fun s => (hasDerivAt_poly_mul_expFilter hp s).deriv

lemma iteratedDeriv_expFilter_four :
    iteratedDeriv 1 expFilter = (fun s => (-4 * s ^ 3) * expFilter s) ∧
    iteratedDeriv 2 expFilter = (fun s => (-12 * s ^ 2 + 16 * s ^ 6) * expFilter s) ∧
    iteratedDeriv 3 expFilter =
      (fun s => (-24 * s + 144 * s ^ 5 - 64 * s ^ 9) * expFilter s) ∧
    iteratedDeriv 4 expFilter =
      (fun s => (-24 + 816 * s ^ 4 - 1152 * s ^ 8 + 256 * s ^ 12) * expFilter s) := by
  have e0 : expFilter = fun s => (fun _ : ℝ => (1 : ℝ)) s * expFilter s := by funext s; simp
  have e1 : iteratedDeriv 1 expFilter = (fun s => (-4 * s ^ 3) * expFilter s) := by
    rw [iteratedDeriv_one, e0,
      deriv_poly_mul_expFilter (p' := fun _ => 0) fun s => hasDerivAt_const s 1]
    funext s; ring
  have e2 : iteratedDeriv 2 expFilter = (fun s => (-12 * s ^ 2 + 16 * s ^ 6) * expFilter s) := by
    rw [iteratedDeriv_succ, e1, deriv_poly_mul_expFilter (p' := fun s => -12 * s ^ 2)
      fun s => by convert (hasDerivAt_pow 3 s).const_mul (-4) using 1; push_cast; ring]
    funext s; ring
  have e3 : iteratedDeriv 3 expFilter =
      (fun s => (-24 * s + 144 * s ^ 5 - 64 * s ^ 9) * expFilter s) := by
    rw [iteratedDeriv_succ, e2, deriv_poly_mul_expFilter (p' := fun s => -24 * s + 96 * s ^ 5)
      fun s => by
        convert ((hasDerivAt_pow 2 s).const_mul (-12)).add ((hasDerivAt_pow 6 s).const_mul 16)
          using 1
        push_cast; ring]
    funext s; ring
  have e4 : iteratedDeriv 4 expFilter =
      (fun s => (-24 + 816 * s ^ 4 - 1152 * s ^ 8 + 256 * s ^ 12) * expFilter s) := by
    rw [iteratedDeriv_succ, e3,
      deriv_poly_mul_expFilter (p' := fun s => -24 + 720 * s ^ 4 - 576 * s ^ 8)
      fun s => by
        convert (((hasDerivAt_id s).const_mul (-24)).add
          ((hasDerivAt_pow 5 s).const_mul 144)).sub ((hasDerivAt_pow 9 s).const_mul 64)
          using 1
        · funext x; simp
        · push_cast; ring]
    funext s; ring
  exact ⟨e1, e2, e3, e4⟩

lemma contDiff_expFilter : ContDiff ℝ ⊤ expFilter := by
  unfold expFilter
  fun_prop

/-- arXiv 2510.05452, Eq. (16): `f(s) = exp(-s⁴)` is a filter function of order four. -/
theorem isFilterFunction_expFilter : IsFilterFunction expFilter 4 := by
  obtain ⟨e1, e2, e3, e4⟩ := iteratedDeriv_expFilter_four
  have hw : ∀ k, iteratedDerivWithin k expFilter (Icc 0 1) 0 = iteratedDeriv k expFilter 0 :=
    fun k => iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (contDiff_expFilter.contDiffAt.of_le le_top) (left_mem_Icc.2 zero_le_one)
  refine ⟨contDiff_expFilter.contDiffOn.of_le le_top, fun s _ => (Real.exp_pos _).le, ?_,
    by simp [expFilter], ?_, ?_⟩
  · intro a ha b hb hab
    simp only [expFilter]
    exact Real.exp_le_exp.2 (neg_le_neg (pow_le_pow_left₀ ha.1 hab 4))
  · intro ℓ h1 h3
    rw [hw]
    interval_cases ℓ
    · rw [e1]; simp
    · rw [e2]; simp
    · rw [e3]; simp
  · rw [hw, e4]; simp [expFilter]

/-- The filter matrix (18) of the exponential filter (16): `F_{(ℓ,m),(ℓ,m)} = (ℓ/(N+1))⁴`. -/
theorem filterMatrix_expFilter :
    filterMatrix N expFilter = blockScalar fun ℓ => ((ℓ : ℝ) / (N + 1)) ^ 4 := by
  simp [filterMatrix, expFilter, Real.log_exp]

/-- The first moment index `(ℓ, m) = (0, 0)`. -/
def mode00 : Mode N := ⟨0, 0⟩

lemma mode_fst_eq_zero_iff (i : Mode N) : i.1 = 0 ↔ i = mode00 := by
  constructor
  · obtain ⟨ℓ, m⟩ := i
    rintro rfl
    have : (m : ℕ) = 0 := by have := m.2; simp at this; omega
    simp only [mode00, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Fin.ext this
  · rintro rfl; rfl

/-- arXiv 2510.05452, below (18): `F_{(0,0),(0,0)} = 0` for every filter with `f(0) = 1`. -/
theorem filterMatrix_mode00 {f : ℝ → ℝ} (hf : f 0 = 1) :
    filterMatrix N f mode00 mode00 = 0 := by
  simp [filterMatrix, blockScalar, mode00, hf]

/-- arXiv 2510.05452, below (18): "the filter does not affect the total particle
concentration": the equation for the moment `u_0^0` (the concentration is `√(4π) u_0^0`) is the
same in the `FP_N` equations (17a) as in the `P_N` equations (12a), whatever the filter
strength. -/
theorem fpnRHS_mode00 {X : Type*} {f : ℝ → ℝ} (hf : f 0 = 1)
    (adv : (X → Mode N → ℝ) → X → Mode N → ℝ) (σa σs : X → ℝ) (G : Matrix (Mode N) (Mode N) ℝ)
    (Sf : Matrix (Mode N) (Fin 3) ℝ → (Mode N → ℝ) → ℝ) (s v : X → Mode N → ℝ) (x : X) :
    fpnRHS adv σa σs G (filterMatrix N f) Sf s v x mode00 = pnRHS adv σa σs G s v x mode00 := by
  simp [fpnRHS, filterMatrix, blockScalar, mulVec_diagonal, mode00, hf]

/-- The diagonal of the filter matrix (18) is non-negative for every filter function, so
`σ_f F` with `σ_f ≥ 0` is an artificial (absorption-like) scattering term. -/
theorem filterMatrix_diag_nonneg {f : ℝ → ℝ} {α : ℕ} (hf : IsFilterFunction f α)
    (i : Mode N) : 0 ≤ filterMatrix N f i i := by
  have hmem : (i.1 : ℝ) / (N + 1) ∈ Icc (0 : ℝ) 1 := by
    have h1 : ((i.1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp i.1.2
    constructor
    · positivity
    · rw [div_le_one (by positivity)]; linarith
  have hle : f ((i.1 : ℝ) / (N + 1)) ≤ 1 := by
    have := hf.antitoneOn (left_mem_Icc.2 zero_le_one) hmem hmem.1
    rwa [hf.map_zero] at this
  simp only [filterMatrix, blockScalar, diagonal_apply_eq]
  exact neg_nonneg.2 (Real.log_nonpos (hf.nonneg _ hmem) hle)

/-- The coefficients `g_ℓ` of isotropic scattering, `g = 1/(4π)`: `g_0 = 1` and `g_ℓ = 0` for
`ℓ ≥ 1` (Eq. (7) with the orthogonality of the Legendre polynomials, not proved here). -/
def isoCoeff (ℓ : Fin (N + 1)) : ℝ := if ℓ = 0 then 1 else 0

/-- arXiv 2510.05452, Sec. 4: for isotropic scattering only the `ℓ = 0` component of
`σₛ P(G - I) v`, the preprocessed third feature column in (51), is nonzero. -/
theorem pOp_features_two_isotropic {X : Type*} (adv : (X → Mode N → ℝ) → X → Mode N → ℝ)
    (σa σs : X → ℝ) (v : X → Mode N → ℝ) (x : X) {ℓ : Fin (N + 1)} (hℓ : ℓ ≠ 0) :
    pOp (fun i => features adv σa σs (scatterMatrix isoCoeff) v x i 2) ℓ = 0 := by
  have hdiag : scatterMatrix (N := N) isoCoeff - 1 = diagonal fun i => -isoCoeff i.1 := by
    rw [scatterMatrix, blockScalar, ← diagonal_one, diagonal_sub]
    congr 1; funext i; ring
  simp only [pOp, blockNorm, features, Matrix.of_apply, hdiag]
  simp [mulVec_diagonal, isoCoeff, hℓ]


/-- Isotropic scattering in the moment basis: `G = diag(1 - g_ℓ) = I - κ e eᵀ` with
`e = c δ_{(0,0)}` and `κ c² = 1`.  For the paper's normalisation `e = ⟨r⟩ = √(4π) δ_{(0,0)}` and
`κ = 1/(4π)`, which is the form of `PNData` (see `pnRHS_eq_pnData_field`). -/
theorem scatterMatrix_isoCoeff {c κ : ℝ} (h : κ * c ^ 2 = 1) :
    scatterMatrix (N := N) isoCoeff =
      1 - κ • vecMulVec (Pi.single mode00 c) (Pi.single mode00 c) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = mode00
    · subst hi
      simp [scatterMatrix, blockScalar, isoCoeff, mode00, vecMulVec_apply, ← h, sq]
    · have h1 : i.1 ≠ 0 := fun h0 => hi ((mode_fst_eq_zero_iff i).1 h0)
      simp [scatterMatrix, blockScalar, isoCoeff, h1, vecMulVec_apply, hi]
  · have : (Pi.single mode00 c : Mode N → ℝ) i * (Pi.single mode00 c : Mode N → ℝ) j = 0 := by
      by_cases hi : i = mode00
      · subst hi; simp [Ne.symm hij]
      · simp [Pi.single_apply, hi]
    simp [scatterMatrix, blockScalar, hij, vecMulVec_apply, this]

end Filter

/-! ### Connection with the `P_N` material of the library and with `ODESolution` -/

section Library

open LeanDLRA.Literature.P1912_07522 in
/-- Bridge to the semi-discrete `P_N` system `PNData` of `LeanDLRA.Literature.P1912_07522` (arXiv
1912.07522): on a grid of cells `m`, with advection `∑_d D_d Y A_d`, total cross-section
`σₜ = σₐ + σₛ`, isotropic scattering `G = I - κ e eᵀ` and isotropic source `q(t) eᵀ`, the
`P_N` right-hand side (14a) of arXiv 2510.05452 is `PNData.field`.  So the rotation results of
this file and the low-rank results of 1912.07522 are about the same equations. -/
theorem pnRHS_eq_pnData_field {m n ι' : Type*} [Fintype m] [Fintype n] [Fintype ι']
    [DecidableEq m] [DecidableEq n] (P : PNData m n ι') (σa σs : m → ℝ)
    (hσt : P.σt = diagonal (σa + σs)) (hσs : P.σs = diagonal σs) (t : ℝ) (Y : m → n → ℝ) :
    Matrix.of (pnRHS (fun Y => (∑ d, P.D d * Matrix.of Y * P.A d : Matrix m n ℝ)) σa σs
      (1 - P.κ • vecMulVec P.e P.e) (P.src t) Y) = P.field t (Matrix.of Y) := by
  ext x j
  simp only [Matrix.of_apply, pnRHS, PNData.field, PNData.homog, PNData.src, hσt, hσs,
    Matrix.mul_assoc, diagonal_mul, Pi.sub_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply,
    sub_mulVec, one_mulVec, Matrix.sum_apply]
  simp only [mulVec, dotProduct, vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply,
    Finset.mul_sum]
  ring_nf
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp [Matrix.smul_apply, vecMulVec_apply]; ring

/-- `W_O` as a linear map on the grid functions `Matrix X ι ℝ`. -/
def rotLin {X ι : Type*} [Fintype ι] (O : X → X) (Z : Matrix ι ι ℝ) :
    Matrix X ι ℝ →ₗ[ℝ] Matrix X ι ℝ where
  toFun v := rotMom O Z v
  map_add' v w := by
    change rotMom O Z (fun x => v x + w x) = fun x => rotMom O Z v x + rotMom O Z w x
    funext x
    simp [rotMom, mulVec_add]
  map_smul' c v := by
    change rotMom O Z (fun x => c • v x) = fun x => c • rotMom O Z v x
    funext x
    simp [rotMom, mulVec_smul]

open scoped LeanDLRA.Frobenius in
/-- arXiv 2510.05452, Theorem 1 for the semi-discrete `FP_N` system on a grid `X` (Eq. (90) with
exact time integration), in the library's ODE notion `ODESolution`: if `u` solves
`u' = s - T u - σ_f F u` on `[a, b]`, then `W_O u` solves the system with source `W_O s` and
cross-sections `R_O σₐ, R_O σₛ`.  Conditional, like `theorem1`, on `Z G = G Z`, `Z F = F Z` and
on the commutation (41) of the discrete advection with the grid rotation `O : X → X` (true for
rotation symmetric grids and stencils); the paper states Theorem 1 for the PDE only. -/
theorem theorem1_ode {X ι : Type*} [Fintype X] [Fintype ι] [DecidableEq ι]
    {adv : (X → ι → ℝ) → X → ι → ℝ} {σa σs : X → ℝ} {G F : Matrix ι ι ℝ}
    {Sf : Matrix ι (Fin 3) ℝ → (ι → ℝ) → ℝ} {O : X → X} {Z : Matrix ι ι ℝ}
    {s : ℝ → Matrix X ι ℝ} {u : ℝ → Matrix X ι ℝ} {a b : ℝ}
    (hG : Z * G = G * Z) (hF : Z * F = F * Z)
    (h41 : ∀ t ∈ Ico a b, adv (rotMom O Z (u t)) = rotMom O Z (adv (u t)))
    (h43 : ∀ v x s', Sf (features adv σa σs G v x) s' =
      Sf (Z * features adv σa σs G v x) (Z *ᵥ s'))
    (hu : ODESolution (fun t (Y : Matrix X ι ℝ) =>
      (fpnRHS adv σa σs G F Sf (s t) Y : Matrix X ι ℝ)) u a b) :
    ODESolution (fun t (Y : Matrix X ι ℝ) =>
      (fpnRHS adv (σa ∘ O) (σs ∘ O) G F Sf (rotMom O Z (s t)) Y : Matrix X ι ℝ))
      (fun t => (rotMom O Z (u t) : Matrix X ι ℝ)) a b := by
  let L : Matrix X ι ℝ →L[ℝ] Matrix X ι ℝ := LinearMap.toContinuousLinearMap (rotLin O Z)
  refine ⟨L.continuous.comp_continuousOn hu.cont, fun t ht => ?_⟩
  have hd := L.hasFDerivAt.comp_hasDerivWithinAt t (hu.deriv t ht)
  have heq := rotMom_fpnRHS (Sf := Sf) (s t) (u t) (h41 t ht) hG hF (h43 (u t))
  change HasDerivWithinAt (fun t => L (u t)) _ _ _
  rw [← heq]
  exact hd

/-- Non-vacuity of `IsLemma1Data`: for `N = 0`, the Dirac measure at `0`, the constant basis
`r = 1` and `Z_O = I`, the hypotheses of Lemma 1 hold for every linear isometry `O`.  (For the
surface measure of `𝕊²` and the real spherical harmonics they are the classical facts cited in the
paper, which need the harmonic analysis on `𝕊²` that Mathlib lacks.) -/
theorem isLemma1Data_dirac {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (O : E ≃ₗᵢ[ℝ] E) :
    IsLemma1Data (N := 0) (Measure.dirac 0) (fun _ _ => 1) O 1 := by
  have hsub : ∀ i j : Mode 0, i = j := fun i j => by
    rw [(mode_fst_eq_zero_iff i).1 (Subsingleton.elim (α := Fin 1) _ _),
      (mode_fst_eq_zero_iff j).1 (Subsingleton.elim (α := Fin 1) _ _)]
  refine ⟨⟨O.continuous.measurable, ?_⟩, fun Ω => ?_, fun i j => integrable_const _,
    fun i j => ?_⟩
  · rw [Measure.map_dirac' O.continuous.measurable, map_zero]
  · rw [blockDiagonal'_one, one_mulVec]
  · rw [hsub i j]; simp

end Library

end LeanDLRA.Literature.P2510_05452
